#!/usr/bin/env python3
"""Print Lean's current tactic goal at a one-based file position."""

import argparse
import json
import os
from pathlib import Path
import queue
import subprocess
import sys
import threading
import time
from urllib.parse import quote


class LeanLsp:
    def __init__(self, process):
        self.process = process
        self.messages = queue.Queue()
        self.next_id = 1
        self.reader = threading.Thread(target=self._read_messages, daemon=True)
        self.reader.start()

    def _read_messages(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        self.messages.put(None)
                        return
                    if line in (b"\r\n", b"\n"):
                        break
                    key, separator, value = line.decode("ascii").partition(":")
                    if separator:
                        headers[key.lower()] = value.strip()
                length = int(headers["content-length"])
                payload = self.process.stdout.read(length)
                self.messages.put(json.loads(payload))
        except Exception as error:
            self.messages.put(error)

    def send(self, message):
        payload = json.dumps(message, ensure_ascii=False).encode("utf-8")
        self.process.stdin.write(
            f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii") + payload
        )
        self.process.stdin.flush()

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params, timeout):
        request_id = self.next_id
        self.next_id += 1
        self.send(
            {"jsonrpc": "2.0", "id": request_id, "method": method, "params": params}
        )
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"Timed out waiting for Lean's {method} response")
            try:
                message = self.messages.get(timeout=remaining)
            except queue.Empty as error:
                raise TimeoutError(
                    f"Timed out waiting for Lean's {method} response"
                ) from error
            if message is None:
                raise RuntimeError("Lean language server exited unexpectedly")
            if isinstance(message, Exception):
                raise RuntimeError(f"Could not read Lean's LSP response: {message}")
            if message.get("method") and "id" in message:
                self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
                continue
            if message.get("id") == request_id:
                if "error" in message:
                    error = message["error"]
                    raise RuntimeError(
                        f"Lean LSP request {method} failed: "
                        f"{error.get('message', error)}"
                    )
                return message.get("result")


def find_project_root(path, explicit_root):
    if explicit_root is not None:
        root = explicit_root.expanduser().resolve()
        if not root.is_dir():
            raise ValueError(f"Project root is not a directory: {root}")
        return root
    for candidate in (path.parent, *path.parent.parents):
        if (candidate / "lakefile.lean").is_file() or (
            candidate / "lakefile.toml"
        ).is_file():
            return candidate
    raise ValueError("Could not find a Lake project; pass --project-root explicitly")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path, help="Lean source file")
    parser.add_argument("--line", type=int, required=True, help="One-based line")
    parser.add_argument(
        "--column", type=int, default=1, help="One-based Unicode column (default: 1)"
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        help="Lake project root (detected from the file's parent directories by default)",
    )
    parser.add_argument(
        "--timeout", type=float, default=120, help="LSP request timeout in seconds"
    )
    args = parser.parse_args()

    path = args.file.expanduser().resolve()
    if not path.is_file():
        raise ValueError(f"Lean source file does not exist: {path}")
    if path.suffix != ".lean":
        raise ValueError(f"Expected a .lean source file: {path}")
    if args.line < 1 or args.column < 1:
        raise ValueError("--line and --column must be positive one-based positions")

    source = path.read_text(encoding="utf-8")
    lines = source.splitlines()
    if args.line > len(lines):
        raise ValueError(f"Line {args.line} is past the end of {path}")
    line = lines[args.line - 1]
    if args.column > len(line) + 1:
        raise ValueError(f"Column {args.column} is past the end of line {args.line}")

    project_root = find_project_root(path, args.project_root)
    position = {
        "line": args.line - 1,
        "character": len(line[: args.column - 1].encode("utf-16-le")) // 2,
    }
    uri = path.as_uri()
    process = subprocess.Popen(
        ["lake", "env", "lean", "--server"],
        cwd=project_root,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=None,
    )
    client = LeanLsp(process)
    try:
        client.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": project_root.as_uri(),
                "capabilities": {},
                "clientInfo": {"name": "lean-goal-inspector", "version": "1"},
            },
            args.timeout,
        )
        client.notify("initialized", {})
        client.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": source,
                }
            },
        )
        client.request(
            "textDocument/waitForDiagnostics",
            {"uri": uri, "version": 1},
            args.timeout,
        )
        goal = client.request(
            "$/lean/plainGoal",
            {"textDocument": {"uri": uri}, "position": position},
            args.timeout,
        )
        if goal is None:
            print("No tactic goal at this position.")
        else:
            print(goal["rendered"])
    finally:
        if process.poll() is None:
            try:
                client.request("shutdown", {}, min(args.timeout, 5))
            except (RuntimeError, TimeoutError, BrokenPipeError):
                pass
            try:
                client.notify("exit", {})
            except BrokenPipeError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.terminate()
                process.wait()


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, TimeoutError, ValueError) as error:
        print(f"lean_goal: {error}", file=sys.stderr)
        sys.exit(1)
