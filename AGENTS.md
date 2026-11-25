# Instructions for formalization agents

## Project

This repository formalizes localic measure theory, including nuclei, sublocales,
and Carathéodory extension. The pinned toolchain and Mathlib revision are Lean
4.36.0; do not change either unless the task requires it.

## Workflow

1. Read the source theorem and preserve its assumptions, quantifiers, domains,
   and conclusion.
2. Search the existing repository and the pinned Mathlib API before introducing
   definitions. Prefer existing nucleus, frame, and sublocale APIs.
3. Keep changes scoped, preserve downstream interfaces, and never use `sorry`,
   `admit`, `axiom`, or `unsafe` to bypass a proof.
4. Compile the affected target while iterating and run `lake build` before
   completing a port.
5. Inspect the final diff and leave unrelated or pre-existing changes intact.

## Lean commands

```sh
lake build Leroy.Nucleus_Image
lake build Leroy.Sublocale
lake build
```

For the actual tactic state at a proof location, use Lean's language server
instead of inferring the goal from an error message:

```sh
python3 scripts/lean_goal.py Leroy/Sublocale.lean --line 202 --column 5
```

The line and column are one-based; the column defaults to 1. The helper opens
the saved file in `lean --server`, waits for elaboration, and calls Lean's
`$/lean/plainGoal` request. It prints all active goals, `no goals` when the
proof is complete, or a message when the cursor is outside a tactic proof.
Use `--help` for options, including an explicit `--project-root`.

Lean LSP references for this pinned version:

- [`$/lean/plainGoal` and `textDocument/waitForDiagnostics`](https://github.com/leanprover/lean4/blob/v4.36.0/src/Lean/Data/Lsp/Extra.lean)
- [Interactive goal-state tests](https://github.com/leanprover/lean4/blob/v4.36.0/tests/server_interactive/plainGoal.lean.out.expected)
