# Progress / handoff notes — Lean cleanup + Typst writeup

Last updated: end of the Phase-2 proof-cleanup session. Read this before
continuing work in this repository.

## State of the build

- `lake build` (full): **clean — 0 errors, 0 warnings** (6398 jobs).
- Axiom check (`lake env lean /tmp/axcheck2.lean`):
  - `Measure.caratheodory.strictly_additive` — `[propext, Classical.choice, Quot.sound]`
  - the capstone example (still named `Beispiel` in the source) — same three axioms.
  - No `sorryAx` anywhere; all former `sorry` occurrences in the repo were inside
    block comments and have been deleted.

## Branch / commit layout

- `main` carries Phase 1 as commit `7cdf63c` ("Phase 1: refactor foundations").
- Phase 2 (this working tree) is committed on branch **`phase2-measure-cleanup`**
  and pushed to `origin`. It touches exactly four files:
  `Leroy/Measure/Basic.lean`, `Regular.lean`, `Restrict.lean`, `Reduction.lean`
  plus this `PROGRESS.md`.
- Do not push `main` without explicit authorization.

## Phase 2 — what was done (Measure files)

All renames are pure renames (statements unchanged) unless noted.

### Leroy tagging convention (user-approved)
- Lemmas that correspond to numbered results in Leroy's paper (`leroy.pdf`,
  arXiv:1303.5631; text extraction at `/tmp/leroy.txt`, measure chapter ~lines
  1501–1900) get a docstring tag `**Leroy, Lemme N (Ch. IV)**` (or Prop./Cor.).
- Intermediate lemmas not in the paper are marked `Auxiliary …` in the docstring.

### Mapping table (Leroy → Lean)
| Leroy | Lean declaration |
| --- | --- |
| Lemme 1 | `Measure.caratheodory.preserves_sup'` (in `Measure/Basic.lean`) |
| Lemme 2 | `Sublocale.eq_sInf_openNhds` / `Sublocale.eq_sInf_nhds` |
| Lemme 3 | `Measure.add_compl_top` |
| Lemme 4 | `Measure.add_compl_inf` |
| Corollaire 1 | `Measure.restrict_subadditive` |
| Lemme 5 | `Measure.inf_filtered` |
| Cor. "Restriction d'une mesure" | `Measure.restrict_sublocale_measure` |
| Lemme 6 | `Measure.preserves_iInf` |
| Lemme 7 (principal) | `Measure.caratheodoryPreserves_iInf` (see note below) |
| Prop. 1 (µ-réduction) | `e_μ`, `e_μ_nucleus`, `μ_Reduction`, `R_μ`, `μ_R_μ_eq` |

### Renames applied in this phase
- `Exists_Neighbourhood_epsilon(_lt)` → `Measure.exists_mem_openNhds_le` / `_lt`
  (tagged Auxiliary for Lemme 1) — `Measure/Basic.lean`.
- `strictly_additive''` → `Measure.add_eq_inf_add_sup`; `Measure.monotone`
  congruence stub → `toFun_congr`; deleted unused `ℕpos`/`Rpos` — `Basic.lean`.
- `intersection_Open_Neighbourhhood` → `Sublocale.eq_sInf_openNhds` (Lemme 2),
  `intersection_Neighbourhood` → `Sublocale.eq_sInf_nhds`,
  `add_complement` → `Measure.add_compl_top` (Lemme 3),
  `add_complement_inf` → `Measure.add_compl_inf` (Lemme 4) — `Regular.lean`.
- `Measure_Neighbourhood_μ_eq_top` → `Measure.toFun_eq_top_of_mem_nhds_reduction`,
  `Measure_μ_Reduction_eq_top` → `Measure.caratheodory_reduction_eq_top`
  (⚠ these two renames were lost in a working-tree accident and are **NOT yet
  re-applied** — the old names are still in `Reduction.lean`).
- Lemme 7: `Measure.caratheodordy.preserves_iInf` (typo) →
  **`Measure.caratheodoryPreserves_iInf`** — deliberately NOT
  `Measure.caratheodory.preserves_iInf`: that namespace collides with the
  *definition* `Measure.caratheodory` and breaks elaboration inside the lemma's
  own proof (reproduced and isolated experimentally; see "Gotchas").
- Also cleaned: dead commented blocks, scratch markers (`---`, `----`,
  `------------- Wichitig`), German comments → English, typos.

### Proof repair in `Reduction.lean` (Lemme 7, `V_n_nonempty`)
The original `use ⊤; simp only [openNhds, Set.mem_ofPred_eq, Open.top_toSublocale,
le_top, exists_const, V_a]` was fragile (and failed outright once the lemma was
renamed). Replaced by an explicit proof reusing the existing API:
```lean
have V_n_nonempty : Nonempty V_a := by
  obtain ⟨w, hw⟩ := Sublocale.openNhds_nonempty (A_i (Classical.arbitrary ι))
  exact ⟨w, ⟨Classical.arbitrary ι, hw⟩⟩
```
(`ι` has no `OfNat`; do not use index `0`.) Note `Sublocale.openNhds_top_mem`
applied via anonymous-constructor notation fails with a confusing
"Application type mismatch … `?m ∈ ⊤.toSublocale`" — go through
`openNhds_nonempty` + `obtain` instead.

## Gotchas discovered (worth remembering)

1. **Namespace/def collision**: naming a lemma
   `Measure.caratheodory.<name>` (namespace of the *definition*
   `Measure.caratheodory`, Basic.lean:89) changes elaboration inside that
   lemma's own proof — a previously-working `simp only` stops closing the goal.
   Keep such lemmas OUT of the `Measure.caratheodory` namespace.
2. **Cascading rw errors**: an unrenamed constant inside
   `repeat rw [← @X, ← @Y]` can surface as a *later*, seemingly unrelated
   `failed to synthesize` error (here at `rw [@le_ciInf_iff']`, Reduction.lean
   ~1023). Grep for all occurrences of an old name before assuming a rename is
   complete.
3. **Editing discipline**: python replace-scripts crashed twice earlier on
   inexact strings; line numbers shift after every edit batch — re-grep before
   sed. Prefer the `edit` tool with exact strings.
4. `scripts/lean_goal.py <file> --line N --column C` gives the true tactic
   state; error positions can mislead (see gotcha 2).
5. doc-gen/docbuild is pinned to v4.28.0-rc1 vs Lean 4.36.0 — known mismatch,
   out of scope.

## Known open items / flags for the writeup

- `strictly_additive` does **not** appear in leroy.pdf — it is the port's own
  capstone; present it as such, not as a Leroy result.
- The README's claim of "µ-reducible" is not backed by a theorem in the code —
  flagged to the user, unresolved.
- `Beispiel` (Reduction.lean, ~line 1160) was planned to be renamed to
  `Measure.caratheodory.example`; **not yet done** (note: `example` may clash
  with the `example` keyword — pick e.g. `Measure.caratheodory.ex` or verify).
- The two `Measure_Neighbourhood_μ_eq_top` / `Measure_μ_Reduction_eq_top`
  renames above still need re-applying + a rebuild.
- Non-built modules `Leroy/Basic.lean`, `Leroy/Factorisation.lean`: light
  cleanup only, per user decision.

## Phase 3 (next): Typst writeup

Plan agreed with user: English, self-contained math exposition with Lean
cross-references (declaration name → file:line), styled like a blueprint.

Scaffold:
```
typst/
├── main.typ          (imports, notation, macros for Lean refs)
├── 1-locales.typ     (frames, nuclei, sublocales — Sublocale.lean, Nucleus.lean)
├── 2-topology.typ    (openNhds/nhds, interior/closure/boundary/exterior — Further_Topology.lean)
├── 3-measure.typ     (measures on sublocales, regularity — Measure/*.lean, Lermes 1–5)
├── 4-extension.typ   (Carathéodory extension, µ-reduction, Lemme 6–7, main theorems)
└── appendix.typ      (auto-generated declaration index: name → file:line)
```
Steps: scaffold files → write sections with `#leanref[...]`-style links to the
Lean declarations (use the mapping table above) → `typst compile` → visually
review PDF → commit.

## Key commands

```sh
lake build                          # full; must be error- AND warning-free
lake build Leroy.Measure.Reduction  # single target
python3 scripts/lean_goal.py Leroy/Measure/Reduction.lean --line N --column C
lake env lean /tmp/axcheck2.lean    # axiom check (recreate if /tmp was wiped:
                                    # import Leroy, #print axioms of the two
                                    # capstone theorems)
```
