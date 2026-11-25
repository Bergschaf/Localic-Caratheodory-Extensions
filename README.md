# Localic Caratheodory Extensions

This repository contains a formalization of localic measure theory – specifically, the Carathéodory extension of measure in the setting of locales. It builds on the foundational work in locale theory (nuclei, sublocales, and their intersections) and formalizes the main result from Olivier Leroy's paper:

**Théorie de la mesure dans les lieux réguliers. ou : Les intersections cachées dans le paradoxe de Banach-Tarski**  
[arXiv:1303.5631](https://arxiv.org/abs/1303.5631)

The key achievement of this project is the formal proof that the Carathéodory extension of measure on locales is both **strictly additive** and **μ-reducible**.

## Development

The repository is pinned to Lean 4.36.0 and Mathlib v4.36.0. Build it with
`lake build`. Agent-specific formalization guidance is in [`AGENTS.md`](AGENTS.md).

To inspect the current tactic goals at a source location, run:

```sh
python3 scripts/lean_goal.py Leroy/Sublocale.lean --line 202 --column 5
```

The helper uses Lean's language server, waits until the document has been
elaborated, and then queries the goal state at the given one-based line and
column.

The sublocale layer uses Mathlib's native set-like `Sublocale` and
`nucleusIsoSublocale`, with a small pointwise compatibility bridge for the
existing proofs. Open and closed sublocales now use the current nucleus
embedding API. Complement characterizations are proved through pointwise
nucleus evaluation, and preservation of closed arbitrary infima uses a direct
lower-bound argument rather than unfolding the old dual-nucleus representation.
The measure reduction is now built from its native nucleus, and neighborhood
arguments use the existing infimum-closure lemmas. Restricted strict
additivity reuses subadditivity, and the example proof delegates to the main
strict-additivity theorem instead of duplicating it.

---

## Overview

- **Locale Theory Foundations:**  
  The required locale theory (including nuclei, sublocales, and their intersections) has been formalized, providing the algebraic infrastructure needed for localic measure theory.

- **Carathéodory Extension in the Localic Setting:**  
  We extend a pre-measure defined on a locale to a measure on the entire locale. Unlike classical measure theory, in the point-free (localic) framework every subset becomes measurable, resolving classical paradoxes like Banach–Tarski through “hidden intersections.”

- **Main Result:**  
  The formalization shows that the Carathéodory extension is strictly additive and μ-reducible, meaning that it behaves well with respect to the intrinsic structure of locales.
