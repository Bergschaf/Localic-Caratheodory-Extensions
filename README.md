# Localic Caratheodory Extensions

This repository contains a formalization of localic measure theory – specifically, the Carathéodory extension of measure in the setting of locales. It builds on the foundational work in locale theory (nuclei, sublocales, and their intersections) and formalizes the main result from Olivier Leroy's paper:

**Théorie de la mesure dans les lieux réguliers. ou : Les intersections cachées dans le paradoxe de Banach-Tarski**  
[arXiv:1303.5631](https://arxiv.org/abs/1303.5631)

The key achievement of this project is the formal proof that the Carathéodory extension of measure on locales is both **strictly additive** and **μ-reducible**.

---

## Overview

- **Locale Theory Foundations:**  
  The required locale theory (including nuclei, sublocales, and their intersections) has been formalized, providing the algebraic infrastructure needed for localic measure theory.

- **Carathéodory Extension in the Localic Setting:**  
  We extend a pre-measure defined on a locale to a measure on the entire locale. Unlike classical measure theory, in the point-free (localic) framework every subset becomes measurable, resolving classical paradoxes like Banach–Tarski through “hidden intersections.”

- **Main Result:**  
  The formalization shows that the Carathéodory extension is strictly additive and μ-reducible, meaning that it behaves well with respect to the intrinsic structure of locales.
