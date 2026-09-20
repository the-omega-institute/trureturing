---
bibkey: kawazumi2025wolpert
authors: Nariya Kawazumi
year: 2025
title: A topological proof of Wolpert's formula for the Weil-Petersson symplectic form in terms of the Fenchel-Nielsen coordinates
doi: 10.1007/s10711-025-01016-3
url: https://arxiv.org/abs/2408.04937v2
claim: A topological proof expresses the Weil-Petersson symplectic form in length and twist coordinates, with an explicit sign convention.
strata_touched:
  - D5/S3/Quantum/Entanglement/GeometricDynamicsSources
license: citation-only
triage: anchor
---

# Wolpert formula and coordinate conventions

## Verified source

Geometriae Dedicata 219, article 56 (2025), published 26 May 2025. Primary publisher text: https://link.springer.com/article/10.1007/s10711-025-01016-3 . Introduction, equation (1), uses the sum of d(twist) wedge d(length). Section 6 discusses the normalization relative to the trace Atiyah-Bott-Goldman form.

## Use and boundary

The formula itself is due to Wolpert; Kawazumi supplies a new proof. The RT geometric-dynamics convention uses the negative of this article's twist coordinate to write d(length) wedge d(twist). This sign change must be carried into Hamilton equations. The closed-surface theorem is not by itself a proof about variable boundary lengths; fixed geodesic boundary leaves are separately supported by Do's work. No quantum-to-gravity dictionary follows from this formula.

## Search log

2026-09-20: inspected the primary publisher introduction and equation (1), and arXiv v2 metadata. This check exposed and resolved an implicit twist-sign convention in the previously uncommitted RT addition. No global novelty claim or Lean verification.
