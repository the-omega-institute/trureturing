---
bibkey: rossetti2025observational
authors: L. Rossetti; S. Mancini; A. Winter; J. Schindler
year: 2025
title: Observational entropy of quantum correlations and entanglement
doi: 10.1109/TIT.2026.3700031
url: https://arxiv.org/abs/2510.10058v1
claim: "The membership of the optimal three-qubit W-state PPT POVM in SEP is posed as an open question."
strata_touched:
  - D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1109/TIT.2026.3700031

Source: https://arxiv.org/abs/2510.10058v1

The cited text is arXiv v1, Sections IX and X.0.4, equations (62), (79), and (83),
printed pages 17, 22, and 23. The IEEE journal text has not been verified.

## Source statements

Page 17, immediately after equation (62):

> In other words, the POVM elements are proportional to separable states.

Page 22:

> the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|

Page 23:

> Proving that (M′, 𝟙 − M′) belongs to the SEP class—i.e., showing that both M′ and 𝟙 − M′ are fully separable—would yield an analytic value for E_SEP(W₃) as well.

> Nevertheless, none of the tests conducted so far have succeeded in detecting entanglement, leaving open the question of whether (M′, 𝟙 − M′) belongs to the SEP class.

The three-qubit basis is indexed by functions `Fin 3 → Fin 2`, listing the three
bits in their site order. The operator M′ has coefficients
`t₂ = 1/2, t₃ = t₄ = 0, t₅ = 2/3, t₆ = 1/12` in equation (83).
The corresponding Lean result refutes membership of this particular two-outcome
measurement in SEP. It does not determine the optimal SEP observational entropy.

## Evidence boundary

The exact-arithmetic experiment is in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/e9a7bd12bab621fac9aa726605def50b3ecab0e5/docs/reports/rossetti-mancini-winter-schindler-2025-w3-ppt-measurement-not-separable).
Its `check.py` SHA-256 is
`0f67cf8ea123698ede88939d2587f06c93af4e49b152631a40e04528acb29659`;
`python3 check.py` exits 0 with `RESULT PASS 0` as reported in issue #19016.
Its checks of the complementary operator and its partial transposes being positive,
and of a separable decomposition of M′, are computed evidence, distinct from the
Lean refutation. Literature-screen completeness and the journal version's question
status are ASSUMED-UNVERIFIED.
