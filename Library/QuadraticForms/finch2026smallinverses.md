---
bibkey: finch2026smallinverses
authors: Steven Finch
year: 2026
title: "Small Matrices with Small Inverses: Unimodular Zerofree Cases"
doi: 10.48550/arXiv.2605.03691
url: https://arxiv.org/abs/2605.03691v4
claim: "Conjecture 4 asserts that no order-six unimodular zerofree integer matrix has both entrywise absolute maxima equal to three."
strata_touched:
  - D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation
license: citation-only
triage: anchor
---

# Finch's order-six zerofree conjecture

## Verified locator

DOI: 10.48550/arXiv.2605.03691

Source: https://arxiv.org/abs/2605.03691v4

The source is version 4, Section 5, Conjecture 4, printed and PDF page 7.
The definitions below occur in the introduction, printed pages 1–2.

## Source statements

> An n×n integer matrix M with determinant ±1 is called **unimodular**. Let α=‖M‖ and β=‖M⁻¹‖, the maximum absolute entry of M and M⁻¹, respectively.

> The matrix M is called **zerofree** if none of the entries in M and none of the entries in M⁻¹ are zero. (Involving both matrices in this definition is somewhat unorthodox.) Our interest is in unimodular zerofree matrices for which both α and β are small.

> *Conjecture 4*. No 6×6 matrices exist that are tied to α=β=3.

The source identifies matrices with their orbits under independent signed
row and column permutations. These operations preserve the determinant's
absolute value, the nonzero-entry conditions for the matrix and its inverse,
and both entrywise maxima. Existence can therefore be expressed over all
integer matrices without selecting the source's canonical representative.

## Formal expression and scope

The carrier is `Matrix (Fin 6) (Fin 6) ℤ`, with zero-based indices.
Unimodularity is `IsUnit M.det`, equivalent over the integers to determinant
one or minus one. Both entrywise maxima are the finite supremum of
`Int.natAbs` over `Fin 6 × Fin 6`. Both nonzero conditions are retained.
Mathlib's nonsingular matrix inverse is a genuine integral inverse under
the determinant-unit hypothesis. The public `claim` uses
`IntegerMatrix`, `Unimodular`, `Zerofree`, `alpha` and `beta` as displayed
in the Scribe and fixed by preregistration.

The order-six counterexample and its certificate proof are derived in the
repository. The source supplies the definitions and conjecture, rather than
the refutation. The symbolic balanced-sign family, exhaustive orbit counts,
odd-dimensional nonexistence questions and the separate case α=β=2 remain
outside this module's conclusion. The source's subsequent discussion does
not use Conjecture 4 as a premise of a proved theorem.

## Evidence and literature boundary

Preregistration: https://github.com/the-omega-institute/trureturing/issues/25882.
Its literature screen found no settlement in the inspected sources;
completeness of citation discovery and any priority claim remain
`ASSUMED-UNVERIFIED`. No journal version was identified in that screen.

The independent exact-arithmetic checker is in
`the-omega-institute/trureturing-experiments`, commit
`e7dc91fabb9838f81fc0f1efce16280247300b94`, at
`docs/reports/finch-unimodular-zerofree-six/check.py`, SHA-256
`74a048acaefd7a7dfb3f311adbba2e45e98c6586c2f33d152c88b6628ca84bb4`.
The recorded command is
`python3 docs/reports/finch-unimodular-zerofree-six/check.py`;
the issue records exit 0 and final output `ALL_CHECKS_OK`.
These finite computations are distinct from the Lean theorem.

This note is citation-only and retains no source archive or program text.
