---
bibkey: fampalee2018sparse
authors: "Marcia Fampa and Jon Lee"
year: 2018
title: "On Sparse Reflexive Generalized Inverses"
doi: null
url: https://arxiv.org/abs/1807.03074v1
claim: "Embedding the inverse of any rank-sized nonsingular submatrix in a zero matrix gives a reflexive generalized inverse of a real rectangular matrix."
strata_touched:
  - D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse
license: citation-only
triage: anchor
---

# A selected-minor generalized inverse

Fampa and Lee, arXiv:1807.03074v1, 9 July 2018, printed page 2,
Theorem 5. The matrix is real, with arbitrary rectangular dimensions and
rank $r$. The theorem embeds the inverse of any nonsingular $r$-by-$r$
submatrix into the corresponding transposed positions of a zero matrix.
The resulting $H$ satisfies $AHA=A$ and $HAH=H$. Its proof identifies the
remaining block with the Schur complement using the rank of $A$.

The integer theorem in `IntegerMatrixInnerInverse` is a transfer and
synthesis, not a verbatim formalization of this real theorem. Total
unimodularity makes a nonzero selected determinant a unit in the integers.
Finite maximality and bordered determinants then establish the global
reconstruction without casting to a field or assuming a rank formula.
The Lean statement asserts only $ABA=A$. It claims neither Moore–Penrose
conditions, support optimality, norm optimality, nor originality.

## Library boundary

Pinned Mathlib provides `Matrix.IsTotallyUnimodular`,
`Matrix.invertibleOfIsUnitDet`, and `Matrix.det_fromBlocks₁₁`. Its
Schur-complement factorization and rectangular Smith-normal-form APIs
do not themselves give the selected-unit-minor reconstruction used here.
The project endpoint-incidence theorem is an immediate potential
consumer; no application-only companion is added.

Ivan-Sergeyev/seymour, commit
`2769b10cb73fda17bafc0f13890dc057a2f4ff2a`,
`Seymour/Matrix/Pivoting.lean`, contains field-valued TU-preserving
long and short tableau pivots and determinant transfer. Those results
are not reproduced. Its Lean 4.18 compatibility and admission into the
Lean 4.33 project are unverified; it is not a dependency of this proof.

Vilin97/lean-pool, commit
`bfe57c879e965dbc30cecd8150ff522cfdb287d9`,
`LeanPool/ErdosGinzburgZiv/EGZ/Balanced/RationalApproximation.lean`,
provides `EGZ.BalancedCombination.exists_matrix_generalized_inverse` over
the rationals. The sibling `Expansion/AffineRelations.lean` theorem
`EGZ.Expansion.exists_integer_generalized_inverse` gives an integer matrix $M$ and
positive integer $N$ with $AMA=N A$. This does not set $N=1$ under TU.
Neither field-valued existence nor clearing denominators establishes
the integral reconstruction needed here. These files are not vendored.

## Verified locator

- https://arxiv.org/pdf/1807.03074v1, printed page 2, Theorem 5.
