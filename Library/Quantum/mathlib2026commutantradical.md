---
bibkey: mathlib2026commutantradical
authors: The mathlib community
year: 2026
title: Artinian Jacobson radicals and the positive matrix trace pairing
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean
claim: Artinian rings have nilpotent Jacobson radicals; nilpotent matrices have nilpotent trace and the complex matrix trace pairing detects zero.
strata_touched:
  - D5/S3/Quantum/Matrix/CommutantSemisimple
license: Apache-2.0
triage: anchor
---

# Unitary commutants and radicals

## Verified locator

The exact upstream locator is:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean

The pinned source was opened through GitHub's raw endpoint successfully.
`IsArtinianRing.isSemisimpleRing_iff_jacobson` characterizes semisimplicity by a zero
Jacobson radical, and the Artinian `IsSemiprimaryRing` instance makes the radical
nilpotent. In the same pinned tree, also opened through the raw endpoint:

- `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` contains
  `Matrix.isNilpotent_trace_of_isNilpotent`.
- `Mathlib/LinearAlgebra/Matrix/PosDef.lean` contains
  `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`.
- `Mathlib/Algebra/Star/Center.lean` contains `Set.star_mem_centralizer'`.
- `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean` contains
  `Matrix.GeneralLinearGroup.upperRightHom`, the shear character.
- `Mathlib/RingTheory/Jacobson/Ideal.lean` contains `Ideal.mem_jacobson_iff`.

These sources supply the algebraic and trace ingredients; they do not state the
complete unitary-commutant theorem. For a radical element X in an adjoint-closed
complex matrix subalgebra, X-adjoint times X remains in the radical and has zero
trace. The positive trace pairing forces X to vanish. A unitary representation
has an adjoint-closed image because adjoints represent inverses, so its commutant
is adjoint-closed as well. The group need not be finite or compact.

The integer shear representation has commutant consisting of matrices with rows
(a,b) and (0,a). The upper-right matrix unit is nonzero and lies in the Jacobson
radical by the left-inverse criterion. This algebra is not semisimple. Its exact
matrix characterization and nonzero radical suffice to refute semisimplicity
without unitarity; no quotient presentation of the dual numbers is needed.
