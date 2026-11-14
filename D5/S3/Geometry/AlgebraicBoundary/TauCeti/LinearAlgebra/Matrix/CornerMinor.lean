/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/LinearAlgebra/Matrix/CornerMinor
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/LinearAlgebra/Matrix/CornerMinor
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/LinearAlgebra/Matrix/CornerMinor.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.LinearAlgebra.Matrix.Congruence

/-!
# The corner minor of a doubly singular matrix

The *corner minor* of a square matrix `A` indexed by `Fin (n + 1)` is the determinant of the
submatrix obtained by deleting its last row and its last column, that is, the determinant of
`A.submatrix Fin.castSucc Fin.castSucc`. Unlike the determinant it is not a conjugation
invariant in general. It becomes one on a matrix that is annihilated on the right by a column
vector `u` and on the left by a row vector `w`, as soon as the conjugating matrix fixes `u` and
`w` as well and the last coordinates of `u` and `w` are units: this is
`Matrix.det_submatrix_castSucc_conj`.

The mechanism is that `u` and `w` give `A` a factorisation through the corner minor's own index
type `Fin n`: the identity with its last row replaced by `w` carries `A` into the image of the
inclusion `Fin n ↪ Fin (n + 1)`, and the identity with its last column replaced by `u` does the
same on the other side. A conjugation `A ↦ N * A * N⁻¹` by a matrix fixing `u` and `w` therefore
multiplies the corner minor by `N.det` on one side and by `N.det⁻¹` on the other.

The rectangular deletion and inclusion matrices and the row and column framing matrices are
recorded first under `[Zero R] [One R]`, followed by their interaction with matrix
multiplication under `[NonAssocSemiring R]`. The sparse Laplace expansions along the last row
and column, the description of the corner minor as an ordinary determinant after replacing the
last column by the last standard basis vector, and the conjugation invariance formula are
proved under `[CommRing R]`.

The intended source of such a matrix is `burau b - 1` for a braid `b`, where `u` is the all-ones
vector and `w` is the geometric vector `(1, t, …, t ^ n)`.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace Matrix

variable {n : ℕ} {R : Type*}

section ZeroOne

variable [Zero R] [One R]

/-! ### The two rectangular matrices that delete and restore the last coordinate -/

/-! ### The two square matrices built from the annihilating vectors -/

end ZeroOne

section NonAssocSemiring

variable [NonAssocSemiring R]

end NonAssocSemiring

variable [CommRing R]

/-- Laplace expansion along the last row of a matrix whose last row vanishes off the diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_row (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j, j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last n),
    Finset.sum_eq_single (Fin.last n) (fun j _ hj => by rw [h j hj]; ring) (by simp)]
  rw [Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

/-! ### Conjugation invariance of the corner minor -/

end Matrix
