/- GID: D5/S3/Arith/Lattices/ExactDualLatticeFormula
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/ExactDualLatticeFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The dual lattice of Lambda^2 A4 is exactly its one-fifth Hodge image. -/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/- Library-search audit trail (2026-08-28):
   * Repository searches found no existing integral dual-lattice declaration or theorem covering
     the displayed six-dimensional Gram and Hodge matrices.
   * Pinned Mathlib's `LinearMap.BilinForm.dualSubmodule_span_of_basis` exactly supplies the
     structural dual-lattice step and is applied below.
   * Loogle, LeanSearch, Reservoir, and GitHub ecosystem searches found Mathlib's declaration and
     third-party wrappers, but no theorem for these concrete `G` and `J` matrices.
-/

namespace D5.S3.Arith.Lattices.ExactDualLatticeFormula

open LinearMap (BilinForm)
open Module Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Coordinate indices for the ordered basis
`u12, u13, u14, u23, u24, u34` of `Lambda^2 A4`. -/
abbrev LatticeIndex := Fin 6

/-- The real scalar extension `L tensor R` in the source's chosen basis. -/
abbrev AmbientSpace := LatticeIndex → ℝ

/-- The chosen ordered real basis. -/
noncomputable def chosenBasis : Basis LatticeIndex ℝ AmbientSpace :=
  Pi.basisFun ℝ LatticeIndex

/-- The integral Gram matrix displayed immediately before the source theorem. -/
def integralGramMatrix : Matrix LatticeIndex LatticeIndex ℤ :=
  !![3, 1, 1, -1, -1, 0;
     1, 3, 1, 1, 0, -1;
     1, 1, 3, 0, 1, 1;
     -1, 1, 0, 3, 1, -1;
     -1, 0, 1, 1, 3, 1;
     0, -1, 1, -1, 1, 3]

/-- The Gram matrix acting on the real scalar extension. -/
def gramMatrix : Matrix LatticeIndex LatticeIndex ℝ :=
  integralGramMatrix.map (Int.castRingHom ℝ)

/-- The integral Hodge discriminant matrix `J` from the source. -/
def integralHodgeMatrix : Matrix LatticeIndex LatticeIndex ℤ :=
  !![0, 1, -1, 1, -1, -3;
     -1, 0, 1, 1, 3, 1;
     1, -1, 0, -3, -1, 1;
     -1, -1, -3, 0, -1, -1;
     1, 3, 1, 1, 0, -1;
     -3, -1, -1, 1, 1, 0]

/-- The Hodge discriminant matrix acting on the real scalar extension. -/
def hodgeMatrix : Matrix LatticeIndex LatticeIndex ℝ :=
  integralHodgeMatrix.map (Int.castRingHom ℝ)

/-- The source endomorphism `J / 5` on the real scalar extension. -/
noncomputable def oneFifthHodgeMatrix : Matrix LatticeIndex LatticeIndex ℝ :=
  (1 / 5 : ℝ) • hodgeMatrix

/-- The Gram pairing in the chosen basis. -/
def gramForm : BilinForm ℝ AmbientSpace :=
  Matrix.toBilin' gramMatrix

/-- The lattice `L = Lambda^2 A4`, represented in its chosen basis by the integer span. -/
noncomputable def lattice : Submodule ℤ AmbientSpace :=
  Submodule.span ℤ (Set.range chosenBasis)

/-- The exact source definition
`L# = {y in L tensor R | <y, L> is contained in Z}`. -/
noncomputable def dualLattice : Submodule ℤ AmbientSpace :=
  gramForm.dualSubmodule lattice

/-- The `Z`-linear endomorphism induced by `J / 5`. -/
noncomputable def oneFifthHodgeMap : AmbientSpace →ₗ[ℤ] AmbientSpace :=
  (Matrix.mulVecLin oneFifthHodgeMatrix).restrictScalars ℤ

/-- The right-hand side `(J / 5)L` as the linear image of the lattice. -/
noncomputable def oneFifthHodgeLattice : Submodule ℤ AmbientSpace :=
  lattice.map oneFifthHodgeMap

set_option maxHeartbeats 1000000 in
-- Kernel reduction of the closed six-by-six determinant needs larger local resource bounds.
set_option maxRecDepth 10000 in
-- The determinant decision procedure recursively unfolds the six finite dimensions.
private lemma integralGramMatrix_det : integralGramMatrix.det = 125 := by
  decide

private lemma gramForm_nondegenerate : gramForm.Nondegenerate := by
  apply BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change (integralGramMatrix.map fun x : ℤ => (x : ℝ)).det ≠ 0
  rw [← Int.cast_det, integralGramMatrix_det]
  norm_num

set_option maxHeartbeats 1000000 in
-- Expanding all 36 concrete dual-basis coordinates needs more than the default budget.
private lemma oneFifthHodge_basis_eq_signed_dual (i : LatticeIndex) :
    oneFifthHodgeMap (chosenBasis i) =
      ![-(gramForm.dualBasis gramForm_nondegenerate chosenBasis 5),
        gramForm.dualBasis gramForm_nondegenerate chosenBasis 4,
        -(gramForm.dualBasis gramForm_nondegenerate chosenBasis 3),
        -(gramForm.dualBasis gramForm_nondegenerate chosenBasis 2),
        gramForm.dualBasis gramForm_nondegenerate chosenBasis 1,
        -(gramForm.dualBasis gramForm_nondegenerate chosenBasis 0)] i := by
  apply (gramForm.dualBasis gramForm_nondegenerate chosenBasis).repr.injective
  ext k
  rw [BilinForm.dualBasis_repr_apply]
  fin_cases i <;> fin_cases k <;>
    norm_num [oneFifthHodgeMap, oneFifthHodgeMatrix, hodgeMatrix, integralHodgeMatrix,
      gramForm, gramMatrix, integralGramMatrix, chosenBasis, Matrix.toBilin'_apply,
      Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.single_apply, Finsupp.single_apply] <;> decide

private lemma span_oneFifthHodge_basis_eq_span_dualBasis :
    Submodule.span ℤ (Set.range fun i => oneFifthHodgeMap (chosenBasis i)) =
      Submodule.span ℤ
        (Set.range (gramForm.dualBasis gramForm_nondegenerate chosenBasis)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change oneFifthHodgeMap (chosenBasis i) ∈
      Submodule.span ℤ
        (Set.range (gramForm.dualBasis gramForm_nondegenerate chosenBasis))
    have dual_mem (j : LatticeIndex) :
        gramForm.dualBasis gramForm_nondegenerate chosenBasis j ∈
          Submodule.span ℤ
            (Set.range (gramForm.dualBasis gramForm_nondegenerate chosenBasis)) :=
      Submodule.subset_span (Set.mem_range_self j)
    rw [oneFifthHodge_basis_eq_signed_dual]
    fin_cases i
    · exact Submodule.neg_mem _ (dual_mem 5)
    · exact dual_mem 4
    · exact Submodule.neg_mem _ (dual_mem 3)
    · exact Submodule.neg_mem _ (dual_mem 2)
    · exact dual_mem 1
    · exact Submodule.neg_mem _ (dual_mem 0)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have image_mem (j : LatticeIndex) :
        oneFifthHodgeMap (chosenBasis j) ∈
          Submodule.span ℤ (Set.range fun k => oneFifthHodgeMap (chosenBasis k)) :=
      Submodule.subset_span (Set.mem_range_self j)
    fin_cases i
    · simpa [oneFifthHodge_basis_eq_signed_dual] using
        (Submodule.neg_mem _ (image_mem 5))
    · simpa [oneFifthHodge_basis_eq_signed_dual] using image_mem 4
    · simpa [oneFifthHodge_basis_eq_signed_dual] using
        (Submodule.neg_mem _ (image_mem 3))
    · simpa [oneFifthHodge_basis_eq_signed_dual] using
        (Submodule.neg_mem _ (image_mem 2))
    · simpa [oneFifthHodge_basis_eq_signed_dual] using image_mem 1
    · simpa [oneFifthHodge_basis_eq_signed_dual] using
        (Submodule.neg_mem _ (image_mem 0))

/-- **Exact dual-lattice formula.** For `L = Lambda^2 A4` in the source's chosen basis,
the integral-pairing dual lattice is exactly `(J / 5)L`. -/
theorem dual_lattice_eq_one_fifth_hodge_lattice :
    dualLattice = oneFifthHodgeLattice := by
  rw [dualLattice, lattice,
    gramForm.dualSubmodule_span_of_basis gramForm_nondegenerate chosenBasis]
  rw [oneFifthHodgeLattice, lattice, Submodule.map_span]
  have image_range :
      oneFifthHodgeMap '' Set.range chosenBasis =
        Set.range (fun i => oneFifthHodgeMap (chosenBasis i)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨chosenBasis i, ⟨i, rfl⟩, rfl⟩
  rw [image_range, span_oneFifthHodge_basis_eq_span_dualBasis]

-- Reverse probe: the public equality recovers the atom's integral-pairing consequence.
example (x : AmbientSpace) (hx : x ∈ oneFifthHodgeLattice) :
    ∀ y ∈ lattice, gramForm x y ∈ (1 : Submodule ℤ ℝ) := by
  have hxDual : x ∈ dualLattice := by
    rw [dual_lattice_eq_one_fifth_hodge_lattice]
    exact hx
  change x ∈ gramForm.dualSubmodule lattice at hxDual
  exact (BilinForm.mem_dualSubmodule gramForm).mp hxDual

-- Trivialization probe: the image contains a concrete nonzero vector, so it is not `{0}`.
example :
    oneFifthHodgeMap (chosenBasis 0) ∈ dualLattice ∧
      oneFifthHodgeMap (chosenBasis 0) ≠ 0 := by
  constructor
  · rw [dual_lattice_eq_one_fifth_hodge_lattice]
    exact ⟨chosenBasis 0, Submodule.subset_span (Set.mem_range_self 0), rfl⟩
  · intro hzero
    have hcoordinate := congrFun hzero 1
    norm_num [oneFifthHodgeMap, oneFifthHodgeMatrix, hodgeMatrix, integralHodgeMatrix,
      chosenBasis, Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at hcoordinate

#print axioms dual_lattice_eq_one_fifth_hodge_lattice

end D5.S3.Arith.Lattices.ExactDualLatticeFormula
