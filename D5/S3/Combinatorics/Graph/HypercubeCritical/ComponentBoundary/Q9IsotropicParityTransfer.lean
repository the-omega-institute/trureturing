/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicParityTransfer
   generality: G
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Zero-block rank inequalities force parity agreement for separated Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary

/-! The two crossing zero blocks in a rank-128 parity matrix constrain which
parities can support kernel words on a separated cubic pair of total order 258. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicParityTransfer

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open Q9MixedBoundaryCollisions (Separated)
open Q9ParityFoldedBoundary (parity parityPart cubic_parityPart_card)

attribute [local instance] Classical.propDecidable

section MatrixRank

variable {K I J R S : Type*} [Field K] [Finite I] [Fintype J] [Fintype S]

/-- Across a zero block, the rank of the selected full rows plus the rank of the
selected full columns is bounded by the rank of the whole matrix. -/
theorem rank_add_rank_le_of_zero_block [Finite R] (M : Matrix I J K) (r : R → I) (s : S → J)
    (hzero : ∀ i j, M (r i) (s j) = 0) :
    (M.submatrix r id).rank + (M.submatrix id s).rank ≤ M.rank := by
  let V := Submodule.span K (Set.range M.row)
  let restrict := LinearMap.funLeft K K s
  let L := restrict.domRestrict V
  have hrange : LinearMap.range L = Submodule.span K (Set.range (M.submatrix id s).row) := by
    change LinearMap.range (restrict.domRestrict (Submodule.span K (Set.range M.row))) = _
    rw [LinearMap.range_domRestrict, Submodule.map_span, ← Set.range_comp]
    rfl
  have hrows : Submodule.span K (Set.range (M.submatrix r id).row) ≤
      (LinearMap.ker L).map V.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨M.row (r i), Submodule.subset_span ⟨r i, rfl⟩⟩, ?_, rfl⟩
    exact LinearMap.mem_ker.mpr (funext (hzero i))
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row,
    M.rank_eq_finrank_span_row, ← hrange]
  calc
    _ ≤ Module.finrank K ((LinearMap.ker L).map V.subtype) +
        Module.finrank K (LinearMap.range L) :=
      Nat.add_le_add_right (Submodule.finrank_mono hrows) _
    _ = Module.finrank K V := by
      rw [Submodule.finrank_map_subtype_eq, Nat.add_comm]
      exact L.finrank_range_add_finrank_ker

/-- The kernel of the column restriction, in the selected coordinates. For an
injective index map these are the ambient kernel words supported there, expressed
before zero extension. -/
def columnRestrictionKernel (M : Matrix I J K) (s : S → J) : Submodule K (S → K) :=
  LinearMap.ker (M.submatrix id s).mulVecLin

/-- The sum of the two mixed-side nullities is at least the excess of the
selected row and column counts over the ambient rank. -/
theorem card_le_rank_add_mixed_nullities [Fintype R] (M : Matrix I J K) (r : R → I) (s : S → J)
    (hzero : ∀ i j, M (r i) (s j) = 0) :
    Fintype.card R + Fintype.card S ≤ M.rank +
      (Module.finrank K (columnRestrictionKernel Mᵀ r) +
       Module.finrank K (columnRestrictionKernel M s)) := by
  have hrow := ((Mᵀ.submatrix id r).mulVecLin).finrank_range_add_finrank_ker
  have hcol := ((M.submatrix id s).mulVecLin).finrank_range_add_finrank_ker
  change (M.submatrix r id)ᵀ.rank +
    Module.finrank K (columnRestrictionKernel Mᵀ r) = Module.finrank K (R → K) at hrow
  change (M.submatrix id s).rank +
    Module.finrank K (columnRestrictionKernel M s) = Module.finrank K (S → K) at hcol
  rw [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card] at hrow
  rw [Module.finrank_fintype_fun_eq_card] at hcol
  have hrank := rank_add_rank_le_of_zero_block M r s hzero
  omega

end MatrixRank

section BoundaryImage

variable {K I J : Type*} [Field K] [Finite I] [Fintype J] [DecidableEq J]

private theorem finrank_map_add_finrank_inf_ker {E F : Type*}
    [AddCommGroup E] [Module K E] [Module.Finite K E] [AddCommGroup F] [Module K F]
    (V : Submodule K E) (f : E →ₗ[K] F) :
    Module.finrank K (V.map f) + Module.finrank K ↥(V ⊓ LinearMap.ker f) =
      Module.finrank K V := by
  have h := (f.domRestrict V).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, ← Submodule.finrank_map_subtype_eq,
    LinearMap.ker_domRestrict, Submodule.map_comap_eq, Submodule.range_subtype] at h
  exact h

/-- One component's boundary image fills the complementary code if its row-side
nullity and the other component's column-side nullity sum to one. For two pure
one-dimensional components of the same parity, swapping the components and
transposing give equality of both boundary images with the complementary code
on each parity. -/
theorem boundary_image_eq_complementary_code_of_mixed_nullity_one
    (B : Matrix I J K) (X : Finset I) (Y Z : Finset J)
    (hdisjoint : Disjoint Y Z) (hbalance : X.card = Y.card)
    (hsize : (Y ∪ Z).card = B.rank + 1)
    (hhalf : Fintype.card J = 2 * B.rank) (hsquare : B * Bᵀ = 0)
    (hcross : ∀ (x : X) (z : Z), B x z = 0)
    (hnull : Module.finrank K (columnRestrictionKernel Bᵀ (Subtype.val : X → I)) +
      Module.finrank K (columnRestrictionKernel B (Subtype.val : Z → J)) = 1) :
    let internal := B.submatrix (Subtype.val : X → I) (Subtype.val : Y → J)
    let ambient := Bᵀ.submatrix id (Subtype.val : X → I)
    (LinearMap.ker internalᵀ.mulVecLin).map ambient.mulVecLin =
      LinearMap.ker B.mulVecLin ⊓
        LinearMap.ker (LinearMap.funLeft K K (Subtype.val : ↥(Y ∪ Z) → J)) := by
  let _ : Fintype I := Fintype.ofFinite I
  let A := B.submatrix (Subtype.val : X → I) (Subtype.val : Y → J)
  let f := (Bᵀ.submatrix id (Subtype.val : X → I)).mulVecLin
  let P := LinearMap.funLeft K K (Subtype.val : ↥(Y ∪ Z) → J)
  let L := (LinearMap.ker Aᵀ.mulVecLin).map f
  let T := LinearMap.ker B.mulVecLin ⊓ LinearMap.ker P
  change L = T
  have hfull : LinearMap.range Bᵀ.mulVecLin = LinearMap.ker B.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, hsquare, Matrix.mulVecLin_zero]
    · have h := B.mulVecLin.finrank_range_add_finrank_ker
      change B.rank + Module.finrank K (LinearMap.ker B.mulVecLin) = _ at h
      rw [Module.finrank_fintype_fun_eq_card, hhalf] at h
      change _ ≤ Bᵀ.rank
      rw [Matrix.rank_transpose]
      omega
  have hLle : L ≤ T := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, LinearMap.mem_ker.mpr (funext fun j => ?_)⟩
    · rw [← hfull]
      have hsub : LinearMap.range f ≤ LinearMap.range Bᵀ.mulVecLin := by
        dsimp only [f]
        rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
        exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x.1, rfl⟩)
      exact hsub ⟨w, rfl⟩
    · rcases Finset.mem_union.mp j.2 with hj | hj
      · exact congrFun (LinearMap.mem_ker.mp hw) ⟨j.1, hj⟩
      · change ∑ x : X, B x j * w x = 0
        exact Finset.sum_eq_zero fun x _ => by rw [hcross x ⟨j.1, hj⟩, zero_mul]
  apply Submodule.eq_of_le_of_finrank_le hLle
  have hker : LinearMap.ker f ≤ LinearMap.ker Aᵀ.mulVecLin := by
    intro w hw
    exact LinearMap.mem_ker.mpr (funext fun y =>
      congrFun (LinearMap.mem_ker.mp hw) y.1)
  have hL := finrank_map_add_finrank_inf_ker (LinearMap.ker Aᵀ.mulVecLin) f
  rw [inf_eq_right.mpr hker] at hL
  change Module.finrank K L +
    Module.finrank K (columnRestrictionKernel Bᵀ (Subtype.val : X → I)) =
    Module.finrank K (LinearMap.ker Aᵀ.mulVecLin) at hL
  have hA := Aᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Aᵀ.rank + Module.finrank K (LinearMap.ker Aᵀ.mulVecLin) =
    Module.finrank K (X → K) at hA
  rw [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hA
  let M := B.submatrix id (Subtype.val : ↥(Y ∪ Z) → J)
  have hT := finrank_map_add_finrank_inf_ker (LinearMap.range Bᵀ.mulVecLin) P
  have hP : (LinearMap.range Bᵀ.mulVecLin).map P = LinearMap.range Mᵀ.mulVecLin := by
    rw [← LinearMap.range_comp]
    rfl
  rw [hP] at hT
  change Mᵀ.rank + Module.finrank K ↥(LinearMap.range Bᵀ.mulVecLin ⊓ LinearMap.ker P) =
    Bᵀ.rank at hT
  rw [hfull, Matrix.rank_transpose, Matrix.rank_transpose] at hT
  change M.rank + Module.finrank K T = B.rank at hT
  let inclZ : Z → ↥(Y ∪ Z) := fun z => ⟨z.1, Finset.mem_union_right Y z.2⟩
  have hbound := rank_add_rank_le_of_zero_block M (Subtype.val : X → I) inclZ hcross
  change (B.submatrix (Subtype.val : X → I) (Subtype.val : ↥(Y ∪ Z) → J)).rank +
    (B.submatrix id (Subtype.val : Z → J)).rank ≤ M.rank at hbound
  let inclY : Y → ↥(Y ∪ Z) := fun y => ⟨y.1, Finset.mem_union_left Z y.2⟩
  have hA_le := Matrix.rank_submatrix_le
    (B.submatrix (Subtype.val : X → I) (Subtype.val : ↥(Y ∪ Z) → J)) id inclY
  change A.rank ≤ (B.submatrix (Subtype.val : X → I) (Subtype.val : ↥(Y ∪ Z) → J)).rank
    at hA_le
  have hZ := ((B.submatrix id (Subtype.val : Z → J)).mulVecLin).finrank_range_add_finrank_ker
  change (B.submatrix id (Subtype.val : Z → J)).rank +
    Module.finrank K (columnRestrictionKernel B (Subtype.val : Z → J)) =
    Module.finrank K (Z → K) at hZ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hZ
  rw [Finset.card_union_of_disjoint hdisjoint] at hsize
  omega

end BoundaryImage

/-- The ambient vertices of a fixed global parity. -/
abbrev ParityVertices (p : Bool) := {x : Q 9 // parity x = p}

private def parityPartInclusion (C : Finset (Q 9)) (p : Bool) :
    ↥(parityPart C p) → ParityVertices p :=
  fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩

/-- Supported parity codewords in the coordinates of the component. The
even code uses the transpose of the matrix from odd to even coordinates. -/
def parityCode {K : Type*} [Field K]
    (B : Matrix (ParityVertices false) (ParityVertices true) K) (C : Finset (Q 9)) :
    (p : Bool) → Submodule K (↥(parityPart C p) → K)
  | false => columnRestrictionKernel Bᵀ (parityPartInclusion C false)
  | true => columnRestrictionKernel B (parityPartInclusion C true)

/-- At a fixed field specialization of the parity matrix, two separated
balanced cubic supports of total order 258 share a parity with a nonzero
supported codeword whenever each support has a nonzero word on some parity. -/
theorem exists_common_parity_codeword {K : Type*} [Field K]
    (B : Matrix (ParityVertices false) (ParityVertices true) K)
    (hrank : B.rank = 128)
    (hsupport : ∀ i j, ¬ (hypercube 9).Adj i.1 j.1 → B i j = 0)
    {C D : Finset (Q 9)} (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : ∃ p, ∃ w : parityCode B C p, w ≠ 0)
    (hD : ∃ p, ∃ w : parityCode B D p, w ≠ 0) :
    ∃ p, (∃ w : parityCode B C p, w ≠ 0) ∧ (∃ w : parityCode B D p, w ≠ 0) := by
  have hCcard : C.card = 6 * directionEdges C 0 := by
    simpa using (direction_edge_count (d := 3) C hrC hbC 0).symm
  have hDcard : D.card = 6 * directionEdges D 0 := by
    simpa using (direction_edge_count (d := 3) D hrD hbD 0).symm
  rw [Finset.card_union_of_disjoint hsep.1] at hcard
  have hCpart := cubic_parityPart_card hCcard hrC
  have hDpart := cubic_parityPart_card hDcard hrD
  have mixed {X Y : Finset (Q 9)}
      (hsize : (parityPart X false).card + (parityPart Y true).card = 129)
      (hcross : ∀ x ∈ X, ∀ y ∈ Y, ¬ (hypercube 9).Adj x y) :
      0 < Module.finrank K (parityCode B X false) +
          Module.finrank K (parityCode B Y true) := by
    have h := card_le_rank_add_mixed_nullities B (parityPartInclusion X false)
      (parityPartInclusion Y true) (fun x y =>
        hsupport _ _ (hcross x.1 (Finset.mem_filter.mp x.2).1 y.1
          (Finset.mem_filter.mp y.2).1))
    rw [Fintype.card_coe, Fintype.card_coe, hsize, hrank] at h
    exact Nat.lt_of_add_lt_add_left h
  have hCD := mixed (X := C) (Y := D) (by rw [hCpart, hDpart]; omega) hsep.2
  have hDC := mixed (X := D) (Y := C) (by rw [hDpart, hCpart]; omega)
    (fun y hy x hx hxy => hsep.2 x hx y hy hxy.symm)
  simp only [← Module.finrank_pos_iff_exists_ne_zero (R := K)] at hC hD ⊢
  rcases hC with ⟨_ | _, hC⟩ <;> rcases hD with ⟨_ | _, hD⟩
  · exact ⟨false, hC, hD⟩
  · by_cases h : 0 < Module.finrank K (parityCode B C true)
    · exact ⟨true, h, hD⟩
    · exact ⟨false, hC, by omega⟩
  · by_cases h : 0 < Module.finrank K (parityCode B C false)
    · exact ⟨false, h, hD⟩
    · exact ⟨true, hC, by omega⟩
  · exact ⟨true, hC, hD⟩

#print axioms rank_add_rank_le_of_zero_block
#print axioms card_le_rank_add_mixed_nullities
#print axioms boundary_image_eq_complementary_code_of_mixed_nullity_one
#print axioms exists_common_parity_codeword

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicParityTransfer
