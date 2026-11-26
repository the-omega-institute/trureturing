/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Both parities of a fixed saturated component pair satisfy the minimum displacement bound. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCompanions
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-! Weighted support on both parities for the components in the 258-vertex
subcubic branch of Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9BoundaryGram (Interior)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedBoundaryGram (signed signed_transpose)
open Q9WeightedSaturation (Rows defect signedBiadjacency)
open TwoBalancedComponents (componentFinset)
open Translation.Q9ActualAperiodicity
  (exists_two_aperiodic_components signed_defect_det_eq_component)
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open private exists_parity_supported_of_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCompanions

private def rowsEquivInterior (C : Finset (Q 9)) {b c : Bool} (h : b = !c) :
    Rows C b ≃ Interior C c where
  toFun x := ⟨⟨x.val.val, by
    have hx : parity x.val.val = !c := (Finset.mem_filter.mp x.property).2.trans h
    exact (Bool.not_eq_iff.mp hx.symm).symm⟩, x.val.property⟩
  invFun y := ⟨⟨y.val.val, y.property⟩, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Bool.eq_not_of_ne y.val.property).trans h.symm⟩⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (Subtype.ext rfl)

open Classical in
/-- A nonzero Gram eigenvalue is preserved when the retained parity is reversed. -/
private theorem signed_defect_singular_opposite
    (C : Finset (Q 9)) (b : Bool) (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i)
    (hdet : (defect w (signedBiadjacency w C b)).det = 0) :
    (defect w (signedBiadjacency w C (!b))).det = 0 := by
  let M := signedBiadjacency w C b
  have hq : (∑ i, w i ^ 2) ≠ 0 :=
    (Finset.sum_pos (fun i _ => pow_pos (hw i) 2) Finset.univ_nonempty).ne'
  have hker : ∃ u ≠ 0, defect w M *ᵥ u = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨u, hu, hMu⟩ := hker
  rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hMu
  have heig := (sub_eq_zero.mp hMu).symm
  have ht : (defect w Mᵀ).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨Mᵀ *ᵥ u, ?_, ?_⟩
    · intro hzero
      rw [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero] at heig
      apply hu
      funext x
      have hx : (∑ i, w i ^ 2) * u x = 0 := by
        simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using congrFun heig.symm x
      exact (mul_eq_zero.mp hx).resolve_left hq
    · rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.transpose_transpose, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec u M Mᵀ, heig, Matrix.mulVec_smul, sub_self]
  let e := rowsEquivInterior C (b := !b) (c := b) rfl
  let f := (rowsEquivInterior C (b := b) (c := !b) (by cases b <;> rfl)).symm
  have hop : signedBiadjacency w C (!b) = (Mᵀ).submatrix e f := by
    ext i j
    change signed w i.val.val j.val.val = signed w j.val.val i.val.val
    exact congrFun (congrFun (signed_transpose w) j.val.val) i.val.val
  calc
    (defect w (signedBiadjacency w C (!b))).det = ((defect w Mᵀ).submatrix e e).det := by
      rw [hop]
      apply congrArg Matrix.det
      symm
      unfold defect
      change (∑ i, w i ^ 2) • (1 : Matrix (Interior C b) (Interior C b) ℝ).submatrix e e -
        (Mᵀ * (Mᵀ)ᵀ).submatrix e e = _
      rw [Matrix.submatrix_one_equiv, ← Matrix.submatrix_mul_equiv Mᵀ (Mᵀ)ᵀ e f e,
        Matrix.transpose_submatrix Mᵀ e f]
    _ = (defect w Mᵀ).det := Matrix.det_submatrix_equiv_self e _
    _ = 0 := ht

open Classical in
/-- A connected balanced cubic support with singular signed defect on `false`
has exact ambient support on either parity, with weighted image inside the support. -/
private theorem exists_both_parity_supported_of_signed_defect_singular
    (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C) (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i)
    (hdet : (defect w (signedBiadjacency w C false)).det = 0) :
    ∀ b : Bool, ∃ f : Q 9 → ℝ, (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear w f x = 0) := by
  intro b
  cases b
  · exact exists_parity_supported_of_singular C false hr hc hb w hw hdet
  · exact exists_parity_supported_of_singular C true hr hc hb w hw
      (signed_defect_singular_opposite C false w hw hdet)

open CubicContactDistance (closest_pair_distance_add_five_le)
open Q9MinimumDistanceOperator (minimumDisplacements minimum_displacements_card_and_equality)
open TwoBalancedComponents (componentFinset_subset)
open private componentFinset_nonempty componentFinset_disjoint componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

open Classical in
/-- A hypothetical subcubic `258`-set in Hong–Wu–Xia Problem 2 contains two
actual components at distance `d ∈ {2, 3, 4}`. On each starting parity that
realizes distance `d`, there are at least `(d + 2).choose 2` displacements.
Equality gives all `d`-subsets of one `d + 2`-axis set. -/
theorem exists_two_components_with_minimum_displacement_bound
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧
      let C := componentFinset U K
      let D := componentFinset U L
      ∃ d : ℕ, 2 ≤ d ∧ d ≤ 4 ∧
        (∀ x ∈ C, ∀ y ∈ D, d ≤ hammingDist x y) ∧
        (∃ x ∈ C, ∃ y ∈ D, hammingDist x y = d) ∧
        ∀ b, (minimumDisplacements C D b d).Nonempty →
          (d + 2).choose 2 ≤ (minimumDisplacements C D b d).card ∧
          ((minimumDisplacements C D b d).card = (d + 2).choose 2 →
            ∃ A : Finset (Fin 9), A.card = d + 2 ∧
              minimumDisplacements C D b d = A.powersetCard d) := by
  obtain ⟨K, L, hKL, hcomponents⟩ := exists_two_aperiodic_components U hU hdeg
  let C := componentFinset U K
  let D := componentFinset U L
  obtain ⟨hc, hbC, hdetC, _⟩ := hcomponents K (Or.inl rfl)
  obtain ⟨hd, hbD, hdetD, _⟩ := hcomponents L (Or.inr rfl)
  obtain ⟨⟨x, y⟩, hxy, hmin⟩ := Finset.exists_min_image (C.product D)
    (fun p => hammingDist p.1 p.2)
    ((componentFinset_nonempty U K).product (componentFinset_nonempty U L))
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  have hsep (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v :=
    hmin (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩)
  have hdisj : Disjoint C D := componentFinset_disjoint U K L hKL
  have hzero : hammingDist x y ≠ 0 := fun h =>
    Finset.disjoint_left.mp hdisj ((hammingDist_eq_zero.mp h) ▸ hx) hy
  have hone : hammingDist x y ≠ 1 := fun h =>
    Finset.disjoint_left.mp hdisj
      (componentFinset_neighbor_closed U K x hx y (componentFinset_subset U L hy) h) hy
  have hhigh : hammingDist x y + 5 ≤ 9 :=
    closest_pair_distance_add_five_le hc hd hbC hx hy hsep
  refine ⟨K, L, hKL, hammingDist x y, by omega, by omega, hsep, ⟨x, hx, y, hy, rfl⟩, ?_⟩
  intro b hne
  apply minimum_displacements_card_and_equality C D b (hammingDist x y) (by omega) hsep hne
  · intro i
    let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by
      dsimp only [w]
      split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hc
      (component_connected U K) hbC w hw
      ((signed_defect_det_eq_component w U false K).trans (hdetC w)) b
  · intro c
    let w : Fin 9 → ℝ := fun _ => 1
    exact exists_both_parity_supported_of_signed_defect_singular D hd
      (component_connected U L) hbD w (fun _ => by norm_num [w])
      ((signed_defect_det_eq_component w U false L).trans (hdetD w)) c

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
