/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedParityProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedParityProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A singular weighted Huang defect bounds the product of the parity row caps from below. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile

/-! Independent weighted row bounds for the two parity sides of an actual component. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct

open scoped BigOperators Matrix Matrix.Norms.Operator
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open BalancedCubeComponentBoundary (directions)
open Q9ComponentSaturation (componentDefect componentDefect_det_eq componentParityFinset)
open Q9WeightedBoundaryGram (signed signed_transpose)
open Q9WeightedSaturation (defect)
open private signed_row_le operator_norm_le_of_rows from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile

open Classical in
/-- A singular component defect forces the independent weighted row caps of
the two parity sides to have product at least the squared norm of the weights. -/
theorem sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero
    (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (w : Fin 9 → ℝ) (hw : ∀ i, 0 ≤ w i) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrows : ∀ x ∈ componentParityFinset U b C,
      ∑ i ∈ directions (componentParityFinset U (!b) C) x, w i ≤ r)
    (hcols : ∀ y ∈ componentParityFinset U (!b) C,
      ∑ i ∈ directions (componentParityFinset U b C) y, w i ≤ s)
    (hdet : (componentDefect w U b C).det = 0) :
    ∑ i, w i ^ 2 ≤ r * s := by
  classical
  let S := componentParityFinset U b C
  let T := componentParityFinset U (!b) C
  let M := (signed w).submatrix (fun x : ↥S => x.val) (fun y : ↥T => y.val)
  have hrow (P : Finset (Q 9)) (x : Q 9) :
      ∑ y : ↥P, |signed w x y.val| ≤ ∑ i ∈ directions P x, w i := by
    rw [← Finset.sum_subtype P (fun _ => Iff.rfl) (fun y => |signed w x y|)]
    exact signed_row_le w hw P x
  have hM : ‖M‖ ≤ r :=
    operator_norm_le_of_rows M hr fun x => (hrow T x.val).trans (hrows x.val x.property)
  have hMt : ‖Mᵀ‖ ≤ s := by
    apply operator_norm_le_of_rows _ hs
    intro y
    have hsym (x : ↥S) : Mᵀ y x = signed w y.val x.val :=
      congrFun (congrFun (signed_transpose w) y.val) x.val
    simp_rw [hsym]
    exact (hrow S y.val).trans (hcols y.val y.property)
  rw [componentDefect_det_eq] at hdet
  change (defect w M).det = 0 at hdet
  obtain ⟨u, hu, he⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := defect w M)).mpr hdet
  rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at he
  have hweight : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm := Matrix.linfty_opNorm_mulVec (M * Mᵀ) u
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight] at hnorm
  have hprod : ‖M * Mᵀ‖ ≤ r * s :=
    (Matrix.linfty_opNorm_mul M Mᵀ).trans (mul_le_mul hM hMt (norm_nonneg _) hr)
  exact le_of_mul_le_mul_right
    (hnorm.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg u))) (norm_pos_iff.mpr hu)

#print axioms sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct
