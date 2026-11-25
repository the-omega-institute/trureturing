/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A singular weighted Huang defect bounds a component's maximum weighted row. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Mathlib.Analysis.Matrix.Normed

/-! The signed block of an actual component gives a bound on its weighted directions. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile

open scoped BigOperators Matrix Matrix.Norms.Operator NNReal
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions)
open SupportedEigenSaturation (matrix_abs_of_adj)
open TwoBalancedComponents (componentFinset)
open Q9ComponentSaturation (componentDefect componentDefect_det_eq componentParityFinset)
open Q9IsotropicHuang (flipSign)
open Q9WeightedBoundaryGram (signed signed_transpose)
open Q9WeightedSaturation (defect)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private componentFinset_nonempty from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

private theorem signed_row_le (w : Fin 9 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (T : Finset (Q 9)) (x : Q 9) :
    ∑ y ∈ T, |signed w x y| ≤ ∑ i ∈ directions T x, w i := by
  classical
  calc
    _ ≤ ∑ y ∈ T, ∑ i, if flip x i = y then w i else 0 := by
      apply Finset.sum_le_sum
      intro y _
      unfold signed
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : flip x i = y
      · rw [ite_eq_left h, ite_eq_left h, abs_mul, abs_of_nonneg (hw i), flipSign_cast,
          matrix_abs_of_adj (flip_adj x i), mul_one]
      · simp [h]
    _ = _ := by
      rw [Finset.sum_comm, directions, Finset.sum_filter]
      simp only [Finset.sum_ite_eq]

private theorem operator_norm_le_of_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) {d : ℝ} (hd : 0 ≤ d) (h : ∀ i, ∑ j, |A i j| ≤ d) :
    ‖A‖ ≤ d := by
  rw [Matrix.linfty_opNorm_def]
  change _ ≤ ((⟨d, hd⟩ : ℝ≥0) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  change ((∑ j, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ d
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h i

open Classical in
/-- A singular weighted Huang defect forces an actual vertex whose incident
direction weights sum to at least the Euclidean norm of the weight vector. -/
theorem exists_weighted_row_of_componentDefect_det_eq_zero
    (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (w : Fin 9 → ℝ) (hw : ∀ i, 0 ≤ w i) (hdet : (componentDefect w U b C).det = 0) :
    ∃ x ∈ componentFinset U C,
      Real.sqrt (∑ i, w i ^ 2) ≤ ∑ i ∈ directions (componentFinset U C) x, w i := by
  classical
  let V := componentFinset U C
  let S := componentParityFinset U b C
  let T := componentParityFinset U (!b) C
  let M := (signed w).submatrix (fun x : ↥S => x.val) (fun y : ↥T => y.val)
  rw [componentDefect_det_eq] at hdet
  change (defect w M).det = 0 at hdet
  obtain ⟨u, hu, he⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := defect w M)).mpr hdet
  rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at he
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image V (fun y => ∑ i ∈ directions V y, w i)
    (componentFinset_nonempty U C)
  let d := ∑ i ∈ directions V x, w i
  have hd : 0 ≤ d := Finset.sum_nonneg fun i _ => hw i
  have hrows (P : Finset (Q 9)) (hP : P ⊆ V) (y : Q 9) (hy : y ∈ V) :
      ∑ z : ↥P, |signed w y z.val| ≤ d := by
    rw [← Finset.sum_subtype P (fun _ => Iff.rfl) (fun z => |signed w y z|)]
    refine (signed_row_le w hw P y).trans (le_trans ?_ (hmax y hy))
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => hw i)
    intro i hi
    exact (mem_directions V y i).mpr (hP ((mem_directions P y i).mp hi))
  have hS : S ⊆ V := Finset.filter_subset _ _
  have hT : T ⊆ V := Finset.filter_subset _ _
  have hM : ‖M‖ ≤ d :=
    operator_norm_le_of_rows M hd fun i => hrows T hT i.val (hS i.property)
  have hMt : ‖Mᵀ‖ ≤ d := by
    apply operator_norm_le_of_rows _ hd
    intro j
    convert hrows S hS j.val (hT j.property) using 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg abs (congrFun (congrFun (signed_transpose w) j.val) i.val)
  have hweight : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm := Matrix.linfty_opNorm_mulVec (M * Mᵀ) u
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight] at hnorm
  have hprod := (Matrix.linfty_opNorm_mul M Mᵀ).trans
    (mul_le_mul hM hMt (norm_nonneg _) hd)
  have hsquare : ∑ i, w i ^ 2 ≤ d ^ 2 :=
    le_of_mul_le_mul_right
      (hnorm.trans (mul_le_mul_of_nonneg_right (by simpa only [pow_two] using hprod)
        (norm_nonneg u))) (norm_pos_iff.mpr hu)
  exact ⟨x, hx, (Real.sqrt_le_iff).2 ⟨hd, hsquare⟩⟩

#print axioms exists_weighted_row_of_componentDefect_det_eq_zero

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
