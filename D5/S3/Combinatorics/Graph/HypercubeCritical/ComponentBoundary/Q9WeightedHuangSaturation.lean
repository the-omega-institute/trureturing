/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedHuangSaturation
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Any 258-point Q9 set supports two positive weighted Huang eigenvectors. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The signed coordinate actions yield two supported positive eigenvectors for
every choice of positive coordinate weights on a 258-vertex subset of Q9. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangSaturation

open scoped BigOperators
open BalancedCriticalSpectrum (Q gamma)
open BalancedCubeGirth (gamma_anticommute)
open Module.End (eigenspace mem_eigenspace_iff)
open private gamma_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
open private paritySign parityMultiply gamma_parityMultiply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactParity
open private outsideRestriction complement_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension

set_option autoImplicit false
noncomputable section

/-- The signed Huang operator with each cube direction scaled by its coordinate weight. -/
def weightedHuang {n : ℕ} (t : Fin n → ℝ) : Module.End ℝ (Q n → ℝ) :=
  ∑ i, t i • gamma i

/-- In the square of the weighted Huang operator, distinct directions cancel in pairs. -/
theorem weightedHuang_square {n : ℕ} (t : Fin n → ℝ) (z : Q n → ℝ) :
    weightedHuang t (weightedHuang t z) = (∑ i, t i ^ 2) • z := by
  let term (i j : Fin n) := (t i * t j) • gamma i (gamma j z)
  have hexpand : weightedHuang t (weightedHuang t z) = ∑ i, ∑ j, term i j := by
    change (∑ i, t i • gamma i) (weightedHuang t z) = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [show weightedHuang t z = ∑ j, t j • gamma j z by
      simp only [weightedHuang, LinearMap.sum_apply, LinearMap.smul_apply]]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, term]
  have hpair (i j : Fin n) : term i j + term j i =
      if j = i then (2 * t i ^ 2) • z else 0 := by
    by_cases h : j = i
    · subst j
      rw [ite_eq_left rfl]
      simp only [term, gamma_square, pow_two, ← add_smul, two_mul]
    · rw [ite_eq_right h]
      simp only [term, gamma_anticommute h z, smul_neg, mul_comm (t j) (t i), add_neg_cancel]
  apply smul_right_injective (M := Q n → ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  calc
    (2 : ℝ) • weightedHuang t (weightedHuang t z) = ∑ i, ∑ j, (term i j + term j i) := by
      simp only [hexpand, two_smul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => term j i)]
    _ = (2 : ℝ) • ((∑ i, t i ^ 2) • z) := by
      simp only [hpair, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        ← Finset.sum_smul, ← Finset.mul_sum, smul_smul]

private def parityMap : Module.End ℝ (Q 9 → ℝ) where
  toFun := parityMultiply
  map_add' z w := by
    funext x
    exact mul_add _ _ _
  map_smul' a z := by
    funext x
    change paritySign x * (a * z x) = a * (paritySign x * z x)
    exact mul_left_comm _ _ _

private theorem parityMap_involutive : Function.Involutive parityMap := by
  intro z
  funext x
  change paritySign x * (paritySign x * z x) = z x
  unfold paritySign
  split <;> simp_all

private theorem weightedHuang_parityMap (t : Fin 9 → ℝ) (z : Q 9 → ℝ) :
    weightedHuang t (parityMap z) = -parityMap (weightedHuang t z) := by
  have hcoord (i : Fin 9) : gamma i (parityMap z) = -parityMap (gamma i z) :=
    gamma_parityMultiply i z
  simp only [weightedHuang, LinearMap.sum_apply, LinearMap.smul_apply, hcoord,
    map_sum, map_smul, smul_neg, Finset.sum_neg_distrib]

private def parityEigenspaceEquiv (t : Fin 9 → ℝ) (r : ℝ) :
    eigenspace (weightedHuang t) r ≃ₗ[ℝ] eigenspace (weightedHuang t) (-r) := by
  have hmap (μ : ℝ) {z : Q 9 → ℝ} (hz : z ∈ eigenspace (weightedHuang t) μ) :
      parityMap z ∈ eigenspace (weightedHuang t) (-μ) := by
    rw [mem_eigenspace_iff, weightedHuang_parityMap, mem_eigenspace_iff.mp hz,
      map_smul, neg_smul]
  refine LinearEquiv.ofLinearMap
    ((parityMap.domRestrict _).codRestrict _ (fun z => hmap r z.property))
    ((parityMap.domRestrict _).codRestrict _ (fun z => by
      change parityMap z.val ∈ eigenspace (weightedHuang t) r
      simpa only [neg_neg] using (hmap (-r) z.property))) ?_ ?_
  all_goals
    ext z : 1
    exact Subtype.ext (parityMap_involutive z.val)

private theorem eigenspaces_isCompl (t : Fin 9 → ℝ) (r : ℝ) (hr : 0 < r)
    (hsq : r ^ 2 = ∑ i, t i ^ 2) :
    IsCompl (eigenspace (weightedHuang t) r) (eigenspace (weightedHuang t) (-r)) := by
  let H := weightedHuang t
  have hne : r ≠ 0 := hr.ne'
  refine ⟨H.disjoint_genEigenspace (show r ≠ -r by linarith) 1 1, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro z _
  have hHz : H (H z) = (r * r) • z := by
    rw [← pow_two, hsq]
    exact weightedHuang_square t z
  let u := r⁻¹ • H z
  have hu : H u = r • z := by
    have hcancel : r⁻¹ * (r * r) = r := by field_simp
    rw [show u = r⁻¹ • H z from rfl, map_smul, hHz, smul_smul, hcancel]
  have hz : H z = r • u := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  let p := (2 : ℝ)⁻¹ • (z + u)
  let m := (2 : ℝ)⁻¹ • (z - u)
  refine Submodule.mem_sup.mpr ⟨p, mem_eigenspace_iff.mpr ?_, m,
    mem_eigenspace_iff.mpr ?_, ?_⟩
  · change H p = r • p
    dsimp only [p]
    rw [map_smul, map_add, hu, hz, ← smul_add, add_comm u z, smul_comm]
  · change H m = (-r) • m
    dsimp only [m]
    rw [map_smul, map_sub, hu, hz, ← smul_sub, ← neg_sub z u, smul_neg, ← neg_smul, smul_comm]
  · dsimp only [p, m]
    rw [← smul_add, show z + u + (z - u) = z + z by abel, ← two_smul ℝ z,
      smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- The positive eigenspace on the full cube has dimension 256. -/
private theorem finrank_positive (t : Fin 9 → ℝ) (ht : ∀ i, 0 < t i) :
    Module.finrank ℝ (eigenspace (weightedHuang t) (Real.sqrt (∑ i, t i ^ 2))) = 256 := by
  have hq : 0 < ∑ i, t i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (ht i) _) Finset.univ_nonempty
  let r := Real.sqrt (∑ i, t i ^ 2)
  change Module.finrank ℝ (eigenspace (weightedHuang t) r) = 256
  have hpos : 0 < r := Real.sqrt_pos.2 hq
  have hsq : r ^ 2 = ∑ i, t i ^ 2 := Real.sq_sqrt hq.le
  have hsum := Submodule.finrank_add_eq_of_isCompl (eigenspaces_isCompl t r hpos hsq)
  have heq := (parityEigenspaceEquiv t r).finrank_eq
  have hdim : Module.finrank ℝ (Q 9 → ℝ) = 512 := by
    rw [Module.finrank_fintype_fun_eq_card, Sensitivity.Q.card]
    norm_num
  rw [hdim] at hsum
  omega

/-- The ambient positive eigenspace intersected with the functions vanishing outside `U`. -/
def supportedWeightedEigenSpace (t : Fin 9 → ℝ) (U : Finset (Q 9)) :
    Submodule ℝ (Q 9 → ℝ) :=
  eigenspace (weightedHuang t) (Real.sqrt (∑ i, t i ^ 2)) ⊓
    LinearMap.ker (outsideRestriction U)

/-- Any 258 vertices of Q9 support at least two independent eigenvectors at the weighted bound. -/
theorem two_le_finrank_supportedWeightedEigenSpace (t : Fin 9 → ℝ) (ht : ∀ i, 0 < t i)
    (U : Finset (Q 9)) (hU : U.card = 258) :
    2 ≤ Module.finrank ℝ (supportedWeightedEigenSpace t U) := by
  let E := eigenspace (weightedHuang t) (Real.sqrt (∑ i, t i ^ 2))
  let L := (outsideRestriction U).domRestrict E
  have hdim : Module.finrank ℝ E = 256 := finrank_positive t ht
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hdim] at hrank
  have hrange := (LinearMap.range L).finrank_le
  rw [Module.finrank_fintype_fun_eq_card, complement_card U hU] at hrange
  let inc : LinearMap.ker L →ₗ[ℝ] supportedWeightedEigenSpace t U :=
    (E.subtype.comp (LinearMap.ker L).subtype).codRestrict _ (fun z =>
      ⟨z.val.property, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp z.property)⟩)
  have hinc : Function.Injective inc := by
    intro z w h
    have hval : ((z.val : E) : Q 9 → ℝ) = ((w.val : E) : Q 9 → ℝ) :=
      congrArg (fun v : supportedWeightedEigenSpace t U => v.val) h
    exact Subtype.ext (Subtype.ext hval)
  have hle := LinearMap.finrank_le_finrank_of_injective hinc
  omega

end
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangSaturation
