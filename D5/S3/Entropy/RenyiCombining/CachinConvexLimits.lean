/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexLimits
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite jets bound the square-root reparametrized slope and make its curvature negative. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexLimits

noncomputable def sqrtSlope (Q₁ : ℝ → ℝ) (z : ℝ) : ℝ :=
  Q₁ (Real.sqrt z) / (2 * Real.sqrt z)

noncomputable def sqrtCurvature (Q₁ Q₂ : ℝ → ℝ) (z : ℝ) : ℝ :=
  (Real.sqrt z * Q₂ (Real.sqrt z) - Q₁ (Real.sqrt z)) /
    (4 * (Real.sqrt z) ^ (3 : ℕ))

theorem sqrt_comp_hasDerivAt {Q Q₁ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hQ : HasDerivAt Q (Q₁ (Real.sqrt z)) (Real.sqrt z)) :
    HasDerivAt (fun x => Q (Real.sqrt x)) (sqrtSlope Q₁ z) z := by
  convert hQ.comp z (Real.hasDerivAt_sqrt hz.ne') using 1 <;>
    simp only [sqrtSlope, Function.comp_def, div_eq_mul_inv, one_mul]

theorem sqrtSlope_hasDerivAt {Q₁ Q₂ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hQ : HasDerivAt Q₁ (Q₂ (Real.sqrt z)) (Real.sqrt z)) :
    HasDerivAt (sqrtSlope Q₁) (sqrtCurvature Q₁ Q₂ z) z := by
  have ht := Real.sqrt_pos.mpr hz
  have hs := Real.hasDerivAt_sqrt hz.ne'
  convert (hQ.comp z hs).div (hs.const_mul 2) (by positivity : 2 * Real.sqrt z ≠ 0) using 1
  · rfl
  · dsimp [sqrtCurvature]
    field_simp [ht.ne']
    <;> ring

private theorem jet_signs_on_interval {Q₁ Q₂ Q₃ Q₄ : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (k : ℝ)
    (h₁ : ∀ t ∈ Icc 0 a, HasDerivAt Q₁ (Q₂ t) t)
    (h₂ : ∀ t ∈ Icc 0 a, HasDerivAt Q₂ (Q₃ t) t)
    (h₃ : ∀ t ∈ Icc 0 a, HasDerivAt Q₃ (Q₄ t) t)
    (h₁₀ : Q₁ 0 = 0) (h₃₀ : Q₃ 0 = 0) (h₂₀ : Q₂ 0 < 2 * k)
    (h₄neg : ∀ t ∈ Ioo 0 a, Q₄ t < 0) :
    ∀ t ∈ Ioo 0 a, Q₁ t < 2 * k * t ∧ t * Q₂ t - Q₁ t < 0 := by
  have hm₃ : StrictAntiOn Q₃ (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (h₃ t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(h₃ t ⟨ht.1.le, ht.2.le⟩).deriv]
        exact h₄neg t ht)
  have hQ₃ : ∀ t ∈ Ioo 0 a, Q₃ t < 0 := by
    intro t ht
    have h := hm₃ ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa only [h₃₀] using h
  have hm₂ : StrictAntiOn Q₂ (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (h₂ t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(h₂ t ⟨ht.1.le, ht.2.le⟩).deriv]
        exact hQ₃ t ht)
  have hQ₂ : ∀ t ∈ Icc 0 a, Q₂ t < 2 * k := by
    intro t ht
    exact lt_of_le_of_lt (hm₂.antitoneOn ⟨le_rfl, ha.le⟩ ht ht.1) h₂₀
  have hshift : ∀ t ∈ Icc 0 a,
      HasDerivAt (fun x => Q₁ x - 2 * k * x) (Q₂ t - 2 * k) t := by
    intro t ht
    convert (h₁ t ht).sub ((hasDerivAt_id t).const_mul (2 * k)) using 1
    · rfl
    · ring
  have hm₁ : StrictAntiOn (fun x => Q₁ x - 2 * k * x) (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (hshift t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [(hshift t (interior_subset ht)).deriv]
        exact sub_neg.mpr (hQ₂ t (interior_subset ht)))
  have hN : ∀ t ∈ Icc 0 a,
      HasDerivAt (fun x => x * Q₂ x - Q₁ x) (t * Q₃ t) t := by
    intro t ht
    convert ((hasDerivAt_id t).mul (h₂ t ht)).sub (h₁ t ht) using 1
    · rfl
    · dsimp
      ring
  have hmN : StrictAntiOn (fun x => x * Q₂ x - Q₁ x) (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (hN t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        have ht' : t ∈ Ioo 0 a := by simpa only [interior_Icc] using ht
        rw [(hN t (interior_subset ht)).deriv]
        exact mul_neg_of_pos_of_neg ht'.1 (hQ₃ t ht'))
  intro t ht
  constructor
  · have h := hm₁ ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simp only [h₁₀, mul_zero, sub_self] at h
    linarith
  · have h := hmN ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa only [zero_mul, h₁₀, sub_self] using h

theorem exists_sqrt_jet_negative {Q₁ Q₂ Q₃ Q₄ : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (k : ℝ)
    (h₁ : ∀ t ∈ Icc 0 a, HasDerivAt Q₁ (Q₂ t) t)
    (h₂ : ∀ t ∈ Icc 0 a, HasDerivAt Q₂ (Q₃ t) t)
    (h₃ : ∀ t ∈ Icc 0 a, HasDerivAt Q₃ (Q₄ t) t)
    (h₁₀ : Q₁ 0 = 0) (h₃₀ : Q₃ 0 = 0) (h₂₀ : Q₂ 0 < 2 * k)
    (h₄cont : ContinuousAt Q₄ 0) (h₄₀ : Q₄ 0 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ioo 0 δ,
      sqrtSlope Q₁ z < k ∧ sqrtCurvature Q₁ Q₂ z < 0 := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), Q₄ t < 0 :=
    h₄cont.eventually (eventually_lt_nhds h₄₀)
  obtain ⟨b, hb, hbound⟩ := Metric.eventually_nhds_iff.mp he
  let c := min a (b / 2)
  have hc : 0 < c := lt_min ha (by linarith)
  have hc₁ : c ≤ a := min_le_left _ _
  have hc₂ : c < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsub : Icc (0 : ℝ) c ⊆ Icc 0 a := Icc_subset_Icc le_rfl hc₁
  have hsign := jet_signs_on_interval hc k
    (fun t ht => h₁ t (hsub ht)) (fun t ht => h₂ t (hsub ht))
    (fun t ht => h₃ t (hsub ht)) h₁₀ h₃₀ h₂₀ (by
      intro t ht
      apply hbound
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans hc₂)
  refine ⟨c ^ (2 : ℕ), sq_pos_of_pos hc, ?_⟩
  intro z hz
  have ht : Real.sqrt z ∈ Ioo 0 c := by
    constructor
    · exact Real.sqrt_pos.mpr hz.1
    · apply (Real.sqrt_lt' hc).mpr
      exact hz.2
  obtain ⟨hfirst, hsecond⟩ := hsign _ ht
  constructor
  · apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) ht.1)).mpr
    nlinarith
  · exact div_neg_of_neg_of_pos hsecond (mul_pos (by norm_num) (pow_pos ht.1 _))

end D5.S3.Entropy.RenyiCombining.CachinConvexLimits
