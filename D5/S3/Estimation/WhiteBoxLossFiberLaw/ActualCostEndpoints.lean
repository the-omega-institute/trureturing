/- GID: D5/S3/Estimation/WhiteBoxLossFiberLaw/ActualCostEndpoints
   generality: G
   mirror-B: D5/B/S3/Estimation/WhiteBoxLossFiberLaw/ActualCostEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained nonnegative coding values on a rotating two-atom dictionary slice. -/

import D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Attained nonnegative two-coordinate energies control the actual dictionary
value function, its endpoint derivatives, and its interval minima. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Estimation.WhiteBoxLossFiberLaw.ActualCostEndpoints

open TwoAtomMatching Set Filter
open scoped BigOperators Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem plane_norm_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (a b : ℝ) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, hu, hv, real_inner_smul_left, inner_smul_right, huv,
    Real.norm_eq_abs, sq_abs]

/-- The second atom rotates in the plane of the orthogonal unit directions. -/
def rotatingDictionary (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (α : ℝ) : UnitDictionary E :=
  canonicalDictionary u (Real.cos α • u + Real.sin α • v) hu (by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [plane_norm_sq u v hu hv huv]
    nlinarith [Real.sin_sq_add_cos_sq α])

/-- The actual infimal objective on the slice with its first atom fixed. -/
def sliceCost (lam pA pAB pB : ℝ) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (α : ℝ) : ℝ :=
  jointCost lam pA pAB pB u v (rotatingDictionary u v hu hv huv α)

/-- The positive part of the first-coordinate Schur residual. -/
def activeMass (lam α : ℝ) : ℝ :=
  max 0 (1 - lam - Real.cos α * (Real.cos α + Real.sin α - lam))

/-- The attained value for the co-occurring sample. -/
def jointValue (lam α : ℝ) : ℝ :=
  1 - (Real.cos α + Real.sin α - lam) ^ 2 / 2 -
    activeMass lam α ^ 2 / (2 * (1 - Real.cos α ^ 2))

private theorem planar_energy (lam x y α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (c : Fin 2 → ℝ) :
    codeEnergy lam (x • u + y • v) (rotatingDictionary u v hu hv huv α) c =
      ((x - c 0 - Real.cos α * c 1) ^ 2 + (y - Real.sin α * c 1) ^ 2) / 2 +
        lam * (c 0 + c 1) := by
  have hc : x • u + y • v -
      atomCombination (rotatingDictionary u v hu hv huv α) c =
      (x - c 0 - Real.cos α * c 1) • u + (y - Real.sin α * c 1) • v := by
    simp only [atomCombination, Fin.sum_univ_two, rotatingDictionary,
      canonicalDictionary, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  simp only [codeEnergy, hc, plane_norm_sq u v hu hv huv, Fin.sum_univ_two]

private theorem attained_cost (lam : ℝ) (x : E) (D : UnitDictionary E)
    (c : Fin 2 → ℝ) (hc : FeasibleCode c)
    (hmin : ∀ d, FeasibleCode d → codeEnergy lam x D c ≤ codeEnergy lam x D d) :
    codeCost lam x D = codeEnergy lam x D c := by
  exact (show IsLeast {z : ℝ | ∃ d, FeasibleCode d ∧ codeEnergy lam x D d = z}
    (codeEnergy lam x D c) from ⟨⟨c, hc, rfl⟩,
      by rintro z ⟨d, hd, rfl⟩; exact hmin d hd⟩).csInf_eq

private theorem interval_geometry {α : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    0 ≤ Real.cos α ∧ 0 < Real.sin α ∧
      1 / Real.sqrt 2 ≤ Real.sin α ∧ 0 < 1 - Real.cos α ^ 2 := by
  have hp := Real.pi_pos
  have hcos := Real.cos_nonneg_of_mem_Icc (show α ∈ Icc (-(Real.pi / 2))
      (Real.pi / 2) from ⟨by linarith [hα.1], hα.2⟩)
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi / 4 by linarith) hα.2 hα.1
  rw [Real.sin_pi_div_four] at hs
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff hsqrt.ne').mpr
    nlinarith
  have hsin : 0 < Real.sin α := by linarith
  refine ⟨hcos, hsin, by simpa [hinv] using hs, ?_⟩
  nlinarith [Real.sin_sq_add_cos_sq α, sq_pos_of_pos hsin]

private theorem clipped_joint_optimizer (lam g s : ℝ) (hlam : 0 ≤ lam)
    (hg : 0 ≤ g) (hs : lam < s) (hcircle : g ^ 2 + s ^ 2 = 1) :
    let m := g + s - lam
    let h := 1 - lam - g * m
    let k := 1 - g ^ 2
    let a := max 0 h / k
    let b := m - g * a
    let V := 1 - m ^ 2 / 2 - max 0 h ^ 2 / (2 * k)
    0 ≤ a ∧ 0 ≤ b ∧
      ((1 - a - g * b) ^ 2 + (1 - s * b) ^ 2) / 2 + lam * (a + b) = V ∧
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        V ≤ ((1 - A - g * B) ^ 2 + (1 - s * B) ^ 2) / 2 + lam * (A + B) := by
  dsimp only
  let m := g + s - lam
  let h := 1 - lam - g * m
  let k := 1 - g ^ 2
  have hs0 : 0 < s := lt_of_le_of_lt hlam hs
  have hk : 0 < k := by dsimp [k]; nlinarith [sq_pos_of_pos hs0]
  have hk0 : k ≠ 0 := hk.ne'
  have hm : 0 < m := by dsimp [m]; linarith
  have hsecond : 0 < m - g * (1 - lam) := by
    dsimp [m]
    nlinarith [mul_nonneg hlam hg]
  have base_identity (A B : ℝ) :
      ((1 - A - g * B) ^ 2 + (1 - s * B) ^ 2) / 2 + lam * (A + B) =
        1 - m ^ 2 / 2 + (B + g * A - m) ^ 2 / 2 + k * A ^ 2 / 2 - h * A := by
    dsimp [m, h, k]
    linear_combination (B ^ 2 / 2) * hcircle
  change 0 ≤ max 0 h / k ∧ 0 ≤ m - g * (max 0 h / k) ∧ _
  by_cases hh : h ≤ 0
  · rw [max_eq_left hh]
    simp only [zero_div, mul_zero, sub_zero, zero_pow, add_zero]
    refine ⟨le_rfl, hm.le, ?_, ?_⟩
    · simpa using base_identity 0 m
    · intro A B hA _
      have hid :
          ((1 - A - g * B) ^ 2 + (1 - s * B) ^ 2) / 2 + lam * (A + B) -
            (1 - m ^ 2 / 2) =
          (B + g * A - m) ^ 2 / 2 + k * A ^ 2 / 2 + (-h) * A := by
        rw [base_identity]
        ring
      have hlast := mul_nonneg (neg_nonneg.mpr hh) hA
      have hsq := mul_nonneg hk.le (sq_nonneg A)
      change 1 - m ^ 2 / 2 - 0 ^ 2 / (2 * k) ≤ _
      norm_num only [zero_pow, zero_div, sub_zero]
      nlinarith [hid, sq_nonneg (B + g * A - m)]
  · have hh0 : 0 < h := lt_of_not_ge hh
    rw [max_eq_right hh0.le]
    have hb : m - g * (h / k) = (m - g * (1 - lam)) / k := by
      dsimp [h, k]
      field_simp [show 1 - g ^ 2 ≠ 0 from hk0]
      <;> ring
    refine ⟨div_nonneg hh0.le hk.le, by rw [hb]; exact div_nonneg hsecond.le hk.le,
      ?_, ?_⟩
    · have hid :
          ((1 - h / k - g * (m - g * (h / k))) ^ 2 +
              (1 - s * (m - g * (h / k))) ^ 2) / 2 +
            lam * (h / k + (m - g * (h / k))) =
          1 - m ^ 2 / 2 - h ^ 2 / (2 * k) := by
        rw [base_identity]
        field_simp [hk0]
        <;> ring
      exact hid
    · intro A B _ _
      have hid :
          ((1 - A - g * B) ^ 2 + (1 - s * B) ^ 2) / 2 + lam * (A + B) -
            (1 - m ^ 2 / 2 - h ^ 2 / (2 * k)) =
          (B + g * A - m) ^ 2 / 2 + k * (A - h / k) ^ 2 / 2 := by
        rw [base_identity]
        field_simp [hk0]
        <;> ring
      have hsq := mul_nonneg hk.le (sq_nonneg (A - h / k))
      nlinarith [sq_nonneg (B + g * A - m)]

private theorem joint_attained (lam α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    ∃ c : Fin 2 → ℝ, FeasibleCode c ∧
      codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) c = jointValue lam α ∧
      (∀ d, FeasibleCode d → jointValue lam α ≤
        codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) d) ∧
      codeCost lam (u + v) (rotatingDictionary u v hu hv huv α) = jointValue lam α := by
  obtain ⟨hg, _, hs, _⟩ := interval_geometry hα
  obtain ⟨ha, hb, he, hmin⟩ := clipped_joint_optimizer lam (Real.cos α) (Real.sin α)
    hlam.le hg (hsmall.trans_le hs) (by nlinarith [Real.sin_sq_add_cos_sq α])
  let a := activeMass lam α / (1 - Real.cos α ^ 2)
  let b := Real.cos α + Real.sin α - lam - Real.cos α * a
  let c : Fin 2 → ℝ := ![a, b]
  have hc : FeasibleCode c := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
  have he' : codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) c =
      jointValue lam α := by
    simpa [one_smul, c, a, b, jointValue, activeMass] using
      (planar_energy lam 1 1 α u v hu hv huv c).trans he
  have hmin' : ∀ d, FeasibleCode d → jointValue lam α ≤
      codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) d := by
    intro d hd
    have hplan := planar_energy lam 1 1 α u v hu hv huv d
    simp only [one_smul] at hplan
    rw [hplan]
    exact hmin (d 0) (d 1) (hd 0) (hd 1)
  refine ⟨c, hc, he', hmin', ?_⟩
  rw [attained_cost lam (u + v) _ c hc (by intro d hd; rw [he']; exact hmin' d hd), he']

private theorem child_attained (lam α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    ∃ c : Fin 2 → ℝ, FeasibleCode c ∧
      codeEnergy lam v (rotatingDictionary u v hu hv huv α) c =
        1 / 2 - (Real.sin α - lam) ^ 2 / 2 ∧
      (∀ d, FeasibleCode d → 1 / 2 - (Real.sin α - lam) ^ 2 / 2 ≤
        codeEnergy lam v (rotatingDictionary u v hu hv huv α) d) ∧
      codeCost lam v (rotatingDictionary u v hu hv huv α) =
        1 / 2 - (Real.sin α - lam) ^ 2 / 2 := by
  obtain ⟨hg, _, hs, hk⟩ := interval_geometry hα
  have hmass : 0 < Real.sin α - lam := sub_pos.mpr (hsmall.trans_le hs)
  let c : Fin 2 → ℝ := ![0, Real.sin α - lam]
  have hc : FeasibleCode c := by intro i; fin_cases i <;> simp [c, hmass.le]
  have identity (d : Fin 2 → ℝ) :
      codeEnergy lam v (rotatingDictionary u v hu hv huv α) d -
          (1 / 2 - (Real.sin α - lam) ^ 2 / 2) =
        (d 1 + Real.cos α * d 0 - (Real.sin α - lam)) ^ 2 / 2 +
          (1 - Real.cos α ^ 2) * d 0 ^ 2 / 2 +
          (lam + Real.cos α * (Real.sin α - lam)) * d 0 := by
    have he := planar_energy lam 0 1 α u v hu hv huv d
    simp only [zero_smul, one_smul, zero_add] at he
    rw [he]
    linear_combination (d 1 ^ 2 / 2) * (Real.sin_sq_add_cos_sq α)
  have he : codeEnergy lam v (rotatingDictionary u v hu hv huv α) c =
      1 / 2 - (Real.sin α - lam) ^ 2 / 2 := by
    have hi := identity c
    simp [c] at hi
    linarith
  have hmin : ∀ d, FeasibleCode d → 1 / 2 - (Real.sin α - lam) ^ 2 / 2 ≤
      codeEnergy lam v (rotatingDictionary u v hu hv huv α) d := by
    intro d hd
    have hlast := mul_nonneg
      (add_nonneg hlam.le (mul_nonneg hg hmass.le)) (hd 0)
    have hquad := mul_nonneg hk.le (sq_nonneg (d 0))
    nlinarith [identity d,
      sq_nonneg (d 1 + Real.cos α * d 0 - (Real.sin α - lam))]
  refine ⟨c, hc, he, hmin, ?_⟩
  rw [attained_cost lam v _ c hc (by intro d hd; rw [he]; exact hmin d hd), he]

private theorem parent_value (lam α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    codeCost lam u (rotatingDictionary u v hu hv huv α) = lam - lam ^ 2 / 2 := by
  have hlt : lam < 1 := (hsmall.trans_le (interval_geometry hα).2.2.1).trans_le
    (Real.sin_le_one α)
  simpa using (code_cost_eq_radial_iff lam 1 u
    (rotatingDictionary u v hu hv huv α) hu hlam hlt).mpr ⟨0, rfl⟩

private theorem zero_value (lam : ℝ) (D : UnitDictionary E) (hlam : 0 < lam) :
    codeCost lam (0 : E) D = 0 := by
  obtain ⟨hl, hu⟩ := code_cost_bounds lam (0 : E) D hlam.le
  simpa using le_antisymm (by simpa using hu) hl

private theorem slice_formula (lam pA pAB pB α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    sliceCost lam pA pAB pB u v hu hv huv α =
      pA * (lam - lam ^ 2 / 2) + pAB * jointValue lam α +
        pB * (1 / 2 - (Real.sin α - lam) ^ 2 / 2) := by
  obtain ⟨_, _, _, _, hj⟩ := joint_attained lam α u v hu hv huv hlam hsmall hα
  obtain ⟨_, _, _, _, hb⟩ := child_attained lam α u v hu hv huv hlam hsmall hα
  simp only [sliceCost, jointCost, parent_value lam α u v hu hv huv hlam hsmall hα,
    hj, hb]

private theorem slice_continuous (lam pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2) :
    ContinuousOn (sliceCost lam pA pAB pB u v hu hv huv)
      (Icc (Real.pi / 4) (Real.pi / 2)) := by
  have hm : Continuous (activeMass lam) := by unfold activeMass; fun_prop
  have hbase : Continuous (fun α : ℝ => 1 - (Real.cos α + Real.sin α - lam) ^ 2 / 2) := by
    fun_prop
  have hden : Continuous (fun α : ℝ => 2 * (1 - Real.cos α ^ 2)) := by fun_prop
  have hj : ContinuousOn (jointValue lam) (Icc (Real.pi / 4) (Real.pi / 2)) :=
    hbase.continuousOn.sub ((hm.pow 2).continuousOn.div hden.continuousOn (by
      intro α hα
      exact mul_ne_zero (by norm_num) (interval_geometry hα).2.2.2.ne'))
  have hf : ContinuousOn (fun α : ℝ =>
      pA * (lam - lam ^ 2 / 2) + pAB * jointValue lam α +
        pB * (1 / 2 - (Real.sin α - lam) ^ 2 / 2))
      (Icc (Real.pi / 4) (Real.pi / 2)) := by
    exact (continuousOn_const.add (continuousOn_const.mul hj)).add
      (by fun_prop)
  exact hf.congr (fun α hα => slice_formula lam pA pAB pB α u v hu hv huv
    hlam hsmall hα)

private def leftModel (lam pA pAB pB α : ℝ) : ℝ :=
  pA * (lam - lam ^ 2 / 2) +
    pAB * (1 - (Real.cos α + Real.sin α - lam) ^ 2 / 2) +
    pB * (1 / 2 - (Real.sin α - lam) ^ 2 / 2)

private def rightModel (lam pA pAB pB α : ℝ) : ℝ :=
  pA * (lam - lam ^ 2 / 2) +
    pAB * (1 - ((1 - lam) ^ 2 -
      2 * Real.cos α * (1 - lam) * (Real.cos α + Real.sin α - lam) +
      (Real.cos α + Real.sin α - lam) ^ 2) / (2 * (1 - Real.cos α ^ 2))) +
    pB * (1 / 2 - (Real.sin α - lam) ^ 2 / 2)

private theorem left_formula (lam pA pAB pB α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hh : 1 - lam - Real.cos α * (Real.cos α + Real.sin α - lam) < 0) :
    sliceCost lam pA pAB pB u v hu hv huv α = leftModel lam pA pAB pB α := by
  rw [slice_formula lam pA pAB pB α u v hu hv huv hlam hsmall hα]
  simp [jointValue, activeMass, max_eq_left hh.le, leftModel]

private theorem right_formula (lam pA pAB pB α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hh : 0 < 1 - lam - Real.cos α * (Real.cos α + Real.sin α - lam)) :
    sliceCost lam pA pAB pB u v hu hv huv α = rightModel lam pA pAB pB α := by
  have hk := (interval_geometry hα).2.2.2.ne'
  rw [slice_formula lam pA pAB pB α u v hu hv huv hlam hsmall hα]
  dsimp [jointValue, activeMass, rightModel]
  rw [max_eq_right hh.le]
  field_simp [hk]
  <;> ring

private theorem active_endpoint_signs (lam : ℝ) (hlam : 0 < lam)
    (hsmall : lam < 1 / Real.sqrt 2) :
    (1 - lam - Real.cos (Real.pi / 4) *
      (Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) - lam) < 0) ∧
    (0 < 1 - lam - Real.cos (Real.pi / 2) *
      (Real.cos (Real.pi / 2) + Real.sin (Real.pi / 2) - lam)) := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 2 / 2 < 1 := by nlinarith
  have hlt : lam < 1 := by
    have hsin := (interval_geometry (show Real.pi / 2 ∈
      Icc (Real.pi / 4) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩)).2.2.1
    rw [Real.sin_pi_div_two] at hsin
    exact hsmall.trans_le hsin
  constructor
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    nlinarith [mul_pos hlam (sub_pos.mpr hr)]
  · simpa using sub_pos.mpr hlt

private theorem left_derivative (lam pA pAB pB α : ℝ) :
    HasDerivAt (leftModel lam pA pAB pB)
      (-pAB * (Real.cos α + Real.sin α - lam) * (Real.cos α - Real.sin α) -
        pB * (Real.sin α - lam) * Real.cos α) α := by
  have hm := (((Real.hasDerivAt_cos α).add (Real.hasDerivAt_sin α)).sub_const lam).pow 2
  have hb := ((Real.hasDerivAt_sin α).sub_const lam).pow 2
  convert! ((hasDerivAt_const α (pA * (lam - lam ^ 2 / 2))).add
      (((hm.div_const 2).const_sub 1).const_mul pAB)).add
      (((hb.div_const 2).const_sub (1 / 2)).const_mul pB) using 1 <;>
    simp only [Pi.add_apply] <;> ring

private theorem right_differentiable (lam pA pAB pB α : ℝ)
    (hk : 1 - Real.cos α ^ 2 ≠ 0) :
    DifferentiableAt ℝ (rightModel lam pA pAB pB) α := by
  unfold rightModel
  fun_prop (disch := exact mul_ne_zero (by norm_num) hk)

private theorem right_endpoint_derivative (lam pA pAB pB : ℝ) :
    HasDerivAt (rightModel lam pA pAB pB) (pAB * lam * (1 - lam)) (Real.pi / 2) := by
  let β := Real.pi / 2
  have hg : HasDerivAt Real.cos (-1) β := by
    simpa [β] using Real.hasDerivAt_cos β
  have hs : HasDerivAt Real.sin 0 β := by
    simpa [β] using Real.hasDerivAt_sin β
  have hm := (hg.add hs).sub_const lam
  have hnum := ((hasDerivAt_const β ((1 - lam) ^ 2)).sub
      (((hg.const_mul 2).mul_const (1 - lam)).mul hm)).add (hm.pow 2)
  have hden := ((hg.pow 2).const_sub 1).const_mul 2
  have hquot := hnum.div hden (by simp [β])
  have hb := ((hs.sub_const lam).pow 2).div_const 2
  convert! ((hasDerivAt_const β (pA * (lam - lam ^ 2 / 2))).add
      ((hquot.const_sub 1).const_mul pAB)).add
      ((hb.const_sub (1 / 2)).const_mul pB) using 1 <;>
    dsimp [rightModel, β] <;>
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring

private theorem slice_left_derivative (lam pA pAB pB α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hh : 1 - lam - Real.cos α * (Real.cos α + Real.sin α - lam) < 0) :
    HasDerivWithinAt (sliceCost lam pA pAB pB u v hu hv huv)
      (-pAB * (Real.cos α + Real.sin α - lam) * (Real.cos α - Real.sin α) -
        pB * (Real.sin α - lam) * Real.cos α)
      (Icc (Real.pi / 4) (Real.pi / 2)) α := by
  have hc : Continuous (fun a : ℝ => 1 - lam - Real.cos a *
      (Real.cos a + Real.sin a - lam)) := by fun_prop
  have he := hc.continuousAt.eventually (gt_mem_nhds hh)
  apply (left_derivative lam pA pAB pB α).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hI
    exact left_formula lam pA pAB pB a u v hu hv huv hlam hsmall hI ha
  · exact left_formula lam pA pAB pB α u v hu hv huv hlam hsmall hα hh

private theorem slice_right_differentiable (lam pA pAB pB α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hh : 0 < 1 - lam - Real.cos α * (Real.cos α + Real.sin α - lam)) :
    DifferentiableWithinAt ℝ (sliceCost lam pA pAB pB u v hu hv huv)
      (Icc (Real.pi / 4) (Real.pi / 2)) α := by
  have hc : Continuous (fun a : ℝ => 1 - lam - Real.cos a *
      (Real.cos a + Real.sin a - lam)) := by fun_prop
  have he := hc.continuousAt.eventually (lt_mem_nhds hh)
  have hd := right_differentiable lam pA pAB pB α (interval_geometry hα).2.2.2.ne'
  apply (hd.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq ?_
      (right_formula lam pA pAB pB α u v hu hv huv hlam hsmall hα hh)).differentiableWithinAt
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hI
  exact right_formula lam pA pAB pB a u v hu hv huv hlam hsmall hI ha

private theorem endpoint_derivatives (lam pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2) :
    HasDerivWithinAt (sliceCost lam pA pAB pB u v hu hv huv)
      (-pB * (1 / Real.sqrt 2 - lam) / Real.sqrt 2)
      (Icc (Real.pi / 4) (Real.pi / 2)) (Real.pi / 4) ∧
    HasDerivWithinAt (sliceCost lam pA pAB pB u v hu hv huv)
      (pAB * lam * (1 - lam))
      (Icc (Real.pi / 4) (Real.pi / 2)) (Real.pi / 2) := by
  have hp := Real.pi_pos
  have hleft : Real.pi / 4 ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨le_rfl, by linarith⟩
  have hright : Real.pi / 2 ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨by linarith, le_rfl⟩
  obtain ⟨hL, hR⟩ := active_endpoint_signs lam hlam hsmall
  constructor
  · have h := slice_left_derivative lam pA pAB pB (Real.pi / 4) u v hu hv huv
      hlam hsmall hleft hL
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      rw [← one_div]
      apply (div_eq_iff hspos.ne').mpr
      nlinarith
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four] at h
    convert h using 1 <;> simp only [sub_self, mul_zero, zero_sub, div_eq_mul_inv, hinv] <;> ring
  · have hc : Continuous (fun a : ℝ => 1 - lam - Real.cos a *
        (Real.cos a + Real.sin a - lam)) := by fun_prop
    have he := hc.continuousAt.eventually (lt_mem_nhds hR)
    apply (right_endpoint_derivative lam pA pAB pB).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hI
      exact right_formula lam pA pAB pB a u v hu hv huv hlam hsmall hI ha
    · exact right_formula lam pA pAB pB (Real.pi / 2) u v hu hv huv hlam hsmall hright hR

private theorem endpoint_neighborhoods (lam pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2) :
    (∀ᶠ α in 𝓝[Icc (Real.pi / 4) (Real.pi / 2)] (Real.pi / 4),
      DifferentiableWithinAt ℝ (sliceCost lam pA pAB pB u v hu hv huv)
        (Icc (Real.pi / 4) (Real.pi / 2)) α) ∧
    (∀ᶠ α in 𝓝[Icc (Real.pi / 4) (Real.pi / 2)] (Real.pi / 2),
      DifferentiableWithinAt ℝ (sliceCost lam pA pAB pB u v hu hv huv)
        (Icc (Real.pi / 4) (Real.pi / 2)) α) := by
  have hc : Continuous (fun a : ℝ => 1 - lam - Real.cos a *
      (Real.cos a + Real.sin a - lam)) := by fun_prop
  obtain ⟨hL, hR⟩ := active_endpoint_signs lam hlam hsmall
  constructor
  · have he := hc.continuousAt.eventually (gt_mem_nhds hL)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hI
    have hd := slice_left_derivative lam pA pAB pB a u v hu hv huv hlam hsmall hI ha
    exact hd.differentiableWithinAt
  · have he := hc.continuousAt.eventually (lt_mem_nhds hR)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hI
    exact slice_right_differentiable lam pA pAB pB a u v hu hv huv hlam hsmall hI ha

private theorem endpoint_exclusion (f : ℝ → ℝ) (a b dA dB : ℝ) (hab : a < b)
    (hA : HasDerivWithinAt f dA (Icc a b) a)
    (hB : HasDerivWithinAt f dB (Icc a b) b) (hdA : dA < 0) (hdB : 0 < dB) :
    ∀ α ∈ Icc a b, IsMinOn f (Icc a b) α → α ∈ Ioo a b := by
  intro α hα hmin
  have hsegment : segment ℝ a b ⊆ Icc a b :=
    (convex_Icc a b).segment_subset ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
  have hsegment' : segment ℝ b a ⊆ Icc a b := by
    exact (convex_Icc a b).segment_subset ⟨hab.le, le_rfl⟩ ⟨le_rfl, hab.le⟩
  have hnotA : α ≠ a := by
    intro heq
    subst α
    have ht := sub_mem_posTangentConeAt_of_segment_subset hsegment
    have hn := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hA.hasFDerivWithinAt ht
    have hn' : 0 ≤ (b - a) * dA := by simpa using hn
    exact (not_lt_of_ge hn') (mul_neg_of_pos_of_neg (sub_pos.mpr hab) hdA)
  have hnotB : α ≠ b := by
    intro heq
    subst α
    have ht := sub_mem_posTangentConeAt_of_segment_subset hsegment'
    have hn := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hB.hasFDerivWithinAt ht
    have hn' : 0 ≤ (a - b) * dB := by simpa using hn
    exact (not_lt_of_ge hn') (mul_neg_of_neg_of_pos (sub_neg.mpr hab) hdB)
  exact ⟨lt_of_le_of_ne hα.1 (Ne.symm hnotA), lt_of_le_of_ne hα.2 hnotB⟩

/-- Both endpoint slopes have strict inward improvement for the actual infimal
cost. The slice has a minimum, and every slice minimum is strictly intermediate.
The weights of the parent sample and of the zero sample need no positivity
assumption; in particular the assertion includes every normalized four-point law. -/
theorem partial_absorption (lam pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hpAB : 0 < pAB) (hpB : 0 < pB) :
    let I := Icc (Real.pi / 4) (Real.pi / 2)
    let J := sliceCost lam pA pAB pB u v hu hv huv
    (rotatingDictionary u v hu hv huv (Real.pi / 4)).1 1 = bisector u v ∧
    (rotatingDictionary u v hu hv huv (Real.pi / 2)).1 1 = v ∧
    (∀ α ∈ I, ∀ p0 : ℝ,
      let D := rotatingDictionary u v hu hv huv α
      p0 * codeCost lam (0 : E) D + pA * codeCost lam u D +
        pAB * codeCost lam (u + v) D + pB * codeCost lam v D = J α) ∧
    (∀ α ∈ I,
      codeCost lam u (rotatingDictionary u v hu hv huv α) = lam - lam ^ 2 / 2 ∧
      (∃ c : Fin 2 → ℝ, FeasibleCode c ∧
        codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) c = jointValue lam α ∧
        (∀ d, FeasibleCode d → jointValue lam α ≤
          codeEnergy lam (u + v) (rotatingDictionary u v hu hv huv α) d) ∧
        codeCost lam (u + v) (rotatingDictionary u v hu hv huv α) = jointValue lam α) ∧
      (∃ c : Fin 2 → ℝ, FeasibleCode c ∧
        codeEnergy lam v (rotatingDictionary u v hu hv huv α) c =
          1 / 2 - (Real.sin α - lam) ^ 2 / 2 ∧
        (∀ d, FeasibleCode d → 1 / 2 - (Real.sin α - lam) ^ 2 / 2 ≤
          codeEnergy lam v (rotatingDictionary u v hu hv huv α) d) ∧
        codeCost lam v (rotatingDictionary u v hu hv huv α) =
          1 / 2 - (Real.sin α - lam) ^ 2 / 2)) ∧
    ContinuousOn J I ∧
    (∀ᶠ α in 𝓝[I] (Real.pi / 4), DifferentiableWithinAt ℝ J I α) ∧
    (∀ᶠ α in 𝓝[I] (Real.pi / 2), DifferentiableWithinAt ℝ J I α) ∧
    HasDerivWithinAt J (-pB * (1 / Real.sqrt 2 - lam) / Real.sqrt 2) I (Real.pi / 4) ∧
    HasDerivWithinAt J (pAB * lam * (1 - lam)) I (Real.pi / 2) ∧
    -pB * (1 / Real.sqrt 2 - lam) / Real.sqrt 2 < 0 ∧
    0 < pAB * lam * (1 - lam) ∧
    (∃ α ∈ I, IsMinOn J I α) ∧
    (∀ α ∈ I, IsMinOn J I α → α ∈ Ioo (Real.pi / 4) (Real.pi / 2)) := by
  dsimp only
  have hp : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hI : Real.pi / 2 ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨hp.le, le_rfl⟩
  have hlt : lam < 1 := (hsmall.trans_le (interval_geometry hI).2.2.1).trans_le
    (Real.sin_le_one (Real.pi / 2))
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hneg : -pB * (1 / Real.sqrt 2 - lam) / Real.sqrt 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hpB)
      (sub_pos.mpr hsmall)) hsqrt
  have hpos : 0 < pAB * lam * (1 - lam) :=
    mul_pos (mul_pos hpAB hlam) (sub_pos.mpr hlt)
  have hcont := slice_continuous lam pA pAB pB u v hu hv huv hlam hsmall
  obtain ⟨hL, hR⟩ := endpoint_derivatives lam pA pAB pB u v hu hv huv hlam hsmall
  obtain ⟨hnL, hnR⟩ := endpoint_neighborhoods lam pA pAB pB u v hu hv huv hlam hsmall
  refine ⟨?_, ?_, ?_, ?_, hcont, hnL, hnR, hL, hR, hneg, hpos, ?_, ?_⟩
  · simp only [rotatingDictionary, canonicalDictionary, Matrix.cons_val_one, Matrix.cons_val_zero,
      Real.cos_pi_div_four, Real.sin_pi_div_four, bisector]
    have heq : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
      symm
      rw [← one_div]
      apply (div_eq_iff hsqrt.ne').mpr
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [heq, smul_add]
  · simp [rotatingDictionary, canonicalDictionary]
  · intro α _ p0
    simp [zero_value lam _ hlam, sliceCost, jointCost]
  · intro α hα
    exact ⟨parent_value lam α u v hu hv huv hlam hsmall hα,
      joint_attained lam α u v hu hv huv hlam hsmall hα,
      child_attained lam α u v hu hv huv hlam hsmall hα⟩
  · exact isCompact_Icc.exists_isMinOn ⟨Real.pi / 2, hI⟩ hcont
  · exact endpoint_exclusion _ _ _ _ _ hp hL hR hneg hpos

end D5.S3.Estimation.WhiteBoxLossFiberLaw.ActualCostEndpoints
