/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Saddle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unique entropy saddle and the minimum distinct-prime counting rate. -/

import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaTail
open OmegaTailUpper

/-- The logarithmic moment of the normalized density. -/
def m (s : ℝ) : ℝ := log (a s) - (π / s) * cot (π / s)

/-- The entropy at the saddle parameter. -/
def H (s : ℝ) : ℝ := s - π * cot (π / s)

/-- The least Rankin rate at the first-order threshold. -/
def C0 : ℝ := sInf (rate 0 '' Set.Ioi 1)

private lemma phase_pos {s : ℝ} (hs : 1 < s) : 0 < π / s :=
  div_pos pi_pos (zero_lt_one.trans hs)

private lemma phase_sin_pos {s : ℝ} (hs : 1 < s) : 0 < sin (π / s) :=
  sin_pos_of_pos_of_lt_pi (phase_pos hs) (div_lt_self pi_pos hs)

private lemma phase_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt (fun s : ℝ => π / s) (-π / s ^ 2) s := by
  convert (hasDerivAt_const s π).div (hasDerivAt_id s)
    (ne_of_gt (zero_lt_one.trans hs)) using 1
  · funext t
    rfl
  · simp only [id_eq]
    ring

private lemma a_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt a ((sin (π / s) - (π / s) * cos (π / s)) / π) s := by
  have hd := ((hasDerivAt_id s).mul ((phase_deriv hs).sin)).div_const π
  convert hd using 1
  · rfl
  · simp only [id_eq]
    field_simp
    <;> ring

private lemma a_lt_one {s : ℝ} (hs : 1 < s) : a s < 1 := by
  have ht := sin_lt (phase_pos hs)
  dsimp [a]
  apply (div_lt_one pi_pos).mpr
  have h := mul_lt_mul_of_pos_left ht (zero_lt_one.trans hs)
  have he : s * (π / s) = π := mul_div_cancel₀ π (ne_of_gt (zero_lt_one.trans hs))
  linarith

private lemma m_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt m ((1 / s) * (1 - (π / s) ^ 2 / sin (π / s) ^ 2)) s := by
  have hs0 : s ≠ 0 := ne_of_gt (zero_lt_one.trans hs)
  have hsin : sin (π / s) ≠ 0 := (phase_sin_pos hs).ne'
  have ha : a s ≠ 0 := (OmegaTailUpper.a_pos hs).ne'
  have hd := ((a_deriv hs).log ha).sub
    ((phase_deriv hs).mul
      (((phase_deriv hs).cos).div ((phase_deriv hs).sin) hsin))
  unfold m
  simp_rw [cot_eq_cos_div_sin]
  convert hd using 1
  dsimp [a]
  field_simp [hs0, hsin, pi_ne_zero]
  ring_nf
  rw [cos_sq']
  ring

private lemma m_deriv_neg {s : ℝ} (hs : 1 < s) :
    (1 / s) * (1 - (π / s) ^ 2 / sin (π / s) ^ 2) < 0 := by
  have hp := phase_pos hs
  have hsin := phase_sin_pos hs
  have hlt := sin_lt hp
  have hsquare : sin (π / s) ^ 2 < (π / s) ^ 2 := by nlinarith
  have hdiv : 1 < (π / s) ^ 2 / sin (π / s) ^ 2 :=
    (one_lt_div₀ (sq_pos_of_pos hsin)).mpr hsquare
  exact mul_neg_of_pos_of_neg (one_div_pos.mpr (zero_lt_one.trans hs)) (by linarith)

/-- The log moment is strictly decreasing throughout its natural domain. -/
private theorem m_strictAnti : StrictAntiOn m (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro s hs
    exact (m_deriv hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : 1 < s := by simpa only [interior_Ioi, Set.mem_Ioi] using hs
    rw [(m_deriv hs').deriv]
    exact m_deriv_neg hs'

private lemma rate_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt (rate 0) (-m s) s := by
  have ha : a s ≠ 0 := (OmegaTailUpper.a_pos hs).ne'
  have hd := (hasDerivAt_id s).mul
    ((hasDerivAt_const s (1 : ℝ)).sub ((a_deriv hs).log ha))
  convert hd using 1
  · funext t
    simp only [rate, sub_zero, Pi.mul_apply, Pi.sub_apply, id_eq]
  · dsimp [m, a]
    rw [cot_eq_cos_div_sin]
    field_simp [(zero_lt_one.trans hs).ne', (phase_sin_pos hs).ne', pi_ne_zero]
    <;> ring

private lemma m_two_neg : m 2 < 0 := by
  have hpi : (2 : ℝ) < π := by linarith [pi_gt_three]
  have ha2 : a 2 = 2 / π := by simp [a]
  have hc : cot (π / 2) = 0 := by simp [cot_eq_cos_div_sin]
  simp only [m, ha2, hc, mul_zero, sub_zero]
  exact log_neg (div_pos (by norm_num) pi_pos) ((div_lt_one pi_pos).mpr hpi)

private lemma m_four_thirds_pos : 0 < m (4 / 3) := by
  have hphase : π / (4 / 3 : ℝ) = π - π / 4 := by ring
  have hsin : sin (π / (4 / 3 : ℝ)) = sqrt 2 / 2 := by
    rw [hphase, sin_pi_sub, sin_pi_div_four]
  have hcos : cos (π / (4 / 3 : ℝ)) = -(sqrt 2 / 2) := by
    rw [hphase, cos_pi_sub, cos_pi_div_four]
  have hsq : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hp : 0 < sqrt (2 : ℝ) := sqrt_pos.2 (by norm_num)
  have hlower : (24 : ℝ) / 17 < sqrt 2 := by nlinarith
  have hc : cot (π / (4 / 3 : ℝ)) = -1 := by
    rw [cot_eq_cos_div_sin, hcos, hsin]
    field_simp
  have ha : a (4 / 3) = 2 * sqrt 2 / (3 * π) := by
    simp only [a, hsin]
    ring
  have ha0 : 0 < a (4 / 3) := OmegaTailUpper.a_pos (by norm_num)
  have hlog := one_sub_inv_le_log_of_pos ha0
  have hinv : (a (4 / 3))⁻¹ < 17 * π / 16 := by
    rw [ha, inv_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * sqrt (2 : ℝ))).mpr
    nlinarith [pi_pos]
  have hpi : π < 22 / 7 := by linarith [pi_lt_d4]
  dsimp [m]
  rw [hc]
  have he : π / (4 / 3 : ℝ) = 3 * π / 4 := by ring
  rw [he]
  linarith

private lemma saddle_exists : ∃ s ∈ Set.Ioo (1 : ℝ) 2, m s = 0 := by
  have hcont : ContinuousOn m (Set.Icc (4 / 3 : ℝ) 2) := by
    intro s hs
    exact (m_deriv (by have := hs.1; linarith)).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' (by norm_num : (4 / 3 : ℝ) ≤ 2)
    hcont ⟨m_two_neg.le, m_four_thirds_pos.le⟩
  refine ⟨s, ⟨by have := hs.1; linarith, ?_⟩, hz⟩
  have hne : s ≠ 2 := by intro he; rw [he] at hz; linarith [m_two_neg]
  exact lt_of_le_of_ne hs.2 hne

/-- The unique parameter in the interval between one and two with zero log moment. -/
def saddle : ℝ := Classical.choose saddle_exists

private lemma saddle_mem : saddle ∈ Set.Ioo (1 : ℝ) 2 :=
  (Classical.choose_spec saddle_exists).1

private lemma m_saddle : m saddle = 0 :=
  (Classical.choose_spec saddle_exists).2

private lemma saddle_min : IsMinOn (rate 0) (Set.Ioi 1) saddle := by
  apply isMinOn_Ioi_of_deriv (rate_deriv saddle_mem.1).continuousAt
  · intro s hs
    exact (rate_deriv hs.1).differentiableAt.differentiableWithinAt
  · intro s hs
    exact (rate_deriv (saddle_mem.1.trans hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(rate_deriv hs.1).deriv]
    have hm := m_strictAnti hs.1 saddle_mem.1 hs.2
    rw [m_saddle] at hm
    linarith
  · intro s hs
    rw [(rate_deriv (saddle_mem.1.trans hs)).deriv]
    have hm := m_strictAnti saddle_mem.1 (saddle_mem.1.trans hs) hs
    rw [m_saddle] at hm
    linarith

private lemma constant_eq_rate : C0 = rate 0 saddle := by
  apply IsLeast.csInf_eq
  refine ⟨⟨saddle, saddle_mem.1, rfl⟩, ?_⟩
  rintro z ⟨s, hs, rfl⟩
  exact saddle_min hs

private lemma rate_eq_entropy : rate 0 saddle = H saddle := by
  have hs0 : saddle ≠ 0 := (zero_lt_one.trans saddle_mem.1).ne'
  have hm := m_saddle
  dsimp [m] at hm
  dsimp [rate, H]
  rw [sub_zero]
  have hlog : log (a saddle) = π / saddle * cot (π / saddle) := by linarith
  rw [hlog]
  field_simp
  <;> ring

/-- The least rate is attained uniquely at the zero log-moment parameter. -/
theorem saddle_characterization :
    saddle ∈ Set.Ioo (1 : ℝ) 2 ∧ m saddle = 0 ∧
      (∀ s : ℝ, 1 < s → m s = 0 → s = saddle) ∧
      IsMinOn (rate 0) (Set.Ioi 1) saddle ∧ C0 = rate 0 saddle ∧ C0 = H saddle := by
  refine ⟨saddle_mem, m_saddle, ?_, saddle_min, constant_eq_rate,
    constant_eq_rate.trans rate_eq_entropy⟩
  intro s hs hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := m_strictAnti hs saddle_mem.1 hlt
    rw [hz, m_saddle] at hm
    exact (lt_irrefl 0) hm
  · have hm := m_strictAnti saddle_mem.1 hs hgt
    rw [hz, m_saddle] at hm
    exact (lt_irrefl 0) hm

/-- The counting exponent strictly exceeds one. -/
theorem constant_gt_one : 1 < C0 := by
  rw [constant_eq_rate]
  have ha0 := OmegaTailUpper.a_pos saddle_mem.1
  have hal := a_lt_one saddle_mem.1
  have hlog := log_neg ha0 hal
  have hs0 := zero_lt_one.trans saddle_mem.1
  dsimp [rate]
  nlinarith [saddle_mem.1]

/-- Moving to the right of the saddle gives a strictly negative log moment. -/
theorem m_neg_of_saddle_lt {s : ℝ} (hs : saddle < s) : m s < 0 := by
  have hm := m_strictAnti saddle_mem.1 (saddle_mem.1.trans hs) hs
  rwa [m_saddle] at hm

/-- The entropy expression is continuous at every admissible parameter. -/
theorem H_continuousAt {s : ℝ} (hs : 1 < s) : ContinuousAt H s := by
  change ContinuousAt (fun t : ℝ => t - π * cot (π / t)) s
  simp only [cot_eq_cos_div_sin]
  have hp : ContinuousAt (fun t : ℝ => π / t) s := (phase_deriv hs).continuousAt
  have hc := continuous_cos.continuousAt.comp hp
  have hsin := continuous_sin.continuousAt.comp hp
  exact continuousAt_id.sub (continuousAt_const.mul
    (hc.div hsin (phase_sin_pos hs).ne'))

end D5.S3.Arith.Robin.Analytic.OmegaTail
