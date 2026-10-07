/- GID: D5/S3/Arith/Robin/ActualPrimeInsertionDampingTransition
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualPrimeInsertionDampingTransition
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual same-clock prime insertion has one full-integral damping sign transition. -/

import D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Finset
open scoped BigOperators Topology Interval

namespace D5.S3.Arith.Robin.ActualPrimeInsertionDampingTransition

open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample

/-- Both actual finite Euler products are evaluated at the common clock log 3. -/
def fixedClockRatio (z v : ℝ) : ℝ :=
  actualEuler z (1 + v / Real.log 3) / actualEuler z 1

def fixedClockSlope (z : ℝ) : ℝ :=
  (∑ p ∈ primeCutoff z, Real.log (p : ℝ) / ((p : ℝ) - 1)) / Real.log 3

def actualNumerator (z v : ℝ) : ℝ :=
  fixedClockRatio z v - 1 - fixedClockSlope z * v

/-- The literal complete compensated integral on the positive half-axis. -/
def actualIntegral (z σ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * actualNumerator z v / v ^ 2

private def c : ℝ := Real.log 2 / Real.log 3
private def g (v : ℝ) : ℝ :=
  (2 - Real.exp (-c * v)) * (1 - Real.exp (-v)) - v
private def h (v : ℝ) : ℝ := g v / (2 * v ^ 2)
private def signedIntegral (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * h v
private def K : ℝ := 2 + c ^ 2 + (c + 1) ^ 2
private def M : ℝ := K / 4

private theorem c_pos : 0 < c := by
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

private theorem c_half_lt : (1 : ℝ) / 2 < c := by
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (3 : ℝ) < 2 * Real.log 2 := by
    calc
      _ < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by
        have hp := Real.log_pow (2 : ℝ) 2
        norm_num at hp
        exact hp
  unfold c
  rw [lt_div_iff₀ h3]
  linarith

private theorem g_zero : g 0 = 0 := by simp [g]

private theorem contDiff_g : ContDiff ℝ ⊤ g := by
  unfold g
  fun_prop

private theorem K_nonneg : 0 ≤ K := by unfold K; positivity
private theorem M_nonneg : 0 ≤ M := div_nonneg K_nonneg (by norm_num)

private theorem cutoff_two : primeCutoff 2 = {2} := by
  norm_num [primeCutoff]
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hn⟩, hp⟩
    have h2 := hp.two_le
    omega
  · rintro rfl
    norm_num

private theorem cutoff_three : primeCutoff 3 = {2, 3} := by
  norm_num [primeCutoff]
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hn⟩, hp⟩
    have h2 := hp.two_le
    omega
  · rintro (rfl | rfl) <;> norm_num

private theorem actualEuler_two (s : ℝ) : actualEuler 2 s = 1 - (2 : ℝ) ^ (-s) := by
  change (∏ p ∈ primeCutoff 2, (1 - (p : ℝ) ^ (-s))) = _
  rw [cutoff_two]
  simp

private theorem actualEuler_three (s : ℝ) :
    actualEuler 3 s = (1 - (2 : ℝ) ^ (-s)) * (1 - (3 : ℝ) ^ (-s)) := by
  change (∏ p ∈ primeCutoff 3, (1 - (p : ℝ) ^ (-s))) = _
  rw [cutoff_three]
  simp

private theorem fixedClockSlope_two : fixedClockSlope 2 = c := by
  norm_num [fixedClockSlope, cutoff_two, c]

private theorem fixedClockSlope_three : fixedClockSlope 3 = c + 1 / 2 := by
  norm_num [fixedClockSlope, cutoff_three, c]
  have h3 : Real.log (3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [h3]


private def gSlope (v : ℝ) : ℝ :=
  2 * Real.exp (-v) + c * Real.exp (-c * v) -
    (c + 1) * Real.exp (-(c + 1) * v) - 1

private def gCurvature (v : ℝ) : ℝ :=
  -2 * Real.exp (-v) - c ^ 2 * Real.exp (-c * v) +
    (c + 1) ^ 2 * Real.exp (-(c + 1) * v)

private def gBracket (v : ℝ) : ℝ :=
  (c + 1) ^ 2 - 2 * Real.exp (c * v) - c ^ 2 * Real.exp v

private theorem exp_mul_cancel (k v : ℝ) :
    Real.exp (k * v) * Real.exp (-k * v) = 1 := by
  rw [← Real.exp_add]
  have he : k * v + -k * v = 0 := by ring
  rw [he, Real.exp_zero]

private theorem hasDerivAt_exp_neg_mul (k v : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (-k * w))
      (-k * Real.exp (-k * v)) v := by
  simpa only [id_eq, mul_one, mul_comm] using
    ((hasDerivAt_id v).const_mul (-k)).exp

private theorem hasDerivAt_g (v : ℝ) : HasDerivAt g (gSlope v) v := by
  have hd := (((hasDerivAt_exp_neg_mul c v).const_sub 2).mul
    ((hasDerivAt_exp_neg_mul 1 v).const_sub 1)).sub (hasDerivAt_id v)
  have he : Real.exp (-c * v) * Real.exp (-v) =
      Real.exp (-(c + 1) * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert hd using 1 <;> try rfl
  all_goals
    first
    | (funext w; simp only [g, neg_one_mul, id_eq, Pi.mul_apply, Pi.sub_apply])
    | (simp only [gSlope, neg_one_mul, id_eq, mul_one]; rw [← he]; ring)

private theorem hasDerivAt_gSlope (v : ℝ) :
    HasDerivAt gSlope (gCurvature v) v := by
  have hd := (((hasDerivAt_exp_neg_mul 1 v).const_mul 2).add
    ((hasDerivAt_exp_neg_mul c v).const_mul c)).sub
      ((hasDerivAt_exp_neg_mul (c + 1) v).const_mul (c + 1))
  have hh := hd.sub_const 1
  convert hh using 1 <;> try rfl
  all_goals
    first
    | (funext w; simp only [gSlope, neg_one_mul, id_eq, Pi.mul_apply, Pi.sub_apply,
        Pi.add_apply])
    | (simp only [gCurvature, neg_one_mul, id_eq, mul_one]; ring)

private theorem hasDerivAt_gBracket (v : ℝ) :
    HasDerivAt gBracket
      (-2 * c * Real.exp (c * v) - c ^ 2 * Real.exp v) v := by
  have hd := ((hasDerivAt_const v ((c + 1) ^ 2)).sub
    (((hasDerivAt_id v).const_mul c).exp.const_mul 2)).sub
      ((hasDerivAt_id v).exp.const_mul (c ^ 2))
  convert hd using 1 <;> try rfl
  all_goals (simp only [id_eq, mul_one]; ring)

private theorem gCurvature_factor (v : ℝ) :
    gCurvature v = Real.exp (-(c + 1) * v) * gBracket v := by
  have h1 : Real.exp (-(c + 1) * v) * Real.exp (c * v) = Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(c + 1) * v) * Real.exp v = Real.exp (-c * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gCurvature gBracket
  calc
    _ = (c + 1) ^ 2 * Real.exp (-(c + 1) * v) -
        2 * (Real.exp (-(c + 1) * v) * Real.exp (c * v)) -
        c ^ 2 * (Real.exp (-(c + 1) * v) * Real.exp v) := by rw [h1, h2]; ring
    _ = _ := by ring

private theorem gBracket_strictAnti (hc : 0 < c) : StrictAnti gBracket := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_gBracket
  intro v
  have h1 : 0 < 2 * c * Real.exp (c * v) := by positivity
  have h2 : 0 ≤ c ^ 2 * Real.exp v := by positivity
  linarith

private theorem gBracket_negative_endpoint (hc : 0 < c) :
    ∃ w : ℝ, 0 < w ∧ gBracket w < 0 := by
  let w : ℝ := ((c + 1) ^ 2 + 1) / c
  have hw : 0 < w := by dsimp [w]; positivity
  have hcw : c * w = (c + 1) ^ 2 + 1 := by
    dsimp [w]
    exact mul_div_cancel₀ _ hc.ne'
  have he := Real.add_one_le_exp (c * w)
  rw [hcw] at he
  have hlast : 0 ≤ c ^ 2 * Real.exp w := by positivity
  refine ⟨w, hw, ?_⟩
  unfold gBracket
  rw [hcw]
  nlinarith [sq_nonneg (c + 1)]

private theorem gSlope_negative_endpoint (hc : 0 < c) {q : ℝ} (hq : 0 < q) :
    gSlope (q + 4) < 0 := by
  let y : ℝ := q + 4
  have hy : 4 ≤ y := by dsimp [y]; linarith
  have he1 : 4 ≤ Real.exp y := by
    have h := Real.add_one_le_exp y
    linarith
  have he2 : 4 * c ≤ Real.exp (c * y) := by
    have h := Real.add_one_le_exp (c * y)
    have hm := mul_le_mul_of_nonneg_left hy hc.le
    linarith
  have h1 := mul_le_mul_of_nonneg_right he1 (Real.exp_pos (-y)).le
  have h2 := mul_le_mul_of_nonneg_right he2 (Real.exp_pos (-c * y)).le
  have hi1 : Real.exp y * Real.exp (-y) = 1 := by
    simpa only [one_mul, neg_one_mul] using exp_mul_cancel 1 y
  rw [hi1] at h1
  rw [exp_mul_cancel c y] at h2
  have hlast : 0 ≤ (c + 1) * Real.exp (-(c + 1) * y) := by positivity
  change gSlope y < 0
  unfold gSlope
  nlinarith

private theorem g_negative_endpoint {t : ℝ} (ht : 0 < t) : g (t + 3) < 0 := by
  let y : ℝ := t + 3
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hmul : (2 - Real.exp (-c * y)) * (1 - Real.exp (-y)) ≤ 2 := by
    have hm := mul_le_mul_of_nonneg_right
      (show 2 - Real.exp (-c * y) ≤ 2 by linarith [Real.exp_pos (-c * y)])
      (sub_nonneg.mpr he)
    have hs : 2 * (1 - Real.exp (-y)) ≤ 2 := by linarith [Real.exp_pos (-y)]
    exact hm.trans hs
  change g y < 0
  unfold g
  dsimp [y] at hmul ⊢
  linarith

/-- The actual finite-prime numerator has one positive crossing with strict signs.
All calculus suppliers above are internal to this complete constructed endpoint. -/
private theorem g_unique_crossing (hcHalf : (1 : ℝ) / 2 < c) :
    ∃ r : ℝ, 0 < r ∧ g r = 0 ∧
      (∀ v : ℝ, v ∈ Set.Ioo 0 r → 0 < g v) ∧
      (∀ v : ℝ, r < v → g v < 0) := by
  have hc : 0 < c := by linarith
  have hBA := gBracket_strictAnti hc
  have hB0 : 0 < gBracket 0 := by
    simp only [gBracket, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  rcases gBracket_negative_endpoint hc with ⟨w, hw, hwB⟩
  have hBI : ContinuousOn gBracket (Set.Icc 0 w) :=
    fun v hv => (hasDerivAt_gBracket v).continuousAt.continuousWithinAt
  rcases intermediate_value_Icc' hw.le hBI
      (show (0 : ℝ) ∈ Set.Icc (gBracket w) (gBracket 0) from ⟨hwB.le, hB0.le⟩) with
    ⟨q, hqI, hqB⟩
  have hq : 0 < q := by
    by_contra hn
    have hz : q = 0 := le_antisymm (le_of_not_gt hn) hqI.1
    rw [hz] at hqB
    linarith
  have hBpos {v : ℝ} (hv : v < q) : 0 < gBracket v := by
    have h := hBA hv
    simpa only [hqB] using h
  have hBneg {v : ℝ} (hv : q < v) : gBracket v < 0 := by
    have h := hBA hv
    simpa only [hqB] using h
  have hSM : StrictMonoOn gSlope (Set.Icc 0 q) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 q)
      (fun v hv => (hasDerivAt_gSlope v).continuousAt.continuousWithinAt)
    intro v hv
    have hv' : v ∈ Set.Ioo 0 q := by simpa only [interior_Icc] using hv
    rw [(hasDerivAt_gSlope v).deriv, gCurvature_factor]
    exact mul_pos (Real.exp_pos _) (hBpos hv'.2)
  have hSA : StrictAntiOn gSlope (Set.Ici q) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici q)
      (fun v hv => (hasDerivAt_gSlope v).continuousAt.continuousWithinAt)
    intro v hv
    have hv' : q < v := by simpa only [interior_Ici, Set.mem_Ioi] using hv
    rw [(hasDerivAt_gSlope v).deriv, gCurvature_factor]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hBneg hv')
  have hS0 : gSlope 0 = 0 := by
    simp only [gSlope, neg_zero, mul_zero, Real.exp_zero, mul_one]
    ring
  have hSq : 0 < gSlope q := by
    have h := hSM ⟨le_rfl, hq.le⟩ ⟨hq.le, le_rfl⟩ hq
    simpa only [hS0] using h
  have hSI : ContinuousOn gSlope (Set.Icc q (q + 4)) :=
    fun v hv => (hasDerivAt_gSlope v).continuousAt.continuousWithinAt
  rcases intermediate_value_Icc' (by linarith : q ≤ q + 4) hSI
      (show (0 : ℝ) ∈ Set.Icc (gSlope (q + 4)) (gSlope q) from
        ⟨(gSlope_negative_endpoint hc hq).le, hSq.le⟩) with ⟨t, htI, htS⟩
  have hqt : q < t := by
    by_contra hn
    have hz : t = q := le_antisymm (le_of_not_gt hn) htI.1
    rw [hz] at htS
    linarith
  have ht : 0 < t := hq.trans hqt
  have hSpos {v : ℝ} (hv : 0 < v) (hvt : v < t) : 0 < gSlope v := by
    by_cases hvq : v ≤ q
    · have h := hSM ⟨le_rfl, hq.le⟩ ⟨hv.le, hvq⟩ hv
      simpa only [hS0] using h
    · have h := hSA (lt_of_not_ge hvq).le hqt.le hvt
      simpa only [htS] using h
  have hSneg {v : ℝ} (hv : t < v) : gSlope v < 0 := by
    have h := hSA hqt.le ((hqt.trans hv).le) hv
    simpa only [htS] using h
  have hGM : StrictMonoOn g (Set.Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (fun v hv => (hasDerivAt_g v).continuousAt.continuousWithinAt)
    intro v hv
    have hv' : v ∈ Set.Ioo 0 t := by simpa only [interior_Icc] using hv
    rw [(hasDerivAt_g v).deriv]
    exact hSpos hv'.1 hv'.2
  have hGA : StrictAntiOn g (Set.Ici t) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici t)
      (fun v hv => (hasDerivAt_g v).continuousAt.continuousWithinAt)
    intro v hv
    have hv' : t < v := by simpa only [interior_Ici, Set.mem_Ioi] using hv
    rw [(hasDerivAt_g v).deriv]
    exact hSneg hv'
  have hg0 : g 0 = 0 := by simp [g]
  have hgt : 0 < g t := by
    have h := hGM ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
    simpa only [hg0] using h
  have hGI : ContinuousOn g (Set.Icc t (t + 3)) :=
    fun v hv => (hasDerivAt_g v).continuousAt.continuousWithinAt
  rcases intermediate_value_Icc' (by linarith : t ≤ t + 3) hGI
      (show (0 : ℝ) ∈ Set.Icc (g (t + 3)) (g t) from
        ⟨(g_negative_endpoint ht).le, hgt.le⟩) with ⟨r, hrI, hrG⟩
  have htr : t < r := by
    by_contra hn
    have hz : r = t := le_antisymm (le_of_not_gt hn) hrI.1
    rw [hz] at hrG
    linarith
  refine ⟨r, ht.trans htr, hrG, ?_, ?_⟩
  · intro v hv
    by_cases hvt : v ≤ t
    · have h := hGM ⟨le_rfl, ht.le⟩ ⟨hv.1.le, hvt⟩ hv.1
      simpa only [hg0] using h
    · have h := hGA (lt_of_not_ge hvt).le htr.le hv.2
      simpa only [hrG] using h
  · intro v hv
    have h := hGA htr.le (htr.trans hv).le hv
    simpa only [hrG] using h


private theorem g_deriv_zero : deriv g 0 = 0 := by
  rw [(hasDerivAt_g 0).deriv]
  simp [gSlope]
  ring

private theorem g_iteratedDeriv_two_zero : iteratedDeriv 2 g 0 = 2 * c - 1 := by
  have hd : deriv g = gSlope := funext (fun v => (hasDerivAt_g v).deriv)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hd, (hasDerivAt_gSlope 0).deriv]
  simp [gCurvature]
  ring

private theorem gCurvature_bound {v : ℝ} (hv : 0 ≤ v) : |gCurvature v| ≤ K := by
  have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hec : Real.exp (-c * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [c_pos])
  have hec1 : Real.exp (-(c + 1) * v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [c_pos])
  have h1 : |-2 * Real.exp (-v)| ≤ 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    norm_num
    linarith
  have h2 : |c ^ 2 * Real.exp (-c * v)| ≤ c ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg c]
  have h3 : |(c + 1) ^ 2 * Real.exp (-(c + 1) * v)| ≤ (c + 1) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (c + 1)]
  have hsub := abs_sub (-2 * Real.exp (-v)) (c ^ 2 * Real.exp (-c * v))
  have hadd := abs_add_le (-2 * Real.exp (-v) - c ^ 2 * Real.exp (-c * v))
    ((c + 1) ^ 2 * Real.exp (-(c + 1) * v))
  unfold gCurvature K
  linarith

private theorem g_quadratic {v : ℝ} (hv : 0 ≤ v) : |g v| ≤ K * v ^ 2 / 2 := by
  exact exact_zero_quadratic_bound g gSlope gCurvature hv g_zero
    (by simp [gSlope]; ring)
    (fun w _ => hasDerivAt_g w) (fun w _ => hasDerivAt_gSlope w)
    (fun w hw => by simpa only [Real.norm_eq_abs] using gCurvature_bound hw.1)

private theorem h_bound (v : ℝ) (hv : 0 ≤ v) : |h v| ≤ M := by
  by_cases hv0 : v = 0
  · simp [h, hv0, M_nonneg]
  · have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv0
    unfold h M
    rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * v ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * v ^ 2)).mpr
    nlinarith [g_quadratic hv]

private theorem signed_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * h v) (Ioi 0) := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * g v / v ^ 2) (Ioi 0) :=
    signed_integrable_of_quadratic g hσ contDiff_g.continuous.continuousOn
      (fun v hv => by
        calc
          |g v| ≤ K * v ^ 2 / 2 := g_quadratic hv
          _ ≤ K * (1 + v) * v ^ 2 / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg v)
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (show (1 : ℝ) ≤ 1 + v by linarith) K_nonneg)
  apply IntegrableOn.congr_fun (hi.div_const 2) _ measurableSet_Ioi
  intro v _
  simp only [h]
  ring


private theorem h_zero_limit :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 ((c - 1 / 2) / 2)) := by
  have hpoly (v : ℝ) :
      taylorWithinEval g 2 univ 0 v = (c - 1 / 2) * v ^ 2 := by
    rw [taylorWithinEval_succ g 1 univ 0 v,
      taylorWithinEval_succ g 0 univ 0 v,
      taylor_within_zero_eval]
    simp only [iteratedDerivWithin_univ, iteratedDeriv_one,
      g_zero, g_deriv_zero,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one,
      zero_add, one_mul, sub_zero, pow_one, smul_eq_mul]
    norm_num
    rw [g_iteratedDeriv_two_zero]
    ring
  have ht := Real.taylor_tendsto (f := g) (x₀ := (0 : ℝ))
    (n := 2) (s := univ) convex_univ (mem_univ 0)
    (contDiff_g.of_le le_top).contDiffOn
  simp only [nhdsWithin_univ, sub_zero, hpoly] at ht
  have hrem : Tendsto
      (fun v : ℝ => (g v - (c - 1 / 2) * v ^ 2) / v ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := ht.mono_left nhdsWithin_le_nhds
  have hsum := (hrem.div_const 2).add_const ((c - 1 / 2) / 2)
  have heq :
      (fun v : ℝ => (g v - (c - 1 / 2) * v ^ 2) / v ^ 2 / 2 +
        (c - 1 / 2) / 2) =ᶠ[𝓝[>] (0 : ℝ)] h := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    unfold h
    field_simp [(mem_Ioi.mp hv).ne']
    <;> ring
  apply Tendsto.congr' heq
  simpa only [zero_div, zero_add] using hsum

private theorem signedIntegral_high_damping_limit :
    Tendsto (fun σ : ℝ => σ * signedIntegral σ) atTop
      (𝓝 ((c - 1 / 2) / 2)) := by
  let F : ℝ → ℝ → ℝ := fun σ t => Real.exp (-t) * h (t / σ)
  have hh : Measurable h := by
    unfold h
    exact contDiff_g.continuous.measurable.div
      (measurable_const.mul (measurable_id.pow_const 2))
  have hmeas (σ : ℝ) :
      AEStronglyMeasurable (F σ) (volume.restrict (Ioi (0 : ℝ))) := by
    exact ((Real.continuous_exp.comp continuous_id.neg).measurable.mul
      (hh.comp (measurable_id.div_const σ))).aestronglyMeasurable
  have hmajor : Integrable
      (fun t : ℝ => M * Real.exp (-t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (_root_.integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul M
  have hbound : ∀ᶠ σ : ℝ in atTop,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ‖F σ t‖ ≤ M * Real.exp (-t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t) * |h (t / σ)| ≤ Real.exp (-t) * M :=
        mul_le_mul_of_nonneg_left
          (h_bound (t / σ) (div_nonneg (mem_Ioi.mp ht).le hσ.le))
          (Real.exp_pos _).le
      _ = M * Real.exp (-t) := mul_comm _ _
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun σ : ℝ => F σ t) atTop
        (𝓝 (Real.exp (-t) * ((c - 1 / 2) / 2))) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have harg : Tendsto (fun σ : ℝ => t / σ) atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨Filter.Tendsto.const_div_atTop
        (tendsto_id : Tendsto (fun σ : ℝ => σ) atTop atTop) t, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
      exact div_pos (mem_Ioi.mp ht) hσ
    exact (h_zero_limit.comp harg).const_mul (Real.exp (-t))
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := atTop)
    (F := F) (f := fun t : ℝ => Real.exp (-t) * ((c - 1 / 2) / 2))
    (fun t : ℝ => M * Real.exp (-t))
    (Eventually.of_forall hmeas) hbound hmajor hlim
  have htarget :
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * ((c - 1 / 2) / 2)) =
        (c - 1 / 2) / 2 := by
    rw [integral_mul_const, _root_.integral_exp_neg_Ioi_zero, one_mul]
  change Tendsto (fun σ : ℝ => ∫ t in Ioi (0 : ℝ), F σ t) atTop
    (𝓝 (∫ t in Ioi (0 : ℝ), Real.exp (-t) * ((c - 1 / 2) / 2))) at hdct
  rw [htarget] at hdct
  have hscale (σ : ℝ) (hσ : 0 < σ) :
      σ * signedIntegral σ = ∫ t in Ioi (0 : ℝ), F σ t := by
    have hc := integral_comp_mul_left_Ioi' (fun t : ℝ => F σ t) 0 hσ
    have heq : (fun v : ℝ => F σ (σ * v)) =
        (fun v : ℝ => Real.exp (-σ * v) * h v) := by
      funext v
      dsimp only [F]
      rw [mul_div_cancel_left₀ v hσ.ne', neg_mul]
    rw [heq] at hc
    simpa only [mul_zero, smul_eq_mul, signedIntegral] using hc
  apply Tendsto.congr' _ hdct
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  exact (hscale σ hσ).symm

open Real


private theorem signedIntegral_continuousOn
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, 0 ≤ v → |h v| ≤ M)
    (hi : ∀ {σ : ℝ}, 0 < σ →
      IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * h v) (Ioi 0)) :
    ContinuousOn signedIntegral (Ioi 0) := by
  rcases hb with ⟨M, hM0, hM⟩
  intro σ₀ hσ₀
  have hσ₀pos : 0 < σ₀ := hσ₀
  have hhalf : 0 < σ₀ / 2 := half_pos hσ₀pos
  have hnear : ∀ᶠ σ : ℝ in 𝓝 σ₀, σ₀ / 2 < σ :=
    eventually_gt_nhds (by linarith)
  have hmeas : ∀ᶠ σ : ℝ in 𝓝 σ₀,
      AEStronglyMeasurable (fun v : ℝ => Real.exp (-σ * v) * h v)
        (volume.restrict (Ioi 0)) := by
    filter_upwards [hnear] with σ hσ
    exact (hi (by linarith : 0 < σ)).aestronglyMeasurable
  have hdom : ∀ᶠ σ : ℝ in 𝓝 σ₀, ∀ᵐ v : ℝ ∂volume.restrict (Ioi 0),
      ‖Real.exp (-σ * v) * h v‖ ≤ M * Real.exp (-(σ₀ / 2) * v) := by
    filter_upwards [hnear] with σ hσ
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-σ * v) * |h v| ≤ Real.exp (-σ * v) * M :=
        mul_le_mul_of_nonneg_left (hM v hvpos.le) (Real.exp_pos _).le
      _ ≤ Real.exp (-(σ₀ / 2) * v) * M :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith)) hM0
      _ = M * Real.exp (-(σ₀ / 2) * v) := mul_comm _ _
  have hdomint : Integrable (fun v : ℝ => M * Real.exp (-(σ₀ / 2) * v))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 hhalf).const_mul M
  have hcont : ∀ᵐ v : ℝ ∂volume.restrict (Ioi 0),
      ContinuousAt (fun σ : ℝ => Real.exp (-σ * v) * h v) σ₀ := by
    exact Filter.Eventually.of_forall (fun v => by fun_prop)
  have hfull : ContinuousAt
      (fun σ : ℝ => ∫ v in Ioi 0, Real.exp (-σ * v) * h v) σ₀ :=
    MeasureTheory.continuousAt_of_dominated hmeas hdom hdomint hcont
  change ContinuousWithinAt
    (fun σ : ℝ => ∫ v in Ioi 0, Real.exp (-σ * v) * h v) (Ioi 0) σ₀
  exact hfull.continuousWithinAt

private theorem tilted_signedIntegral_strictMonoOn {r : ℝ}
    (hr : 0 < r)
    (hleft : ∀ v : ℝ, v ∈ Ioo 0 r → 0 < g v)
    (hright : ∀ v : ℝ, v ∈ Ioi r → g v < 0)
    (hi : ∀ {σ : ℝ}, 0 < σ →
      IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * h v) (Ioi 0)) :
    StrictMonoOn (fun σ : ℝ => Real.exp (σ * r) * signedIntegral σ) (Ioi 0) := by
  let F : ℝ → ℝ → ℝ := fun σ v => Real.exp (σ * (r - v)) * h v
  have hF_eq (σ v : ℝ) :
      Real.exp (σ * r) * (Real.exp (-σ * v) * h v) = F σ v := by
    dsimp [F]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hFint (σ : ℝ) (hσ : 0 < σ) : IntegrableOn (F σ) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((hi hσ).const_mul (Real.exp (σ * r)))
      (fun v _ => hF_eq σ v) measurableSet_Ioi
  have hF_integral (σ : ℝ) :
      (∫ v in Ioi 0, F σ v) = Real.exp (σ * r) * signedIntegral σ := by
    calc
      (∫ v in Ioi 0, F σ v) =
          ∫ v in Ioi 0, Real.exp (σ * r) * (Real.exp (-σ * v) * h v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        exact (hF_eq σ v).symm
      _ = Real.exp (σ * r) * signedIntegral σ := by
        rw [integral_const_mul]
        rfl
  intro σ₁ hσ₁ σ₂ hσ₂ hσ₁₂
  have hσ₁pos : 0 < σ₁ := hσ₁
  have hσ₂pos : 0 < σ₂ := hσ₂
  let d : ℝ → ℝ := fun v => F σ₂ v - F σ₁ v
  have hdint : IntegrableOn d (Ioi 0) :=
    (hFint σ₂ hσ₂pos).sub (hFint σ₁ hσ₁pos)
  have hdpos_left (v : ℝ) (hv : v ∈ Ioo 0 r) : 0 < d v := by
    have hvpos : 0 < v := hv.1
    have hhpos : 0 < h v := by
      dsimp [h]
      exact div_pos (hleft v hv) (mul_pos (by norm_num) (pow_pos hvpos 2))
    have hexp : Real.exp (σ₁ * (r - v)) < Real.exp (σ₂ * (r - v)) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hσ₁₂ (sub_pos.mpr hv.2))
    dsimp [d, F]
    exact sub_pos.mpr (mul_lt_mul_of_pos_right hexp hhpos)
  have hdnonneg : ∀ᵐ v : ℝ ∂volume.restrict (Ioi 0), 0 ≤ d v := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hv
    rcases lt_trichotomy v r with hvr | hvr | hvr
    · exact (hdpos_left v ⟨hvpos, hvr⟩).le
    · simp [d, F, hvr]
    · have hhneg : h v < 0 := by
        dsimp [h]
        exact div_neg_of_neg_of_pos (hright v hvr)
          (mul_pos (by norm_num) (pow_pos hvpos 2))
      have hexp : Real.exp (σ₂ * (r - v)) < Real.exp (σ₁ * (r - v)) :=
        Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right hσ₁₂ (sub_neg.mpr hvr))
      dsimp [d, F]
      exact (sub_pos.mpr (mul_lt_mul_of_neg_right hexp hhneg)).le
  have hsupport : Ioo 0 r ⊆ Function.support d ∩ Ioi 0 := by
    intro v hv
    exact ⟨(hdpos_left v hv).ne', hv.1⟩
  have hvolume : 0 < volume (Ioo (0 : ℝ) r) := by
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr hr
  have hdpositive : 0 < ∫ v in Ioi 0, d v :=
    (setIntegral_pos_iff_support_of_nonneg_ae hdnonneg hdint).2
      (lt_of_lt_of_le hvolume (measure_mono hsupport))
  have hdiff : (∫ v in Ioi 0, d v) =
      Real.exp (σ₂ * r) * signedIntegral σ₂ -
        Real.exp (σ₁ * r) * signedIntegral σ₁ := by
    change (∫ v in Ioi 0, F σ₂ v - F σ₁ v) = _
    rw [integral_sub (hFint σ₂ hσ₂pos) (hFint σ₁ hσ₁pos),
      hF_integral σ₂, hF_integral σ₁]
  rw [hdiff] at hdpositive
  exact sub_pos.mp hdpositive


private theorem scaled_power_two (v : ℝ) :
    (2 : ℝ) ^ (-(1 + v / Real.log 3)) = (1 / 2) * Real.exp (-c * v) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * (-(1 + v / Real.log 3)) = -Real.log 2 + -c * v := by
    unfold c
    ring
  rw [he, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem scaled_power_three (v : ℝ) :
    (3 : ℝ) ^ (-(1 + v / Real.log 3)) = (1 / 3) * Real.exp (-v) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hn : Real.log (3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : Real.log 3 * (-(1 + v / Real.log 3)) = -Real.log 3 + -v := by
    field_simp [hn]
    ring
  rw [he, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  norm_num

private theorem fixedClockRatio_two (v : ℝ) :
    fixedClockRatio 2 v = 2 - Real.exp (-c * v) := by
  unfold fixedClockRatio
  rw [actualEuler_two, actualEuler_two, scaled_power_two]
  norm_num
  ring

private theorem fixedClockRatio_three (v : ℝ) :
    fixedClockRatio 3 v =
      (2 - Real.exp (-c * v)) * (3 / 2 - Real.exp (-v) / 2) := by
  unfold fixedClockRatio
  rw [actualEuler_three, actualEuler_three, scaled_power_two, scaled_power_three]
  norm_num
  ring

private def twoNumerator (v : ℝ) : ℝ := 1 - Real.exp (-c * v) - c * v
private def twoSlope (v : ℝ) : ℝ := c * Real.exp (-c * v) - c
private def twoCurvature (v : ℝ) : ℝ := -c ^ 2 * Real.exp (-c * v)

private theorem hasDerivAt_twoNumerator (v : ℝ) :
    HasDerivAt twoNumerator (twoSlope v) v := by
  have hd := ((hasDerivAt_exp_neg_mul c v).const_sub 1).sub
    ((hasDerivAt_id v).const_mul c)
  convert hd using 1 <;> try rfl
  simp only [twoSlope, mul_one]
  ring

private theorem hasDerivAt_twoSlope (v : ℝ) :
    HasDerivAt twoSlope (twoCurvature v) v := by
  have hd := ((hasDerivAt_exp_neg_mul c v).const_mul c).sub_const c
  convert hd using 1 <;> try rfl
  · simp [twoCurvature]
    ring

private theorem two_quadratic {v : ℝ} (hv : 0 ≤ v) :
    |twoNumerator v| ≤ c ^ 2 * v ^ 2 / 2 := by
  apply exact_zero_quadratic_bound twoNumerator twoSlope twoCurvature hv
    (by simp [twoNumerator]) (by simp [twoSlope])
    (fun w _ => hasDerivAt_twoNumerator w) (fun w _ => hasDerivAt_twoSlope w)
  intro w hw
  have he : Real.exp (-c * w) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [c_pos, hw.1])
  simp only [twoCurvature, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg c), abs_of_pos (Real.exp_pos _)]
  nlinarith [sq_nonneg c]

private theorem actualNumerator_two (v : ℝ) : actualNumerator 2 v = twoNumerator v := by
  rw [actualNumerator, fixedClockRatio_two, fixedClockSlope_two]
  unfold twoNumerator
  ring

private theorem actualNumerator_three (v : ℝ) :
    actualNumerator 3 v = twoNumerator v + g v / 2 := by
  rw [actualNumerator, fixedClockRatio_three, fixedClockSlope_three]
  unfold twoNumerator g
  ring

private theorem two_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * twoNumerator v / v ^ 2) (Ioi 0) := by
  apply signed_integrable_of_quadratic twoNumerator (C := c ^ 2) hσ
    (fun v _ => (hasDerivAt_twoNumerator v).continuousAt.continuousWithinAt)
  intro v hv
  calc
    |twoNumerator v| ≤ c ^ 2 * v ^ 2 / 2 := two_quadratic hv
    _ ≤ c ^ 2 * (1 + v) * v ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg v)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1 + v by linarith) (sq_nonneg c)

private theorem actual_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * actualNumerator 2 v / v ^ 2) (Ioi 0) ∧
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * actualNumerator 3 v / v ^ 2) (Ioi 0) := by
  have hi2 := two_integrable hσ
  have hid := signed_integrable hσ
  constructor
  · exact hi2.congr_fun (fun v _ => by rw [actualNumerator_two]) measurableSet_Ioi
  · apply IntegrableOn.congr_fun (hi2.add hid) _ measurableSet_Ioi
    intro v _
    simp only [Pi.add_apply]
    rw [actualNumerator_three]
    simp only [h]
    ring

private theorem actual_difference {σ : ℝ} (hσ : 0 < σ) :
    actualIntegral 3 σ - actualIntegral 2 σ = signedIntegral σ := by
  have hi := actual_integrable hσ
  unfold actualIntegral signedIntegral
  rw [← integral_sub hi.2 hi.1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [actualNumerator_three, actualNumerator_two]
  simp only [h]
  ring

private theorem h_tail {v : ℝ} (hv : 4 ≤ v) : h v ≤ -(1 / 4) / v := by
  have hv0 : 0 < v := by linarith
  have hec : Real.exp (-c * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [c_pos])
  have hev : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc0 := Real.exp_pos (-c * v)
  have he0 := Real.exp_pos (-v)
  have hprod : (2 - Real.exp (-c * v)) * (1 - Real.exp (-v)) ≤ 2 := by
    nlinarith
  have hg : g v ≤ -v / 2 := by unfold g; linarith
  unfold h
  apply (div_le_iff₀ (by positivity : 0 < 2 * v ^ 2)).mpr
  have heq : -(1 / 4) / v * (2 * v ^ 2) = -v / 2 := by
    field_simp [hv0.ne']
    ring
  rw [heq]
  exact hg

private theorem signedIntegral_low_bound {σ : ℝ} (hσ : 0 < σ) (hσ4 : σ ≤ 1 / 4) :
    signedIntegral σ ≤ 4 * M - (Real.exp (-1) / 4) * Real.log (1 / (4 * σ)) := by
  let R : ℝ := 1 / σ
  let f : ℝ → ℝ := fun v => Real.exp (-σ * v) * h v
  let a : ℝ := Real.exp (-1) / 4
  have hR : 4 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hσ).mpr
    linarith
  have hR0 : 0 < R := by linarith
  have hf : IntegrableOn f (Ioi 0) := signed_integrable hσ
  have hf4 : IntegrableOn f (Ioi 4) := hf.mono_set (Ioi_subset_Ioi (by norm_num))
  have hfR : IntegrableOn f (Ioi R) := hf.mono_set (Ioi_subset_Ioi hR0.le)
  have hnearI : IntervalIntegrable f volume 0 4 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 4)).mpr
      (hf.mono_set Ioc_subset_Ioi_self)
  have hmidI : IntervalIntegrable f volume 4 R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
      (hf.mono_set (fun v hv => by
        show 0 < v
        have := hv.1
        linarith))
  have hnear : (∫ v in (0 : ℝ)..4, f v) ≤ 4 * M := by
    have he := intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 4) hnearI
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 4)
      (fun v hv => by
        have hexp : Real.exp (-σ * v) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
        calc
          f v ≤ Real.exp (-σ * v) * |h v| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
          _ ≤ Real.exp (-σ * v) * M :=
            mul_le_mul_of_nonneg_left (h_bound v hv.1.le) (Real.exp_pos _).le
          _ ≤ M := by nlinarith [M_nonneg])
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using he
  have hmajorI : IntervalIntegrable (fun v : ℝ => -a * (1 / v)) volume 4 R := by
    apply (ContinuousOn.const_mul _ (-a)).intervalIntegrable_of_Icc hR
    exact continuousOn_const.div continuousOn_id (fun v hv => by have := hv.1; linarith)
  have hmid : (∫ v in (4 : ℝ)..R, f v) ≤ -a * Real.log (R / 4) := by
    have he := intervalIntegral.integral_mono_on_of_le_Ioo hR hmidI hmajorI
      (fun v hv => by
        have hv0 : 0 < v := by have := hv.1; linarith
        have hexp : Real.exp (-1) ≤ Real.exp (-σ * v) := by
          apply Real.exp_le_exp.mpr
          have hvR := hv.2.le
          have hσv : σ * v ≤ 1 := by
            have hs := mul_le_mul_of_nonneg_left hvR hσ.le
            dsimp [R] at hs
            rw [mul_one_div_cancel hσ.ne'] at hs
            exact hs
          linarith
        have ht := h_tail hv.1.le
        dsimp [f, a]
        calc
          Real.exp (-σ * v) * h v ≤ Real.exp (-σ * v) * (-(1 / 4) / v) :=
            mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
          _ ≤ Real.exp (-1) * (-(1 / 4) / v) :=
            mul_le_mul_of_nonpos_right hexp
              (div_nonpos_of_nonpos_of_nonneg (by norm_num) hv0.le)
          _ = -(Real.exp (-1) / 4) * (1 / v) := by ring)
    simpa only [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos (by norm_num : (0 : ℝ) < 4) hR0] using he
  have htail : (∫ v in Ioi R, f v) ≤ 0 := by
    apply integral_nonpos_of_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hv0 : 0 < v := hR0.trans hv
    have ht := h_tail (hR.trans hv.le)
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (ht.trans (div_nonpos_of_nonpos_of_nonneg (by norm_num) hv0.le))
  have hs0 := intervalIntegral.integral_interval_add_Ioi hf hf4
  have hs1 := intervalIntegral.integral_interval_add_Ioi hf4 hfR
  have hlog : R / 4 = 1 / (4 * σ) := by dsimp [R]; ring
  rw [hlog] at hmid
  change (∫ v in Ioi 0, f v) ≤ _
  dsimp [a] at hmid
  nlinarith

private theorem signedIntegral_negative : ∃ σ : ℝ, 0 < σ ∧ signedIntegral σ < 0 := by
  let σ : ℝ := 1 / (4 * Real.exp (16 * Real.exp 1 * M + 1))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hE : 1 ≤ Real.exp (16 * Real.exp 1 * M + 1) :=
    Real.one_le_exp_iff.mpr (by
      have hp := mul_nonneg (Real.exp_pos (1 : ℝ)).le M_nonneg
      nlinarith)
  have hσ4 : σ ≤ 1 / 4 := by
    dsimp [σ]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    nlinarith
  have hlog : Real.log (1 / (4 * σ)) = 16 * Real.exp 1 * M + 1 := by
    have heq : 1 / (4 * σ) = Real.exp (16 * Real.exp 1 * M + 1) := by
      dsimp [σ]
      field_simp
    rw [heq, Real.log_exp]
  have heprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hb := signedIntegral_low_bound hσ hσ4
  rw [hlog] at hb
  have hcancel : Real.exp (-1) / 4 * (16 * Real.exp 1 * M + 1) =
      4 * M + Real.exp (-1) / 4 := by
    calc
      _ = 4 * M * (Real.exp (-1) * Real.exp 1) + Real.exp (-1) / 4 := by ring
      _ = _ := by rw [heprod]; ring
  rw [hcancel] at hb
  refine ⟨σ, hσ, ?_⟩
  linarith [Real.exp_pos (-1)]

private theorem signedIntegral_positive : ∃ σ : ℝ, 0 < σ ∧ 0 < signedIntegral σ := by
  have hA : 0 < (c - 1 / 2) / 2 := by linarith [c_half_lt]
  have he : ∀ᶠ σ : ℝ in atTop, 0 < σ * signedIntegral σ :=
    signedIntegral_high_damping_limit.eventually (eventually_gt_nhds hA)
  rcases (he.and (eventually_gt_atTop (0 : ℝ))).exists with ⟨σ, hprod, hσ⟩
  exact ⟨σ, hσ, (mul_pos_iff_of_pos_left hσ).mp hprod⟩

/-- The actual insertion from primes {2} to {2,3}, at the common clock log 3,
has exactly one positive damping transition in its complete compensated integral.
This statement concerns the first Laplace term, not the full Robin pairing. -/
theorem result :
    (∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun v : ℝ =>
        Real.exp (-σ * v) * actualNumerator 2 v / v ^ 2) (Ioi 0) ∧
      IntegrableOn (fun v : ℝ =>
        Real.exp (-σ * v) * actualNumerator 3 v / v ^ 2) (Ioi 0)) ∧
    ∃ σstar : ℝ, 0 < σstar ∧
      actualIntegral 3 σstar - actualIntegral 2 σstar = 0 ∧
      (∀ σ : ℝ, 0 < σ → σ < σstar →
        actualIntegral 3 σ - actualIntegral 2 σ < 0) ∧
      (∀ σ : ℝ, σstar < σ →
        0 < actualIntegral 3 σ - actualIntegral 2 σ) := by
  refine ⟨fun σ hσ => actual_integrable hσ, ?_⟩
  rcases g_unique_crossing c_half_lt with ⟨r, hr, _, hleft, hright⟩
  have hmono := tilted_signedIntegral_strictMonoOn hr hleft
    (fun v hv => hright v hv) (fun hσ => signed_integrable hσ)
  rcases signedIntegral_negative with ⟨lo, hlo, hneg⟩
  rcases signedIntegral_positive with ⟨hi, hhi, hpos⟩
  have hlow : Real.exp (lo * r) * signedIntegral lo < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  have hhigh : 0 < Real.exp (hi * r) * signedIntegral hi :=
    mul_pos (Real.exp_pos _) hpos
  have hlh : lo < hi := by
    by_contra hn
    have hm := hmono.monotoneOn hhi hlo (le_of_not_gt hn)
    linarith
  have hcont := signedIntegral_continuousOn ⟨M, M_nonneg, h_bound⟩
    (fun hσ => signed_integrable hσ)
  have hcontI : ContinuousOn signedIntegral (Icc lo hi) :=
    hcont.mono (fun σ hσ => hlo.trans_le hσ.1)
  rcases intermediate_value_Icc hlh.le hcontI
    (show (0 : ℝ) ∈ Icc (signedIntegral lo) (signedIntegral hi) from
      ⟨hneg.le, hpos.le⟩) with ⟨σstar, hstarI, hstar⟩
  have hstarpos : 0 < σstar := hlo.trans_le hstarI.1
  refine ⟨σstar, hstarpos, ?_, ?_, ?_⟩
  · rw [actual_difference hstarpos, hstar]
  · intro σ hσ hσstar
    rw [actual_difference hσ]
    have hs := hmono hσ hstarpos hσstar
    dsimp only at hs
    rw [hstar, mul_zero] at hs
    exact neg_of_mul_neg_right hs (Real.exp_pos _).le
  · intro σ hstarσ
    have hσ : 0 < σ := hstarpos.trans hstarσ
    rw [actual_difference hσ]
    have hs := hmono hstarpos hσ hstarσ
    dsimp only at hs
    rw [hstar, mul_zero] at hs
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hs

end D5.S3.Arith.Robin.ActualPrimeInsertionDampingTransition
