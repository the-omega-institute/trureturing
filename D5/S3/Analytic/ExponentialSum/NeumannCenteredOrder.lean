/- GID: D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder
   generality: G
   mirror-B: D5/B/S3/Analytic/ExponentialSum/NeumannCenteredOrder
   mirror-E: none(waiver:analytic-spectral-comparison)
   anchors: []
   utility: none
   digest: A balanced finite signed spectrum gives strict centered prefixes, strict stop-loss inequalities, and an exact midpoint pulse gap. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Centered order of real port kernels with a balanced finite signed exponential difference. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NeumannCenteredOrder

open MeasureTheory Set
open scoped BigOperators

/-- The signed difference has one fast positive mode and finitely many slower negative modes.
The inverse-rate balance cancels the constant terms in its antiderivative. -/
structure BalancedSpectrum (ι : Type*) where
  modes : Finset ι
  fastRate : ℝ
  fastWeight : ℝ
  rate : ι → ℝ
  weight : ι → ℝ
  rate_pos : ∀ i ∈ modes, 0 < rate i
  rate_lt : ∀ i ∈ modes, rate i < fastRate
  weight_nonneg : ∀ i ∈ modes, 0 ≤ weight i
  weight_pos : ∃ i ∈ modes, 0 < weight i
  balance : fastWeight / fastRate = ∑ i ∈ modes, weight i / rate i

variable {ι : Type*}

/-- The signed kernel difference specified by the spectrum. -/
def BalancedSpectrum.difference (S : BalancedSpectrum ι) (t : ℝ) : ℝ :=
  S.fastWeight * Real.exp (-(S.fastRate * t)) -
    ∑ i ∈ S.modes, S.weight i * Real.exp (-(S.rate i * t))

/-- The actual time integral of the signed kernel difference. -/
def BalancedSpectrum.primitive (S : BalancedSpectrum ι) (t : ℝ) : ℝ :=
  ∫ x in 0..t, S.difference x

/-- Center a kernel by its time average over a horizon. -/
def centered (k : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ :=
  k x - (∫ s in 0..T, k s) / T

private theorem integral_decay {r : ℝ} (hr : r ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.exp (-(r * x))) =
      (Real.exp (-(r * a)) - Real.exp (-(r * b))) / r := by
  simp only [← neg_mul]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hr), integral_exp]
  simp only [smul_eq_mul, inv_neg, div_eq_mul_inv]
  ring

private theorem integral_weighted_decay (w : ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    (∫ x in 0..t, w * Real.exp (-(r * x))) = w / r * (1 - Real.exp (-(r * t))) := by
  rw [intervalIntegral.integral_const_mul, integral_decay hr]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-- Integrating the signed difference and using the inverse-rate balance leaves a sum of
differences of endpoint exponentials. -/
theorem BalancedSpectrum.primitive_eq (S : BalancedSpectrum ι) (t : ℝ) :
    S.primitive t = ∑ i ∈ S.modes, S.weight i / S.rate i *
      (Real.exp (-(S.rate i * t)) - Real.exp (-(S.fastRate * t))) := by
  obtain ⟨j, hj, _⟩ := S.weight_pos
  have hfast := (S.rate_pos j hj).trans (S.rate_lt j hj)
  have hcont (w r : ℝ) : Continuous (fun x : ℝ => w * Real.exp (-(r * x))) := by
    fun_prop
  unfold BalancedSpectrum.primitive BalancedSpectrum.difference
  rw [intervalIntegral.integral_sub ((hcont _ _).intervalIntegrable _ _)
    ((continuous_finsetSum _ fun i _ => hcont (S.weight i) (S.rate i)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i _ =>
      (hcont (S.weight i) (S.rate i)).intervalIntegrable _ _),
    integral_weighted_decay _ hfast.ne', S.balance, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_weighted_decay _ (S.rate_pos i hi).ne']
  ring

/-- The normalized time integral is a positive mixture of integrals over the spectral
intervals between each slow rate and the fast rate. -/
theorem BalancedSpectrum.primitive_div_eq (S : BalancedSpectrum ι) {t : ℝ} (ht : t ≠ 0) :
    S.primitive t / t = ∑ i ∈ S.modes, S.weight i / S.rate i *
      (∫ r in S.rate i..S.fastRate, Real.exp (-(r * t))) := by
  rw [S.primitive_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_comm _ t, integral_decay ht]
  ring

/-- Each spectral interval contributes a strictly decreasing exponential integral.
One positive weight makes the normalized time integral strictly decreasing. -/
theorem BalancedSpectrum.strictAntiOn_primitive_div (S : BalancedSpectrum ι) :
    StrictAntiOn (fun t => S.primitive t / t) (Ioi 0) := by
  intro t ht T hT htT
  change S.primitive T / T < S.primitive t / t
  rw [S.primitive_div_eq (mem_Ioi.mp hT).ne', S.primitive_div_eq (mem_Ioi.mp ht).ne']
  have hterm (i : ι) (hi : i ∈ S.modes) :
      (∫ r in S.rate i..S.fastRate, Real.exp (-(r * T))) <
        (∫ r in S.rate i..S.fastRate, Real.exp (-(r * t))) := by
    have hpoint (r : ℝ) (hr : r ∈ Icc (S.rate i) S.fastRate) :
        Real.exp (-(r * T)) < Real.exp (-(r * t)) :=
      Real.exp_lt_exp.mpr <|
        neg_lt_neg (mul_lt_mul_of_pos_left htT ((S.rate_pos i hi).trans_le hr.1))
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (S.rate_lt i hi) (by fun_prop) (by fun_prop)
      (fun r hr => (hpoint r (Ioc_subset_Icc_self hr)).le)
      ⟨S.rate i, left_mem_Icc.mpr (S.rate_lt i hi).le,
        hpoint _ (left_mem_Icc.mpr (S.rate_lt i hi).le)⟩
  obtain ⟨j, hj, hw⟩ := S.weight_pos
  exact Finset.sum_lt_sum
    (fun i hi => mul_le_mul_of_nonneg_left (hterm i hi).le
      (div_nonneg (S.weight_nonneg i hi) (S.rate_pos i hi).le))
    ⟨j, hj, mul_lt_mul_of_pos_left (hterm j hj) (div_pos hw (S.rate_pos j hj))⟩

private theorem integral_sub_eq_primitive (S : BalancedSpectrum ι) {kp km : ℝ → ℝ}
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hp : ContinuousOn kp (Icc 0 T)) (hm : ContinuousOn km (Icc 0 T))
    (hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x) :
    (∫ x in 0..t, kp x) - (∫ x in 0..t, km x) = S.primitive t := by
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht]
    exact Icc_subset_Icc le_rfl htT
  rw [← intervalIntegral.integral_sub (hp.mono hsub).intervalIntegrable
    (hm.mono hsub).intervalIntegrable]
  exact intervalIntegral.integral_congr (fun x hx => hd x (hsub hx))

private theorem centered_prefix_eq (S : BalancedSpectrum ι) {kp km : ℝ → ℝ}
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hp : ContinuousOn kp (Icc 0 T)) (hm : ContinuousOn km (Icc 0 T))
    (hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x) :
    (∫ x in 0..t, centered kp T x - centered km T x) =
      S.primitive t - t * (S.primitive T / T) := by
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht]
    exact Icc_subset_Icc le_rfl htT
  have hkp : IntervalIntegrable kp volume 0 t := (hp.mono hsub).intervalIntegrable
  have hkm : IntervalIntegrable km volume 0 t := (hm.mono hsub).intervalIntegrable
  unfold centered
  rw [intervalIntegral.integral_congr (g := fun x => (kp x - km x) -
      (((∫ s in 0..T, kp s) - (∫ s in 0..T, km s)) / T))
      (fun _ _ => by ring),
    intervalIntegral.integral_sub (f := fun x => kp x - km x) (hkp.sub hkm)
      intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    intervalIntegral.integral_sub hkp hkm,
    integral_sub_eq_primitive S ht htT hp hm hd,
    integral_sub_eq_primitive S (ht.trans htT) le_rfl hp hm hd]

/-- Every interior centered prefix has a strict gap. Continuity on the horizon is
enough for this step, with no monotonicity assumptions on the two kernels. -/
theorem BalancedSpectrum.centered_prefix_pos (S : BalancedSpectrum ι) {kp km : ℝ → ℝ}
    {t T : ℝ} (ht : 0 < t) (htT : t < T)
    (hp : ContinuousOn kp (Icc 0 T)) (hm : ContinuousOn km (Icc 0 T))
    (hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x) :
    0 < ∫ x in 0..t, (centered kp T x - centered km T x) := by
  rw [centered_prefix_eq S ht.le htT.le hp hm hd, sub_pos, mul_comm t]
  exact (lt_div_iff₀ ht).mp (S.strictAntiOn_primitive_div ht (ht.trans htT) htT)

/-- The unit-amplitude pulse as a function of lag from the terminal time. -/
def midpointPulse (T x : ℝ) : ℝ :=
  if x ≤ T / 2 then 1 else -1

/-- An a.e. measurable input in the unit ball with zero time integral. -/
structure Admissible (T : ℝ) (u : ℝ → ℝ) : Prop where
  measurable : AEStronglyMeasurable u (volume.restrict (Ioc 0 T))
  amplitude : ∀ᵐ x ∂(volume.restrict (Ioc 0 T)), |u x| ≤ 1
  zero_integral : (∫ x in 0..T, u x) = 0

/-- The scalar terminal response, in lag coordinates. -/
def response (k : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in 0..T, k x * u x

private theorem midpointPulse_measurable (T : ℝ) : Measurable (midpointPulse T) := by
  exact measurable_const.piecewise measurableSet_Iic measurable_const

private theorem midpointPulse_amplitude (T x : ℝ) : |midpointPulse T x| = 1 := by
  unfold midpointPulse
  split <;> simp

private theorem response_midpointPulse {k : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hk : IntervalIntegrable k volume 0 T) :
    response k T (midpointPulse T) =
      2 * (∫ x in 0..T / 2, k x) - (∫ x in 0..T, k x) := by
  have hmid : 0 ≤ T / 2 := by positivity
  have hmidT : T / 2 ≤ T := by linarith
  have hpulse : IntervalIntegrable (fun x => k x * midpointPulse T x) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (hk.1.mul_bdd (midpointPulse_measurable T).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, midpointPulse_amplitude]))
  have hleft : uIcc 0 (T / 2) ⊆ uIcc 0 T := by
    rw [uIcc_of_le hmid, uIcc_of_le hT.le]
    exact Icc_subset_Icc le_rfl hmidT
  have hright : uIcc (T / 2) T ⊆ uIcc 0 T := by
    rw [uIcc_of_le hmidT, uIcc_of_le hT.le]
    exact Icc_subset_Icc hmid le_rfl
  have hfirst :
      (∫ x in 0..T / 2, k x * midpointPulse T x) = ∫ x in 0..T / 2, k x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hmid] at hx
    simp [midpointPulse, hx.2]
  have hsecond :
      (∫ x in T / 2..T, k x * midpointPulse T x) = -(∫ x in T / 2..T, k x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le hmidT
    intro x hx
    simp [midpointPulse, hx.1.not_ge]
  unfold response
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hpulse.mono_set hleft) (hpulse.mono_set hright), hfirst, hsecond]
  linarith [intervalIntegral.integral_add_adjacent_intervals
    (hk.mono_set hleft) (hk.mono_set hright)]

private theorem midpointPulse_admissible {T : ℝ} (hT : 0 < T) :
    Admissible T (midpointPulse T) where
  measurable := (midpointPulse_measurable T).aestronglyMeasurable
  amplitude := ae_of_all _ (fun x => (midpointPulse_amplitude T x).le)
  zero_integral := by
    have h := response_midpointPulse hT (k := fun _ => 1) intervalIntegrable_const
    simp only [response, one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      mul_one] at h
    linarith

private theorem response_le_midpointPulse {k u : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hk : ContinuousOn k (Icc 0 T)) (hmono : AntitoneOn k (Icc 0 T))
    (hu : Admissible T u) :
    response k T u ≤ response k T (midpointPulse T) := by
  let c := k (T / 2)
  have hmid : T / 2 ∈ Icc 0 T := ⟨by linarith, by linarith⟩
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 T) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have weight_eq {v : ℝ → ℝ} (hv : Admissible T v) :
      response k T v = ∫ x in Ioc 0 T, (k x - c) * v x := by
    have hvint : IntegrableOn v (Ioc 0 T) :=
      hconst.mono' hv.measurable (by simpa only [Real.norm_eq_abs] using hv.amplitude)
    have hkv := (hk.intervalIntegrable_of_Icc hT.le).1.mul_bdd hv.measurable
      (by simpa only [Real.norm_eq_abs] using hv.amplitude)
    have hzero : (∫ x in Ioc 0 T, v x) = 0 := by
      simpa only [intervalIntegral.integral_of_le hT.le] using hv.zero_integral
    simp only [response, intervalIntegral.integral_of_le hT.le, sub_mul]
    rw [integral_sub hkv (hvint.const_mul c), integral_const_mul, hzero, mul_zero, sub_zero]
  have hweighted {v : ℝ → ℝ} (hv : Admissible T v) :
      IntegrableOn (fun x => (k x - c) * v x) (Ioc 0 T) :=
    ((hk.sub continuousOn_const).intervalIntegrable_of_Icc hT.le).1.mul_bdd hv.measurable
      (by simpa only [Real.norm_eq_abs] using hv.amplitude)
  have hv := midpointPulse_admissible hT
  rw [weight_eq hu, weight_eq hv]
  apply integral_mono_ae (hweighted hu) (hweighted hv)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hu.amplitude] with x hx hbound
  have hx' := Ioc_subset_Icc_self hx
  rcases le_or_gt x (T / 2) with h | h
  · simpa only [midpointPulse, ite_eq_left h, mul_one] using
      mul_le_mul_of_nonneg_left (abs_le.mp hbound).2 (sub_nonneg.mpr (hmono hx' hmid h))
  · simp only [midpointPulse, ite_eq_right h.not_ge]
    exact mul_le_mul_of_nonpos_left (abs_le.mp hbound).1
      (sub_nonpos.mpr (hmono hmid hx' h.le))

/-- The same midpoint pulse maximizes both port responses over all admissible inputs,
and the difference of attained maxima is exactly the strictly positive spectral gap. -/
theorem BalancedSpectrum.midpoint_optimal_gap (S : BalancedSpectrum ι)
    {kp km : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hp : ContinuousOn kp (Icc 0 T)) (hm : ContinuousOn km (Icc 0 T))
    (hmp : AntitoneOn kp (Icc 0 T)) (hmm : AntitoneOn km (Icc 0 T))
    (hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x) :
    Admissible T (midpointPulse T) ∧
    (∀ u, Admissible T u → response kp T u ≤ response kp T (midpointPulse T) ∧
      response km T u ≤ response km T (midpointPulse T)) ∧
    response kp T (midpointPulse T) - response km T (midpointPulse T) =
      2 * S.primitive (T / 2) - S.primitive T ∧
    0 < 2 * S.primitive (T / 2) - S.primitive T := by
  have hmid : 0 < T / 2 := by positivity
  have hmidT : T / 2 < T := by linarith
  refine ⟨midpointPulse_admissible hT, fun u hu =>
    ⟨response_le_midpointPulse hT hp hmp hu, response_le_midpointPulse hT hm hmm hu⟩, ?_, ?_⟩
  · rw [response_midpointPulse hT (hp.intervalIntegrable_of_Icc hT.le),
      response_midpointPulse hT (hm.intervalIntegrable_of_Icc hT.le)]
    linarith [integral_sub_eq_primitive S hmid.le hmidT.le hp hm hd,
      integral_sub_eq_primitive S hT.le le_rfl hp hm hd]
  · have h := S.centered_prefix_pos hmid hmidT hp hm hd
    rw [centered_prefix_eq S hmid.le hmidT.le hp hm hd] at h
    have hcancel : T / 2 * (S.primitive T / T) = S.primitive T / 2 := by
      field_simp
    rw [hcancel] at h
    linarith

/-- The integrated stop loss over the horizon. Divide by the horizon for the mean stop loss. -/
def stopLoss (k : ℝ → ℝ) (T z : ℝ) : ℝ :=
  ∫ x in 0..T, max (k x - z) 0

private theorem continuousOn_centered {k : ℝ → ℝ} {T : ℝ}
    (hk : ContinuousOn k (Icc 0 T)) : ContinuousOn (centered k T) (Icc 0 T) :=
  hk.sub continuousOn_const

private theorem integral_centered {k : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hk : ContinuousOn k (Icc 0 T)) :
    (∫ x in 0..T, centered k T x) = 0 := by
  unfold centered
  rw [intervalIntegral.integral_sub (hk.intervalIntegrable_of_Icc hT.le)
    intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    sub_eq_zero, mul_div_cancel₀ _ hT.ne']

private theorem prefix_sub_le_stopLoss {f : ℝ → ℝ} {T r z : ℝ}
    (hr : 0 ≤ r) (hrT : r ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    (∫ x in 0..r, f x - z) ≤ stopLoss f T z := by
  have hhinge : ContinuousOn (fun x => max (f x - z) 0) (Icc 0 T) :=
    (hf.sub continuousOn_const).sup continuousOn_const
  have hleft : Icc 0 r ⊆ Icc 0 T := Icc_subset_Icc le_rfl hrT
  have hright : Icc r T ⊆ Icc 0 T := Icc_subset_Icc hr le_rfl
  have hprefix := intervalIntegral.integral_mono_on (μ := volume) hr
    ((hf.sub continuousOn_const).mono hleft |>.intervalIntegrable_of_Icc hr)
    ((hhinge.mono hleft).intervalIntegrable_of_Icc hr)
    (fun x _ => le_max_left (f x - z) 0)
  unfold stopLoss
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hhinge.mono hleft).intervalIntegrable_of_Icc hr)
    ((hhinge.mono hright).intervalIntegrable_of_Icc hrT)]
  exact hprefix.trans (le_add_of_nonneg_right
    (intervalIntegral.integral_nonneg hrT fun _ _ => le_max_right _ _))

/-- Strict stop-loss comparison for strikes strictly between the centered plus values at `T`
and `0`. Both kernels are continuous on the horizon, and the minus kernel is antitone. -/
theorem BalancedSpectrum.centered_stopLoss_lt (S : BalancedSpectrum ι)
    {kp km : ℝ → ℝ} {T z : ℝ} (hT : 0 < T)
    (hp : ContinuousOn kp (Icc 0 T)) (hm : ContinuousOn km (Icc 0 T))
    (hmm : AntitoneOn km (Icc 0 T))
    (hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x)
    (hlo : centered kp T T < z) (hhi : z < centered kp T 0) :
    stopLoss (centered km T) T z < stopLoss (centered kp T) T z := by
  let f := centered kp T
  let g := centered km T
  have hf := continuousOn_centered hp
  have hg := continuousOn_centered hm
  have hgmono : AntitoneOn g (Icc 0 T) := fun _ ha _ hb hab =>
    sub_le_sub_right (hmm ha hb hab) _
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have htop : T ∈ Icc 0 T := right_mem_Icc.mpr hT.le
  have hfh : ContinuousOn (fun x => max (f x - z) 0) (Icc 0 T) :=
    (hf.sub continuousOn_const).sup continuousOn_const
  change stopLoss g T z < stopLoss f T z
  by_cases hzlo : z ≤ g T
  · have hg_eq : stopLoss g T z = ∫ x in 0..T, g x - z := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hT.le] at hx
      exact max_eq_left (sub_nonneg.mpr (hzlo.trans (hgmono hx htop hx.2)))
    have hmean : ∀ k : ℝ → ℝ, ContinuousOn k (Icc 0 T) →
        (∫ x in 0..T, centered k T x - z) = -(T * z) := by
      intro k hk
      rw [intervalIntegral.integral_sub
        ((continuousOn_centered hk).intervalIntegrable_of_Icc hT.le) intervalIntegrable_const,
        integral_centered hT hk, intervalIntegral.integral_const, sub_zero, smul_eq_mul, zero_sub]
    rw [hg_eq, hmean km hm, ← hmean kp hp]
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
      (hf.sub continuousOn_const) hfh (fun x _ => le_max_left (f x - z) 0)
      ⟨T, htop, (sub_neg.mpr hlo).trans_le (le_max_right _ _)⟩
  by_cases hzhi : g 0 ≤ z
  · have hg_eq : stopLoss g T z = 0 := by
      calc
        _ = ∫ _ in 0..T, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hT.le] at hx
          exact max_eq_right (sub_nonpos.mpr ((hgmono h0 hx hx.1).trans hzhi))
        _ = 0 := intervalIntegral.integral_zero
    have hpositive : (∫ _ in 0..T, (0 : ℝ)) < stopLoss f T z :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
        continuousOn_const hfh (fun x _ => le_max_right (f x - z) 0)
        ⟨0, h0, (sub_pos.mpr hhi).trans_le (le_max_left _ _)⟩
    rw [hg_eq]
    simpa only [intervalIntegral.integral_zero] using hpositive
  obtain ⟨r, hr, hrz⟩ :=
    intermediate_value_Icc' hT.le hg ⟨lt_of_not_ge hzlo |>.le, lt_of_not_ge hzhi |>.le⟩
  change g r = z at hrz
  have hr0 : 0 < r := hr.1.lt_of_ne (fun h => hzhi (by rw [h, hrz]))
  have hrT : r < T := hr.2.lt_of_ne (fun h => hzlo (by rw [← h, hrz]))
  have hleft : Icc 0 r ⊆ Icc 0 T := Icc_subset_Icc le_rfl hr.2
  have hright : Icc r T ⊆ Icc 0 T := Icc_subset_Icc hr.1 le_rfl
  have hgh : ContinuousOn (fun x => max (g x - z) 0) (Icc 0 T) :=
    (hg.sub continuousOn_const).sup continuousOn_const
  have hfirst : (∫ x in 0..r, max (g x - z) 0) = ∫ x in 0..r, g x - z := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr.1] at hx
    exact max_eq_left (by rw [← hrz]; exact sub_nonneg.mpr (hgmono (hleft hx) hr hx.2))
  have hsecond : (∫ x in r..T, max (g x - z) 0) = 0 := by
    calc
      _ = ∫ _ in r..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hr.2] at hx
        exact max_eq_right (by rw [← hrz]; exact sub_nonpos.mpr (hgmono hr (hright hx) hx.1))
      _ = 0 := intervalIntegral.integral_zero
  have hg_eq : stopLoss g T z = ∫ x in 0..r, g x - z := by
    unfold stopLoss
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hgh.mono hleft).intervalIntegrable_of_Icc hr.1)
      ((hgh.mono hright).intervalIntegrable_of_Icc hr.2), hfirst, hsecond, add_zero]
  rw [hg_eq]
  refine lt_of_lt_of_le ?_ (prefix_sub_le_stopLoss hr.1 hr.2 hf)
  have hpre := S.centered_prefix_pos hr0 hrT hp hm hd
  change 0 < ∫ x in 0..r, f x - g x at hpre
  rw [intervalIntegral.integral_sub ((hf.mono hleft).intervalIntegrable_of_Icc hr.1)
    ((hg.mono hleft).intervalIntegrable_of_Icc hr.1)] at hpre
  rw [intervalIntegral.integral_sub ((hg.mono hleft).intervalIntegrable_of_Icc hr.1)
    intervalIntegrable_const, intervalIntegral.integral_sub
    ((hf.mono hleft).intervalIntegrable_of_Icc hr.1) intervalIntegrable_const]
  linarith

end NeumannCenteredOrder
