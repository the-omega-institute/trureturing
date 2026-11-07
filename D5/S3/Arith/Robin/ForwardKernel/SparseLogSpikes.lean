/- GID: D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/SparseLogSpikes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse logarithmic spikes are continuous, isolated and geometrically controlled. -/

import D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpnessDefs
import D5.S3.Arith.Robin.ForwardKernel.ClippedLogEnergy
import D5.S3.Arith.Robin.ForwardKernel.CuspAverages
import D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingBounds

/-! Regularity, localization and amplitude bounds for sparse logarithmic perturbations. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs
open scoped Topology BigOperators

noncomputable section

/-- An admissible spike is supported between nine tenths and eleven tenths of its center. -/
theorem spike_support_tenth {a b : ℝ} {n₀ n : ℕ}
    (hs : AdmissibleStart b n₀) (hn : n₀ ≤ n) :
    Function.support (spike a b n) ⊆ Icc (9 / 10 * center n) (11 / 10 * center n) := by
  intro x hx
  have hx' := spike_support_subset a b n hx
  have hr := hs.2 n hn
  constructor <;> linarith [hx'.1, hx'.2]

private lemma spike_continuous (a b : ℝ) (n : ℕ) : Continuous (spike a b n) := by
  have hh := Real.rpow_pos_of_pos (center_pos n) a
  have hk := Real.rpow_pos_of_pos (center_pos n) b
  by_cases hhk : center n ^ a < center n ^ b
  · exact continuous_const.mul ((clippedLog_continuous hh hhk).comp
      (continuous_id.sub continuous_const))
  · have hz : spike a b n = fun _ => 0 := by
      funext x
      have hm : center n ^ b ≤ max (center n ^ a) |x - center n| :=
        (le_of_not_gt hhk).trans (le_max_left _ _)
      simp only [spike, clippedLog, min_eq_left hm, div_self hk.ne', Real.log_one, mul_zero]
    rw [hz]
    exact continuous_const

/-- The locally finite sum defining the perturbation is continuous. -/
theorem perturbation_continuous {a b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) : Continuous (perturbation a b n₀) := by
  have he : perturbation a b n₀ = fun x => ∑ᶠ j, spike a b (n₀ + j) x := by
    funext x
    exact tsum_eq_finsum (perturbation_finite_support hs x)
  rw [he]
  exact continuous_finsum (fun j => spike_continuous a b (n₀ + j)) (spike_locallyFinite hs)

/-- The sparse perturbation is Borel measurable and bounded on every compact interval. -/
theorem perturbation_locallyBoundedMeasurable {a b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) : LocallyBoundedMeasurable (perturbation a b n₀) := by
  exact DyadicSmoothingBounds.continuous_lbm (perturbation_continuous hs)

private lemma center_succ (n : ℕ) : center (n + 1) = 10 * center n := by
  simp only [center, pow_succ]
  ring

private lemma other_spike_zero {a b : ℝ} {n₀ n j : ℕ}
    (hs : AdmissibleStart b n₀) (_hn : n₀ ≤ n) (hj : n₀ ≤ j) (hjn : j ≠ n)
    {x : ℝ} (hx : x ∈ Icc (center n) (3 * center n)) : spike a b j x = 0 := by
  by_contra hz
  have hsupport := spike_support_tenth hs hj hz
  rcases lt_or_gt_of_ne hjn with hlt | hgt
  · have hc := center_strictMono.monotone (show j + 1 ≤ n by omega)
    rw [center_succ] at hc
    linarith [center_pos j, hx.1, hsupport.2]
  · have hc := center_strictMono.monotone (show n + 1 ≤ j by omega)
    rw [center_succ] at hc
    linarith [center_pos n, hx.2, hsupport.1]

/-- Throughout three center lengths only the spike at that center can contribute. -/
theorem perturbation_eq_spike_on {a b : ℝ} {n₀ n : ℕ}
    (hs : AdmissibleStart b n₀) (hn : n₀ ≤ n) {x : ℝ}
    (hx : x ∈ Icc (center n) (3 * center n)) :
    perturbation a b n₀ x = spike a b n x := by
  unfold perturbation
  rw [tsum_eq_single (n - n₀)]
  · congr 2
    omega
  · intro j hj
    exact other_spike_zero hs hn (Nat.le_add_right _ _) (by omega) hx

/-- Isolation holds on the entire forward range used by both moving lengths. -/
theorem perturbation_forward_eq_spike {a b : ℝ} {n₀ n : ℕ}
    (hs : AdmissibleStart b n₀) (hn : n₀ ≤ n) {x u : ℝ}
    (hx : x ∈ Icc (center n) (2 * center n))
    (hu : u ∈ Icc (0 : ℝ) (2 * center n ^ b)) :
    perturbation a b n₀ (x + u) = spike a b n (x + u) := by
  apply perturbation_eq_spike_on hs hn
  have hr := hs.2 n hn
  constructor <;> linarith [hx.1, hx.2, hu.1, hu.2, center_pos n]

private lemma log_center_succ (n : ℕ) :
    Real.log (center (n + 1)) = Real.log (center n) + Real.log 10 := by
  rw [center_succ, Real.log_mul (by norm_num) (center_pos n).ne']
  ring

/-- Successive amplitudes have limiting ratio the square root of ten. -/
theorem amplitude_ratio_tendsto :
    Tendsto (fun n : ℕ => amplitude (n + 1) / amplitude n)
      atTop (𝓝 (Real.sqrt 10)) := by
  let t : ℕ → ℝ := fun n => Real.log (center n)
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp center_tendsto
  have htc : Tendsto (fun n => t n + Real.log 10) atTop atTop := ht.atTop_add tendsto_const_nhds
  have hlog := Real.tendsto_log_atTop.comp htc
  have hd := (Real.tendsto_log_comp_add_sub_log (Real.log 10)).comp ht
  have hz := hd.div_atTop hlog
  have hr : Tendsto (fun n => Real.log (t n) / Real.log (t n + Real.log 10))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    dsimp only [Function.comp_def] at *
    field_simp
    ring
  have hs : Tendsto (fun n => (t n + Real.log 10) / t n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := Real.log 10)).div_atTop ht)
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    field_simp
  have hprod := ((tendsto_const_nhds (x := (10 : ℝ))).mul hs).mul hr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hprod
  simp only [mul_one] at hsqrt
  apply hsqrt.congr'
  filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ)),
    htc.eventually (eventually_gt_atTop (1 : ℝ))] with n hn hn'
  change Real.sqrt (10 * ((t n + Real.log 10) / t n) *
    (Real.log (t n) / Real.log (t n + Real.log 10))) = _
  have htpos : 0 < t n := by linarith
  have htpos' : 0 < t n + Real.log 10 := by linarith
  have hlpos := Real.log_pos hn
  have hlpos' := Real.log_pos hn'
  unfold amplitude
  rw [log_center_succ]
  change Real.sqrt (10 * ((t n + Real.log 10) / t n) *
    (Real.log (t n) / Real.log (t n + Real.log 10))) =
    Real.sqrt (center (n + 1) * (t n + Real.log 10) / Real.log (t n + Real.log 10)) /
      Real.sqrt (center n * t n / Real.log (t n))
  rw [← Real.sqrt_div (le_of_lt (div_pos
    (mul_pos (center_pos (n + 1)) htpos') hlpos'))]
  congr 1
  rw [center_succ]
  change _ = 10 * center n * (t n + Real.log 10) /
    Real.log (t n + Real.log 10) / (center n * t n / Real.log (t n))
  field_simp [(center_pos n).ne', htpos.ne', hlpos.ne', hlpos'.ne']

/-- Beyond a fixed index the amplitudes at least double at every step. -/
private theorem amplitude_eventually_doubling :
    ∀ᶠ n : ℕ in atTop, 2 * amplitude n ≤ amplitude (n + 1) := by
  have htwo : (2 : ℝ) < Real.sqrt 10 := by
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  filter_upwards [amplitude_ratio_tendsto.eventually (lt_mem_nhds htwo)] with n hn
  by_cases hz : amplitude n = 0
  · simp only [hz, mul_zero]
    exact Real.sqrt_nonneg _
  · exact ((lt_div_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz))).1 hn).le

/-- A finite sum of amplitudes is bounded by a fixed multiple of its final term. -/
theorem amplitude_partial_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (∑ n ∈ Finset.range (m + 1), amplitude n) ≤ C * amplitude m := by
  have ht := Real.tendsto_log_atTop.comp center_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (amplitude_eventually_doubling.and (ht.eventually (eventually_gt_atTop (1 : ℝ))))
  have hlogN : 1 < Real.log (center N) := (hN N le_rfl).2
  have hA : 0 < amplitude N := by
    apply Real.sqrt_pos.2
    exact div_pos (mul_pos (center_pos N) (by linarith [hlogN]))
      (Real.log_pos (hN N le_rfl).2)
  let C := max 2 ((∑ n ∈ Finset.range (N + 1), amplitude n) / amplitude N)
  have hC : 2 ≤ C := le_max_left _ _
  have hbase : (∑ n ∈ Finset.range (N + 1), amplitude n) ≤ C * amplitude N := by
    exact (div_le_iff₀ hA).1 (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop N] with m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hd := (hN (N + k) (by omega)).1
    have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ C by linarith)
    have hc := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg
      (center (N + k + 1) * Real.log (center (N + k + 1)) /
        Real.log (Real.log (center (N + k + 1)))))
    rw [show N + (k + 1) + 1 = (N + k + 1) + 1 by omega, Finset.sum_range_succ]
    change (∑ n ∈ Finset.range (N + k + 1), amplitude n) + amplitude (N + k + 1) ≤
      C * amplitude (N + k + 1)
    change 2 * amplitude (N + k + 1) ≤ C * amplitude (N + k + 1) at hc
    nlinarith

private lemma amplitude_log_bound {n : ℕ} {x : ℝ}
    (hX : Real.exp (Real.exp 2) ≤ center n) (hx : 0 < x)
    (hXx : center n ≤ 2 * x) (hxX : x ≤ 2 * center n)
    (hlx : 2 ≤ Real.log x) :
    amplitude n * Real.log (center n) ≤ 8 * spikePointScale x := by
  have hXpos := center_pos n
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLX : Real.exp 2 ≤ Real.log (center n) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hLX1 : 1 ≤ Real.log (center n) := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hllX : 2 ≤ Real.log (Real.log (center n)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLX
  have hLXpos : 0 < Real.log (center n) := by linarith
  have hlxpos : 0 < Real.log x := by linarith
  have hllxpos : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hllXpos : 0 < Real.log (Real.log (center n)) := by linarith
  have hlogXx : Real.log (center n) ≤ 2 * Real.log x := by
    have h := Real.log_le_log hXpos hXx
    rw [Real.log_mul (by norm_num) hx.ne'] at h
    linarith
  have hlogxX : Real.log x ≤ 2 * Real.log (center n) := by
    have h := Real.log_le_log hx hxX
    rw [Real.log_mul (by norm_num) hXpos.ne'] at h
    linarith
  have hloglog : Real.log (Real.log x) ≤ 2 * Real.log (Real.log (center n)) := by
    have h := Real.log_le_log hlxpos hlogxX
    rw [Real.log_mul (by norm_num) hLXpos.ne'] at h
    linarith
  have hrad : center n * Real.log (center n) / Real.log (Real.log (center n)) ≤
      8 * (x * Real.log x / Real.log (Real.log x)) := by
    calc
      _ ≤ (2 * x) * (2 * Real.log x) / (Real.log (Real.log x) / 2) := by
        gcongr
        linarith
      _ = _ := by ring
  have hq : 0 ≤ x * Real.log x / Real.log (Real.log x) := by positivity
  have hA : amplitude n ≤ 4 * Real.sqrt (x * Real.log x / Real.log (Real.log x)) := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hq]
    linarith
  have he : Real.sqrt (x * Real.log x / Real.log (Real.log x)) * Real.log x =
      spikePointScale x := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hx.le]
    unfold spikePointScale
    have hp : (Real.log x) ^ (3 / 2 : ℝ) = Real.sqrt (Real.log x) * Real.log x := by
      calc
        _ = (Real.log x) ^ (1 / 2 : ℝ) * (Real.log x) ^ (1 : ℝ) := by
          rw [← Real.rpow_add hlxpos]
          norm_num
        _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
    rw [hp]
    ring
  calc
    _ ≤ (4 * Real.sqrt (x * Real.log x / Real.log (Real.log x))) * (2 * Real.log x) := by
      gcongr
    _ = 8 * spikePointScale x := by rw [← he]; ring

private lemma spike_abs_bound {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |spike a b n x| ≤ (b - a) * (amplitude n * Real.log (center n)) := by
  have hc : 1 < center n := by
    simpa only [center, pow_zero] using center_strictMono (show 0 < n by omega)
  have hh := Real.rpow_pos_of_pos (center_pos n) a
  have hk := Real.rpow_pos_of_pos (center_pos n) b
  have hhk := Real.rpow_lt_rpow_of_exponent_lt hc hab
  have h := clip_range hh hhk (x - center n)
  have he : Real.log (center n ^ a / center n ^ b) =
      -(b - a) * Real.log (center n) := by
    rw [Real.log_div hh.ne' hk.ne', Real.log_rpow (center_pos n),
      Real.log_rpow (center_pos n)]
    ring
  rw [he] at h
  have hb : |clippedLog (center n ^ a) (center n ^ b) (x - center n)| ≤
      (b - a) * Real.log (center n) := by
    rw [abs_of_nonpos h.2]
    linarith [h.1]
  rw [spike, abs_mul, abs_of_nonneg (show 0 ≤ amplitude n from Real.sqrt_nonneg _)]
  calc
    _ ≤ amplitude n * ((b - a) * Real.log (center n)) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The perturbation obeys the logarithmic pointwise growth bound. -/
theorem perturbation_pointwise_bound {a b : ℝ} {n₀ : ℕ}
    (hab : a < b) (hs : AdmissibleStart b n₀) :
    Asymptotics.IsBigO atTop (perturbation a b n₀) spikePointScale := by
  apply Asymptotics.IsBigO.of_bound (8 * (b - a))
  filter_upwards [eventually_ge_atTop (2 * Real.exp (Real.exp 2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x hx hlx
  have hxpos : 0 < x := by linarith [Real.exp_pos (Real.exp 2)]
  have hscale : 0 ≤ spikePointScale x := by
    unfold spikePointScale
    positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hscale]
  by_cases hall : ∀ j : ℕ, spike a b (n₀ + j) x = 0
  · simp only [perturbation, hall, tsum_zero, abs_zero]
    positivity
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hn : n₀ ≤ n₀ + j := Nat.le_add_right _ _
    have hsup := spike_support_tenth hs hn hj
    have hXx : center (n₀ + j) ≤ 2 * x := by linarith [hsup.1]
    have hxX : x ≤ 2 * center (n₀ + j) := by linarith [hsup.2, center_pos (n₀ + j)]
    have hX : Real.exp (Real.exp 2) ≤ center (n₀ + j) := by
      linarith [hsup.2, Real.exp_pos (Real.exp 2)]
    have heq : perturbation a b n₀ x = spike a b (n₀ + j) x := by
      unfold perturbation
      apply tsum_eq_single j
      intro i hij
      by_contra hi
      obtain ⟨U, hU, huniq⟩ := perturbation_locally_single_spike hs x
      have hxu := mem_of_mem_nhds hU
      exact hij (huniq i j x hxu x hxu hi hj)
    rw [heq]
    calc
      _ ≤ (b - a) * (amplitude (n₀ + j) * Real.log (center (n₀ + j))) :=
        spike_abs_bound hab (hs.1.trans hn) x
      _ ≤ (b - a) * (8 * spikePointScale x) :=
        mul_le_mul_of_nonneg_left (amplitude_log_bound hX hxpos hXx hxX hlx) (sub_nonneg.mpr hab.le)
      _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
