/- GID: D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse logarithmic spikes have negligible variance on exponent bands. -/

import D5.S3.Arith.Robin.ForwardKernel.SparseLogSpikes
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

/-! Uniform cumulative variance bounds for sparse logarithmic perturbations. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs CrossExponentDefs
open scoped Topology BigOperators

noncomputable section

private lemma spike_energy {a b C u : ℝ} {n : ℕ}
    (hab : a < b) (hn : 1 ≤ n) (hu : 0 < u)
    (hC : ∀ h k u : ℝ, 0 < h → h < k → 0 < u →
      Integrable (fun y => (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ∧
      (∫ y : ℝ, (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ≤ C * u) :
    Integrable (fun x => increment (spike a b n) u x ^ 2) ∧
      (∫ x : ℝ, increment (spike a b n) u x ^ 2) ≤ amplitude n ^ 2 * (C * u) := by
  have hc : 1 < center n := by
    simpa only [center, pow_zero] using center_strictMono (show 0 < n by omega)
  obtain ⟨hi, he⟩ := hC (center n ^ a) (center n ^ b) u
    (Real.rpow_pos_of_pos (center_pos n) a)
    (Real.rpow_lt_rpow_of_exponent_lt hc hab) hu
  have heq (x : ℝ) : increment (spike a b n) u x ^ 2 = amplitude n ^ 2 *
      (clippedLog (center n ^ a) (center n ^ b) ((x - center n) + u) -
        clippedLog (center n ^ a) (center n ^ b) (x - center n)) ^ 2 := by
    simp only [increment, spike, show x + u - center n = (x - center n) + u by ring]
    ring
  simp_rw [heq]
  refine ⟨(hi.comp_sub_right (center n)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : ℝ => (clippedLog (center n ^ a) (center n ^ b) (y + u) -
      clippedLog (center n ^ a) (center n ^ b) y) ^ 2) (center n)]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

private lemma perturbation_eq_finite {a b Y : ℝ} {n₀ m : ℕ}
    (hs : AdmissibleStart b n₀) (hm : 3 * Y < center (m + 1))
    {x : ℝ} (hx : x ≤ 2 * Y) :
    perturbation a b n₀ x =
      ∑ j ∈ Finset.range (m + 1 - n₀), spike a b (n₀ + j) x := by
  apply tsum_eq_sum
  intro j hj
  have hjm : m + 1 - n₀ ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  by_contra hz
  have ht := spike_support_tenth hs (Nat.le_add_right n₀ j) hz
  have hc := center_strictMono.monotone (show m + 1 ≤ n₀ + j by omega)
  linarith [center_pos (n₀ + j), ht.1]

private lemma finite_variance_bound {a b C Y u : ℝ} {n₀ m : ℕ}
    (hab : a < b) (hs : AdmissibleStart b n₀) (hY : 1 ≤ Y)
    (hu : 0 < u) (huY : u ≤ Y) (hm : 3 * Y < center (m + 1))
    (hC : 0 < C)
    (henergy : ∀ h k u : ℝ, 0 < h → h < k → 0 < u →
      Integrable (fun y => (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ∧
      (∫ y : ℝ, (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ≤ C * u) :
    cumulativeVariance (perturbation a b n₀) Y u ≤
      C * u * (∑ j ∈ Finset.range (m + 1 - n₀), amplitude (n₀ + j)) ^ 2 := by
  let μ := volume.restrict (Ioc (1 : ℝ) Y)
  let f := fun j x => increment (spike a b (n₀ + j)) u x
  have hi (j : ℕ) := spike_energy hab (hs.1.trans (Nat.le_add_right n₀ j)) hu henergy
  have hf (j : ℕ) : MemLp (f j) 2 μ := by
    apply (memLp_two_iff_integrable_sq ?_).mpr (hi j).1.restrict
    have hm : Measurable (f j) := by
      dsimp [f, increment, spike, clippedLog]
      fun_prop
    exact hm.aestronglyMeasurable
  have hnorm (j : ℕ) : lpNorm (f j) 2 μ ≤
      Real.sqrt (C * u) * amplitude (n₀ + j) := by
    rw [VarianceTransfer.lpNorm_two_eq_intervalL2 hY (hf j).aestronglyMeasurable]
    unfold intervalL2
    apply Real.sqrt_le_iff.mpr
    have hA : 0 ≤ amplitude (n₀ + j) := Real.sqrt_nonneg _
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hA, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ C * u)]
    rw [intervalIntegral.integral_of_le hY]
    exact (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => sq_nonneg _)) (hi j).1).trans
      ((hi j).2.trans_eq (by ring))
  have hsum := lpNorm_sum_le (s := Finset.range (m + 1 - n₀))
    (fun j _ => hf j) (by norm_num : (1 : ENNReal) ≤ 2)
  have hmem := memLp_finsetSum' (Finset.range (m + 1 - n₀)) (fun j _ => hf j)
  rw [VarianceTransfer.lpNorm_two_eq_intervalL2 hY hmem.aestronglyMeasurable] at hsum
  have hbound := hsum.trans (Finset.sum_le_sum (fun j _ => hnorm j))
  rw [← Finset.mul_sum] at hbound
  have heq : cumulativeVariance (perturbation a b n₀) Y u =
      ∫ x in (1 : ℝ)..Y, (∑ j ∈ Finset.range (m + 1 - n₀), f j x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hY] at hx
    simp only [increment, perturbation_eq_finite hs hm (show x ≤ 2 * Y by linarith [hx.2]),
      perturbation_eq_finite hs hm (show x + u ≤ 2 * Y by linarith [hx.2]),
      ← Finset.sum_sub_distrib, f]
  rw [heq]
  have hnonneg : 0 ≤ ∫ x in (1 : ℝ)..Y,
      (∑ j ∈ Finset.range (m + 1 - n₀), f j x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hY (fun _ => sq_nonneg _)
  have hmass : 0 ≤ ∑ j ∈ Finset.range (m + 1 - n₀), amplitude (n₀ + j) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hp := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hmass)).mpr hbound
  simpa only [intervalL2, Finset.sum_apply, mul_pow, Real.sq_sqrt hnonneg,
    Real.sq_sqrt (show 0 ≤ C * u by positivity), mul_assoc] using hp

private lemma amplitude_sq_comparison {m : ℕ} {Y : ℝ}
    (hY : 0 < Y) (hXY : center m ≤ 3 * Y) (hYX : Y ≤ 4 * center m)
    (hlX : 3 ≤ Real.log (center m)) (hllX : 3 ≤ Real.log (Real.log (center m)))
    (hlY : 3 ≤ Real.log Y) :
    amplitude m ^ 2 ≤ 12 * (Y * Real.log Y / Real.log (Real.log Y)) := by
  have hlXp : 0 < Real.log (center m) := by linarith
  have hllXp : 0 < Real.log (Real.log (center m)) := by linarith
  have hlYp : 0 < Real.log Y := by linarith
  have hllYp : 0 < Real.log (Real.log Y) := Real.log_pos (by linarith)
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogXY : Real.log (center m) ≤ 2 * Real.log Y := by
    have ht := Real.log_le_log (center_pos m) hXY
    rw [Real.log_mul (by norm_num) hY.ne'] at ht
    linarith
  have hlogYX : Real.log Y ≤ 2 * Real.log (center m) := by
    have ht := Real.log_le_log hY hYX
    rw [Real.log_mul (by norm_num) (center_pos m).ne'] at ht
    linarith
  have hllYX : Real.log (Real.log Y) ≤ 2 * Real.log (Real.log (center m)) := by
    have ht := Real.log_le_log hlYp hlogYX
    rw [Real.log_mul (by norm_num) hlXp.ne'] at ht
    linarith
  rw [amplitude, Real.sq_sqrt (div_nonneg
    (mul_nonneg (center_pos m).le hlXp.le) hllXp.le)]
  calc
    _ ≤ (3 * Y) * (2 * Real.log Y) / (Real.log (Real.log Y) / 2) := by
      gcongr
      linarith
    _ = _ := by ring

/-- Uniform short-step variance bound, used by CommonBandSharpness. -/
theorem perturbation_variance_bound
    {a b β : ℝ} {n₀ : ℕ}
    (_ha : 0 < a) (hab : a < b) (hβ : β < 1)
    (hs : AdmissibleStart b n₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℝ in atTop, ∀ u : ℝ,
      0 < u → u ≤ Y ^ β →
        cumulativeVariance (perturbation a b n₀) Y u ≤
          C * Y * u * Real.log Y / Real.log (Real.log Y) := by
  obtain ⟨C, hC, henergy⟩ := clippedLog_translation_energy
  obtain ⟨D, hD, hsum⟩ := amplitude_partial_sum_bound
  have ht := Real.tendsto_log_atTop.comp center_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hsum.and ((ht.eventually (eventually_ge_atTop (3 : ℝ))).and
      ((Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop (3 : ℝ)))))
  refine ⟨12 * C * D ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (center (max N n₀)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3 : ℝ))] with Y hY hYN hlY
  intro u hu huβ
  have hYp : 0 < Y := by linarith
  obtain ⟨m, hm, hm'⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 3 * Y by linarith) (by norm_num : (1 : ℝ) < 10)
  change center m ≤ 3 * Y at hm
  change 3 * Y < center (m + 1) at hm'
  have hYX : Y ≤ 4 * center m := by
    simp only [center, pow_succ] at hm' ⊢
    linarith
  have hNm : max N n₀ ≤ m := by
    by_contra! hh
    have ht' := center_strictMono.monotone hh
    linarith
  have hmN : N ≤ m := (le_max_left _ _).trans hNm
  have hmn₀ : n₀ ≤ m + 1 := (le_max_right _ _).trans hNm |>.trans (Nat.le_succ m)
  have hmass : (∑ j ∈ Finset.range (m + 1 - n₀), amplitude (n₀ + j)) ≤
      D * amplitude m := by
    have he := Finset.sum_range_add amplitude n₀ (m + 1 - n₀)
    rw [Nat.add_sub_of_le hmn₀] at he
    have hn : 0 ≤ ∑ j ∈ Finset.range n₀, amplitude j :=
      Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
    have htotal := (hN m hmN).1
    linarith
  have hv := finite_variance_bound hab hs hY hu
    (huβ.trans (Real.rpow_le_self_of_one_le hY hβ.le)) hm' hC henergy
  have hsq := (sq_le_sq₀
    (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    (mul_nonneg hD.le (Real.sqrt_nonneg _))).mpr hmass
  have ha := amplitude_sq_comparison hYp hm hYX (hN m hmN).2.1 (hN m hmN).2.2 hlY
  calc
    _ ≤ C * u * (D * amplitude m) ^ 2 :=
      hv.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = C * u * D ^ 2 * amplitude m ^ 2 := by ring
    _ ≤ C * u * D ^ 2 * (12 * (Y * Real.log Y / Real.log (Real.log Y))) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by ring

/-- The variance is negligible uniformly on a common exponent band; used by CommonBandSharpness. -/
theorem perturbation_band_negligible
    {α a b β : ℝ} {n₀ : ℕ}
    (hBa : ValidBand α a β) (hab : a < b) (_hbβ : b < β)
    (hs : AdmissibleStart b n₀) :
    CumulativeVarianceBandNegligibleFor (perturbation a b n₀) α β := by
  have hβ : β < 1 := hBa.2.2.2
  obtain ⟨C, hC, hV⟩ := perturbation_variance_bound
    (hBa.1.trans hBa.2.1) hab hβ hs
  intro ε hε
  filter_upwards [hV, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (C / (ε * (1 - β))))] with Y hV hY hlY hllY
  intro u huα huβ
  have hYp : 0 < Y := by linarith
  have hup : 0 < u := (Real.rpow_pos_of_pos hYp α).trans_le huα
  have hllp : 0 < Real.log (Real.log Y) := Real.log_pos hlY
  have hlog : (1 - β) * Real.log Y ≤ Real.log (Y / u) := by
    have ht := Real.log_le_log hup huβ
    rw [Real.log_rpow hYp] at ht
    rw [Real.log_div hYp.ne' hup.ne']
    linarith
  have hlogp : 0 < Real.log (Y / u) :=
    (mul_pos (sub_pos.mpr hβ) (by linarith)).trans_le hlog
  have hM : 0 < Y * u * Real.log (Y / u) := by positivity
  have hVp : 0 ≤ cumulativeVariance (perturbation a b n₀) Y u :=
    intervalIntegral.integral_nonneg_of_forall hY (fun _ => sq_nonneg _)
  rw [abs_of_nonneg (div_nonneg hVp hM.le)]
  apply (div_le_iff₀ hM).mpr
  have hsmall : C / Real.log (Real.log Y) ≤ ε * (1 - β) := by
    apply (div_le_iff₀ hllp).mpr
    have ht := (div_le_iff₀ (mul_pos hε (sub_pos.mpr hβ))).mp hllY
    simpa only [Function.comp_apply, mul_comm] using ht
  calc
    _ ≤ C * Y * u * Real.log Y / Real.log (Real.log Y) := hV u hup huβ
    _ = (C / Real.log (Real.log Y)) * (Y * u * Real.log Y) := by ring
    _ ≤ (ε * (1 - β)) * (Y * u * Real.log Y) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = ε * (Y * u) * ((1 - β) * Real.log Y) := by ring
    _ ≤ ε * (Y * u) * Real.log (Y / u) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
