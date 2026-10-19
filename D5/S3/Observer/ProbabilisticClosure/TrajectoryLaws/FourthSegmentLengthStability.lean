/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLengthStability
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLengthStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original phase-p length continuity and deterministic depth separation. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
import D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
import D5.S1.Recurrence.FibVajda
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw FourthSegmentLawRecovery.Length FourthSegmentLawRecovery.Rates
open NativeConditionalControl.DepthLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability

private def x (r : ℝ) : ℝ := r * (1 - r)
private def oddMass (j : ℕ) (r : ℝ) : ℝ := r * x r^j
private def evenMass (j : ℕ) (r : ℝ) : ℝ := (1 - r)^2 * x r^j
private def slope (j : ℕ) (r : ℝ) : ℝ := (j : ℝ) * x r^(j - 1) * (1 - 2 * r)
private def budgetTerm (j : ℕ) (r : ℝ) : ℝ :=
  (3 - 2 * r) * x r^j + (1 - x r) * slope j r

private lemma x_bounds {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    0 < x r ∧ x r < 1 ∧ 0 ≤ 1 - 2 * r := by
  dsimp [x]
  constructor
  · exact mul_pos (by linarith [hr.1]) (by linarith [hr.2])
  constructor
  · nlinarith [sq_nonneg (r - 1 / 2)]
  · linarith [hr.2]

private lemma budget_bound {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    2 * (1 - r) / (1 - x r) ≤ 12 / 7 := by
  apply (div_le_iff₀ (by linarith [(x_bounds hr).2.1])).mpr
  have hh : 0 ≤ (r - 1 / 3) * (r + 1 / 2) :=
    mul_nonneg (by linarith [hr.1]) (by linarith [hr.1])
  dsimp [x]
  nlinarith

private lemma derivatives (j : ℕ) (r : ℝ) :
    HasDerivAt (oddMass j) (x r^j + r * slope j r) r ∧
    HasDerivAt (evenMass j) (-2 * (1 - r) * x r^j + (1 - r)^2 * slope j r) r := by
  have hx : HasDerivAt x (1 - 2 * r) r := by
    convert! (hasDerivAt_id r).mul ((hasDerivAt_const r 1).sub (hasDerivAt_id r)) using 1 <;>
      dsimp [x] <;> ring
  constructor
  · convert! (hasDerivAt_id r).mul (hx.pow j) using 1 <;>
      dsimp [oddMass, slope] <;> ring
  · convert! (((hasDerivAt_const r 1).sub (hasDerivAt_id r)).pow 2).mul (hx.pow j) using 1 <;>
      dsimp [evenMass, slope] <;> ring

private lemma slope_hasSum {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    HasSum (fun j => slope j r) ((1 - 2 * r) / (1 - x r)^2) := by
  have hx := x_bounds hr
  have hn : ‖x r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_right ((1 - 2 * r) / x r)
  convert! hs using 1
  · ext j
    cases j with
    | zero => simp [slope]
    | succ j => simp [slope, pow_succ]; field_simp [hx.1.ne', sub_ne_zero.mpr hx.2.1.ne'] <;> ring
  · field_simp [hx.1.ne', sub_ne_zero.mpr hx.2.1.ne'] <;> ring

private lemma budget_hasSum {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    HasSum (fun j => budgetTerm j r) (4 * (1 - r) / (1 - x r)) := by
  have hx := x_bounds hr
  have hg := hasSum_geometric_of_abs_lt_one (r := x r) (by simpa [abs_of_pos hx.1] using hx.2.1)
  have hs := (hg.mul_left (3 - 2 * r)).add ((slope_hasSum hr).mul_left (1 - x r))
  convert! hs using 1
  field_simp [hx.1.ne', sub_ne_zero.mpr hx.2.1.ne'] <;> ring

private lemma derivative_term_bound {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) (j : ℕ) :
    |deriv (oddMass j) r| + |deriv (evenMass j) r| ≤ budgetTerm j r := by
  have hx := x_bounds hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hj : 0 ≤ slope j r := by
    unfold slope
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1.le _)) hx.2.2
  have hpow : 0 ≤ x r^j := pow_nonneg hx.1.le j
  rw [(derivatives j r).1.deriv, (derivatives j r).2.deriv]
  have hodd : 0 ≤ x r^j + r * slope j r := by positivity
  rw [abs_of_nonneg hodd]
  have hab := abs_add_le (-2 * (1 - r) * x r^j) ((1 - r)^2 * slope j r)
  have hneg : -2 * (1 - r) * x r^j ≤ 0 := by nlinarith [mul_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) hpow]
  have hpos : 0 ≤ (1 - r)^2 * slope j r := by positivity
  rw [abs_of_nonpos hneg, abs_of_nonneg hpos] at hab
  dsimp [budgetTerm, x] at *
  nlinarith

private lemma derivative_budget {r : ℝ} (hr : r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    Summable (fun j => |deriv (oddMass j) r| + |deriv (evenMass j) r|) ∧
    (1 / 2 : ℝ) * (∑' j, (|deriv (oddMass j) r| + |deriv (evenMass j) r|)) ≤
      2 * (1 - r) / (1 - x r) ∧ 2 * (1 - r) / (1 - x r) ≤ 12 / 7 := by
  have hb := budget_hasSum hr
  have hs := Summable.of_nonneg_of_le (fun j => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (derivative_term_bound hr) hb.summable
  refine ⟨hs, ?_, budget_bound hr⟩
  have he := hs.tsum_le_tsum (derivative_term_bound hr) hb.summable
  rw [hb.tsum_eq] at he
  calc
    _ ≤ (1 / 2 : ℝ) * (4 * (1 - r) / (1 - x r)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

private lemma common_tv_bound {A : Type*} [MeasurableSpace A]
    (μ ν ρ : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ρ ≤ μ) (hν : ρ ≤ ν) :
    measurableTotalVariation μ ν ≤ ENNReal.ofReal (1 - ρ.real Set.univ) := by
  letI : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hμ
  change measurableTotalVariation μ ν ≤ ENNReal.ofReal (1 - (ρ Set.univ).toReal)
  rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top ρ Set.univ)]
  exact RarePriorAbsoluteRisk.common_measure_tv μ ν ρ hμ hν

private def common (r s : unitInterval) : Measure RawTail :=
  Measure.sum fun j : ℕ =>
    (alphaMass r * (alphaMass r * betaMass r)^j) • Measure.dirac (some (pWord j 0)) +
    (betaMass s^2 * (alphaMass r * betaMass r)^j) • Measure.dirac (some (pWord j 1))

private lemma mass_real (r : unitInterval) :
    (alphaMass r).toReal = (r : ℝ) ∧ (betaMass r).toReal = 1 - (r : ℝ) := by
  simp [alphaMass, betaMass]

private lemma common_le {r s : unitInterval} (hrs : (r : ℝ) ≤ (s : ℝ))
    (hs : (s : ℝ) ≤ 2 / 5) :
    common r s ≤ explicitStoppedWordLaw .p r ∧
    common r s ≤ explicitStoppedWordLaw .p s := by
  have hb : betaMass s ≤ betaMass r := by
    apply (ENNReal.toReal_le_toReal (by simp [betaMass]) (by simp [betaMass])).mp
    rw [(mass_real s).2, (mass_real r).2]
    linarith
  have ha : alphaMass r ≤ alphaMass s := by
    apply (ENNReal.toReal_le_toReal (by simp [alphaMass]) (by simp [alphaMass])).mp
    rw [(mass_real r).1, (mass_real s).1]
    exact hrs
  have hx : alphaMass r * betaMass r ≤ alphaMass s * betaMass s := by
    apply (ENNReal.toReal_le_toReal (by simp [alphaMass, betaMass, ENNReal.mul_ne_top])
      (by simp [alphaMass, betaMass, ENNReal.mul_ne_top])).mp
    simp only [ENNReal.toReal_mul, (mass_real r).1, (mass_real r).2,
      (mass_real s).1, (mass_real s).2]
    have hh : 0 ≤ ((s : ℝ) - (r : ℝ)) * (1 - (r : ℝ) - (s : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  constructor <;> apply Measure.le_iff.mpr <;> intro E hE <;>
    simp only [common, explicitStoppedWordLaw, Measure.sum_apply _ hE,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  · apply ENNReal.tsum_le_tsum
    intro j
    exact add_le_add le_rfl (mul_le_mul'
      (mul_le_mul' (pow_le_pow_left₀ zero_le hb 2) le_rfl) le_rfl)
  · apply ENNReal.tsum_le_tsum
    intro j
    exact add_le_add
      (mul_le_mul' (mul_le_mul' ha (pow_le_pow_left₀ zero_le hx j)) le_rfl)
      (mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hx j)) le_rfl)

private lemma common_mass {r s : unitInterval}
    (hr : (r : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    (common r s).real Set.univ = ((r : ℝ) + (1 - (s : ℝ))^2) / (1 - x r) := by
  have hf (j : ℕ) : alphaMass r * (alphaMass r * betaMass r)^j ≠ ∞ ∧
      betaMass s^2 * (alphaMass r * betaMass r)^j ≠ ∞ := by
    simp [alphaMass, betaMass, ENNReal.mul_ne_top, ENNReal.pow_ne_top]
  have hg := (hasSum_geometric_of_abs_lt_one (r := x r)
    (by simpa [abs_of_pos (x_bounds hr).1] using (x_bounds hr).2.1))
  change ((common r s) Set.univ).toReal = _
  simp only [common, Measure.sum_apply _ MeasurableSet.univ, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.add_ne_top.mpr (hf j))]
  simp only [ENNReal.toReal_add (hf _).1 (hf _).2, ENNReal.toReal_mul,
    ENNReal.toReal_pow, (mass_real r).1, (mass_real r).2, (mass_real s).2]
  change (∑' j, ((r : ℝ) * x r^j + (1 - (s : ℝ))^2 * x r^j)) = _
  rw [((hg.summable.mul_left (r : ℝ)).tsum_add (hg.summable.mul_left ((1 - (s : ℝ))^2))),
    tsum_mul_left, tsum_mul_left, hg.tsum_eq]
  ring

private lemma stopped_probability (r : unitInterval) :
    IsProbabilityMeasure (explicitStoppedWordLaw .p r) := by
  rw [← (actual_fourth_segment_stopped_word_law r .p).2]
  infer_instance

private lemma word_tv_ordered {r s : unitInterval}
    (hr : (r : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5))
    (hs : (s : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) (hrs : (r : ℝ) ≤ (s : ℝ)) :
    measurableTotalVariation (explicitStoppedWordLaw .p r) (explicitStoppedWordLaw .p s) ≤
      ENNReal.ofReal ((12 / 7 : ℝ) * |(r : ℝ) - (s : ℝ)|) := by
  letI := stopped_probability r
  letI := stopped_probability s
  obtain ⟨hcr, hcs⟩ := common_le hrs hs.2
  apply (common_tv_bound _ _ (common r s) hcr hcs).trans
  apply ENNReal.ofReal_le_ofReal
  rw [common_mass hr, abs_of_nonpos (sub_nonpos.mpr hrs)]
  have hd : 0 < 1 - x r := by linarith [(x_bounds hr).2.1]
  have he : 1 - ((r : ℝ) + (1 - (s : ℝ))^2) / (1 - x r) =
      ((s : ℝ) - (r : ℝ)) * (2 - (r : ℝ) - (s : ℝ)) / (1 - x r) := by
    have hn : 1 - (r : ℝ) * (1 - r) ≠ 0 := by simpa [x] using hd.ne'
    dsimp [x]; field_simp [hn] <;> ring
  rw [he]
  calc
    _ ≤ ((s : ℝ) - (r : ℝ)) * (2 * (1 - (r : ℝ)) / (1 - x r)) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    _ ≤ ((s : ℝ) - (r : ℝ)) * (12 / 7) :=
      mul_le_mul_of_nonneg_left (budget_bound hr) (by linarith)
    _ = _ := by ring

private lemma length_tv_bound {r s : unitInterval}
    (hr : (r : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5))
    (hs : (s : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5)) :
    measurableTotalVariation ((explicitStoppedWordLaw .p r).map lengthProjection)
      ((explicitStoppedWordLaw .p s).map lengthProjection) ≤
      ENNReal.ofReal ((12 / 7 : ℝ) * |(r : ℝ) - (s : ℝ)|) := by
  apply (measurable_total_variation_map_le _ _ _ (measurable_of_countable lengthProjection)).trans
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · exact word_tv_ordered hr hs h
  · rw [measurable_total_variation_comm, abs_sub_comm]
    exact word_tv_ordered hs hr h

private lemma adjacent_rate_gap (k : Depth) :
    |(rate k : ℝ) - (rate ⟨k.val + 1, by omega⟩: ℝ)| =
      1 / ((Nat.fib (k.val + 3) : ℝ) * Nat.fib (k.val + 4)) := by
  have hd (j : ℕ) (hj : 0 < j) : 0 < (Nat.fib j : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr hj
  have hv : (Nat.fib (k.val + 2) : ℝ) * Nat.fib (k.val + 3) -
      (Nat.fib (k.val + 1) : ℝ) * Nat.fib (k.val + 4) = (-1 : ℝ)^(k.val + 1) := by
    have hh := D5.S1.Recurrence.FibVajda.fib_vajda (k.val + 1) 1 2
    norm_num only [Nat.fib_one, Nat.fib_two, mul_one] at hh
    have hz : (Nat.fib (k.val + 2) : ℤ) * Nat.fib (k.val + 3) -
        (Nat.fib (k.val + 1) : ℤ) * Nat.fib (k.val + 4) = (-1 : ℤ)^(k.val + 1) := by
      simpa [Nat.add_assoc] using hh
    exact_mod_cast hz
  change |(Nat.fib (k.val + 1) : ℝ) / Nat.fib (k.val + 3) -
    (Nat.fib (k.val + 2) : ℝ) / Nat.fib (k.val + 4)| = _
  rw [div_sub_div _ _ (hd _ (by omega)).ne' (hd _ (by omega)).ne', abs_div,
    abs_of_pos (mul_pos (hd _ (by omega)) (hd _ (by omega)))]
  have hn : (Nat.fib (k.val + 1) : ℝ) * Nat.fib (k.val + 4) -
      (Nat.fib (k.val + 2) : ℝ) * Nat.fib (k.val + 3) = -((-1 : ℝ)^(k.val + 1)) := by linarith
  rw [mul_comm (Nat.fib (k.val + 3) : ℝ), hn, abs_neg, abs_pow]
  norm_num

private lemma adjacent_length_bound (k : Depth) :
    measurableTotalVariation ((explicitStoppedWordLaw .p (rate k)).map lengthProjection)
      ((explicitStoppedWordLaw .p (rate ⟨k.val + 1, by omega⟩)).map lengthProjection) ≤
      ENNReal.ofReal (12 / (7 * (Nat.fib (k.val + 3) : ℝ) * Nat.fib (k.val + 4))) := by
  have hh := length_tv_bound (rate_bounds k) (rate_bounds ⟨k.val + 1, by omega⟩)
  rw [adjacent_rate_gap] at hh
  convert! hh using 1 <;> congr 1 <;> ring

private lemma dirac_separation (k l : Depth) (hkl : k ≠ l) :
    measurableTotalVariation (Measure.dirac k) (Measure.dirac l) = 1 := by
  apply le_antisymm
  · unfold measurableTotalVariation
    refine iSup_le fun E => max_le ?_ ?_
    · exact (tsub_le_self.trans (measure_mono (Set.subset_univ _) |>.trans_eq (by simp)))
    · exact (tsub_le_self.trans (measure_mono (Set.subset_univ _) |>.trans_eq (by simp)))
  · unfold measurableTotalVariation
    apply le_iSup_of_le (⟨{k}, measurableSet_singleton k⟩ : {E : Set Depth // MeasurableSet E})
    simp [Measure.dirac_apply, Set.mem_singleton_iff, hkl, hkl.symm]

private lemma reciprocal_fib_limit :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (12 / (7 * (Nat.fib (n + 4) : ℝ) * Nat.fib (n + 5)))) atTop (𝓝 0) := by
  have hf (a : ℕ) : Tendsto (fun n : ℕ => (Nat.fib (n + a + 2) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.fib_add_two_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat a))
  have h4 : Tendsto (fun n : ℕ => (Nat.fib (n + 4) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [Nat.add_assoc, Function.comp_def] using tendsto_inv_atTop_zero.comp (hf 2)
  have h5 : Tendsto (fun n : ℕ => (Nat.fib (n + 5) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [Nat.add_assoc, Function.comp_def] using tendsto_inv_atTop_zero.comp (hf 3)
  have he : Tendsto (fun n : ℕ => 12 / (7 * (Nat.fib (n + 4) : ℝ) * Nat.fib (n + 5)))
      atTop (𝓝 0) := by
    convert! (h4.mul h5).const_mul (12 / 7 : ℝ) using 1
    · funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · norm_num
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp he

private lemma adjacent_limit :
    Tendsto (fun n : ℕ => measurableTotalVariation
      ((explicitStoppedWordLaw .p (rate ⟨n + 1, by omega⟩)).map lengthProjection)
      ((explicitStoppedWordLaw .p (rate ⟨n + 2, by omega⟩)).map lengthProjection)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds reciprocal_fib_limit
    (fun _ => zero_le)
  intro n
  simpa [Nat.add_assoc] using adjacent_length_bound ⟨n + 1, by omega⟩

/-- The original phase-p parser has a full countable length law, a uniform
coordinate derivative budget and quantitative TV continuity. Distinct deterministic
Fibonacci depths stay separated although their adjacent output laws converge. -/
theorem original_stopped_length_stability :
    (∀ r : unitInterval,
      (rawReadLaw r).map (fun ω => lengthProjection (stoppedReadWord .p ω)) =
        (explicitStoppedWordLaw .p r).map lengthProjection ∧
      rawReadLaw r {ω | stoppedReadWord .p ω = none} = 0 ∧
      ((explicitStoppedWordLaw .p r).map lengthProjection) {none} = 0 ∧
      ((explicitStoppedWordLaw .p r).map lengthProjection) {some 0} = 0 ∧
      ∀ j : ℕ,
        (((explicitStoppedWordLaw .p r).map lengthProjection) {some (2 * j + 1)}).toReal =
          (r : ℝ) * ((r : ℝ) * (1 - r))^j ∧
        (((explicitStoppedWordLaw .p r).map lengthProjection) {some (2 * j + 2)}).toReal =
          (1 - (r : ℝ))^2 * ((r : ℝ) * (1 - r))^j) ∧
    (∀ r : ℝ, r ∈ Set.Icc (1 / 3 : ℝ) (2 / 5) →
      Summable (fun j : ℕ =>
        |deriv (fun t : ℝ => t * (t * (1 - t))^j) r| +
        |deriv (fun t : ℝ => (1 - t)^2 * (t * (1 - t))^j) r|) ∧
      (1 / 2 : ℝ) * (∑' j : ℕ,
        (|deriv (fun t : ℝ => t * (t * (1 - t))^j) r| +
        |deriv (fun t : ℝ => (1 - t)^2 * (t * (1 - t))^j) r|)) ≤
        2 * (1 - r) / (1 - r * (1 - r)) ∧ 2 * (1 - r) / (1 - r * (1 - r)) ≤ 12 / 7) ∧
    (∀ r s : unitInterval, (r : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5) →
      (s : ℝ) ∈ Set.Icc (1 / 3 : ℝ) (2 / 5) →
      measurableTotalVariation ((explicitStoppedWordLaw .p r).map lengthProjection)
        ((explicitStoppedWordLaw .p s).map lengthProjection) ≤
        ENNReal.ofReal ((12 / 7 : ℝ) * |(r : ℝ) - (s : ℝ)|)) ∧
    (∀ k : Depth,
      |(rate k : ℝ) - (rate ⟨k.val + 1, by omega⟩: ℝ)| =
        1 / ((Nat.fib (k.val + 3) : ℝ) * Nat.fib (k.val + 4)) ∧
      measurableTotalVariation ((explicitStoppedWordLaw .p (rate k)).map lengthProjection)
        ((explicitStoppedWordLaw .p (rate ⟨k.val + 1, by omega⟩)).map lengthProjection) ≤
        ENNReal.ofReal (12 / (7 * (Nat.fib (k.val + 3) : ℝ) * Nat.fib (k.val + 4)))) ∧
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (12 / (7 * (Nat.fib (n + 4) : ℝ) * Nat.fib (n + 5)))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => measurableTotalVariation
      ((explicitStoppedWordLaw .p (rate ⟨n + 1, by omega⟩)).map lengthProjection)
      ((explicitStoppedWordLaw .p (rate ⟨n + 2, by omega⟩)).map lengthProjection)) atTop (𝓝 0) ∧
    (∀ k l : Depth, k ≠ l →
      measurableTotalVariation (Measure.dirac k) (Measure.dirac l) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, reciprocal_fib_limit, adjacent_limit, dirac_separation⟩
  · intro r
    refine ⟨?_, actual_noncompletion_mass_zero r .p, ?_, ?_, ?_⟩
    · rw [← (actual_fourth_segment_stopped_word_law r .p).2,
        Measure.map_map (measurable_of_countable lengthProjection) (measurable_stopped_read_word .p)]
      rfl
    · simp [explicitStoppedWordLaw, Measure.map_apply
        (measurable_of_countable lengthProjection), Measure.sum_apply, lengthProjection]
    · simp [explicitStoppedWordLaw, Measure.map_apply
        (measurable_of_countable lengthProjection), Measure.sum_apply, lengthProjection, p_word_length]
    · intro j
      rw [(p_kernel_atoms r j).1, (p_kernel_atoms r j).2]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, (mass_real r).1, (mass_real r).2]
      exact ⟨trivial, trivial⟩
  · intro r hr
    exact derivative_budget hr
  · intro r s hr hs
    exact length_tv_bound hr hs
  · intro k
    exact ⟨adjacent_rate_gap k, adjacent_length_bound k⟩

#print axioms original_stopped_length_stability

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
