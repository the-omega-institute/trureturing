/- GID: D5/S3/Analytic/Asymptotics/PhaseLawSpectralEscape
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PhaseLawSpectralEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable positive spectra admit phase-only moment inversion and native weak escape. -/

import D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
import D5.S3.Analytic.Asymptotics.PhaseLawDyadicCoercivity
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

set_option autoImplicit false
open Filter MeasureTheory Set ENNReal
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.PhaseLawSpectralEscape

open LogarithmicPhaseStiffness (phaseCost)
open PhaseLawDyadicCoercivity (lowCutoff maskedMoment maskedTail phase_law_dyadic_coercivity)

noncomputable section

def maskedPhase {ι : Type*} (frequency weight : ι → ℝ) (strict : Bool)
    (cutoff time : ℝ) : ℝ := by
  classical
  exact ∑' index, if lowCutoff frequency strict cutoff index then
    2 * weight index * (1 - Real.cos (frequency index * time)) else 0

structure InverseConstants where
  invCost : ℝ
  firstCutoff : ℝ
  momentError : ℝ
  secondMoment : ℝ
  fourthMoment : ℝ
  tailMass : ℝ
  numerator : ℝ
  firstLog : ℝ
  firstTime : ℝ
  distributionError : ℝ

def inverseConstants (alpha error firstTime mass : ℝ) : InverseConstants :=
  let invCost := 2 * alpha + 3 * error
  let firstCutoff := 16 / firstTime
  let momentError := error + 136 * invCost
  let secondMoment := max momentError (firstCutoff ^ 2 * mass +
    alpha * (Real.log firstCutoff) ^ 2)
  let fourthMoment := max (64 * invCost) (firstCutoff ^ 2 * mass)
  let tailMass := max (32 * invCost) (firstCutoff ^ 2 * mass)
  let numerator := secondMoment + fourthMoment / 8
  let firstLog := max (max 1 (Real.log firstCutoff)) (4 * error / alpha)
  ⟨invCost, firstCutoff, momentError, secondMoment, fourthMoment, tailMass, numerator,
    firstLog, Real.exp (-firstLog), 4 * (numerator + error) / alpha⟩

def betaTwoOne : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.betaMeasure 2 1,
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by norm_num)⟩

def spectralProbability {ι : Type*} (discrete : PMF ι) (position : ι → ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨(PMF.map position discrete).toMeasure, inferInstance⟩

def chordCoordinate {ι : Type*} (frequency weight : ι → ℝ) (time : ℝ) (index : ι) :
    ℂ := (Real.sqrt (weight index) : ℂ) *
      (Complex.exp (Complex.I * ((frequency index * time : ℝ) : ℂ)) - 1) /
        (Real.sqrt (phaseCost frequency weight time) : ℂ)

set_option maxHeartbeats 1600000 in
theorem phase_law_spectral_escape {ι : Type*} (frequency weight : ι → ℝ)
    (hweight : ∀ index, 0 ≤ weight index) (hfrequency : ∀ index, 0 < frequency index)
    (hsum : Summable weight) {alpha error firstTime : ℝ} (halpha : 0 < alpha)
    (herror : 0 ≤ error) (hfirst : 0 < firstTime) (hsmall : firstTime ≤ Real.exp (-1))
    (hlaw : ∀ time, 0 < time → time ≤ firstTime →
      |phaseCost frequency weight time - alpha * time ^ 2 * (Real.log (1 / time)) ^ 2| ≤
        error * time ^ 2 * (Real.log (1 / time) + 1)) :
    let constants := inverseConstants alpha error firstTime (∑' index, weight index)
    (∀ cutoff, 1 ≤ cutoff → ∀ strict : Bool,
      |maskedMoment frequency weight strict 2 cutoff - alpha * (Real.log cutoff) ^ 2| ≤
          constants.secondMoment * (Real.log cutoff + 1) ∧
      maskedMoment frequency weight strict 4 cutoff ≤
          constants.fourthMoment * cutoff ^ 2 * (Real.log cutoff + 1) ∧
      maskedTail frequency weight strict cutoff ≤
          constants.tailMass * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1)) ∧
    (∀ time, 0 < |time| → |time| ≤ constants.firstTime →
      alpha / 2 * time ^ 2 * (Real.log (1 / |time|)) ^ 2 ≤
          phaseCost frequency weight time ∧
      0 < alpha / 2 * time ^ 2 * (Real.log (1 / |time|)) ^ 2 ∧
      ∀ strict : Bool, ∀ position ∈ Icc (0 : ℝ) 1,
        |maskedPhase frequency weight strict
          (Real.exp (position * Real.log (1 / |time|))) time /
            phaseCost frequency weight time - position ^ 2| ≤
          constants.distributionError / Real.log (1 / |time|)) ∧
    ∃ probability : ℝ → ProbabilityMeasure ℝ,
      ∃ chord : ℝ → lp (fun _ : ι => ℂ) 2,
        (∀ time, 0 < |time| → |time| ≤ constants.firstTime →
          (∃ discrete : PMF ι,
            (∀ index, discrete index = ENNReal.ofReal
              (2 * weight index * (1 - Real.cos (frequency index * time)) /
                phaseCost frequency weight time)) ∧
            probability time = spectralProbability discrete
              (fun index => Real.log (frequency index) / Real.log (1 / |time|))) ∧
          (∀ index, chord time index = chordCoordinate frequency weight time index) ∧
          ‖chord time‖ = 1) ∧
        Tendsto probability (𝓝[≠] (0 : ℝ)) (𝓝 betaTwoOne) ∧
        (∀ test : BoundedContinuousFunction ℝ ℝ,
          Tendsto (fun time => ∫ value, test value ∂(probability time : Measure ℝ))
            (𝓝[≠] (0 : ℝ)) (𝓝 (∫ value, test value ∂(betaTwoOne : Measure ℝ)))) ∧
        Tendsto (fun time => toWeakSpace ℂ _ (chord time)) (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
        (∀ functional : StrongDual ℂ (lp (fun _ : ι => ℂ) 2),
          Tendsto (fun time => functional (chord time)) (𝓝[≠] (0 : ℝ)) (𝓝 0)) := by
  classical
  dsimp only
  let constants := inverseConstants alpha error firstTime (∑' index, weight index)
  have hphase_nonneg (time : ℝ) (index : ι) :
      0 ≤ 2 * weight index * (1 - Real.cos (frequency index * time)) :=
    mul_nonneg (mul_nonneg (by norm_num) (hweight index))
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hphase_bound (time : ℝ) (index : ι) :
      2 * weight index * (1 - Real.cos (frequency index * time)) ≤ 4 * weight index := by
    have hcos := Real.neg_one_le_cos (frequency index * time)
    nlinarith [hweight index]
  have hphase_sum (time : ℝ) :
      Summable (fun index => 2 * weight index * (1 - Real.cos (frequency index * time))) :=
    Summable.of_nonneg_of_le (hphase_nonneg time) (hphase_bound time) (hsum.mul_left 4)
  have hmoment_sum (strict : Bool) (power : ℕ) {cutoff : ℝ} (hcutoff : 0 ≤ cutoff) :
      Summable (fun index => if lowCutoff frequency strict cutoff index then
        weight index * frequency index ^ power else 0) := by
    apply Summable.of_nonneg_of_le _ _ (hsum.mul_left (cutoff ^ power))
    · intro index
      have hai := hweight index
      have hgi := (hfrequency index).le
      split_ifs <;> positivity
    · intro index
      split_ifs with hlow
      · have hle : frequency index ≤ cutoff := by
          cases strict <;> simp only [lowCutoff, Bool.false_eq_true, if_false, if_true] at hlow
          · exact hlow
          · exact hlow.le
        calc
          _ ≤ weight index * cutoff ^ power :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hfrequency index).le hle _) (hweight index)
          _ = _ := by ring
      · exact mul_nonneg (pow_nonneg hcutoff _) (hweight index)
  have htail_sum (strict : Bool) (cutoff : ℝ) :
      Summable (fun index => if (if strict then cutoff < frequency index
        else cutoff ≤ frequency index) then weight index else 0) := by
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro index
      split_ifs <;> first | exact hweight index | exact le_rfl
    · intro index
      split_ifs <;> first | exact le_rfl | exact hweight index
  have hscalar_taylor {value : ℝ} (hvalue : |value| ≤ 1) :
      |2 * (1 - Real.cos value) - value ^ 2| ≤ value ^ 4 / 8 := by
    have hcos := Real.cos_bound hvalue
    rw [(by decide : Even (4 : ℕ)).pow_abs] at hcos
    have heq : 2 * (1 - Real.cos value) - value ^ 2 =
        -2 * (Real.cos value - (1 - value ^ 2 / 2)) := by ring
    rw [heq, abs_mul]
    norm_num
    nlinarith [pow_nonneg (sq_nonneg value) 2]
  have hfirst_one : firstTime ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlarge_positive {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) : 1 ≤ cutoff := by
    have hmul := (div_le_iff₀ hfirst).mp hcutoff
    nlinarith
  have hcoercivity := phase_law_dyadic_coercivity frequency weight hweight hfrequency hsum
    halpha herror hfirst hsmall hlaw
  have hquartic_large {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) (strict : Bool) :
      maskedMoment frequency weight strict 4 cutoff ≤
        64 * (2 * alpha + 3 * error) * cutoff ^ 2 * (Real.log cutoff + 1) :=
    (hcoercivity cutoff hcutoff strict).1
  have htail_large {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) (strict : Bool) :
      maskedTail frequency weight strict cutoff ≤
        32 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) :=
    (hcoercivity cutoff hcutoff strict).2
  have hmask_phase_sum (strict : Bool) (cutoff time : ℝ) :
      Summable (fun index => if lowCutoff frequency strict cutoff index then
        2 * weight index * (1 - Real.cos (frequency index * time)) else 0) := by
    apply Summable.of_nonneg_of_le _ _ (hsum.mul_left 4)
    · intro index
      split_ifs <;> first | exact hphase_nonneg time index | exact le_rfl
    · intro index
      split_ifs
      · exact hphase_bound time index
      · exact mul_nonneg (by norm_num) (hweight index)
  have hcutoff_complement (strict : Bool) (cutoff : ℝ) (index : ι) :
      (¬lowCutoff frequency strict cutoff index) ↔
        (if !strict then cutoff < frequency index else cutoff ≤ frequency index) := by
    cases strict <;> simp [lowCutoff, not_le, not_lt]
  have hcosine_approximation {cutoff time : ℝ} (hcutoff : 0 < cutoff)
      (hsmall_arg : cutoff * |time| ≤ 1) (strict : Bool) :
      |phaseCost frequency weight time - time ^ 2 * maskedMoment frequency weight strict 2 cutoff| ≤
        time ^ 4 / 8 * maskedMoment frequency weight strict 4 cutoff +
          4 * maskedTail frequency weight (!strict) cutoff ∧
      |maskedPhase frequency weight strict cutoff time -
        time ^ 2 * maskedMoment frequency weight strict 2 cutoff| ≤
          time ^ 4 / 8 * maskedMoment frequency weight strict 4 cutoff := by
    let moment2 := fun index => if lowCutoff frequency strict cutoff index
      then weight index * frequency index ^ 2 else 0
    let moment4 := fun index => if lowCutoff frequency strict cutoff index
      then weight index * frequency index ^ 4 else 0
    let high := fun index => if (if !strict then cutoff < frequency index
      else cutoff ≤ frequency index) then weight index else 0
    have hlow_error (index : ι) (hlow : lowCutoff frequency strict cutoff index) :
        |2 * weight index * (1 - Real.cos (frequency index * time)) -
          time ^ 2 * weight index * frequency index ^ 2| ≤
            time ^ 4 / 8 * weight index * frequency index ^ 4 := by
      have hle : frequency index ≤ cutoff := by
        cases strict <;> simp only [lowCutoff, Bool.false_eq_true, if_false, if_true] at hlow
        · exact hlow
        · exact hlow.le
      have harg : |frequency index * time| ≤ 1 := by
        rw [abs_mul, abs_of_pos (hfrequency index)]
        exact (mul_le_mul_of_nonneg_right hle (abs_nonneg time)).trans hsmall_arg
      have htaylor := mul_le_mul_of_nonneg_left (hscalar_taylor harg) (hweight index)
      have heq : 2 * weight index * (1 - Real.cos (frequency index * time)) -
          time ^ 2 * weight index * frequency index ^ 2 =
            weight index * (2 * (1 - Real.cos (frequency index * time)) -
              (frequency index * time) ^ 2) := by ring
      rw [heq, abs_mul, abs_of_nonneg (hweight index)]
      exact htaylor.trans_eq (by ring)
    have hmajorant (index : ι) :
        ‖2 * weight index * (1 - Real.cos (frequency index * time)) - time ^ 2 * moment2 index‖ ≤
          time ^ 4 / 8 * moment4 index + 4 * high index := by
      by_cases hlow : lowCutoff frequency strict cutoff index
      · have hnot_high := not_iff_not.mpr (hcutoff_complement strict cutoff index) |>.mp
          (not_not.mpr hlow)
        simpa only [moment2, moment4, high, if_pos hlow, if_neg hnot_high, mul_zero, add_zero,
          Real.norm_eq_abs, mul_assoc] using hlow_error index hlow
      · have hhigh := (hcutoff_complement strict cutoff index).mp hlow
        simp only [moment2, moment4, high, if_neg hlow, if_pos hhigh, mul_zero, sub_zero,
          zero_add, Real.norm_eq_abs, abs_of_nonneg (hphase_nonneg time index)]
        exact hphase_bound time index
    have hlow_majorant (index : ι) :
        ‖(if lowCutoff frequency strict cutoff index then
          2 * weight index * (1 - Real.cos (frequency index * time)) else 0) -
            time ^ 2 * moment2 index‖ ≤ time ^ 4 / 8 * moment4 index := by
      by_cases hlow : lowCutoff frequency strict cutoff index
      · simpa only [moment2, moment4, if_pos hlow, Real.norm_eq_abs, mul_assoc]
          using hlow_error index hlow
      · simp only [moment2, moment4, if_neg hlow, mul_zero, sub_zero, norm_zero]
        exact le_rfl
    have hsum2 := hmoment_sum strict 2 hcutoff.le
    have hsum4 := hmoment_sum strict 4 hcutoff.le
    have hsumhigh := htail_sum (!strict) cutoff
    have hfull := tsum_of_norm_bounded
      ((hsum4.mul_left (time ^ 4 / 8)).add (hsumhigh.mul_left 4)).hasSum hmajorant
    have hlow := tsum_of_norm_bounded (hsum4.mul_left (time ^ 4 / 8)).hasSum hlow_majorant
    rw [(hphase_sum time).tsum_sub (hsum2.mul_left (time ^ 2)),
      (hsum4.mul_left (time ^ 4 / 8)).tsum_add (hsumhigh.mul_left 4),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, Real.norm_eq_abs] at hfull
    rw [(hmask_phase_sum strict cutoff time).tsum_sub (hsum2.mul_left (time ^ 2)),
      tsum_mul_left, tsum_mul_left, Real.norm_eq_abs] at hlow
    exact ⟨hfull, hlow⟩
  have hsecond_large {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) (strict : Bool) :
      |maskedMoment frequency weight strict 2 cutoff - alpha * (Real.log cutoff) ^ 2| ≤
        (error + 136 * (2 * alpha + 3 * error)) * (Real.log cutoff + 1) := by
    have hcutoff_one := hlarge_positive hcutoff
    have hcutoff_pos : 0 < cutoff := by linarith
    have htime_pos : 0 < 1 / cutoff := by positivity
    have htime_small : 1 / cutoff ≤ firstTime := by
      apply (div_le_iff₀ hcutoff_pos).mpr
      have hmul := (div_le_iff₀ hfirst).mp hcutoff
      nlinarith
    have hsmall_arg : cutoff * |1 / cutoff| ≤ 1 := by
      rw [abs_of_pos htime_pos, mul_one_div_cancel hcutoff_pos.ne']
    have happ := (hcosine_approximation hcutoff_pos hsmall_arg strict).1
    have hfourth := mul_le_mul_of_nonneg_left (hquartic_large hcutoff strict)
      (by positivity : 0 ≤ (1 / cutoff) ^ 4 / 8)
    have htail := mul_le_mul_of_nonneg_left (htail_large hcutoff (!strict))
      (by norm_num : (0 : ℝ) ≤ 4)
    have herror_bound : (1 / cutoff) ^ 4 / 8 * maskedMoment frequency weight strict 4 cutoff +
        4 * maskedTail frequency weight (!strict) cutoff ≤
          136 * (2 * alpha + 3 * error) * (1 / cutoff) ^ 2 * (Real.log cutoff + 1) := by
      calc
        _ ≤ (1 / cutoff) ^ 4 / 8 *
              (64 * (2 * alpha + 3 * error) * cutoff ^ 2 * (Real.log cutoff + 1)) +
            4 * (32 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1)) :=
          add_le_add hfourth htail
        _ = _ := by field_simp <;> ring
    have hphase := hlaw (1 / cutoff) htime_pos htime_small
    simp only [one_div, Real.log_inv, neg_neg] at hphase
    have htriangle := abs_sub_le
      ((1 / cutoff) ^ 2 * maskedMoment frequency weight strict 2 cutoff)
      (phaseCost frequency weight (1 / cutoff))
      (alpha * (1 / cutoff) ^ 2 * (Real.log cutoff) ^ 2)
    rw [abs_sub_comm ((1 / cutoff) ^ 2 * maskedMoment frequency weight strict 2 cutoff)
      (phaseCost frequency weight (1 / cutoff))] at htriangle
    have hnorm : |(1 / cutoff) ^ 2 * (maskedMoment frequency weight strict 2 cutoff -
        alpha * (Real.log cutoff) ^ 2)| ≤
          (error + 136 * (2 * alpha + 3 * error)) * (1 / cutoff) ^ 2 * (Real.log cutoff + 1) := by
      have happ' := happ.trans herror_bound
      simp only [one_div] at happ' htriangle ⊢
      have hsum := htriangle.trans (add_le_add happ' hphase)
      calc
        _ = |cutoff⁻¹ ^ 2 * maskedMoment frequency weight strict 2 cutoff -
            alpha * cutoff⁻¹ ^ 2 * (Real.log cutoff) ^ 2| := by congr 1; ring
        _ ≤ 136 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) +
            error * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := hsum
        _ = _ := by ring
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)] at hnorm
    exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos htime_pos)).mp (by nlinarith [hnorm])
  have hmass_nonneg : 0 ≤ ∑' index, weight index := tsum_nonneg hweight
  have hmoment_bound {cutoff : ℝ} (hcutoff : 0 ≤ cutoff) (strict : Bool) (power : ℕ) :
      0 ≤ maskedMoment frequency weight strict power cutoff ∧
      maskedMoment frequency weight strict power cutoff ≤ cutoff ^ power * (∑' index, weight index) := by
    have hnonneg (index : ι) : 0 ≤ (if lowCutoff frequency strict cutoff index then
        weight index * frequency index ^ power else 0) := by
      have hai := hweight index
      have hgi := (hfrequency index).le
      split_ifs <;> positivity
    refine ⟨tsum_nonneg hnonneg, ?_⟩
    rw [← tsum_mul_left]
    apply (hmoment_sum strict power hcutoff).tsum_le_tsum _ (hsum.mul_left (cutoff ^ power))
    intro index
    split_ifs with hlow
    · have hle : frequency index ≤ cutoff := by
        cases strict <;> simp only [lowCutoff, Bool.false_eq_true, if_false, if_true] at hlow
        · exact hlow
        · exact hlow.le
      calc
        _ ≤ weight index * cutoff ^ power :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hfrequency index).le hle _) (hweight index)
        _ = _ := by ring
    · exact mul_nonneg (pow_nonneg hcutoff _) (hweight index)
  have htail_bound (cutoff : ℝ) (strict : Bool) :
      0 ≤ maskedTail frequency weight strict cutoff ∧
      maskedTail frequency weight strict cutoff ≤ ∑' index, weight index := by
    have hnonneg (index : ι) : 0 ≤ (if (if strict then cutoff < frequency index
        else cutoff ≤ frequency index) then weight index else 0) := by
      split_ifs <;> first | exact hweight index | exact le_rfl
    refine ⟨tsum_nonneg hnonneg, (htail_sum strict cutoff).tsum_le_tsum ?_ hsum⟩
    intro index
    split_ifs <;> first | exact le_rfl | exact hweight index
  have hcutoff0_positive : 0 < 16 / firstTime := by positivity
  have hcutoff0_one : 1 ≤ 16 / firstTime := hlarge_positive le_rfl
  have hconstants_nonneg : 0 ≤ constants.secondMoment ∧ 0 ≤ constants.fourthMoment ∧
      0 ≤ constants.tailMass ∧ 0 ≤ constants.numerator ∧ 0 ≤ constants.distributionError := by
    dsimp only [constants, inverseConstants]
    have hcost : 0 ≤ 2 * alpha + 3 * error := by positivity
    have hsecond : 0 ≤ max (error + 136 * (2 * alpha + 3 * error))
        ((16 / firstTime) ^ 2 * (∑' index, weight index) + alpha * (Real.log (16 / firstTime)) ^ 2) :=
      (by positivity : 0 ≤ error + 136 * (2 * alpha + 3 * error)).trans (le_max_left _ _)
    have hfourth : 0 ≤ max (64 * (2 * alpha + 3 * error))
        ((16 / firstTime) ^ 2 * (∑' index, weight index)) :=
      (by positivity : 0 ≤ 64 * (2 * alpha + 3 * error)).trans (le_max_left _ _)
    have htail : 0 ≤ max (32 * (2 * alpha + 3 * error))
        ((16 / firstTime) ^ 2 * (∑' index, weight index)) :=
      (by positivity : 0 ≤ 32 * (2 * alpha + 3 * error)).trans (le_max_left _ _)
    exact ⟨hsecond, hfourth, htail, by positivity, by positivity⟩
  have hall_moments (cutoff : ℝ) (hcutoff : 1 ≤ cutoff) (strict : Bool) :
      |maskedMoment frequency weight strict 2 cutoff - alpha * (Real.log cutoff) ^ 2| ≤
          constants.secondMoment * (Real.log cutoff + 1) ∧
      maskedMoment frequency weight strict 4 cutoff ≤
          constants.fourthMoment * cutoff ^ 2 * (Real.log cutoff + 1) ∧
      maskedTail frequency weight strict cutoff ≤
          constants.tailMass * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := by
    have hcutoff_pos : 0 < cutoff := by linarith
    have hlog := Real.log_nonneg hcutoff
    by_cases hlarge : 16 / firstTime ≤ cutoff
    · refine ⟨(hsecond_large hlarge strict).trans ?_,
        (hquartic_large hlarge strict).trans ?_, (htail_large hlarge strict).trans ?_⟩
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith : 0 ≤ Real.log cutoff + 1)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (sq_nonneg cutoff)) (by linarith : 0 ≤ Real.log cutoff + 1)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (sq_nonneg cutoff⁻¹)) (by linarith : 0 ≤ Real.log cutoff + 1)
    · have hearly : cutoff ≤ 16 / firstTime := (not_le.mp hlarge).le
      have hlog0 := Real.log_nonneg hcutoff0_one
      have hlogle := Real.log_le_log hcutoff_pos hearly
      have hsecond := hmoment_bound hcutoff_pos.le strict 2
      have hfourth := hmoment_bound hcutoff_pos.le strict 4
      have htail := htail_bound cutoff strict
      have hscale : cutoff ^ 2 ≤ (16 / firstTime) ^ 2 :=
        pow_le_pow_left₀ hcutoff_pos.le hearly 2
      have hweightscale := mul_le_mul_of_nonneg_right hscale hmass_nonneg
      have hsecond_const : (16 / firstTime) ^ 2 * (∑' index, weight index) +
          alpha * (Real.log (16 / firstTime)) ^ 2 ≤ constants.secondMoment := le_max_right _ _
      have hfourth_const : (16 / firstTime) ^ 2 * (∑' index, weight index) ≤
          constants.fourthMoment := le_max_right _ _
      have htail_const : (16 / firstTime) ^ 2 * (∑' index, weight index) ≤
          constants.tailMass := le_max_right _ _
      refine ⟨?_, ?_, ?_⟩
      · have hlogweight := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlog hlogle 2) halpha.le
        have hconstant_log : 0 ≤ constants.secondMoment * Real.log cutoff :=
          mul_nonneg hconstants_nonneg.1 hlog
        apply abs_le.mpr
        constructor <;> nlinarith [hsecond.1, hsecond.2]
      · calc
          _ ≤ cutoff ^ 4 * (∑' index, weight index) := hfourth.2
          _ = (cutoff ^ 2 * (∑' index, weight index)) * cutoff ^ 2 := by ring
          _ ≤ constants.fourthMoment * cutoff ^ 2 :=
            mul_le_mul_of_nonneg_right (hweightscale.trans hfourth_const) (sq_nonneg cutoff)
          _ ≤ _ := by
            have hprod := mul_nonneg
              (mul_nonneg hconstants_nonneg.2.1 (sq_nonneg cutoff)) hlog
            nlinarith
      · have htail_product : maskedTail frequency weight strict cutoff * cutoff ^ 2 ≤
          constants.tailMass :=
          (mul_le_mul_of_nonneg_right htail.2 (sq_nonneg cutoff)).trans
            (by nlinarith [hweightscale, htail_const])
        have htail_log : constants.tailMass ≤ constants.tailMass * (Real.log cutoff + 1) := by
          nlinarith [mul_nonneg hconstants_nonneg.2.2.1 hlog]
        apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hcutoff_pos)).mp
        have heq : constants.tailMass * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) * cutoff ^ 2 =
            constants.tailMass * (Real.log cutoff + 1) := by field_simp
        rw [heq]
        exact htail_product.trans htail_log
  have heven (time : ℝ) : phaseCost frequency weight |time| = phaseCost frequency weight time := by
    by_cases htime : 0 ≤ time
    · rw [abs_of_nonneg htime]
    · simp only [abs_of_neg (lt_of_not_ge htime), phaseCost, mul_neg, Real.cos_neg]
  have htime_log {time : ℝ} (htime : 0 < |time|) (hthreshold : |time| ≤ constants.firstTime) :
      constants.firstLog ≤ Real.log (1 / |time|) := by
    have hlog := Real.log_le_log htime hthreshold
    change Real.log |time| ≤ Real.log (Real.exp (-constants.firstLog)) at hlog
    rw [Real.log_exp] at hlog
    simp only [one_div, Real.log_inv]
    linarith
  have hthreshold_first : constants.firstTime ≤ firstTime := by
    have hlog : Real.log (16 / firstTime) ≤ constants.firstLog :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hlog)
    change Real.exp (-constants.firstLog) ≤ firstTime
    have heq : Real.exp (-Real.log (16 / firstTime)) = firstTime / 16 := by
      rw [Real.exp_neg, Real.exp_log hcutoff0_positive]
      field_simp
    rw [heq] at hexp
    exact hexp.trans (by linarith)
  have hpositive {time : ℝ} (htime : 0 < |time|) (hthreshold : |time| ≤ constants.firstTime) :
      alpha / 2 * time ^ 2 * (Real.log (1 / |time|)) ^ 2 ≤ phaseCost frequency weight time ∧
      0 < alpha / 2 * time ^ 2 * (Real.log (1 / |time|)) ^ 2 := by
    have hlog := htime_log htime hthreshold
    have hlogone : 1 ≤ Real.log (1 / |time|) :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hlog
    have hlogerror : 4 * error / alpha ≤ Real.log (1 / |time|) := (le_max_right _ _).trans hlog
    have hmul := (div_le_iff₀ halpha).mp hlogerror
    have herrorlog : error * (Real.log (1 / |time|) + 1) ≤
        alpha / 2 * (Real.log (1 / |time|)) ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_right hmul
        (by linarith : 0 ≤ Real.log (1 / |time|))
      nlinarith
    have hphase := hlaw |time| htime (hthreshold.trans hthreshold_first)
    rw [heven, sq_abs] at hphase
    have hlower := (abs_le.mp hphase).1
    have hscaled := mul_le_mul_of_nonneg_left herrorlog (sq_nonneg time)
    have htime_ne : time ≠ 0 := abs_pos.mp htime
    refine ⟨by nlinarith, ?_⟩
    exact mul_pos (mul_pos (div_pos halpha (by norm_num)) (sq_pos_of_ne_zero htime_ne))
      (sq_pos_of_pos (by linarith))
  have hdistribution {time : ℝ} (htime : 0 < |time|)
      (hthreshold : |time| ≤ constants.firstTime) (strict : Bool)
      {position : ℝ} (hposition : position ∈ Icc (0 : ℝ) 1) :
      |maskedPhase frequency weight strict (Real.exp (position * Real.log (1 / |time|))) time /
        phaseCost frequency weight time - position ^ 2| ≤
          constants.distributionError / Real.log (1 / |time|) := by
    let logarithm := Real.log (1 / |time|)
    let cutoff := Real.exp (position * logarithm)
    have hlogone : 1 ≤ logarithm :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans (htime_log htime hthreshold)
    have hlogpos : 0 < logarithm := by linarith
    have hfourth_nonneg := hconstants_nonneg.2.1
    have hcutoffpos : 0 < cutoff := Real.exp_pos _
    have hcutoffone : 1 ≤ cutoff := Real.one_le_exp_iff.mpr (mul_nonneg hposition.1 hlogpos.le)
    have hlogcutoff : Real.log cutoff = position * logarithm := Real.log_exp _
    have hscaledposition : position * logarithm ≤ logarithm := by
      nlinarith [mul_le_mul_of_nonneg_right hposition.2 hlogpos.le]
    have hcutoffupper : cutoff ≤ 1 / |time| := by
      have derivedEstimate := Real.exp_le_exp.mpr hscaledposition
      rw [Real.exp_log (div_pos (by norm_num) htime)] at derivedEstimate
      exact derivedEstimate
    have hsmall_arg : cutoff * |time| ≤ 1 := by
      have derivedEstimate := mul_le_mul_of_nonneg_right hcutoffupper htime.le
      exact derivedEstimate.trans_eq (by field_simp)
    have hscale_square : time ^ 2 * cutoff ^ 2 ≤ 1 := by
      have derivedEstimate := pow_le_pow_left₀ (mul_nonneg hcutoffpos.le (abs_nonneg time)) hsmall_arg 2
      simpa only [mul_pow, sq_abs, one_pow, mul_comm] using derivedEstimate
    have hmoment := (hall_moments cutoff hcutoffone strict).1
    have hfourth := (hall_moments cutoff hcutoffone strict).2.1
    have hlow := (hcosine_approximation hcutoffpos hsmall_arg strict).2
    have hmoment_scaled := mul_le_mul_of_nonneg_left hmoment (sq_nonneg time)
    have hfourth_scaled := mul_le_mul_of_nonneg_left hfourth (by positivity : 0 ≤ time ^ 4 / 8)
    have hscale_bound : time ^ 4 / 8 *
        (constants.fourthMoment * cutoff ^ 2 * (Real.log cutoff + 1)) ≤
          constants.fourthMoment / 8 * time ^ 2 * (logarithm + 1) := by
      have hlogcutoff_nonneg : 0 ≤ Real.log cutoff := Real.log_nonneg hcutoffone
      have hscale := mul_le_mul_of_nonneg_left hscale_square
        (by positivity : 0 ≤ constants.fourthMoment / 8 * time ^ 2 * (Real.log cutoff + 1))
      have hlogscale := mul_le_mul_of_nonneg_left
        (by rw [hlogcutoff]; linarith : Real.log cutoff + 1 ≤ logarithm + 1)
        (by positivity : 0 ≤ constants.fourthMoment / 8 * time ^ 2)
      nlinarith
    have hmoment_bound_scaled : time ^ 2 * constants.secondMoment * (Real.log cutoff + 1) ≤
        constants.secondMoment * time ^ 2 * (logarithm + 1) := by
      have derivedEstimate := mul_le_mul_of_nonneg_left
        (by rw [hlogcutoff]; linarith : Real.log cutoff + 1 ≤ logarithm + 1)
        (mul_nonneg (sq_nonneg time) hconstants_nonneg.1)
      nlinarith
    have hnumerator : |maskedPhase frequency weight strict cutoff time -
        alpha * time ^ 2 * (position * logarithm) ^ 2| ≤
          constants.numerator * time ^ 2 * (logarithm + 1) := by
      have htriangle := abs_sub_le (maskedPhase frequency weight strict cutoff time)
        (time ^ 2 * maskedMoment frequency weight strict 2 cutoff)
        (alpha * time ^ 2 * (position * logarithm) ^ 2)
      have hmoment_abs : |time ^ 2 * maskedMoment frequency weight strict 2 cutoff -
          alpha * time ^ 2 * (position * logarithm) ^ 2| =
            time ^ 2 * |maskedMoment frequency weight strict 2 cutoff -
              alpha * (Real.log cutoff) ^ 2| := by
        calc
          _ = |time ^ 2 * (maskedMoment frequency weight strict 2 cutoff -
              alpha * (Real.log cutoff) ^ 2)| := by rw [hlogcutoff]; congr 1; ring
          _ = _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg time)]
      rw [hmoment_abs] at htriangle
      have hmoment_scaled_bound : time ^ 2 * |maskedMoment frequency weight strict 2 cutoff -
          alpha * (Real.log cutoff) ^ 2| ≤
            constants.secondMoment * time ^ 2 * (logarithm + 1) :=
        hmoment_scaled.trans (by nlinarith [hmoment_bound_scaled])
      have derivedEstimate := htriangle.trans (add_le_add (hlow.trans (hfourth_scaled.trans hscale_bound))
        hmoment_scaled_bound)
      have hnum : constants.numerator = constants.secondMoment + constants.fourthMoment / 8 := rfl
      rw [hnum]
      nlinarith
    have hphase := hlaw |time| htime (hthreshold.trans hthreshold_first)
    rw [heven, sq_abs] at hphase
    have hsquare : 0 ≤ position ^ 2 ∧ position ^ 2 ≤ 1 := by
      constructor
      · exact sq_nonneg position
      · nlinarith [hposition.1, hposition.2]
    have hphase_scaled := mul_le_mul_of_nonneg_left hphase hsquare.1
    have hphase_reduced : position ^ 2 *
        |phaseCost frequency weight time - alpha * time ^ 2 * logarithm ^ 2| ≤
          error * time ^ 2 * (logarithm + 1) := by
      have derivedEstimate := mul_le_mul_of_nonneg_right hsquare.2
        (by positivity : 0 ≤ error * time ^ 2 * (logarithm + 1))
      nlinarith
    have hratio_numerator : |maskedPhase frequency weight strict cutoff time -
        position ^ 2 * phaseCost frequency weight time| ≤
          (constants.numerator + error) * time ^ 2 * (logarithm + 1) := by
      have heq : maskedPhase frequency weight strict cutoff time -
          position ^ 2 * phaseCost frequency weight time =
            (maskedPhase frequency weight strict cutoff time -
              alpha * time ^ 2 * (position * logarithm) ^ 2) +
              position ^ 2 * (alpha * time ^ 2 * logarithm ^ 2 -
                phaseCost frequency weight time) := by ring
      rw [heq]
      have htriangle := abs_add_le
        (maskedPhase frequency weight strict cutoff time - alpha * time ^ 2 * (position * logarithm) ^ 2)
        (position ^ 2 * (alpha * time ^ 2 * logarithm ^ 2 - phaseCost frequency weight time))
      rw [abs_mul, abs_of_nonneg hsquare.1, abs_sub_comm
        (alpha * time ^ 2 * logarithm ^ 2)] at htriangle
      exact (htriangle.trans (add_le_add hnumerator hphase_reduced)).trans_eq (by ring)
    have hpositivity := hpositive htime hthreshold
    have hdelta : 0 < phaseCost frequency weight time := hpositivity.2.trans_le hpositivity.1
    have hratio_scale : (constants.numerator + error) * time ^ 2 * (logarithm + 1) ≤
        constants.distributionError / logarithm * phaseCost frequency weight time := by
      have hcoefficient : 0 ≤ constants.numerator + error :=
        add_nonneg hconstants_nonneg.2.2.2.1 herror
      calc
        _ ≤ 2 * (constants.numerator + error) * time ^ 2 * logarithm := by
          have derivedEstimate := mul_le_mul_of_nonneg_left (by linarith : logarithm + 1 ≤ 2 * logarithm)
            (mul_nonneg hcoefficient (sq_nonneg time))
          nlinarith
        _ = constants.distributionError / logarithm * (alpha / 2 * time ^ 2 * logarithm ^ 2) := by
          change _ = (4 * (constants.numerator + error) / alpha) / logarithm * _
          field_simp
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpositivity.1
          (div_nonneg hconstants_nonneg.2.2.2.2 hlogpos.le)
    change |maskedPhase frequency weight strict cutoff time / phaseCost frequency weight time -
      position ^ 2| ≤ constants.distributionError / logarithm
    rw [show maskedPhase frequency weight strict cutoff time / phaseCost frequency weight time -
        position ^ 2 = (maskedPhase frequency weight strict cutoff time -
          position ^ 2 * phaseCost frequency weight time) / phaseCost frequency weight time by field_simp,
      abs_div, abs_of_pos hdelta]
    exact (div_le_iff₀ hdelta).mpr (hratio_numerator.trans hratio_scale)
  refine ⟨hall_moments, ?_, ?_⟩
  · intro time htime hthreshold
    exact ⟨(hpositive htime hthreshold).1, (hpositive htime hthreshold).2,
      fun strict position hposition => hdistribution htime hthreshold strict hposition⟩
  · have hobjects (time : ℝ) (hdelta : 0 < phaseCost frequency weight time) :
        (∃ discrete : PMF ι, ∀ index, discrete index = ENNReal.ofReal
          (2 * weight index * (1 - Real.cos (frequency index * time)) /
            phaseCost frequency weight time)) ∧
        ∃ chord : lp (fun _ : ι => ℂ) 2,
          (∀ index, chord index = chordCoordinate frequency weight time index) ∧ ‖chord‖ = 1 := by
      let mass := fun index => 2 * weight index * (1 - Real.cos (frequency index * time)) /
        phaseCost frequency weight time
      have hmass_nonneg (index : ι) : 0 ≤ mass index :=
        div_nonneg (hphase_nonneg time index) hdelta.le
      have hmass_sum : Summable mass := (hphase_sum time).div_const _
      have hmass_total : ∑' index, mass index = 1 := by
        rw [tsum_div_const]
        exact div_self hdelta.ne'
      have hmass_ennreal : HasSum (fun index => ENNReal.ofReal (mass index)) 1 := by
        apply ENNReal.summable.hasSum_iff.mpr
        rw [← ENNReal.ofReal_tsum_of_nonneg hmass_nonneg hmass_sum, hmass_total, ENNReal.ofReal_one]
      refine ⟨⟨⟨fun index => ENNReal.ofReal (mass index), hmass_ennreal⟩, fun _ => rfl⟩, ?_⟩
      have hchord_square (value : ℝ) :
          ‖Complex.exp (Complex.I * value) - 1‖ ^ 2 = 2 * (1 - Real.cos value) := by
        rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
          (by decide : Even (2 : ℕ)).pow_abs]
        have hdouble := Real.cos_two_mul (value / 2)
        rw [show 2 * (value / 2) = value by ring] at hdouble
        nlinarith only [hdouble, Real.sin_sq_add_cos_sq (value / 2)]
      have hnorm_square (index : ι) :
          ‖chordCoordinate frequency weight time index‖ ^ 2 = mass index := by
        dsimp only [chordCoordinate, mass]
        rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg (weight index)),
          abs_of_nonneg (Real.sqrt_nonneg (phaseCost frequency weight time)),
          div_pow, mul_pow, Real.sq_sqrt (hweight index), Real.sq_sqrt hdelta.le, hchord_square]
        ring
      have hraw_sum : Summable (fun index =>
          ‖chordCoordinate frequency weight time index‖ ^ (2 : ℕ)) :=
        hmass_sum.congr (fun index => (hnorm_square index).symm)
      have hraw_mem : Memℓp (chordCoordinate frequency weight time) 2 :=
        memℓp_gen (by simpa [Real.rpow_two] using hraw_sum)
      let chord : lp (fun _ : ι => ℂ) 2 := ⟨chordCoordinate frequency weight time, hraw_mem⟩
      have hnorm : ‖chord‖ ^ (2 : ℕ) = 1 := by
        have heq := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) chord
        norm_num [Real.rpow_two] at heq
        rw [heq]
        exact (tsum_congr hnorm_square).trans hmass_total
      exact ⟨chord, fun _ => rfl, by nlinarith [norm_nonneg chord]⟩
    have hdelta (time : ℝ) (htime : 0 < |time| ∧ |time| ≤ constants.firstTime) :
        0 < phaseCost frequency weight time :=
      (hpositive htime.1 htime.2).2.trans_le (hpositive htime.1 htime.2).1
    let probability : ℝ → ProbabilityMeasure ℝ := fun time =>
      if htime : 0 < |time| ∧ |time| ≤ constants.firstTime then
        spectralProbability (Classical.choose (hobjects time (hdelta time htime)).1)
          (fun index => Real.log (frequency index) / Real.log (1 / |time|))
      else betaTwoOne
    let chord : ℝ → lp (fun _ : ι => ℂ) 2 := fun time =>
      if htime : 0 < |time| ∧ |time| ≤ constants.firstTime then
        Classical.choose (hobjects time (hdelta time htime)).2
      else 0
    refine ⟨probability, chord, ?_, ?_⟩
    · intro time htime hthreshold
      have hnear : 0 < |time| ∧ |time| ≤ constants.firstTime := ⟨htime, hthreshold⟩
      simp only [probability, chord, dif_pos hnear]
      exact ⟨⟨Classical.choose (hobjects time (hdelta time hnear)).1,
        Classical.choose_spec (hobjects time (hdelta time hnear)).1, rfl⟩,
        (Classical.choose_spec (hobjects time (hdelta time hnear)).2).1,
        (Classical.choose_spec (hobjects time (hdelta time hnear)).2).2⟩
    · have hnear_event : ∀ᶠ time in 𝓝[≠] (0 : ℝ),
          0 < |time| ∧ |time| ≤ constants.firstTime := by
        have hthreshold : 0 < constants.firstTime := Real.exp_pos _
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hthreshold)] with time hne hball
        have htime : time ≠ 0 := by simpa using hne
        have hsmall_time : |time| < constants.firstTime := by
          simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hball
        exact ⟨abs_pos.mpr htime, hsmall_time.le⟩
      have hlog_limit : Tendsto (fun time : ℝ => Real.log (1 / |time|)) (𝓝[≠] 0) atTop := by
        simpa only [one_div, Real.log_inv, Real.log_abs, Function.comp_def] using
          tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero
      have hinverse_limit : Tendsto (fun time : ℝ => 1 / Real.log (1 / |time|))
          (𝓝[≠] 0) (𝓝 0) := by
        simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog_limit
      have hcoordinate (index : ι) : Tendsto (fun time => chord time index) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        let coefficient := Real.sqrt (weight index) * frequency index / Real.sqrt (alpha / 2)
        have hcoefficient : 0 ≤ coefficient := by
          dsimp only [coefficient]
          exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hfrequency index).le) (Real.sqrt_nonneg _)
        have hbound : ∀ᶠ time in 𝓝[≠] (0 : ℝ),
            ‖chord time index‖ ≤ coefficient / Real.log (1 / |time|) := hnear_event.mono (fun time hnear => by
          have hlogone : 1 ≤ Real.log (1 / |time|) :=
            ((le_max_left _ _).trans (le_max_left _ _)).trans (htime_log hnear.1 hnear.2)
          have hlogpos : 0 < Real.log (1 / |time|) := by linarith
          have hdelta_pos := hdelta time hnear
          have hsqrt_delta : 0 < Real.sqrt (phaseCost frequency weight time) := Real.sqrt_pos.mpr hdelta_pos
          have hsqrt_lower := Real.sqrt_le_sqrt (hpositive hnear.1 hnear.2).1
          rw [Real.sqrt_mul (mul_nonneg (div_nonneg halpha.le (by norm_num)) (sq_nonneg time)),
            Real.sqrt_mul (div_nonneg halpha.le (by norm_num)), Real.sqrt_sq_eq_abs,
            Real.sqrt_sq_eq_abs, abs_of_pos hlogpos] at hsqrt_lower
          have hformula : chord time index = chordCoordinate frequency weight time index := by
            simp only [chord, dif_pos hnear]
            exact (Classical.choose_spec (hobjects time (hdelta time hnear)).2).1 index
          rw [hformula]
          dsimp only [chordCoordinate]
          rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (Real.sqrt_nonneg _)]
          apply (div_le_iff₀ hsqrt_delta).mpr
          have hexp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := frequency index * time)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hfrequency index)] at hexp
          calc
            _ ≤ Real.sqrt (weight index) * (frequency index * |time|) :=
              mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
            _ = coefficient / Real.log (1 / |time|) *
                (Real.sqrt (alpha / 2) * |time| * Real.log (1 / |time|)) := by
              dsimp only [coefficient]
              field_simp [ne_of_gt (show 0 < Real.sqrt (alpha / 2) from
                Real.sqrt_pos.mpr (div_pos halpha (by norm_num))), hlogpos.ne']
            _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt_lower (div_nonneg hcoefficient hlogpos.le))
        have hnorm_limit : Tendsto (fun time => ‖chord time index‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
          squeeze_zero' (Eventually.of_forall (fun time => norm_nonneg (chord time index))) hbound
            (by simpa only [div_eq_mul_inv, one_div, mul_zero, one_mul] using hinverse_limit.const_mul coefficient)
        exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_limit
      have hnorm_bound : ∀ᶠ time in 𝓝[≠] (0 : ℝ), ‖chord time‖ ≤ 1 :=
        hnear_event.mono (fun time hnear => by
          simp only [chord, dif_pos hnear]
          exact (Classical.choose_spec (hobjects time (hdelta time hnear)).2).2.le)
      have hinner (vector : lp (fun _ : ι => ℂ) 2) :
          Tendsto (fun time => inner ℂ vector (chord time)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        apply Metric.tendsto_nhds.mpr
        intro tolerance htolerance
        have hsum_single := lp.hasSum_single (p := 2) (by simp) vector
        have hfinite_event : ∀ᶠ finite : Finset ι in (SummationFilter.unconditional ι).filter,
            ‖vector - ∑ index ∈ finite, lp.single 2 index (vector index)‖ < tolerance / 2 := by
          have derivedEstimate := hsum_single.eventually (Metric.ball_mem_nhds vector (by positivity : 0 < tolerance / 2))
          simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using derivedEstimate
        obtain ⟨finite, hfinite⟩ := hfinite_event.exists
        let approximation := ∑ index ∈ finite, lp.single 2 index (vector index)
        have hfinite_inner (time : ℝ) : inner ℂ approximation (chord time) =
            ∑ index ∈ finite, inner ℂ (vector index) (chord time index) := by
          dsimp only [approximation]
          rw [sum_inner]
          apply Finset.sum_congr rfl
          intro index _
          exact lp.inner_single_left (𝕜 := ℂ) index (vector index) (chord time)
        have hfinite_limit : Tendsto (fun time => inner ℂ approximation (chord time))
            (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
          have derivedEstimate := tendsto_finsetSum finite (fun index _ =>
            (Filter.Tendsto.inner (𝕜 := ℂ)
              (tendsto_const_nhds (x := vector index)) (hcoordinate index)))
          simpa only [hfinite_inner, inner_zero_right, Finset.sum_const_zero] using derivedEstimate
        have hfinite_small := hfinite_limit.eventually
          (Metric.ball_mem_nhds 0 (by positivity : 0 < tolerance / 2))
        filter_upwards [hfinite_small, hnorm_bound] with time hsmall_inner hnorm
        simp only [Metric.mem_ball, dist_zero_right] at hsmall_inner ⊢
        have htriangle : ‖inner ℂ vector (chord time)‖ ≤
            ‖inner ℂ approximation (chord time)‖ +
              ‖inner ℂ (vector - approximation) (chord time)‖ := by
          rw [show inner ℂ vector (chord time) = inner ℂ approximation (chord time) +
              inner ℂ (vector - approximation) (chord time) by rw [inner_sub_left]; ring]
          exact norm_add_le _ _
        have hcs := norm_inner_le_norm (𝕜 := ℂ) (vector - approximation) (chord time)
        have hbounded := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (vector - approximation))
        nlinarith
      have heval (functional : StrongDual ℂ (lp (fun _ : ι => ℂ) 2)) :
          Tendsto (fun time => functional (chord time)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        simpa only [InnerProductSpace.toDual_symm_apply] using
          hinner ((InnerProductSpace.toDual ℂ _).symm functional)
      have hweak : Tendsto (fun time => toWeakSpace ℂ _ (chord time)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        apply (WeakBilin.tendsto_iff_forall_eval_tendsto
          (topDualPairing ℂ (lp (fun _ : ι => ℂ) 2)).flip
          (separatingDual_iff_injective.mp inferInstance)).mpr
        intro functional
        change Tendsto (fun time => functional (chord time)) _ (𝓝 (functional 0))
        simpa only [map_zero] using heval functional
      suffices hprobability : Tendsto probability (𝓝[≠] (0 : ℝ)) (𝓝 betaTwoOne) by
        exact ⟨hprobability, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hprobability,
          hweak, heval⟩
      have hbeta (value : ℝ) : (betaTwoOne : Measure ℝ) (Iic value) =
          ENNReal.ofReal ((max 0 (min 1 value)) ^ 2) := by
        have hgamma2 : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
        have hgamma3 : Real.Gamma 3 = 2 := by simpa using Real.Gamma_nat_eq_factorial 2
        have hpdf (position : ℝ) : ProbabilityTheory.betaPDFReal 2 1 position =
            if 0 < position ∧ position < 1 then 2 * position else 0 := by
          simp only [ProbabilityTheory.betaPDFReal, ProbabilityTheory.beta]
          norm_num [hgamma2, hgamma3, Real.Gamma_one]
        have hpdf_function : ProbabilityTheory.betaPDF 2 1 =
            (Ioo (0 : ℝ) 1).indicator (fun position => ENNReal.ofReal (2 * position)) := by
          funext position
          rw [ProbabilityTheory.betaPDF, hpdf]
          by_cases hposition : 0 < position ∧ position < 1 <;> simp [Set.indicator, hposition]
        have hmeasure : (betaTwoOne : Measure ℝ) =
            (volume.restrict (Ioc (0 : ℝ) 1)).withDensity
              (fun position => ENNReal.ofReal (2 * position)) := by
          change ProbabilityTheory.betaMeasure 2 1 = _
          rw [ProbabilityTheory.betaMeasure, hpdf_function, withDensity_indicator measurableSet_Ioo,
            restrict_Ioo_eq_restrict_Ioc]
        rw [hmeasure, withDensity_apply _ measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioc_inter_Iic]
        change (∫⁻ position in Ioc 0 (min 1 value), ENNReal.ofReal (2 * position)) = _
        by_cases hnonneg : 0 ≤ min 1 value
        · rw [max_eq_right hnonneg]
          have hint : IntervalIntegrable (fun position : ℝ => 2 * position) volume 0 (min 1 value) :=
            (by fun_prop : Continuous _).intervalIntegrable _ _
          have hae : 0 ≤ᵐ[volume.restrict (Ioc 0 (min 1 value))] (fun position : ℝ => 2 * position) :=
            (ae_restrict_mem measurableSet_Ioc).mono (fun position hposition =>
              mul_nonneg (by norm_num) hposition.1.le)
          rw [← ofReal_integral_eq_lintegral_ofReal hint.1 hae,
            ← intervalIntegral.integral_of_le hnonneg, intervalIntegral.integral_const_mul, integral_id]
          congr 1
          ring
        · have hnonpos : min 1 value ≤ 0 := (not_le.mp hnonneg).le
          rw [max_eq_left hnonpos, Ioc_eq_empty (not_lt.mpr hnonpos)]
          simp
      let cdf := fun time value => (probability time : Measure ℝ).real (Iic value)
      have hcdf (time value : ℝ) (hnear : 0 < |time| ∧ |time| ≤ constants.firstTime) :
          cdf time value = maskedPhase frequency weight false
            (Real.exp (value * Real.log (1 / |time|))) time / phaseCost frequency weight time := by
        have hlogpos : 0 < Real.log (1 / |time|) := by
          have derivedEstimate := ((le_max_left _ _).trans (le_max_left _ _)).trans (htime_log hnear.1 hnear.2)
          linarith
        let discrete := Classical.choose (hobjects time (hdelta time hnear)).1
        have hmass := Classical.choose_spec (hobjects time (hdelta time hnear)).1
        have hcondition (index : ι) :
            Real.log (frequency index) / Real.log (1 / |time|) ≤ value ↔
              frequency index ≤ Real.exp (value * Real.log (1 / |time|)) :=
          (div_le_iff₀ hlogpos).trans (Real.log_le_iff_le_exp (hfrequency index))
        have hnonneg (index : ι) : 0 ≤
            (if lowCutoff frequency false (Real.exp (value * Real.log (1 / |time|))) index then
              2 * weight index * (1 - Real.cos (frequency index * time)) else 0) /
                phaseCost frequency weight time := by
          apply div_nonneg _ (hdelta time hnear).le
          split_ifs <;> first | exact hphase_nonneg time index | exact le_rfl
        have hmeasure : (probability time : Measure ℝ) (Iic value) = ENNReal.ofReal
            (maskedPhase frequency weight false (Real.exp (value * Real.log (1 / |time|))) time /
              phaseCost frequency weight time) := by
          change (↑(if htime : 0 < |time| ∧ |time| ≤ constants.firstTime then
            spectralProbability (Classical.choose (hobjects time (hdelta time htime)).1)
              (fun index => Real.log (frequency index) / Real.log (1 / |time|))
            else betaTwoOne) : Measure ℝ) (Iic value) = _
          rw [dif_pos hnear]
          change (discrete.map (fun index => Real.log (frequency index) / Real.log (1 / |time|))).toMeasure
            (Iic value) = _
          rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Iic,
            PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
          simp only [Set.indicator, Set.mem_preimage, Set.mem_Iic, hcondition]
          rw [show maskedPhase frequency weight false (Real.exp (value * Real.log (1 / |time|))) time /
              phaseCost frequency weight time = ∑' index,
                (if lowCutoff frequency false (Real.exp (value * Real.log (1 / |time|))) index then
                  2 * weight index * (1 - Real.cos (frequency index * time)) else 0) /
                    phaseCost frequency weight time by rw [maskedPhase, tsum_div_const]]
          rw [ENNReal.ofReal_tsum_of_nonneg hnonneg
            ((hmask_phase_sum false _ time).div_const _)]
          apply tsum_congr
          intro index
          simp only [lowCutoff, Bool.false_eq_true, if_false]
          split_ifs
          · exact hmass index
          · simp
        change ((probability time : Measure ℝ) (Iic value)).toReal = _
        rw [hmeasure, ENNReal.toReal_ofReal]
        simpa only [maskedPhase, tsum_div_const] using tsum_nonneg hnonneg
      have hcdf_nonneg (time value : ℝ) : 0 ≤ cdf time value := measureReal_nonneg
      have hcdf_one (time value : ℝ) : cdf time value ≤ 1 := by
        simpa only [probReal_univ] using
          (measureReal_mono (μ := (probability time : Measure ℝ)) (subset_univ (Iic value)))
      have hcdf_mono (time : ℝ) {left right : ℝ} (hle : left ≤ right) :
          cdf time left ≤ cdf time right := measureReal_mono (Iic_subset_Iic.mpr hle)
      have hcdf_interval (value : ℝ) (hvalue : value ∈ Icc (0 : ℝ) 1) :
          Tendsto (fun time => cdf time value) (𝓝[≠] (0 : ℝ)) (𝓝 (value ^ 2)) := by
        apply tendsto_iff_norm_sub_tendsto_zero.mpr
        have hbound : ∀ᶠ time in 𝓝[≠] (0 : ℝ), ‖cdf time value - value ^ 2‖ ≤
            constants.distributionError / Real.log (1 / |time|) :=
          hnear_event.mono (fun time hnear => by
            rw [Real.norm_eq_abs, hcdf time value hnear]
            exact hdistribution hnear.1 hnear.2 false hvalue)
        exact squeeze_zero' (Eventually.of_forall (fun time => norm_nonneg (cdf time value - value ^ 2)))
          hbound (by simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
            hinverse_limit.const_mul constants.distributionError)
      have hcdf_real (value : ℝ) : Tendsto (fun time => cdf time value) (𝓝[≠] (0 : ℝ))
          (𝓝 ((max 0 (min 1 value)) ^ 2)) := by
        by_cases hnonneg : 0 ≤ value
        · by_cases hone : value ≤ 1
          · simpa only [min_eq_right hone, max_eq_right hnonneg] using hcdf_interval value ⟨hnonneg, hone⟩
          · have hlarge : 1 ≤ value := (not_le.mp hone).le
            rw [min_eq_left hlarge, max_eq_right (by norm_num : (0 : ℝ) ≤ 1), one_pow]
            exact tendsto_of_tendsto_of_tendsto_of_le_of_le
              (by simpa using hcdf_interval 1 (by norm_num)) tendsto_const_nhds
              (fun time => hcdf_mono time hlarge) (fun time => hcdf_one time value)
        · have hsmall_value : value ≤ 0 := (not_le.mp hnonneg).le
          rw [min_eq_right (by linarith : value ≤ 1), max_eq_left hsmall_value, zero_pow (by norm_num)]
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
            (by simpa using hcdf_interval 0 (by norm_num))
            (fun time => hcdf_nonneg time value) (fun time => hcdf_mono time hsmall_value)
      have hcdf_ennreal (value : ℝ) :
          Tendsto (fun time => (probability time : Measure ℝ) (Iic value)) (𝓝[≠] (0 : ℝ))
            (𝓝 ((betaTwoOne : Measure ℝ) (Iic value))) := by
        rw [hbeta]
        convert ENNReal.tendsto_ofReal (hcdf_real value) using 1
        funext time
        exact (ENNReal.ofReal_toReal (by finiteness)).symm
      refine (isPiSystem_Ioc (id : ℝ → ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
      · rintro interval ⟨left, right, hlt, rfl⟩
        exact measurableSet_Ioc
      · intro neighborhood hopen point hpoint
        rcases mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds hpoint) with
          ⟨left, right, ⟨hleft, hright⟩, hsubset⟩
        let midpoint := (point + right) / 2
        have hpoint_mid : point < midpoint := by dsimp [midpoint]; linarith
        have hmid_right : midpoint < right := by dsimp [midpoint]; linarith
        exact ⟨Ioc left midpoint, ⟨left, midpoint, hleft.trans hpoint_mid, rfl⟩,
          Ioc_mem_nhds hleft hpoint_mid, (Ioc_subset_Ioo_right hmid_right).trans hsubset⟩
      · rintro interval ⟨left, right, hlt, rfl⟩
        simp only [id_eq] at hlt ⊢
        have hsub := ENNReal.Tendsto.sub (hcdf_ennreal right) (hcdf_ennreal left)
          (Or.inl (by finiteness : (betaTwoOne : Measure ℝ) (Iic right) ≠ ∞))
        have hsubNN := (ENNReal.tendsto_toNNReal (by finiteness :
          (betaTwoOne : Measure ℝ) (Iic right) - (betaTwoOne : Measure ℝ) (Iic left) ≠ ∞)).comp hsub
        have hsource : (fun time => probability time (Ioc left right)) =
            fun time => ((probability time : Measure ℝ) (Iic right) -
              (probability time : Measure ℝ) (Iic left)).toNNReal := by
          funext time
          change ((probability time : Measure ℝ) (Ioc left right)).toNNReal = _
          rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hlt.le) nullMeasurableSet_Iic]
          finiteness
        have htarget : betaTwoOne (Ioc left right) =
            ((betaTwoOne : Measure ℝ) (Iic right) - (betaTwoOne : Measure ℝ) (Iic left)).toNNReal := by
          change ((betaTwoOne : Measure ℝ) (Ioc left right)).toNNReal = _
          rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hlt.le) nullMeasurableSet_Iic]
          finiteness
        rw [hsource, htarget]
        exact hsubNN

#print axioms phase_law_spectral_escape

end

end D5.S3.Analytic.Asymptotics.PhaseLawSpectralEscape
