/- GID: D5/S3/Quantum/WeylChronology/GoldenInterferometricRecovery
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-range-and-kernel-proofs)
   anchors: []
   digest: A calibrated sine fringe faithfully reads bounded Magnus centers and legal golden factors. -/

import D5.S3.Quantum.WeylChronology.GoldenWordInterferometry

/-!
# Range-safe interferometric recovery

The observable is the normalized plus-port probability already derived from
concrete split-path displacement amplitudes. Coupling kappa means a*b, so
word versus reversal gives phase 2*kappa*m. The integer bound 4*abs(m)<=n^2
makes abs(kappa)*n^2<=pi a sufficient no-alias condition for a pi/2 analyzer.

This proves an exact probability-level recovery statement, not recovery from
one Bernoulli sample. Coupling noise, estimator confidence, imperfect path
closure, loss, and readout visibility are not silently assumed away in a
claimed experiment: they are absent from this explicit ideal model.

The coupling/range tradeoff is discussed in Razian et al.,
arXiv:2604.06565v1. The two-setting readout is implemented experimentally in
Fluehmann and Home, PRL 125,043602 (2020). The quantitative sufficient bound
here is derived for the repository's word coordinate, not copied as a claimed
bound or experiment from either paper. No quantum advantage is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery

open MeasureTheory
open D5.S1.Words
open D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
open D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

noncomputable section

/-- The actual sine-analyzer fringe for the word/reversal interferometer. -/
def chronologyFringe (κ : ℝ) (word : List Bool) : ℝ :=
  plusProbability (Real.pi / 2) (2 * κ * (magnusCenter word : ℝ))

/-- The endpoint-compensated device is the same calibrated fringe with
coupling ab/2. This connects the recovery theorem to a count-only reference. -/
theorem compensated_probability_eq_chronology_fringe (a b : ℝ) (word : List Bool)
    (f : ℝ → ℂ) (hnorm : (∫ q : ℝ, Complex.normSq (f q)) = 1) :
    (∫ q : ℝ, Complex.normSq
      (compensatedPlusOutput (Real.pi / 2) a b word f q)) =
      chronologyFringe (a * b / 2) word := by
  rw [normalized_compensated_probability (Real.pi / 2) a b word f hnorm]
  unfold chronologyFringe
  congr 1
  ring

/-- The centered pair coordinate cannot exceed all pairs of unlike letters. -/
theorem center_absolute_bound (word : List Bool) :
    |(magnusCenter word : ℝ)| ≤ (word.count true : ℝ) * (word.count false : ℝ) := by
  have hpair : (scatteredTrueFalseCount word : ℝ) +
      (scatteredTrueFalseCount word.reverse : ℝ) =
      (word.count true : ℝ) * (word.count false : ℝ) := by
    exact_mod_cast scattered_pair_reversal_sum word
  have hp : (0 : ℝ) ≤ scatteredTrueFalseCount word := by positivity
  have hq : (0 : ℝ) ≤ scatteredTrueFalseCount word.reverse := by positivity
  have hm : (magnusCenter word : ℝ) =
      2 * (scatteredTrueFalseCount word : ℝ) -
        (word.count true : ℝ) * (word.count false : ℝ) := by
    exact_mod_cast magnus_center_formula word
  rw [hm, abs_le]
  constructor <;> linarith

/-- A word-length-only calibration bound, valid for every binary word. -/
theorem center_length_bound (word : List Bool) :
    4 * |(magnusCenter word : ℝ)| ≤ (word.length : ℝ) ^ 2 := by
  have hc := center_absolute_bound word
  have hlength : (word.count true : ℝ) + (word.count false : ℝ) = word.length := by
    exact_mod_cast binary_letter_counts_length word
  nlinarith [sq_nonneg ((word.count true : ℝ) - (word.count false : ℝ))]

/-- The sufficient window calibration places the full relative phase in one
monotone sine band. The factor two comes from comparing reversal arms. -/
theorem relative_phase_in_sine_band (κ : ℝ) (word : List Bool)
    (hcal : |κ| * (word.length : ℝ) ^ 2 ≤ Real.pi) :
    |2 * κ * (magnusCenter word : ℝ)| ≤ Real.pi / 2 := by
  have hbound := mul_le_mul_of_nonneg_left (center_length_bound word) (abs_nonneg κ)
  simp only [abs_mul, abs_ofNat]
  nlinarith

/-- In the calibrated window the physical fringe and the integer center have
exactly the same indistinguishability kernel. -/
theorem chronology_fringe_kernel (κ : ℝ) (hκ : κ ≠ 0) (left right : List Bool)
    (hleft : |κ| * (left.length : ℝ) ^ 2 ≤ Real.pi)
    (hright : |κ| * (right.length : ℝ) ^ 2 ≤ Real.pi) :
    chronologyFringe κ left = chronologyFringe κ right ↔
      magnusCenter left = magnusCenter right := by
  constructor
  · intro h
    have hphase := sine_analyzer_injective_on_band
      (2 * κ * (magnusCenter left : ℝ)) (2 * κ * (magnusCenter right : ℝ))
      (relative_phase_in_sine_band κ left hleft)
      (relative_phase_in_sine_band κ right hright) h
    have hm : (magnusCenter left : ℝ) = (magnusCenter right : ℝ) :=
      mul_left_cancel₀ (mul_ne_zero (by norm_num) hκ) hphase
    exact_mod_cast hm
  · intro h
    simp only [chronologyFringe, h]

/-- One conservative nonzero coupling, explicit for every finite window length. -/
def safeCoupling (n : ℕ) : ℝ := Real.pi / (2 * ((n : ℝ) + 1) ^ 2)

/-- The conservative choice satisfies both the nonzero and the range obligations. -/
theorem safe_coupling_calibrated (n : ℕ) :
    0 < safeCoupling n ∧ |safeCoupling n| * (n : ℝ) ^ 2 ≤ Real.pi := by
  have hpos : 0 < safeCoupling n := by unfold safeCoupling; positivity
  refine ⟨hpos, ?_⟩
  rw [abs_of_pos hpos]
  unfold safeCoupling
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 2)).mpr
  have hn : (0 : ℝ) ≤ n := by positivity
  exact mul_le_mul_of_nonneg_left (by nlinarith : (n : ℝ) ^ 2 ≤
    2 * ((n : ℝ) + 1) ^ 2) Real.pi_pos.le

/-- For a known length and count, one calibrated fringe recovers a legal
consecutive golden factor, while absolute occurrence positions remain hidden. -/
theorem golden_factor_recovered_by_count_and_fringe (κ : ℝ) (n i j : ℕ)
    (hκ : κ ≠ 0) (hcal : |κ| * (n : ℝ) ^ 2 ≤ Real.pi)
    (hcount : goldenWindowTrueCount i n = goldenWindowTrueCount j n)
    (hfringe : chronologyFringe κ (goldenFactor n i) =
      chronologyFringe κ (goldenFactor n j)) : goldenFactor n i = goldenFactor n j := by
  apply golden_factor_eq_of_count_and_center n i j hcount
  apply (chronology_fringe_kernel κ hκ (goldenFactor n i) (goldenFactor n j)
    (by simpa [goldenFactor] using hcal) (by simpa [goldenFactor] using hcal)).mp
  exact hfringe

/-- At even length the legal-language parity theorem removes the extra count. -/
theorem even_golden_factor_recovered_by_fringe (κ : ℝ) (n i j : ℕ)
    (hn : Even n) (hκ : κ ≠ 0) (hcal : |κ| * (n : ℝ) ^ 2 ≤ Real.pi)
    (hfringe : chronologyFringe κ (goldenFactor n i) =
      chronologyFringe κ (goldenFactor n j)) : goldenFactor n i = goldenFactor n j := by
  apply even_length_center_recovers_golden_factor n hn i j
  exact (chronology_fringe_kernel κ hκ (goldenFactor n i) (goldenFactor n j)
    (by simpa [goldenFactor] using hcal) (by simpa [goldenFactor] using hcal)).mp hfringe

/-- A directly usable setting: its range and nonzero coupling obligations are
proved, rather than left to a future experimenter as an injectivity premise. -/
theorem even_golden_factor_recovered_at_safe_setting (n i j : ℕ) (hn : Even n)
    (hfringe : chronologyFringe (safeCoupling n) (goldenFactor n i) =
      chronologyFringe (safeCoupling n) (goldenFactor n j)) :
    goldenFactor n i = goldenFactor n j := by
  have hc := safe_coupling_calibrated n
  exact even_golden_factor_recovered_by_fringe (safeCoupling n) n i j hn
    hc.1.ne' hc.2 hfringe

/-- Physical translation does not erase the mathematical odd-length collision:
two different legal factors yield the same fringe for every coupling. -/
theorem odd_golden_fringe_collision (n : ℕ) (hn : Odd n) :
    ∃ i j : ℕ, goldenFactor n i ≠ goldenFactor n j ∧
      ∀ κ : ℝ, chronologyFringe κ (goldenFactor n i) =
        chronologyFringe κ (goldenFactor n j) := by
  obtain ⟨i, j, hne, hi, hj⟩ := odd_length_center_collision n hn
  refine ⟨i, j, hne, ?_⟩
  intro κ
  simp only [chronologyFringe, hi, hj]

/-- Palindromes have the balanced sine fringe at any coupling. The converse
requires both a legal-language theorem and a no-alias premise. -/
theorem palindrome_fringe_half (κ : ℝ) (word : List Bool)
    (hpal : word.reverse = word) : chronologyFringe κ word = 1 / 2 := by
  rw [chronologyFringe, magnus_center_zero_of_reverse_eq word hpal]
  simp [plus_probability_formula, Real.cos_sub_pi_div_two]

#print axioms compensated_probability_eq_chronology_fringe
#print axioms center_length_bound
#print axioms chronology_fringe_kernel
#print axioms safe_coupling_calibrated
#print axioms golden_factor_recovered_by_count_and_fringe
#print axioms even_golden_factor_recovered_by_fringe
#print axioms even_golden_factor_recovered_at_safe_setting
#print axioms odd_golden_fringe_collision

end
end D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
