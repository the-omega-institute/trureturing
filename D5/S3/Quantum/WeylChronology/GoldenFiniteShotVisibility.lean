/- GID: D5/S3/Quantum/WeylChronology/GoldenFiniteShotVisibility
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-finite-probability-identities)
   anchors: []
   digest: Ramsey contrast turns golden chronology into the frozen symmetric Bernoulli law, with exact kernels, variation, affinity, and finite-shot testing floors. -/

import D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
import D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms
import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData
import D5.S3.Estimation.ErrorExponents.FiniteRepetitionLawKernel

/-!
# Visibility and finite-shot golden chronology readout

This module is deliberately an adapter. It introduces no second Bernoulli,
total-variation, Bhattacharyya, iid-power, or testing-error theory. The one-shot
outcome law is the frozen `positiveBiasLaw`; exact TV and affinity are imported
from `FourLocalEvidenceClosedForms`; finite repetition and testing floors are
imported from the estimation lane.

The physical parameter `visibility` is the Ramsey fringe contrast in the
standard phenomenological law `(1 + V sin phase) / 2`. Contrast-damped Ramsey
fringes are standard experimentally. For example, Ramsey data are routinely
fit with an offset plus contrast times a sinusoid; trapped-ion experiments also
report state-population confidence intervals under binomial statistics.

The exact bridge is

`signal = V * sin(2*kappa*m(word))`,
`bias = signal / 2`,
`law = positiveBiasLaw bias`.

At zero visibility every word has the same law. At positive visibility and in
the already-proved no-alias band, the one-shot law kernel is exactly the Magnus
center kernel. The frozen finite-repetition theorem then proves that every
positive finite number of independent shots has exactly that same equality
kernel: repetition amplifies statistical separation but cannot cross a
one-shot collision.

For a word and its reversal the two laws are the frozen symmetric `+bias` and
`-bias` pair. Therefore their one-shot total variation is exactly `|signal|`,
and, for visibility strictly below one, their Bhattacharyya affinity is exactly
`sqrt (1 - signal^2)`. The existing iid testing theorem then gives the explicit
necessary finite-shot error floor `(1 - signal^2)^N / 2` and its sample-count
product consequence.

These are probability-level limits. A finite experiment observes samples, not
the exact law. The module assumes independent repeated shots and a calibrated
contrast. It does not model contrast uncertainty, additive readout offset,
correlated drift, residual endpoint displacement, or a constructive optimal
decision rule. It also does not import the unmerged Fourier-Magnus matrix draft
#4504; that draft remains the adjacent noncommutative interpretation layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility

open D5.S1.Words
open D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
open D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData
open D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Metric
open D5.S3.RenyiDivergence
open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.Estimation.BhattacharyyaExponent
open D5.S3.Estimation.ErrorExponents.FiniteRepetitionLawKernel

noncomputable section

/-- Contrast-weighted sine signal of the calibrated chronology phase. -/
def visibilitySignal (visibility kappa : ℝ) (word : List Bool) : ℝ :=
  visibility * Real.sin (2 * kappa * (magnusCenter word : ℝ))

/-- The observed plus-port probability after contrast loss and with no additive offset. -/
def visibleChronologyFringe (visibility kappa : ℝ) (word : List Bool) : ℝ :=
  (1 + visibilitySignal visibility kappa word) / 2

/-- Bias relative to one half. This is the exact parameter of the frozen symmetric Bernoulli law. -/
def chronologyBias (visibility kappa : ℝ) (word : List Bool) : ℝ :=
  visibilitySignal visibility kappa word / 2

/-- One finite Ramsey shot, represented by the repository's canonical two-point bias law. -/
def visibleChronologyLaw (visibility kappa : ℝ) (word : List Bool) : Bool → ℝ :=
  positiveBiasLaw (chronologyBias visibility kappa word)

/-- The contrast model is exactly the affine damping of the previously frozen ideal fringe. -/
theorem visible_chronology_fringe_eq_affine_ideal
    (visibility kappa : ℝ) (word : List Bool) :
    visibleChronologyFringe visibility kappa word =
      (1 - visibility) / 2 + visibility * chronologyFringe kappa word := by
  unfold visibleChronologyFringe visibilitySignal chronologyFringe
  rw [plus_probability_formula, Real.cos_sub_pi_div_two]
  ring

/-- The `true` mass of the canonical Bool law is the visible plus-port probability. -/
theorem visible_chronology_law_true
    (visibility kappa : ℝ) (word : List Bool) :
    visibleChronologyLaw visibility kappa word true =
      visibleChronologyFringe visibility kappa word := by
  simp [visibleChronologyLaw, chronologyBias, visibleChronologyFringe,
    positiveBiasLaw]
  ring

private theorem visibility_signal_abs_le_one
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility ≤ 1) :
    |visibilitySignal visibility kappa word| ≤ 1 := by
  have hsin :
      |Real.sin (2 * kappa * (magnusCenter word : ℝ))| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  rw [visibilitySignal, abs_mul, abs_of_nonneg hvisibility_nonneg]
  calc
    visibility * |Real.sin (2 * kappa * (magnusCenter word : ℝ))| ≤
        visibility * 1 := mul_le_mul_of_nonneg_left hsin hvisibility_nonneg
    _ ≤ 1 := by simpa using hvisibility_one

private theorem visibility_signal_abs_lt_one
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1) :
    |visibilitySignal visibility kappa word| < 1 := by
  have hsin :
      |Real.sin (2 * kappa * (magnusCenter word : ℝ))| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  rw [visibilitySignal, abs_mul, abs_of_nonneg hvisibility_nonneg]
  calc
    visibility * |Real.sin (2 * kappa * (magnusCenter word : ℝ))| ≤
        visibility * 1 := mul_le_mul_of_nonneg_left hsin hvisibility_nonneg
    _ < 1 := by simpa using hvisibility_one

private theorem chronology_bias_abs_le_half
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility ≤ 1) :
    |chronologyBias visibility kappa word| ≤ 1 / 2 := by
  have hsignal := visibility_signal_abs_le_one visibility kappa word
    hvisibility_nonneg hvisibility_one
  rw [chronologyBias, abs_div]
  norm_num
  nlinarith

private theorem chronology_bias_abs_lt_half
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1) :
    |chronologyBias visibility kappa word| < 1 / 2 := by
  have hsignal := visibility_signal_abs_lt_one visibility kappa word
    hvisibility_nonneg hvisibility_one
  rw [chronologyBias, abs_div]
  norm_num
  nlinarith

/-- On the physical contrast range, the visible one-shot law is honest probability data. -/
theorem visible_chronology_probability_data
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility ≤ 1) :
    (∀ b, 0 ≤ visibleChronologyLaw visibility kappa word b) ∧
      ∑ b, visibleChronologyLaw visibility kappa word b = 1 := by
  have hdata :=
    (bias_laws_probability_data
      (chronology_bias_abs_le_half visibility kappa word
        hvisibility_nonneg hvisibility_one)).1
  simpa [visibleChronologyLaw] using hdata

private theorem visibility_signal_reverse
    (visibility kappa : ℝ) (word : List Bool) :
    visibilitySignal visibility kappa word.reverse =
      -visibilitySignal visibility kappa word := by
  unfold visibilitySignal
  rw [magnus_center_reverse]
  simp only [Int.cast_neg]
  have hangle :
      2 * kappa * (-(magnusCenter word : ℝ)) =
        -(2 * kappa * (magnusCenter word : ℝ)) := by ring
  rw [hangle, Real.sin_neg]
  ring

private theorem chronology_bias_reverse
    (visibility kappa : ℝ) (word : List Bool) :
    chronologyBias visibility kappa word.reverse =
      -chronologyBias visibility kappa word := by
  rw [chronologyBias, visibility_signal_reverse]
  ring

private theorem visible_chronology_reverse_law
    (visibility kappa : ℝ) (word : List Bool) :
    visibleChronologyLaw visibility kappa word.reverse =
      negativeBiasLaw (chronologyBias visibility kappa word) := by
  unfold visibleChronologyLaw
  rw [chronology_bias_reverse]
  funext b
  cases b <;> simp [positiveBiasLaw, negativeBiasLaw]

/-- Zero contrast erases every chronology channel already at the one-shot law level. -/
theorem zero_visibility_law_collapse
    (kappa : ℝ) (left right : List Bool) :
    visibleChronologyLaw 0 kappa left = visibleChronologyLaw 0 kappa right := by
  simp [visibleChronologyLaw, chronologyBias, visibilitySignal]

/-- Positive visibility preserves the already-proved calibrated Magnus-center kernel. -/
theorem positive_visibility_law_kernel
    (visibility kappa : ℝ)
    (hvisibility : 0 < visibility) (hkappa : kappa ≠ 0)
    (left right : List Bool)
    (hleft : |kappa| * (left.length : ℝ) ^ 2 ≤ Real.pi)
    (hright : |kappa| * (right.length : ℝ) ^ 2 ≤ Real.pi) :
    visibleChronologyLaw visibility kappa left =
        visibleChronologyLaw visibility kappa right ↔
      magnusCenter left = magnusCenter right := by
  constructor
  · intro hlaw
    have htrue := congrFun hlaw true
    have hbias :
        chronologyBias visibility kappa left =
          chronologyBias visibility kappa right := by
      simpa [visibleChronologyLaw, positiveBiasLaw] using htrue
    have hsignal :
        visibilitySignal visibility kappa left =
          visibilitySignal visibility kappa right := by
      unfold chronologyBias at hbias
      linarith
    have hvisible :
        visibleChronologyFringe visibility kappa left =
          visibleChronologyFringe visibility kappa right := by
      unfold visibleChronologyFringe
      linarith
    rw [visible_chronology_fringe_eq_affine_ideal,
      visible_chronology_fringe_eq_affine_ideal] at hvisible
    have hscaled :
        visibility * chronologyFringe kappa left =
          visibility * chronologyFringe kappa right := by
      linarith
    have hfringe : chronologyFringe kappa left = chronologyFringe kappa right :=
      mul_left_cancel₀ hvisibility.ne' hscaled
    exact (chronology_fringe_kernel kappa hkappa left right hleft hright).mp hfringe
  · intro hcenter
    have hfringe :=
      (chronology_fringe_kernel kappa hkappa left right hleft hright).mpr hcenter
    simp [visibleChronologyLaw, chronologyBias, visibilitySignal, hcenter]

/-- Every positive finite number of independent shots has the same equality kernel as one shot.
Repetition may amplify separation, but it cannot recover information lost by the one-shot law. -/
theorem positive_repetition_law_kernel
    (visibility kappa : ℝ)
    (hvisibility : 0 < visibility) (hvisibility_one : visibility ≤ 1)
    (hkappa : kappa ≠ 0)
    (left right : List Bool)
    (hleft : |kappa| * (left.length : ℝ) ^ 2 ≤ Real.pi)
    (hright : |kappa| * (right.length : ℝ) ^ 2 ≤ Real.pi)
    (shots : ℕ) (hshots : 0 < shots) :
    iidPower (visibleChronologyLaw visibility kappa left) shots =
        iidPower (visibleChronologyLaw visibility kappa right) shots ↔
      magnusCenter left = magnusCenter right := by
  have hleftData := visible_chronology_probability_data
    visibility kappa left hvisibility.le hvisibility_one
  have hrightData := visible_chronology_probability_data
    visibility kappa right hvisibility.le hvisibility_one
  have hrepetition :=
    (finite_repetition_amplifies_without_crossing_law_kernel
      (law := fun word : List Bool => visibleChronologyLaw visibility kappa word)
      left right shots hleftData hrightData hshots).2
  exact hrepetition.trans
    (positive_visibility_law_kernel visibility kappa hvisibility hkappa
      left right hleft hright)

/-- For a chronology and its reversal, one-shot total variation is exactly the absolute
contrast-weighted sine signal. -/
theorem word_reverse_total_variation
    (visibility kappa : ℝ) (word : List Bool) :
    totalVariation
        (visibleChronologyLaw visibility kappa word)
        (visibleChronologyLaw visibility kappa word.reverse) =
      |visibilitySignal visibility kappa word| := by
  rw [visible_chronology_reverse_law]
  change totalVariation
      (positiveBiasLaw (chronologyBias visibility kappa word))
      (negativeBiasLaw (chronologyBias visibility kappa word)) = _
  rw [total_variation_closed_form]
  unfold chronologyBias
  rw [abs_div]
  norm_num
  ring

/-- For nonsaturated visibility, reversal affinity has an exact closed form in the physical
contrast-weighted signal. -/
theorem word_reverse_bhattacharyya
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1) :
    bhattacharyya
        (visibleChronologyLaw visibility kappa word)
        (visibleChronologyLaw visibility kappa word.reverse) =
      Real.sqrt (1 - visibilitySignal visibility kappa word ^ 2) := by
  rw [visible_chronology_reverse_law]
  change bhattacharyya
      (positiveBiasLaw (chronologyBias visibility kappa word))
      (negativeBiasLaw (chronologyBias visibility kappa word)) = _
  rw [bhattacharyya_closed_form
    (chronology_bias_abs_lt_half visibility kappa word
      hvisibility_nonneg hvisibility_one)]
  unfold chronologyBias
  congr 1
  ring

private theorem visibility_signal_square_lt_one
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1) :
    visibilitySignal visibility kappa word ^ 2 < 1 := by
  have habs := visibility_signal_abs_lt_one visibility kappa word
    hvisibility_nonneg hvisibility_one
  have hsquare :
      |visibilitySignal visibility kappa word| ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).2 habs
  simpa [sq_abs] using hsquare

/-- No arbitrary decision event on `shots` independent Ramsey outcomes beats this explicit
Bhattacharyya testing floor for distinguishing a word from its reversal. -/
theorem word_reverse_iid_testing_error_floor
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1)
    (shots : ℕ) (decision : Finset (IidSpace Bool shots)) :
    (1 - visibilitySignal visibility kappa word ^ 2) ^ shots / 2 ≤
      (∑ z ∈ decision,
          iidPower (visibleChronologyLaw visibility kappa word) shots z) +
        ∑ z ∈ decisionᶜ,
          iidPower (visibleChronologyLaw visibility kappa word.reverse) shots z := by
  have hleftData := visible_chronology_probability_data
    visibility kappa word hvisibility_nonneg hvisibility_one.le
  have hrightData := visible_chronology_probability_data
    visibility kappa word.reverse hvisibility_nonneg hvisibility_one.le
  have hbound := iid_testing_error_bhattacharyya
    (visibleChronologyLaw visibility kappa word)
    (visibleChronologyLaw visibility kappa word.reverse)
    shots decision hleftData hrightData
  rw [word_reverse_bhattacharyya visibility kappa word
    hvisibility_nonneg hvisibility_one] at hbound
  have hrad : 0 ≤ 1 - visibilitySignal visibility kappa word ^ 2 := by
    have hsquare := visibility_signal_square_lt_one visibility kappa word
      hvisibility_nonneg hvisibility_one
    linarith
  have hpower :
      (Real.sqrt (1 - visibilitySignal visibility kappa word ^ 2)) ^ (2 * shots) =
        (1 - visibilitySignal visibility kappa word ^ 2) ^ shots := by
    rw [pow_mul, Real.sq_sqrt hrad]
  rw [hpower] at hbound
  exact hbound

/-- Any test whose total two-hypothesis error is at most `eps` must satisfy this exact
product-form shot requirement. This is a necessary condition, not an upper-bound algorithm. -/
theorem word_reverse_sample_complexity_product
    (visibility kappa : ℝ) (word : List Bool)
    (hvisibility_nonneg : 0 ≤ visibility) (hvisibility_one : visibility < 1)
    (shots : ℕ) (decision : Finset (IidSpace Bool shots)) (eps : ℝ)
    (herror :
      (∑ z ∈ decision,
          iidPower (visibleChronologyLaw visibility kappa word) shots z) +
        ∑ z ∈ decisionᶜ,
          iidPower (visibleChronologyLaw visibility kappa word.reverse) shots z ≤ eps) :
    (1 - visibilitySignal visibility kappa word ^ 2) ^ shots ≤ 2 * eps := by
  have hleftData := visible_chronology_probability_data
    visibility kappa word hvisibility_nonneg hvisibility_one.le
  have hrightData := visible_chronology_probability_data
    visibility kappa word.reverse hvisibility_nonneg hvisibility_one.le
  have hbound := bhattacharyya_sample_complexity_product
    (visibleChronologyLaw visibility kappa word)
    (visibleChronologyLaw visibility kappa word.reverse)
    shots decision eps hleftData hrightData herror
  rw [word_reverse_bhattacharyya visibility kappa word
    hvisibility_nonneg hvisibility_one] at hbound
  have hrad : 0 ≤ 1 - visibilitySignal visibility kappa word ^ 2 := by
    have hsquare := visibility_signal_square_lt_one visibility kappa word
      hvisibility_nonneg hvisibility_one
    linarith
  have hpower :
      (Real.sqrt (1 - visibilitySignal visibility kappa word ^ 2)) ^ (2 * shots) =
        (1 - visibilitySignal visibility kappa word ^ 2) ^ shots := by
    rw [pow_mul, Real.sq_sqrt hrad]
  rw [hpower] at hbound
  exact hbound

#print axioms visible_chronology_fringe_eq_affine_ideal
#print axioms visible_chronology_law_true
#print axioms visible_chronology_probability_data
#print axioms zero_visibility_law_collapse
#print axioms positive_visibility_law_kernel
#print axioms positive_repetition_law_kernel
#print axioms word_reverse_total_variation
#print axioms word_reverse_bhattacharyya
#print axioms word_reverse_iid_testing_error_floor
#print axioms word_reverse_sample_complexity_product

end
end D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
