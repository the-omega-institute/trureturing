/- GID: D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove TV, affinity, Hellinger, and KL forms with zero, negative, and boundary audits. -/

/- Library-search audit trail (2026-08-26):
   * Searched the pinned repository for totalVariation, bhattacharyya, hellingerSq,
     and klDivergence.
   * Found the finite definitions, Bool sum lemmas, and the normalized Hellinger bridge.
   * No public replacement for the frozen private affinity proof was found; it is reproved here.
-/

import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

noncomputable section

/-- Total variation uses the repository's half-L1 normalization; this identity is algebraic for
all real deltas, while the probability interpretation is restricted to `|delta| < 1 / 2`. -/
theorem total_variation_closed_form (delta : Real) :
    totalVariation (positiveBiasLaw delta) (negativeBiasLaw delta) = 2 * |delta| := by
  rw [totalVariation, Fintype.sum_bool]
  simp only [positiveBiasLaw, negativeBiasLaw, Bool.false_eq_true, ↓reduceIte]
  have hfirst : 1 / 2 + delta - (1 / 2 - delta) = 2 * delta := by ring
  have hsecond : 1 / 2 - delta - (1 / 2 + delta) = -(2 * delta) := by ring
  rw [hfirst, hsecond, abs_neg]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  ring

#print axioms total_variation_closed_form

private theorem bias_laws_probability_data {delta : Real} (hdelta : |delta| < 1 / 2) :
    ((forall b, 0 <= positiveBiasLaw delta b) /\
      ∑ b, positiveBiasLaw delta b = 1) /\
    ((forall b, 0 <= negativeBiasLaw delta b) /\
      ∑ b, negativeBiasLaw delta b = 1) := by
  have hlower : 0 <= 1 / 2 - delta := by
    rw [abs_lt] at hdelta
    linarith
  have hupper : 0 <= 1 / 2 + delta := by
    rw [abs_lt] at hdelta
    linarith
  constructor <;> constructor
  · intro b
    cases b <;> simp only [positiveBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
      linarith
  · norm_num [positiveBiasLaw, Fintype.sum_bool]
  · intro b
    cases b <;> simp only [negativeBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
      linarith
  · norm_num [negativeBiasLaw, Fintype.sum_bool]

/-- The symbol `rho` is read as Bhattacharyya affinity, not a correlation coefficient. -/
theorem bhattacharyya_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta) =
      Real.sqrt (1 - 4 * delta ^ 2) := by
  have hplus : 0 <= 1 / 2 + delta := by
    rw [abs_lt] at hdelta
    linarith
  have hminus : 0 <= 1 / 2 - delta := by
    rw [abs_lt] at hdelta
    linarith
  have hproduct : 0 <= (1 / 2 + delta) * (1 / 2 - delta) :=
    mul_nonneg hplus hminus
  have hradicand : 0 <= 1 - 4 * delta ^ 2 := by
    nlinarith [sq_nonneg (|delta|), sq_abs delta]
  rw [bhattacharyya]
  simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  have hsame :
      (1 / 2 - delta) * (1 / 2 + delta) =
        (1 / 2 + delta) * (1 / 2 - delta) := by ring
  rw [hsame]
  have hsquare :
      (2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta))) ^ 2 =
        (Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
    calc
      (2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta))) ^ 2 =
          4 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta)) ^ 2 := by ring
      _ = 4 * ((1 / 2 + delta) * (1 / 2 - delta)) := by
        rw [Real.sq_sqrt hproduct]
      _ = 1 - 4 * delta ^ 2 := by ring
      _ = (Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt hradicand]
  have hleft : 0 <= 2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta)) := by positivity
  have hright : 0 <= Real.sqrt (1 - 4 * delta ^ 2) := Real.sqrt_nonneg _
  nlinarith

#print axioms bhattacharyya_closed_form

theorem hellinger_sq_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    hellingerSq (positiveBiasLaw delta) (negativeBiasLaw delta) =
      2 * (1 - Real.sqrt (1 - 4 * delta ^ 2)) := by
  obtain ⟨hpositive, hnegative⟩ := bias_laws_probability_data hdelta
  rw [hellinger_sq_eq_two_sub _ _ hpositive hnegative, bhattacharyya_closed_form hdelta]

#print axioms hellinger_sq_closed_form

/-- `klDivergence` uses natural logarithms (`Real.log`), so this is the nats convention. -/
theorem kl_divergence_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    klDivergence (positiveBiasLaw delta) (negativeBiasLaw delta) =
      2 * delta * Real.log ((1 + 2 * delta) / (1 - 2 * delta)) := by
  rw [abs_lt] at hdelta
  have hplus : 0 < 1 / 2 + delta := by linarith
  have hminus : 0 < 1 / 2 - delta := by linarith
  rw [klDivergence]
  simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  have hreciprocal :
      (1 / 2 - delta) / (1 / 2 + delta) =
        ((1 / 2 + delta) / (1 / 2 - delta))⁻¹ := by
    field_simp [hplus.ne', hminus.ne']
  rw [hreciprocal, Real.log_inv]
  have hratio :
      (1 / 2 + delta) / (1 / 2 - delta) =
        (1 + 2 * delta) / (1 - 2 * delta) := by
    field_simp [hminus.ne']
  rw [hratio]
  ring

#print axioms kl_divergence_closed_form

/-- At zero bias the laws coincide, giving the four zero/one values in the stated normalization. -/
theorem zero_bias_degenerate_case :
    totalVariation (positiveBiasLaw 0) (negativeBiasLaw 0) = 0 /\
    bhattacharyya (positiveBiasLaw 0) (negativeBiasLaw 0) = 1 /\
    hellingerSq (positiveBiasLaw 0) (negativeBiasLaw 0) = 0 /\
    klDivergence (positiveBiasLaw 0) (negativeBiasLaw 0) = 0 := by
  have hdelta : |(0 : Real)| < 1 / 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using total_variation_closed_form (0 : Real)
  · convert bhattacharyya_closed_form hdelta using 1
    norm_num
  · convert hellinger_sq_closed_form hdelta using 1
    norm_num
  · convert kl_divergence_closed_form hdelta using 1
    norm_num

#print axioms zero_bias_degenerate_case

/-- A negative bias is an interior point and is checked through all four closed forms. -/
theorem negative_bias_degenerate_case :
    |(-1 / 4 : Real)| < 1 / 2 /\
    totalVariation (positiveBiasLaw (-1 / 4)) (negativeBiasLaw (-1 / 4)) =
      2 * |(-1 / 4 : Real)| /\
    bhattacharyya (positiveBiasLaw (-1 / 4)) (negativeBiasLaw (-1 / 4)) =
      Real.sqrt (1 - 4 * (-1 / 4 : Real) ^ 2) /\
    hellingerSq (positiveBiasLaw (-1 / 4)) (negativeBiasLaw (-1 / 4)) =
      2 * (1 - Real.sqrt (1 - 4 * (-1 / 4 : Real) ^ 2)) /\
    klDivergence (positiveBiasLaw (-1 / 4)) (negativeBiasLaw (-1 / 4)) =
      2 * (-1 / 4 : Real) * Real.log ((1 + 2 * (-1 / 4 : Real)) /
        (1 - 2 * (-1 / 4 : Real))) := by
  have hdelta : |(-1 / 4 : Real)| < 1 / 2 := by norm_num
  exact ⟨hdelta, total_variation_closed_form _, bhattacharyya_closed_form hdelta,
    hellinger_sq_closed_form hdelta, kl_divergence_closed_form hdelta⟩

#print axioms negative_bias_degenerate_case

/-- Strict positivity is needed for the ordinary finite-KL interpretation: at `delta = 1 / 2`,
the reference law has a zero coordinate. The repository's real-valued KL is totalized there. -/
theorem strict_bias_bound_is_necessary :
    negativeBiasLaw (1 / 2 : Real) true = 0 /\
    ¬(∀ b : Bool, 0 < negativeBiasLaw (1 / 2 : Real) b) /\
    klDivergence (positiveBiasLaw (1 / 2 : Real))
      (negativeBiasLaw (1 / 2 : Real)) = 0 := by
  constructor
  · norm_num [negativeBiasLaw]
  constructor
  · intro h
    have htrue := h true
    norm_num [negativeBiasLaw] at htrue
  · norm_num [klDivergence, positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool]

#print axioms strict_bias_bound_is_necessary

end
end D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms
