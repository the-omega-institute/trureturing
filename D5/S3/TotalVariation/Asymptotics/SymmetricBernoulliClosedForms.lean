/- GID: D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliClosedForms
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/SymmetricBernoulliClosedForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute four finite evidence measures for the symmetric Bernoulli pair. -/

import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

/- Library-search audit trail (2026-08-26):
   * Current-tree name and body-shape searches found the canonical frozen
     `positiveBiasLaw`, `negativeBiasLaw`, `totalVariation`, `bhattacharyya`,
     `hellingerSq`, and `klDivergence` definitions, which are reused here.
   * The adjacent asymptotics module contains three private closed-form helper
     lemmas, but its public theorem states only second-order asymptotics, so it
     is not an exact bind for this four-identity statement.
   * Pinned-Mathlib searches for Bernoulli total variation, Hellinger,
     Bhattacharyya, and finite KL closed forms found no exact theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliClosedForms

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.Pinsker

noncomputable section

/-- On the full probability domain, the symmetric two-point laws have exact
total variation, affinity, squared Hellinger, and KL evidence formulas. -/
theorem symmetric_bernoulli_evidence_closed_forms (delta : Real)
    (hdelta : |delta| < 1 / 2) :
    totalVariation (positiveBiasLaw delta) (negativeBiasLaw delta) =
        2 * |delta| /\
      bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta) =
        Real.sqrt (1 - 4 * delta ^ 2) /\
      hellingerSq (positiveBiasLaw delta) (negativeBiasLaw delta) =
        2 * (1 - Real.sqrt (1 - 4 * delta ^ 2)) /\
      klDivergence (positiveBiasLaw delta) (negativeBiasLaw delta) =
        2 * delta * Real.log ((1 + 2 * delta) / (1 - 2 * delta)) := by
  have hbounds : -(1 / 2 : Real) < delta /\ delta < 1 / 2 :=
    (abs_lt.mp hdelta)
  have hplus : 0 < 1 / 2 + delta := by linarith
  have hminus : 0 < 1 / 2 - delta := by linarith
  have hpositive :
      (forall b, 0 <= positiveBiasLaw delta b) /\
        ∑ b, positiveBiasLaw delta b = 1 := by
    constructor
    · intro b
      cases b <;> simp only [positiveBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
        linarith
    · norm_num [positiveBiasLaw, Fintype.sum_bool]
  have hnegative :
      (forall b, 0 <= negativeBiasLaw delta b) /\
        ∑ b, negativeBiasLaw delta b = 1 := by
    constructor
    · intro b
      cases b <;> simp only [negativeBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
        linarith
    · norm_num [negativeBiasLaw, Fintype.sum_bool]
  have haffinity :
      bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta) =
        Real.sqrt (1 - 4 * delta ^ 2) := by
    have hproduct : 0 <= (1 / 2 + delta) * (1 / 2 - delta) :=
      mul_nonneg hplus.le hminus.le
    have hradicand : 0 <= 1 - 4 * delta ^ 2 := by
      nlinarith [sq_nonneg (|delta|), sq_abs delta]
    rw [bhattacharyya]
    simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte]
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
    nlinarith [Real.sqrt_nonneg ((1 / 2 + delta) * (1 / 2 - delta)),
      Real.sqrt_nonneg (1 - 4 * delta ^ 2)]
  refine ⟨?_, haffinity, ?_, ?_⟩
  · rw [totalVariation]
    simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte]
    have hleft : 1 / 2 - delta - (1 / 2 + delta) = -(2 * delta) := by ring
    have hright : 1 / 2 + delta - (1 / 2 - delta) = 2 * delta := by ring
    rw [hleft, hright, abs_neg, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    ring
  · rw [hellinger_sq_eq_two_sub _ _ hpositive hnegative, haffinity]
  · rw [klDivergence]
    simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte]
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

#print axioms symmetric_bernoulli_evidence_closed_forms

end

end D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliClosedForms
