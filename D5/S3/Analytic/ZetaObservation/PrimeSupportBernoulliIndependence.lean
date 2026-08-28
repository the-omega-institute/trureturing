/- GID: D5/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-support bits have independent power-law Bernoulli distributions. -/

import D5.S3.Analytic.Zeta.ZetaPrimeIndependence
import Mathlib.Probability.Distributions.Bernoulli

/- Library-search audit trail (2026-08-26):
   * The current-tree theorem `iIndepFun_factorization` is the family SSOT for
     mutual independence of all prime-exponent coordinates. The proof maps
     those coordinates through the measurable positive-support predicate.
   * The current-tree theorem `measure_factorization_ge` gives the exact
     positive-support mass `p ^ (-s)`.
   * Pinned Mathlib's `bernoulliMeasure` is the canonical Bernoulli law on
     `Bool`; `iIndepFun.comp` preserves the full joint-law independence.
   * Body-shape searches for a Boolean factorization-support coordinate and
     its Bernoulli law found no existing D5 declaration or definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.PrimeSupportBernoulliIndependence

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence

noncomputable section

/-- Under the zeta distribution, the indicator that a prime exponent is
positive has Bernoulli parameter `p ^ (-s)`. These support indicators are
mutually independent as one prime-indexed family. -/
theorem prime_support_bits_independent_bernoulli (s : Real) (hs : 1 < s) :
    (forall p : Nat.Primes,
      let parameter : unitInterval :=
        ⟨(p.1 : Real) ^ (-s),
          Real.rpow_nonneg (by positivity) _,
          Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast p.2.one_lt.le) (by linarith)⟩
      HasLaw (fun n : Nat => decide (0 < n.factorization p.1))
        (bernoulliMeasure true false parameter)
        (zetaDist s hs).toMeasure) /\
    iIndepFun
      (fun p : Nat.Primes => fun n : Nat => decide (0 < n.factorization p.1))
      (zetaDist s hs).toMeasure := by
  constructor
  · intro p
    have hparameterNonnegative : 0 <= (p.1 : Real) ^ (-s) :=
      Real.rpow_nonneg (by positivity) _
    have hparameterAtMostOne : (p.1 : Real) ^ (-s) <= 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast p.2.one_lt.le) (by linarith)
    let parameter : unitInterval :=
      ⟨(p.1 : Real) ^ (-s),
        hparameterNonnegative, hparameterAtMostOne⟩
    refine ⟨Measurable.aemeasurable (by fun_prop), ?_⟩
    apply Measure.ext_of_singleton
    intro bit
    fin_cases bit
    · rw [Measure.map_apply Measurable.of_discrete
          (MeasurableSet.singleton true)]
      rw [show (fun n : Nat => decide (0 < n.factorization p.1)) ⁻¹' {true} =
          {n : Nat | 1 <= n.factorization p.1} by
        ext n
        simp
        omega]
      rw [measure_factorization_ge s hs p.1 1 p.2]
      rw [bernoulliMeasure_apply_of_mem_of_notMem parameter
        (MeasurableSet.singleton true) (by simp) (by simp)]
      norm_num
      rw [ENNReal.ofReal_eq_coe_nnreal hparameterNonnegative]
      rfl
    · rw [Measure.map_apply Measurable.of_discrete
          (MeasurableSet.singleton false)]
      rw [show (fun n : Nat => decide (0 < n.factorization p.1)) ⁻¹' {false} =
          {n : Nat | n.factorization p.1 = 0} by
        ext n
        simp]
      rw [measure_factorization_eq s hs p.1 0 p.2]
      rw [bernoulliMeasure_apply_of_notMem_of_mem parameter
        (MeasurableSet.singleton false) (by simp) (by simp)]
      norm_num
      rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr hparameterAtMostOne)]
      rfl
  · simpa only [Function.comp_def] using
      (iIndepFun_factorization s hs).comp
        (fun (_ : Nat.Primes) (exponent : Nat) => decide (0 < exponent))
        (fun _ => Measurable.of_discrete)

#print axioms prime_support_bits_independent_bernoulli

end

end D5.S3.Analytic.ZetaObservation.PrimeSupportBernoulliIndependence
