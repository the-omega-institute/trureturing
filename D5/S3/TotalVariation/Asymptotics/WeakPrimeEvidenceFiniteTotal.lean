/- GID: D5/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal
   generality: I
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-indexed weak Bernoulli coordinates can have finite total affinity evidence. -/

import D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms

/- Library-search audit trail (2026-08-28):
   * Repository searches for weak coordinates, finite evidence, summable affinity,
     and prime evidence found no frozen theorem on channel-derived negative-log
     Bhattacharyya evidence. Existing prime-power evidence and KL-evidence results
     use different carriers.
   * The frozen `positiveBiasLaw`, `negativeBiasLaw`,
     `bhattacharyya_closed_form`, and `symmetric_bernoulli_second_order`
     declarations are reused as the canonical local channel and affinity facts.
   * Pinned Mathlib supplies `Nat.Primes.summable_rpow`,
     `summable_of_isBigO`, and `Summable.tendsto_cofinite_zero`; no exact theorem
     constructs this prime-indexed channel family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.WeakPrimeEvidenceFiniteTotal

open Filter Asymptotics
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Asymptotics.FourLocalEvidenceClosedForms

noncomputable section

/-- Infinitely many symmetric Bernoulli coordinates can each carry positive but
vanishing negative-log affinity evidence while their total evidence remains finite. -/
theorem weak_prime_evidence_finite_total :
    (forall p : Nat.Primes,
      0 < -Real.log (bhattacharyya
        (positiveBiasLaw ((p : Real) ^ (-2 : Real)))
        (negativeBiasLaw ((p : Real) ^ (-2 : Real))))) /\
    Summable (fun p : Nat.Primes =>
      -Real.log (bhattacharyya
        (positiveBiasLaw ((p : Real) ^ (-2 : Real)))
        (negativeBiasLaw ((p : Real) ^ (-2 : Real))))) /\
    Tendsto (fun p : Nat.Primes =>
      -Real.log (bhattacharyya
        (positiveBiasLaw ((p : Real) ^ (-2 : Real)))
        (negativeBiasLaw ((p : Real) ^ (-2 : Real)))))
      cofinite (nhds 0) := by
  let delta : Nat.Primes -> Real := fun p => (p : Real) ^ (-2 : Real)
  have hdelta : Summable delta := by
    dsimp [delta]
    exact Nat.Primes.summable_rpow.mpr (by norm_num)
  have hdelta_zero : Tendsto delta cofinite (nhds 0) :=
    hdelta.tendsto_cofinite_zero
  have hdelta_sq : Summable (fun p => delta p ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-4 : Real) < -1)
    refine h.congr fun p => ?_
    dsimp [delta]
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul (by positivity)]
    norm_num
  have hdelta_fourth : Summable (fun p => delta p ^ 4) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-8 : Real) < -1)
    refine h.congr fun p => ?_
    dsimp [delta]
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul (by positivity)]
    norm_num
  have hremainder_bigO :
      (fun p : Nat.Primes =>
        -Real.log (bhattacharyya (positiveBiasLaw (delta p))
          (negativeBiasLaw (delta p))) - 2 * delta p ^ 2)
        =O[cofinite] (fun p => delta p ^ 4) :=
    symmetric_bernoulli_second_order.2.1.comp_tendsto hdelta_zero
  have hremainder :
      Summable (fun p : Nat.Primes =>
        -Real.log (bhattacharyya (positiveBiasLaw (delta p))
          (negativeBiasLaw (delta p))) - 2 * delta p ^ 2) :=
    summable_of_isBigO hdelta_fourth hremainder_bigO
  have hevidence :
      Summable (fun p : Nat.Primes =>
        -Real.log (bhattacharyya (positiveBiasLaw (delta p))
          (negativeBiasLaw (delta p)))) := by
    refine (hremainder.add (hdelta_sq.mul_left 2)).congr fun p => ?_
    ring
  refine ⟨?_, hevidence, hevidence.tendsto_cofinite_zero⟩
  intro p
  have hp_two : (2 : Real) <= (p : Real) := by
    exact_mod_cast p.prop.two_le
  have hp_pos : 0 < (p : Real) := lt_of_lt_of_le (by norm_num) hp_two
  have hdelta_pos : 0 < delta p := by
    dsimp [delta]
    exact Real.rpow_pos_of_pos hp_pos _
  have hdelta_le : delta p <= 1 / 4 := by
    dsimp [delta]
    have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : 0 < (2 : Real))
      hp_two (by norm_num : (-2 : Real) <= 0)
    norm_num at hpow ⊢
    exact hpow
  have hdelta_abs : |delta p| < 1 / 2 := by
    rw [abs_of_pos hdelta_pos]
    linarith
  rw [bhattacharyya_closed_form hdelta_abs]
  have hradicand_pos : 0 < 1 - 4 * delta p ^ 2 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 - 4 * delta p ^ 2) :=
    Real.sqrt_pos.2 hradicand_pos
  have hsqrt_lt : Real.sqrt (1 - 4 * delta p ^ 2) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < 1)]
    nlinarith
  simpa using Real.log_neg hsqrt_pos hsqrt_lt

#print axioms weak_prime_evidence_finite_total

end
end D5.S3.TotalVariation.Asymptotics.WeakPrimeEvidenceFiniteTotal
