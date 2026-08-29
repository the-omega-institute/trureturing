/- GID: D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold
   generality: I
   mirror-B: D5/B/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weak prime signals split at one half; zero amplitude and missing bridge are audited. -/
/- Library-search audit trail (2026-08-29): repository name, body-shape, digest,
   and residual-index searches found no declaration combining a named weak-prime
   signal, nonzero scaling, and both sides of the product-law dichotomy. The exact
   numerical predecessor is `quadratic_prime_energy_summable_iff_half_lt`, and
   `primeEvidence_summable_iff_one_lt` is its unique prime-series source. Pinned
   Mathlib has five `Kakutani` file hits, all for Riesz--Markov--Kakutani, so the
   absent product-measure theorem is represented by a named explicit premise.
   Mathlib's canonical measure relations are `Measure.MutuallySingular` and
   bidirectional `Measure.AbsolutelyContinuous`. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Analytic.ZetaEntropyPlane.LocalEvidenceOrderThreshold
import D5.S3.Observer.MeasureSeparation.ZeroBayesResidualCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MeasureSeparation.WeakPrimeSignalCompletionThreshold

open Filter MeasureTheory Set
open scoped MeasureTheory Topology
open D5.S3.Analytic.ZetaEntropyPlane.LocalEvidenceOrderThreshold
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Observer.MeasureSeparation.ZeroBayesResidualCriterion

noncomputable section

/-- The prime-indexed signal amplitude `c * p ^ (-alpha)`. -/
def weakPrimeSignal (c alpha : Real) (p : Nat.Primes) : Real :=
  c * firstEventMass alpha p

/-- An explicit substitute for the unavailable Kakutani product-measure theorem. -/
def SignalKakutaniDichotomy {Index Transcript : Type*}
    [MeasurableSpace Transcript] (energy : Index -> Real)
    (productP productQ : Measure Transcript) : Prop :=
  (productP ⟂ₘ productQ ↔ ¬Summable energy) ∧
    ((productP ≪ productQ ∧ productQ ≪ productP) ↔ Summable energy)

example (c alpha : Real) :
    quadraticStatisticalEnergy (weakPrimeSignal c alpha) =
      fun p => c ^ 2 * quadraticStatisticalEnergy (firstEventMass alpha) p := by
  funext p
  simp only [quadraticStatisticalEnergy, weakPrimeSignal]
  ring

example (c alpha : Real) (hc : c ≠ 0) :
    Summable (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) ↔
      (1 / 2 : Real) < alpha := by
  rw [show quadraticStatisticalEnergy (weakPrimeSignal c alpha) =
      fun p => c ^ 2 * quadraticStatisticalEnergy (firstEventMass alpha) p by
    funext p
    simp only [quadraticStatisticalEnergy, weakPrimeSignal]
    ring]
  rw [summable_mul_left_iff (pow_ne_zero 2 hc)]
  exact quadratic_prime_energy_summable_iff_half_lt alpha

example (c alpha : Real) (hc : c ≠ 0) :
    ¬Summable (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) ↔
      alpha ≤ (1 / 2 : Real) := by
  rw [not_congr (show
    Summable (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) ↔
        (1 / 2 : Real) < alpha by
      rw [show quadraticStatisticalEnergy (weakPrimeSignal c alpha) =
          fun p => c ^ 2 * quadraticStatisticalEnergy (firstEventMass alpha) p by
        funext p
        simp only [quadraticStatisticalEnergy, weakPrimeSignal]
        ring]
      rw [summable_mul_left_iff (pow_ne_zero 2 hc)]
      exact quadratic_prime_energy_summable_iff_half_lt alpha)]
  exact not_lt

example (alpha : Real) :
    weakPrimeSignal 0 alpha = 0 ∧
      Summable (quadraticStatisticalEnergy (weakPrimeSignal 0 alpha)) := by
  constructor
  · funext p
    simp [weakPrimeSignal]
  · simpa [weakPrimeSignal] using
      (quadraticStatisticalEnergy_zero_summable (ι := Nat.Primes))

example :
    ¬(¬Summable (quadraticStatisticalEnergy (weakPrimeSignal 0 0)) ↔
      (0 : Real) ≤ 1 / 2) := by
  simp [weakPrimeSignal, quadraticStatisticalEnergy]

example (c : Real) (p : Nat.Primes) :
    Tendsto (fun alpha => weakPrimeSignal c alpha p) atTop (nhds 0) := by
  have hp : (1 : Real) < (p : Real) := by
    exact_mod_cast p.2.one_lt
  have hbase : Tendsto (fun alpha : Real => ((p : Real)⁻¹) ^ alpha)
      atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one (p : Real)⁻¹ (by positivity)
      (inv_lt_one₀ (by positivity)).mpr hp
  have hsignal : Tendsto (fun alpha : Real => (p : Real) ^ (-alpha))
      atTop (nhds 0) := by
    simpa only [Real.rpow_neg_eq_inv_rpow] using hbase
  simpa [weakPrimeSignal, firstEventMass, primeEvidence] using
    tendsto_const_nhds.mul hsignal

example {Transcript : Type*} [MeasurableSpace Transcript]
    (productP productQ : Measure Transcript) (c alpha : Real) (hc : c ≠ 0)
    (hK : SignalKakutaniDichotomy
      (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) productP productQ) :
    (productP ⟂ₘ productQ ↔ alpha ≤ (1 / 2 : Real)) ∧
      ((productP ≪ productQ ∧ productQ ≪ productP) ↔
        (1 / 2 : Real) < alpha) := by
  rcases hK with ⟨hsingular, hequivalent⟩
  constructor
  · rw [hsingular]
    rw [not_congr (show
      Summable (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) ↔
          (1 / 2 : Real) < alpha by
        rw [show quadraticStatisticalEnergy (weakPrimeSignal c alpha) =
            fun p => c ^ 2 * quadraticStatisticalEnergy (firstEventMass alpha) p by
          funext p
          simp only [quadraticStatisticalEnergy, weakPrimeSignal]
          ring]
        rw [summable_mul_left_iff (pow_ne_zero 2 hc)]
        exact quadratic_prime_energy_summable_iff_half_lt alpha)]
    exact not_lt
  · rw [hequivalent]
    rw [show Summable (quadraticStatisticalEnergy (weakPrimeSignal c alpha)) ↔
        (1 / 2 : Real) < alpha by
      rw [show quadraticStatisticalEnergy (weakPrimeSignal c alpha) =
          fun p => c ^ 2 * quadraticStatisticalEnergy (firstEventMass alpha) p by
        funext p
        simp only [quadraticStatisticalEnergy, weakPrimeSignal]
        ring]
      rw [summable_mul_left_iff (pow_ne_zero 2 hc)]
      exact quadratic_prime_energy_summable_iff_half_lt alpha]

example :
    ¬Summable
        (quadraticStatisticalEnergy (weakPrimeSignal 1 (1 / 2 : Real))) ∧
      ¬((Measure.dirac () : Measure Unit) ⟂ₘ Measure.dirac ()) := by
  constructor
  · rw [show quadraticStatisticalEnergy (weakPrimeSignal 1 (1 / 2 : Real)) =
        quadraticStatisticalEnergy (firstEventMass (1 / 2 : Real)) by
      funext p
      simp [weakPrimeSignal]]
    exact quadratic_prime_energy_one_half_not_summable
  · simp

end

end D5.S3.Observer.MeasureSeparation.WeakPrimeSignalCompletionThreshold
