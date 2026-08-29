/- GID: D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear and quadratic prime masses split at one and one half, with degeneracies. -/
/- Library-search audit trail (2026-08-25): `primeEvidence*` hit the exact
   prime-power threshold; `PrimeExponentLaw.measure_factorization_ge` hit the
   zeta-law activation probability. `Real.summable_one_div_nat_rpow` is only
   natural-indexed. `Summable` and `Nat.Primes.summable_rpow` were inspected.
   `hellingerDist` had no hit; the repository uses `hellingerSq`, and
   `symmetric_bernoulli_second_order` supplies the quadratic local asymptotic.
   `WeakPrimeEvidenceFiniteTotal` treats only one fixed exponent, not this iff. -/

import D5.S3.Analytic.Zeta.PrimeExponentLaw
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.LocalEvidenceOrderThreshold

open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

noncomputable section

/-!
`primeEvidence` is a numerical evidence family. The first definition below gives
that same local formula its event-mass role, while the probability bridge proves
that role against the actual zeta law whenever the global law exists.

Primality is load-bearing in both exact power-law thresholds through
`primeEvidence_summable_iff_one_lt`. In contrast, the quadratic-energy definition,
its zero-family theorem, and its empty/unit degenerations work for every index type.
Finite prime truncations are summable without any prime-distribution theorem.

The only proof argument `hs : 1 < s` occurs in the probability bridge. It is used
both to construct `zetaDist s hs` and by `measure_factorization_ge`; it is therefore
definitional rather than a removable analytic hypothesis. All threshold statements
are unconditional equivalences, so no hypothesis counterexample theorem is needed.
-/

/-- The local mass of the event that the exponent at `p` is positive. -/
def firstEventMass (s : ℝ) (p : Nat.Primes) : ℝ :=
  primeEvidence s p

/-- The quadratic statistical energy contributed by one coordinate. -/
def quadraticStatisticalEnergy {ι : Type*} (δ : ι → ℝ) (i : ι) : ℝ :=
  δ i ^ 2

/-- In the realizable zeta regime, first-event mass is the actual activation probability. -/
theorem firstEventMass_eq_activation_probability (s : ℝ) (hs : 1 < s)
    (p : Nat.Primes) :
    (zetaDist s hs).toMeasure {n : ℕ | 0 < n.factorization p.1} =
      ENNReal.ofReal (firstEventMass s p) := by
  rw [show {n : ℕ | 0 < n.factorization p.1} =
      {n : ℕ | 1 ≤ n.factorization p.1} by
    ext n
    simp only [Set.mem_setOf_eq]
    omega]
  simpa [firstEventMass, primeEvidence] using
    (measure_factorization_ge s hs p.1 1 p.2)

#print axioms firstEventMass_eq_activation_probability

/-- First-event masses are summable exactly above exponent one. -/
theorem firstEventMass_summable_iff_one_lt (s : ℝ) :
    Summable (firstEventMass s) ↔ 1 < s := by
  change Summable (primeEvidence s) ↔ 1 < s
  exact primeEvidence_summable_iff_one_lt s

#print axioms firstEventMass_summable_iff_one_lt

/-- Squaring the power-law deviation doubles its exponent on the same prime spectrum. -/
theorem quadratic_prime_energy_eq_firstEventMass (α : ℝ) :
    quadraticStatisticalEnergy (firstEventMass α) = firstEventMass (2 * α) := by
  funext p
  simp only [quadraticStatisticalEnergy, firstEventMass, primeEvidence]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

#print axioms quadratic_prime_energy_eq_firstEventMass

/-- Quadratic power-law energy is summable exactly above exponent one half. -/
theorem quadratic_prime_energy_summable_iff_half_lt (α : ℝ) :
    Summable (quadraticStatisticalEnergy (firstEventMass α)) ↔
      (1 / 2 : ℝ) < α := by
  rw [quadratic_prime_energy_eq_firstEventMass,
    firstEventMass_summable_iff_one_lt]
  constructor <;> intro h <;> linarith

#print axioms quadratic_prime_energy_summable_iff_half_lt

/-- Linear activation and quadratic evidence have different exact critical exponents. -/
theorem local_evidence_order_critical_thresholds :
    (∀ s : ℝ, Summable (firstEventMass s) ↔ 1 < s) ∧
      (∀ α : ℝ, Summable (quadraticStatisticalEnergy (firstEventMass α)) ↔
        (1 / 2 : ℝ) < α) ∧
      (1 : ℝ) ≠ 1 / 2 := by
  exact ⟨firstEventMass_summable_iff_one_lt,
    quadratic_prime_energy_summable_iff_half_lt, by norm_num⟩

#print axioms local_evidence_order_critical_thresholds

/-- At and below one, the first-event masses are not summable. -/
theorem firstEventMass_at_most_one_not_summable :
    ∀ s : ℝ, s ≤ 1 → ¬ Summable (firstEventMass s) := by
  intro s hs hsum
  exact (not_lt.mpr hs) ((firstEventMass_summable_iff_one_lt s).mp hsum)

#print axioms firstEventMass_at_most_one_not_summable

/-- Exponent zero is the constant-one first-event family and is not summable. -/
theorem firstEventMass_zero :
    (∀ p : Nat.Primes, firstEventMass 0 p = 1) ∧
      ¬ Summable (firstEventMass 0) := by
  constructor
  · intro p
    simp [firstEventMass, primeEvidence]
  · exact firstEventMass_at_most_one_not_summable 0 (by norm_num)

#print axioms firstEventMass_zero

/-- The zero deviation has zero, hence summable, quadratic energy on every index type. -/
theorem quadraticStatisticalEnergy_zero_summable {ι : Type*} :
    Summable (quadraticStatisticalEnergy (fun _ : ι ↦ (0 : ℝ))) := by
  have hzero : quadraticStatisticalEnergy (fun _ : ι ↦ (0 : ℝ)) =
      fun _ : ι ↦ (0 : ℝ) := by
    funext i
    simp [quadraticStatisticalEnergy]
  rw [hzero]
  exact summable_zero

#print axioms quadraticStatisticalEnergy_zero_summable

/-- Every finite prime truncation is summable, independently of its exponent. -/
theorem finite_prime_truncation_summable (S : Finset Nat.Primes) (s : ℝ) :
    Summable (fun p : Nat.Primes ↦ if p ∈ S then firstEventMass s p else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply S.finite_toSet.subset
  intro p hp
  simp only [Function.mem_support] at hp
  by_cases hmem : p ∈ S
  · exact hmem
  · simp [hmem] at hp

#print axioms finite_prime_truncation_summable

/-- Empty and singleton index types make every quadratic-energy family summable. -/
theorem quadratic_energy_empty_and_unit_summable :
    (∀ δ : Empty → ℝ, Summable (quadraticStatisticalEnergy δ)) ∧
      (∀ δ : Unit → ℝ, Summable (quadraticStatisticalEnergy δ)) := by
  constructor <;> intro δ <;> exact Summable.of_finite

#print axioms quadratic_energy_empty_and_unit_summable

/-- The exponent one-half boundary itself is not summable. -/
theorem quadratic_prime_energy_one_half_not_summable :
    ¬ Summable
      (quadraticStatisticalEnergy (firstEventMass (1 / 2 : ℝ))) := by
  rw [quadratic_prime_energy_summable_iff_half_lt]
  norm_num

#print axioms quadratic_prime_energy_one_half_not_summable

end

end D5.S3.Analytic.ZetaEntropyPlane.LocalEvidenceOrderThreshold
