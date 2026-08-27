/- GID: D5/S3/Observer/ArithmeticTomography/FinitePrimePrecisionWindowError
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/FinitePrimePrecisionWindowError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime and precision truncation has horizontal-plus-vertical error. -/

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/- Library-search audit trail (2026-08-28):
   * Repository name and body-shape searches found no exact finite prime-precision
     window theorem or canonical normalized prime-distance construction.
   * Pinned Mathlib exact hit `Nat.Primes.summable_rpow` supplies convergence for
     the source range `1 < s`.
   * Exact hits `Summable.sum_add_tsum_subtype_compl`, `Summable.tsum_le_tsum`,
     `Summable.tsum_pos`, and `Real.rpow_add` split and bound the two error terms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.ArithmeticTomography.FinitePrimePrecisionWindowError

/-- A normalized prime-weighted distance loses at most the omitted-prime tail plus
the sum of the local precision tails. The local functions are the exact and
precision-truncated distances for a fixed pair of points; quantifying them makes
the bound uniform over every pair satisfying the source local metric laws. -/
theorem finite_prime_precision_window_error
    (s : Real) (hs : 1 < s)
    (primes : Finset Nat.Primes) (precision : Nat.Primes -> Nat)
    (distance truncatedDistance : Nat.Primes -> Real)
    (hdistance : forall p, distance p ∈ Set.Icc 0 1)
    (htruncation : forall p, p ∈ primes ->
      0 <= distance p - truncatedDistance p ∧
        distance p - truncatedDistance p <=
          (p.1 : Real) ^ (-(precision p : Real))) :
    0 <=
        (∑' p : Nat.Primes, (p.1 : Real) ^ (-s) * distance p) /
            (∑' p : Nat.Primes, (p.1 : Real) ^ (-s)) -
          (∑ p ∈ primes,
              (p.1 : Real) ^ (-s) * truncatedDistance p) /
            (∑' p : Nat.Primes, (p.1 : Real) ^ (-s)) ∧
      (∑' p : Nat.Primes, (p.1 : Real) ^ (-s) * distance p) /
            (∑' p : Nat.Primes, (p.1 : Real) ^ (-s)) -
          (∑ p ∈ primes,
              (p.1 : Real) ^ (-s) * truncatedDistance p) /
            (∑' p : Nat.Primes, (p.1 : Real) ^ (-s)) <=
        ((∑' p : {p : Nat.Primes // p ∉ primes},
              (p.1.1 : Real) ^ (-s)) +
            ∑ p ∈ primes,
              (p.1 : Real) ^ (-(s + precision p))) /
          (∑' p : Nat.Primes, (p.1 : Real) ^ (-s)) := by
  classical
  let weight : Nat.Primes -> Real := fun p => (p.1 : Real) ^ (-s)
  let exactTerm : Nat.Primes -> Real := fun p => weight p * distance p
  have hweight : Summable weight := by
    exact Nat.Primes.summable_rpow.mpr (by linarith)
  have hweight_nonneg : forall p, 0 <= weight p := fun p =>
    Real.rpow_nonneg (by positivity) _
  have hprime_pos : forall p : Nat.Primes, 0 < (p.1 : Real) := by
    intro p
    exact_mod_cast p.2.pos
  have hweight_pos : forall p, 0 < weight p := fun p =>
    Real.rpow_pos_of_pos (hprime_pos p) _
  have hexact : Summable exactTerm := by
    apply hweight.of_nonneg_of_le
    · intro p
      exact mul_nonneg (hweight_nonneg p) (hdistance p).1
    · intro p
      simpa [exactTerm, weight] using
        mul_le_mul_of_nonneg_left (hdistance p).2 (hweight_nonneg p)
  have hnormalizer : 0 < ∑' p : Nat.Primes, weight p := by
    exact hweight.tsum_pos hweight_nonneg
      (⟨2, Nat.prime_two⟩ : Nat.Primes) (hweight_pos _)
  have hdecomp := hexact.sum_add_tsum_subtype_compl primes
  have htail :
      (∑' p : {p : Nat.Primes // p ∉ primes}, exactTerm p.1) <=
        ∑' p : {p : Nat.Primes // p ∉ primes}, weight p.1 := by
    exact (hexact.subtype _).tsum_le_tsum
      (fun p => by
        simpa [exactTerm] using
          mul_le_mul_of_nonneg_left (hdistance p.1).2 (hweight_nonneg p.1))
      (hweight.subtype _)
  have hfinite_nonneg :
      0 <= ∑ p ∈ primes, weight p * (distance p - truncatedDistance p) := by
    exact Finset.sum_nonneg fun p hp =>
      mul_nonneg (hweight_nonneg p) (htruncation p hp).1
  have hfinite_bound :
      (∑ p ∈ primes, weight p * (distance p - truncatedDistance p)) <=
        ∑ p ∈ primes, (p.1 : Real) ^ (-(s + precision p)) := by
    apply Finset.sum_le_sum
    intro p hp
    calc
      weight p * (distance p - truncatedDistance p) <=
          weight p * (p.1 : Real) ^ (-(precision p : Real)) :=
        mul_le_mul_of_nonneg_left (htruncation p hp).2 (hweight_nonneg p)
      _ = (p.1 : Real) ^ (-(s + precision p)) := by
        rw [show -(s + (precision p : Real)) =
          -s + -(precision p : Real) by ring]
        exact (Real.rpow_add (hprime_pos p) _ _).symm
  have hnumerator_eq :
      (∑' p : Nat.Primes, exactTerm p) -
          ∑ p ∈ primes, weight p * truncatedDistance p =
        (∑ p ∈ primes, weight p * (distance p - truncatedDistance p)) +
          ∑' p : {p : Nat.Primes // p ∉ primes}, exactTerm p.1 := by
    calc
      (∑' p : Nat.Primes, exactTerm p) -
            ∑ p ∈ primes, weight p * truncatedDistance p =
          (∑ p ∈ primes, exactTerm p) -
              (∑ p ∈ primes, weight p * truncatedDistance p) +
            ∑' p : {p : Nat.Primes // p ∉ primes}, exactTerm p.1 := by
        rw [← hdecomp]
        ring
      _ = (∑ p ∈ primes, weight p * (distance p - truncatedDistance p)) +
            ∑' p : {p : Nat.Primes // p ∉ primes}, exactTerm p.1 := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        simp only [exactTerm, mul_sub]
  have hnumerator :
      0 <= (∑' p : Nat.Primes, exactTerm p) -
          ∑ p ∈ primes, weight p * truncatedDistance p ∧
        (∑' p : Nat.Primes, exactTerm p) -
            ∑ p ∈ primes, weight p * truncatedDistance p <=
          (∑' p : {p : Nat.Primes // p ∉ primes}, weight p.1) +
            ∑ p ∈ primes, (p.1 : Real) ^ (-(s + precision p)) := by
    rw [hnumerator_eq]
    constructor
    · exact add_nonneg hfinite_nonneg
        (tsum_nonneg fun p =>
          mul_nonneg (hweight_nonneg p.1) (hdistance p.1).1)
    · exact (add_le_add hfinite_bound htail).trans_eq (add_comm _ _)
  change 0 <= _ / (∑' p, weight p) - _ / (∑' p, weight p) ∧
    _ / (∑' p, weight p) - _ / (∑' p, weight p) <= _
  rw [← sub_div]
  constructor
  · exact div_nonneg hnumerator.1 hnormalizer.le
  · apply (div_le_div_iff₀ hnormalizer hnormalizer).2
    exact mul_le_mul_of_nonneg_right
      (by simpa [weight, exactTerm, add_comm] using hnumerator.2)
      hnormalizer.le

#print axioms finite_prime_precision_window_error

end D5.S3.Observer.ArithmeticTomography.FinitePrimePrecisionWindowError
