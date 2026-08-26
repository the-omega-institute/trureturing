/- GID: D5/S3/Observer/ArithmeticTomography/SmallPrimeChannelOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/SmallPrimeChannelOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first m primes maximize information among m complete equal-cost channels. -/

import Mathlib

/- Library-search audit trail (2026-08-25):
   * Repository searches for small-prime priority, prime-channel entropy,
     fixed-cardinality information budgets, and strictly decreasing prime
     information found no exact D5 theorem. The adjacent frozen
     `finite_prime_information_budget` is a logarithmic capacity lower bound,
     not a selection optimality result.
   * Pinned-Mathlib searches for antitone finite-sum maximization and
     first-prime selection found no exact packaged theorem.
   * Exact pinned-Mathlib hits `Nat.Subtype.orderIsoOfNat` and
     `Finset.sum_le_sum` provide the canonical increasing prime enumeration
     and the pointwise-to-total comparison used below.
   * Body-shape searches found no D5 definition of the first-prime channel
     family or of this fixed-cardinality objective; this module introduces no
     new `def` or `abbrev`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.SmallPrimeChannelOptimality

/-- At a fixed zeta parameter above one, if complete-channel information is
strictly decreasing with the prime, then the first `m` primes maximize the
total information among every ordered choice of exactly `m` distinct primes.
The common index cardinality is the equal-cost budget constraint. -/
theorem small_prime_channel_optimality
    (s : {parameter : Real // 1 < parameter})
    (primeInformation :
      {parameter : Real // 1 < parameter} → {p : Nat // Nat.Prime p} → Real)
    (hdecreasing : StrictAnti (primeInformation s))
    (m : Nat) (chosen : Fin m ↪o Nat)
    (hprime : ∀ i, Nat.Prime (chosen i)) :
    (∑ i : Fin m, primeInformation s ⟨chosen i, hprime i⟩) ≤
      ∑ i : Fin m, primeInformation s
        ⟨Nat.nth (fun p : Nat => Nat.Prime p) i,
          Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i⟩ := by
  let primeOrder : Nat ≃o {p : Nat // Nat.Prime p} :=
    @Nat.Subtype.orderIsoOfNat {p : Nat | Nat.Prime p}
      Nat.infinite_setOf_prime.to_subtype
  let chosenIndices : Fin m → Nat :=
    fun i => primeOrder.symm ⟨chosen i, hprime i⟩
  have chosenIndices_strictMono : StrictMono chosenIndices := by
    intro i j hij
    apply primeOrder.symm.strictMono
    exact chosen.strictMono hij
  have index_le_chosen_index : ∀ i : Fin m, i.val ≤ chosenIndices i := by
    cases m with
    | zero =>
      intro i
      exact i.elim0
    | succ m =>
      intro i
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          exact Nat.succ_le_of_lt
            (lt_of_le_of_lt ih
              (chosenIndices_strictMono i.castSucc_lt_succ))
  apply Finset.sum_le_sum
  intro i _
  apply hdecreasing.antitone
  change (⟨Nat.nth (fun p : Nat => Nat.Prime p) i,
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i⟩ :
    {p : Nat // Nat.Prime p}) ≤ ⟨chosen i, hprime i⟩
  calc
    (⟨Nat.nth (fun p : Nat => Nat.Prime p) i,
        Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i⟩ :
        {p : Nat // Nat.Prime p}) = primeOrder i.val := by
      apply Subtype.ext
      change Nat.nth (fun p : Nat => Nat.Prime p) i =
        ((@Nat.Subtype.orderIsoOfNat {p : Nat | Nat.Prime p}
          Nat.infinite_setOf_prime.to_subtype) i).val
      exact Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOf_prime i
    _ ≤ primeOrder (chosenIndices i) :=
      primeOrder.monotone (index_le_chosen_index i)
    _ = ⟨chosen i, hprime i⟩ :=
      primeOrder.apply_symm_apply ⟨chosen i, hprime i⟩

#print axioms small_prime_channel_optimality

end D5.S3.Observer.ArithmeticTomography.SmallPrimeChannelOptimality
