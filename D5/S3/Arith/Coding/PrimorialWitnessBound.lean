/- GID: D5/S3/Arith/Coding/PrimorialWitnessBound
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/PrimorialWitnessBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A large prime-prefix product bounds the first distinguishing-prime index. -/

import D5.S3.Arith.Coding.HorizontalCompletenessDepth
import Mathlib.RingTheory.Coprime.Lemmas

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for primorial witness bounds, first nondividing
     primes, and least distinguishing indices found no covering declaration.
     `HorizontalCompletenessDepth` supplies the canonical `primePrefixProduct`
     but only proves a finite-window injectivity threshold.
   * The body-shape search for an `sInf` of positive prime-nondivisibility
     witnesses was a miss, so the source-defined complexity is introduced here.
   * Pinned Mathlib has no exact theorem for this witness bound. The proof
     directly applies `Nat.notMem_of_lt_sInf`, `Fintype.prod_dvd_of_coprime`,
     `Nat.coprime_primes`, and `Int.natAbs_le_of_dvd_ne_zero`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Coding.PrimorialWitnessBound

open D5.S3.Arith.Coding.HorizontalCompletenessDepth

/-- The least positive one-based index of a prime that distinguishes two integers
by failing to divide their difference. -/
def horizontalWitnessComplexity (x y : Int) : Nat :=
  sInf {j : Nat | 0 < j ∧
    ¬((Nat.nth Nat.Prime (j - 1) : Nat) : Int) ∣ x - y}

/-- If the product of the first `r` primes exceeds a nonzero integer difference,
then a distinguishing prime occurs among those first `r` primes. -/
theorem primorial_witness_bound (x y : Int) (hxy : x ≠ y) (r : Nat)
    (hbound : Int.natAbs (x - y) < primePrefixProduct r) :
    horizontalWitnessComplexity x y ≤ r := by
  by_contra notBounded
  have hr_lt : r < horizontalWitnessComplexity x y :=
    Nat.lt_of_not_ge notBounded
  have allDivide : ∀ i : Fin r,
      ((Nat.nth Nat.Prime i : Nat) : Int) ∣ x - y := by
    intro i
    by_contra notDivides
    have witnessMem : i.1 + 1 ∈ {j : Nat | 0 < j ∧
        ¬((Nat.nth Nat.Prime (j - 1) : Nat) : Int) ∣ x - y} := by
      constructor
      · omega
      · simpa only [Nat.add_sub_cancel] using notDivides
    have witnessLt : i.1 + 1 < horizontalWitnessComplexity x y := by
      exact lt_of_le_of_lt (by omega) hr_lt
    exact (Nat.notMem_of_lt_sInf (s := {j : Nat | 0 < j ∧
      ¬((Nat.nth Nat.Prime (j - 1) : Nat) : Int) ∣ x - y})
        (by simpa only [horizontalWitnessComplexity] using witnessLt)) witnessMem
  have productDivides :
      (∏ i : Fin r, ((Nat.nth Nat.Prime i : Nat) : Int)) ∣ x - y := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      have hindexNe : (i : Nat) ≠ (j : Nat) := by
        intro sameIndex
        exact hij (Fin.ext sameIndex)
      have hprimeNe : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime j :=
        fun samePrime => hindexNe
          ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective samePrime)
      exact ((Nat.coprime_primes (Nat.prime_nth_prime i)
        (Nat.prime_nth_prime j)).2 hprimeNe).isCoprime
    · exact allDivide
  have prefixDivides : ((primePrefixProduct r : Nat) : Int) ∣ x - y := by
    simpa only [primePrefixProduct, ← Fin.prod_univ_eq_prod_range, Nat.cast_prod]
      using productDivides
  have differenceNe : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have productLe := Int.natAbs_le_of_dvd_ne_zero prefixDivides differenceNe
  have : primePrefixProduct r ≤ Int.natAbs (x - y) := by
    simpa only [Int.natAbs_natCast] using productLe
  exact (Nat.not_le_of_gt hbound) this

end D5.S3.Arith.Coding.PrimorialWitnessBound
