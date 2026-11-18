/- GID: D5/S3/Arith/Robin/GronwallAbundant/Coding
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GronwallAbundant/Coding
   mirror-E: none(waiver:finite-counting-inequality)
   anchors: []
   utility: none
   digest: Prime prefixes and bounded missing sets encode integers injectively. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.GronwallAbundant
open Finset
open scoped BigOperators

/-- Subsets with bounded cardinality are partitioned by their actual sizes. -/
theorem small_subsets_card {α : Type*} (s : Finset α) (K : ℕ) :
    (s.powerset.filter (fun u => u.card ≤ K)).card =
      ∑ j ∈ Finset.range (K + 1), s.card.choose j := by
  classical
  have hsum := Finset.sum_powerset_apply_card (α := ℕ)
    (fun j => if j ≤ K then 1 else 0) (x := s)
  have hleft : (∑ u ∈ s.powerset, if u.card ≤ K then 1 else 0) =
      (s.powerset.filter (fun u => u.card ≤ K)).card := by simp
  rw [hleft] at hsum
  rw [hsum]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hK : K ≤ s.card
  · rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hK 1))]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
    · intro j hj hjK
      rw [if_neg (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjK)]
  · have hc : s.card ≤ K := by omega
    calc
      _ = ∑ j ∈ Finset.range (s.card + 1), s.card.choose j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
      _ = _ := Finset.sum_subset (Finset.range_mono (by omega)) (by
        intro j hj hjc
        exact Nat.choose_eq_zero_of_lt (by
          simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hjc))

/-- A truncated binomial sum is controlled by its generating polynomial. -/
theorem binomial_partial_sum_weighted (M K : ℕ) (hKM : K ≤ M)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ K * (∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ)) ≤ (1 + t) ^ M := by
  calc
    _ = ∑ j ∈ Finset.range (K + 1), t ^ K * (M.choose j : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (K + 1), t ^ j * (M.choose j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one ht0 ht1 (by have := Finset.mem_range.mp hj; omega))
        (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (M + 1), t ^ j * (M.choose j : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.add_le_add_right hKM 1)) (fun _ _ _ => by positivity)
    _ = (1 + t) ^ M := by
      simpa [add_comm] using (add_pow t (1 : ℝ) M).symm

/-- The missing-set choices satisfy the elementary binomial entropy bound. -/
theorem binomial_partial_sum_entropy (M K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ M) :
    (∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ)) ≤
      Real.exp ((K : ℝ) * (1 + Real.log ((M : ℝ) / K))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hK0 (by exact_mod_cast hKM)
  let t : ℝ := K / M
  have ht0 : 0 < t := div_pos hK0 hM0
  have ht1 : t ≤ 1 := (div_le_one hM0).mpr (by exact_mod_cast hKM)
  have hs0 : 0 < ∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ) := by
    have hone : (1 : ℝ) ≤ ∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ) := by
      simpa using Finset.single_le_sum (fun j _ => Nat.cast_nonneg (M.choose j))
        (show 0 ∈ Finset.range (K + 1) by simp)
    linarith
  have he : (1 + t) ^ M ≤ Real.exp (K : ℝ) := by
    calc
      _ ≤ (Real.exp t) ^ M := pow_le_pow_left₀ (by positivity)
        (by simpa [add_comm] using Real.add_one_le_exp t) M
      _ = Real.exp (K : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [t]
        field_simp [hM0.ne']
  have hw := (binomial_partial_sum_weighted M K hKM t ht0.le ht1).trans he
  have hl := Real.log_le_log (mul_pos (pow_pos ht0 _) hs0) hw
  rw [Real.log_mul (pow_pos ht0 _).ne' hs0.ne', Real.log_pow, Real.log_exp] at hl
  have htlog : Real.log t = Real.log (K : ℝ) - Real.log (M : ℝ) :=
    Real.log_div hK0.ne' hM0.ne'
  have hlog : Real.log ((M : ℝ) / K) = Real.log (M : ℝ) - Real.log (K : ℝ) :=
    Real.log_div hM0.ne' hK0.ne'
  apply (Real.log_le_iff_le_exp hs0).mp
  rw [hlog]
  rw [htlog] at hl
  nlinarith

/-- The last prime in the support, with value zero for the empty support. -/
def primeEnd (N : ℕ) : ℕ := N.primeFactors.sup id

/-- Missing primes above the small-prime cutoff in the support prefix. -/
def upperHoles (N L : ℕ) : Finset ℕ :=
  (Finset.range (primeEnd N + 1)).filter (fun q => q.Prime ∧ L ≤ q ∧ ¬q ∣ N)

/-- The prime prefix endpoint, all small exponents, and the omitted large primes. -/
def primeCode (L N : ℕ) : ℕ × (Fin L → ℕ) × Finset ℕ :=
  (primeEnd N, (fun q => N.factorization q), upperHoles N L)

/-- An integer with only squarefree large prime factors is recovered from its code. -/
theorem primeCode_injective_on (L : ℕ) :
    Set.InjOn (primeCode L) {N : ℕ | N ≠ 0 ∧
      ∀ q : ℕ, L ≤ q → N.factorization q ≤ 1} := by
  intro N hN M hM heq
  have he : primeEnd N = primeEnd M := congrArg Prod.fst heq
  have hs : (fun q : Fin L => N.factorization q) =
      (fun q : Fin L => M.factorization q) := congrArg (fun z => z.2.1) heq
  have hh : upperHoles N L = upperHoles M L := congrArg (fun z => z.2.2) heq
  apply Nat.eq_of_factorization_eq hN.1 hM.1
  intro q
  by_cases hqL : q < L
  · exact congrFun hs ⟨q, hqL⟩
  have hLq : L ≤ q := by omega
  by_cases hp : q.Prime
  · have hvN := hN.2 q hLq
    have hvM := hM.2 q hLq
    by_cases hqe : q ≤ primeEnd N
    · have hmem : q ∈ upperHoles N L ↔ q ∈ upperHoles M L := by rw [hh]
      simp only [upperHoles, Finset.mem_filter, Finset.mem_range, hp, hLq,
        Nat.lt_succ_iff, hqe, ← he, true_and] at hmem
      have hd : q ∣ N ↔ q ∣ M := not_iff_not.mp hmem
      rw [hp.dvd_iff_one_le_factorization hN.1,
        hp.dvd_iff_one_le_factorization hM.1] at hd
      omega
    · have hn : N.factorization q = 0 := by
        by_contra hz
        have hmem : q ∈ N.primeFactors := by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          exact hz
        have hle : q ≤ primeEnd N := Finset.le_sup (f := id) hmem
        exact hqe hle
      have hm : M.factorization q = 0 := by
        by_contra hz
        have hmem : q ∈ M.primeFactors := by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          exact hz
        have hle : q ≤ primeEnd M := Finset.le_sup (f := id) hmem
        exact hqe (hle.trans_eq he.symm)
      rw [hn, hm]
  · rw [Nat.factorization_eq_zero_of_not_prime N hp,
      Nat.factorization_eq_zero_of_not_prime M hp]

/-- A finite collection of integers with bounded codes satisfies the coding bound. -/
theorem prime_code_card_bound (s : Finset ℕ) (M L A K : ℕ)
    (hzero : ∀ N ∈ s, N ≠ 0)
    (hend : ∀ N ∈ s, primeEnd N < M)
    (hsmall : ∀ N ∈ s, ∀ q : Fin L, N.factorization q ≤ A)
    (hlarge : ∀ N ∈ s, ∀ q : ℕ, L ≤ q → N.factorization q ≤ 1)
    (hholes : ∀ N ∈ s, (upperHoles N L).card ≤ K) :
    s.card ≤ M * (A + 1) ^ L * (∑ j ∈ Finset.range (K + 1), M.choose j) := by
  let small : Finset (Fin L → ℕ) := Fintype.piFinset (fun _ => Finset.range (A + 1))
  let target := (Finset.range M).product (small.product ((Finset.range M).powerset.filter (fun H => H.card ≤ K)))
  have hcode : ∀ N ∈ s, primeCode L N ∈ target := by
    intro N hN
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (hend N hN), Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · simp only [small, Fintype.mem_piFinset, Finset.mem_range]
      intro q
      exact Nat.lt_succ_of_le (hsmall N hN q)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, hholes N hN⟩
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hlt := Finset.mem_range.mp hq'.1
      exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_lt_succ hlt) (hend N hN))
  have hinj : Set.InjOn (primeCode L) (↑s : Set ℕ) := by
    apply (primeCode_injective_on L).mono
    intro N hN
    exact ⟨hzero N hN, hlarge N hN⟩
  have hc := Finset.card_le_card_of_injOn (primeCode L) hcode hinj
  dsimp only [target] at hc
  simp only [Finset.product_eq_sprod] at hc
  rw [Finset.card_product, Finset.card_product, Finset.card_range,
    small_subsets_card, Finset.card_range] at hc
  have hsmallcard : small.card = (A + 1) ^ L := by
    dsimp only [small]
    simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hsmallcard] at hc
  simpa only [mul_assoc] using hc

end D5.S3.Arith.Robin.GronwallAbundant
