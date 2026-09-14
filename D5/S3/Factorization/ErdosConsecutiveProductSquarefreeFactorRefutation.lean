/- GID: D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   generality: I
   mirror-B: D5/B/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.NumberTheory.Primorial, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim; result=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result; claim=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim
   digest: The starting value 47 refutes uniqueness of Erdos's 23 in the consecutive-product question. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.ErdosConsecutiveProductSquarefreeFactorRefutation

/-- The product of the `k` integers immediately following `x`. -/
def P (x k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (x + i)

/-- The product of prime factors of `P x k` having exponent exactly one. -/
def v (x k : ℕ) : ℕ :=
  ∏ p ∈ (P x k).primeFactors.filter (fun p => (P x k).factorization p = 1), p

/-- The complementary product of prime powers having exponent at least two. -/
def u (x k : ℕ) : ℕ :=
  ∏ p ∈ (P x k).primeFactors.filter (fun p => 2 ≤ (P x k).factorization p),
    p ^ (P x k).factorization p

/-- The reported suggestion that 23 is the sole positive exceptional starting value. -/
def claim : Prop :=
  ∀ x : ℕ, 1 ≤ x → x ≠ 23 → ∃ k : ℕ, 1 ≤ k ∧ u x k < v x k

private theorem finite_cases (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 1) :
    v 47 k < u 47 k := by
  have hf : (P 47 k).factorization =
      ∑ i ∈ Finset.Icc 1 k, (47 + i).factorization := by
    unfold P
    apply Nat.factorization_prod
    intro i _
    omega
  have hs (S : Finset ℕ) :
      (∑ i ∈ S, (47 + i).factorization).support =
        S.biUnion (fun i => (47 + i).primeFactors) := by
    induction S using Finset.induction with
    | empty => simp
    | @insert i S hi ih =>
        simp only [Finset.sum_insert hi, Finset.biUnion_insert, Finsupp.support_add_eq_union,
          Nat.support_factorization, ih]
  simp only [v, u, ← Nat.support_factorization, hf, hs]
  interval_cases k <;> decide +kernel

private theorem tail_cases (k : ℕ) (hk : 119 ≤ k) : v 47 k < u 47 k := by
  have hn : P 47 k ≠ 0 := by
    unfold P
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    omega
  have hfac : (P 47 k).primeFactors ⊆ Nat.primesLE (47 + k) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hdivprod : p ∣ ∏ i ∈ Finset.Icc 1 k, (47 + i) := by
      simpa only [P] using hdiv
    obtain ⟨i, hi, hpi⟩ := (hprime.prime.dvd_finsetProd_iff (fun i => 47 + i)).mp hdivprod
    apply Nat.mem_primesLE.mpr
    have hibound : i ≤ k := (Finset.mem_Icc.mp hi).2
    exact ⟨(Nat.le_of_dvd (by omega : 0 < 47 + i) hpi).trans
      (Nat.add_le_add_left hibound 47), hprime⟩
  have hvle : v 47 k ≤ primorial (47 + k) := by
    unfold v
    rw [primorial_eq_prod_primesLE]
    have hs : (P 47 k).primeFactors.filter
        (fun p => (P 47 k).factorization p = 1) ⊆ Nat.primesLE (47 + k) := by
      intro p hp
      exact hfac (Finset.mem_filter.mp hp).1
    exact Nat.le_of_dvd (primorial_pos _) <|
      Finset.prod_dvd_prod_of_subset _ _ _ hs
  have hPbound : 48 ^ k ≤ P 47 k := by
    unfold P
    have h : (∏ _i ∈ Finset.Icc 1 k, (48 : ℕ)) ≤
        ∏ i ∈ Finset.Icc 1 k, (47 + i) := by
      apply Finset.prod_le_prod
      · intro i _; omega
      · intro i hi; have := Finset.mem_Icc.mp hi; omega
    simpa [Finset.prod_const, Nat.card_Icc] using h
  have hpow : 16 ^ (47 + k) < 48 ^ k := by
    have h3 : 16 ^ 47 < 3 ^ k := by
      calc
        16 ^ 47 < 3 ^ 119 := by norm_num
        _ ≤ 3 ^ k := pow_le_pow_right' (by omega) hk
    calc
      16 ^ (47 + k) = 16 ^ 47 * 16 ^ k := pow_add ..
      _ < 3 ^ k * 16 ^ k := Nat.mul_lt_mul_of_pos_right h3 (pow_pos (by omega) _)
      _ = 48 ^ k := by rw [← mul_pow]; norm_num
  have hsq : v 47 k * v 47 k ≤ 16 ^ (47 + k) := by
    have hbound := hvle.trans (primorial_le_four_pow (47 + k))
    calc
      v 47 k * v 47 k ≤ 4 ^ (47 + k) * 4 ^ (47 + k) := Nat.mul_le_mul hbound hbound
      _ = 16 ^ (47 + k) := by rw [← mul_pow]; norm_num
  have hdecomp : u 47 k * v 47 k = P 47 k := by
    have hpos (p : ℕ) (hp : p ∈ (P 47 k).primeFactors) :
        0 < (P 47 k).factorization p := by
      have : p ∈ (P 47 k).factorization.support := by simpa using hp
      exact Finsupp.mem_support_iff.mp this |> Nat.pos_of_ne_zero
    unfold u v
    rw [mul_comm]
    calc
      (∏ p ∈ (P 47 k).primeFactors with (P 47 k).factorization p = 1, p) *
          (∏ p ∈ (P 47 k).primeFactors with 2 ≤ (P 47 k).factorization p,
            p ^ (P 47 k).factorization p) =
        (∏ p ∈ (P 47 k).primeFactors with (P 47 k).factorization p = 1,
            p ^ (P 47 k).factorization p) *
        (∏ p ∈ (P 47 k).primeFactors with ¬ (P 47 k).factorization p = 1,
            p ^ (P 47 k).factorization p) := by
          congr 1
          · apply Finset.prod_congr rfl
            intro p hp
            simp only [Finset.mem_filter] at hp
            simp [hp.2]
          · apply Finset.prod_congr
            · ext p; simp only [Finset.mem_filter]; constructor
              · intro ⟨hp, he⟩; exact ⟨hp, by omega⟩
              · intro ⟨hp, he⟩; exact ⟨hp, by have := hpos p hp; omega⟩
            intro p _
            rfl
      _ = ∏ p ∈ (P 47 k).primeFactors, p ^ (P 47 k).factorization p :=
        Finset.prod_filter_mul_prod_filter_not _ _ _
      _ = P 47 k := (Nat.prod_primeFactors_pow_factorization hn).symm
  have hlarge : v 47 k * v 47 k < u 47 k * v 47 k := by
    rw [hdecomp]
    exact (hsq.trans_lt hpow).trans_le hPbound
  have hvpos : 0 < v 47 k := by
    unfold v
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  exact (Nat.mul_lt_mul_right hvpos).mp hlarge

end D5.S3.Factorization.ErdosConsecutiveProductSquarefreeFactorRefutation
