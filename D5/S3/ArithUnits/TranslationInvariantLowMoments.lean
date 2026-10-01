/- GID: D5/S3/ArithUnits/TranslationInvariantLowMoments
   generality: G
   mirror-B: D5/B/S3/ArithUnits/TranslationInvariantLowMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Translation invariance annihilates power moments below the characteristic boundary. -/

import Mathlib

/- Library search (2026-09-29): `FiniteField.sum_pow_lt_card_sub_one` treats the
   entire finite field. The source below treats arbitrary finite subsets of any
   field of characteristic p that are invariant under one nonzero translation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.TranslationInvariantLowMoments

open Classical in
/-- A finite set preserved by a nonzero translation has zero power moments
strictly below the first characteristic resonance. -/
theorem power_sum_eq_zero_of_add_invariant
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (S : Finset K) (a : K) (k : ℕ)
    (ha : a ≠ 0)
    (hinv : S.image (fun x => x + a) = S)
    (hk : k + 1 < p) :
    ∑ x ∈ S, x ^ k = 0 := by
  classical
  let M : ℕ → K := fun n => ∑ x ∈ S, x ^ n
  have hinj : Function.Injective (fun x : K => x + a) :=
    fun _ _ h => add_right_cancel h
  have hshift (n : ℕ) : M n = ∑ x ∈ S, (x + a) ^ n := by
    change (∑ x ∈ S, x ^ n) = _
    calc
      (∑ x ∈ S, x ^ n) = ∑ x ∈ S.image (fun x => x + a), x ^ n := by rw [hinv]
      _ = ∑ x ∈ S, (x + a) ^ n := by rw [Finset.sum_image hinj.injOn]
  have hbin (n : ℕ) :
      (∑ x ∈ S, (x + a) ^ n) =
        ∑ i ∈ Finset.range (n + 1), a ^ (n - i) * (n.choose i : K) * M i := by
    calc
      (∑ x ∈ S, (x + a) ^ n) =
          ∑ x ∈ S, ∑ i ∈ Finset.range (n + 1),
            x ^ i * a ^ (n - i) * (n.choose i : K) := by simp_rw [add_pow]
      _ = ∑ i ∈ Finset.range (n + 1), a ^ (n - i) * (n.choose i : K) * M i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [M, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hrec (n : ℕ) :
      (∑ i ∈ Finset.range n, a ^ (n - i) * (n.choose i : K) * M i) = 0 := by
    have heq :
        (∑ i ∈ Finset.range (n + 1), a ^ (n - i) * (n.choose i : K) * M i) =
          M n := (hbin n).symm.trans (hshift n).symm
    rw [Finset.sum_range_succ] at heq
    have h :
        (∑ i ∈ Finset.range n, a ^ (n - i) * (n.choose i : K) * M i) + M n =
          M n := by simpa using heq
    linear_combination h
  have hall : ∀ j : ℕ, j + 1 < p → M j = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have hzero :
          (∑ i ∈ Finset.range j,
            a ^ (j + 1 - i) * ((j + 1).choose i : K) * M i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hip : i + 1 < p := by omega
        simp [ih i hij hip]
      have h := hrec (j + 1)
      rw [Finset.sum_range_succ, hzero] at h
      have hprod : a * ((j + 1 : ℕ) : K) * M j = 0 := by
        simpa [Nat.choose_succ_self_right] using h
      have hcast : ((j + 1 : ℕ) : K) ≠ 0 := by
        intro hc
        have hdiv : p ∣ j + 1 := (CharP.cast_eq_zero_iff K p (j + 1)).mp hc
        exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos j) hj) hdiv
      exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ha hcast)
  simpa only [M] using hall k hk

#print axioms power_sum_eq_zero_of_add_invariant

end D5.S3.ArithUnits.TranslationInvariantLowMoments
