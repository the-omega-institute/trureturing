/- GID: D5/S3/Arith/OeisA400168PrimorialGap
   generality: I
   mirror-B: D5/B/S3/Arith/OeisA400168PrimorialGap
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/OeisA400168PrimorialGap.claim; result=D5/S3/Arith/OeisA400168PrimorialGap.result; claim=D5/S3/Arith/OeisA400168PrimorialGap.claim
   digest: The input 2^49 answers the A400168 existence question positively. -/

import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.OeisA400168PrimorialGap

/-- Product of the first `k` primes, indexed by count rather than prime value. -/
noncomputable def P : ℕ → ℕ
  | 0 => 1
  | k + 1 => primorial (Nat.nth Nat.Prime k)

/-- The first strict primorial threshold; in particular the length of zero is zero. -/
noncomputable def L (m : ℕ) : ℕ := Nat.find (show ∃ k, m < P k from by
  refine ⟨m + 1, ?_⟩
  change m < primorial (Nat.nth Nat.Prime m)
  exact lt_of_lt_of_le (by omega : m < m + 2)
    ((Nat.add_two_le_nth_prime m).trans le_primorial_self))

/-- The arithmetic derivative, including the empty factorizations at zero and one. -/
def D (n : ℕ) : ℕ := n.factorization.sum (fun p e => e * (n / p))

/-- Maximum over every positive-exponent prime-power divisor; the empty maximum is zero. -/
noncomputable def M (n : ℕ) : ℕ :=
  (n.divisors.filter IsPrimePow).sup (fun d => L (n / d))

/-- The universal negative answer to the question whether A400168 has a term above one. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → L (D n) ≤ M n + 1

/-- The original existence question has a positive answer at `n = 2^49`. -/
theorem result : Not claim := by
  classical
  have hPmono : Monotone P := by
    intro a b hab
    cases a with
    | zero =>
      cases b with
      | zero => exact le_rfl
      | succ b => exact primorial_pos _
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        exact primorial_mono
          (Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega))
  have hP12 : P 12 = 7420738134810 := by
    have hc : Nat.count Nat.Prime 37 = 11 := by decide +kernel
    have hp : Nat.nth Nat.Prime 11 = 37 := by
      simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 37)
    change primorial (Nat.nth Nat.Prime 11) = _
    rw [hp]
    decide +kernel
  have hP13 : P 13 = 304250263527210 := by
    have hc : Nat.count Nat.Prime 41 = 12 := by decide +kernel
    have hp : Nat.nth Nat.Prime 12 = 41 := by
      simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 41)
    change primorial (Nat.nth Nat.Prime 12) = _
    rw [hp]
    decide +kernel
  have hP14 : P 14 = 13082761331670030 := by
    have hc : Nat.count Nat.Prime 43 = 13 := by decide +kernel
    have hp : Nat.nth Nat.Prime 13 = 43 := by
      simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 43)
    change primorial (Nat.nth Nat.Prime 13) = _
    rw [hp]
    decide +kernel
  have hP15 : P 15 = 614889782588491410 := by
    have hc : Nat.count Nat.Prime 47 = 14 := by decide +kernel
    have hp : Nat.nth Nat.Prime 14 = 47 := by
      simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 47)
    change primorial (Nat.nth Nat.Prime 14) = _
    rw [hp]
    decide +kernel
  have hD : D (2 ^ 49) = 13792273858822144 := by
    simp only [D, Nat.factorization_pow, Nat.prime_two.factorization]
    norm_num
  have hlength : ∀ m k, P k ≤ m → m < P (k + 1) → L m = k + 1 := by
    intro m k hlo hhi
    apply le_antisymm
    · exact Nat.find_min' _ hhi
    · apply Nat.le_of_not_gt
      intro hlt
      have hspec : m < P (L m) := by
        unfold L
        exact Nat.find_spec (p := fun k => m < P k) _
      have : P (L m) ≤ P k := hPmono (by omega)
      omega
  have hLhalf : L (2 ^ 48) = 13 := by
    apply hlength (2 ^ 48) 12 <;> norm_num [hP12, hP13]
  have hLD : L (D (2 ^ 49)) = 15 := by
    rw [hD]
    apply hlength 13792273858822144 14 <;> norm_num [hP14, hP15]
  have hM : M (2 ^ 49) = 13 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro d hd
      obtain ⟨hdiv, hpp⟩ := Finset.mem_filter.mp hd
      obtain ⟨e, he, rfl⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two 49).mp hdiv
      have hepos : 0 < e := by
        by_contra h
        have hezero : e = 0 := by omega
        simp only [hezero, pow_zero, not_isPrimePow_one] at hpp
      have hden : 2 ≤ 2 ^ e := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hepos
      have hquot : 2 ^ 49 / 2 ^ e ≤ 2 ^ 48 := by
        have h := Nat.div_le_div_left (a := 2 ^ 49) hden (by norm_num : 0 < 2)
        norm_num at h ⊢
        exact h
      exact Nat.find_min' _ (lt_of_le_of_lt hquot (by norm_num [hP13]))
    · have hd : 2 ∈ (2 ^ 49 : ℕ).divisors.filter IsPrimePow := by
        apply Finset.mem_filter.mpr
        refine ⟨?_, Nat.prime_two.isPrimePow⟩
        exact (Nat.mem_divisors_prime_pow Nat.prime_two 49).mpr ⟨1, by norm_num, by norm_num⟩
      have h := Finset.le_sup (f := fun d => L ((2 ^ 49 : ℕ) / d)) hd
      norm_num at h
      simpa only [M, show (562949953421312 : ℕ) = 2 ^ 49 by norm_num,
        show (281474976710656 : ℕ) = 2 ^ 48 by norm_num, hLhalf] using h
  intro hc
  have h := hc (2 ^ 49) (by norm_num)
  rw [hLD, hM] at h
  omega

#print axioms result

end D5.S3.Arith.OeisA400168PrimorialGap
