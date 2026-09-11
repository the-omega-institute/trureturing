/- GID: D5/S3/Arith/Congruence/PowerResidueRecursionFour
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/PowerResidueRecursionFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The recursively defined A374911 sequence takes value four exactly at three and nine. -/

import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith


namespace D5.S3.Arith.Congruence.PowerResidueRecursionFour

/-- The original recursion, with the zero case guarding both recursive calls. -/
def seq (n : ℕ) : ℕ :=
  if _h : n = 0 then 1 else seq (2 ^ n % n) + seq (3 ^ n % n)
termination_by n
decreasing_by all_goals exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

private theorem seq_zero : seq 0 = 1 := by rw [seq, dif_pos rfl]

private theorem seq_rec {n : ℕ} (hn : n ≠ 0) :
    seq n = seq (2 ^ n % n) + seq (3 ^ n % n) := by rw [seq, dif_neg hn]

private theorem seq_one : seq 1 = 2 := by norm_num [seq_rec, seq_zero]

private theorem seq_pos (n : ℕ) : 0 < seq n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; rw [seq_zero]; omega
    · rw [seq_rec hn]
      have h₂ := ih (2 ^ n % n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
      have h₃ := ih (3 ^ n % n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
      omega

/-- Zero is the unique index with value one. -/
theorem seq_eq_one (n : ℕ) : seq n = 1 ↔ n = 0 := by
  by_cases hn : n = 0
  · simp [hn, seq_zero]
  · rw [seq_rec hn]
    have := seq_pos (2 ^ n % n)
    have := seq_pos (3 ^ n % n)
    omega

/-- One is the unique index with value two. -/
theorem seq_eq_two (n : ℕ) : seq n = 2 ↔ n = 1 := by
  constructor
  · intro hs
    have hn : n ≠ 0 := by intro hn; simp [hn, seq_zero] at hs
    have hr := seq_rec hn
    have h₂ := seq_pos (2 ^ n % n)
    have h₃ := seq_pos (3 ^ n % n)
    have hz₂ := (seq_eq_one _).mp (show seq (2 ^ n % n) = 1 by omega)
    have hz₃ := (seq_eq_one _).mp (show seq (3 ^ n % n) = 1 by omega)
    apply Nat.eq_one_of_dvd_coprimes (a := 2 ^ n) (b := 3 ^ n)
      ((by decide : Nat.Coprime 2 3).pow n n)
    · exact Nat.dvd_of_mod_eq_zero hz₂
    · exact Nat.dvd_of_mod_eq_zero hz₃
  · rintro rfl; exact seq_one

private theorem two_pow_self_mod_ne_one {n : ℕ} (hn : 1 < n) : 2 ^ n % n ≠ 1 := by
  intro h
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hm : Nat.ModEq p (2 ^ n) 1 :=
    (show Nat.ModEq n (2 ^ n) 1 by simpa [Nat.ModEq, Nat.mod_eq_of_lt hn] using h).of_dvd
      (Nat.minFac_dvd n)
  have hz : (2 : ZMod p) ^ n = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 p).mpr hm
  have hne : (2 : ZMod p) ≠ 0 := by
    intro heq
    simp [heq, zero_pow (by omega : n ≠ 0)] at hz
  have hd₁ := orderOf_dvd_of_pow_eq_one hz
  have hd₂ := ZMod.orderOf_dvd_card_sub_one hne
  have hc : n.Coprime (p - 1) := Nat.coprime_of_lt_minFac (by have := hp.two_le; omega)
    (by have := hp.two_le; dsimp [p] at *; omega)
  have hd := Nat.dvd_gcd hd₁ hd₂
  rw [hc.gcd_eq_one] at hd
  have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have h10 : (1 : ZMod p) = 0 := by linear_combination h21
  exact one_ne_zero h10

private theorem three_pow_dvd_two_pow_add_one (k : ℕ) : 3 ^ k ∣ 2 ^ (3 ^ k) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide : Odd 3) (by decide) (by decide) ((by decide : Odd 3).pow : Odd (3 ^ k))
  have hv : padicValNat 3 (2 ^ (3 ^ k) + 1) = 1 + k := by
    simpa using h
  apply (padicValNat_dvd_iff_le (by positivity : 2 ^ (3 ^ k) + 1 ≠ 0)).mpr
  omega

private theorem three_pow_self_mod_two_pow (k : ℕ) :
    3 ^ (2 ^ (k + 1)) % (2 ^ (k + 1)) = 1 := by
  have hc : Nat.Coprime 3 (2 ^ (k + 1)) := (by decide : Nat.Coprime 3 2).pow_right _
  have h := (Nat.ModEq.pow_totient hc).pow 2
  rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 2)] at h
  simp only [Nat.reduceSub, mul_one, one_pow, ← pow_mul, ← pow_succ] at h
  exact Nat.mod_eq_of_modEq h (one_lt_pow₀ (by decide) (by omega))

/-- Value three occurs precisely at the positive powers of two. -/
theorem seq_eq_three (n : ℕ) : seq n = 3 ↔ ∃ k : ℕ, 0 < k ∧ n = 2 ^ k := by
  constructor
  · intro hs
    have hn : 1 < n := by
      have hn₀ : n ≠ 0 := by intro h; simp [h, seq_zero] at hs
      have hn₁ : n ≠ 1 := by intro h; simp [h, seq_one] at hs
      omega
    have hr := seq_rec (by omega : n ≠ 0)
    have h₂ := seq_pos (2 ^ n % n)
    have h₃ := seq_pos (3 ^ n % n)
    have hl : seq (2 ^ n % n) = 1 := by
      have hne : seq (2 ^ n % n) ≠ 2 := by
        intro heq
        exact two_pow_self_mod_ne_one hn ((seq_eq_two _).mp heq)
      omega
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (Nat.dvd_of_mod_eq_zero ((seq_eq_one _).mp hl))
    refine ⟨k, ?_, hk⟩
    by_contra h
    have hz : k = 0 := by omega
    simp only [hz, pow_zero] at hk
    omega
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [seq_rec (by positivity : 2 ^ (t + 1) ≠ 0),
      Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 (Nat.le_of_lt (Nat.lt_two_pow_self))),
      three_pow_self_mod_two_pow, seq_zero, seq_one]

private theorem two_pow_self_mod_three_pow (k : ℕ) :
    2 ^ (3 ^ k) % (3 ^ k) = 3 ^ k - 1 := by
  have hm : 0 < 3 ^ k := by positivity
  have hr := Nat.mod_lt (2 ^ (3 ^ k)) hm
  have hd := Nat.mod_eq_zero_of_dvd (three_pow_dvd_two_pow_add_one k)
  have hd' : 3 ^ k ∣ 2 ^ (3 ^ k) % (3 ^ k) + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod, Nat.mod_mod] using hd
  have := Nat.le_of_dvd (by omega : 0 < 2 ^ (3 ^ k) % (3 ^ k) + 1) hd'
  omega

private theorem three_pow_gt_linear {k : ℕ} (hk : 3 ≤ k) : 4 * k + 1 < 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

private theorem three_pow_sub_one_eq_two_pow {k j : ℕ} (hk : 0 < k)
    (heq : 3 ^ k - 1 = 2 ^ j) : k = 1 ∨ k = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra h
  have hk₃ : 3 ≤ k := by omega
  have hg := three_pow_gt_linear hk₃
  by_cases heven : Even k
  · have hv := padicValNat.pow_two_sub_one (x := 3) (n := k)
      (by decide) (by decide) (by omega) heven
    have hv₄ : padicValNat 2 4 = 2 := by
      change padicValNat 2 (2 ^ 2) = 2
      exact padicValNat.prime_pow 2
    norm_num [heq, hv₄] at hv
    have hj : j = 2 + padicValNat 2 k := by omega
    have hle : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
    have hbound : 2 ^ j ≤ 4 * k := by
      rw [hj, pow_add]
      exact Nat.mul_le_mul_left 4 hle
    omega
  · obtain ⟨t, ht⟩ := Nat.not_even_iff_odd.mp heven
    have hm : 3 ^ k % 4 = 3 := by
      rw [ht, pow_add, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    have hp : 3 ^ k = 2 ^ j + 1 := by omega
    have hj₂ : 2 ≤ j := by
      by_contra h
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> norm_num at hp <;> omega
    have hd : 4 ∣ 2 ^ j := pow_dvd_pow 2 hj₂
    have hmod := congrArg (fun x : ℕ => x % 4) hp
    rw [hm, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd] at hmod
    norm_num at hmod

/-- The complete classification asked for in OEIS A374911. -/
theorem a374911_eq_four (n : ℕ) : seq n = 4 ↔ n = 3 ∨ n = 9 := by
  constructor
  · intro hs
    have hn : 1 < n := by
      have hn₀ : n ≠ 0 := by intro h; simp [h, seq_zero] at hs
      have hn₁ : n ≠ 1 := by intro h; simp [h, seq_one] at hs
      omega
    have hr := seq_rec (by omega : n ≠ 0)
    have h₂ := seq_pos (2 ^ n % n)
    have h₃ := seq_pos (3 ^ n % n)
    have hl₁ : seq (2 ^ n % n) ≠ 1 := by
      intro hl
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (Nat.dvd_of_mod_eq_zero ((seq_eq_one _).mp hl))
      have hkpos : 0 < k := by
        by_contra h
        have hz : k = 0 := by omega
        simp only [hz, pow_zero] at hk
        omega
      have := (seq_eq_three n).mpr ⟨k, hkpos, hk⟩
      omega
    have hl₂ : seq (2 ^ n % n) ≠ 2 := by
      intro hl
      exact two_pow_self_mod_ne_one hn ((seq_eq_two _).mp hl)
    have hl : seq (2 ^ n % n) = 3 := by omega
    have hz := (seq_eq_one _).mp (show seq (3 ^ n % n) = 1 by omega)
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (Nat.dvd_of_mod_eq_zero hz)
    have hkpos : 0 < k := by
      by_contra h
      have hz : k = 0 := by omega
      simp only [hz, pow_zero] at hk
      omega
    obtain ⟨j, _, hj⟩ := (seq_eq_three _).mp hl
    rw [hk, two_pow_self_mod_three_pow] at hj
    rcases three_pow_sub_one_eq_two_pow hkpos hj with h | h
    · left; simpa [h] using hk
    · right; simpa [h] using hk
  · rintro (rfl | rfl) <;> norm_num [seq_rec, seq_zero]

#print axioms seq_eq_one
#print axioms seq_eq_two
#print axioms seq_eq_three
#print axioms a374911_eq_four

end D5.S3.Arith.Congruence.PowerResidueRecursionFour
