/- GID: D5/S3/Arith/Congruence/WuA227244C2Equality
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/WuA227244C2Equality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The least prime divisor on the entire 220n+8 progression is 47. -/

import D5.S3.Arith.Primes.WuA227244ConjectureFour
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace D5.S3.Arith.Congruence.WuA227244C2Equality

private def G (m : ℕ) : ℤ := ((2 : ℤ) ^ (2 ^ m) + 1) * 2 ^ (2 ^ (2 ^ m)) - 1

private def reduced (q d p L r : ℕ) : ZMod q :=
  ((2 : ZMod q) ^ (2^(220*r+8)%d) + 1) *
    2 ^ (2^(p+2^(220*r+8)%p)%d) - 1

private lemma formula_reduce (q d p L n : ℕ)
    (hq : (2 : ZMod q)^d=1)
    (ht : (2 : ZMod d)^(p+p)=(2 : ZMod d)^p)
    (hd : (2 : ZMod d)^(220*L+8)=(2 : ZMod d)^8)
    (hp : (2 : ZMod p)^(220*L+8)=(2 : ZMod p)^8)
    (hsmall : p ≤ 2^8) :
    (G (220*n+8) : ZMod q) = reduced q d p L (n%L) := by
  let m := 220*n+8
  let mr := 220*(n%L)+8
  have hD : 2^m%d=2^mr%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      D5.S3.Arith.Primes.WuA227244ConjectureFour.progression_reduce (2 : ZMod d) 220 8 L n hd
  have hP : 2^m%p=2^mr%p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      D5.S3.Arith.Primes.WuA227244ConjectureFour.progression_reduce (2 : ZMod p) 220 8 L n hp
  have he : p ≤ 2^m := by
    have hm : 8 ≤ m := by dsimp [m]; omega
    exact hsmall.trans (Nat.pow_le_pow_right (by decide) hm)
  have hB : 2^(2^m)%d=2^(p+2^mr%p)%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    push_cast
    rw [D5.S3.Arith.Primes.WuA227244ConjectureFour.tail_reduce (2 : ZMod d) p (2^m) ht he, hP]
  have hA : (2 : ZMod q)^(2^m)=(2 : ZMod q)^(2^mr%d) := by
    rw [pow_eq_pow_mod (2^m) hq, hD]
  change (((((2 : ℤ)^(2^m)+1)*2^(2^(2^m))-1) : ℤ) : ZMod q) = _
  push_cast
  rw [hA, pow_eq_pow_mod (2^(2^m)) hq, hB]
  rfl

private lemma residue_3 (n : ℕ) : (G (220*n+8) : ZMod 3) = reduced 3 2 1 1 (n%1) := by
  exact formula_reduce 3 2 1 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_3 (n : ℕ) : (G (220*n+8) : ZMod 3) ≠ 0 := by
  rw [residue_3]
  simp only [Nat.mod_one]
  decide
private lemma residue_5 (n : ℕ) : (G (220*n+8) : ZMod 5) = reduced 5 4 2 1 (n%1) := by
  exact formula_reduce 5 4 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_5 (n : ℕ) : (G (220*n+8) : ZMod 5) ≠ 0 := by
  rw [residue_5]
  simp only [Nat.mod_one]
  decide
private lemma residue_7 (n : ℕ) : (G (220*n+8) : ZMod 7) = reduced 7 6 2 1 (n%1) := by
  exact formula_reduce 7 6 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_7 (n : ℕ) : (G (220*n+8) : ZMod 7) ≠ 0 := by
  rw [residue_7]
  simp only [Nat.mod_one]
  decide
private lemma residue_11 (n : ℕ) : (G (220*n+8) : ZMod 11) = reduced 11 10 4 1 (n%1) := by
  exact formula_reduce 11 10 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_11 (n : ℕ) : (G (220*n+8) : ZMod 11) ≠ 0 := by
  rw [residue_11]
  simp only [Nat.mod_one]
  decide
private lemma residue_13 (n : ℕ) : (G (220*n+8) : ZMod 13) = reduced 13 12 2 1 (n%1) := by
  exact formula_reduce 13 12 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_13 (n : ℕ) : (G (220*n+8) : ZMod 13) ≠ 0 := by
  rw [residue_13]
  simp only [Nat.mod_one]
  decide
private lemma residue_17 (n : ℕ) : (G (220*n+8) : ZMod 17) = reduced 17 16 4 1 (n%1) := by
  exact formula_reduce 17 16 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_17 (n : ℕ) : (G (220*n+8) : ZMod 17) ≠ 0 := by
  rw [residue_17]
  simp only [Nat.mod_one]
  decide
private lemma residue_19 (n : ℕ) : (G (220*n+8) : ZMod 19) = reduced 19 18 6 3 (n%3) := by
  exact formula_reduce 19 18 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_19 (n : ℕ) : (G (220*n+8) : ZMod 19) ≠ 0 := by
  rw [residue_19]
  have table : ∀ r : Fin 3, reduced 19 18 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_23 (n : ℕ) : (G (220*n+8) : ZMod 23) = reduced 23 22 10 1 (n%1) := by
  exact formula_reduce 23 22 10 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_23 (n : ℕ) : (G (220*n+8) : ZMod 23) ≠ 0 := by
  rw [residue_23]
  simp only [Nat.mod_one]
  decide
private lemma residue_29 (n : ℕ) : (G (220*n+8) : ZMod 29) = reduced 29 28 3 3 (n%3) := by
  exact formula_reduce 29 28 3 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_29 (n : ℕ) : (G (220*n+8) : ZMod 29) ≠ 0 := by
  rw [residue_29]
  have table : ∀ r : Fin 3, reduced 29 28 3 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_31 (n : ℕ) : (G (220*n+8) : ZMod 31) = reduced 31 30 4 1 (n%1) := by
  exact formula_reduce 31 30 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_31 (n : ℕ) : (G (220*n+8) : ZMod 31) ≠ 0 := by
  rw [residue_31]
  simp only [Nat.mod_one]
  decide
private lemma residue_37 (n : ℕ) : (G (220*n+8) : ZMod 37) = reduced 37 36 6 3 (n%3) := by
  exact formula_reduce 37 36 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_37 (n : ℕ) : (G (220*n+8) : ZMod 37) ≠ 0 := by
  rw [residue_37]
  have table : ∀ r : Fin 3, reduced 37 36 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_41 (n : ℕ) : (G (220*n+8) : ZMod 41) = reduced 41 40 4 1 (n%1) := by
  exact formula_reduce 41 40 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_41 (n : ℕ) : (G (220*n+8) : ZMod 41) ≠ 0 := by
  rw [residue_41]
  simp only [Nat.mod_one]
  decide
private lemma residue_43 (n : ℕ) : (G (220*n+8) : ZMod 43) = reduced 43 42 6 3 (n%3) := by
  exact formula_reduce 43 42 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_43 (n : ℕ) : (G (220*n+8) : ZMod 43) ≠ 0 := by
  rw [residue_43]
  have table : ∀ r : Fin 3, reduced 43 42 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_47 (n : ℕ) : (G (220*n+8) : ZMod 47) = reduced 47 46 11 1 (n%1) := by
  exact formula_reduce 47 46 11 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma divisible_47 (n : ℕ) : (47 : ℤ) ∣ G (220*n+8) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 47).mp
  rw [residue_47]
  simp only [Nat.mod_one]
  decide
private lemma nonzero_2 (n : ℕ) : (G (220*n+8) : ZMod 2) ≠ 0 := by
  have he : (2 : ℕ)^(2^(220*n+8)) ≠ 0 := by positivity
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [G, hz, zero_pow he]

theorem result : ∀ n : ℕ,
  Nat.Prime 47 ∧
  (47 : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (220*n+8)) + 1) *
    2 ^ (2 ^ (2 ^ (220*n+8))) - 1) ∧
  ∀ q : ℕ, Nat.Prime q →
    (q : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (220*n+8)) + 1) *
      2 ^ (2 ^ (2 ^ (220*n+8))) - 1) → 47 ≤ q := by
  change ∀ n : ℕ,
    Nat.Prime 47 ∧ (47 : ℤ) ∣ G (220*n+8) ∧
    ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ G (220*n+8) → 47 ≤ q
  intro n
  refine ⟨by norm_num, divisible_47 n, ?_⟩
  intro q hprime hdvd
  by_contra hbound
  have hq : q < 47 := by omega
  have hz : (G (220*n+8) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
  interval_cases q <;> norm_num at hprime
  · exact nonzero_2 n hz
  · exact nonzero_3 n hz
  · exact nonzero_5 n hz
  · exact nonzero_7 n hz
  · exact nonzero_11 n hz
  · exact nonzero_13 n hz
  · exact nonzero_17 n hz
  · exact nonzero_19 n hz
  · exact nonzero_23 n hz
  · exact nonzero_29 n hz
  · exact nonzero_31 n hz
  · exact nonzero_37 n hz
  · exact nonzero_41 n hz
  · exact nonzero_43 n hz

end D5.S3.Arith.Congruence.WuA227244C2Equality
