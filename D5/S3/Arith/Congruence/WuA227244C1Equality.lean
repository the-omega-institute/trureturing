/- GID: D5/S3/Arith/Congruence/WuA227244C1Equality
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/WuA227244C1Equality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The least prime divisor on the entire 20n+16 progression is 101. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace D5.S3.Arith.Congruence.WuA227244C1Equality

private def G (m : ℕ) : ℤ := ((2 : ℤ) ^ (2 ^ m) + 1) * 2 ^ (2 ^ (2 ^ m)) - 1

private lemma progression_reduce {M : Type*} [CommMonoid M] (a : M) (s t L n : ℕ)
    (h : a ^ (s*L+t) = a^t) :
    a^(s*n+t) = a^(s*(n%L)+t) := by
  have hp : Function.Periodic (fun k : ℕ => a^(s*k+t)) L := by
    intro k
    calc
      a^(s*(k+L)+t) = a^(s*k) * a^(s*L+t) := by
        rw [← pow_add]; congr 1 <;> ring
      _ = a^(s*k+t) := by rw [h, ← pow_add]
  exact (hp.map_mod_nat n).symm

private lemma tail_reduce {M : Type*} [CommMonoid M] (a : M) (p e : ℕ)
    (h : a^(p+p)=a^p) (he : p ≤ e) : a^e = a^(p+e%p) := by
  have hp : Function.Periodic (fun k : ℕ => a^(k+p)) p := by
    intro k
    calc
      a^(k+p+p) = a^k * a^(p+p) := by rw [← pow_add]; congr 1 <;> omega
      _ = a^(k+p) := by rw [h, ← pow_add]
  have hr : (e-p)%p=e%p := by
    conv_rhs => rw [← Nat.sub_add_cancel he]
    simp
  calc
    a^e = a^((e-p)+p) := by rw [Nat.sub_add_cancel he]
    _ = a^(((e-p)%p)+p) := (hp.map_mod_nat (e-p)).symm
    _ = a^(p+e%p) := by rw [hr, Nat.add_comm]

private def reduced (q d p L r : ℕ) : ZMod q :=
  ((2 : ZMod q) ^ (2^(20*r+16)%d) + 1) *
    2 ^ (2^(p+2^(20*r+16)%p)%d) - 1

private lemma formula_reduce (q d p L n : ℕ)
    (hq : (2 : ZMod q)^d=1)
    (ht : (2 : ZMod d)^(p+p)=(2 : ZMod d)^p)
    (hd : (2 : ZMod d)^(20*L+16)=(2 : ZMod d)^16)
    (hp : (2 : ZMod p)^(20*L+16)=(2 : ZMod p)^16)
    (hsmall : p ≤ 2^16) :
    (G (20*n+16) : ZMod q) = reduced q d p L (n%L) := by
  let m := 20*n+16
  let mr := 20*(n%L)+16
  have hD : 2^m%d=2^mr%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod d) 20 16 L n hd
  have hP : 2^m%p=2^mr%p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod p) 20 16 L n hp
  have he : p ≤ 2^m := by
    have hm : 16 ≤ m := by dsimp [m]; omega
    exact hsmall.trans (Nat.pow_le_pow_right (by decide) hm)
  have hB : 2^(2^m)%d=2^(p+2^mr%p)%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    push_cast
    rw [tail_reduce (2 : ZMod d) p (2^m) ht he, hP]
  have hA : (2 : ZMod q)^(2^m)=(2 : ZMod q)^(2^mr%d) := by
    rw [pow_eq_pow_mod (2^m) hq, hD]
  change (((((2 : ℤ)^(2^m)+1)*2^(2^(2^m))-1) : ℤ) : ZMod q) = _
  push_cast
  rw [hA, pow_eq_pow_mod (2^(2^m)) hq, hB]
  rfl

private lemma residue_3 (n : ℕ) : (G (20*n+16) : ZMod 3) = reduced 3 2 1 1 (n%1) := by
  exact formula_reduce 3 2 1 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_3 (n : ℕ) : (G (20*n+16) : ZMod 3) ≠ 0 := by
  rw [residue_3]
  simp only [Nat.mod_one]
  decide
private lemma residue_5 (n : ℕ) : (G (20*n+16) : ZMod 5) = reduced 5 4 2 1 (n%1) := by
  exact formula_reduce 5 4 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_5 (n : ℕ) : (G (20*n+16) : ZMod 5) ≠ 0 := by
  rw [residue_5]
  simp only [Nat.mod_one]
  decide
private lemma residue_7 (n : ℕ) : (G (20*n+16) : ZMod 7) = reduced 7 6 2 1 (n%1) := by
  exact formula_reduce 7 6 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_7 (n : ℕ) : (G (20*n+16) : ZMod 7) ≠ 0 := by
  rw [residue_7]
  simp only [Nat.mod_one]
  decide
private lemma residue_11 (n : ℕ) : (G (20*n+16) : ZMod 11) = reduced 11 10 4 1 (n%1) := by
  exact formula_reduce 11 10 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_11 (n : ℕ) : (G (20*n+16) : ZMod 11) ≠ 0 := by
  rw [residue_11]
  simp only [Nat.mod_one]
  decide
private lemma residue_13 (n : ℕ) : (G (20*n+16) : ZMod 13) = reduced 13 12 2 1 (n%1) := by
  exact formula_reduce 13 12 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_13 (n : ℕ) : (G (20*n+16) : ZMod 13) ≠ 0 := by
  rw [residue_13]
  simp only [Nat.mod_one]
  decide
private lemma residue_17 (n : ℕ) : (G (20*n+16) : ZMod 17) = reduced 17 16 4 1 (n%1) := by
  exact formula_reduce 17 16 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_17 (n : ℕ) : (G (20*n+16) : ZMod 17) ≠ 0 := by
  rw [residue_17]
  simp only [Nat.mod_one]
  decide
private lemma residue_19 (n : ℕ) : (G (20*n+16) : ZMod 19) = reduced 19 18 6 3 (n%3) := by
  exact formula_reduce 19 18 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_19 (n : ℕ) : (G (20*n+16) : ZMod 19) ≠ 0 := by
  rw [residue_19]
  have table : ∀ r : Fin 3, reduced 19 18 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_23 (n : ℕ) : (G (20*n+16) : ZMod 23) = reduced 23 22 10 1 (n%1) := by
  exact formula_reduce 23 22 10 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_23 (n : ℕ) : (G (20*n+16) : ZMod 23) ≠ 0 := by
  rw [residue_23]
  simp only [Nat.mod_one]
  decide
private lemma residue_29 (n : ℕ) : (G (20*n+16) : ZMod 29) = reduced 29 28 3 3 (n%3) := by
  exact formula_reduce 29 28 3 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_29 (n : ℕ) : (G (20*n+16) : ZMod 29) ≠ 0 := by
  rw [residue_29]
  have table : ∀ r : Fin 3, reduced 29 28 3 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_31 (n : ℕ) : (G (20*n+16) : ZMod 31) = reduced 31 30 4 1 (n%1) := by
  exact formula_reduce 31 30 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_31 (n : ℕ) : (G (20*n+16) : ZMod 31) ≠ 0 := by
  rw [residue_31]
  simp only [Nat.mod_one]
  decide
private lemma residue_37 (n : ℕ) : (G (20*n+16) : ZMod 37) = reduced 37 36 6 3 (n%3) := by
  exact formula_reduce 37 36 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_37 (n : ℕ) : (G (20*n+16) : ZMod 37) ≠ 0 := by
  rw [residue_37]
  have table : ∀ r : Fin 3, reduced 37 36 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_41 (n : ℕ) : (G (20*n+16) : ZMod 41) = reduced 41 40 4 1 (n%1) := by
  exact formula_reduce 41 40 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_41 (n : ℕ) : (G (20*n+16) : ZMod 41) ≠ 0 := by
  rw [residue_41]
  simp only [Nat.mod_one]
  decide
private lemma residue_43 (n : ℕ) : (G (20*n+16) : ZMod 43) = reduced 43 42 6 3 (n%3) := by
  exact formula_reduce 43 42 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_43 (n : ℕ) : (G (20*n+16) : ZMod 43) ≠ 0 := by
  rw [residue_43]
  have table : ∀ r : Fin 3, reduced 43 42 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_47 (n : ℕ) : (G (20*n+16) : ZMod 47) = reduced 47 46 11 11 (n%11) := by
  exact formula_reduce 47 46 11 11 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_47 (n : ℕ) : (G (20*n+16) : ZMod 47) ≠ 0 := by
  rw [residue_47]
  have table : ∀ r : Fin 11, reduced 47 46 11 11 r.val ≠ 0 := by decide
  exact table ⟨n%11, Nat.mod_lt _ (by decide)⟩
private lemma residue_53 (n : ℕ) : (G (20*n+16) : ZMod 53) = reduced 53 52 12 3 (n%3) := by
  exact formula_reduce 53 52 12 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_53 (n : ℕ) : (G (20*n+16) : ZMod 53) ≠ 0 := by
  rw [residue_53]
  have table : ∀ r : Fin 3, reduced 53 52 12 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_59 (n : ℕ) : (G (20*n+16) : ZMod 59) = reduced 59 58 28 21 (n%21) := by
  exact formula_reduce 59 58 28 21 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_59 (n : ℕ) : (G (20*n+16) : ZMod 59) ≠ 0 := by
  rw [residue_59]
  have table : ∀ r : Fin 21, reduced 59 58 28 21 r.val ≠ 0 := by decide
  exact table ⟨n%21, Nat.mod_lt _ (by decide)⟩
private lemma residue_61 (n : ℕ) : (G (20*n+16) : ZMod 61) = reduced 61 60 4 1 (n%1) := by
  exact formula_reduce 61 60 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_61 (n : ℕ) : (G (20*n+16) : ZMod 61) ≠ 0 := by
  rw [residue_61]
  simp only [Nat.mod_one]
  decide
private lemma residue_67 (n : ℕ) : (G (20*n+16) : ZMod 67) = reduced 67 66 10 1 (n%1) := by
  exact formula_reduce 67 66 10 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_67 (n : ℕ) : (G (20*n+16) : ZMod 67) ≠ 0 := by
  rw [residue_67]
  simp only [Nat.mod_one]
  decide
private lemma residue_71 (n : ℕ) : (G (20*n+16) : ZMod 71) = reduced 71 70 12 3 (n%3) := by
  exact formula_reduce 71 70 12 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_71 (n : ℕ) : (G (20*n+16) : ZMod 71) ≠ 0 := by
  rw [residue_71]
  have table : ∀ r : Fin 3, reduced 71 70 12 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_73 (n : ℕ) : (G (20*n+16) : ZMod 73) = reduced 73 72 6 3 (n%3) := by
  exact formula_reduce 73 72 6 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_73 (n : ℕ) : (G (20*n+16) : ZMod 73) ≠ 0 := by
  rw [residue_73]
  have table : ∀ r : Fin 3, reduced 73 72 6 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_79 (n : ℕ) : (G (20*n+16) : ZMod 79) = reduced 79 78 12 3 (n%3) := by
  exact formula_reduce 79 78 12 3 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_79 (n : ℕ) : (G (20*n+16) : ZMod 79) ≠ 0 := by
  rw [residue_79]
  have table : ∀ r : Fin 3, reduced 79 78 12 3 r.val ≠ 0 := by decide
  exact table ⟨n%3, Nat.mod_lt _ (by decide)⟩
private lemma residue_83 (n : ℕ) : (G (20*n+16) : ZMod 83) = reduced 83 82 20 1 (n%1) := by
  exact formula_reduce 83 82 20 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_83 (n : ℕ) : (G (20*n+16) : ZMod 83) ≠ 0 := by
  rw [residue_83]
  simp only [Nat.mod_one]
  decide
private lemma residue_89 (n : ℕ) : (G (20*n+16) : ZMod 89) = reduced 89 88 10 1 (n%1) := by
  exact formula_reduce 89 88 10 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_89 (n : ℕ) : (G (20*n+16) : ZMod 89) ≠ 0 := by
  rw [residue_89]
  simp only [Nat.mod_one]
  decide
private lemma residue_97 (n : ℕ) : (G (20*n+16) : ZMod 97) = reduced 97 96 6 1 (n%1) := by
  exact formula_reduce 97 96 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma nonzero_97 (n : ℕ) : (G (20*n+16) : ZMod 97) ≠ 0 := by
  rw [residue_97]
  simp only [Nat.mod_one]
  decide
private lemma residue_101 (n : ℕ) : (G (20*n+16) : ZMod 101) = reduced 101 100 20 1 (n%1) := by
  exact formula_reduce 101 100 20 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma divisible_101 (n : ℕ) : (101 : ℤ) ∣ G (20*n+16) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 101).mp
  rw [residue_101]
  simp only [Nat.mod_one]
  decide
private lemma nonzero_2 (n : ℕ) : (G (20*n+16) : ZMod 2) ≠ 0 := by
  have he : (2 : ℕ)^(2^(20*n+16)) ≠ 0 := by positivity
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [G, hz, zero_pow he]

theorem result : ∀ n : ℕ,
  Nat.Prime 101 ∧
  (101 : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (20*n+16)) + 1) *
    2 ^ (2 ^ (2 ^ (20*n+16))) - 1) ∧
  ∀ q : ℕ, Nat.Prime q →
    (q : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (20*n+16)) + 1) *
      2 ^ (2 ^ (2 ^ (20*n+16))) - 1) → 101 ≤ q := by
  change ∀ n : ℕ,
    Nat.Prime 101 ∧ (101 : ℤ) ∣ G (20*n+16) ∧
    ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ G (20*n+16) → 101 ≤ q
  intro n
  refine ⟨by norm_num, divisible_101 n, ?_⟩
  intro q hprime hdvd
  by_contra hbound
  have hq : q < 101 := by omega
  have hz : (G (20*n+16) : ZMod q) = 0 :=
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
  · exact nonzero_47 n hz
  · exact nonzero_53 n hz
  · exact nonzero_59 n hz
  · exact nonzero_61 n hz
  · exact nonzero_67 n hz
  · exact nonzero_71 n hz
  · exact nonzero_73 n hz
  · exact nonzero_79 n hz
  · exact nonzero_83 n hz
  · exact nonzero_89 n hz
  · exact nonzero_97 n hz

end D5.S3.Arith.Congruence.WuA227244C1Equality
