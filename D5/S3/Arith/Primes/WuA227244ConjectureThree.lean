/- GID: D5/S3/Arith/Primes/WuA227244ConjectureThree
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/WuA227244ConjectureThree
   mirror-E: none(waiver:unbounded-modular-reduction)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Arith/Primes/WuA227244ConjectureThree.result; instance=D5/S3/Arith/Primes/WuA227244ConjectureThree.reduced
   digest: Under two independent progression noncoverage hypotheses, 149 is the least prime divisor. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace D5.S3.Arith.Primes.WuA227244ConjectureThree

def G (m : ℕ) : ℤ := ((2 : ℤ) ^ (2 ^ m) + 1) * 2 ^ (2 ^ (2 ^ m)) - 1

private theorem progression_reduce {M : Type*} [CommMonoid M] (a : M) (s t L n : ℕ)
    (h : a ^ (s*L+t) = a^t) :
    a^(s*n+t) = a^(s*(n%L)+t) := by
  have hp : Function.Periodic (fun k : ℕ => a^(s*k+t)) L := by
    intro k
    calc
      a^(s*(k+L)+t) = a^(s*k) * a^(s*L+t) := by
        rw [← pow_add]; congr 1 <;> ring
      _ = a^(s*k+t) := by rw [h, ← pow_add]
  exact (hp.map_mod_nat n).symm

private theorem tail_reduce {M : Type*} [CommMonoid M] (a : M) (p e : ℕ)
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

def reduced (q d p L r : ℕ) : ZMod q :=
  ((2 : ZMod q) ^ (2^(72*r+32)%d) + 1) *
    2 ^ (2^(p+2^(72*r+32)%p)%d) - 1

private theorem formula_reduce (q d p L n : ℕ)
    (hq : (2 : ZMod q)^d=1)
    (ht : (2 : ZMod d)^(p+p)=(2 : ZMod d)^p)
    (hd : (2 : ZMod d)^(72*L+32)=(2 : ZMod d)^32)
    (hp : (2 : ZMod p)^(72*L+32)=(2 : ZMod p)^32)
    (hsmall : p ≤ 2^32) :
    (G (72*n+32) : ZMod q) = reduced q d p L (n%L) := by
  let m := 72*n+32
  let mr := 72*(n%L)+32
  have hD : 2^m%d=2^mr%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod d) 72 32 L n hd
  have hP : 2^m%p=2^mr%p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod p) 72 32 L n hp
  have he : p ≤ 2^m := by
    have hm : 32 ≤ m := by dsimp [m]; omega
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

private theorem noncoverage_C1 (n : ℕ)
    (h : ¬ ∃ k : ℕ, 72*n+32 = 20*k+16) : n%5 ≠ 2 := by
  intro hr
  apply h
  refine ⟨18*(n/5)+8, ?_⟩
  omega

private theorem noncoverage_C2 (n : ℕ)
    (h : ¬ ∃ k : ℕ, 72*n+32 = 220*k+8) : n%55 ≠ 18 := by
  intro hr
  apply h
  refine ⟨18*(n/55)+6, ?_⟩
  omega

private theorem residue_3 (n : ℕ) : (G (72*n+32) : ZMod 3) = reduced 3 2 1 1 (n%1) := by
  exact formula_reduce 3 2 1 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_3 (n : ℕ) : (G (72*n+32) : ZMod 3) ≠ 0 := by
  rw [residue_3]
  simp only [Nat.mod_one]
  decide
private theorem residue_5 (n : ℕ) : (G (72*n+32) : ZMod 5) = reduced 5 4 2 1 (n%1) := by
  exact formula_reduce 5 4 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_5 (n : ℕ) : (G (72*n+32) : ZMod 5) ≠ 0 := by
  rw [residue_5]
  simp only [Nat.mod_one]
  decide
private theorem residue_7 (n : ℕ) : (G (72*n+32) : ZMod 7) = reduced 7 6 2 1 (n%1) := by
  exact formula_reduce 7 6 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_7 (n : ℕ) : (G (72*n+32) : ZMod 7) ≠ 0 := by
  rw [residue_7]
  simp only [Nat.mod_one]
  decide
private theorem residue_11 (n : ℕ) : (G (72*n+32) : ZMod 11) = reduced 11 10 4 1 (n%1) := by
  exact formula_reduce 11 10 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_11 (n : ℕ) : (G (72*n+32) : ZMod 11) ≠ 0 := by
  rw [residue_11]
  simp only [Nat.mod_one]
  decide
private theorem residue_13 (n : ℕ) : (G (72*n+32) : ZMod 13) = reduced 13 12 2 1 (n%1) := by
  exact formula_reduce 13 12 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_13 (n : ℕ) : (G (72*n+32) : ZMod 13) ≠ 0 := by
  rw [residue_13]
  simp only [Nat.mod_one]
  decide
private theorem residue_17 (n : ℕ) : (G (72*n+32) : ZMod 17) = reduced 17 16 4 1 (n%1) := by
  exact formula_reduce 17 16 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_17 (n : ℕ) : (G (72*n+32) : ZMod 17) ≠ 0 := by
  rw [residue_17]
  simp only [Nat.mod_one]
  decide
private theorem residue_19 (n : ℕ) : (G (72*n+32) : ZMod 19) = reduced 19 18 6 1 (n%1) := by
  exact formula_reduce 19 18 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_19 (n : ℕ) : (G (72*n+32) : ZMod 19) ≠ 0 := by
  rw [residue_19]
  simp only [Nat.mod_one]
  decide
private theorem residue_23 (n : ℕ) : (G (72*n+32) : ZMod 23) = reduced 23 22 10 5 (n%5) := by
  exact formula_reduce 23 22 10 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_23 (n : ℕ) : (G (72*n+32) : ZMod 23) ≠ 0 := by
  rw [residue_23]
  have table : ∀ r : Fin 5, reduced 23 22 10 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩
private theorem residue_29 (n : ℕ) : (G (72*n+32) : ZMod 29) = reduced 29 28 3 1 (n%1) := by
  exact formula_reduce 29 28 3 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_29 (n : ℕ) : (G (72*n+32) : ZMod 29) ≠ 0 := by
  rw [residue_29]
  simp only [Nat.mod_one]
  decide
private theorem residue_31 (n : ℕ) : (G (72*n+32) : ZMod 31) = reduced 31 30 4 1 (n%1) := by
  exact formula_reduce 31 30 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_31 (n : ℕ) : (G (72*n+32) : ZMod 31) ≠ 0 := by
  rw [residue_31]
  simp only [Nat.mod_one]
  decide
private theorem residue_37 (n : ℕ) : (G (72*n+32) : ZMod 37) = reduced 37 36 6 1 (n%1) := by
  exact formula_reduce 37 36 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_37 (n : ℕ) : (G (72*n+32) : ZMod 37) ≠ 0 := by
  rw [residue_37]
  simp only [Nat.mod_one]
  decide
private theorem residue_41 (n : ℕ) : (G (72*n+32) : ZMod 41) = reduced 41 40 4 1 (n%1) := by
  exact formula_reduce 41 40 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_41 (n : ℕ) : (G (72*n+32) : ZMod 41) ≠ 0 := by
  rw [residue_41]
  simp only [Nat.mod_one]
  decide
private theorem residue_43 (n : ℕ) : (G (72*n+32) : ZMod 43) = reduced 43 42 6 1 (n%1) := by
  exact formula_reduce 43 42 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_43 (n : ℕ) : (G (72*n+32) : ZMod 43) ≠ 0 := by
  rw [residue_43]
  simp only [Nat.mod_one]
  decide
private theorem residue_47 (n : ℕ) : (G (72*n+32) : ZMod 47) = reduced 47 46 11 55 (n%55) := by
  exact formula_reduce 47 46 11 55 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_47 (n : ℕ) (hn : n%55 ≠ 18) : (G (72*n+32) : ZMod 47) ≠ 0 := by
  rw [residue_47]
  have table : ∀ r : Fin 55, r.val ≠ 18 → reduced 47 46 11 55 r.val ≠ 0 := by decide
  exact table ⟨n%55, Nat.mod_lt _ (by decide)⟩ hn
private theorem residue_53 (n : ℕ) : (G (72*n+32) : ZMod 53) = reduced 53 52 12 1 (n%1) := by
  exact formula_reduce 53 52 12 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_53 (n : ℕ) : (G (72*n+32) : ZMod 53) ≠ 0 := by
  rw [residue_53]
  simp only [Nat.mod_one]
  decide
private theorem residue_59 (n : ℕ) : (G (72*n+32) : ZMod 59) = reduced 59 58 28 7 (n%7) := by
  exact formula_reduce 59 58 28 7 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_59 (n : ℕ) : (G (72*n+32) : ZMod 59) ≠ 0 := by
  rw [residue_59]
  have table : ∀ r : Fin 7, reduced 59 58 28 7 r.val ≠ 0 := by decide
  exact table ⟨n%7, Nat.mod_lt _ (by decide)⟩
private theorem residue_61 (n : ℕ) : (G (72*n+32) : ZMod 61) = reduced 61 60 4 1 (n%1) := by
  exact formula_reduce 61 60 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_61 (n : ℕ) : (G (72*n+32) : ZMod 61) ≠ 0 := by
  rw [residue_61]
  simp only [Nat.mod_one]
  decide
private theorem residue_67 (n : ℕ) : (G (72*n+32) : ZMod 67) = reduced 67 66 10 5 (n%5) := by
  exact formula_reduce 67 66 10 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_67 (n : ℕ) : (G (72*n+32) : ZMod 67) ≠ 0 := by
  rw [residue_67]
  have table : ∀ r : Fin 5, reduced 67 66 10 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩
private theorem residue_71 (n : ℕ) : (G (72*n+32) : ZMod 71) = reduced 71 70 12 1 (n%1) := by
  exact formula_reduce 71 70 12 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_71 (n : ℕ) : (G (72*n+32) : ZMod 71) ≠ 0 := by
  rw [residue_71]
  simp only [Nat.mod_one]
  decide
private theorem residue_73 (n : ℕ) : (G (72*n+32) : ZMod 73) = reduced 73 72 6 1 (n%1) := by
  exact formula_reduce 73 72 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_73 (n : ℕ) : (G (72*n+32) : ZMod 73) ≠ 0 := by
  rw [residue_73]
  simp only [Nat.mod_one]
  decide
private theorem residue_79 (n : ℕ) : (G (72*n+32) : ZMod 79) = reduced 79 78 12 1 (n%1) := by
  exact formula_reduce 79 78 12 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_79 (n : ℕ) : (G (72*n+32) : ZMod 79) ≠ 0 := by
  rw [residue_79]
  simp only [Nat.mod_one]
  decide
private theorem residue_83 (n : ℕ) : (G (72*n+32) : ZMod 83) = reduced 83 82 20 5 (n%5) := by
  exact formula_reduce 83 82 20 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_83 (n : ℕ) : (G (72*n+32) : ZMod 83) ≠ 0 := by
  rw [residue_83]
  have table : ∀ r : Fin 5, reduced 83 82 20 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩
private theorem residue_89 (n : ℕ) : (G (72*n+32) : ZMod 89) = reduced 89 88 10 5 (n%5) := by
  exact formula_reduce 89 88 10 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_89 (n : ℕ) : (G (72*n+32) : ZMod 89) ≠ 0 := by
  rw [residue_89]
  have table : ∀ r : Fin 5, reduced 89 88 10 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩
private theorem residue_97 (n : ℕ) : (G (72*n+32) : ZMod 97) = reduced 97 96 6 1 (n%1) := by
  exact formula_reduce 97 96 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_97 (n : ℕ) : (G (72*n+32) : ZMod 97) ≠ 0 := by
  rw [residue_97]
  simp only [Nat.mod_one]
  decide
private theorem residue_101 (n : ℕ) : (G (72*n+32) : ZMod 101) = reduced 101 100 20 5 (n%5) := by
  exact formula_reduce 101 100 20 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_101 (n : ℕ) (hn : n%5 ≠ 2) : (G (72*n+32) : ZMod 101) ≠ 0 := by
  rw [residue_101]
  have table : ∀ r : Fin 5, r.val ≠ 2 → reduced 101 100 20 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩ hn
private theorem residue_103 (n : ℕ) : (G (72*n+32) : ZMod 103) = reduced 103 102 8 1 (n%1) := by
  exact formula_reduce 103 102 8 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_103 (n : ℕ) : (G (72*n+32) : ZMod 103) ≠ 0 := by
  rw [residue_103]
  simp only [Nat.mod_one]
  decide
private theorem residue_107 (n : ℕ) : (G (72*n+32) : ZMod 107) = reduced 107 106 52 13 (n%13) := by
  exact formula_reduce 107 106 52 13 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_107 (n : ℕ) : (G (72*n+32) : ZMod 107) ≠ 0 := by
  rw [residue_107]
  have table : ∀ r : Fin 13, reduced 107 106 52 13 r.val ≠ 0 := by decide
  exact table ⟨n%13, Nat.mod_lt _ (by decide)⟩
private theorem residue_109 (n : ℕ) : (G (72*n+32) : ZMod 109) = reduced 109 108 18 1 (n%1) := by
  exact formula_reduce 109 108 18 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_109 (n : ℕ) : (G (72*n+32) : ZMod 109) ≠ 0 := by
  rw [residue_109]
  simp only [Nat.mod_one]
  decide
private theorem residue_113 (n : ℕ) : (G (72*n+32) : ZMod 113) = reduced 113 112 6 1 (n%1) := by
  exact formula_reduce 113 112 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_113 (n : ℕ) : (G (72*n+32) : ZMod 113) ≠ 0 := by
  rw [residue_113]
  simp only [Nat.mod_one]
  decide
private theorem residue_127 (n : ℕ) : (G (72*n+32) : ZMod 127) = reduced 127 126 6 1 (n%1) := by
  exact formula_reduce 127 126 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_127 (n : ℕ) : (G (72*n+32) : ZMod 127) ≠ 0 := by
  rw [residue_127]
  simp only [Nat.mod_one]
  decide
private theorem residue_131 (n : ℕ) : (G (72*n+32) : ZMod 131) = reduced 131 130 12 1 (n%1) := by
  exact formula_reduce 131 130 12 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_131 (n : ℕ) : (G (72*n+32) : ZMod 131) ≠ 0 := by
  rw [residue_131]
  simp only [Nat.mod_one]
  decide
private theorem residue_137 (n : ℕ) : (G (72*n+32) : ZMod 137) = reduced 137 136 8 1 (n%1) := by
  exact formula_reduce 137 136 8 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_137 (n : ℕ) : (G (72*n+32) : ZMod 137) ≠ 0 := by
  rw [residue_137]
  simp only [Nat.mod_one]
  decide
private theorem residue_139 (n : ℕ) : (G (72*n+32) : ZMod 139) = reduced 139 138 22 55 (n%55) := by
  exact formula_reduce 139 138 22 55 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_139 (n : ℕ) : (G (72*n+32) : ZMod 139) ≠ 0 := by
  rw [residue_139]
  have table : ∀ r : Fin 55, reduced 139 138 22 55 r.val ≠ 0 := by decide
  exact table ⟨n%55, Nat.mod_lt _ (by decide)⟩
private theorem residue_149 (n : ℕ) : (G (72*n+32) : ZMod 149) = reduced 149 148 36 1 (n%1) := by
  exact formula_reduce 149 148 36 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem divisible_149 (n : ℕ) : (149 : ℤ) ∣ G (72*n+32) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 149).mp
  rw [residue_149]
  simp only [Nat.mod_one]
  decide
private theorem nonzero_2 (n : ℕ) : (G (72*n+32) : ZMod 2) ≠ 0 := by
  have he : (2 : ℕ)^(2^(72*n+32)) ≠ 0 := by positivity
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [G, hz, zero_pow he]

theorem result : ∀ n : ℕ,
  (¬ ∃ k : ℕ, 72*n+32 = 20*k+16) →
  (¬ ∃ k : ℕ, 72*n+32 = 220*k+8) →
  Nat.Prime 149 ∧
  (149 : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (72*n+32)) + 1) *
    2 ^ (2 ^ (2 ^ (72*n+32))) - 1) ∧
  ∀ q : ℕ, Nat.Prime q →
    (q : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (72*n+32)) + 1) *
      2 ^ (2 ^ (2 ^ (72*n+32))) - 1) → 149 ≤ q := by
  intro n hC1 hC2
  have hn1 := noncoverage_C1 n hC1
  have hn2 := noncoverage_C2 n hC2
  refine ⟨by norm_num, divisible_149 n, ?_⟩
  intro q hprime hdvd
  by_contra hbound
  have hq : q < 149 := by omega
  have hz : (G (72*n+32) : ZMod q) = 0 :=
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
  · exact nonzero_47 n hn2 hz
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
  · exact nonzero_101 n hn1 hz
  · exact nonzero_103 n hz
  · exact nonzero_107 n hz
  · exact nonzero_109 n hz
  · exact nonzero_113 n hz
  · exact nonzero_127 n hz
  · exact nonzero_131 n hz
  · exact nonzero_137 n hz
  · exact nonzero_139 n hz

end D5.S3.Arith.Primes.WuA227244ConjectureThree
