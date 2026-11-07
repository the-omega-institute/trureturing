/- GID: D5/S3/Arith/Primes/WuA227244ConjectureFour
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/WuA227244ConjectureFour
   mirror-E: none(waiver:unbounded-modular-reduction)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Arith/Primes/WuA227244ConjectureFour.result; instance=D5/S3/Arith/Primes/WuA227244ConjectureFour.reduced
   digest: Fifty-nine is the least prime divisor on Wu's specified unbounded progression. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace D5.S3.Arith.Primes.WuA227244ConjectureFour

def G (m : ℕ) : ℤ := ((2 : ℤ) ^ (2 ^ m) + 1) * 2 ^ (2 ^ (2 ^ m)) - 1

def claim : Prop := ∀ n : ℕ, n % 55 ≠ 26 →
  Nat.Prime 59 ∧ (59 : ℤ) ∣ G (168*n+43) ∧
  ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ G (168*n+43) → 59 ≤ q

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
  ((2 : ZMod q) ^ (2^(168*r+43)%d) + 1) *
    2 ^ (2^(p+2^(168*r+43)%p)%d) - 1

private theorem formula_reduce (q d p L n : ℕ)
    (hq : (2 : ZMod q)^d=1)
    (ht : (2 : ZMod d)^(p+p)=(2 : ZMod d)^p)
    (hd : (2 : ZMod d)^(168*L+43)=(2 : ZMod d)^43)
    (hp : (2 : ZMod p)^(168*L+43)=(2 : ZMod p)^43)
    (hsmall : p ≤ 43) :
    (G (168*n+43) : ZMod q) = reduced q d p L (n%L) := by
  let m := 168*n+43
  let mr := 168*(n%L)+43
  have hD : 2^m%d=2^mr%d := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ d).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod d) 168 43 L n hd
  have hP : 2^m%p=2^mr%p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      progression_reduce (2 : ZMod p) 168 43 L n hp
  have he : p ≤ 2^m := by
    have hm : 43 ≤ m := by dsimp [m]; omega
    have hx := Nat.lt_two_pow_self (n := m)
    omega
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

private theorem residue_3 (n : ℕ) : (G (168*n+43) : ZMod 3) = reduced 3 2 1 1 (n%1) := by
  exact formula_reduce 3 2 1 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_3 (n : ℕ) : (G (168*n+43) : ZMod 3) ≠ 0 := by
  rw [residue_3]
  simp only [Nat.mod_one]
  decide
private theorem residue_5 (n : ℕ) : (G (168*n+43) : ZMod 5) = reduced 5 4 2 1 (n%1) := by
  exact formula_reduce 5 4 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_5 (n : ℕ) : (G (168*n+43) : ZMod 5) ≠ 0 := by
  rw [residue_5]
  simp only [Nat.mod_one]
  decide
private theorem residue_7 (n : ℕ) : (G (168*n+43) : ZMod 7) = reduced 7 6 2 1 (n%1) := by
  exact formula_reduce 7 6 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_7 (n : ℕ) : (G (168*n+43) : ZMod 7) ≠ 0 := by
  rw [residue_7]
  simp only [Nat.mod_one]
  decide
private theorem residue_11 (n : ℕ) : (G (168*n+43) : ZMod 11) = reduced 11 10 4 1 (n%1) := by
  exact formula_reduce 11 10 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_11 (n : ℕ) : (G (168*n+43) : ZMod 11) ≠ 0 := by
  rw [residue_11]
  simp only [Nat.mod_one]
  decide
private theorem residue_13 (n : ℕ) : (G (168*n+43) : ZMod 13) = reduced 13 12 2 1 (n%1) := by
  exact formula_reduce 13 12 2 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_13 (n : ℕ) : (G (168*n+43) : ZMod 13) ≠ 0 := by
  rw [residue_13]
  simp only [Nat.mod_one]
  decide
private theorem residue_17 (n : ℕ) : (G (168*n+43) : ZMod 17) = reduced 17 16 4 1 (n%1) := by
  exact formula_reduce 17 16 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_17 (n : ℕ) : (G (168*n+43) : ZMod 17) ≠ 0 := by
  rw [residue_17]
  simp only [Nat.mod_one]
  decide
private theorem residue_19 (n : ℕ) : (G (168*n+43) : ZMod 19) = reduced 19 18 6 1 (n%1) := by
  exact formula_reduce 19 18 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_19 (n : ℕ) : (G (168*n+43) : ZMod 19) ≠ 0 := by
  rw [residue_19]
  simp only [Nat.mod_one]
  decide
private theorem residue_23 (n : ℕ) : (G (168*n+43) : ZMod 23) = reduced 23 22 10 5 (n%5) := by
  exact formula_reduce 23 22 10 5 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_23 (n : ℕ) : (G (168*n+43) : ZMod 23) ≠ 0 := by
  rw [residue_23]
  have table : ∀ r : Fin 5, reduced 23 22 10 5 r.val ≠ 0 := by decide
  exact table ⟨n%5, Nat.mod_lt _ (by decide)⟩
private theorem residue_29 (n : ℕ) : (G (168*n+43) : ZMod 29) = reduced 29 28 3 1 (n%1) := by
  exact formula_reduce 29 28 3 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_29 (n : ℕ) : (G (168*n+43) : ZMod 29) ≠ 0 := by
  rw [residue_29]
  simp only [Nat.mod_one]
  decide
private theorem residue_31 (n : ℕ) : (G (168*n+43) : ZMod 31) = reduced 31 30 4 1 (n%1) := by
  exact formula_reduce 31 30 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_31 (n : ℕ) : (G (168*n+43) : ZMod 31) ≠ 0 := by
  rw [residue_31]
  simp only [Nat.mod_one]
  decide
private theorem residue_37 (n : ℕ) : (G (168*n+43) : ZMod 37) = reduced 37 36 6 1 (n%1) := by
  exact formula_reduce 37 36 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_37 (n : ℕ) : (G (168*n+43) : ZMod 37) ≠ 0 := by
  rw [residue_37]
  simp only [Nat.mod_one]
  decide
private theorem residue_41 (n : ℕ) : (G (168*n+43) : ZMod 41) = reduced 41 40 4 1 (n%1) := by
  exact formula_reduce 41 40 4 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_41 (n : ℕ) : (G (168*n+43) : ZMod 41) ≠ 0 := by
  rw [residue_41]
  simp only [Nat.mod_one]
  decide
private theorem residue_43 (n : ℕ) : (G (168*n+43) : ZMod 43) = reduced 43 42 6 1 (n%1) := by
  exact formula_reduce 43 42 6 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_43 (n : ℕ) : (G (168*n+43) : ZMod 43) ≠ 0 := by
  rw [residue_43]
  simp only [Nat.mod_one]
  decide
private theorem residue_47 (n : ℕ) : (G (168*n+43) : ZMod 47) = reduced 47 46 11 55 (n%55) := by
  exact formula_reduce 47 46 11 55 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_47 (n : ℕ) (hn : n%55 ≠ 26) : (G (168*n+43) : ZMod 47) ≠ 0 := by
  rw [residue_47]
  have table : ∀ r : Fin 55, r.val ≠ 26 → reduced 47 46 11 55 r.val ≠ 0 := by decide
  exact table ⟨n%55, Nat.mod_lt _ (by decide)⟩ hn
private theorem residue_53 (n : ℕ) : (G (168*n+43) : ZMod 53) = reduced 53 52 12 1 (n%1) := by
  exact formula_reduce 53 52 12 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem nonzero_53 (n : ℕ) : (G (168*n+43) : ZMod 53) ≠ 0 := by
  rw [residue_53]
  simp only [Nat.mod_one]
  decide
private theorem residue_59 (n : ℕ) : (G (168*n+43) : ZMod 59) = reduced 59 58 28 1 (n%1) := by
  exact formula_reduce 59 58 28 1 n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem divisible_59 (n : ℕ) : (59 : ℤ) ∣ G (168*n+43) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 59).mp
  rw [residue_59]
  simp only [Nat.mod_one]
  decide
private theorem nonzero_2 (n : ℕ) : (G (168*n+43) : ZMod 2) ≠ 0 := by
  have he : (2 : ℕ)^(2^(168*n+43)) ≠ 0 := by positivity
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [G, hz, zero_pow he]

theorem result : ∀ n : ℕ, n % 55 ≠ 26 →
  Nat.Prime 59 ∧
  (59 : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (168*n+43)) + 1) *
    2 ^ (2 ^ (2 ^ (168*n+43))) - 1) ∧
  ∀ q : ℕ, Nat.Prime q →
    (q : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (168*n+43)) + 1) *
      2 ^ (2 ^ (2 ^ (168*n+43))) - 1) → 59 ≤ q := by
  change claim
  intro n hn
  refine ⟨by norm_num, divisible_59 n, ?_⟩
  intro q hprime hdvd
  by_contra hbound
  have hq : q < 59 := by omega
  have hz : (G (168*n+43) : ZMod q) = 0 :=
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
  · exact nonzero_47 n hn hz
  · exact nonzero_53 n hz

set_option pp.proofs false in
#print result
#print axioms result
end D5.S3.Arith.Primes.WuA227244ConjectureFour
