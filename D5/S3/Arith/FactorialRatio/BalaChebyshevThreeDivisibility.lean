/- GID: D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility
   mirror-E: none(waiver:unbounded-prime-valuation-proof)
   anchors: []
   utility: none
   digest: The Chebyshev factorial ratio is divisible by 3n+1 at every natural n. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.BalaChebyshevThreeDivisibility

private def floorDefect (n q : Nat) : Int :=
  ((30*n/q : Nat) : Int)+((n/q : Nat) : Int)-((15*n/q : Nat) : Int)-
    ((10*n/q : Nat) : Int)-((6*n/q : Nat) : Int)

/-- The local step function is nonnegative. A divisor of 3n+1 gives an entire
unit of valuation when its modulus is 7 or at least 10. The excluded small
moduli are not silently asserted to satisfy that stronger statement. -/
private theorem local_floor_bounds (n q : Nat) (hq : 0 < q) :
    0 ≤ floorDefect n q ∧
      ((q = 7 ∨ 10 ≤ q) → q ∣ 3*n+1 → floorDefect n q = 1) := by
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  have split (c : Nat) : c*n/q = c*(n/q)+c*r/q := by
    calc
      c*n/q = (q*(c*(n/q))+c*r)/q := by
        congr 1
        calc
          c*n = c*(q*(n/q)+r) := congrArg (fun x => c*x) (Nat.div_add_mod n q).symm
          _ = q*(c*(n/q))+c*r := by ring
      _ = c*(n/q)+c*r/q := by rw [Nat.mul_add_div hq]
  have red : floorDefect n q = floorDefect r q := by
    unfold floorDefect
    rw [split 30, split 15, split 10, split 6, Nat.div_eq_of_lt hr]
    push_cast
    ring
  have half : 15*r/q = (30*r/q)/2 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (15*r)*2 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
  have third : 10*r/q = (30*r/q)/3 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (10*r)*3 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 3)]
  have fifth : 6*r/q = (30*r/q)/5 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (6*r)*5 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 5)]
  have bound : 30*r/q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  constructor
  · rw [red]
    unfold floorDefect
    rw [Nat.div_eq_of_lt hr, half, third, fifth]
    omega
  · intro hsize hdiv
    have hrd : q ∣ 3*r+1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hm := Nat.mod_eq_zero_of_dvd hdiv
      simpa [r, Nat.add_mod, Nat.mul_mod] using hm
    rw [red]
    rcases hsize with rfl | hsize
    · have hm := Nat.mod_eq_zero_of_dvd hrd
      have hr2 : r = 2 := by omega
      norm_num [floorDefect, hr2]
    · obtain ⟨t, ht⟩ := hrd
      have ht0 : 0 < t := by
        by_contra hn
        have hz : t = 0 := by omega
        simp [hz] at ht
      have ht3 : t < 3 := by
        by_contra hn
        have hh := Nat.mul_le_mul_left q (show 3 ≤ t by omega)
        nlinarith
      have ht12 : t = 1 ∨ t = 2 := by omega
      rcases ht12 with rfl | rfl
      · have h30 : 30*r/q = 9 := (Nat.div_eq_iff hq).mpr (by omega)
        have h15 : 15*r/q = 4 := (Nat.div_eq_iff hq).mpr (by omega)
        have h10 : 10*r/q = 3 := (Nat.div_eq_iff hq).mpr (by omega)
        have h6 : 6*r/q = 1 := (Nat.div_eq_iff hq).mpr (by omega)
        norm_num [floorDefect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]
      · have h30 : 30*r/q = 19 := (Nat.div_eq_iff hq).mpr (by omega)
        have h15 : 15*r/q = 9 := (Nat.div_eq_iff hq).mpr (by omega)
        have h10 : 10*r/q = 6 := (Nat.div_eq_iff hq).mpr (by omega)
        have h6 : 6*r/q = 3 := (Nat.div_eq_iff hq).mpr (by omega)
        norm_num [floorDefect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]

/-- Peter Bala's August 2025 A211417 clause: a(n)/(3n+1) is integral.
The factorial divisibility statement avoids truncated natural-number division.
It includes n=0 and proves the whole conjecture, not a bounded numerical check.
The separately settled (30n-1) clause is not the target of this theorem. -/
theorem bala_three_integrality (n : Nat) :
    (3*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ∣
      (30*n).factorial*n.factorial := by
  classical
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hL : (30*n).factorial*n.factorial ≠ 0 := by positivity
  have hR : (3*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ≠ 0 := by positivity
  apply (Nat.factorization_prime_le_iff_dvd hR hL).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul (by positivity : (3*n+1)*(15*n).factorial*(10*n).factorial ≠ 0)
      (Nat.factorial_ne_zero (6*n)),
    padicValNat.mul (by positivity : (3*n+1)*(15*n).factorial ≠ 0) (Nat.factorial_ne_zero (10*n)),
    padicValNat.mul (by omega : 3*n+1 ≠ 0) (Nat.factorial_ne_zero (15*n)),
    padicValNat.mul (Nat.factorial_ne_zero (30*n)) (Nat.factorial_ne_zero n)]
  have vf (m : Nat) (hm : m ≤ 30*n+1) :
      padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 (30*n+2), m/p^j :=
    padicValNat_factorial (lt_of_le_of_lt (p.log_le_self m) (by omega))
  have total :
      (padicValNat p (30*n).factorial : Int)+(padicValNat p n.factorial : Int)-
      (padicValNat p (15*n).factorial : Int)-(padicValNat p (10*n).factorial : Int)-
      (padicValNat p (6*n).factorial : Int) =
      ∑ j ∈ Finset.Ico 1 (30*n+2), floorDefect n (p^j) := by
    rw [vf (30*n) (by omega), vf n (by omega), vf (15*n) (by omega),
      vf (10*n) (by omega), vf (6*n) (by omega)]
    simp only [Nat.cast_sum, floorDefect, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have total_nonneg : 0 ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), floorDefect n (p^j) :=
    Finset.sum_nonneg (fun j _ => (local_floor_bounds n (p^j) (pow_pos hp.pos j)).1)
  by_cases hpd : p ∣ 3*n+1
  swap
  · have hz := padicValNat.eq_zero_of_not_dvd hpd
    omega
  by_cases hp2 : p = 2
  · subst p
    have hd : ¬2 ∣ 5*n := by omega
    have hchoose := Nat.choose_mul_factorial_mul_factorial (show 3*n ≤ 8*n by omega)
    rw [show 8*n-3*n = 5*n by omega] at hchoose
    have hc := congrArg (padicValNat 2) hchoose
    rw [padicValNat.mul
      (mul_ne_zero (Nat.choose_ne_zero (n := 8*n) (k := 3*n) (by omega))
        (Nat.factorial_ne_zero (3*n)))
      (Nat.factorial_ne_zero (5*n)),
      padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 3*n) (by omega))
        (Nat.factorial_ne_zero (3*n))] at hc
    have step := Nat.choose_succ_right_eq (8*n) (3*n)
    rw [show 8*n-3*n = 5*n by omega] at step
    have hs := congrArg (padicValNat 2) step
    rw [padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 3*n+1) (by omega))
        (by omega : 3*n+1 ≠ 0),
      padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 3*n) (by omega)) (by omega : 5*n ≠ 0),
      padicValNat.eq_zero_of_not_dvd hd] at hs
    have f15 := padicValNat_factorial_mul (p := 2) (15*n)
    have f5 := padicValNat_factorial_mul (p := 2) (5*n)
    have f3 := padicValNat_factorial_mul (p := 2) (3*n)
    have f4 := padicValNat_factorial_mul (p := 2) (4*n)
    have f2 := padicValNat_factorial_mul (p := 2) (2*n)
    have f1 := padicValNat_factorial_mul (p := 2) n
    norm_num [← Nat.mul_assoc] at f15 f5 f3 f4 f2 f1
    omega
  by_cases hp3 : p = 3
  · subst p
    omega
  by_cases hp5 : p = 5
  · subst p
    have hd : ¬5 ∣ 2*n := by omega
    have hchoose := Nat.choose_mul_factorial_mul_factorial (show 3*n ≤ 5*n by omega)
    rw [show 5*n-3*n = 2*n by omega] at hchoose
    have hc := congrArg (padicValNat 5) hchoose
    rw [padicValNat.mul
      (mul_ne_zero (Nat.choose_ne_zero (n := 5*n) (k := 3*n) (by omega))
        (Nat.factorial_ne_zero (3*n)))
      (Nat.factorial_ne_zero (2*n)),
      padicValNat.mul (Nat.choose_ne_zero (n := 5*n) (k := 3*n) (by omega))
        (Nat.factorial_ne_zero (3*n))] at hc
    have step := Nat.choose_succ_right_eq (5*n) (3*n)
    rw [show 5*n-3*n = 2*n by omega] at step
    have hs := congrArg (padicValNat 5) step
    rw [padicValNat.mul (Nat.choose_ne_zero (n := 5*n) (k := 3*n+1) (by omega))
        (by omega : 3*n+1 ≠ 0),
      padicValNat.mul (Nat.choose_ne_zero (n := 5*n) (k := 3*n) (by omega)) (by omega : 2*n ≠ 0),
      padicValNat.eq_zero_of_not_dvd hd] at hs
    have f6 := padicValNat_factorial_mul (p := 5) (6*n)
    have f3 := padicValNat_factorial_mul (p := 5) (3*n)
    have f2 := padicValNat_factorial_mul (p := 5) (2*n)
    have f1 := padicValNat_factorial_mul (p := 5) n
    norm_num [← Nat.mul_assoc] at f6 f3 f2 f1
    omega
  have hp7 : 7 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at hp <;> omega
  let v := padicValNat p (3*n+1)
  have vb : v ≤ 30*n+1 := by
    exact (padicValNat_le_nat_log (3*n+1)).trans ((p.log_le_self _).trans (by omega))
  have low : (v : Int) ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), floorDefect n (p^j) := by
    calc
      (v : Int) = ∑ j ∈ Finset.Ico 1 (v+1), (1 : Int) := by simp
      _ ≤ ∑ j ∈ Finset.Ico 1 (v+1), floorDefect n (p^j) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj0, hjv⟩ := Finset.mem_Ico.mp hj
        have hd : p^j ∣ 3*n+1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [v] at hjv; omega)
        have hsize : p^j = 7 ∨ 10 ≤ p^j := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have hk : 1 ≤ p^k := Nat.succ_le_iff.mpr (pow_pos hp.pos k)
          by_cases hbig : 10 ≤ p
          · right
            rw [pow_succ]
            nlinarith
          have hpeq : p = 7 := by
            interval_cases p <;> norm_num at hp <;> omega
          subst p
          cases k with
          | zero => norm_num
          | succ k =>
            right
            have hh : 1 ≤ (7:Nat)^k := Nat.succ_le_iff.mpr (pow_pos (by decide) k)
            simp only [pow_succ]
            nlinarith
        rw [(local_floor_bounds n (p^j) (pow_pos hp.pos j)).2 hsize hd]
      _ ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), floorDefect n (p^j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j _ _
          exact (local_floor_bounds n (p^j) (pow_pos hp.pos j)).1
  dsimp [v] at low
  omega

end D5.S3.Arith.FactorialRatio.BalaChebyshevThreeDivisibility
