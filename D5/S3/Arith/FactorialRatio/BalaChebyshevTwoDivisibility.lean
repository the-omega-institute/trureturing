/- GID: D5/S3/Arith/FactorialRatio/BalaChebyshevTwoDivisibility
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaChebyshevTwoDivisibility
   mirror-E: none(waiver:unbounded-prime-valuation-proof)
   anchors: []
   utility: none
   digest: Seven times the Chebyshev factorial ratio is divisible by 2n+1 for every n. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.BalaChebyshevTwoDivisibility

private def defect (n q : Nat) : Int :=
  ((30*n/q : Nat) : Int)+((n/q : Nat) : Int)-((15*n/q : Nat) : Int)-
    ((10*n/q : Nat) : Int)-((6*n/q : Nat) : Int)

/-- The divisor residue and the large-scale compensation interval are different
sources of valuation. Small divisor moduli 3, 5 and 7 are not declared units. -/
private theorem local_bounds (n q : Nat) (hq : 0 < q) :
    0 ≤ defect n q ∧
    (9 ≤ q → q ∣ 2*n+1 → defect n q = 1) ∧
    (5*n < q → q ≤ 30*n → defect n q = 1) := by
  have half (x : Nat) : 15*x/q = (30*x/q)/2 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*x = (15*x)*2 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
  have third (x : Nat) : 10*x/q = (30*x/q)/3 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*x = (10*x)*3 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 3)]
  have fifth (x : Nat) : 6*x/q = (30*x/q)/5 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*x = (6*x)*5 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 5)]
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
  have red : defect n q = defect r q := by
    unfold defect
    rw [split 30, split 15, split 10, split 6, Nat.div_eq_of_lt hr]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hb : 30*r/q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
    rw [red]
    unfold defect
    rw [Nat.div_eq_of_lt hr, half, third, fifth]
    omega
  · intro hsize hd
    have hrd : q ∣ 2*r+1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hm := Nat.mod_eq_zero_of_dvd hd
      simpa [r, Nat.add_mod, Nat.mul_mod] using hm
    obtain ⟨t, ht⟩ := hrd
    have ht0 : 0 < t := by
      by_contra h
      have hz : t = 0 := by omega
      simp [hz] at ht
    have ht2 : t < 2 := by
      by_contra h
      have hh := Nat.mul_le_mul_left q (show 2 ≤ t by omega)
      nlinarith
    have ht1 : t = 1 := by omega
    have hres : 2*r+1 = q := by simpa [ht1] using ht
    have h10 : 10*r/q = 4 := (Nat.div_eq_iff hq).mpr (by omega)
    have h6 : 6*r/q = 2 := (Nat.div_eq_iff hq).mpr (by omega)
    rw [red]
    by_cases h15 : 15 ≤ q
    · have h30 : 30*r/q = 14 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15r : 15*r/q = 7 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15r, h10, h6, Nat.div_eq_of_lt hr]
    · have h30 : 30*r/q = 13 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15r : 15*r/q = 6 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15r, h10, h6, Nat.div_eq_of_lt hr]
  · intro hlo hhi
    have hnq : n < q := by omega
    have hklo : 1 ≤ 30*n/q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
    have hkhi : 30*n/q < 6 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
    unfold defect
    rw [Nat.div_eq_of_lt hnq, half, third, fifth]
    omega

/-- For p=3 or 5, the largest p-power below 30n is a fresh valuation unit,
strictly beyond every p-power that divides 2n+1. -/
private theorem compensation_scale (n p : Nat) (hn : 0 < n)
    (hp : p.Prime) (hsmall : p = 3 ∨ p = 5) :
    ∃ t : Nat, t ∈ Finset.Ico 1 (30*n+2) ∧
      padicValNat p (2*n+1) < t ∧ defect n (p^t) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let t := Nat.log p (30*n)
  have hlo : p^t ≤ 30*n := Nat.pow_log_le_self p (by omega)
  have hhi : 30*n < p^(t+1) := Nat.lt_pow_succ_log_self hp.one_lt (30*n)
  have hq : 5*n < p^t := by
    rw [pow_succ] at hhi
    rcases hsmall with hp3 | hp5 <;> subst p <;> nlinarith
  have hqd : 2*n+1 < p^t := by omega
  have htv : padicValNat p (2*n+1) < t := by
    by_contra h
    have hd : p^t ∣ 2*n+1 :=
      (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    exact (not_le_of_gt hqd) (Nat.le_of_dvd (by omega) hd)
  have htbound : t ≤ 30*n := Nat.log_le_self p (30*n)
  refine ⟨t, ?_, htv, (local_bounds n (p^t) (pow_pos hp.pos t)).2.2 hq hlo⟩
  simp only [Finset.mem_Ico]
  omega

/-- Bala's A211417 7A(n)/(2n+1) conjecture, in division-free form. -/
theorem bala_two_integrality (n : Nat) :
    (2*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ∣
      7*((30*n).factorial*n.factorial) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hL : 7*((30*n).factorial*n.factorial) ≠ 0 := by positivity
  have hR : (2*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ≠ 0 := by positivity
  apply (Nat.factorization_prime_le_iff_dvd hR hL).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul
      (by positivity : (2*n+1)*(15*n).factorial*(10*n).factorial ≠ 0)
      (Nat.factorial_ne_zero (6*n)),
    padicValNat.mul (by positivity : (2*n+1)*(15*n).factorial ≠ 0)
      (Nat.factorial_ne_zero (10*n)),
    padicValNat.mul (by omega : 2*n+1 ≠ 0) (Nat.factorial_ne_zero (15*n)),
    padicValNat.mul (by decide : (7 : Nat) ≠ 0)
      (mul_ne_zero (Nat.factorial_ne_zero (30*n)) (Nat.factorial_ne_zero n)),
    padicValNat.mul (Nat.factorial_ne_zero (30*n)) (Nat.factorial_ne_zero n)]
  have vf (m : Nat) (hm : m ≤ 30*n+1) :
      padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 (30*n+2), m/p^j :=
    padicValNat_factorial (lt_of_le_of_lt (Nat.log_le_self p m) (by omega))
  have total :
      (padicValNat p (30*n).factorial : Int)+(padicValNat p n.factorial : Int)-
      (padicValNat p (15*n).factorial : Int)-(padicValNat p (10*n).factorial : Int)-
      (padicValNat p (6*n).factorial : Int) =
      ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) := by
    rw [vf (30*n) (by omega), vf n (by omega), vf (15*n) (by omega),
      vf (10*n) (by omega), vf (6*n) (by omega)]
    simp only [Nat.cast_sum, defect, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have nonneg (j : Nat) : 0 ≤ defect n (p^j) :=
    (local_bounds n (p^j) (pow_pos hp.pos j)).1
  have sum_nonneg : 0 ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) :=
    Finset.sum_nonneg (fun j _ => nonneg j)
  by_cases hpd : p ∣ 2*n+1
  swap
  · have hz := padicValNat.eq_zero_of_not_dvd hpd
    omega
  have hp3 : 3 ≤ p := by
    have htwo := hp.two_le
    by_contra h
    have hp2 : p = 2 := by omega
    subst p
    omega
  let v := padicValNat p (2*n+1)
  have hv : 1 ≤ v := one_le_padicValNat_of_dvd (by omega) hpd
  have vb : v ≤ 30*n+1 :=
    (padicValNat_le_nat_log (2*n+1)).trans ((Nat.log_le_self p _).trans (by omega))
  have unit_tail (j : Nat) (hj : j ∈ Finset.Ico 2 (v+1)) : defect n (p^j) = 1 := by
    obtain ⟨hj2, hjv⟩ := Finset.mem_Ico.mp hj
    have hd : p^j ∣ 2*n+1 := (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [v] at hjv; omega)
    have hsize : 9 ≤ p^j := by
      rw [show j = 2+(j-2) by omega, pow_add, pow_two]
      have hpos : 1 ≤ p^(j-2) := Nat.succ_le_iff.mpr (pow_pos hp.pos _)
      nlinarith
    exact (local_bounds n (p^j) (pow_pos hp.pos j)).2.1 hsize hd
  have tail_sum : (∑ j ∈ Finset.Ico 2 (v+1), defect n (p^j)) = ((v-1 : Nat) : Int) := by
    calc
      _ = ∑ j ∈ Finset.Ico 2 (v+1), (1 : Int) :=
        Finset.sum_congr rfl (fun j hj => unit_tail j hj)
      _ = ((v-1 : Nat) : Int) := by simp
  have tail_subset : Finset.Ico 2 (v+1) ⊆ Finset.Ico 1 (30*n+2) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  have tail_le : ((v-1 : Nat) : Int) ≤
      ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) := by
    rw [← tail_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg tail_subset (fun j _ _ => nonneg j)
  by_cases hs : p = 3 ∨ p = 5
  · obtain ⟨t, htb, htv, htunit⟩ := compensation_scale n p hn hp hs
    have hnot : t ∉ Finset.Ico 2 (v+1) := by
      simp only [Finset.mem_Ico]
      dsimp [v] at *
      omega
    have hsub : insert t (Finset.Ico 2 (v+1)) ⊆ Finset.Ico 1 (30*n+2) :=
      Finset.insert_subset_iff.mpr ⟨htb, tail_subset⟩
    have hl := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j => defect n (p^j)) hsub (fun j _ _ => nonneg j)
    rw [Finset.sum_insert hnot, htunit, tail_sum] at hl
    dsimp [v] at *
    omega
  by_cases hp7 : p = 7
  · have hseven : padicValNat p 7 = 1 := by subst p; norm_num
    dsimp [v] at *
    omega
  have hp11 : 11 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at hp <;> omega
  have head_unit : defect n (p^1) = 1 := by
    exact (local_bounds n (p^1) (pow_pos hp.pos 1)).2.1
      (by simpa using (show 9 ≤ p by omega)) (by simpa using hpd)
  have hnot : 1 ∉ Finset.Ico 2 (v+1) := by simp
  have hsub : insert 1 (Finset.Ico 2 (v+1)) ⊆ Finset.Ico 1 (30*n+2) := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨by simp, tail_subset⟩
  have hl := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => defect n (p^j)) hsub (fun j _ _ => nonneg j)
  rw [Finset.sum_insert hnot, head_unit, tail_sum] at hl
  dsimp [v] at *
  omega

#print axioms bala_two_integrality

end D5.S3.Arith.FactorialRatio.BalaChebyshevTwoDivisibility
