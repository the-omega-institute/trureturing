/- GID: D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk
   generality: G
   mirror-B: D5/B/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cullinan–Young’s even Krawtchouk sign interpolant coefficient formula is proved. -/

/- Public source proposition: claim.
   The claim retains the literal source sum and product, without duplicate definitions;
   private interpolate_source identifies them with Mathlib Lagrange.interpolate for the proof.
   proof_shape: result=bind-only; escape_witness: none.
   admission_basis: open-problem-resolution (#19000; Proved).
   Direct frozen dependencies: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19833.
   All theorem rows below have proof_shape: bind-only and escape_witness: none.
   interpolate_source -> consumer: result.
   denom -> consumers: denom_inv.
   ell_factor -> consumer: ell_pred.
   ell_top -> consumers: I_top_zero.
   sum_nodes -> consumers: ell_pred.
   ell_pred -> consumers: I_pred_sum.
   weighted_sum -> consumers: I_pred_sum.
   neg_pow_reflect -> consumers: denom_inv, weight_reflect.
   denom_inv -> consumers: I_top_zero, I_pred_sum.
   weight_reflect -> consumers: I_top_zero, I_pred_sum.
   sign_reflect -> consumers: I_top_zero, I_pred_sum.
   I_degree_le -> consumers: leading_even.
   I_top_zero -> consumers: leading_even.
   symmetric_sum -> consumers: I_pred_sum.
   I_pred_sum -> consumers: I_pred_catalan.
   I_pred_catalan -> consumers: leading_even.
   leading_even -> consumers: result.
   The private definition weight has type Nat -> Nat -> Rat and is used by denom_inv,
   weight_reflect, I_top_zero, and I_pred_sum.
   Utility is none: the proof gives unbounded rational identities; no finite computation
   refutes a claim and no bounded enumeration, certified instance, or checker is delivered.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk

open Polynomial

noncomputable def ell (N i : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.range (N + 1)).erase i,
    C (1 / ((i : ℚ) - j)) * (X - C ((j : ℚ) - (N : ℚ) / 2))

noncomputable def I (N : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (N + 1),
    C ((SignType.sign ((i : ℚ) - (N : ℚ) / 2) : SignType) : ℚ) * ell N i

/-- Cullinan–Young, arXiv:2603.05408, Remark 8: "Numerical experimentation suggests that the
leading coefficient of I_N(x) (and, therefore, F_N(x)) is given by (−1)^{(N−2)/2} C((N−2)/2)/(N−1)!,
where C(n) is the nth Catalan number" (for even `N`). -/
def claim : Prop :=
  ∀ N : ℕ, 2 ≤ N → Even N →
    (I N).leadingCoeff = (-1) ^ ((N - 2) / 2) * (catalan ((N - 2) / 2) : ℚ) / ((N - 1).factorial : ℚ)

end D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk

namespace D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk
open Polynomial Finset

private lemma interpolate_source (N : ℕ) :
    (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))) =
      I N := by
  simp only [I, ell, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    sub_sub_sub_cancel_right, one_div]

private lemma denom (i k : ℕ) :
    (∏ j ∈ (range (i + k + 1)).erase i, ((i : ℚ) - j)) =
      (-1 : ℚ)^k * (i.factorial : ℚ) * (k.factorial : ℚ) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    rw [range_add_one, erase_insert (by simp)]
    rw [prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  | succ k ih =>
    have hne : i + k + 1 ≠ i := by omega
    rw [show i + (k + 1) + 1 = (i + k + 1) + 1 by omega, range_add_one, erase_insert_of_ne hne]
    rw [prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ]
    push_cast
    ring

private lemma ell_factor (N i : ℕ) :
    (Lagrange.basis (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) i) = C ((∏ j ∈ (range (N+1)).erase i, ((i : ℚ)-j))⁻¹) *
      ∏ j ∈ (range (N+1)).erase i, (X - C ((j : ℚ) - (N : ℚ)/2)) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, sub_sub_sub_cancel_right,
    prod_mul_distrib, ← map_prod, ← prod_inv_distrib]

private lemma ell_top (N i : ℕ) (hi : i ≤ N) :
    ((Lagrange.basis (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) i)).coeff N = (∏ j ∈ (range (N+1)).erase i, ((i : ℚ)-j))⁻¹ := by
  have hv : Set.InjOn (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (range (N+1)) := by
    intro a ha b hb h
    exact_mod_cast sub_left_inj.mp h
  have himem : i ∈ range (N+1) := mem_range.mpr (by omega)
  have hd := Lagrange.natDegree_basis hv himem
  simpa only [leadingCoeff, hd, card_range, Nat.add_sub_cancel,
    sub_sub_sub_cancel_right] using Lagrange.leadingCoeff_basis hv himem

private lemma sum_nodes (N : ℕ) :
    (∑ j ∈ range (N+1), ((j : ℚ)-(N : ℚ)/2)) = 0 := by
  have hnat := Finset.sum_range_id_mul_two (N+1)
  rw [Nat.add_sub_cancel] at hnat
  have h := congrArg (fun x : ℕ => (x : ℚ)) hnat
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  linarith

private lemma ell_pred (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    ((Lagrange.basis (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) i)).coeff (N-1) =
      (∏ j ∈ (range (N+1)).erase i, ((i : ℚ)-j))⁻¹ * ((i : ℚ)-(N : ℚ)/2) := by
  rw [ell_factor, coeff_C_mul]
  have hc : ((range (N+1)).erase i).card = N := by
    simp [card_erase_of_mem (mem_range.mpr (by omega : i < N+1))]
  have ht := prod_X_sub_C_coeff_card_pred ((range (N+1)).erase i)
    (fun j => (j : ℚ) - (N : ℚ)/2) (by omega : 0 < ((range (N+1)).erase i).card)
  rw [hc] at ht
  rw [ht]
  have h := sum_erase_add (range (N+1)) (fun j => (j : ℚ)-(N : ℚ)/2)
    (mem_range.mpr (by omega : i < N+1))
  rw [sum_nodes] at h
  congr 1
  linarith

private lemma weighted_sum (m : ℕ) :
    (∑ k ∈ range (m+1), ((m+1 : ℚ)-k) * (-1 : ℚ)^k * ((2*m+2).choose k : ℚ)) =
      (-1 : ℚ)^m * ((2*m).choose m : ℚ) := by
  cases m with
  | zero => norm_num [sum_range_succ]
  | succ n =>
    have hA : (∑ k ∈ range (n+1+1), (-1 : ℚ)^k * ((2*(n+1)+2).choose k : ℚ)) =
        (-1 : ℚ)^(n+1) * ((2*(n+1)+1).choose (n+1) : ℚ) := by
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose
        (n := 2*(n+1)+1) (m := n+1))
    have hA' : (∑ k ∈ range (n+1), (-1 : ℚ)^k * ((2*(n+1)+1).choose k : ℚ)) =
        (-1 : ℚ)^n * ((2*(n+1)).choose n : ℚ) := by
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose
        (n := 2*(n+1)) (m := n))
    have hB : (∑ k ∈ range (n+1+1), (k : ℚ) * (-1 : ℚ)^k *
        ((2*(n+1)+2).choose k : ℚ)) =
        -(2*(n+1)+2 : ℚ) * ((-1 : ℚ)^n * ((2*(n+1)).choose n : ℚ)) := by
      rw [sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      calc
        _ = -(2*(n+1)+2 : ℚ) *
            (∑ k ∈ range (n+1), (-1 : ℚ)^k * ((2*(n+1)+1).choose k : ℚ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          have ht : (2*(n+1)+2 : ℚ) * ((2*(n+1)+1).choose k : ℚ) =
              ((2*(n+1)+2).choose (k+1) : ℚ) * (k+1 : ℚ) := by
            exact_mod_cast Nat.add_one_mul_choose_eq (2*(n+1)+1) k
          push_cast
          rw [pow_succ]
          linear_combination (-1 : ℚ)^k * ht
        _ = _ := by rw [hA']
    have hp : ((2*(n+1)+1).choose (n+1) : ℚ) =
        ((2*(n+1)).choose n : ℚ) + ((2*(n+1)).choose (n+1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ (2*(n+1)) n
    have hr : ((2*(n+1)).choose (n+1) : ℚ) * (n+1 : ℚ) =
        ((2*(n+1)).choose n : ℚ) * (n+2 : ℚ) := by
      have ht := Nat.choose_succ_right_eq (2*(n+1)) n
      rw [show 2*(n+1)-n = n+2 by omega] at ht
      exact_mod_cast ht
    calc
      _ = (n+1+1 : ℚ) *
          (∑ k ∈ range (n+1+1), (-1 : ℚ)^k * ((2*(n+1)+2).choose k : ℚ)) -
          ∑ k ∈ range (n+1+1), (k : ℚ) * (-1 : ℚ)^k * ((2*(n+1)+2).choose k : ℚ) := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro k hk
        push_cast
        ring
      _ = _ := by
        rw [hA, hB, hp, pow_succ]
        linear_combination -(-1 : ℚ)^n * hr

private lemma neg_pow_reflect (N i : ℕ) (hi : i ≤ N) (hN : Even N) :
    (-1 : ℚ)^(N-i) = (-1 : ℚ)^i := by
  apply mul_right_cancel₀ (pow_ne_zero i (by norm_num : (-1 : ℚ) ≠ 0))
  rw [← pow_add, Nat.sub_add_cancel hi, hN.neg_one_pow, ← mul_pow]
  simp

private def weight (N i : ℕ) : ℚ := (-1)^i * (N.choose i : ℚ) / (N.factorial : ℚ)

private lemma denom_inv (N i : ℕ) (hi : i ≤ N) (hN : Even N) :
    (∏ j ∈ (range (N+1)).erase i, ((i : ℚ)-j))⁻¹ = weight N i := by
  have hd := denom i (N-i)
  rw [Nat.add_sub_of_le hi] at hd
  have hf : (N.choose i : ℚ) * (i.factorial : ℚ) * ((N-i).factorial : ℚ) =
      (N.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hN0 : (N.factorial : ℚ) ≠ 0 := by positivity
  have hi0 : (i.factorial : ℚ) ≠ 0 := by positivity
  have hk0 : ((N-i).factorial : ℚ) ≠ 0 := by positivity
  rw [hd, mul_inv_rev, mul_inv_rev, ← inv_pow, inv_neg, inv_one,
    neg_pow_reflect N i hi hN]
  unfold weight
  apply (eq_div_iff hN0).mpr
  rw [← hf]
  field_simp

private lemma weight_reflect (N i : ℕ) (hi : i ≤ N) (hN : Even N) :
    weight N (N-i) = weight N i := by
  simp only [weight, neg_pow_reflect N i hi hN, Nat.choose_symm hi]

private lemma sign_reflect (N i : ℕ) (hi : i ≤ N) :
    (SignType.sign (((N-i : ℕ) : ℚ)-(N : ℚ)/2) : ℚ) =
      -(SignType.sign ((i : ℚ)-(N : ℚ)/2) : ℚ) := by
  rw [Nat.cast_sub hi]
  have h : (N : ℚ)-i-(N : ℚ)/2 = -((i : ℚ)-(N : ℚ)/2) := by ring
  rw [h, Left.sign_neg, SignType.coe_neg]

private lemma I_degree_le (N : ℕ) : (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))).natDegree ≤ N := by
  have hv : Set.InjOn (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (range (N+1)) := by
    intro a ha b hb h
    exact_mod_cast sub_left_inj.mp h
  apply natDegree_le_of_degree_le
  simpa only [card_range, Nat.add_sub_cancel] using
    Lagrange.degree_interpolate_le
      (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ)) hv

private lemma I_top_zero (N : ℕ) (hN : Even N) : (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))).coeff N = 0 := by
  let f : ℕ → ℚ := fun i =>
    (SignType.sign ((i : ℚ)-(N : ℚ)/2) : ℚ) * weight N i
  have he : (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))).coeff N = ∑ i ∈ range (N+1), f i := by
    simp only [Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul]
    apply sum_congr rfl
    intro i hi
    rw [ell_top N i (mem_range_succ_iff.mp hi),
      denom_inv N i (mem_range_succ_iff.mp hi) hN]
  rw [he]
  have hr := sum_range_reflect f (N+1)
  have hs : (∑ i ∈ range (N+1), f (N+1-1-i)) = -(∑ i ∈ range (N+1), f i) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ N := mem_range_succ_iff.mp hi
    change _ * _ = -(_ * _)
    rw [show N+1-1-i = N-i by omega, sign_reflect N i hi', weight_reflect N i hi' hN]
    ring
  linarith

private lemma symmetric_sum (f : ℕ → ℚ) (m : ℕ)
    (hf : ∀ i ≤ 2*m, f (2*m-i) = f i) (hm : f m = 0) :
    (∑ i ∈ range (2*m+1), f i) = 2 * ∑ i ∈ range m, f i := by
  rw [show 2*m+1 = m+(m+1) by omega, sum_range_add]
  have h : (∑ i ∈ range (m+1), f (m+i)) = ∑ i ∈ range (m+1), f i := by
    rw [← sum_range_reflect (fun i => f (m+i)) (m+1)]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := mem_range_succ_iff.mp hi
    rw [show m+(m+1-1-i) = 2*m-i by omega, hf i (by omega)]
  rw [h, sum_range_succ, hm]
  ring

private lemma I_pred_sum (m : ℕ) :
    (Lagrange.interpolate (Finset.range ((2*(m+1))+1)) (fun j : ℕ => (j : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) : ℚ))).coeff (2*(m+1)-1) =
      2 * ((-1 : ℚ)^m * ((2*m).choose m : ℚ)) / ((2*(m+1)).factorial : ℚ) := by
  let N := 2*(m+1)
  have hNe : Even N := even_two_mul (m + 1)
  have hNp : 0 < N := Nat.zero_lt_succ (Nat.mul 2 m + 1)
  let f : ℕ → ℚ := fun i =>
    (SignType.sign ((i : ℚ)-(N : ℚ)/2) : ℚ) * weight N i * ((i : ℚ)-(N : ℚ)/2)
  have he : (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))).coeff (N-1) = ∑ i ∈ range (N+1), f i := by
    simp only [Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul]
    apply sum_congr rfl
    intro i hi
    rw [ell_pred N i hNp (mem_range_succ_iff.mp hi),
      denom_inv N i (mem_range_succ_iff.mp hi) hNe]
    dsimp [f]
    ring
  have hs : (∑ i ∈ range (N+1), f i) = 2 * ∑ i ∈ range (m+1), f i := by
    apply symmetric_sum f (m+1)
    · intro i hi
      dsimp [f]
      change _ * weight N (N-i) * _ = _ * weight N i * _
      rw [sign_reflect N i hi, weight_reflect N i hi hNe, Nat.cast_sub hi]
      ring
    · dsimp [f, N]
      push_cast
      have h : (m+1 : ℚ) - 2*(m+1)/2 = 0 := by ring
      rw [h]
      simp
  have hl : (∑ i ∈ range (m+1), f i) =
      (∑ i ∈ range (m+1), ((m+1 : ℚ)-i) * (-1 : ℚ)^i * ((2*m+2).choose i : ℚ)) /
        (N.factorial : ℚ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    have hi' : i < m+1 := mem_range.mp hi
    have hcast : ((N : ℕ) : ℚ)/2 = m+1 := by dsimp [N]; push_cast; ring
    have hneg : (i : ℚ)-(N : ℚ)/2 < 0 := by
      rw [hcast, sub_neg]
      exact_mod_cast hi'
    dsimp [f, weight]
    rw [sign_neg hneg, SignType.coe_neg_one, hcast,
      show N = 2*m+2 by dsimp [N]; omega]
    ring
  change (Lagrange.interpolate (Finset.range (N+1)) (fun j : ℕ => (j : ℚ) - (N : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - (N : ℚ)/2) : ℚ))).coeff (N-1) = _
  rw [he, hs, hl, weighted_sum]
  dsimp [N]
  ring

private lemma I_pred_catalan (m : ℕ) :
    (Lagrange.interpolate (Finset.range ((2*(m+1))+1)) (fun j : ℕ => (j : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) : ℚ))).coeff (2*(m+1)-1) =
      (-1 : ℚ)^m * (catalan m : ℚ) / ((2*m+1).factorial : ℚ) := by
  rw [I_pred_sum]
  have hc : (m+1 : ℚ)*(catalan m : ℚ) = ((2*m).choose m : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom m
  rw [show 2*(m+1) = (2*m+1)+1 by omega, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, ← hc]
  have hfac : ((2*m+1).factorial : ℚ) ≠ 0 := by positivity
  have hm : (m+1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero m
  push_cast
  field_simp
  ring

private lemma leading_even (m : ℕ) :
    (Lagrange.interpolate (Finset.range ((2*(m+1))+1)) (fun j : ℕ => (j : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) : ℚ))).leadingCoeff =
      (-1 : ℚ)^m * (catalan m : ℚ) / ((2*m+1).factorial : ℚ) := by
  have hc : (catalan m : ℚ) ≠ 0 := by
    have h := succ_mul_catalan_eq_centralBinom m
    have hp := Nat.centralBinom_pos m
    have hn : catalan m ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at h
      omega
    exact_mod_cast hn
  have hn : (Lagrange.interpolate (Finset.range ((2*(m+1))+1)) (fun j : ℕ => (j : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) : ℚ))).coeff (2*(m+1)-1) ≠ 0 := by
    rw [I_pred_catalan]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc) (by positivity)
  have hd : (Lagrange.interpolate (Finset.range ((2*(m+1))+1)) (fun j : ℕ => (j : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) (fun i : ℕ => (SignType.sign ((i : ℚ) - ((2*(m+1) : ℕ) : ℚ)/2) : ℚ))).natDegree = 2*(m+1)-1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_le_pred (I_degree_le _) (I_top_zero _ (even_two_mul _))) hn
  rw [leadingCoeff, hd, I_pred_catalan]

theorem result : claim := by
  intro N hN hEven
  rw [← interpolate_source]
  obtain ⟨k, hk⟩ := hEven
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hNeq : N = 2*(m+1) := by omega
  rw [hNeq, show (2*(m+1)-2)/2 = m by omega, show 2*(m+1)-1 = 2*m+1 by omega]
  exact leading_even m


end D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk
