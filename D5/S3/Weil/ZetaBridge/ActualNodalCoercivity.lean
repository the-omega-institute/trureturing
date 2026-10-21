/- GID: D5/S3/Weil/ZetaBridge/ActualNodalCoercivity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualNodalCoercivity
   mirror-E: none(waiver:finite-nodal-reconstruction-estimate)
   anchors: []
   utility: none
   digest: Represent the actual arithmetic columns by nodal polynomials and reconstruct finite heads uniformly from coefficients. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Actual nodal polynomials and uniform finite reconstruction

The common denominator and the two numerators use the unnormalised Lagrange
nodal products. Clearing the actual real divided difference preserves its
complex cast and its factor of pi. No analytic hypothesis on c is needed.

The coefficient estimate is the usual Lagrange node-separation argument
followed by finite Cauchy--Schwarz. Its explicit constant depends only on the
finite integer nodes and their radius. It includes the zero vector and a
singleton set. These are finite algebraic estimates; they do not assert an
infinite paired-tail estimate or positivity of the physical Weil form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ActualNodalCoercivity

open scoped BigOperators
open Polynomial
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- The common denominator, exactly the product of X minus each integer node. -/
def D (S : Finset ℤ) : ℂ[X] :=
  Lagrange.nodal S (fun n : ℤ => (n : ℂ))

/-- The unnormalised interpolation numerator of the finite head. -/
def Q (S : Finset ℤ) (v : ℤ → ℂ) : ℂ[X] :=
  ∑ n ∈ S, C (v n) * Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))

/-- The same numerator with the actual arithmetic boundary symbol as weight. -/
def P (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) : ℂ[X] :=
  ∑ n ∈ S, C ((arithmeticBoundarySymbol c n : ℂ) * v n) *
    Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))

private theorem numerator_natDegree_lt (S : Finset ℤ) (hS : S.Nonempty)
    (v : ℤ → ℂ) : (Q S v).natDegree < S.card := by
  classical
  have hle : (Q S v).natDegree ≤ S.card - 1 := by
    unfold Q
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    calc
      (C (v n) * Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).natDegree
          ≤ (Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = (S.erase n).card := Lagrange.natDegree_nodal
      _ = S.card - 1 := Finset.card_erase_of_mem hn
  exact lt_of_le_of_lt hle (Nat.sub_lt hS.card_pos (by decide))

private theorem denominator_eval_ne_zero (S : Finset ℤ) (m : ℤ) (hm : m ∉ S) :
    (D S).eval (m : ℂ) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro n hn hmn
  have heq : m = n := by exact_mod_cast hmn
  exact hm (by simpa only [heq] using hn)

private theorem denominator_eval_split (S : Finset ℤ) (m n : ℤ) (hn : n ∈ S) :
    (D S).eval (m : ℂ) = ((m : ℂ) - (n : ℂ)) *
      (Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).eval (m : ℂ) := by
  unfold D
  rw [Lagrange.nodal_eq_mul_nodal_erase hn, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

private theorem clear_actual_summand (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (m : ℤ) (hm : m ∉ S) (n : ℤ) (hn : n ∈ S) :
    (Real.pi : ℂ) * (D S).eval (m : ℂ) *
        (((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
          (Real.pi * ((m : ℝ) - (n : ℝ)))) : ℝ) : ℂ) * v n) =
      ((arithmeticBoundarySymbol c n : ℂ) * v n) *
          (Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).eval (m : ℂ) -
        (arithmeticBoundarySymbol c m : ℂ) *
          (v n * (Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).eval
            (m : ℂ)) := by
  have hden := denominator_eval_ne_zero S m hm
  rw [denominator_eval_split S m n hn] at hden
  have hdiff : (m : ℂ) - (n : ℂ) ≠ 0 := (mul_ne_zero_iff.mp hden).1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [denominator_eval_split S m n hn]
  push_cast
  field_simp [hpi, hdiff] <;> ring

/-- Exact polynomial representation of the actual arithmetic divided-difference
column. Both numerator degrees are strictly below the number of head nodes. -/
theorem actual_nodal_polynomial_model (c : ℕ) (S : Finset ℤ) (hS : S.Nonempty)
    (v : ℤ → ℂ) :
    (P c S v).natDegree < S.card ∧ (Q S v).natDegree < S.card ∧
      ∀ m : ℤ, m ∉ S →
        (Real.pi : ℂ) * (D S).eval (m : ℂ) * couplingColumn c S v m =
          (P c S v).eval (m : ℂ) -
            (arithmeticBoundarySymbol c m : ℂ) * (Q S v).eval (m : ℂ) := by
  classical
  refine ⟨?_, numerator_natDegree_lt S hS v, ?_⟩
  · exact numerator_natDegree_lt S hS
      (fun n => (arithmeticBoundarySymbol c n : ℂ) * v n)
  · intro m hm
    simp only [couplingColumn, P, Q, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n hn => clear_actual_summand c S v m hm n hn)

theorem numerator_eval_node (S : Finset ℤ) (v : ℤ → ℂ)
    (n : ℤ) (hn : n ∈ S) :
    (Q S v).eval (n : ℂ) = v n *
      (Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).eval (n : ℂ) := by
  classical
  simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_eq_single n
  · intro j _ hjn
    have hmem : n ∈ S.erase j := Finset.mem_erase.mpr ⟨hjn.symm, hn⟩
    rw [Lagrange.eval_nodal_at_node hmem, mul_zero]
  · intro hnot
    exact (hnot hn).elim

private theorem norm_integer_node (n : ℤ) : ‖(n : ℂ)‖ = (n.natAbs : ℝ) := by
  simp only [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem erased_node_norm_one_le (S : Finset ℤ) (n : ℤ) :
    1 ≤ ‖(Lagrange.nodal (S.erase n) (fun j : ℤ => (j : ℂ))).eval (n : ℂ)‖ := by
  classical
  rw [Lagrange.eval_nodal, norm_prod]
  apply Finset.one_le_prod₀
  intro j hj
  have hnj : n - j ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hj).1.symm
  have hsep : 1 ≤ (n - j).natAbs := by
    have hpos : (n - j).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnj
    exact Nat.one_le_iff_ne_zero.mpr hpos
  rw [← Int.cast_sub, norm_integer_node]
  exact_mod_cast hsep

private theorem head_norm_sq_le_node (S : Finset ℤ) (v : ℤ → ℂ)
    (n : ℤ) (hn : n ∈ S) : ‖v n‖ ^ 2 ≤ ‖(Q S v).eval (n : ℂ)‖ ^ 2 := by
  have hnorm : ‖v n‖ ≤ ‖(Q S v).eval (n : ℂ)‖ := by
    rw [numerator_eval_node S v n hn, norm_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (erased_node_norm_one_le S n) (norm_nonneg (v n))
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

private theorem evaluation_norm_sq_le (p : ℂ[X]) (d A : ℕ)
    (hp : p.natDegree < d) (hA : 1 ≤ A) (n : ℤ) (hn : n.natAbs ≤ A) :
    ‖p.eval (n : ℂ)‖ ^ 2 ≤
      (d : ℝ) * (A : ℝ) ^ (2 * (d - 1)) *
        ∑ r ∈ Finset.range d, ‖p.coeff r‖ ^ 2 := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hnA : ‖(n : ℂ)‖ ≤ (A : ℝ) := by
    rw [norm_integer_node]
    exact_mod_cast hn
  have htriangle : ‖p.eval (n : ℂ)‖ ≤
      ∑ r ∈ Finset.range d, ‖p.coeff r‖ * ‖(n : ℂ)‖ ^ r := by
    rw [Polynomial.eval_eq_sum_range' hp]
    simpa only [norm_mul, norm_pow] using
      norm_sum_le (Finset.range d) (fun r => p.coeff r * (n : ℂ) ^ r)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range d)
    (fun r => ‖p.coeff r‖) (fun r => ‖(n : ℂ)‖ ^ r)
  have hpowers : (∑ r ∈ Finset.range d, (‖(n : ℂ)‖ ^ r) ^ 2) ≤
      (d : ℝ) * (A : ℝ) ^ (2 * (d - 1)) := by
    calc
      (∑ r ∈ Finset.range d, (‖(n : ℂ)‖ ^ r) ^ 2)
          ≤ ∑ _r ∈ Finset.range d, (A : ℝ) ^ (2 * (d - 1)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrle : r ≤ d - 1 := by
          have hrlt := Finset.mem_range.mp hr
          omega
        calc
          (‖(n : ℂ)‖ ^ r) ^ 2 ≤ ((A : ℝ) ^ r) ^ 2 :=
            pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r)
              (pow_le_pow_left₀ (norm_nonneg _) hnA r) 2
          _ = (A : ℝ) ^ (2 * r) := by rw [← pow_mul, Nat.mul_comm r 2]
          _ ≤ (A : ℝ) ^ (2 * (d - 1)) :=
            pow_le_pow_right₀ hAreal (Nat.mul_le_mul_left 2 hrle)
      _ = _ := by simp
  have henergy : 0 ≤ ∑ r ∈ Finset.range d, ‖p.coeff r‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    ‖p.eval (n : ℂ)‖ ^ 2
        ≤ (∑ r ∈ Finset.range d, ‖p.coeff r‖ * ‖(n : ℂ)‖ ^ r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ r ∈ Finset.range d, ‖p.coeff r‖ ^ 2) *
        ∑ r ∈ Finset.range d, (‖(n : ℂ)‖ ^ r) ^ 2 := hcs
    _ ≤ (∑ r ∈ Finset.range d, ‖p.coeff r‖ ^ 2) *
        ((d : ℝ) * (A : ℝ) ^ (2 * (d - 1))) :=
      mul_le_mul_of_nonneg_left hpowers henergy
    _ = _ := by ring

private theorem finite_head_reconstruction (S : Finset ℤ) (A : ℕ)
    (hS : S.Nonempty) (hA : 1 ≤ A) (hbound : ∀ n ∈ S, n.natAbs ≤ A)
    (v : ℤ → ℂ) :
    (∑ n ∈ S, ‖v n‖ ^ 2) ≤
      (S.card : ℝ) ^ 2 * (A : ℝ) ^ (2 * (S.card - 1)) *
        ∑ r ∈ Finset.range S.card, ‖(Q S v).coeff r‖ ^ 2 := by
  calc
    (∑ n ∈ S, ‖v n‖ ^ 2) ≤ ∑ n ∈ S, ‖(Q S v).eval (n : ℂ)‖ ^ 2 :=
      Finset.sum_le_sum (fun n hn => head_norm_sq_le_node S v n hn)
    _ ≤ ∑ _n ∈ S, (S.card : ℝ) * (A : ℝ) ^ (2 * (S.card - 1)) *
        ∑ r ∈ Finset.range S.card, ‖(Q S v).coeff r‖ ^ 2 :=
      Finset.sum_le_sum (fun n hn => evaluation_norm_sq_le (Q S v) S.card A
        (numerator_natDegree_lt S hS v) hA n (hbound n hn))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

private theorem reconstruction_denominator_pos (S : Finset ℤ) (A : ℕ)
    (hS : S.Nonempty) (hA : 1 ≤ A) :
    0 < (S.card : ℝ) ^ 2 * (A : ℝ) ^ (2 * (S.card - 1)) := by
  have hd : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hAr : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  exact mul_pos (pow_pos hd 2) (pow_pos hAr _)

/-- An explicit reconstruction estimate uniform in every coefficient vector and
every positive natural scale. The radius and its hypotheses precede both. -/
theorem uniform_coefficient_reconstruction (S : Finset ℤ) (A : ℕ)
    (hS : S.Nonempty) (hA : 1 ≤ A) (hbound : ∀ n ∈ S, n.natAbs ≤ A)
    (c : ℕ) (v : ℤ → ℂ) (N : ℕ) (hN : 0 < N) :
    (1 / ((S.card : ℝ) ^ 2 * (A : ℝ) ^ (2 * (S.card - 1)))) *
        (∑ n ∈ S, ‖v n‖ ^ 2) ≤
      ∑ r ∈ Finset.range S.card, (N : ℝ) ^ (2 * r) *
        (‖(P c S v).coeff r‖ ^ 2 + ‖(Q S v).coeff r‖ ^ 2) := by
  have hden := reconstruction_denominator_pos S A hS hA
  have hraw := finite_head_reconstruction S A hS hA hbound v
  have hQ : (1 / ((S.card : ℝ) ^ 2 * (A : ℝ) ^ (2 * (S.card - 1)))) *
      (∑ n ∈ S, ‖v n‖ ^ 2) ≤
        ∑ r ∈ Finset.range S.card, ‖(Q S v).coeff r‖ ^ 2 := by
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hraw
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  refine le_trans hQ (Finset.sum_le_sum ?_)
  intro r _
  have hscale : (1 : ℝ) ≤ (N : ℝ) ^ (2 * r) := one_le_pow₀ hNreal
  have hsum : 0 ≤ ‖(P c S v).coeff r‖ ^ 2 + ‖(Q S v).coeff r‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    ‖(Q S v).coeff r‖ ^ 2 ≤
        ‖(P c S v).coeff r‖ ^ 2 + ‖(Q S v).coeff r‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ ≤ (N : ℝ) ^ (2 * r) *
        (‖(P c S v).coeff r‖ ^ 2 + ‖(Q S v).coeff r‖ ^ 2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hsum

end D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
