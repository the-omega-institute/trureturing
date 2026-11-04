/- GID: D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, mathlib/module/Mathlib.Data.ENat.Basic, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate, mathlib/module/Mathlib.Order.Bounds.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.claim; result=D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result; claim=D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.claim
   digest: The cyclic arrangement conjecture of arXiv:2610.33653v1 fails at (a,b)=(6,1): the valid-dimension supremum cannot equal the threshold maximum. -/

/-
   proof_shape: result=bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#22620; Refuted)
   Direct frozen dependencies: none
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Polynomials.JavaheriArrangementDimensionRefutation

open Set
open scoped BigOperators

/-- The exponent used on the right side of Javaheri's cyclic inequality. -/
noncomputable def c (a b : ℝ) : ℝ := (a + b + 1) / 2

/-- The cyclic inequality, with the successor taken modulo the dimension. -/
def arrangementInequality (a b : ℝ) (n : ℕ) (x : Fin n → ℝ) : Prop :=
  (∑ i : Fin n, x i) *
      (∑ i : Fin n, Real.rpow (x i) a * Real.rpow (x (finRotate n i)) b) ≤
    (∑ i : Fin n, Real.rpow (x i) (c a b)) ^ 2

/-- Positive dimensions in which the cyclic inequality holds for every nonnegative tuple. -/
def validDimensions (a b : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ ∀ x : Fin n → ℝ,
    (∀ i : Fin n, 0 ≤ x i) → arrangementInequality a b n x}

/-- The extended-natural least upper bound used for the largest valid dimension. -/
def IsN (a b : ℝ) (N : ℕ∞) : Prop :=
  IsLUB ((fun n : ℕ => (n : ℕ∞)) '' validDimensions a b) N

/-- The source threshold set, including its explicit one-dimensional exception. -/
def thresholdDimensions (a b : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧
    (n = 1 ∨ (a + b - 1) ^ 2 ≤ 8 * a * b * (Real.sin (Real.pi / (n : ℝ))) ^ 2)}

/-- The greatest-element specification for the source quantity N*. -/
def IsNStar (a b : ℝ) (Nstar : ℕ) : Prop :=
  IsGreatest (thresholdDimensions a b) Nstar

/-- Javaheri's Conjecture 1.3 with the implicit extrema made explicit. -/
def claim : Prop :=
  ∀ (a : ℝ) (b : ℝ), 0 ≤ a → 0 ≤ b → a + b ≠ 1 →
    (∃ (N : ℕ∞) (Nstar : ℕ), IsN a b N ∧ IsNStar a b Nstar) ∧
    ∀ (N : ℕ∞) (Nstar : ℕ), IsN a b N → IsNStar a b Nstar → N = (Nstar : ℕ∞)

private noncomputable def triple : Fin 3 → ℝ := fun i => if i = 0 then 6 else 5

private lemma triple_refutes : ¬ arrangementInequality 6 1 3 triple := by
  norm_num [arrangementInequality, triple, c, Fin.sum_univ_three, Real.rpow_natCast]

private lemma not_valid_three : 3 ∉ validDimensions 6 1 := by
  intro h
  have hineq := h.2 triple (by
    intro i
    simp [triple]
    split <;> norm_num)
  exact triple_refutes hineq

private lemma isNStar_three : IsNStar 6 1 3 := by
  refine ⟨?_, ?_⟩
  · constructor
    · norm_num
    · right
      norm_num [thresholdDimensions, Real.sin_pi_div_three]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · intro n hn
    rcases hn with ⟨hnpos, hncond⟩
    by_cases h1 : n = 1
    · omega
    by_cases h2 : n = 2
    · omega
    by_cases h3 : n = 3
    · omega
    have hn4 : 4 ≤ n := by omega
    have hncast : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hden : 0 < (n : ℝ) := by positivity
    have hfrac : Real.pi / (n : ℝ) ≤ Real.pi / 4 := by
      exact div_le_div_of_nonneg_left Real.pi_nonneg (by norm_num) hncast
    have harg0 : -(Real.pi / 2) ≤ Real.pi / (n : ℝ) := by
      have hpi : 0 ≤ Real.pi := Real.pi_nonneg
      have hnonneg : 0 ≤ Real.pi / (n : ℝ) := div_nonneg hpi hden.le
      linarith
    have harg1 : Real.pi / 4 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_nonneg]
    have hsin : Real.sin (Real.pi / (n : ℝ)) ≤ Real.sin (Real.pi / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two harg0 harg1 hfrac
    have hsin_nonneg : 0 ≤ Real.sin (Real.pi / (n : ℝ)) := by
      have harg_nonneg : 0 ≤ Real.pi / (n : ℝ) := div_nonneg Real.pi_nonneg hden.le
      exact Real.sin_nonneg_of_nonneg_of_le_pi harg_nonneg (by
        have hncast1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        exact (div_le_iff₀ hden).2 (by nlinarith [Real.pi_pos.le]))
    have hsquare : (Real.sin (Real.pi / (n : ℝ))) ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [Real.sin_pi_div_four] at hsin
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hbad : ¬ ((6 + 1 - 1 : ℝ)^2 ≤
        8 * 6 * 1 * (Real.sin (Real.pi / (n : ℝ))) ^ 2) := by
      nlinarith
    rcases hncond with h | h
    · omega
    · exact False.elim (hbad h)

/-- The explicit positive triple (6,5,5) refutes the universal conjecture. -/
theorem result : ¬ claim := by
  intro h
  have h6 := h 6 1 (by norm_num) (by norm_num) (by norm_num)
  rcases h6.1 with ⟨N, Nstar, hN, hNstar⟩
  have hstar : IsNStar 6 1 3 := isNStar_three
  have hNstar_eq : Nstar = 3 :=
    Nat.le_antisymm (hstar.2 hNstar.1) (hNstar.2 hstar.1)
  have hN_eq : N = (3 : ℕ∞) := h6.2 N 3 hN hstar
  have hN' : IsN 6 1 (3 : ℕ∞) := by simpa [hN_eq] using hN
  have hNupper : (3 : ℕ∞) ∈ upperBounds
      ((fun n : ℕ => (n : ℕ∞)) '' validDimensions 6 1) := by
    exact hN'.1
  have htwo_upper : (2 : ℕ∞) ∈ upperBounds
      ((fun n : ℕ => (n : ℕ∞)) '' validDimensions 6 1) := by
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    have hnle3_enat : (n : ℕ∞) ≤ 3 := hNupper ⟨n, hn, rfl⟩
    have hnle3 : n ≤ 3 := by exact_mod_cast hnle3_enat
    have hnne3 : n ≠ 3 := by
      intro hn3
      exact not_valid_three (hn3 ▸ hn)
    have hnle2 : n ≤ 2 := by omega
    exact ENat.natCast_le_natCast.mpr hnle2
  have hleast := hN'.2 htwo_upper
  norm_num at hleast

#print axioms claim
#print axioms result

end D5.S0.Certificates.Polynomials.JavaheriArrangementDimensionRefutation
