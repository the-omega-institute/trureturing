/- GID: D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.claim; result=D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result; claim=D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.claim
   digest: Two positive normalized stationary states at C = 10 refute uniqueness. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation

open scoped BigOperators

noncomputable section

/-! The dynamics use the net-flux reading of Eq. (1) in Myhill and Blumenfeld,
J. Phys. A 56, 345001, arXiv:2306.10526v2, consistent with the flux and Eq. (2)
in §I.A. In particular, the reverse loss flux uses the product-order fraction.
The normalization term remains part of the general right-hand side. -/

def J (C : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 3 C).product (Finset.Icc 3 C)).filter
    (fun a => a.1 ≤ a.2 ∧ a.1 + a.2 - 2 ≤ C)

def delta (i j : ℕ) : ℝ :=
  if i = j then 1 else 0

def flux
    (p q : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ)
    (i j : ℕ) : ℝ :=
  p (min i j) (max i j) * Q i * Q j
    - q (min i j) (max i j) * Q (i + j - 2)

def rhs
    (C : ℕ)
    (p q : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ)
    (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
      (∑ i ∈ Finset.Icc 3 (k - 1),
        flux p q Q i (k - i + 2) *
          (1 + delta i (k - i + 2)))
    - (∑ i ∈ Finset.Icc (k + 1) C,
        flux p q Q k (i - k + 2) *
          (1 + delta i (2 * k - 2)))
    + Q k * (∑ a ∈ J C, flux p q Q a.1 a.2)

def PositiveRates
    (C : ℕ)
    (p q : ℕ → ℕ → ℝ) : Prop :=
  ∀ a ∈ J C, 0 < p a.1 a.2 ∧ 0 < q a.1 a.2

def Physical (C : ℕ) (Q : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 3 ≤ k → k ≤ C → 0 < Q k) ∧
    (∑ k ∈ Finset.Icc 3 C, Q k) = 1

def Stationary
    (C : ℕ)
    (p q : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ C → rhs C p q Q k = 0

def claim : Prop :=
  ∀ C : ℕ, 3 ≤ C →
    ∀ p q : ℕ → ℕ → ℝ,
      PositiveRates C p q →
      ∀ Q Q' : ℕ → ℝ,
        Physical C Q →
        Physical C Q' →
        Stationary C p q Q →
        Stationary C p q Q' →
        ∀ k : ℕ, 3 ≤ k → k ≤ C → Q k = Q' k

private def p10 (i j : ℕ) : ℝ :=
  if i = 3 ∧ j = 3 then 10 / 3 else
  if i = 3 ∧ j = 4 then 2 / 3 else
  if i = 3 ∧ j = 5 then 4 / 15 else
  if i = 3 ∧ j = 6 then 4 / 3 else
  if i = 3 ∧ j = 7 then 2 / 3 else
  if i = 3 ∧ j = 8 then 2 else
  if i = 3 ∧ j = 9 then 509018 / 225 else
  if i = 4 ∧ j = 4 then 1 else
  if i = 4 ∧ j = 5 then 35579 / 175 else
  if i = 4 ∧ j = 6 then 2 else
  if i = 4 ∧ j = 7 then 422 / 5 else
  if i = 4 ∧ j = 8 then 2 else
  if i = 5 ∧ j = 5 then 386 / 225 else
  if i = 5 ∧ j = 6 then 30416 / 25 else
  if i = 5 ∧ j = 7 then 255689 / 25 else
  if i = 6 ∧ j = 6 then 4 else
  1

private def q10 (i j : ℕ) : ℝ :=
  if i = 3 ∧ j = 3 then 1 else
  if i = 3 ∧ j = 4 then 2 / 5 else
  if i = 3 ∧ j = 5 then 2 else
  if i = 3 ∧ j = 6 then 972 / 5 else
  if i = 3 ∧ j = 7 then 2 else
  if i = 3 ∧ j = 8 then 2 else
  if i = 3 ∧ j = 9 then 2138 / 75 else
  if i = 4 ∧ j = 4 then 141 / 10 else
  if i = 4 ∧ j = 5 then 1 else
  if i = 4 ∧ j = 6 then 2 else
  if i = 4 ∧ j = 7 then 2 else
  if i = 4 ∧ j = 8 then 3967 / 35 else
  if i = 5 ∧ j = 5 then 35878 / 315 else
  if i = 5 ∧ j = 6 then 2 else
  if i = 5 ∧ j = 7 then 233557 / 35 else
  if i = 6 ∧ j = 6 then 2 else
  1

private def X (k : ℕ) : ℝ :=
  if k = 3 then 3 / 16 else
  if k = 4 then 2 / 16 else
  if k = 5 then 5 / 16 else
  if k = 6 then 1 / 16 else
  if k = 7 then 2 / 16 else
  if k = 8 then 1 / 16 else
  if k = 9 then 1 / 16 else
  if k = 10 then 1 / 16 else
  0

private def Y (k : ℕ) : ℝ :=
  if k = 3 then 12 / 34 else
  if k = 4 then 6 / 34 else
  if k = 5 then 5 / 34 else
  if k = 6 then 4 / 34 else
  if k = 7 then 4 / 34 else
  if k = 8 then 1 / 34 else
  if k = 9 then 1 / 34 else
  if k = 10 then 1 / 34 else
  0

private def sum10 (e : ℕ → ℕ → ℝ) : ℝ :=
  e 3 3 + e 3 4 + e 3 5 + e 3 6
    + e 3 7 + e 3 8 + e 3 9
    + e 4 4 + e 4 5 + e 4 6 + e 4 7 + e 4 8
    + e 5 5 + e 5 6 + e 5 7 + e 6 6

private def balance10 (e : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 3 then
    -(2 * e 3 3 + e 3 4 + e 3 5 + e 3 6
      + e 3 7 + e 3 8 + e 3 9)
  else if k = 4 then
    e 3 3 - (e 3 4 + 2 * e 4 4 + e 4 5
      + e 4 6 + e 4 7 + e 4 8)
  else if k = 5 then
    e 3 4 - (e 3 5 + e 4 5 + 2 * e 5 5
      + e 5 6 + e 5 7)
  else if k = 6 then
    e 3 5 + e 4 4
      - (e 3 6 + e 4 6 + e 5 6 + 2 * e 6 6)
  else if k = 7 then
    e 3 6 + e 4 5 - (e 3 7 + e 4 7 + e 5 7)
  else if k = 8 then
    e 3 7 + e 4 6 + e 5 5 - (e 3 8 + e 4 8)
  else if k = 9 then
    e 3 8 + e 4 7 + e 5 6 - e 3 9
  else if k = 10 then
    e 3 9 + e 4 8 + e 5 7 + e 6 6
  else 0

private theorem J10 :
    J 10 =
      {(3, 3), (3, 4), (3, 5), (3, 6),
       (3, 7), (3, 8), (3, 9),
       (4, 4), (4, 5), (4, 6), (4, 7), (4, 8),
       (5, 5), (5, 6), (5, 7), (6, 6)} := by
  decide

private theorem sum_J10 (e : ℕ → ℕ → ℝ) :
    (∑ a ∈ J 10, e a.1 a.2) = sum10 e := by
  rw [J10, sum10.eq_1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]
  ring

private theorem sum_Icc_3_10 (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 3 10, f k) =
      f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  norm_num [Finset.sum_Icc_succ_top]

private theorem rhs10
    (p q : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ)
    (k : ℕ)
    (hlo : 3 ≤ k)
    (hhi : k ≤ 10) :
    rhs 10 p q Q k =
      balance10 (flux p q Q) k
        + Q k * sum10 (flux p q Q) := by
  unfold rhs
  rw [sum_J10]
  apply congrArg (fun t : ℝ => t + Q k * sum10 (flux p q Q))
  interval_cases k <;>
    simp only [delta.eq_1, flux.eq_1, balance10.eq_1] <;>
    norm_num [Finset.sum_Icc_succ_top] <;> ring

private theorem rates10_positive :
    PositiveRates 10 p10 q10 := by
  intro a ha
  rw [J10] at ha
  fin_cases ha <;> rw [p10.eq_1, q10.eq_1] <;> norm_num

private theorem X_physical : Physical 10 X := by
  constructor
  · intro k hlo hhi
    interval_cases k <;> norm_num [X]
  · rw [sum_Icc_3_10]
    norm_num [X]

private theorem Y_physical : Physical 10 Y := by
  constructor
  · intro k hlo hhi
    interval_cases k <;> norm_num [Y]
  · rw [sum_Icc_3_10]
    norm_num [Y]

private theorem X_sum_zero : sum10 (flux p10 q10 X) = 0 := by
  norm_num [sum10, flux, p10, q10, X]

private theorem Y_sum_zero : sum10 (flux p10 q10 Y) = 0 := by
  norm_num [sum10, flux, p10, q10, Y]

private theorem X_balance_zero
    (k : ℕ) (hlo : 3 ≤ k) (hhi : k ≤ 10) :
    balance10 (flux p10 q10 X) k = 0 := by
  interval_cases k <;> norm_num [balance10, flux, p10, q10, X]

private theorem Y_balance_zero
    (k : ℕ) (hlo : 3 ≤ k) (hhi : k ≤ 10) :
    balance10 (flux p10 q10 Y) k = 0 := by
  interval_cases k <;> norm_num [balance10, flux, p10, q10, Y]

private theorem X_stationary : Stationary 10 p10 q10 X := by
  intro k hlo hhi
  rw [rhs10 p10 q10 X k hlo hhi, X_balance_zero k hlo hhi, X_sum_zero]
  simp

private theorem Y_stationary : Stationary 10 p10 q10 Y := by
  intro k hlo hhi
  rw [rhs10 p10 q10 Y k hlo hhi, Y_balance_zero k hlo hhi, Y_sum_zero]
  simp

private theorem X3_ne_Y3 : X 3 ≠ Y 3 := by
  rw [X.eq_1, Y.eq_1]
  norm_num

/-- The universal uniqueness conjecture fails at C = 10 with strictly positive rates. -/
theorem result : ¬ claim := by
  intro h
  have h3 : X 3 = Y 3 :=
    h 10 (by norm_num)
      p10 q10 rates10_positive
      X Y X_physical Y_physical
      X_stationary Y_stationary
      3 (by norm_num) (by norm_num)
  exact X3_ne_Y3 h3

end

end D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation
