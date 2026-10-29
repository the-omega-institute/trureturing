/- GID: D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim; result=D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result; claim=D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim
   digest: A six-time Leggett-Garg family satisfies all polygon inequalities but has no joint law. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The six-time counterexample to polygon-plus-three-time sufficiency. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation

open scoped BigOperators

noncomputable section

def PairTables (n : ℕ) := Fin n → Fin n → Bool → Bool → ℝ

def IsPairFamily {n : ℕ} (p : PairTables n) : Prop :=
  (∀ i j, i < j → (∀ a b, 0 ≤ p i j a b) ∧ (∑ a, ∑ b, p i j a b = 1)) ∧
  ∃ m : Fin n → Bool → ℝ,
    ∀ i j, i < j →
      (∀ a, ∑ b, p i j a b = m i a) ∧
      (∀ b, ∑ a, p i j a b = m j b)

private def sgn (a : Bool) : ℝ := if a then 1 else -1

def corr {n : ℕ} (p : PairTables n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, sgn a * sgn b * p i j a b

def NGonInequalities {n : ℕ} (p : PairTables n) : Prop :=
  ∀ s : Fin n → Bool,
    (if Odd n then (1 : ℝ) else 0) ≤
      n + 2 * ∑ i, ∑ j, if i < j then sgn (s i) * sgn (s j) * corr p i j else 0

def ThreeTimeLG {n : ℕ} (p : PairTables n) : Prop :=
  ∀ i j k, i < j → j < k → ∀ a b c : Bool,
    0 ≤ 1 + sgn a * sgn b * corr p i j +
      sgn a * sgn c * corr p i k + sgn b * sgn c * corr p j k

def HasJointDistribution {n : ℕ} (p : PairTables n) : Prop :=
  ∃ μ : (Fin n → Bool) → ℝ,
    (∀ x, 0 ≤ μ x) ∧
    ∀ i j, i < j → ∀ a b,
      (∑ x with x i = a ∧ x j = b, μ x) = p i j a b

def claim : Prop :=
  ∀ (n : ℕ) (p : PairTables n), 3 ≤ n → IsPairFamily p →
    NGonInequalities p → ThreeTimeLG p → HasJointDistribution p

private def p : PairTables 6 := fun i j a b =>
  (1 + sgn a * sgn b * if i = 5 then (if j = 4 then -(1 : ℝ) / 2 else 1 / 2)
    else if j = 5 then (if i = 4 then -(1 : ℝ) / 2 else 1 / 2) else 0) / 4

private theorem p_family : IsPairFamily p := by
  change IsPairFamily (fun i j a b =>
    (1 + (if a then (1 : ℝ) else -1) * (if b then 1 else -1) *
      if i = 5 then (if j = 4 then -(1 : ℝ) / 2 else 1 / 2)
      else if j = 5 then (if i = 4 then -(1 : ℝ) / 2 else 1 / 2) else 0) / 4)
  refine ⟨?_, ?_⟩
  · intro i j hij
    constructor
    · intro a b
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num
    · fin_cases i <;> fin_cases j <;>
        norm_num [Fin.sum_univ_succ]
  · refine ⟨fun _ _ => (1 : ℝ) / 2, ?_⟩
    intro i j hij
    constructor <;> intro a <;> fin_cases i <;> fin_cases j <;> fin_cases a <;>
      norm_num [Fin.sum_univ_succ]

private theorem p_corr (i j : Fin 6) :
    corr p i j = if i = 5 then (if j = 4 then -(1 : ℝ) / 2 else 1 / 2)
      else if j = 5 then (if i = 4 then -(1 : ℝ) / 2 else 1 / 2) else 0 := by
  change (∑ a : Bool, ∑ b : Bool,
    (if a then (1 : ℝ) else -1) * (if b then 1 else -1) *
      ((1 + (if a then (1 : ℝ) else -1) * (if b then 1 else -1) *
        if i = 5 then (if j = 4 then -(1 : ℝ) / 2 else 1 / 2)
        else if j = 5 then (if i = 4 then -(1 : ℝ) / 2 else 1 / 2) else 0) / 4)) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
-- Enumerating the six Boolean signs expands the polygon expression completely.
private theorem p_ngon : NGonInequalities p := by
  have hodd : ¬ Odd (6 : ℕ) := by
    intro h
    rcases h with ⟨k, hk⟩
    omega
  intro s
  change (if Odd (6 : ℕ) then (1 : ℝ) else 0) ≤
    6 + 2 * ∑ i, ∑ j, if i < j then
      (if s i then (1 : ℝ) else -1) * (if s j then 1 else -1) * corr p i j else 0
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    cases h3 : s 3 <;> cases h4 : s 4 <;> cases h5 : s 5 <;>
    norm_num [p_corr, Fin.sum_univ_succ, hodd,
      h0, h1, h2, h3, h4, h5]
set_option maxHeartbeats 1000000 in
-- Enumerating the ordered triples and three signs closes the finite LG checks.
private theorem p_three : ThreeTimeLG p := by
  intro i j k hij hjk a b c
  change 0 ≤ 1 + (if a then (1 : ℝ) else -1) * (if b then 1 else -1) * corr p i j +
    (if a then 1 else -1) * (if c then 1 else -1) * corr p i k +
      (if b then 1 else -1) * (if c then 1 else -1) * corr p j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [p_corr]

private def b : Fin 6 → ℝ := ![1, 1, 1, 1, -1, -2]

private def weight (x : Fin 6 → Bool) : ℝ := ∑ i, b i * sgn (x i)

set_option maxHeartbeats 1000000 in
-- The square identity is discharged by the 64 Boolean assignments.
private theorem weight_sq_expand (x : Fin 6 → Bool) :
    weight x ^ 2 = ∑ i, b i ^ 2 +
      2 * ∑ i, ∑ j, if i < j then b i * b j * sgn (x i) * sgn (x j) else 0 := by
  change (∑ i : Fin 6, ![(1 : ℝ), 1, 1, 1, -1, -2] i *
      (if x i then 1 else -1)) ^ 2 =
    (∑ i : Fin 6, ![(1 : ℝ), 1, 1, 1, -1, -2] i ^ 2) +
      2 * ∑ i : Fin 6, ∑ j : Fin 6, if i < j then
        ![(1 : ℝ), 1, 1, 1, -1, -2] i * ![(1 : ℝ), 1, 1, 1, -1, -2] j *
          (if x i then 1 else -1) * (if x j then 1 else -1) else 0
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    norm_num [Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5]

private theorem sum_pair_fibers (μ : (Fin 6 → Bool) → ℝ) (i j : Fin 6) :
    ∑ x, μ x = ∑ a, ∑ b, ∑ x with x i = a ∧ x j = b, μ x := by
  have h := Finset.sum_fiberwise (s := (Finset.univ : Finset (Fin 6 → Bool)))
    (g := fun x : Fin 6 → Bool => (x i, x j)) μ
  rw [← h]
  rw [Fintype.sum_prod_type]
  congr 1

private theorem sum_mu_one (μ : (Fin 6 → Bool) → ℝ)
    (hμ : ∀ i j, i < j → ∀ a b,
      (∑ x with x i = a ∧ x j = b, μ x) = p i j a b) :
    ∑ x, μ x = 1 := by
  rw [sum_pair_fibers μ 0 1]
  simp_rw [hμ 0 1 (by omega)]
  exact (p_family.1 0 1 (by omega)).2

private theorem pair_expect (μ : (Fin 6 → Bool) → ℝ)
    (hμ : ∀ i j, i < j → ∀ a b,
      (∑ x with x i = a ∧ x j = b, μ x) = p i j a b)
    (i j : Fin 6) (hij : i < j) :
    ∑ x, μ x * (sgn (x i) * sgn (x j)) = corr p i j := by
  have h := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Fin 6 → Bool)))
    (g := fun x : Fin 6 → Bool => (x i, x j))
    (fun x => μ x * (sgn (x i) * sgn (x j)))
  rw [← h, Fintype.sum_prod_type]
  simp only [Finset.sum_filter, Prod.mk.injEq]
  congr 1
  funext a
  congr 1
  funext b
  rw [← Finset.sum_filter]
  calc
    (∑ x with x i = a ∧ x j = b,
        μ x * (sgn (x i) * sgn (x j))) =
      ∑ x with x i = a ∧ x j = b, (sgn a * sgn b) * μ x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx.1, hx.2]
        ring
    _ = sgn a * sgn b * ∑ x with x i = a ∧ x j = b, μ x := by
      rw [Finset.mul_sum]
    _ = sgn a * sgn b * p i j a b := by
      rw [hμ i j hij a b]

private theorem exchange_sum (μ : (Fin 6 → Bool) → ℝ)
    (f : (Fin 6 → Bool) → Fin 6 → Fin 6 → ℝ) :
    ∑ x, μ x * (∑ i, ∑ j, f x i j) = ∑ i, ∑ j, ∑ x, μ x * f x i j := by
  calc
    ∑ x, μ x * (∑ i, ∑ j, f x i j) = ∑ x, ∑ i, ∑ j, μ x * f x i j := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ x, μ x * f x i j := by
      rw [Finset.sum_comm]
      congr 1
      funext i
      rw [Finset.sum_comm]

private theorem weighted_square_sum (μ : (Fin 6 → Bool) → ℝ)
    (hμ : ∀ i j, i < j → ∀ a b,
      (∑ x with x i = a ∧ x j = b, μ x) = p i j a b) :
    ∑ x, μ x * weight x ^ 2 =
      (∑ i, b i ^ 2) * (∑ x, μ x) +
        2 * ∑ i, ∑ j, if i < j then b i * b j * corr p i j else 0 := by
  have hinner :
      (∑ i, ∑ j, ∑ x, μ x *
          (if i < j then b i * b j * sgn (x i) * sgn (x j) else 0)) =
        ∑ i, ∑ j, if i < j then
          b i * b j * corr p i j else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      calc
        _ = ∑ x, (b i * b j) * (μ x * (sgn (x i) * sgn (x j))) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = b i * b j * corr p i j := by
          rw [← Finset.mul_sum]
          rw [pair_expect μ hμ i j hij]
    · simp [hij]
  calc
    ∑ x, μ x * weight x ^ 2 =
        ∑ x, μ x * (∑ i, b i ^ 2 +
          2 * ∑ i, ∑ j, if i < j then b i * b j * sgn (x i) * sgn (x j) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [weight_sq_expand x]
    _ = (∑ i, b i ^ 2) * (∑ x, μ x) +
        2 * ∑ x, μ x * (∑ i, ∑ j,
          if i < j then b i * b j * sgn (x i) * sgn (x j) else 0) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      congr 1
      · ring
      · calc
        _ = ∑ x, 2 * (μ x * (∑ i, ∑ j,
              if i < j then b i * b j * sgn (x i) * sgn (x j) else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = (∑ i, b i ^ 2) * (∑ x, μ x) +
        2 * ∑ i, ∑ j, ∑ x, μ x *
          (if i < j then b i * b j * sgn (x i) * sgn (x j) else 0) := by
      rw [exchange_sum]
    _ = (∑ i, b i ^ 2) * (∑ x, μ x) +
        2 * ∑ i, ∑ j, if i < j then b i * b j * corr p i j else 0 := by
      rw [hinner]

private theorem weight_sq_lower (x : Fin 6 → Bool) : 1 ≤ weight x ^ 2 := by
  change (1 : ℝ) ≤ (∑ i : Fin 6, ![(1 : ℝ), 1, 1, 1, -1, -2] i *
    (if x i then 1 else -1)) ^ 2
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    norm_num [Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5]

private theorem p_no_joint : ¬ HasJointDistribution p := by
  rintro ⟨μ, hμ_nonneg, hμ⟩
  have hsum : ∑ x, μ x = 1 := sum_mu_one μ hμ
  have hlower : 1 ≤ ∑ x, μ x * weight x ^ 2 := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro x hx
    have hm := mul_le_mul_of_nonneg_left (weight_sq_lower x) (hμ_nonneg x)
    simpa using hm
  have hexpect := weighted_square_sum μ hμ
  have heval : ∑ x, μ x * weight x ^ 2 = -1 := by
    rw [hexpect, hsum]
    change (∑ i : Fin 6, ![(1 : ℝ), 1, 1, 1, -1, -2] i ^ 2) * 1 +
      2 * (∑ i : Fin 6, ∑ j : Fin 6, if i < j then
        ![(1 : ℝ), 1, 1, 1, -1, -2] i * ![(1 : ℝ), 1, 1, 1, -1, -2] j * corr p i j
        else 0) = -1
    norm_num [p_corr, Fin.sum_univ_succ]
  linarith

theorem result : ¬ claim := by
  intro h
  exact p_no_joint (h 6 p (by omega) p_family p_ngon p_three)

end
end D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation
