/- GID: D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim; result=D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result; claim=D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim
   digest: A six-time Leggett-Garg family satisfies all polygon inequalities but has no joint law. -/

import Mathlib

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

def sgn (a : Bool) : ℝ := if a then 1 else -1

def corr {n : ℕ} (p : PairTables n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, sgn a * sgn b * p i j a b

def NGonInequalities {n : ℕ} (p : PairTables n) : Prop :=
  ∀ s : Fin n → Bool,
    (if Odd n then (1 : ℝ) else 0) ≤
      n + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, sgn (s i) * sgn (s j) * corr p i j

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
  refine ⟨?_, ?_⟩
  · intro i j hij
    constructor
    · intro a b
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [p, sgn]
    · fin_cases i <;> fin_cases j <;>
        norm_num [p, sgn, Fin.sum_univ_succ]
  · refine ⟨fun _ _ => (1 : ℝ) / 2, ?_⟩
    intro i j hij
    constructor <;> intro a <;> fin_cases i <;> fin_cases j <;> fin_cases a <;>
      norm_num [p, sgn, Fin.sum_univ_succ]
private theorem p_ngon : NGonInequalities p := by sorry
private theorem p_three : ThreeTimeLG p := by sorry
private theorem p_no_joint : ¬ HasJointDistribution p := by sorry

theorem result : ¬ claim := by
  intro h
  exact p_no_joint (h 6 p (by omega) p_family p_ngon p_three)

end
end D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation
