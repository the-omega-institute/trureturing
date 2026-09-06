/- GID: D5/S3/StatisticalMechanics/HardCore/BranchingPotential
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/BranchingPotential
   mirror-E: none(waiver:symbolic-induction)
   anchors: []
   digest: Integer potentials bound controlled branching at every depth and history. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.BranchingPotential

open scoped BigOperators

variable {State Action Direction : Type*} [Fintype Direction]

/-- The weighted number of children, with an absent child contributing zero. -/
def childWeight (step : State → Action → Direction → Option State)
    (w : State → ℕ) (i : State) (a : Action) : ℕ :=
  ∑ d, (step i a d).elim 0 w

/-- Number of depth-n descendants. The controller can depend on the entire
newest-first direction history and on the current state. -/
def pathCount (step : State → Action → Direction → Option State)
    (policy : List Direction → State → Action) : ℕ → List Direction → State → ℕ
  | 0, _, _ => 1
  | n + 1, history, i =>
      ∑ d, (step i (policy history i) d).elim 0
        (pathCount step policy n (d :: history))

/-- A positive integer super-potential gives an all-depth upper bound for
one specified controller. No spectral radius or asymptotic hypothesis is used. -/
theorem upper_of_superpotential
    (step : State → Action → Direction → Option State)
    (policy : List Direction → State → Action) (w : State → ℕ)
    (numerator denominator : ℕ) (hw : ∀ i, 1 ≤ w i)
    (hrow : ∀ history i,
      denominator * childWeight step w i (policy history i) ≤ numerator * w i)
    (n : ℕ) (history : List Direction) (i : State) :
    denominator ^ n * pathCount step policy n history i ≤ numerator ^ n * w i := by
  induction n generalizing history i with
  | zero => simpa [pathCount] using hw i
  | succ n ih =>
      have hs : denominator ^ n * pathCount step policy (n + 1) history i ≤
          numerator ^ n * childWeight step w i (policy history i) := by
        simp only [pathCount, childWeight, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        cases hnext : step i (policy history i) d with
        | none => simp
        | some j => simpa using ih (d :: history) j
      calc
        denominator ^ (n + 1) * pathCount step policy (n + 1) history i =
            denominator * (denominator ^ n *
              pathCount step policy (n + 1) history i) := by rw [pow_succ]; ring
        _ ≤ denominator * (numerator ^ n *
              childWeight step w i (policy history i)) := Nat.mul_le_mul_left _ hs
        _ = numerator ^ n *
              (denominator * childWeight step w i (policy history i)) := by ring
        _ ≤ numerator ^ n * (numerator * w i) :=
          Nat.mul_le_mul_left _ (hrow history i)
        _ = numerator ^ (n + 1) * w i := by rw [pow_succ]; ring

/-- A bounded nonnegative sub-potential gives an all-depth lower bound.
The row inequality must hold for the actions actually selected at every history. -/
theorem lower_of_subpotential
    (step : State → Action → Direction → Option State)
    (policy : List Direction → State → Action) (w : State → ℕ)
    (numerator denominator cap : ℕ) (hw : ∀ i, w i ≤ cap)
    (hrow : ∀ history i,
      numerator * w i ≤ denominator * childWeight step w i (policy history i))
    (n : ℕ) (history : List Direction) (i : State) :
    numerator ^ n * w i ≤ cap * denominator ^ n * pathCount step policy n history i := by
  induction n generalizing history i with
  | zero => simpa [pathCount] using hw i
  | succ n ih =>
      have hs : numerator ^ n * childWeight step w i (policy history i) ≤
          cap * denominator ^ n * pathCount step policy (n + 1) history i := by
        simp only [pathCount, childWeight, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        cases hnext : step i (policy history i) d with
        | none => simp
        | some j => simpa using ih (d :: history) j
      calc
        numerator ^ (n + 1) * w i = numerator ^ n * (numerator * w i) := by
          rw [pow_succ]; ring
        _ ≤ numerator ^ n *
              (denominator * childWeight step w i (policy history i)) :=
          Nat.mul_le_mul_left _ (hrow history i)
        _ = denominator *
              (numerator ^ n * childWeight step w i (policy history i)) := by ring
        _ ≤ denominator * (cap * denominator ^ n *
              pathCount step policy (n + 1) history i) := Nat.mul_le_mul_left _ hs
        _ = cap * denominator ^ (n + 1) *
              pathCount step policy (n + 1) history i := by rw [pow_succ]; ring

#print axioms upper_of_superpotential
#print axioms lower_of_subpotential

end D5.S3.StatisticalMechanics.HardCore.BranchingPotential
