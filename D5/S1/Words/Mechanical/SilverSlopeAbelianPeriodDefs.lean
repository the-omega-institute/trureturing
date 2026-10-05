/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Boolean abelian decompositions and the silver-slope candidate set. -/
/-
Judgement form:
  silverSlope:
    proof_shape: definition
    escape_witness: none (literal definition)
  AbelianDecomposition:
    proof_shape: definition
    escape_witness: none (literal definition)
  AbelianPeriod:
    proof_shape: definition
    escape_witness: none (literal definition)
  minAbelianPeriod:
    proof_shape: definition
    escape_witness: none (literal definition)
  abelianPeriodSet:
    proof_shape: definition
    escape_witness: none (literal definition)
  silverAbelianPeriodSet:
    proof_shape: definition
    escape_witness: none (literal definition)
  silverCandidateSet:
    proof_shape: definition
    escape_witness: none (literal definition)
admission_basis: none (definitions consumed by the settling result)
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Recurrence.PellCompanionGcd
import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd
open Set
open D5.S1.Words.Complexity
noncomputable def silverSlope : Real := Real.sqrt 2 - 1
def AbelianDecomposition (w : List Bool) (m : Nat) : Prop :=
  0 < m ∧
    ∃ head tail : List Bool, ∃ blocks : List (List Bool),
      blocks ≠ [] ∧
      w = head ++ blocks.flatten ++ tail ∧
      (∀ b ∈ blocks, b.length = m) ∧
      (∀ a ∈ blocks, ∀ b ∈ blocks, parikh a = parikh b) ∧
      (∃ p : Nat × Nat, (∀ b ∈ blocks, parikh b = p) ∧
        (parikh head) < p ∧ (parikh tail) < p)
def AbelianPeriod (w : List Bool) (m : Nat) : Prop :=
  AbelianDecomposition w m
noncomputable def minAbelianPeriod (w : List Bool) : Nat :=
  by classical exact if h : ∃ m, AbelianPeriod w m then Nat.find h else 0
def abelianPeriodSet (alpha rho : Real) : Set Nat :=
  {m | ∃ n i : Nat, 0 < n ∧ minAbelianPeriod (lowerMechanicalFactor alpha rho n i) = m}
def silverAbelianPeriodSet : Set Nat :=
  abelianPeriodSet silverSlope 0
def silverCandidateSet : Set Nat :=
  {m | (∃ k, m = P (k + 1)) ∨
    (∃ k, m = 2 * P (k + 1)) ∨
    (∃ k, 1 ≤ k ∧ m = P (k + 1) + P k)}
end D5.S1.Words.Mechanical
