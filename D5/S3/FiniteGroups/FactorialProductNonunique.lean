/- GID: D5/S3/FiniteGroups/FactorialProductNonunique
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/FactorialProductNonunique
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/FactorialProductNonunique.claim; result=D5/S3/FiniteGroups/FactorialProductNonunique.result; claim=D5/S3/FiniteGroups/FactorialProductNonunique.claim
   digest: Distinct finite integer sets can have equal factorial-weight products. -/

/- admission_basis: open-problem-resolution (#27274; Refuted).
   result | proof_shape: bind-only | escape_witness: none | external Problem 5.6.
   leftParameters, rightParameters | proof_shape: bind-only | consumer: result.
   claim | proof_shape: bind-only | consumer: result.
   The designated refutation result is exempt from four-slot registration.
   The factor is reused from its original owner without a second definition. -/

import D5.S3.FiniteGroups.TransversalProbabilityMonotone
import Mathlib.Tactic.NormNum.NatFactorial

namespace D5.S3.FiniteGroups.FactorialProductNonunique

open TransversalProbabilityMonotone

private def leftParameters : Finset ℕ :=
  {10, 17, 21, 23, 24, 27, 38, 45, 46, 48, 56, 65, 68, 77, 80, 84, 95, 141}

private def rightParameters : Finset ℕ :=
  {11, 16, 20, 22, 25, 26, 39, 44, 47, 49, 57, 64, 69, 76, 81, 85, 94, 140}

/-- The set form of ALM Problem 5.6, with no bound on cardinalities or parameters. -/
def claim : Prop :=
  ∀ A B : Finset ℕ, (∀ m ∈ A, 1 < m) → (∀ m ∈ B, 1 < m) →
    (∏ m ∈ A, orbitWeight m) = (∏ m ∈ B, orbitWeight m) → A = B

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- A pair of disjoint eighteen-element sets refutes factorial-product uniqueness. -/
theorem result : ¬ claim := by
  intro h
  have hA : ∀ m ∈ leftParameters, 1 < m := by norm_num [leftParameters]
  have hB : ∀ m ∈ rightParameters, 1 < m := by norm_num [rightParameters]
  have he : (∏ m ∈ leftParameters, orbitWeight m) =
      (∏ m ∈ rightParameters, orbitWeight m) := by
    norm_num [leftParameters, rightParameters, orbitWeight]
  have hn : leftParameters ≠ rightParameters := by decide
  exact hn (h leftParameters rightParameters hA hB he)

end D5.S3.FiniteGroups.FactorialProductNonunique
