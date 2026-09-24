/- GID: D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.claim; result=D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.result; claim=D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.claim
   digest: The partitions (1,1) and (2) refute printed Question 9 on derivative separation. -/

/- Formalization classification:
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9046)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.DawseyPartitionPolynomialDerivativeQuestionRefutation

open Polynomial

/-- The partition polynomial `f_λ(x) = Σ_i m_i x^i` of Definition (1): one summand
`X^i` per part `i` of the multiset of parts, so a part of multiplicity `m_i`
contributes `m_i · X^i`. -/
noncomputable def partitionPolynomial {n : ℕ} (l : Nat.Partition n) : Polynomial ℤ :=
  (l.parts.map fun i => Polynomial.X ^ i).sum

/-- `lg(λ)`, the largest part (`0` for the empty partition of `0`). -/
def largestPart {n : ℕ} (l : Nat.Partition n) : ℕ := l.parts.sup

/-- Question 9 as printed: any two unequal partitions are distinguished by some
positive `d ≤ min{lg λ, lg λ′}`. -/
def claim : Prop :=
  ∀ (n m : ℕ) (l : Nat.Partition n) (l' : Nat.Partition m), l.parts ≠ l'.parts →
    ∃ d : ℕ, 0 < d ∧ d ≤ min (largestPart l) (largestPart l') ∧
      (Polynomial.derivative^[d] (partitionPolynomial l)).eval 1 ≠
        (Polynomial.derivative^[d] (partitionPolynomial l')).eval 1

private def leftPartition : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by norm_num

private def rightPartition : Nat.Partition 2 where
  parts := {2}
  parts_pos := by simp
  parts_sum := by norm_num

example : leftPartition.parts ≠ rightPartition.parts := by
  change ({1, 1} : Multiset ℕ) ≠ {2}
  decide

example : largestPart leftPartition = 1 := by
  simp [largestPart, leftPartition]

example : largestPart rightPartition = 2 := by
  simp [largestPart, rightPartition]

example (l : Nat.Partition 0) : largestPart l = 0 := by
  simp [largestPart]

example : partitionPolynomial leftPartition = X + X := by
  simp [partitionPolynomial, leftPartition]

example : partitionPolynomial rightPartition = X ^ 2 := by
  simp [partitionPolynomial, rightPartition]

example : (Polynomial.derivative^[1] (partitionPolynomial leftPartition)).eval 1 = 2 := by
  simp [partitionPolynomial, leftPartition]

example : (Polynomial.derivative^[1] (partitionPolynomial rightPartition)).eval 1 = 2 := by
  simp [partitionPolynomial, rightPartition]

/-- The pair `(1,1)`, `(2)` answers the printed Question 9 in the negative. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨d, hd0, hdle, hne⟩ := h 2 2 leftPartition rightPartition (by
    change ({1, 1} : Multiset ℕ) ≠ {2}
    decide)
  have hd : d = 1 := by
    simp [largestPart, leftPartition, rightPartition] at hdle
    omega
  subst d
  apply hne
  simp [partitionPolynomial, leftPartition, rightPartition]

#print axioms result

end D5.S0.Certificates.DawseyPartitionPolynomialDerivativeQuestionRefutation
