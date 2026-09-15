/- GID: D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/StephanSlopingBinaryPeriodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.Data.Nat.Nth, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.claim; result=D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.result; claim=D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.claim
   digest: The values at indices 129 and 172 refute the proposed period 43 of OEIS A103585. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

noncomputable section

namespace D5.S0.Certificates.StephanSlopingBinaryPeriodRefutation

/-- The sloping-binary sequence A102370, in the finite form of its OEIS formula. -/
def s (k : ℕ) : ℕ :=
  k + ∑ m ∈ Finset.Icc 1 (k + 1), if (k + m) % 2 ^ m = 0 then 2 ^ m else 0

/-- The predicate selecting the integers used to form A103585. -/
def P (k : ℕ) : Prop :=
  s k = k + 2

/-- OEIS A103585 with zero-based indexing. -/
def A (i : ℕ) : ℕ :=
  Nat.nth P i % 4

/-- Ralf Stephan's proposed period-43 property for A103585. -/
def claim : Prop :=
  ∀ i : ℕ, A (i + 43) = A i

/-- The 129th and 172nd OEIS entries differ, so period 43 fails. -/
theorem result : ¬ claim := by
  letI : DecidablePred P := fun k => by
    unfold P
    infer_instance
  intro hclaim
  have hp383 : P 383 := by decide
  have hcount383 : Nat.count P 383 = 128 := by decide
  have hnth128 : Nat.nth P 128 = 383 := by
    rw [← hcount383]
    exact Nat.nth_count hp383
  have hp513 : P 513 := by decide
  have hcount513 : Nat.count P 513 = 171 := by decide
  have hnth171 : Nat.nth P 171 = 513 := by
    rw [← hcount513]
    exact Nat.nth_count hp513
  have hperiod := hclaim 128
  norm_num [A, hnth128, hnth171] at hperiod

#print axioms s
#print axioms P
#print axioms A
#print axioms claim
#print axioms result

end D5.S0.Certificates.StephanSlopingBinaryPeriodRefutation
