/- GID: D5/S1/Digit/Infinite/NoContinuousAdditionExtension
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/NoContinuousAdditionExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No separately continuous binary operation on legal infinite digit streams extends natural number addition. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import D5.S1.Digit.Infinite.MultiplierObstruction

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.NoContinuousAdditionExtension

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.MultiplierObstruction
open scoped Topology
open Filter

/-- A binary operation agrees with addition on every pair of natural number digit rows. -/
def ExtendsFiniteAddition (A : LegalDigits → LegalDigits → LegalDigits) : Prop :=
  ∀ n m : ℕ, A (zRow n) (zRow m) = zRow (n + m)

/-- No separately continuous binary operation on legal digit streams extends finite addition. -/
theorem result :
    ¬ ∃ A : LegalDigits → LegalDigits → LegalDigits,
      (∀ x, Continuous (A x)) ∧
      (∀ y, Continuous (fun x => A x y)) ∧ ExtendsFiniteAddition A := by
  sorry

end D5.S1.Digit.Infinite.NoContinuousAdditionExtension
