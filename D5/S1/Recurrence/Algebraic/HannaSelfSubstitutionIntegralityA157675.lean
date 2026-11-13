/- GID: D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's A157675 self-substitution series has integer coefficients. -/

/-
admission_basis: open-problem-resolution (#18710; Proved)
escape_witness: HannaSelfSubstitutionIntegrality.claim_of_preservation.
claim: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675.result.
result: proof_shape: content; escape_witness: HannaSelfSubstitutionIntegrality.claim_of_preservation; consumers: external settlement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24041.
-/
import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675

open D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality (SolvesHanna)
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

/-- OEIS A157675: "G.f.: A(x) = exp( Sum_{n>=1} A(2^n*x)^n * x^n/n )."
The comment is "Conjectured to consist entirely of integers." -/
def claim : Prop :=
  (∃ A, SolvesHanna (fun n => (2 : ℚ) ^ n) A) ∧
    ∀ A, SolvesHanna (fun n => (2 : ℚ) ^ n) A → IntegralSeries A

theorem result : claim := by
  exact HannaSelfSubstitutionIntegrality.result _
    (HannaSelfSubstitutionIntegrality.geometric_input 2)

end D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675
