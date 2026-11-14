/- GID: D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's A157675 self-substitution series has integer coefficients. -/

/-
admission_basis: open-problem-resolution (#18710; Proved)
escape_witness: none.
claim: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675.result.
result: proof_shape: bind-only; escape_witness: none; consumers: none; external assertion settled under #18710.
The public result is a bind-only application of the main result and geometric_input.
Its admission is the independent external tier-1 assertion preregistered in
#18710 before probes, not an inherited escape witness.
Literature completeness remains ASSUMED-UNVERIFIED.
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
