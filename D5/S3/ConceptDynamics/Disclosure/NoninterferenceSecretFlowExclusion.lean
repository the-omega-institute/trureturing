/- GID: D5/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Noninterference excludes secret-dependent changes in the public program output. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-25):
   * Exact D5 hit `ConceptJoinUniversal.Refines` is the source's factorization
     order and expresses its primary boxed definition of noninterference.
   * Searches for low-input equality, secret inequality, public output, and
     deterministic noninterference found no theorem on these source maps.
   * `ExecutionPrivacyObstruction` is an adjacent disclosure theorem on concept
     meets and structural leakage, not this explicit program-flow carrier.
   * Pinned Mathlib contains the underlying equality logic but no packaged
     noninterference theorem. `loogle` and `leansearch` are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.NoninterferenceSecretFlowExclusion

open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u v w x y

/-- Deterministic noninterference rules out two states with equal public inputs,
different secrets, and different public outputs after the same program flow. -/
theorem noninterference_secret_flow_exclusion
    {State : Type u} {Low : Type v} {High : Type w}
    {ProgramState : Type x} {PublicOutput : Type y}
    (low : State -> Low) (high : State -> High)
    (flow : State -> ProgramState) (output : ProgramState -> PublicOutput)
    (noninterference : Refines (output ∘ flow) low) :
    ¬∃ left right,
      low left = low right ∧
      high left ≠ high right ∧
      output (flow left) ≠ output (flow right) := by
  rcases noninterference with ⟨factor, factorization⟩
  rintro ⟨left, right, sameLow, differentSecret, differentOutput⟩
  by_cases sameSecret : high left = high right
  · exact differentSecret sameSecret
  · apply differentOutput
    calc
      output (flow left) = factor (low left) := congrFun factorization left
      _ = factor (low right) := congrArg factor sameLow
      _ = output (flow right) := (congrFun factorization right).symm

#print axioms noninterference_secret_flow_exclusion

end D5.S3.ConceptDynamics.Disclosure.NoninterferenceSecretFlowExclusion
