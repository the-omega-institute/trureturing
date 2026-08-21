/- GID: D5/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorized targets and image-correct decoding exclude misleading reception. -/

/- Library-search audit trail (2026-08-21):
   * Repository searches for misleading-message exclusion, decoder agreement on
     a message image, and target factorization found no exact theorem.
   * The directly applicable pinned-library primitives are Function.comp_apply
     and Set.mem_range_self; the pointwise proof below applies both explicitly.
-/

import Mathlib.Data.Set.Function

noncomputable section

namespace D5.S3.ConceptDynamics.Transport.MisleadingReceiverExclusion

def Misleading {State Message Target : Type*}
    (messageOf : State -> Message) (targetOf : State -> Target)
    (decode : Message -> Target) (state : State) : Prop :=
  decode (messageOf state) ≠ targetOf state

theorem misleading_impossible {State Message Target : Type*}
    (messageOf : State -> Message) (targetOf : State -> Target)
    (decode : Message -> Target) (correctDecode : Message -> Target)
    (factorization : targetOf = correctDecode ∘ messageOf)
    (agreement : forall message, message ∈ Set.range messageOf ->
      decode message = correctDecode message) :
    forall state, ¬ Misleading messageOf targetOf decode state := by
  intro state hmisleading
  apply hmisleading
  rw [factorization, Function.comp_apply]
  exact agreement (messageOf state) (Set.mem_range_self state)

#print axioms misleading_impossible

end D5.S3.ConceptDynamics.Transport.MisleadingReceiverExclusion
