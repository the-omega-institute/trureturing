/- GID: D5/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorized targets and image-correct decoding exclude misleading reception. -/

module
prelude
public import OmegaInit.Core

namespace D5.S3.ConceptDynamics.Transport.MisleadingReceiverExclusion

open Omega

/-- A decoded message is misleading when it disagrees with the target of its state. -/
public def Misleading {State : Type u} {Message : Type v} {Target : Type w}
    (messageOf : State → Message) (targetOf : State → Target)
    (decode : Message → Target) (state : State) : Prop :=
  Not (Eq (decode (messageOf state)) (targetOf state))

/-- Decoder agreement on all attainable messages excludes misleading reception. -/
public theorem misleading_impossible {State : Type u} {Message : Type v} {Target : Type w}
    (messageOf : State → Message) (targetOf : State → Target)
    (decode correctDecode : Message → Target)
    (factorization : ∀ state, Eq (targetOf state) (correctDecode (messageOf state)))
    (agreement : ∀ message, Exists (fun state => Eq (messageOf state) message) →
      Eq (decode message) (correctDecode message)) :
    ∀ state, Not (Misleading messageOf targetOf decode state) :=
  fun state misleading => misleading
    ((agreement (messageOf state) (Exists.intro state rfl)).trans (factorization state).symm)

end D5.S3.ConceptDynamics.Transport.MisleadingReceiverExclusion
