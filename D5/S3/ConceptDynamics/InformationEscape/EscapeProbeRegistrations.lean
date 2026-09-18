/- GID: D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trigger probe: one new public theorem with a complete four-slot escape registration. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.EscapeProbeRegistrations
open RegistrationTemplates EscapeRecord LeanInformationAudit
open D5.S3.ConceptDynamics.CIRPT

/-- The probe theorem: the identity readout over `Bool` never changes a bit. -/
theorem probe_four_slot_true : ∀ x : Bool, x = x := fun _ => rfl

/-- One CUT slot reading a Boolean state; the law fixes the readout at `false`. -/
def probeArena : PrimitiveLawArena.{0, 0, 0} where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := r.readout () false = false

local instance : DecidableEq probeArena.State := instDecidableEqBool

def probeRealization : PrimitiveRealization probeArena.signature :=
  cutRealization (fun x : Bool => x)

def probeBad : PrimitiveRealization probeArena.signature :=
  cutRealization (fun _ : Bool => true)

theorem probe_bridge : LegacyPrimitiveRealization probeArena (∀ x : Bool, x = x) probeRealization :=
  ⟨⟨fun _ => rfl, fun _ => probe_four_slot_true⟩⟩

theorem probe_lawVariation : probeArena.Law probeRealization ∧ ¬ probeArena.Law probeBad :=
  ⟨rfl, Bool.noConfusion⟩

theorem probe_slotSensitivity : FiniteSlotSensitivity probeArena := by
  constructor
  · intro i
    refine ⟨probeRealization, probeBad, ?_, ?_, ?_⟩
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · intro j; exact Fin.elim0 j
    · exact ⟨fun _ => probe_lawVariation.2, fun _ => probe_lawVariation.1⟩
  · intro i; exact Fin.elim0 i

/-- The identity kernel separates both Boolean states: the closure leaves no residual. -/
def probeChain : LayerChain probeArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun x : Bool => x)
  refines := fun r => Fin.elim0 r

theorem probe_emptyProof : EscapeResidualEmpty probeChain := by
  change probeChain.unresolvedCount = 0
  decide +kernel

register_information_template D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization

register_information_theorem probe_four_slot_true in probeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives probeRealization.toPrimitiveBundle realization probe_bridge
  variation probe_lawVariation sensitivity probe_slotSensitivity
  escape from (Bool) escape continues (probe_emptyProof)

example : probe_four_slot_true.__information_unit.Statement = (∀ x : Bool, x = x) := rfl
#print axioms probe_bridge
#print axioms probe_emptyProof

end D5.S3.ConceptDynamics.InformationEscape.EscapeProbeRegistrations
