import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

/-! Shared mathematics of the report-cohort fixtures. It records nothing. -/

namespace LeanInformationAudit.Tests.CohortArena
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Unit, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law r := r.readout () false = false

def good : PrimitiveRealization arena.signature := ⟨fun _ x => x, Fin.elim0⟩
def bad : PrimitiveRealization arena.signature := ⟨fun _ _ => true, Fin.elim0⟩
theorem lawVariation : arena.Law good ∧ ¬arena.Law bad := ⟨rfl, Bool.noConfusion⟩
theorem slotSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    refine ⟨good, bad, ?_, ?_, ?_⟩
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · intro j; exact Fin.elim0 j
    · exact ⟨fun _ => lawVariation.2, fun _ => lawVariation.1⟩
  · intro i; exact Fin.elim0 i

def reads : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => x)

end LeanInformationAudit.Tests.CohortArena
