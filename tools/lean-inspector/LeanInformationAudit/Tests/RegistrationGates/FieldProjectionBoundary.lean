import LeanInformationAudit.ReadoutProvenance
import LeanInformationAudit.StructuralRealization

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape
namespace FieldProjectionBoundary

def signature : PrimitiveSignature.{0, 0, 0} Bool where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by intro; decide
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def project (realization : PrimitiveRealization signature) (i : Unit) (state : Bool) : Bool :=
  realization.readout i state

theorem target : (137 : Nat) = 137 := rfl

run_cmd Elab.Command.liftCoreM do
  let actual ← readoutClosure (← getEnv) ``target (mkConst ``project)
  if !actual.1 && actual.2.isSome then
    logInfo m!"[PASS] AuditedDependentOutput: {actual}"
  else logError m!"[FAIL] AuditedDependentOutput: {actual}"
end FieldProjectionBoundary
