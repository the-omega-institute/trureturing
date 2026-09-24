import LeanInformationAudit.Tests.RegistrationGates.ProvenanceTypes

open Lean LeanInformationAudit
namespace RegistrationProvenance

-- The proposition is definitionally equal to the registered statement.
noncomputable def sharedConstantDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide decisionProposition (Classical.propDecidable _) then x else false
check_provenance "SharedConstantDecision" using sharedConstantDecision expects "unclassified_form" for specificTruth

-- External constants are leaves; unfolding Unit would add PUnit here.
run_cmd Elab.Command.liftCoreM do
  let actual ← RegistrationGates.readoutClosure (← getEnv) ``truth (mkConst ``clean)
  unless actual == (false, some #["Bool", "RegistrationProvenance.clean", "Unit"]) do
    throwError "[FAIL] ExternalLeafNotTraversed: {repr actual}"
  logInfo "[PASS] ExternalLeafNotTraversed"

-- The binder type is syntactically the registered statement.
def binderStatement : Prop := ∀ p : Prop, p → p
theorem binderTruth : binderStatement := fun _ h => h
def binderProofRead (_ : Unit) (x : Bool) : Bool := let _ : binderStatement := fun _ h => h; x
check_provenance "PureBinderFallback" using binderProofRead expects "unclassified_form" for binderTruth

end RegistrationProvenance
