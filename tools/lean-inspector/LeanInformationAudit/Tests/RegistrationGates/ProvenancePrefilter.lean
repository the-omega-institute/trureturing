import LeanInformationAudit.Tests.RegistrationGates.ProvenanceTypes

open Lean LeanInformationAudit
namespace RegistrationProvenance

-- Eq/Nat occur on both sides; the filter must preserve the final comparison.
noncomputable def sharedConstantDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide decisionProposition (Classical.propDecidable _) then x else false
check_provenance "SharedConstantDecision" using sharedConstantDecision expects "unclassified_form" for specificTruth

-- Bool/Unit have no dependency in common with True. Observe the production
-- skip branch as well as its clean verdict; a disabled filter must fail here.
run_cmd Elab.Command.liftCoreM do
  let saved ← getTraceState
  let actual ← withOptions (·.set `trace.InformationProvenance.filter true) <|
    RegistrationGates.readoutClosure (← getEnv) ``truth (mkConst ``clean)
  let traces ← getTraces
  setTraceState saved
  let mut skipped := false
  for trace in traces do
    if (← trace.msg.toString).contains "disjoint" then skipped := true
  unless actual.1 == false && actual.2.isSome && skipped do
    throwError "[FAIL] DisjointConstantType: clean={actual.1 == false}, skipped={skipped}"
  logInfo "[PASS] DisjointConstantType"

-- This normal form contains only binders, locals and sorts, so use isDefEq.
def binderStatement : Prop := ∀ p : Prop, p → p
theorem binderTruth : binderStatement := fun _ h => h
def binderProofRead (_ : Unit) (x : Bool) : Bool := let _ : binderStatement := fun _ h => h; x
check_provenance "PureBinderFallback" using binderProofRead expects "forbidden_dependency" for binderTruth

end RegistrationProvenance
