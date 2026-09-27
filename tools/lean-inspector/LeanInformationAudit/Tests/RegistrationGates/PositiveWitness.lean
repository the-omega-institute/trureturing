import LeanInformationAuditAnalysis.Tests.WitnessCarriers
import LeanInformationAudit.Tests.RegistrationGates.Round7PackedConsumer

open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
namespace PositiveWitness

def protectedProduct (_ : Unit) (state : Bool) : PProd Type Bool := ⟨Nat, state⟩
def keepProduct (_ other : PProd Type Bool) : PProd Type Bool := other
def warmedHidden (i : Unit) (state : Bool) : PProd Type Bool :=
  keepProduct (protectedProduct i state) (WitnessCarriers.hiddenProduct i state)
def warmedClean (i : Unit) (state : Bool) : PProd Type Bool :=
  keepProduct (protectedProduct i state) (WitnessCarriers.cleanProduct i state)

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  for (label, readout) in [
      ("ExternalHiddenProduct", ``WitnessCarriers.hiddenProduct),
      ("ExternalCleanProduct", ``WitnessCarriers.cleanProduct),
      ("ProducerMemoHidden", ``warmedHidden),
      ("ProducerMemoClean", ``warmedClean),
      ("AbstractPredicatePacket", ``WitnessCarriers.hiddenPredicate),
      ("AbstractFamilyPacket", ``WitnessCarriers.hiddenFamily),
      ("ExternalHiddenStatements", ``WitnessCarriers.hiddenStatements),
      ("ExternalCleanStatements", ``WitnessCarriers.cleanStatements)] do
    let actual ← readoutClosure env ``AllowlistBoundaries.target (mkConst readout)
    if actual.1 && actual.2.isSome then logInfo m!"[PASS] {label}: {actual}"
    else logError m!"[FAIL] {label}: expected completed rejection; actual={actual}"
  let actual ← readoutClosure env ``AllowlistBoundaries.target (mkConst ``protectedProduct)
  if !actual.1 && actual.2.isSome then logInfo m!"[PASS] ProtectedConcreteProduct: {actual}"
  else logError m!"[FAIL] ProtectedConcreteProduct: {actual}"

-- Kernel types require evidence on both success constructors. No empty/default
-- success value or optional rule identifier satisfies this API.
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let some info := env.find? ``ProvenanceAdmissionWitness.mk
    | throwError "[FAIL] WitnessRequiresRule: constructor missing"
  Meta.forallTelescope info.type fun fields _ => do
    unless fields.size == 4 do throwError "[FAIL] WitnessRequiresRule: unexpected fields"
    unless (← Meta.inferType fields[0]!) == mkConst ``ProvenanceAllowRule do
      throwError "[FAIL] WitnessRequiresRule: rule is optional or absent"
    for index in [1, 2] do
      unless (← Meta.inferType fields[index]!) == mkConst ``Expr do
        throwError "[FAIL] WitnessRequiresRule: missing recognized head/type"
  logInfo "[PASS] WitnessRequiresRule"
  for userName in [
      `LeanInformationAudit.RegistrationGates.TypeClassification.allowlisted,
      `LeanInformationAudit.RegistrationGates.StatementStep.recognized] do
    let some (_, info) := env.constants.toList.find? (fun (name, _) =>
      (privateToUserName? name).getD name == userName)
      | throwError "[FAIL] SuccessRequiresWitness: missing {userName}"
    Meta.forallTelescope info.type fun fields _ => do
      unless fields.size == 1 && (← Meta.inferType fields[0]!) ==
          mkConst ``ProvenanceAdmissionWitness do
        throwError "[FAIL] SuccessRequiresWitness: {userName} allows unwitnessed success"
  logInfo "[PASS] SuccessRequiresWitness"
end PositiveWitness
