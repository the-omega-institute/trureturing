import LeanInformationAudit.ReadoutProvenance
import LeanInformationAuditAnalysis.Tests.AliasSortCarriers

open Lean LeanInformationAudit.RegistrationGates
namespace AliasSortCarrierBoundaries

theorem target : (137 : Nat) = 137 := rfl

run_cmd Elab.Command.liftTermElabM do
  for (constructor, aliasKind) in [( ``AliasSortCarriers.TypePacket.mk, ``AliasSortCarriers.CarrierKind),
      (``AliasSortCarriers.PropPacket.mk, ``AliasSortCarriers.PropositionKind),
      (``AliasSortCarriers.FamilyPacket.mk, ``AliasSortCarriers.FamilyKind)] do
    let info ← getConstInfo constructor
    Meta.forallTelescope info.type fun fields _ => do
      unless (← Meta.inferType fields[0]!).isConstOf aliasKind do
        throwError "[INVALID] AliasCarrierShape: {constructor} field lost its alias"
  logInfo "[PASS] AliasCarrierShape"

run_cmd Elab.Command.liftCoreM do
  for (label, readout) in [
      ("AliasTypeHidden", ``AliasSortCarriers.typeHidden),
      ("AliasTypeClean", ``AliasSortCarriers.typeClean),
      ("AliasPropHidden", ``AliasSortCarriers.propHidden),
      ("AliasPropClean", ``AliasSortCarriers.propClean),
      ("AliasFamilyHidden", ``AliasSortCarriers.familyHidden),
      ("AliasFamilyClean", ``AliasSortCarriers.familyClean)] do
    let actual ← readoutClosure (← getEnv) ``target (mkConst readout)
    if actual.1 && actual.2.isSome then logInfo m!"[PASS] {label}: {actual}"
    else logError m!"[FAIL] {label}: expected completed unaudited carrier rejection; actual={actual}"
  for (label, readout) in [("OrdinaryAliasControl", ``AliasSortCarriers.ordinary),
      ("IndependentProofAliasControl", ``AliasSortCarriers.independentProof)] do
    let actual ← readoutClosure (← getEnv) ``target (mkConst readout)
    if !actual.1 && actual.2.isSome then logInfo m!"[PASS] {label}: {actual}"
    else logError m!"[FAIL] {label}: {actual}"
  let actual ← readoutClosure (← getEnv) ``target (mkConst ``AliasSortCarriers.plain)
  if !actual.1 && actual.2.isSome then logInfo m!"[PASS] AliasExternalBoolControl: {actual}"
  else logError m!"[FAIL] AliasExternalBoolControl: {actual}"
end AliasSortCarrierBoundaries
