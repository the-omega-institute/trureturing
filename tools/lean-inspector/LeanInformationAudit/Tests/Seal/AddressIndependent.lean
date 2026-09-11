import LeanInformationAudit.Tests.SealOvercomplete
open Lean Meta Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.SealOvercomplete
namespace LeanInformationAudit.Tests.Seal.AddressIndependent
local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
information_theorem peer in arena primitives fstRealization : arena.Law fstRealization := by trivial
run_cmd do
  let some prepared := (← prepareCatalogs)[0]? | throwError "missing catalog"
  let result ← prepareProofs #[prepared]
  let rows := result.records[0]!.theorems.mapIdx fun i row =>
    { row with primitiveKernelAddress := s!"diagnostic-{i}" }
  let (declarations, classes) ← liftTermElabM <| prepareCollisionClasses prepared.record prepared.value rows
  unless classes.size == 1 && classes[0]!.1.size == 2 &&
      classes[0]!.1.contains ``peer && classes[0]!.1.contains ``fstTheorem do
    throwError "AddressIndependent: equal kernels with distinct addresses split"
  for declaration in declarations do
    let .thmDecl info := declaration | throwError "AddressIndependent: non-proof class"
    liftTermElabM <| checkWithKernel info.value
end LeanInformationAudit.Tests.Seal.AddressIndependent
