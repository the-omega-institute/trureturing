import LeanInformationAudit.Tests.Occurrence.AliasConstruction

open Lean LeanInformationAudit D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer
namespace AliasBoundary
set_option linter.style.longLine false
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def direct := objectArena
abbrev abbreviated := direct
@[reducible] def reducibleAlias := abbreviated
@[irreducible] def opaqueHint := reducibleAlias
def identity := id opaqueHint
def beta := (fun x : Arena => x) identity
def zeta := let x := beta; x
def forwarding (_ : Unit) : Arena := objectArena
def application := forwarding ()
def constructed := id (Arena.mk objectArena.State
  objectArena.stateFintype objectArena.stateDecidableEq)
def projected := lawArena.toArena
def selected := if True then objectArena else objectArena

run_cmd do
  for name in #[`AliasBoundary.direct, `AliasBoundary.abbreviated,
      `AliasBoundary.reducibleAlias, `AliasBoundary.opaqueHint,
      `AliasBoundary.identity, `AliasBoundary.beta, `AliasBoundary.zeta,
      `AliasBoundary.application] do
    let owner ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName name
    unless owner == `LeanInformationAudit.Tests.ImportClosureProducer.objectArena do
      throwError "AliasBoundary: forwarding alias retains an intermediate name: {name}"
  let importedOwner ← Lean.Elab.Command.liftTermElabM <|
    resolveCanonicalArenaName `AliasConstruction.forwardingCopy
  unless importedOwner == `AliasConstruction.fieldCopy do
    throwError "AliasBoundary: imported construction loses its owner"
  for name in #[`AliasBoundary.constructed, `AliasBoundary.projected, `AliasBoundary.selected] do
    let owner ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName name
    unless owner == name do
      throwError "AliasBoundary: construction/projection/recursor crosses the reduction boundary: {name}"
-- An occupied generated address still reports the already resolved prospective owner.
run_cmd do
  let name := catalogQualifiedName (← getEnv).header.mainModule `AliasBoundary.zeta
    `collision `AliasBoundary.next theoremUnitSuffix
  let id := mkIdent (`_root_ ++ name)
  Lean.Elab.Command.elabCommand (← `(command| def $id : Nat := 0))

/-- error: IE-C025 QualifiedNameCollision root=LeanInformationAudit.Tests.Occurrence.AliasBoundary catalog=collision generated_name=AliasBoundary.next.«LeanInformationAudit.Tests.Occurrence.AliasBoundary/AliasBoundary.zeta/collision».__information_unit occurrences=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/AliasBoundary.next"] -/
#guard_msgs (error) in
information_theorem next
  in lawArena object_arena zeta catalog collision
  primitives fixtureRealization
  : lawArena.Law fixtureRealization := by trivial
end AliasBoundary
