import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean LeanInformationAudit D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer
namespace AliasConstruction
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def fieldCopy : Arena where
  State := objectArena.State
  stateFintype := objectArena.stateFintype
  stateDecidableEq := objectArena.stateDecidableEq

def explicitMk : Arena := Arena.mk objectArena.State
  objectArena.stateFintype objectArena.stateDecidableEq

def secondFactory : Arena := Arena.ofFintype Bool

def forwardingCopy := id fieldCopy
def unusedConstruction := (fun _ : Arena => objectArena) fieldCopy

run_cmd do
  let copyOwner ← Lean.Elab.Command.liftTermElabM <|
    resolveCanonicalArenaName `AliasConstruction.forwardingCopy
  let originalOwner ← Lean.Elab.Command.liftTermElabM <|
    resolveCanonicalArenaName `AliasConstruction.unusedConstruction
  unless copyOwner == `AliasConstruction.fieldCopy &&
      originalOwner == `LeanInformationAudit.Tests.ImportClosureProducer.objectArena do
    throwError "AliasConstruction: only a live construction determines ownership"

theorem legacy : LegacyPrimitiveRealization lawArena True fixtureRealization where
  equivalence := Iff.rfl

register_information_theorem importedTheorem
  in lawArena object_arena fieldCopy catalog copy
  primitives fixtureRealization.toPrimitiveBundle realization legacy
register_information_theorem importedTheorem
  in lawArena object_arena explicitMk catalog mk
  primitives fixtureRealization.toPrimitiveBundle realization legacy
register_information_theorem importedTheorem
  in lawArena object_arena secondFactory catalog factory
  primitives fixtureRealization.toPrimitiveBundle realization legacy

run_cmd do
  let owners := (InformationRegistry.entries (← getEnv)).map (·.canonicalObjectArenaName)
  unless owners == #[`LeanInformationAudit.Tests.ImportClosureProducer.objectArena,
      `AliasConstruction.fieldCopy, `AliasConstruction.explicitMk,
      `AliasConstruction.secondFactory] do
    throwError "AliasConstruction: independent constructions must all register as separate owners"
end AliasConstruction
