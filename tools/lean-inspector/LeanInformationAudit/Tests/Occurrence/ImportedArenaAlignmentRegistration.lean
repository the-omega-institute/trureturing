import LeanInformationAudit.Tests.Occurrence.ImportedArenaAlignmentSource
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer

namespace QualityRegistration
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

theorem defaultFact : True := trivial
theorem contextFact : True := trivial
theorem bridge : LegacyPrimitiveRealization lawArena True fixtureRealization where
  equivalence := Iff.rfl

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityPure.defaultUse owner=QualityPure.defaultUse -/
#guard_msgs (error) in
register_information_theorem defaultFact
  in lawArena object_arena QualityPure.defaultUse catalog defaultCopy
  primitives fixtureRealization.toPrimitiveBundle realization bridge
register_information_theorem contextFact
  in lawArena object_arena QualityContext.drift catalog contextCopy
  primitives fixtureRealization.toPrimitiveBundle realization bridge

private partial def withoutMetadata (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ body => some (withoutMetadata body)
    | _ => none

-- Acquire unsupported Expr evidence explicitly as well: its deferred error must
-- survive the next import, without storing an accepted registration.
run_cmd do
  for name in #[`QualityPure.defaultUse, `QualityPure.defaultTailUse,
      `QualityPure.inferredUse, `QualityContext.unresolved] do
    let .defnInfo info ← getConstInfo name | throwError "expected definition"
    let recovered ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless withoutMetadata recovered == withoutMetadata info.value do
      throwError "[FAIL] inserted/unsupported Expr erasure: {name}"
    let diagnostic ← liftTermElabM do
      try
        return s!"accepted owner={← resolveCanonicalArenaName name}"
      catch ex => ex.toMessageData.toString
    unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
      throwError "[FAIL] expected live source rejection for {name}: {diagnostic}"

run_cmd do
  for (name, expected) in #[
      (`QualityPure.deadDefaultUse, `ProvenanceProbe.arena),
      (`QualityPure.deadDefaultTailUse, `ProvenanceProbe.arena),
      (`QualityPure.deadInferredUse, `ProvenanceProbe.arena),
      (`QualityPure.explicitDefaultUse, `QualityPure.explicitDefaultUse),
      (`QualityPure.namedDefaultUse, `QualityPure.namedDefaultUse),
      (`QualityContext.drift, `QualityContext.drift),
      (`QualityContext.qualified, `QualityContext.qualified),
      (`QualityContext.direct, `QualityContext.direct),
      (`QualityContext.termLet, `QualityContext.termLet),
      (`QualityContext.directAlias, `ProvenanceProbe.arena),
      (`QualityContext.classAlias, `ProvenanceProbe.arena),
      (`QualityContext.qualifiedClassAlias, `ProvenanceProbe.arena),
      (`QualityContext.localContextUse, `QualityContext.localContextUse),
      (`ProvenanceProbe.tacticFactory, `ProvenanceProbe.tacticFactory)] do
    let actual ← liftTermElabM <| resolveCanonicalArenaName name
    unless actual == expected do
      throwError "[FAIL] alignment {name}: expected={expected} actual={actual}"
    let .defnInfo info ← getConstInfo name | throwError "expected definition"
    let recovered ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless withoutMetadata recovered == withoutMetadata info.value do
      throwError "[FAIL] alignment Expr erasure: {name}"

run_cmd do
  unless (InformationRegistry.find? (← getEnv) `QualityRegistration.defaultFact).isNone do
    throwError "[FAIL] QUALITY-DEFAULT must reject before registration"
  let some entry := InformationRegistry.find? (← getEnv) `QualityRegistration.contextFact
    | throwError "missing context registration"
  unless entry.canonicalObjectArenaName == `QualityContext.drift do
    throwError "[FAIL] QUALITY-CONTEXT expected=QualityContext.drift \
      actual={entry.canonicalObjectArenaName}"
  logInfo "[PASS] QUALITY-DEFAULT rejected IE-C003; QUALITY-CONTEXT owner=QualityContext.drift"

end QualityRegistration

-- Compare with the existing elaboration hook, where the original construction
-- sites are still available, including the compiler-inserted default argument.
namespace QualityHook
open ProvenanceProbe

def defaultCopy (a : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }) : Arena := a
def defaultUse : Arena := defaultCopy

def direct : Arena := by
  letI localArena : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  exact localArena

run_cmd do
  for name in #[`QualityHook.defaultUse, `QualityHook.direct] do
    unless (← liftTermElabM <| resolveCanonicalArenaName name) == name do
      throwError "[FAIL] original elaboration-hook control: {name}"

end QualityHook
