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
    | .mdata data body =>
      if data.contains ArenaProvenance.construction || data.contains ArenaProvenance.unsupported then
        some (withoutMetadata body)
      else none
    | _ => none

-- Acquire unsupported Expr evidence explicitly as well: its deferred error must
-- survive the next import, without storing an accepted registration.
run_cmd do
  for name in #[`QualityPure.defaultUse, `QualityPure.defaultTailUse,
      `QualityPure.inferredUse, `QualityPure.localImplicitDefaultUse,
      `QualityContext.unresolved] do
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
      (`QualityPure.localImplicitDeadDefaultUse, `ProvenanceProbe.arena),
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


namespace QualityGroupedHook

def hold (_u : Unit) (a : Arena.{0} := ProvenanceProbe.arena)
    (_ignored : Arena.{0}) : Arena.{0} := a
def shifted : Arena.{0} :=
  (hold ()) {
    State := ProvenanceProbe.arena.State
    stateFintype := ProvenanceProbe.arena.stateFintype
    stateDecidableEq := ProvenanceProbe.arena.stateDecidableEq }

def holdCopy (_u : Unit) (a : Arena.{0} := {
    State := ProvenanceProbe.arena.State
    stateFintype := ProvenanceProbe.arena.stateFintype
    stateDecidableEq := ProvenanceProbe.arena.stateDecidableEq })
    (_ignored : Arena.{0}) : Arena.{0} := a
def shiftedCopy : Arena.{0} := (holdCopy ()) ProvenanceProbe.arena

end QualityGroupedHook

namespace QualityGroupedRegistration
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

theorem aliasFact : True := trivial
theorem copyFact : True := trivial
theorem bridge : LegacyPrimitiveRealization lawArena True fixtureRealization := ⟨Iff.rfl⟩
/-- error: IE-C003 ArenaSourceUnsupported arena=QualityGrouped.shifted owner=QualityGrouped.shifted -/
#guard_msgs (error) in
register_information_theorem aliasFact
  in lawArena object_arena QualityGrouped.shifted catalog groupedAlias
  primitives fixtureRealization.toPrimitiveBundle realization bridge
/-- error: IE-C003 ArenaSourceUnsupported arena=QualityGrouped.shiftedCopy owner=QualityGrouped.shiftedCopy -/
#guard_msgs (error) in
register_information_theorem copyFact
  in lawArena object_arena QualityGrouped.shiftedCopy catalog groupedCopy
  primitives fixtureRealization.toPrimitiveBundle realization bridge
end QualityGroupedRegistration

run_cmd do
  for (name, expected) in #[
      (`QualityGroupedHook.shifted, `ProvenanceProbe.arena),
      (`QualityGroupedHook.shiftedCopy, `QualityGroupedHook.shiftedCopy),
      (`QualityGrouped.deadInserted, `ProvenanceProbe.arena),
      (`QualityGrouped.liveOuter, `QualityGrouped.liveOuter),
      (`QualityGrouped.explicitInner, `ProvenanceProbe.arena),
      (`QualityGrouped.namedInner, `ProvenanceProbe.arena),
      (`QualityGrouped.groupedExplicit, `ProvenanceProbe.arena)] do
    let actual ← liftTermElabM <| resolveCanonicalArenaName name
    unless actual == expected do
      throwError "[FAIL] grouped alignment {name}: expected={expected} actual={actual}"
  for name in #[`QualityGrouped.shifted, `QualityGrouped.shiftedCopy] do
    let .defnInfo info ← getConstInfo name | throwError "expected definition"
    -- Acquire the deferred rejection independently of the failed command's rollback.
    let recovered ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless QualityRegistration.withoutMetadata recovered ==
        QualityRegistration.withoutMetadata info.value do
      throwError "[FAIL] grouped Expr erasure {name}"
    let args := recovered.getAppArgs
    unless args.size == 3 do throwError "[FAIL] unexpected grouped compiled arity {name}"
    let .mdata data _ := args[1]!
      | throwError "[FAIL] missing evidence on actual inner default {name}"
    unless data.contains ArenaProvenance.unsupported do
      throwError "[FAIL] missing unsupported evidence on actual inner default {name}"
    let diagnostic ← liftTermElabM do
      try return s!"accepted owner={← resolveCanonicalArenaName name}"
      catch ex => ex.toMessageData.toString
    unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
      throwError "[FAIL] grouped live inserted default: {diagnostic}"
  for name in #[`QualityGroupedRegistration.aliasFact, `QualityGroupedRegistration.copyFact] do
    unless (InformationRegistry.find? (← getEnv) name).isNone do
      throwError "[FAIL] grouped unsupported registration inserted: {name}"
  logInfo "[PASS] Q3 dual grouped defaults reject IE-C003 before insertion; \
    hook owners and dead defaults preserved"
