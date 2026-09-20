import LeanInformationAudit.Tests.Occurrence.ImportedArenaSource
import LeanInformationAudit.Syntax

open Lean Lean.Elab.Command LeanInformationAudit

private partial def withoutMetadata (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ body => some (withoutMetadata body)
    | _ => none

-- These expectations specify the original hook's live-head semantics. In particular,
-- the field copy must keep its own name even when Lean stores exactly the alias Expr.
run_cmd do
  let env ← getEnv
  let aliasInfo ← getConstInfo `ProvenanceProbe.aliasArena
  let copyInfo ← getConstInfo `ProvenanceProbe.copyArena
  unless aliasInfo.value! == copyInfo.value! do
    throwError "the eta counterexample must have identical imported Expr values"
  let localAliasInfo ← getConstInfo `ProvenanceProbe.localFunctionAlias
  let localCopyInfo ← getConstInfo `ProvenanceProbe.localFunctionCopy
  unless localAliasInfo.value! == localCopyInfo.value! do
    throwError "the local-function eta counterexample must have identical imported Expr values"
  for name in #[`ProvenanceProbe.localFunctionAlias, `ProvenanceProbe.localFunctionCopy,
      `ProvenanceProbe.localImplicitAlias] do
    let actual ← liftTermElabM <| resolveCanonicalArenaName name
    logInfo m!"local-function provenance: {name}: {actual}"
  for name in #[`ProvenanceProbe.aliasArena, `ProvenanceProbe.copyArena] do
    let some idx := env.getModuleIdxFor? name | throwError "missing compiler owner"
    unless env.header.moduleNames[idx]! ==
        `LeanInformationAudit.Tests.Occurrence.ImportedArenaSource do
      throwError "wrong compiler owner"
    unless (← findDeclarationRanges? name).isSome do
      throwError "missing imported compiler range"
  for (name, expected) in #[
      (`ProvenanceProbe.arena, `ProvenanceProbe.arena),
      (`ProvenanceProbe.aliasArena, `ProvenanceProbe.arena),
      (`ProvenanceProbe.abbreviated, `ProvenanceProbe.arena),
      (`ProvenanceProbe.reducibleAlias, `ProvenanceProbe.arena),
      (`ProvenanceProbe.opaqueHint, `ProvenanceProbe.arena),
      (`ProvenanceProbe.hintedForward, `ProvenanceProbe.arena),
      (`ProvenanceProbe.application, `ProvenanceProbe.arena),
      (`ProvenanceProbe.explicitMk, `ProvenanceProbe.explicitMk),
      (`ProvenanceProbe.copyArena, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.literalCopy, `ProvenanceProbe.literalCopy),
      (`ProvenanceProbe.live, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.dead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.inlineLive, `ProvenanceProbe.inlineLive),
      (`ProvenanceProbe.inlineDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localCopy, `ProvenanceProbe.localCopy),
      (`ProvenanceProbe.localFunctionAlias, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localFunctionCopy, `ProvenanceProbe.localFunctionCopy),
      (`ProvenanceProbe.localFunctionUnused, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localFunctionDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localFunctionBinders, `ProvenanceProbe.localFunctionBinders),
      (`ProvenanceProbe.localFunctionLambda, `ProvenanceProbe.localFunctionLambda),
      (`ProvenanceProbe.localFunctionNested, `ProvenanceProbe.localFunctionNested),
      (`ProvenanceProbe.localFunctionUnsupportedDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localFunctionUnsupportedUnused, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localImplicitAlias, `ProvenanceProbe.arena),
      (`ProvenanceProbe.localImplicitDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.throughParameter, `ProvenanceProbe.throughParameter),
      (`ProvenanceProbe.reservedForward, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.explicit, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.named, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.liveImplicit, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.inlineImplicit, `ProvenanceProbe.inlineImplicit),
      (`ProvenanceProbe.groupedNamed, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.unusedLet, `ProvenanceProbe.arena),
      (`ProvenanceProbe.nested, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.groupedLive, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.groupedDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.groupedInline, `ProvenanceProbe.groupedInline),
      (`ProvenanceProbe.typedLambda, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.tacticAlias, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.tacticFactory, `ProvenanceProbe.tacticFactory),
      (`ProvenanceProbe.unsupportedDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.selected, `ProvenanceProbe.selected),
      (`ProvenanceProbe.higherOrderLive, `ProvenanceProbe.higherOrderLive),
      (`ProvenanceProbe.higherOrderDead, `ProvenanceProbe.arena),
      (`ProvenanceProbe.projected, `ProvenanceProbe.projected)] do
    let actual ← liftTermElabM <| resolveCanonicalArenaName name
    unless actual == expected do
      throwError "imported provenance: {name}: expected {expected}, actual {actual}"
    let .defnInfo info ← getConstInfo name | throwError "expected a definition"
    let recovered ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless withoutMetadata recovered == withoutMetadata info.value do
      throwError "provenance must preserve the compiled Expr: {name}"
    let compiled ← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name
    unless compiled == expected do
      throwError "compiled provenance: {name}: expected {expected}, actual {compiled}"

-- Publish unsupported evidence too: erasure still preserves the original value,
-- and the next importing module must reject the same live paths without IO.
run_cmd do
  for name in #[`ProvenanceProbe.localFunctionUnsupported, `ProvenanceProbe.localImplicitCopy] do
    let .defnInfo info ← getConstInfo name | throwError "expected a definition"
    let recovered ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless withoutMetadata recovered == withoutMetadata info.value do
      throwError "unsupported provenance must preserve the compiled Expr: {name}"

/-- error: IE-C003 ArenaSourceUnsupported arena=ProvenanceProbe.unsupportedLive owner=ProvenanceProbe.unsupportedLive -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.unsupportedLive

/-- error: IE-C003 ArenaSourceUnsupported arena=ProvenanceProbe.localFunctionUnsupported owner=ProvenanceProbe.localFunctionUnsupported -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.localFunctionUnsupported

/-- error: IE-C003 ArenaSourceUnsupported arena=ProvenanceProbe.localImplicitCopy owner=ProvenanceProbe.localImplicitCopy -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.localImplicitCopy

-- A repeated binder name across partial applications is not a globally named
-- argument. Recovery must reject that ambiguity instead of marking the dead input.
/-- error: IE-C003 ArenaSourceUnsupported arena=ProvenanceProbe.ambiguousNamed owner=ProvenanceProbe.ambiguousNamed -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.ambiguousNamed

/-- error: IE-C003 ArenaSourceUnavailable declaration=ProvenanceProbe.rangeMissing reason=range -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.rangeMissing

/-- error: IE-C003 ArenaResolutionBudgetExceeded arena=ProvenanceProbe.expensive limit=4096 -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.expensive

run_cmd do
  let owner ← liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.privateLive
  unless privateToUserName owner == `ProvenanceProbe.privateCopy do
    throwError "private constructor must use its compiler owner and range"
  let root ← Repository.root
  unless (← Repository.rootFrom (root / "Reg")) == root do
    throwError "nested package must resolve the same repository source root"
