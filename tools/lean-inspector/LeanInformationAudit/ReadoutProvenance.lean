import LeanInformationAudit.Sha256
import Lean

namespace LeanInformationAudit.RegistrationGates
open Lean Meta

/-- Correctness bounds, independent of machine speed: at most 4096 constants,
524288 expression nodes, and forwarding recursion with fuel 256.
Exhaustion always means incomplete, including on the clean path. -/
def provenanceConstantFuel : Nat := 4096
def provenanceExpressionFuel : Nat := 524288

/-- These judge APIs cannot supply independent object readouts. Membership is
by declaration identity, independent of the theorem key's representation. -/
def provenanceJudgeAPIs : Array Name := #[
  `LeanInformationAudit.InformationRegistry.entries,
  `LeanInformationAudit.InformationRegistry.find?,
  `LeanInformationAudit.InformationRegistry.hasTheorem,
  `LeanInformationAudit.InformationRegistry.hasOccurrence,
  `LeanInformationAudit.InformationRegistry.hasUnit,
  `LeanInformationAudit.InformationRegistryEntry.statementIdentity,
  `LeanInformationAudit.ExpectedOccurrence.statementIdentity,
  `LeanInformationAudit.theoremStatementIdentity,
  `LeanInformationAudit.Sha256.digest, `LeanInformationAudit.Sha256.hex,
  `LeanInformationAudit.StatementKey.mk, `LeanInformationAudit.StatementKey.statementId,
  `LeanInformationAudit.ClosedNumericalObligation.mk,
  `LeanInformationAudit.InfinitePrimitiveObligation.mk,
  `LeanInformationAudit.UnfaithfulPrimitiveObligation.mk,
  `LeanInformationAudit.FiniteOccurrenceDisposition.mk,
  `LeanInformationAudit.StructuralOccurrenceDisposition.mk,
  `LeanInformationAudit.BoundedFiniteTruncationDisposition.mk,
  `LeanInformationAudit.UnreachableDisposition.mk]

/-- A fresh, fixed budget per comparison; exceptions propagate to the query's
incomplete result. Only types and identity data are reduced, never proof values. -/
private def boundedDefEq (a b : Expr) : MetaM Bool :=
  withCurrHeartbeats <| withOptions
    (fun o => (o.set `maxHeartbeats (10000 : Nat)).set `maxRecDepth (1024 : Nat)) do
      isDefEq a b

/-- One memoized classification pass per readout. Open binder propositions stay
open: no metavariable synthesis may turn an unrelated decision into this one. -/
private def sameStatement (statement candidate : Expr) :
    StateRefT (Std.HashMap Expr Bool) MetaM Bool := do
  if candidate.hasLooseBVars || candidate.hasFVar then return false
  if candidate.hasMVar then throwError "unresolved provenance type"
  if let some answer := (← get)[candidate]? then return answer
  let answer ← boundedDefEq candidate statement
  modify (·.insert candidate answer)
  return answer

initialize registerTraceClass `InformationProvenance.check

/-- Only expose record construction; never reduce a readout or a proof. -/
private def recordHead (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn with
    | .mdata _ body => recordHead env fuel (mkAppN body args)
    | .letE _ _ value body _ => recordHead env fuel (mkAppN (body.instantiate1 value) args)
    | .lam _ _ _ _ =>
      if args.isEmpty then some e else recordHead env fuel (e.getAppFn.beta args)
    | .const name levels =>
      match env.find? name with
      | some (.defnInfo info) =>
        recordHead env fuel (mkAppN (info.value.instantiateLevelParams info.levelParams levels) args)
      | some _ => some e
      | none => none
    | .proj _ index value =>
      let value ← recordHead env fuel value
      let .const name _ := value.getAppFn | some e
      let some (.ctorInfo info) := env.find? name | some e
      let field ← value.getAppArgs[info.numParams + index]?
      recordHead env fuel (mkAppN field args)
    | _ => some e

/-- The realization supplies the family's carrier annotations. Project these
schema fields before scanning an inline family, just as readoutFamily projects
the readout field itself; the arena's Law/DecidableEq fields are not readouts.
Explicit user let/proof annotations and the body remain raw. -/
private def familyCarriers (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, .lam n type body bi => do
    let type ← if #[
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index,
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Output,
        `D5.S3.ConceptDynamics.InformationEscape.Arena.State,
        `LeanInformationAudit.StructuralPrimitiveSignature.Index,
        `LeanInformationAudit.StructuralPrimitiveSignature.Output,
        `LeanInformationAudit.StructuralArena.State].contains (type.getAppFn.constName?.getD .anonymous) then
      recordHead env 256 type else some type
    return .lam n type (← familyCarriers env fuel body) bi
  | _, e => some e

/-- Native and legacy paths share the same raw readout-family extraction. The
legacy bridge contributes its type's realization argument, never its proof. -/
private def readoutFamily (env : Environment) (realization : Name) : Option Expr := do
  let info ← env.find? realization
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env 256 info.type
      unless type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do none
      type.getAppArgs[2]?
    | .defnInfo _ => some (mkConst realization)
    | _ => none
  let value ← recordHead env 256 root
  let name ← value.getAppFn.constName?
  unless name == `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      name == `LeanInformationAudit.StructuralPrimitiveRealization.mk do none
  familyCarriers env 256 (← value.getAppArgs[2]?)

private def children (e : Expr) : List Expr :=
  match e with
  | .app f a => [f, a]
  | .lam _ t b _ | .forallE _ t b _ => [t, b]
  | .letE _ t v b _ => [t, v, b]
  | .mdata _ b => [b]
  | .proj name _ b => [mkConst name, b]
  | _ => []

/-- Substitute actual arguments into a constant's stored type, without inferType
or elaboration. The telescope and each forwarding reduction have fixed fuel. -/
private def appliedType (env : Environment) (e : Expr) : Option Expr := do
  let .const name levels := e.getAppFn | some e
  let info ← env.find? name
  -- Only instance-producing declarations need specialization. A dependent
  -- data projection with an unknown result type is not an instance declaration.
  let head ← recordHead env 256 info.type
  let result := head.getForallBody
  let .const _ _ := result.getAppFn | some e
  let result ← recordHead env 256 result
  unless result.isAppOfArity ``Decidable 1 do return e
  let args := e.getAppArgs
  if args.size > 256 then none else do
    let mut type := info.type.instantiateLevelParams info.levelParams levels
    for arg in args do
      let .forallE _ _ body _ ← recordHead env 256 type | none
      type := body.instantiate1 arg
    recordHead env 256 type

/-- Track the registered proof's raw dependencies transitively, once and only
when a reached theorem needs classification. Both worklists have fixed bounds;
shared unapplied proof combinators are not themselves forbidden proof terms. -/
private def proofExpressions (env : Environment) (value : Expr) :
    MetaM (Option (Std.HashSet Expr)) := do
  let mut todo := [value]
  let mut proofs : Std.HashSet Expr := {}
  let mut constants : NameHashSet := {}
  let mut visited : Std.HashSet Expr := {}
  let mut fuel := provenanceExpressionFuel
  while let e :: rest := todo do
    if fuel == 0 then return none
    fuel := fuel - 1
    todo := rest
    if visited.contains e then continue
    visited := visited.insert e
    if let .const name levels := e.getAppFn then
      let some info := env.find? name | return none
      if !e.hasLooseBVars && e.getAppNumArgs >= info.type.getNumHeadForalls &&
          (info.isTheorem || (← isProp info.type)) then
        proofs := proofs.insert e
        if !constants.contains name then
          if constants.size >= provenanceConstantFuel then return none
          constants := constants.insert name
        if let some value := info.value? (allowOpaque := true) then
          todo := (value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs :: todo
    todo := children e ++ todo
  return some proofs

/-- Complete raw ConstantInfo dependency query. Types and values are inspected
without elaboration, realization enumeration or unfolding proofs. A forbidden
node stops semantic analysis; only dependency collection continues so a partial
frontier is never presented as the complete provenance_closure. -/
private def collectReadout (env : Environment) (theoremName : Name) (readout : Expr) :
    StateRefT (Std.HashMap Expr Bool) MetaM (Bool × Option (Array String)) := do
  let some theoremInfo := env.find? theoremName | return (false, none)
  let identity := "sha256:" ++ Sha256.hex (toString theoremInfo.type).toUTF8
  let quotedName := toExpr theoremName
  let mut proofTerms : Option (Std.HashSet Expr) := none
  let mut todo := [readout]
  let mut constants : NameHashSet := {}
  let mut visited : Std.HashSet Expr := {}
  let mut applications : Array Expr := #[]
  let mut forbidden := false
  let mut fuel := provenanceExpressionFuel
  while let e :: rest := todo do
    Core.checkMaxHeartbeats "readout provenance"
    if fuel == 0 then return (forbidden, none)
    fuel := fuel - 1
    todo := rest
    if visited.contains e then continue
    visited := visited.insert e
    -- Name-indexed certificates and StatementKey/statement-id sources retain
    -- these literal identity inputs in their type or value, even in dead terms.
    if e == quotedName || e == mkStrLit identity then forbidden := true
    if e.hasMVar then return (forbidden, none)
    if (theoremInfo.value? (allowOpaque := true)) == some e then forbidden := true
    if !forbidden && !e.hasLooseBVars then
      if let some info := e.getAppFn.constName?.bind env.find? then
        if info.isTheorem && e.getAppNumArgs >= info.type.getNumHeadForalls then
          if proofTerms.isNone then
            let some value := theoremInfo.value? (allowOpaque := true) | return (false, none)
            proofTerms ← proofExpressions env value
          let some proofs := proofTerms | return (false, none)
          if proofs.contains e then forbidden := true
    if e.isAppOfArity ``Decidable 1 then
      if !forbidden && (← sameStatement theoremInfo.type e.getAppArgs[0]!) then forbidden := true
    if !forbidden && e.isApp && e.getAppFn.isConst then
      applications := applications.push e
    if let .const name _ := e then
      if constants.contains name then continue
      if constants.size >= provenanceConstantFuel then return (forbidden, none)
      constants := constants.insert name
      let some info := env.find? name | return (forbidden, none)
      let proofDeclaration := match info with
        | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
        | _ => false
      if name == theoremName || provenanceJudgeAPIs.contains name then forbidden := true
      -- A user-defined certificate has the same forbidden capability when a
      -- constructor parameter is Name (or StatementKey), whatever computes it.
      if let .ctorInfo ctor := info then
        if ctor.numParams > 256 then return (forbidden, none)
        let mut type := ctor.type
        for _ in [:ctor.numParams] do
          let .forallE _ parameter body _ := type | return (forbidden, none)
          let some parameter := recordHead env 256 parameter | return (forbidden, none)
          if parameter.isConstOf ``Name ||
              parameter.isConstOf `LeanInformationAudit.StatementKey then forbidden := true
          type := body
      if !forbidden && proofDeclaration && (← sameStatement theoremInfo.type info.type) then
        forbidden := true
      -- Literal evidence also covers materialized identities whose API call was
      -- evaluated before the readout was stored (e.g. String.append fragments).
      if !forbidden && info.type.isConstOf ``String then
        if ← boundedDefEq e (mkStrLit identity) then forbidden := true
      todo := info.type :: todo
      match info.value? (allowOpaque := true) with
      | some value => todo := value :: todo
      | none =>
        -- Kernel primitives/axioms have complete type-only dependency sets;
        -- an axiom used as the defining readout has no obtainable definition.
        if e == readout || (info.isAxiom &&
            !#[`propext, `Classical.choice, `Quot.sound].contains name) then
          return (forbidden, none)
    else
      todo := children e ++ todo
  -- Classify specialized instances only when raw provenance is still clean.
  -- Applications belong to the visited closure and therefore share its bound.
  if !forbidden then
    for e in applications do
      let some type := appliedType env e | return (false, none)
      if type.isAppOfArity ``Decidable 1 then
        if ← sameStatement theoremInfo.type type.getAppArgs[0]! then
          forbidden := true
          break
  let names := constants.toArray.map Name.toString |>.qsort (· < ·)
  return (forbidden, some names)

/-- A query owns one fresh Meta context and one classification cache. A total
200000-heartbeat/1024-depth bound also covers proof scanning and specialization.
Frozen registrations call this once at registration; the seal consumes metadata. -/
def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) := do
  trace[InformationProvenance.check] "{theoremName}: {readout.getAppFn.constName?}"
  tryCatchRuntimeEx (do
    withEnv env <| withCurrHeartbeats <| withOptions
      (fun o => (o.set `maxHeartbeats (200000 : Nat)).set `maxRecDepth (1024 : Nat)) <|
      (collectReadout env theoremName readout).run' {} |>.run')
    (fun _ => pure (false, none))

/-- IE-C050 precedes all readout-value diagnostics, including IE-C021. A family
is checked as one dependent function, covering every signature index without
sampling or enumerating realizations. Inline families use the realization owner
as their address; named families retain the defining constant's address. -/
def provenanceError (env : Environment) (root catalog theoremName realization : Name) :
    CoreM (Option String) := do
  let readout := readoutFamily env realization
  let address := readout.bind (·.getAppFn.constName?) |>.getD realization
  let (forbidden, closure) ← match readout with
    | some e => readoutClosure env theoremName e
    | none => pure (false, none)
  if !forbidden && closure.isSome then return none
  let reason := if closure.isNone then "incomplete_closure" else "forbidden_dependency"
  let payload := match closure with
    | some names => Json.arr (names.map Json.str)
    | none => Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} \
    readout={address} reason={reason} provenance={payload.compress}"

end LeanInformationAudit.RegistrationGates
