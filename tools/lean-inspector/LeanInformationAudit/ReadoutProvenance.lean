import Lean

namespace LeanInformationAudit.RegistrationGates
open Lean

def provenanceConstantFuel : Nat := 4096
def provenanceExpressionFuel : Nat := 524288

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

initialize registerTraceClass `InformationProvenance.check

private def recordHead (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn with
    | .mdata _ body => recordHead env fuel (mkAppN body args)
    | .letE _ _ value body _ => recordHead env fuel (mkAppN (body.instantiate1 value) args)
    | .lam _ _ _ _ => if args.isEmpty then some e else recordHead env fuel (e.getAppFn.beta args)
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

private def familyCarriers (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    if #[
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index,
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Output,
      `D5.S3.ConceptDynamics.InformationEscape.Arena.State,
      `LeanInformationAudit.StructuralPrimitiveSignature.Index,
      `LeanInformationAudit.StructuralPrimitiveSignature.Output,
      `LeanInformationAudit.StructuralArena.State].contains (e.getAppFn.constName?.getD .anonymous) then
      return ← familyCarriers env fuel (← recordHead env 256 e)
    let go := familyCarriers env fuel
    match e with
    | .app f a => return .app (← go f) (← go a)
    | .lam n t b bi => return .lam n (← go t) (← go b) bi
    | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
    | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
    | .mdata m b => return .mdata m (← go b)
    | .proj n i b => return .proj n i (← go b)
    | _ => return e

private def readoutFamily (env : Environment) (realization : Name) : Option Expr := do
  let info ← env.find? realization
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env 256 info.type
      unless type.isAppOfArity `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do none
      type.getAppArgs[2]?
    | .defnInfo _ => some (mkConst realization)
    | _ => none
  let value ← recordHead env 256 root
  let name ← value.getAppFn.constName?
  unless name == `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      name == `LeanInformationAudit.StructuralPrimitiveRealization.mk do none
  familyCarriers env 256 (← value.getAppArgs[2]?)

private def generatedAddress : Name → Bool
  | .str parent suffix =>
      #["__information_unit", "__primitive_realization", "__structural_unit",
        "__structural_realization", "__information_catalog", "__lowers_escape",
        "__escape_enriched", "__trivial_in_catalog", "__state_enumeration",
        "__information_registration_diagnostic", "__kernel_projection"].contains suffix ||
      suffix.startsWith "__catalog_" || suffix.startsWith "__system_catalog_" || generatedAddress parent
  | .num parent _ => generatedAddress parent
  | .anonymous => false

private def judgePayload (info : ConstantInfo) : Bool :=
  match info with
  | .ctorInfo ctor => #[
      `LeanInformationAudit.InformationRegistryEntry, `LeanInformationAudit.ExpectedOccurrence,
      `LeanInformationAudit.CatalogUnitRecord, `LeanInformationAudit.CatalogRecord,
      `LeanInformationAudit.SealTheoremRecord, `LeanInformationAudit.SealArenaRecord,
      `LeanInformationAudit.SealedOccurrenceState, `LeanInformationAudit.StagedAnalysisState,
      `LeanInformationAudit.StructuralProvenanceEntry,
      `LeanInformationAudit.StructuralRegistrationEvidence,
      `LeanInformationAudit.BoundedTruncationFamily,
      `LeanInformationAudit.UnreachableElaborationEvidence,
      `LeanInformationAudit.AnalysisDisposition, `LeanInformationAudit.CensusAssessment,
      `LeanInformationAudit.AnalysisObservation, `LeanInformationAudit.DispositionInventory,
      `LeanInformationAudit.TruncationCertification].contains ctor.induct
  | _ => false

private def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

private def eraseLevels (e : Expr) : Expr :=
  let params := (collectLevelParams {} e).params.toList
  stripMData (e.instantiateLevelParams params (params.map fun _ => .zero))

private def containsExpr (needle hay : Expr) : Bool :=
  if eraseLevels hay == eraseLevels needle then true else
    match hay with
    | .app f a => containsExpr needle f || containsExpr needle a
    | .lam _ t b _ | .forallE _ t b _ => containsExpr needle t || containsExpr needle b
    | .letE _ t v b _ => containsExpr needle t || containsExpr needle v || containsExpr needle b
    | .mdata _ b => containsExpr needle b
    | .proj _ _ b => containsExpr needle b
    | _ => false

private def closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

private def telescopeResult : Expr → Expr
  | .forallE _ _ body _ => telescopeResult body
  | .mdata _ e => telescopeResult e
  | e => e

private def resultHead (e : Expr) : Option Name := (telescopeResult e).getAppFn.constName?

private def decisionFamily : Array Name := #[
  ``Decidable, ``DecidablePred, ``DecidableRel, ``DecidableEq,
  ``DecidableLE, ``DecidableLT]

private def listedProducers : Array Name := #[
  ``Decidable.isTrue, ``Decidable.isFalse, ``decidable_of_iff, ``decidable_of_iff',
  ``decidable_of_bool, ``decidable_of_decidable_of_iff, ``decidable_of_decidable_of_eq,
  ``decEq, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Bool.decEq,
  ``instDecidableEqOfLawfulBEq, ``inferInstance]

private def propLooking (env : Environment) : Expr → CoreM Bool
  | .forallE _ _ body _ => propLooking env body
  | .mdata _ e => propLooking env e
  | .const n _ => do
      let some info := env.find? n | return false
      return (telescopeResult info.type).isSort
  | .app f _ => do
      let some n := f.getAppFn.constName? | return false
      let some info := env.find? n | return false
      return (telescopeResult info.type).isSort
  | .sort .zero => pure true
  | _ => pure false

private def isCtorOrInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

private def moduleName (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) |>.getD env.header.mainModule

private def inProtected (env : Environment) (n : Name) : Bool :=
  if (env.getModuleIdxFor? n).isNone then true else
    let m := moduleName env n
    m == env.header.mainModule || m.getRoot == `D5 || m.getRoot == `LeanInformationAudit

private def namespaceLabel (env : Environment) (n : Name) : String :=
  if n.getRoot == `Classical then "external:Classical"
  else if inProtected env n then
    if moduleName env n == env.header.mainModule then "protected:current"
    else if n.getRoot == `LeanInformationAudit then "protected:judge" else "protected:D5"
  else "external:other"

private structure Unclassified where
  className : String
  firstName : Name
  namespaceName : String
  siteName : Name

private inductive Position where | dataPos | proofPos | typePos
  deriving BEq

private structure WalkState where
  theoremName : Name
  statement : Expr
  decision : Expr
  visited : Std.HashSet Expr := {}
  walked : NameHashSet := {}
  queued : NameHashSet := {}
  pending : List (Name × Position × Name) := []
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

private abbrev WalkM := StateRefT WalkState CoreM

private def noteUnclassified (u : Unclassified) : WalkM Unit := do
  if (← get).unclassified |>.isNone then modify fun s => { s with unclassified := some u }

private def queue (n : Name) (pos : Position) (site : Name) : WalkM Unit := do
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then modify fun s => { s with incomplete := true } else
    modify fun s => { s with queued := s.queued.insert n, pending := List.cons (n, pos, site) s.pending, constFuel := s.constFuel - 1 }

private def compareCanonical (a b : Expr) : Bool := eraseLevels a == eraseLevels b

private def hasPContent (env : Environment) (e : Expr) : Bool :=
  let rec go : Expr → Bool
    | .const n _ =>
      inProtected env n && match env.find? n with
      | some (.defnInfo _) | some (.opaqueInfo _) | some (.thmInfo _) => true
      | _ => false
    | .app f a => go f || go a
    | .lam _ t b _ | .forallE _ t b _ => go t || go b
    | .letE _ t v b _ => go t || go v || go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => false
  go e

private partial def visit (env : Environment) : Position → Name → Expr → WalkM Unit
  | pos, origin, e => do
    let s ← get
    if s.forbidden then return
    if s.exprFuel == 0 then modify fun s => { s with incomplete := true }; return
    modify fun s => { s with exprFuel := s.exprFuel - 1 }
    let e := stripMData e
    if (← get).visited.contains e then return
    modify fun s => { s with visited := s.visited.insert e }
    let dataPos := pos == .dataPos
    let checkU (x : Expr) : WalkM Unit := do
      if dataPos && (← propLooking env x) && closed x && hasPContent env x then
        noteUnclassified (Unclassified.mk "closed_decision" (x.getAppFn.constName?.getD `closed_decision) "protected:D5" origin)
    if dataPos && closed e && containsExpr (← get).statement e && e != (← get).statement then
      noteUnclassified (Unclassified.mk "statement_subterm" (e.getAppFn.constName?.getD `statement_subterm) "protected:current" origin)
    checkU e
    match e with
    | .const n _ =>
      let info := env.find? n
      modify fun s => { s with walked := s.walked.insert n }
      if n == (← get).theoremName then modify fun s => { s with forbidden := true }
      if provenanceJudgeAPIs.contains n || generatedAddress n || info.any judgePayload then
        modify fun s => { s with forbidden := true }
      if dataPos && n.getRoot == `Classical then
        noteUnclassified (Unclassified.mk "classical_choice" n "external:Classical" origin)
      if dataPos && !inProtected env n then
        if let some i := info then
          if !Lean.Meta.isInstanceCore env n then
            if let some h := resultHead i.type then
              if decisionFamily.contains h && !listedProducers.contains n then
                noteUnclassified (Unclassified.mk "unlisted_decision_producer" n (namespaceLabel env n) origin)
      if let some i := info then
        if compareCanonical i.type (← get).statement || compareCanonical i.type (← get).decision then
          modify fun s => { s with forbidden := true }
        if inProtected env n && !(← get).queued.contains n then queue n pos origin
      else modify fun s => { s with incomplete := true }
    | .app f a =>
      let args := e.getAppArgs
      if let .const head _ := e.getAppFn then
        if (head == ``Decidable.isTrue || head == ``Decidable.isFalse) && args.size > 0 then
          if compareCanonical args[0]! (← get).statement then modify fun s => { s with forbidden := true }
      visit env pos origin f; visit env pos origin a
    | .lam _ t b _ =>
      if compareCanonical t (← get).statement || compareCanonical t (← get).decision then
        modify fun s => { s with forbidden := true }
      else if containsExpr (← get).statement t then
        noteUnclassified (Unclassified.mk "statement_mentioning_type" (t.getAppFn.constName?.getD `statement_mentioning_type) "protected:current" origin)
      if dataPos then checkU t
      visit env .typePos origin t; visit env pos origin b
    | .forallE _ t b _ =>
      if compareCanonical t (← get).statement || compareCanonical t (← get).decision then
        modify fun s => { s with forbidden := true }
      else if containsExpr (← get).statement t then
        noteUnclassified (Unclassified.mk "statement_mentioning_type" (t.getAppFn.constName?.getD `statement_mentioning_type) "protected:current" origin)
      if dataPos then checkU t
      visit env .typePos origin t; visit env pos origin b
    | .letE _ t v b _ =>
      if compareCanonical t (← get).statement || compareCanonical t (← get).decision then
        modify fun s => { s with forbidden := true }
      else if containsExpr (← get).statement t then
        noteUnclassified (Unclassified.mk "statement_mentioning_type" (t.getAppFn.constName?.getD `statement_mentioning_type) "protected:current" origin)
      if dataPos then checkU t
      visit env .typePos origin t; visit env pos origin v; visit env pos origin b
    | .mdata _ b => visit env pos origin b
    | .proj n _ b =>
      if provenanceJudgeAPIs.contains n || generatedAddress n || (env.find? n).any judgePayload then
        modify fun s => { s with forbidden := true }
      visit env pos origin b
    | _ => pure ()

private def process (env : Environment) : WalkM Unit := do
  while !(← get).forbidden do
    let some (n, pos, site) := (← get).pending.head? | break
    modify fun s => { s with pending := s.pending.tail! }
    let some info := env.find? n | modify fun s => { s with incomplete := true }; continue
    if let some value := info.value? (allowOpaque := true) then
      let valuePos := match info with | .thmInfo _ => .proofPos | _ => .dataPos
      visit env .typePos n info.type
      visit env valuePos n value
    else if !isCtorOrInductive env n && !#[`propext, `Classical.choice, `Quot.sound].contains n then
      modify fun s => { s with incomplete := true }

private structure WalkResult where
  forbidden : Bool
  unclassified : Option Unclassified
  incomplete : Bool
  walked : Array String

private def collectReadout (env : Environment) (theoremName : Name) (readout : Expr) : CoreM WalkResult := do
  let some theoremInfo := env.find? theoremName | return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement := eraseLevels theoremInfo.type
  let decision := mkApp (mkConst ``Decidable) statement
  let computation : WalkM Unit := do
    visit env .dataPos (readout.getAppFn.constName?.getD theoremName) readout
    process env
  let (_, state) ← computation.run { theoremName := theoremName, statement := statement, decision := decision }
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  return (WalkResult.mk state.forbidden state.unclassified state.incomplete names)

private def safeCollect (env : Environment) (theoremName : Name) (readout : Expr) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName readout)
    (fun _ => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

private def readoutClosureCurrent (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  let r ← safeCollect env theoremName readout
  if r.incomplete then return (false, none)
  return (r.forbidden || r.unclassified.isSome, some r.walked)

def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) :=
  withEnv env (readoutClosureCurrent theoremName readout)

private def unclassifiedJson (u : Unclassified) (walked : Array String) : Json :=
  Json.mkObj [
    ("class", Json.str u.className), ("first", Json.str u.firstName.toString),
    ("namespace", Json.str u.namespaceName), ("site", Json.str u.siteName.toString),
    ("walked", Json.arr (walked.map Json.str))]

def provenanceErrorCurrent (root catalog theoremName realization : Name) : CoreM (Option String) := do
  let env ← getEnv
  let readout := readoutFamily env realization
  let address := readout.bind (·.getAppFn.constName?) |>.getD realization
  let result ← match readout with
    | some e => safeCollect env theoremName e
    | none => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  if !result.forbidden && result.unclassified.isNone && !result.incomplete then return none
  let reason := if result.forbidden then "forbidden_dependency"
    else if result.unclassified.isSome then "unclassified_form" else "incomplete_closure"
  let payload := if result.incomplete && result.unclassified.isNone then Json.null
    else if let some u := result.unclassified then unclassifiedJson u result.walked
    else Json.arr (result.walked.map Json.str)
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} \
+    readout={address} reason={reason} provenance={payload.compress}"

def provenanceError (env : Environment) (root catalog theoremName realization : Name) : CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

end LeanInformationAudit.RegistrationGates
