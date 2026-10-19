import LeanInformationAuditRegAnalysis.SearchReduction.Presentation
import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Constructions.RecOn
import Lean.Meta.Constructions.NoConfusion
import Lean.Meta.Constructions.BRecOn
import Lean.Meta.Structure

/-! Prefix reconstruction. Author certificate bodies never enter the search environment. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

abbrev transportVersion : String := "prefix-reconstruction-v1"
abbrev reconstructionBudget : Nat := 200000

private initialize referenceHintCache :
    IO.Ref (Option (Array (Nat × TSyntax `tactic))) ← IO.mkRef none

/-- The immutable strategy list always comes from the pinned Mathlib import,
including when a clean vocabulary prefix is already available. -/
def referenceHints : IO (Array (Nat × TSyntax `tactic)) := do
  if let some hints := ← referenceHintCache.get then return hints
  let env ← importModules #[{module := `Mathlib}] options 0
    (leakEnv := true) (loadExts := true)
  let hints ← strategies env
  referenceHintCache.set (some hints)
  return hints

structure VocabularyCertificate where
  owner : Name
  type : Expr
  proof : Expr
  axioms : Array Name

structure TransportContext where
  source : Environment
  target : Name := .anonymous
  targetType : Expr := mkSort .zero
  forbidden : NameSet := {}
  visiting : NameSet := {}
  bound : NameSet := {}
  certificates? : Option (IO.Ref (Array VocabularyCertificate)) := none
  budgetStart : Nat := 0
  searchHeartbeats? : Option (IO.Ref Nat) := none

private def sourceConstant (ctx : TransportContext) (n : Name) : MetaM ConstantInfo := do
  let some info := (ctx.source.setExporting false).find? n
    | throwError "search.missing_vocabulary: {n}"
  if info.isUnsafe then throwError "search.unsafe_vocabulary: {n}"
  return info

private def localParameters : MetaM (Array Expr) := do
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  return xs

/-- A source projection is recognized by its expression shape, then regenerated
from the rebuilt constructor telescope. No source proof value is installed. -/
def projectionShape (info : ConstantInfo) : Option (Name × Nat) := do
  let mut body ← info.value? (allowOpaque := true)
  while body.isLambda do body := body.bindingBody!
  let .proj owner index _ := body | none
  return (owner, index)

private def checkReconstructionBudget (ctx : TransportContext) : MetaM Unit := do
  if let some used := ctx.searchHeartbeats? then
    let work := (← IO.getNumHeartbeats) - ctx.budgetStart - (← used.get)
    if work > reconstructionBudget * 1000 then
      throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
        m!"search.vocabulary_work_budget: {work / 1000}/{reconstructionBudget}"

mutual
  partial def transportVocabulary (ctx : TransportContext) (n : Name) : MetaM Unit := do
    let ctx ← if ctx.searchHeartbeats?.isSome then pure ctx else do
      pure {ctx with budgetStart := ← IO.getNumHeartbeats, searchHeartbeats? := some (← IO.mkRef 0)}
    try
      -- R's independent commands retain their own limits. Their allocation is
      -- excluded from the separate bound on reconstruction work.
      withTheReader Core.Context (fun reader => {reader with maxHeartbeats := 0}) do
        checkReconstructionBudget ctx
        -- A referenced global definition owns its telescope. Parameters of the
        -- expression that mentioned it must never enter its proof obligations.
        withLCtx {} {} <| transportVocabularyCore ctx n
        checkReconstructionBudget ctx
    catch ex =>
      if ex.isMaxHeartbeat then
        throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
          m!"search.vocabulary_reconstruction_budget: {n}: {ex.toMessageData}"
      throw ex

  partial def transportVocabularyCore (ctx : TransportContext) (n : Name) : MetaM Unit := do
    if ctx.forbidden.contains n || n == ctx.target then
      throwError "search.target_in_vocabulary_certificate: {n}"
    if ctx.bound.contains n || (← getEnv).contains n then return
    if ctx.visiting.contains n then throwError "search.vocabulary_cycle: {n}"
    let info ← sourceConstant ctx n
    let next := {ctx with visiting := ctx.visiting.insert n}
    match info with
    | .inductInfo value => rebuildInductive next value
    | .ctorInfo value => transportVocabulary ctx value.induct
    | .recInfo value =>
      for owner in value.all do transportVocabulary ctx owner
      unless (← getEnv).contains n do throwError "search.generated_reconstruction_failed: {n}"
    | _ =>
      -- Generated eliminators are generated from the kernel-rebuilt group.
      if let .str owner suffix := n then
        if ["casesOn", "recOn", "noConfusion", "noConfusionType", "below", "brecOn"].contains suffix then
          if let some (.inductInfo _) := (ctx.source.setExporting false).find? owner then
            transportVocabulary ctx owner
            unless (← getEnv).contains n do throwError "search.generated_reconstruction_failed: {n}"
            return
      if let some (owner, index) := projectionShape info then
        transportVocabulary ctx owner
        let ind ← getConstInfoInduct owner
        let ctor ← getConstInfoCtor ind.ctors.head!
        let names := (Array.range (index + 1)).map fun i =>
          {ref := Syntax.missing, projName := if i == index then n else n ++ Name.num `_prefixProjection i : StructProjDecl}
        -- Generate earlier field projections under fresh names solely to obtain
        -- dependent field types. They contain only Expr.proj, never author terms.
        mkProjections owner names false
        unless ← isDefEq (← getConstInfo n).type info.type do
          throwError "search.generated_projection_type_mismatch: {n}"
        return
      if ← withEnv ctx.source (isProp info.type) then
        throwError "search.certificate_constant_requires_obligation: {n}"
      let .defnInfo value := info
        | throwError "search.generated_reconstruction_failed: {n}"
      let type ← reconstructExpression next n value.type
      let body ← reconstructExpression next n value.value
      addDecl (.defnDecl {value with type, value := body})
      setReducibilityStatus n .reducible
      IO.eprintln s!"vocabulary rebuilt: {n}"

  partial def reconstructExpression (ctx : TransportContext) (owner : Name) (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun part => do
      checkReconstructionBudget ctx
      if ← withEnv ctx.source (isProof part) then
        let type ← withEnv ctx.source (inferType part)
        let xs ← localParameters
        let closed ← mkForallFVars xs type
        -- Reconstruct only the obligation type; the author's term is never
        -- passed to R. The current group and the complete T/S set stay absent.
        let closed ← reconstructExpression ctx owner closed
        let levels := (collectLevelParams {} closed).params.toList
        if closed.getUsedConstants.any ctx.bound.contains then
          throwError "search.vocabulary_obligation_unclosed: {owner}: group-local type {closed}"
        let env ← getEnv
        let hints ← referenceHints
        let started ← IO.getNumHeartbeats
        let (outcome, rows) ← search env levels closed #[] hints
        let used := (← IO.getNumHeartbeats) - started
        if let some spent := ctx.searchHeartbeats? then spent.modify (· + used)
        checkReconstructionBudget ctx
        IO.eprintln s!"vocabulary obligation: owner={owner}, type={closed}, outcome={reprStr outcome}, internal_heartbeats={used}"
        let some row := rows.find? (·.proof?.isSome)
          | if outcome == .incomplete .heartbeat then
              throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
                m!"search.vocabulary_obligation_budget: {owner}: {closed}"
            let isTarget ← try
              withEnv ctx.source do
                let defeq := match Kernel.isDefEq ctx.source {} ctx.targetType closed with
                  | .ok equal => equal
                  | .error _ => false
                return defeq || (← singleSourceConversion ctx.targetType closed).isSome ||
                  (← certifiedRestatement ctx.targetType closed)
              catch ex =>
                if ex.isRuntime || ex.isInterrupt then throw ex
                pure false
            if isTarget then throwError "search.target_in_vocabulary_certificate: {owner}: {closed}"
            throwError "search.vocabulary_obligation_unclosed: {owner}: {closed}: {reprStr outcome}"
        let proof := row.proof?.get!
        let beforeCheck ← getEnv
        let checked ← checkProof (← mkFreshUserName `_prefixCertificate) levels closed proof
        setEnv beforeCheck
        if let some certificates := ctx.certificates? then
          certificates.modify (·.push {owner, type := closed, proof, axioms := checked})
        unless standardAxioms checked do throwError "search.vocabulary_certificate_axioms: {owner}"
        IO.eprintln s!"vocabulary certificate checked: owner={owner}, strategy={row.strategy}, axioms={checked}"
        -- Inline the result. No certificate constant becomes a searchable fact.
        let args ← xs.filterM fun x => return !(← getFVarLocalDecl x).isLet
        return .done (mkAppN proof args)
      if let .const n _ := part then transportVocabulary ctx n
      if let .proj n _ _ := part then transportVocabulary ctx n
      return .continue)

  partial def rebuildInductive (ctx : TransportContext) (value : InductiveVal) : MetaM Unit := do
    if value.numNested != 0 then
      throwError "search.generated_reconstruction_failed: nested group {value.all}"
    let group := value.all
    let signatureContext := {ctx with bound := group.foldl (fun s n => s.insert n) ctx.bound}
    let mut types := []
    for n in group do
      let .inductInfo member ← sourceConstant ctx n
        | throwError "search.generated_reconstruction_failed: group {n}"
      let mut ctors := []
      for c in member.ctors do
        let ctor ← sourceConstant ctx c
        let type ← reconstructExpression signatureContext c ctor.type
        ctors := ctors ++ [{name := c, type : Constructor}]
      let type ← reconstructExpression signatureContext n member.type
      types := types ++ [{name := n, type, ctors : InductiveType}]
    addDecl (.inductDecl value.levelParams value.numParams types false)
    for n in group do
      mkCasesOn n
      mkRecOn n
      mkNoConfusion n
      mkBelow n
    for n in group do mkBRecOn n
    IO.eprintln s!"vocabulary inductive group rebuilt: {group}"
end

/-- The import and witness-export paths use the same reconstruction kernel. -/
def copyVocabulary (source : Environment) (n : Name) (visiting : NameSet := {}) : MetaM Unit :=
  transportVocabulary {source, visiting} n

end LeanInformationAudit.SearchReduction
