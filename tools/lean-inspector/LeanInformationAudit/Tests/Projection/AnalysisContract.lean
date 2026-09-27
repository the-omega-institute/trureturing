import LeanInformationAudit.Projection.AnalysisProjection
import LeanInformationAudit.Tests.Projection.KernelLaws

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

private def prepareStageProof (name : Name) (value : Expr) :
    Lean.Elab.Term.TermElabM (Array Declaration) := do
  return (← (ProjectionProof.proof name value).run #[]).2

private def expectStageRejection (label : String) (names : Array Name)
    (prepare : Lean.Elab.Term.TermElabM (Array Declaration)) :
    Lean.Elab.Term.TermElabM Unit := do
  let before ← getEnv
  let rejected ← try
    let declarations ← prepare
    let _ ← stageDeclarations before declarations
    pure false
  catch _ => pure true
  unless rejected do
    throwError "[FAIL] ProjectionStage.{label}: accepted invalid declarations"
  let after ← getEnv
  for name in names do
    unless after.contains name == before.contains name do
      throwError "projection staging leaked {name} after rejecting {label}"

run_cmd do
  liftTermElabM do
    let testRoot := `ProjectionStageContract
    let first := testRoot.str "first"
    let second := testRoot.str "second"
    let closed := mkConst ``True.intro
    let before ← getEnv
    let declarations ← (do
      let _ ← ProjectionProof.proof first closed
      let _ ← ProjectionProof.proof second closed
      pure () : ProjectionM Unit).run #[]
    let staged ← stageDeclarations before declarations.2
    for name in #[first, second] do
      let some (.thmInfo info) := staged.find? name
        | throwError "projection staging omitted valid theorem {name}"
      unless info.type == mkConst ``True do
        throwError "projection staging changed valid theorem {name}"
      if (← getEnv).contains name then
        throwError "projection staging published {name} before its caller committed"

    let malformed := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero])
      #[mkConst ``Nat, mkConst ``True.intro]
    unless ← isProp (← inferType malformed) do
      throwError "projection staging fixture no longer exercises inference without checking"
    expectStageRejection "ill-typed-application" #[first] <|
      prepareStageProof first malformed

    expectStageRejection "unassigned-metavariable" #[first] do
      prepareStageProof first (← mkFreshExprMVar (mkConst ``True))
    expectStageRejection "assigned-raw-metavariable" #[first] do
      let value ← mkFreshExprMVar (mkConst ``True)
      value.mvarId!.assign closed
      prepareStageProof first value
    expectStageRejection "free-variable" #[first] <|
      withLocalDeclD `localProof (mkConst ``True) fun value =>
        prepareStageProof first value

    let unknown := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero])
      #[mkConst ``Nat, mkConst (testRoot.str "missing")]
    expectStageRejection "unknown-constant" #[first] <|
      prepareStageProof first unknown

    expectStageRejection "declared-type-mismatch" #[first] do
      let declarations ← prepareStageProof first closed
      return declarations.map fun declaration => match declaration with
        | .thmDecl info => .thmDecl { info with type := mkConst ``False }
        | _ => declaration

    -- Corrupt the second prepared declaration so rejection must occur during
    -- final kernel staging, after the first valid declaration was staged.
    expectStageRejection "later-invalid-declaration" #[first, second] do
      let firstDeclarations ← prepareStageProof first closed
      let secondDeclarations ← prepareStageProof second closed
      return firstDeclarations ++ secondDeclarations.map fun declaration => match declaration with
        | .thmDecl info => .thmDecl { info with value := mkNatLit 0 }
        | _ => declaration

    expectStageRejection "duplicate-batch-name" #[first] do
      let declarations ← prepareStageProof first closed
      return declarations ++ declarations
    expectStageRejection "existing-name-collision" #[``True.intro] <|
      prepareStageProof ``True.intro closed

run_cmd do
  let (analysis, declarations) ← liftTermElabM do
    let value ← mkConstWithFreshMVarLevels ``catalog
    let enum ← ProjectionProof.enumeration (← mkConstWithFreshMVarLevels ``arena) ``arena
    (prepareAnalysisProjection value enum #[``aFst, ``bSnd, ``cId] `AnalysisContract).run #[]
  unless analysis.exclusiveCaptureTotal == 0 do throwError "exclusive total"
  unless analysis.spectrum.map (·.count) == #[0, 0, 8, 4] do throwError "spectrum"
  unless analysis.overlap.map (·.count) == #[8, 4, 8, 8, 8, 12] do throwError "overlap"
  unless analysis.refinement[1]!.comparison == "incomparable" do throwError "refinement"
  unless analysis.equivalenceClasses.size == 3 do throwError "equivalence"
  setEnv (← liftCoreM <| stageDeclarations (← getEnv) declarations)
  for declaration in declarations do
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))

run_cmd do
  let (analysis, declarations) ← liftTermElabM do
    let members := #[``cId, ``bSnd, ``aFst]
    let vector ← ProjectionProof.vector (← members.mapM fun name => do
      mkConstWithFreshMVarLevels name)
    let value ← mkAppM
      ``D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector #[vector]
    let enum ← ProjectionProof.enumeration (← mkConstWithFreshMVarLevels ``arena) ``arena
    (prepareAnalysisProjection value enum members `ReverseAnalysisContract).run #[]
  unless analysis.overlap.size == 6 && analysis.overlap.all (fun row =>
      row.left == row.right || row.left.toString < row.right.toString) do
    throwError "overlap triangle must follow canonical Name order"
  setEnv (← liftCoreM <| stageDeclarations (← getEnv) declarations)
  for declaration in declarations do
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))

end LeanInformationAudit.Tests.Projection
