import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause
import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity

/-! Existing frozen direct applications and a local conjunction projection.
The target modules are absent from the independent baseline imports. -/
open LeanInformationAudit.SearchReduction

#search_reduction D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause.clause_numerator_vanishes_at_golden
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [D5.S0.Tower.DBonacciGeneral.ChampionLimit]
  using [] as frozenAliasResult
#guard frozenAliasResult = Verdict.bindOnly

#search_reduction D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause.substitution_tower_clause
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [D5.S0.Tower.DBonacci.Substitution,
    D5.S0.Tower.DBonacciGeneral.ChampionLimit,
    D5.S0.Tower.ErgodicBridge.General,
    D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenAggregate,
    D5.S0.Tower.NonPisotVerdict.NotEventuallyPeriodic,
    D5.S0.Tower.NonPisot.GapCounts,
    D5.S0.Tower.TribonacciSurvivors.StrictFiniteDepth]
  using [] as frozenPackageResult
/- The first conjunct uses distinct compiler-generated matchers. Their types
are kernel definitionally equal, but reducible statement matching does not
identify the two matcher heads. With no S the graph records no reduction. -/
#guard frozenPackageResult = Verdict.insufficient
#guard frozenPackageResult.baseline = Run.exhausted ∨
  frozenPackageResult.baseline = Run.incomplete Failure.undecided

/- §5 preserves the complete source telescope. robustKnowledge is a predicate
definition, not a proof of the factivity statement; the conjunction theorem has
different binders. Neither supplies a single-source view of this target.
Its terminal predicate is not True, reflexive equality or an affine tautology,
so N does not certify it as neutral. Projection from the target's own
hKnowledge assumption belongs to R, independently of presentation lookup. -/
run_meta do
  let env ← Lean.getEnv
  let target := (← Lean.getConstInfo
    ``D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity.robust_knowledge_factivity).type
  let .ok keys := LeanInformationAudit.SearchReduction.normalizedAtoms env target
    | throwError "factivity target normalization failed"
  if keys.all (·.isScope) then throwError "factivity was incorrectly certified neutral"
  let definition := (← Lean.getConstInfo
    ``D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction.robustKnowledge).type
  if ← Lean.Meta.isProp definition then
    throwError "predicate definition was treated as a proposition proof"
  for name in #[
      ``D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction.robustKnowledge,
      ``D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction.robust_knowledge_conjunction] do
    let source := (← Lean.getConstInfo name).type
    let .ok sourceKeys := LeanInformationAudit.SearchReduction.normalizedAtoms env source
      | throwError "factivity source normalization failed: {name}"
    if LeanInformationAudit.SearchReduction.supportIncluded keys sourceKeys then
      throwError "incompatible factivity source matched the complete telescope: {name}"
  Lean.logInfo "factivity: nonneutral target; predicate definition and conjunction source do not match"

#search_reduction D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity.robust_knowledge_factivity
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction]
  using [] as frozenProjectionResult
#guard frozenProjectionResult = Verdict.bindOnly
#guard frozenProjectionResult.presentation = Run.exhausted
#guard frozenProjectionResult.baseline = Run.found

#print axioms frozenAliasResult.baselineProof
#print axioms frozenProjectionResult.baselineProof
