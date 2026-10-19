import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause
import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity

/-! Existing frozen direct applications and a local conjunction projection.
The target modules are absent from the independent baseline imports. -/
open LeanInformationAudit.Tests.SearchReduction

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
#guard frozenPackageResult = Verdict.bindOnly

#search_reduction D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity.robust_knowledge_factivity
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction]
  using [] as frozenProjectionResult
#guard frozenProjectionResult = Verdict.bindOnly
#guard frozenProjectionResult.presentation = Run.found ∨
  frozenProjectionResult.presentation = Run.exhausted

#print axioms frozenAliasResult.baselineProof
#print axioms frozenPackageResult.baselineProof
#print axioms frozenProjectionResult.baselineProof
