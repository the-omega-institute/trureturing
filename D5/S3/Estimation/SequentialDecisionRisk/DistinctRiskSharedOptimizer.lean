/- GID: D5/S3/Estimation/SequentialDecisionRisk/DistinctRiskSharedOptimizer
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/DistinctRiskSharedOptimizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct expected-risk profiles can induce the same optimizer profile. -/

import D5.S3.Estimation.SequentialDecisionRisk.PredictiveRiskOptimizerHierarchy

/- Library-search audit trail (2026-08-28):
   * The frozen hierarchy supplies the canonical `riskProfile` and
     `optimizerProfile`; both are instantiated rather than redeclared.
   * Pinned Mathlib has generic argmin APIs but no exact countermodel relating
     these source-semantic profiles.
   * Repository body-shape searches found no distinct-risk/shared-optimizer
     countermodel over the canonical profiles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.SequentialDecisionRisk.DistinctRiskSharedOptimizer

open D5.S3.Estimation.SequentialDecisionRisk.PredictiveRiskOptimizerHierarchy

/-- Two histories can have different expected-risk profiles while inducing the
same complete optimizer profile for the same predictive law and loss family. -/
theorem distinct_risk_profiles_can_share_optimizer_profile :
    ∃ (law : Bool → PMF Bool)
        (loss : Unit → Bool → Bool → Real),
      riskProfile law loss false ≠ riskProfile law loss true ∧
        optimizerProfile law loss false = optimizerProfile law loss true := by
  refine ⟨fun history => PMF.pure history,
    fun _ _ outcome => if outcome = true then 1 else 0, ?_, ?_⟩
  · intro risksEqual
    have sameRisk := congrFun (congrFun risksEqual ()) false
    norm_num [riskProfile] at sameRisk
  · funext task
    apply Set.ext
    intro action
    simp [optimizerProfile, riskProfile]

#print axioms distinct_risk_profiles_can_share_optimizer_profile

end D5.S3.Estimation.SequentialDecisionRisk.DistinctRiskSharedOptimizer
