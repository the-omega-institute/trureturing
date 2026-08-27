/- GID: D5/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictive laws refine expected-risk and optimizer-set equivalence. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-28):
   * No exact D5 or pinned-Mathlib theorem was found for the three-way
     predictive-law/risk/optimizer kernel chain.
   * `PosteriorUniversalSufficiency` and `ExperimentStatePosteriorDecisionSeparation`
     are posterior-specific and do not state the source's complete-law premise.
   * Body-shape searches for a general finite PMF risk profile and optimizer-set
     profile found no existing declarations; the two source primitives are
     introduced here and used independently in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Estimation.SequentialDecisionRisk.PredictiveRiskOptimizerHierarchy

universe u

/- The expected-loss profile is built from the predictive law and the source's
   loss family, rather than postulating a risk relation. -/
def riskProfile {History Outcome Task Action : Type*} [Fintype Outcome]
    (law : History -> PMF Outcome)
    (loss : Task -> Action -> Outcome -> Real) :
    History -> Task -> Action -> Real :=
  fun history task action =>
    ∑ outcome, (law history outcome).toReal * loss task action outcome

/- The optimizer profile records the full action argmin set separately for
   every task in the source loss family. -/
def optimizerProfile {History Outcome Task Action : Type*} [Fintype Outcome]
    (law : History -> PMF Outcome)
    (loss : Task -> Action -> Outcome -> Real) :
    History -> Task -> Set Action :=
  fun history task =>
    {action | ∀ alternative,
      riskProfile law loss history task action ≤
        riskProfile law loss history task alternative}

/- Complete predictive-law equality implies equality of every expected risk,
   and equality of the complete risk vector implies equality of every task's
   optimizer set. -/
theorem predictive_risk_optimizer_kernel_hierarchy
    {History Outcome Task Action : Type*} [Fintype Outcome]
    (law : History -> PMF Outcome)
    (loss : Task -> Action -> Outcome -> Real) :
    Setoid.ker law ≤ Setoid.ker (riskProfile law loss) ∧
      Setoid.ker (riskProfile law loss) ≤ Setoid.ker (optimizerProfile law loss) := by
  constructor
  · intro history history' equalLaw
    change law history = law history' at equalLaw
    funext task action
    simp only [riskProfile]
    rw [equalLaw]
  · intro history history' equalRisk
    change riskProfile law loss history = riskProfile law loss history' at equalRisk
    change optimizerProfile law loss history = optimizerProfile law loss history'
    funext task
    apply Set.ext
    intro action
    constructor
    · intro optimal
      change ∀ alternative,
        riskProfile law loss history task action ≤
          riskProfile law loss history task alternative at optimal
      change ∀ alternative,
        riskProfile law loss history' task action ≤
          riskProfile law loss history' task alternative
      intro alternative
      calc
        riskProfile law loss history' task action =
            riskProfile law loss history task action :=
          (congrFun (congrFun equalRisk task) action).symm
        _ ≤ riskProfile law loss history task alternative :=
          optimal alternative
        _ = riskProfile law loss history' task alternative :=
          congrFun (congrFun equalRisk task) alternative
    · intro optimal
      change ∀ alternative,
        riskProfile law loss history' task action ≤
          riskProfile law loss history' task alternative at optimal
      change ∀ alternative,
        riskProfile law loss history task action ≤
          riskProfile law loss history task alternative
      intro alternative
      calc
        riskProfile law loss history task action =
            riskProfile law loss history' task action :=
          congrFun (congrFun equalRisk task) action
        _ ≤ riskProfile law loss history' task alternative :=
          optimal alternative
        _ = riskProfile law loss history task alternative :=
          (congrFun (congrFun equalRisk task) alternative).symm

example :
    Setoid.ker (fun _ : Unit => PMF.pure ()) ≤
      Setoid.ker (riskProfile (History := Unit) (Outcome := Unit)
        (Task := Unit) (Action := Unit) (fun _ : Unit => PMF.pure ())
        (fun _ _ _ => (0 : Real))) := by
  intro first second _
  rfl

example : optimizerProfile (History := Unit) (Outcome := Unit)
    (Task := Unit) (Action := Unit) (fun _ : Unit => PMF.pure ())
    (fun _ _ _ => (0 : Real)) () () = Set.univ := by
  apply Set.eq_univ_of_forall
  intro action
  intro alternative
  rfl

#print axioms predictive_risk_optimizer_kernel_hierarchy

end D5.S3.Estimation.SequentialDecisionRisk.PredictiveRiskOptimizerHierarchy
