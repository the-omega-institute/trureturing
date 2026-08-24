/- GID: D5/S3/ConceptDynamics/Interventions/BlockCausalQuotientDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/BlockCausalQuotientDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Block intervention channels decompose causal equivalence and its quotient. -/

import D5.S3.ConceptDynamics.EmpiricalIdentifiability
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * Searches across `D5`, `Blueprint`, and every existing
     `ConceptDynamics/Interventions` module found no block-product causal
     equivalence or quotient decomposition.
   * Exact family SSOT hit `empiricalSetoid` is imported from
     `ConceptDynamics.EmpiricalIdentifiability` rather than redeclared.
   * Pinned Mathlib supplies the exact canonical product equivalence
     `Setoid.piQuotientEquiv`; it is applied directly below. No exact theorem
     already packages the intervention-channel equivalence. -/

noncomputable section

namespace D5.S3.ConceptDynamics.Interventions.BlockCausalQuotientDecomposition

open D5.S3.ConceptDynamics.EmpiricalIdentifiability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The joint response of independent blocks is assembled coordinatewise from
the local intervention channels. -/
def blockInterventionalOutcome {I : Type*} {Action Law : I -> Type*}
    (intervention : forall i, Action i)
    (model : forall i, Action i -> Law i) : forall i, Law i :=
  fun i => model i (intervention i)

private theorem block_equivalence_iff_local
    {I : Type*} {Action Law : I -> Type*}
    [forall i, Nonempty (Action i)]
    (M N : forall i, Action i -> Law i) :
    (forall intervention,
      blockInterventionalOutcome intervention M =
        blockInterventionalOutcome intervention N) <->
      forall i intervention, M i intervention = N i intervention := by
  classical
  constructor
  · intro h i intervention
    let baseline : forall j, Action j :=
      fun j => Classical.choice (inferInstance : Nonempty (Action j))
    have coordinateEquality :=
      congrFun (h (Function.update baseline i intervention)) i
    simpa only [blockInterventionalOutcome, Function.update_self] using
      coordinateEquality
  · intro h intervention
    funext i
    exact h i (intervention i)

/-- The canonical causal quotient map sends a global model class to the family
of its local model classes. -/
noncomputable def causalQuotientEquiv
    {I : Type*} {Action Law : I -> Type*} [Fintype I]
    [forall i, Nonempty (Action i)] :
    Quotient (empiricalSetoid
      (blockInterventionalOutcome (I := I) (Action := Action) (Law := Law))) ≃
      (forall i, Quotient (empiricalSetoid
        (fun intervention (model : Action i -> Law i) => model intervention))) :=
  (Quotient.congrRight (fun M N => block_equivalence_iff_local M N)).trans
    (Setoid.piQuotientEquiv (fun i => empiricalSetoid
      (fun intervention (model : Action i -> Law i) => model intervention))).symm

/-- With unrestricted product interventions, global causal equivalence is
exactly local causal equivalence in every block, and the canonical global
causal quotient is the finite product of the local causal quotients. -/
theorem causal_equivalence_block_decomposition
    {I : Type*} {Action Law : I -> Type*} [Fintype I]
    [forall i, Nonempty (Action i)] :
    (forall M N : forall i, Action i -> Law i,
      (forall intervention,
        blockInterventionalOutcome intervention M =
          blockInterventionalOutcome intervention N) <->
        forall i intervention, M i intervention = N i intervention) /\
    (forall M : forall i, Action i -> Law i,
      causalQuotientEquiv (I := I) (Action := Action) (Law := Law)
          (empiricalClass
            (blockInterventionalOutcome
              (I := I) (Action := Action) (Law := Law)) M) =
        fun i => empiricalClass
          (fun intervention (model : Action i -> Law i) => model intervention)
          (M i)) := by
  constructor
  · exact block_equivalence_iff_local
  · intro M
    rfl

#print axioms blockInterventionalOutcome
#print axioms causalQuotientEquiv
#print axioms causal_equivalence_block_decomposition

end D5.S3.ConceptDynamics.Interventions.BlockCausalQuotientDecomposition
