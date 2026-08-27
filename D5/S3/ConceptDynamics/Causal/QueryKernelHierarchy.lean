/- GID: D5/S3/ConceptDynamics/Causal/QueryKernelHierarchy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/QueryKernelHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nested query families induce a strictness-capable hierarchy of kernels. -/
/- Library-search audit trail (2026-08-27):
   * `rg -n 'queryKernel.*queryKernel|query.*kernel.*chain|kernel.*hierarch' D5`
     found no general theorem deriving both query-kernel inclusions from family containment.
   * `QueryFamilyIdentification.queryKernel` is the canonical dependent-family kernel
     primitive and is reused directly; no query, joint-law, or kernel definition is added.
   * `ObservationInterventionCounterfactualChain` is restricted to one Boolean SCM class,
     so it is not an exact hit for the general containment theorem. Its two countermodel
     clauses are reused directly as the required strictness witnesses.
   * A pinned Mathlib search for `query`, `counterfactual`, and `intervention` found no
     theorem for this causal-query hierarchy. Only congruence of equality is needed below. -/

import D5.S3.ConceptDynamics.Sufficiency.QueryFamilyIdentification
import D5.S3.ConceptDynamics.Causal.ObservationInterventionCounterfactualChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.QueryKernelHierarchy

open D5.S3.ConceptDynamics.Sufficiency.QueryFamilyIdentification
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Causal.ObservationInterventionCounterfactualChain

/-- If every observational query is readable from an interventional query and every
interventional query is readable from a counterfactual query, the corresponding kernels
form the expected chain. The two frozen Boolean countermodels witness strictness of its
two links. -/
theorem query_kernel_hierarchy
    {M ObsIndex IntIndex CfIndex : Type*}
    {ObsAnswer : ObsIndex -> Type*}
    {IntAnswer : IntIndex -> Type*}
    {CfAnswer : CfIndex -> Type*}
    (obsQuery : (i : ObsIndex) -> M -> ObsAnswer i)
    (intQuery : (i : IntIndex) -> M -> IntAnswer i)
    (cfQuery : (i : CfIndex) -> M -> CfAnswer i)
    (obsToInt : ObsIndex -> IntIndex)
    (intToCf : IntIndex -> CfIndex)
    (obsFromInt : (i : ObsIndex) -> IntAnswer (obsToInt i) -> ObsAnswer i)
    (intFromCf : (i : IntIndex) -> CfAnswer (intToCf i) -> IntAnswer i)
    (hObs : forall i m,
      obsFromInt i (intQuery (obsToInt i) m) = obsQuery i m)
    (hInt : forall i m,
      intFromCf i (cfQuery (intToCf i) m) = intQuery i m) :
    (forall m n, queryKernel cfQuery m n -> queryKernel intQuery m n) /\
    (forall m n, queryKernel intQuery m n -> queryKernel obsQuery m n) /\
    (exists first second : DeterministicBoolSCM,
      Int first = Int second /\ CF first ≠ CF second) /\
    (exists first second : DeterministicBoolSCM,
      Obs first = Obs second /\ Int first ≠ Int second) := by
  refine ⟨?_, ?_,
    observation_intervention_counterfactual_chain.2.2.1,
    observation_intervention_counterfactual_chain.2.2.2⟩
  · intro first second sameCf i
    calc
      intQuery i first = intFromCf i (cfQuery (intToCf i) first) := (hInt i first).symm
      _ = intFromCf i (cfQuery (intToCf i) second) :=
        congrArg (intFromCf i) (sameCf (intToCf i))
      _ = intQuery i second := hInt i second
  · intro first second sameInt i
    calc
      obsQuery i first = obsFromInt i (intQuery (obsToInt i) first) := (hObs i first).symm
      _ = obsFromInt i (intQuery (obsToInt i) second) :=
        congrArg (obsFromInt i) (sameInt (obsToInt i))
      _ = obsQuery i second := hObs i second

#print axioms query_kernel_hierarchy

example :
    let query : (i : Unit) -> Unit -> Unit := fun _ _ => ()
    let index : Unit -> Unit := id
    let readback : (i : Unit) -> Unit -> Unit := fun _ _ => ()
    (forall i m, readback i (query (index i) m) = query i m) /\
      (forall i m, readback i (query (index i) m) = query i m) := by
  simp

example : Nonempty Unit := ⟨()⟩

end D5.S3.ConceptDynamics.Causal.QueryKernelHierarchy
