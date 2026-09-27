import LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaOIProbe
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas
open LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaFiniteTemplates LeanInformationAudit
open Lean Meta Elab Command

register_information_template interventionFiniteRealization constructors 1
  [D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM]
register_information_template observationFiniteRealization constructors 1
  [D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection,
   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM]

run_cmd do
  for name in #[``interventionFiniteRealization, ``observationFiniteRealization] do
    match TemplateAudit.selectedPlan (← getEnv) name with
    | .ok plan => logInfo m!"ENROLL_PROBE {name}: accepted work={plan.chargedWork} bytes={plan.serializedBytes}"
    | .error err => logError m!"ENROLL_PROBE {name}: {err}"

def c0 : Fin 16 := (⟨Nat.zero, (let h : Nat.lt 0 16 := (by change 0 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c1 : Fin 16 := (⟨(Nat.succ Nat.zero), (let h : Nat.lt 1 16 := (by change 1 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c2 : Fin 16 := (⟨(Nat.succ (Nat.succ Nat.zero)), (let h : Nat.lt 2 16 := (by change 2 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c3 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ Nat.zero))), (let h : Nat.lt 3 16 := (by change 3 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c4 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))), (let h : Nat.lt 4 16 := (by change 4 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c5 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))), (let h : Nat.lt 5 16 := (by change 5 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c6 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))), (let h : Nat.lt 6 16 := (by change 6 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c7 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))), (let h : Nat.lt 7 16 := (by change 7 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c8 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))), (let h : Nat.lt 8 16 := (by change 8 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c9 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))), (let h : Nat.lt 9 16 := (by change 9 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c10 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))), (let h : Nat.lt 10 16 := (by change 10 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c11 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))))), (let h : Nat.lt 11 16 := (by change 11 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c12 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))), (let h : Nat.lt 12 16 := (by change 12 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c13 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))))))), (let h : Nat.lt 13 16 := (by change 13 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c14 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))), (let h : Nat.lt 14 16 := (by change 14 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))
def c15 : Fin 16 := (⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))))))))), (let h : Nat.lt 15 16 := (by change 15 < 16; decide); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))))

def pack4 (a b c d : Bool) : Fin 16 :=
  (Bool.rec (Bool.rec (Bool.rec (Bool.rec c0 c1 d) (Bool.rec c2 c3 d) c) (Bool.rec (Bool.rec c4 c5 d) (Bool.rec c6 c7 d) c) b) (Bool.rec (Bool.rec (Bool.rec c8 c9 d) (Bool.rec c10 c11 d) c) (Bool.rec (Bool.rec c12 c13 d) (Bool.rec c14 c15 d) c) b) a)

def marginal4 (a b c d : Bool) : Fin 16 :=
  (Bool.rec (Bool.rec (Bool.rec (Bool.rec c0 c1 d) (Bool.rec c3 c4 d) c) (Bool.rec (Bool.rec c1 c2 d) (Bool.rec c4 c5 d) c) b) (Bool.rec (Bool.rec (Bool.rec c3 c4 d) (Bool.rec c6 c7 d) c) (Bool.rec (Bool.rec c4 c5 d) (Bool.rec c7 c8 d) c) b) a)

private theorem finite_slot_sensitive (A : Arena) [DecidableEq A.State]
    (x y : A.State) (hne : x ≠ y) : FiniteSlotSensitivity (finiteArena A) := by
  let key : A.State → Fin 16 := fun z => if z = x then c0 else c1
  let good := interventionFiniteRealization (fun _ : A.State => c0) key
  let badFirst := interventionFiniteRealization key key
  let badSecond := interventionFiniteRealization (fun _ : A.State => c0) (fun _ => c0)
  have hg : (finiteArena A).Law good := by
    refine ⟨x, y, rfl, ?_⟩
    change key x ≠ key y
    simp [key, hne.symm, c0, c1]
  have hb1 : ¬ (finiteArena A).Law badFirst := by
    rintro ⟨a, b, he, hn⟩; exact hn he
  have hb2 : ¬ (finiteArena A).Law badSecond := by
    rintro ⟨a, b, he, hn⟩; exact hn rfl
  constructor
  · intro i; cases i
    · refine ⟨good, badFirst, ?_, ?_, ⟨fun _ => hb1, fun _ => hg⟩⟩
      · intro j hj; cases j; exact (hj rfl).elim; rfl
      · intro j; exact Fin.elim0 j
    · refine ⟨good, badSecond, ?_, ?_, ⟨fun _ => hb2, fun _ => hg⟩⟩
      · intro j hj; cases j; rfl; exact (hj rfl).elim
      · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j

section Intervention
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open D5.S3.ConceptDynamics.ConceptJoinUniversal
attribute [local instance] FourthFifthArenas.modelFintype FourthFifthArenas.modelDecidableEq

def icIntCode (M : DeterministicBoolSCM) : Fin 16 := marginal4
  (M.outcome false false) (M.outcome false true) (M.outcome true false) (M.outcome true true)
def icCFCode (M : DeterministicBoolSCM) : Fin 16 := pack4
  (M.outcome false false) (M.outcome false true) (M.outcome true false) (M.outcome true true)
private theorem ic_int_code_eq : ∀ M N : DeterministicBoolSCM,
    icIntCode M = icIntCode N ↔ Int M = Int N := by decide +kernel
private theorem ic_cf_code_eq : ∀ M N : DeterministicBoolSCM,
    icCFCode M = icCFCode N ↔ CF M = CF N := by decide +kernel
def interventionObject : Arena := Arena.ofFintype DeterministicBoolSCM
def interventionArena := finiteArena interventionObject
def interventionRealization : PrimitiveRealization (finiteSignature DeterministicBoolSCM) :=
  interventionFiniteRealization (fun M => icIntCode M) (fun M => icCFCode M)
private local instance : DecidableEq interventionArena.State := FourthFifthArenas.modelDecidableEq
private local instance : DecidableEq interventionObject.State := FourthFifthArenas.modelDecidableEq
private theorem intervention_equiv :
    FourthFifthArenas.interventionArena.Law SharedArenaPeers.interventionRealization ↔
      interventionArena.Law interventionRealization := by
  change (∃ M N, Int M = Int N ∧ CF M ≠ CF N) ↔
    ∃ M N, icIntCode M = icIntCode N ∧ icCFCode M ≠ icCFCode N
  simp only [ne_eq, ic_int_code_eq, ic_cf_code_eq]
private theorem intervention_law_sensitive : interventionArena.Law interventionRealization ∧
    ¬ interventionArena.Law (interventionFiniteRealization (fun _ => c0) (fun _ => c0)) :=
  ⟨intervention_equiv.mp SharedArenaPeers.intervention_law_sensitive.1,
    fun ⟨_,_,_,h⟩ => h rfl⟩
private theorem intervention_slot_sensitive : FiniteSlotSensitivity interventionArena :=
  finite_slot_sensitive interventionObject noEffectModel flipEffectModel (by
    change (noEffectModel : DeterministicBoolSCM) ≠ flipEffectModel
    decide)

private theorem intervention_bridge : LegacyPrimitiveRealization interventionArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  ⟨SharedArenaPeers.intervention_bridge.equivalence.trans intervention_equiv⟩
register_information_theorem intervention_strictly_weaker_than_counterfactual in interventionArena
  object_arena interventionObject catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives interventionRealization.toPrimitiveBundle realization intervention_bridge
  variation intervention_law_sensitive sensitivity intervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

private theorem finer_bridge : LegacyPrimitiveRealization interventionArena
    ((∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
      ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  ⟨SharedArenaPeers.finer_bridge.equivalence.trans intervention_equiv⟩
register_information_theorem counterfactual_kernel_strictly_finer in interventionArena
  object_arena interventionObject catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives interventionRealization.toPrimitiveBundle realization finer_bridge
  variation intervention_law_sensitive sensitivity intervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

private theorem fiber_bridge : LegacyPrimitiveRealization interventionArena
    (∃ μ M N, M ∈ couplingFiber allSingleWorldMarginals μ ∧
      N ∈ couplingFiber allSingleWorldMarginals μ ∧ CF M ≠ CF N) interventionRealization :=
  ⟨SharedArenaPeers.fiber_bridge.equivalence.trans intervention_equiv⟩
register_information_theorem boolean_counterfactual_varies_on_coupling_fiber in interventionArena
  object_arena interventionObject catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives interventionRealization.toPrimitiveBundle realization fiber_bridge
  variation intervention_law_sensitive sensitivity intervention_slot_sensitive
  escape from (BooleanCoupling) escape continues (open)

private theorem not_identifiable_bridge : LegacyPrimitiveRealization interventionArena
    (¬ ∃ f : (Bool → BooleanMarginal) → (Bool → Bool → Bool → Bool),
      CF = f ∘ allSingleWorldMarginals) interventionRealization :=
  ⟨SharedArenaPeers.not_identifiable_bridge.equivalence.trans intervention_equiv⟩
register_information_theorem boolean_counterfactual_not_identifiable in interventionArena
  object_arena interventionObject catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives interventionRealization.toPrimitiveBundle realization not_identifiable_bridge
  variation intervention_law_sensitive sensitivity intervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

private theorem target_bridge : LegacyPrimitiveRealization interventionArena
    (Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
      ¬ Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal)
    interventionRealization :=
  ⟨SharedArenaPeers.target_bridge.equivalence.trans intervention_equiv⟩
register_information_theorem interventional_marginal_sufficient_but_counterfactual_joint_not in interventionArena
  object_arena interventionObject catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives interventionRealization.toPrimitiveBundle realization target_bridge
  variation intervention_law_sensitive sensitivity intervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

end Intervention
section Observation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
def oiObsCode (M : DeterministicBoolSCM) : Fin 16 :=
  match M.direction with
  | .xCausesY => pack4 (M.root false) (M.child (M.root false))
      (M.root true) (M.child (M.root true))
  | .yCausesX => pack4 (M.child (M.root false)) (M.root false)
      (M.child (M.root true)) (M.root true)
def oiIntCode (M : DeterministicBoolSCM) : Fin 16 :=
  match M.direction with
  | .xCausesY => pack4 (M.child false) (M.child false) (M.child true) (M.child true)
  | .yCausesX => pack4 (M.root false) (M.root true) (M.root false) (M.root true)
private theorem oi_obs_code_eq : ∀ M N : DeterministicBoolSCM,
    oiObsCode M = oiObsCode N ↔ Obs M = Obs N := by decide +kernel
private theorem oi_int_code_eq : ∀ M N : DeterministicBoolSCM,
    oiIntCode M = oiIntCode N ↔ Int M = Int N := by decide +kernel
def observationObject : Arena := Arena.ofFintype DeterministicBoolSCM
def observationInterventionArena := finiteArena observationObject
def observationRealization : PrimitiveRealization (finiteSignature DeterministicBoolSCM) :=
  observationFiniteRealization (fun M => oiObsCode M) (fun M => oiIntCode M)
private local instance : DecidableEq observationInterventionArena.State := inferInstanceAs (DecidableEq DeterministicBoolSCM)
private local instance : DecidableEq observationObject.State := inferInstanceAs (DecidableEq DeterministicBoolSCM)
private theorem observation_equiv :
    ObservationIntervention.observationInterventionArena.Law SharedArenaPeers.observationRealization ↔
      observationInterventionArena.Law observationRealization := by
  change (∃ M N, Obs M = Obs N ∧ Int M ≠ Int N) ↔
    ∃ M N, oiObsCode M = oiObsCode N ∧ oiIntCode M ≠ oiIntCode N
  simp only [ne_eq, oi_obs_code_eq, oi_int_code_eq]
private theorem observation_law_sensitive : observationInterventionArena.Law observationRealization ∧
    ¬ observationInterventionArena.Law (observationFiniteRealization (fun _ => c0) (fun _ => c0)) :=
  ⟨observation_equiv.mp SharedArenaPeers.observation_law_sensitive.1,
    fun ⟨_,_,_,h⟩ => h rfl⟩
private theorem observation_slot_sensitive : FiniteSlotSensitivity observationInterventionArena :=
  finite_slot_sensitive observationObject xCausesYModel yCausesXModel (by
    change (xCausesYModel : DeterministicBoolSCM) ≠ yCausesXModel
    decide)

private theorem observation_bridge : LegacyPrimitiveRealization observationInterventionArena
    (∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N) observationRealization :=
  ⟨SharedArenaPeers.observation_bridge.equivalence.trans observation_equiv⟩
register_information_theorem observation_strictly_weaker_than_intervention in observationInterventionArena
  object_arena observationObject catalog finiteProbe
  readout via (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))
  primitives observationRealization.toPrimitiveBundle realization observation_bridge
  variation observation_law_sensitive sensitivity observation_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

private theorem profile_bridge : LegacyPrimitiveRealization observationInterventionArena
    (let profile : DeterministicBoolSCM → Option Bool → Bool → Bool × Bool :=
      fun M action => match action with | none => Obs M | some x => Int M x
    {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker profile p.1 p.2} ⊂
      {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker Obs p.1 p.2})
    observationRealization :=
  ⟨SharedArenaPeers.profile_bridge.equivalence.trans observation_equiv⟩
register_information_theorem intervention_kernel_strictly_finer_than_observation in observationInterventionArena
  object_arena observationObject catalog finiteProbe
  readout via (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))
  primitives observationRealization.toPrimitiveBundle realization profile_bridge
  variation observation_law_sensitive sensitivity observation_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (open)

end Observation
end LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaOIProbe
