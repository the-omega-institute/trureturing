/- GID: D5/S3/ConceptDynamics/InformationEscape/SharedArenaPeers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SharedArenaPeers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Five frozen causal peers reuse separation on canonical arenas and expose zero unique capture in their maximal shared catalogs. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Census.Query

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers

open RegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open D5.S3.ConceptDynamics.CIRPT

register_information_template interventionFiniteRealization constructors 1
  [D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM]
register_information_template observationFiniteRealization constructors 1
  [D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection,
   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM]

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


/- The separation template supplies both readouts; the bridges only
transport statement shapes through existing fiber/factorization results.
No primitive reads theorem truth or proof data. Each arena keeps its gold peer. -/

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
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq

-- Shared, template-generated realization; reindexing preserves the canonical signature.
def interventionTemplate := separationRealization Int CF
def interventionRealization : PrimitiveRealization interventionSignature where
  readout | .intervention => interventionTemplate.readout false
          | .counterfactual => interventionTemplate.readout true
  anchor := Fin.elim0

theorem intervention_bridge : LegacyPrimitiveRealization interventionArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  ⟨(separationLegacy interventionArena.toArena Int CF).equivalence⟩

-- Law-variation witness at the registered signature: the actual realization satisfies
-- the law and a constant realization of the same signature fails it.
theorem intervention_law_sensitive : interventionArena.Law interventionRealization ∧
    ¬ interventionArena.Law ⟨(fun i _ => interventionRealization.readout i noEffectModel), Fin.elim0⟩ := by
  refine ⟨intervention_bridge.equivalence.mp intervention_strictly_weaker_than_counterfactual, ?_⟩
  rintro ⟨_, _, _, h⟩; exact h rfl

-- Slot sensitivity: two-class readouts keyed on the no-effect model let each readout
-- slot alone flip the law while the other slot and the (empty) anchors stay fixed.
def interventionKey (M : DeterministicBoolSCM) : Bool := decide (M = noEffectModel)

def interventionKeyedCounterfactual : PrimitiveRealization interventionSignature where
  readout | .intervention => fun _ _ _ => 0
          | .counterfactual => fun M _ _ _ => interventionKey M
  anchor := Fin.elim0

def interventionConstantCounterfactual : PrimitiveRealization interventionSignature where
  readout | .intervention => fun _ _ _ => 0
          | .counterfactual => fun _ _ _ _ => true
  anchor := Fin.elim0

def interventionKeyedBoth : PrimitiveRealization interventionSignature where
  readout | .intervention => fun M _ _ => if interventionKey M then 0 else 1
          | .counterfactual => fun M _ _ _ => interventionKey M
  anchor := Fin.elim0

theorem interventionKeyedCounterfactual_law :
    interventionArena.Law interventionKeyedCounterfactual :=
  ⟨noEffectModel, flipEffectModel, rfl, by
    show (fun (_ _ _ : Bool) => interventionKey noEffectModel) ≠
      (fun (_ _ _ : Bool) => interventionKey flipEffectModel)
    decide⟩

theorem interventionConstantCounterfactual_not_law :
    ¬ interventionArena.Law interventionConstantCounterfactual :=
  fun ⟨_, _, _, h⟩ => h rfl

theorem interventionKeyedBoth_not_law : ¬ interventionArena.Law interventionKeyedBoth := by
  rintro ⟨M, N, hInt, hCF⟩
  apply hCF
  have h : (if interventionKey M then 0 else 1) = (if interventionKey N then 0 else 1) :=
    congrFun (congrFun hInt true) true
  show (fun (_ _ _ : Bool) => interventionKey M) = (fun (_ _ _ : Bool) => interventionKey N)
  cases hM : interventionKey M <;> cases hN : interventionKey N <;> simp_all

theorem intervention_slot_sensitive :
    LeanInformationAudit.FiniteSlotSensitivity interventionArena := by
  constructor
  · intro i
    cases i
    · refine ⟨interventionKeyedCounterfactual, interventionKeyedBoth, ?_, ?_, ?_⟩
      · intro j hj; cases j
        · exact (hj rfl).elim
        · rfl
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ => interventionKeyedBoth_not_law, fun _ => interventionKeyedCounterfactual_law⟩
    · refine ⟨interventionKeyedCounterfactual, interventionConstantCounterfactual, ?_, ?_, ?_⟩
      · intro j hj; cases j
        · rfl
        · exact (hj rfl).elim
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ => interventionConstantCounterfactual_not_law,
          fun _ => interventionKeyedCounterfactual_law⟩
  · intro i; exact Fin.elim0 i

def icIntCode (M : DeterministicBoolSCM) : Fin 16 := marginal4
  (M.outcome false false) (M.outcome false true) (M.outcome true false) (M.outcome true true)
def icCFCode (M : DeterministicBoolSCM) : Fin 16 := pack4
  (M.outcome false false) (M.outcome false true) (M.outcome true false) (M.outcome true true)
private theorem ic_int_code_eq : ∀ M N : DeterministicBoolSCM,
    icIntCode M = icIntCode N ↔ Int M = Int N := by decide +kernel
private theorem ic_cf_code_eq : ∀ M N : DeterministicBoolSCM,
    icCFCode M = icCFCode N ↔ CF M = CF N := by decide +kernel
private def finiteInterventionStates : List DeterministicBoolSCM :=
  [false, true].flatMap fun ff =>
    [false, true].flatMap fun ft =>
      [false, true].flatMap fun tf =>
        [false, true].map fun tt =>
          ⟨fun exogenous treatment =>
            if exogenous then (if treatment then tt else tf)
            else if treatment then ft else ff⟩
def finiteInterventionArena : Arena := Arena.ofFintype DeterministicBoolSCM
def finiteInterventionLawArena := finiteArena finiteInterventionArena
namespace finiteInterventionArena
def __state_enumeration : Arena.StateEnumeration finiteInterventionArena where
  states := finiteInterventionStates
  nodup := by change finiteInterventionStates.Nodup; decide
  complete := by change finiteInterventionStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide
end finiteInterventionArena
private def finiteInterventionRealization : PrimitiveRealization (finiteSignature DeterministicBoolSCM) :=
  interventionFiniteRealization (fun M => icIntCode M) (fun M => icCFCode M)
private local instance : DecidableEq finiteInterventionLawArena.State := FourthFifthArenas.modelDecidableEq
private local instance : DecidableEq finiteInterventionArena.State := FourthFifthArenas.modelDecidableEq
private theorem finiteIntervention_equiv :
    FourthFifthArenas.interventionArena.Law interventionRealization ↔
      finiteInterventionLawArena.Law finiteInterventionRealization := by
  change (∃ M N, Int M = Int N ∧ CF M ≠ CF N) ↔
    ∃ M N, icIntCode M = icIntCode N ∧ icCFCode M ≠ icCFCode N
  simp only [ne_eq, ic_int_code_eq, ic_cf_code_eq]
private theorem finiteIntervention_law_sensitive :
    finiteInterventionLawArena.Law finiteInterventionRealization ∧
      ¬ finiteInterventionLawArena.Law
        (interventionFiniteRealization (fun _ => c0) (fun _ => c0)) :=
  ⟨finiteIntervention_equiv.mp intervention_law_sensitive.1,
    fun ⟨_, _, _, h⟩ => h rfl⟩
private theorem finiteIntervention_slot_sensitive :
    FiniteSlotSensitivity finiteInterventionLawArena :=
  finite_slot_sensitive finiteInterventionArena noEffectModel flipEffectModel (by
    change (noEffectModel : DeterministicBoolSCM) ≠ flipEffectModel
    decide)
private theorem finiteIntervention_bridge : LegacyPrimitiveRealization finiteInterventionLawArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N)
    finiteInterventionRealization :=
  ⟨intervention_bridge.equivalence.trans finiteIntervention_equiv⟩
private def finiteInterventionChain : LayerChain finiteInterventionLawArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun M : DeterministicBoolSCM => (icIntCode M, icCFCode M))
  refines := fun r => Fin.elim0 r
private theorem finiteIntervention_empty : EscapeResidualEmpty finiteInterventionChain := by
  change finiteInterventionChain.unresolvedCount = 0
  decide +kernel

register_information_theorem intervention_strictly_weaker_than_counterfactual in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteIntervention_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
expect_information_occurrence intervention_strictly_weaker_than_counterfactual in finiteInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- Pick 1: the collapse identity supplies the kernel inclusion independently of strictness.
theorem finer_bridge : LegacyPrimitiveRealization interventionArena
    ((∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
      ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization := by
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  exact ⟨And.right, fun h => ⟨counterfactual_eq_implies_interventional_eq, h⟩⟩
private theorem finiteFiner_bridge : LegacyPrimitiveRealization finiteInterventionLawArena
    ((∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
      ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N)
    finiteInterventionRealization :=
  ⟨finer_bridge.equivalence.trans finiteIntervention_equiv⟩
register_information_theorem counterfactual_kernel_strictly_finer in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteFiner_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
expect_information_occurrence counterfactual_kernel_strictly_finer in finiteInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- Pick 2: the common fiber label is existential bookkeeping, not a primitive.
theorem fiber_bridge : LegacyPrimitiveRealization interventionArena
    (∃ μ M N, M ∈ couplingFiber allSingleWorldMarginals μ ∧
      N ∈ couplingFiber allSingleWorldMarginals μ ∧ CF M ≠ CF N) interventionRealization := by
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  constructor
  · rintro ⟨μ, M, N, hM, hN, hCF⟩
    exact ⟨M, N, hM.trans hN.symm, hCF⟩
  · rintro ⟨M, N, hInt, hCF⟩
    exact ⟨allSingleWorldMarginals M, M, N, rfl, hInt.symm, hCF⟩
private theorem finiteFiber_bridge : LegacyPrimitiveRealization finiteInterventionLawArena
    (∃ μ M N, M ∈ couplingFiber allSingleWorldMarginals μ ∧
      N ∈ couplingFiber allSingleWorldMarginals μ ∧ CF M ≠ CF N)
    finiteInterventionRealization :=
  ⟨fiber_bridge.equivalence.trans finiteIntervention_equiv⟩
register_information_theorem boolean_counterfactual_varies_on_coupling_fiber in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteFiber_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (BooleanCoupling) escape continues (finiteIntervention_empty)
expect_information_occurrence boolean_counterfactual_varies_on_coupling_fiber in finiteInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- Pick 3: reuse the general factorization criterion, then negate its fiber condition.
theorem not_identifiable_bridge : LegacyPrimitiveRealization interventionArena
    (¬ ∃ f : (Bool → BooleanMarginal) → (Bool → Bool → Bool → Bool),
      CF = f ∘ allSingleWorldMarginals) interventionRealization := by
  classical
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  rw [counterfactual_identifiable_iff_constant_on_fiber]
  simp only [not_forall, exists_prop]
  rfl
private theorem finiteNotIdentifiable_bridge : LegacyPrimitiveRealization finiteInterventionLawArena
    (¬ ∃ f : (Bool → BooleanMarginal) → (Bool → Bool → Bool → Bool),
      CF = f ∘ allSingleWorldMarginals) finiteInterventionRealization :=
  ⟨not_identifiable_bridge.equivalence.trans finiteIntervention_equiv⟩
register_information_theorem boolean_counterfactual_not_identifiable in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteNotIdentifiable_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
expect_information_occurrence boolean_counterfactual_not_identifiable in finiteInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- Pick 4: the same criterion identifies exactly the failed target upgrade.
theorem target_bridge : LegacyPrimitiveRealization interventionArena
    (Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
      ¬ Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal)
    interventionRealization := by
  classical
  let : Nonempty DeterministicBoolSCM := ⟨noEffectModel⟩
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  have self := universal_sufficiency_factorization interventionMarginal interventionMarginal
  have target := universal_sufficiency_factorization interventionMarginal counterfactualJoint
  rw [self.1, self.2, target.1, target.2]
  simp only [not_forall, exists_prop]
  exact ⟨And.right, fun h => ⟨fun _ _ hsame => hsame, h⟩⟩
private theorem finiteTarget_bridge : LegacyPrimitiveRealization finiteInterventionLawArena
    (Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
      ¬ Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal)
    finiteInterventionRealization :=
  ⟨target_bridge.equivalence.trans finiteIntervention_equiv⟩
register_information_theorem interventional_marginal_sufficient_but_counterfactual_joint_not
  in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteTarget_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
expect_information_occurrence interventional_marginal_sufficient_but_counterfactual_joint_not in finiteInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- The bundle contains exactly the two law readouts and no anchors, for every state pair.
theorem intervention_exact_use (x y : DeterministicBoolSCM) :
    interventionRealization.toPrimitiveBundle.agrees x y ↔ Int x = Int y ∧ CF x = CF y := by
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  constructor
  · intro h; exact ⟨h.1 .intervention, h.1 .counterfactual⟩
  · intro h; exact ⟨fun i => by cases i; exact h.1; exact h.2, fun j => Fin.elim0 j⟩

theorem intervention_gold_kernel_equal : ∀ x y,
    interventionRealization.toPrimitiveBundle.agrees x y ↔
      InformationEscapeRealizations.FourthFifthRealizations.interventionRealization.toPrimitiveBundle.agrees x y := by decide

theorem intervention_nondegenerate : interventionArena.toArena.Nondegenerate := by decide
def interventionEnumeration : Arena.StateEnumeration interventionArena.toArena :=
  interventionArena.__state_enumeration

-- Order matches the canonical seal's theorem-name order; checked below against its builder.
def interventionCatalog : Catalog finiteInterventionArena := Catalog.ofVector ![
  boolean_counterfactual_not_identifiable.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  boolean_counterfactual_varies_on_coupling_fiber.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  counterfactual_kernel_strictly_finer.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  intervention_strictly_weaker_than_counterfactual.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  interventional_marginal_sufficient_but_counterfactual_joint_not.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit]

private theorem finiteIntervention_nondegenerate :
    finiteInterventionLawArena.toArena.Nondegenerate := by decide

theorem intervention_unique_zero (i : Fin 5) : interventionCatalog.uniqueCaptureCount i = 0 := by
  fin_cases i
  · exact (interventionCatalog.same_kernel_both_zero (0 : Fin 5) (1 : Fin 5) (by change (0 : Fin 5) ≠ 1; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (1 : Fin 5) (0 : Fin 5) (by change (1 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (2 : Fin 5) (0 : Fin 5) (by change (2 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (3 : Fin 5) (0 : Fin 5) (by change (3 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (4 : Fin 5) (0 : Fin 5) (by change (4 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1

end Intervention

section Observation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention

def observationTemplate := separationRealization Obs Int
def observationRealization : PrimitiveRealization observationInterventionSignature where
  readout | .observation => observationTemplate.readout false
          | .intervention => observationTemplate.readout true
  anchor := Fin.elim0

theorem observation_bridge : LegacyPrimitiveRealization observationInterventionArena
    (∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N) observationRealization :=
  ⟨(separationLegacy observationInterventionArena.toArena Obs Int).equivalence⟩

theorem observation_law_sensitive : observationInterventionArena.Law observationRealization ∧
    ¬ observationInterventionArena.Law ⟨(fun i _ => observationRealization.readout i xCausesYModel), Fin.elim0⟩ := by
  refine ⟨observation_bridge.equivalence.mp observation_strictly_weaker_than_intervention, ?_⟩
  rintro ⟨_, _, _, h⟩; exact h rfl

def observationKey (M : DeterministicBoolSCM) : Bool := decide (M = xCausesYModel)

def observationKeyedIntervention : PrimitiveRealization observationInterventionSignature where
  readout | .observation => fun _ _ => (false, false)
          | .intervention => fun M _ _ => (observationKey M, false)
  anchor := Fin.elim0

def observationConstantIntervention : PrimitiveRealization observationInterventionSignature where
  readout | .observation => fun _ _ => (false, false)
          | .intervention => fun _ _ _ => (false, false)
  anchor := Fin.elim0

def observationKeyedBoth : PrimitiveRealization observationInterventionSignature where
  readout | .observation => fun M _ => (observationKey M, false)
          | .intervention => fun M _ _ => (observationKey M, false)
  anchor := Fin.elim0

theorem observationKeyedIntervention_law :
    observationInterventionArena.Law observationKeyedIntervention :=
  ⟨xCausesYModel, yCausesXModel, rfl, by
    show (fun (_ _ : Bool) => (observationKey xCausesYModel, false)) ≠
      (fun (_ _ : Bool) => (observationKey yCausesXModel, false))
    decide⟩

theorem observationConstantIntervention_not_law :
    ¬ observationInterventionArena.Law observationConstantIntervention :=
  fun ⟨_, _, _, h⟩ => h rfl

theorem observationKeyedBoth_not_law : ¬ observationInterventionArena.Law observationKeyedBoth := by
  rintro ⟨M, N, hObs, hInt⟩
  apply hInt
  have h : observationKey M = observationKey N := congrArg Prod.fst (congrFun hObs true)
  show (fun (_ _ : Bool) => (observationKey M, false)) = (fun (_ _ : Bool) => (observationKey N, false))
  rw [h]

theorem observation_slot_sensitive :
    LeanInformationAudit.FiniteSlotSensitivity observationInterventionArena := by
  constructor
  · intro i
    cases i
    · refine ⟨observationKeyedIntervention, observationKeyedBoth, ?_, ?_, ?_⟩
      · intro j hj; cases j
        · exact (hj rfl).elim
        · rfl
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ => observationKeyedBoth_not_law, fun _ => observationKeyedIntervention_law⟩
    · refine ⟨observationKeyedIntervention, observationConstantIntervention, ?_, ?_, ?_⟩
      · intro j hj; cases j
        · rfl
        · exact (hj rfl).elim
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ => observationConstantIntervention_not_law,
          fun _ => observationKeyedIntervention_law⟩
  · intro i; exact Fin.elim0 i

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
private def finiteObservationStates : List DeterministicBoolSCM :=
  [.xCausesY, .yCausesX].flatMap fun direction =>
    [fun _ => false, id, fun x => !x, fun _ => true].flatMap fun root =>
      [fun _ => false, id, fun x => !x, fun _ => true].map fun child =>
        ⟨direction, root, child⟩
def finiteObservationInterventionArena : Arena := Arena.ofFintype DeterministicBoolSCM
def finiteObservationInterventionLawArena := finiteArena finiteObservationInterventionArena
namespace finiteObservationInterventionArena
def __state_enumeration : Arena.StateEnumeration finiteObservationInterventionArena where
  states := finiteObservationStates
  nodup := by change finiteObservationStates.Nodup; decide
  complete := by change finiteObservationStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide
end finiteObservationInterventionArena
private def finiteObservationRealization : PrimitiveRealization (finiteSignature DeterministicBoolSCM) :=
  observationFiniteRealization (fun M => oiObsCode M) (fun M => oiIntCode M)
private local instance : DecidableEq finiteObservationInterventionLawArena.State := inferInstanceAs (DecidableEq DeterministicBoolSCM)
private local instance : DecidableEq finiteObservationInterventionArena.State := inferInstanceAs (DecidableEq DeterministicBoolSCM)
private theorem finiteObservation_equiv :
    ObservationIntervention.observationInterventionArena.Law observationRealization ↔
      finiteObservationInterventionLawArena.Law finiteObservationRealization := by
  change (∃ M N, Obs M = Obs N ∧ Int M ≠ Int N) ↔
    ∃ M N, oiObsCode M = oiObsCode N ∧ oiIntCode M ≠ oiIntCode N
  simp only [ne_eq, oi_obs_code_eq, oi_int_code_eq]
private theorem finiteObservation_law_sensitive :
    finiteObservationInterventionLawArena.Law finiteObservationRealization ∧
      ¬ finiteObservationInterventionLawArena.Law
        (observationFiniteRealization (fun _ => c0) (fun _ => c0)) :=
  ⟨finiteObservation_equiv.mp observation_law_sensitive.1,
    fun ⟨_, _, _, h⟩ => h rfl⟩
private theorem finiteObservation_slot_sensitive :
    FiniteSlotSensitivity finiteObservationInterventionLawArena :=
  finite_slot_sensitive finiteObservationInterventionArena xCausesYModel yCausesXModel (by
    change (xCausesYModel : DeterministicBoolSCM) ≠ yCausesXModel
    decide)
private def finiteObservationInterventionChain :
    LayerChain finiteObservationInterventionLawArena.toArena where
  length := 0
  kernel := fun _ => cutKernel
    (fun M : DeterministicBoolSCM => (oiObsCode M, oiIntCode M))
  refines := fun r => Fin.elim0 r
private def finiteObservationResidual :
    EscapeResidualWitness finiteObservationInterventionChain :=
  ⟨⟨.xCausesY, fun _ => false, fun _ => false⟩,
    ⟨.yCausesX, fun _ => false, fun _ => false⟩, by decide +kernel⟩
private theorem finiteObservation_bridge :
    LegacyPrimitiveRealization finiteObservationInterventionLawArena
      (∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N)
      finiteObservationRealization :=
  ⟨observation_bridge.equivalence.trans finiteObservation_equiv⟩

register_information_theorem observation_strictly_weaker_than_intervention in finiteObservationInterventionLawArena
  object_arena finiteObservationInterventionArena catalog finiteProbe
  readout via (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))
  primitives finiteObservationRealization.toPrimitiveBundle realization finiteObservation_bridge
  variation finiteObservation_law_sensitive sensitivity finiteObservation_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteObservationResidual)
expect_information_occurrence observation_strictly_weaker_than_intervention in finiteObservationInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

-- Pick 5: a full profile includes the null action, so its strictness is separation.
theorem profile_bridge : LegacyPrimitiveRealization observationInterventionArena
    (let profile : DeterministicBoolSCM → Option Bool → Bool → Bool × Bool :=
      fun M action => match action with | none => Obs M | some x => Int M x
    {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker profile p.1 p.2} ⊂
      {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker Obs p.1 p.2})
    observationRealization := by
  refine ⟨Iff.trans ?_ observation_bridge.equivalence⟩
  dsimp only
  rw [Set.ssubset_iff_exists]
  constructor
  · rintro ⟨_, ⟨M, N⟩, hObs, hProfile⟩
    refine ⟨M, N, hObs, fun hInt => hProfile ?_⟩
    funext action; cases action with
    | none => exact hObs
    | some x => exact congrFun hInt x
  · rintro ⟨M, N, hObs, hInt⟩
    refine ⟨fun _ h => congrFun h none, (M, N), hObs, fun h => hInt ?_⟩
    funext x; exact congrFun h (some x)
private theorem finiteProfile_bridge :
    LegacyPrimitiveRealization finiteObservationInterventionLawArena
      (let profile : DeterministicBoolSCM → Option Bool → Bool → Bool × Bool :=
        fun M action => match action with | none => Obs M | some x => Int M x
      {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker profile p.1 p.2} ⊂
        {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker Obs p.1 p.2})
      finiteObservationRealization :=
  ⟨profile_bridge.equivalence.trans finiteObservation_equiv⟩
register_information_theorem intervention_kernel_strictly_finer_than_observation
  in finiteObservationInterventionLawArena
  object_arena finiteObservationInterventionArena catalog finiteProbe
  readout via (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))
  primitives finiteObservationRealization.toPrimitiveBundle realization finiteProfile_bridge
  variation finiteObservation_law_sensitive sensitivity finiteObservation_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteObservationResidual)
expect_information_occurrence intervention_kernel_strictly_finer_than_observation in finiteObservationInterventionArena
  from "D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers"

theorem observation_exact_use (x y : DeterministicBoolSCM) :
    observationRealization.toPrimitiveBundle.agrees x y ↔ Obs x = Obs y ∧ Int x = Int y := by
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  constructor
  · intro h; exact ⟨h.1 .observation, h.1 .intervention⟩
  · intro h; exact ⟨fun i => by cases i; exact h.1; exact h.2, fun j => Fin.elim0 j⟩

theorem observation_gold_kernel_equal : ∀ x y,
    observationRealization.toPrimitiveBundle.agrees x y ↔
      InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization.toPrimitiveBundle.agrees x y := by decide

theorem observation_nondegenerate : observationInterventionArena.toArena.Nondegenerate := by decide
def observationEnumeration : Arena.StateEnumeration observationInterventionArena.toArena :=
  observationInterventionArena.__state_enumeration

def observationCatalog : Catalog finiteObservationInterventionArena := Catalog.ofVector ![
  intervention_kernel_strictly_finer_than_observation.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit,
  observation_strictly_weaker_than_intervention.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit]

private theorem finiteObservation_nondegenerate :
    finiteObservationInterventionLawArena.toArena.Nondegenerate := by decide

theorem observation_unique_zero (i : Fin 2) : observationCatalog.uniqueCaptureCount i = 0 := by
  fin_cases i
  · exact (observationCatalog.same_kernel_both_zero (0 : Fin 2) (1 : Fin 2) (by change (0 : Fin 2) ≠ 1; decide) (fun _ _ => Iff.rfl)).1
  · exact (observationCatalog.same_kernel_both_zero (1 : Fin 2) (0 : Fin 2) (by change (1 : Fin 2) ≠ 0; decide) (fun _ _ => Iff.rfl)).1

end Observation

/-- Every occurrence in both maximal catalogs is trivial relative to its real peers. -/
theorem all_peers_trivial :
    (∀ i, interventionCatalog.TrivialInCatalog i) ∧ (∀ i, observationCatalog.TrivialInCatalog i) := by
  constructor
  · intro i; exact Finset.card_eq_zero.mp (intervention_unique_zero i)
  · intro i; exact Finset.card_eq_zero.mp (observation_unique_zero i)

/-- Removing any one occurrence leaves escape unchanged in both nondegenerate arenas. -/
theorem no_peer_lowers_escape :
    (∀ i, ¬ interventionCatalog.LowersEscape i) ∧
    (∀ i, ¬ observationCatalog.LowersEscape i) := by
  exact ⟨fun i => (Catalog.trivialInCatalog_iff_not_lowersEscape _ _ finiteIntervention_nondegenerate).mp
    (all_peers_trivial.1 i),
    fun i => (Catalog.trivialInCatalog_iff_not_lowersEscape _ _ finiteObservation_nondegenerate).mp
      (all_peers_trivial.2 i)⟩

-- Compare the measured catalogs with the engine's complete, canonically grouped vectors.
open Lean Meta LeanInformationAudit in
run_cmd do
  let catalogs ← prepareCatalogs
  unless catalogs.size == 2 do throwError "expected two maximal canonical catalogs"
  for (prepared, expected) in catalogs.zip #[``interventionCatalog, ``observationCatalog] do
    Lean.Elab.Command.liftTermElabM do
      unless ← isDefEq prepared.type (← inferType (mkConst expected)) do
        throwError "measured catalog uses a different canonical arena: {expected}"
      -- The engine's empty vector tail is extensionally empty, not definitionally
      -- the vecEmpty term. Check every actual unit in its complete finite vector.
      for unit in prepared.record.units do
        let bound ← mkAppM ``LT.lt #[mkNatLit unit.index, mkNatLit prepared.record.units.size]
        let position ← mkAppM ``Fin.mk #[mkNatLit unit.index, ← mkDecideProof bound]
        let measured ← mkAppM ``Catalog.theoremAt #[mkConst expected, position]
        unless ← isDefEq measured (mkConst unit.unitName) do
          throwError "measured catalog differs at occurrence {unit.theoremName}"
    logInfo m!"MAXIMAL_CATALOG_VALIDATED: {prepared.record.arenaName}; occurrences={prepared.record.units.size}"

-- Zero capture is an informational disposition. Both complete catalogs seal as redundant.
#guard_msgs (error) in
#seal_information_theory

open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let records := SealRecords.forRoot env env.header.mainModule
  unless records.map (·.theorems.size) == #[5, 2] &&
      records.map (·.fullEscapeCount) == #[0, 24] do
    throwError "expected both complete maximal catalogs with unchanged escape counts"
  for record in records do
    unless (match record.verdict with
        | .redundant certificate => env.contains certificate
        | .irredundant _ => false) do
      throwError "zero-capture catalog requires a published redundancy certificate"
    for occurrence in record.theorems do
      unless occurrence.uniqueCaptureCount == 0 &&
          occurrence.withoutEscapeCount == record.fullEscapeCount &&
          (match occurrence.certificate with
          | .trivial certificate => env.contains certificate
          | .positive _ => false) do
        throwError "every peer requires a zero-capture triviality certificate"
  if SealRecords.systemCatalogIrredundant env env.header.mainModule then
    throwError "redundant maximal catalogs cannot certify system irredundancy"
  let index ← CensusQuery.indexScope env.header.mainModule
  let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  unless head.exitCode == 0 do throwError "cannot read checkout identity"
  let entries := InformationRegistry.entries env
  unless entries.size == 7 do throwError "expected seven registered occurrences"
  for entry in entries do
    let key : StatementKey := ⟨entry.theoremName, theoremStatementIdentity env entry.theoremName⟩
    match ← CensusQuery.assess index head.stdout.trimAscii.toString key with
    | .certified (.trivialInCatalog payload) =>
        unless payload.root == env.header.mainModule do
          throwError "triviality certificate belongs to a different root"
        logInfo m!"CENSUS_QUERY_TRIVIAL: {entry.theoremName}; registered=true; positive=false"
    | _ => throwError "maximal catalog lacks certified triviality for {entry.theoremName}"

#print axioms D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit
#print axioms D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation.«D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit
#print axioms intervention_gold_kernel_equal
#print axioms observation_gold_kernel_equal
#print axioms no_peer_lowers_escape

#print axioms finer_bridge
#print axioms fiber_bridge
#print axioms not_identifiable_bridge
#print axioms target_bridge
#print axioms profile_bridge
#print axioms intervention_exact_use
#print axioms observation_exact_use
#print axioms intervention_law_sensitive
#print axioms observation_law_sensitive
#print axioms intervention_nondegenerate
#print axioms observation_nondegenerate
#print axioms interventionEnumeration
#print axioms observationEnumeration
#print axioms all_peers_trivial
#print axioms intervention_slot_sensitive
#print axioms observation_slot_sensitive

end D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
