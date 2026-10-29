import D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Dependent-family realization of the acquired-history criterion. -/

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition

namespace Reg.D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
universe u v

structure Model where
  Event : Type u
  finiteEvent : Fintype Event
  eventEq : DecidableEq Event
  family : Finset (Finset Event)
  nonempty : family.Nonempty
  Symbol : Type v
  readout : State family → Symbol

attribute [instance] Model.finiteEvent Model.eventEq

def pack {E : Type u} [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hF : F.Nonempty) {Q : Type v} (r : State F → Q) : Model where
  Event := E
  finiteEvent := inferInstance
  eventEq := inferInstance
  family := F
  nonempty := hF
  Symbol := Q
  readout := r

abbrev signature : Signature where
  Params := Model.{u,v}
  State m := History m.Event m.Symbol → Decision m.family
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ m p => Acquires m.readout p) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law a := ∀ {E : Type u} [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hF : F.Nonempty) {Q : Type v} (r : State F → Q),
    ((∃ p : History E Q → Decision F, a.readout () (pack hF r) p) ↔ CommonEnabled r) ∧
    (CommonEnabled r ↔ IsolatedSinks r) ∧
    (CommonEnabled r ↔ FiniteAcquirable r)

def small : Model.{u,v} where
  Event := ULift.{u} Unit
  finiteEvent := inferInstance
  eventEq := inferInstance
  family := {∅}
  nonempty := Finset.singleton_nonempty _
  Symbol := ULift.{v} Unit
  readout := fun _ => ULift.up ()

private theorem state_eq (C D : State small.family) : C = D := by
  apply Subtype.ext
  exact (Finset.mem_singleton.mp C.property).trans (Finset.mem_singleton.mp D.property).symm

private theorem small_common : CommonEnabled small.readout := by
  intro C h
  obtain ⟨D, _, hne⟩ := h
  exact (hne (state_eq D C)).elim

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨p, hp⟩ := (h small.nonempty small.readout).1.mpr small_common
  exact hp

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let C : State small.family := ⟨∅, Finset.mem_singleton_self _⟩
  let good : History small.Event small.Symbol → Decision small.family := fun _ => Sum.inl C
  let bad : History small.Event small.Symbol → Decision small.family := fun _ => Sum.inr (ULift.up ())
  have hg : Acquires small.readout good := by
    intro D
    refine ⟨0, Run.stop D (small.readout D, []) ?_⟩
    exact congrArg Sum.inl (state_eq C D)
  have hb : ¬ Acquires small.readout bad := by
    intro h
    obtain ⟨n, hn⟩ := h C
    cases hn with
    | stop D h hp => simp [bad] at hp
    | step D h e n hp he tail =>
      exact Finset.insert_ne_empty e _ (Finset.mem_singleton.mp he.2)
  refine ⟨small, good, bad, ?_⟩
  intro heq
  exact hb (heq.mp hg)

def family : Registration arena.{u,v} (type_of% (@acquisition_criterion.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@acquisition_criterion, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@acquisition_criterion.{u,v}) (type_of% (actual.{u,v})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition.acquisition_criterion.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m p => Acquires m.readout p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
    definition := none
    coordinates := #[0,1,2,3,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg","arg","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
end Reg.D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
