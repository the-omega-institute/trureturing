import D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Dependent-family realization of the attained installed-readout minimum. -/

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
open D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout

namespace Reg.D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout
universe u v

structure Model where
  Event : Type u
  finiteEvent : Fintype Event
  eventEq : DecidableEq Event
  family : Finset (Finset Event)

attribute [instance] Model.finiteEvent Model.eventEq

def pack {E : Type u} [Fintype E] [DecidableEq E] (F : Finset (Finset E)) : Model where
  Event := E
  finiteEvent := inferInstance
  eventEq := inferInstance
  family := F

abbrev signature : Signature where
  Params := Model.{u}
  State m := Finset m.Event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ m H => Hits m.family H) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law a := ∀ {E : Type u} [Fintype E] [DecidableEq E]
    (F : Finset (Finset E)), F.Nonempty →
    ((∃ H : Finset E, a.readout () (pack F) H ∧ H.card = hittingNumber F) ∧
      ∀ K : Finset E, a.readout () (pack F) K → hittingNumber F ≤ K.card) ∧
    (∀ (Q : Type v) (r : State F → Q),
      (∃ p : History E Q → Decision F, Acquires r p) →
      (sinks F).card + hittingNumber F ≤ effectiveSize r) ∧
    (∃ r : State F → State F ⊕ E, FiniteAcquirable r ∧
      effectiveSize r = (sinks F).card + hittingNumber F)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨H, hH, _⟩ := (h ({∅} : Finset (Finset (ULift.{u} Unit)))
    (Finset.singleton_nonempty _)).1.1
  exact hH

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let E := ULift.{u} Unit
  let F : Finset (Finset E) := Finset.univ
  let m : Model := pack F
  have hall : Hits F Finset.univ := by
    intro C hn
    obtain ⟨e, he⟩ : ∃ e, Enabled F C e := by simpa [Sink] using hn
    exact ⟨e, Finset.mem_univ _, he⟩
  have hnone : ¬ Hits F ∅ := by
    intro h
    let C : State F := ⟨∅, Finset.mem_univ _⟩
    have hn : ¬ Sink F C := by
      intro hs
      apply hs (ULift.up ())
      simp [Enabled, C, F]
    obtain ⟨e, he, _⟩ := h C hn
    simp at he
  refine ⟨m, ∅, Finset.univ, ?_⟩
  intro heq
  exact hnone (heq.mpr hall)

def family : Registration arena.{u,v} (type_of% (@installed_readout_optimum.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@installed_readout_optimum, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@installed_readout_optimum.{u,v}) (type_of% (actual.{u})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout.installed_readout_optimum.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m H => Hits m.family H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn","arg","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
end Reg.D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout
