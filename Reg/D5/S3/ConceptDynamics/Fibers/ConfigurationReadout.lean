import D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
import Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
open D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
namespace Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
universe u v
abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {E : Type u} [PartialOrder E] (compatible : Finset E → Prop)
    (R : LocalReadout.{u,v} compatible),
    (∀ (C D : FiniteConfigurations compatible) (l m : List E)
      (hl : Exec C.1 l D.1) (hm : Exec C.1 m D.1) (x : R.fibre C),
      r.readout () (R.fibre D) (legalPathMap compatible R C D l hl x)
        (legalPathMap compatible R C D m hm x)) ↔ LegalDiamonds compatible R

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let compatible : Finset (ULift.{u} Unit) → Prop := fun _ => True
  let R : LocalReadout compatible := {fibre := fun _ => ULift.{v} Unit,edge := fun _ _ _ _ _ x => x}
  have hd : LegalDiamonds compatible R := by
    intro C D a b ha hb hab hba he x
    have heq : b = a := Subsingleton.elim _ _
    subst b
    exact (hab.1 (Set.mem_insert a C.1)).elim
  let O := emptyConfiguration compatible True.intro
  exact (h compatible R).mpr hd O O [] [] rfl rfl (ULift.up ())

def family : Registration arena.{u,v} (type_of% (@actual_path_composition_iff.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_path_composition_iff,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨ULift.{v} Bool,ULift.up false,ULift.up true,?_⟩
    intro h
    have hh : (ULift.up false : ULift.{v} Bool) = ULift.up true := (congrFun h (ULift.up true)).mpr rfl
    have hh' := congrArg ULift.down hh
    cases hh'

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_path_composition_iff.{u,v})
    (type_of% (realize signature.{v} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationReadout.actual_path_composition_iff.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationReadout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family


abbrev staticArena : Arena where
  signature := signature.{v}
  Law q := ∀ {E : Type u} [PartialOrder E] (compatible : Finset E → Prop)
    (R : LocalReadout.{u,v} compatible) (hempty : compatible ∅),
    LegalDiamonds compatible R → ∀ x : R.fibre (emptyConfiguration compatible hempty),
    ∃! f : ∀ C, R.fibre C,
      q.readout () (R.fibre (emptyConfiguration compatible hempty))
        (f (emptyConfiguration compatible hempty)) x ∧ StaticCompatible compatible R f

private theorem staticRejected : ¬ staticArena.{u,v}.Law rejected := by
  intro h
  let compatible : Finset (ULift.{u} Unit) → Prop := fun _ => True
  let R : LocalReadout compatible := {fibre := fun _ => ULift.{v} Unit,edge := fun _ _ _ _ _ x => x}
  have hd : LegalDiamonds compatible R := by
    intro C D a b ha hb hab hba he x
    have heq : b = a := Subsingleton.elim _ _
    subst b
    exact (hab.1 (Set.mem_insert a C.1)).elim
  obtain ⟨f,hf,_⟩ := h compatible R True.intro hd (ULift.up ())
  exact hf.1

def staticFamily : Registration staticArena.{u,v} (type_of% (@static_assignment_unique.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@static_assignment_unique,rejected,staticRejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,staticRejected⟩,fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨ULift.{v} Bool,ULift.up false,ULift.up true,?_⟩
    intro h
    have hh : (ULift.up false : ULift.{v} Bool) = ULift.up true := (congrFun h (ULift.up true)).mpr rfl
    have hh' := congrArg ULift.down hh
    cases hh'

def staticRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@static_assignment_unique.{u,v})
    (type_of% (realize signature.{v} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationReadout.static_assignment_unique.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationReadout.staticFamily
  realizationSource := none
  generated := false
  arena := .source ⟨staticArena⟩
  objectArena := .source ⟨staticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source staticArena ⟨staticFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms staticFamily
end Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
