import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.WeavingDiagramPorts

/-! The observation is the full port-code map on every admissible diagram.
The full source telescope and family interventions are retained.
Exact occurrence selection and current declared binding remain separate obligations. -/

set_option autoImplicit false
namespace Reg.D5.S3.Topology.WeavingDiagramPorts
open _root_.D5.S3.Topology.WeavingDiagramPorts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev sourceScope := type_of% (@reach_iff_code)

structure Inputs where
  diagram : Parameters
  parity : ℕ
  parity_lt : parity < 2

abbrev maps (P : Inputs) := Dart P.diagram → ℕ × ZMod P.diagram.m

abbrev signature : Signature where
  Params := Inputs
  State := maps
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => maps
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ P : Inputs, ∀ x y : Dart P.diagram,
    Reach P.diagram P.parity x y ↔
      R.readout () P (code P.diagram P.parity) x =
        R.readout () P (code P.diagram P.parity) y

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h P x y
    exact h P.diagram P.parity P.parity_lt x y
  · intro h P p hp x y
    exact h ⟨P,p,hp⟩ x y

theorem actual_positive : arena.Law actual := source_bridge.mp reach_iff_code


private def witness : Inputs := ⟨⟨2,3,by decide,by decide⟩,0,by decide⟩

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => (0,0)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h witness (0,⟨0,by decide⟩,.bl) (1,⟨0,by decide⟩,.bl)).mpr rfl
  have he := (reach_iff_code witness.diagram 0 (by decide) _ _).mp hh
  have ht := congrArg Prod.snd he
  change (0 : ZMod 3) = 1 at ht
  exact (by decide : (0 : ZMod 3) ≠ 1) ht

noncomputable def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    refine ⟨witness,code witness.diagram witness.parity,(fun _ => (0,0)),?_⟩
    intro h
    have hh := congrArg (fun f => (f (0,⟨0,by decide⟩,.bl)).1) h
    change (1 : ℕ) = 0 at hh
    omega

noncomputable def reachRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@reach_iff_code) (Realization signature) Type Unit where
  unitName := `D5.S3.Topology.WeavingDiagramPorts.reach_iff_code.__information_unit
  realizationName := `Reg.D5.S3.Topology.WeavingDiagramPorts.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Sigma maps)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_bridge
#print axioms actual_positive
#print axioms familyRegistration
#print axioms reachRegistration
end Reg.D5.S3.Topology.WeavingDiagramPorts
