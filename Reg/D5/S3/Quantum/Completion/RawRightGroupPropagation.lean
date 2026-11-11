import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawRightGroupPropagation

/-! Full original source telescopes with an enrolled dependent equality readout. -/
namespace Reg.D5.S3.Quantum.Completion.RawRightGroupPropagation
open _root_.D5.S3.Quantum.Completion.RawRightGroupPropagation
open _root_.D5.S3.Quantum.Completion.RawUnanchoredReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

private theorem zero_raw {A : Type*} [MulOneClass A] :
    RawCost (id : A → A) (fun _ _ => (0 : ℝ)) := by
  constructor <;> intros <;> norm_num

private def trivialLabels : LabelGroup (id : ULift.{u} Unit → ULift.{u} Unit)
    (ULift.{v} Unit) where
  label := ⟨fun _ => 1, fun _ _ _ => Subsingleton.elim _ _⟩
  map_one := rfl
  map_mul := fun _ _ => Subsingleton.elim _ _
  marker := id
  map_marker := fun _ => rfl
  assoc := fun _ _ _ => Subsingleton.elim _ _

def rightArena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} [MulOneClass M] {G : Type v} [Group G]
    {U : M → M} {c : M → M → ℝ}, RawCost U c →
      ∀ (L : LabelGroup U G) (a b : M) (g : G),
        R.readout () () (c (a * L.label g) (b * L.label g)) (c a b)

private theorem right_rejected : ¬ rightArena.{u,v}.Law rejected := by
  intro h
  exact h zero_raw trivialLabels 1 1 1

def right_source : Registration rightArena.{u,v} (type_of% @right_invariant.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@right_invariant.{u,v}, rejected, right_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity rightArena.Law actual rejected right_rejected
  dependence := dependence

def independentArena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} [MulOneClass M] {G : Type v} [Group G]
    {U : M → M} {c : M → M → ℝ}, ∀ (h : RawCost U c) (L : LabelGroup U G)
      (a b : M) (z w : zeroSubgroup h L),
        R.readout () () (c (a * L.label (z : G)) (b * L.label (w : G))) (c a b)

private theorem independent_rejected : ¬ independentArena.{u,v}.Law rejected := by
  intro h
  exact h zero_raw trivialLabels 1 1 1 1

def independent_source : Registration independentArena.{u,v}
    (type_of% @independent_zero_tails.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@independent_zero_tails.{u,v}, rejected, independent_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity independentArena.Law actual rejected independent_rejected
  dependence := dependence

def right_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@right_invariant.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawRightGroupPropagation.right_invariant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawRightGroupPropagation.right_source
  realizationSource := none
  generated := false
  arena := .source ⟨rightArena⟩
  objectArena := .source ⟨rightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rightArena ⟨right_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def independent_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@independent_zero_tails.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawRightGroupPropagation.independent_zero_tails.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawRightGroupPropagation.independent_source
  realizationSource := none
  generated := false
  arena := .source ⟨independentArena⟩
  objectArena := .source ⟨independentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source independentArena ⟨independent_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawRightGroupPropagation
