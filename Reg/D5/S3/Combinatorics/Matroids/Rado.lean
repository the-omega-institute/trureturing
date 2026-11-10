import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.Rado

namespace Reg.D5.S3.Combinatorics.Matroids.Rado

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.Rado
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Type v
  State E := Matroid E
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output b E := if b then Set E → Prop else Set E → ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun b _ M => match b with
    | false => M.eRk
    | true => M.Indep) (fun e => nomatch e)

def rejected (i : Bool) : Realization signature.{v} :=
  realize signature (fun b _ M => match b with
    | false => if i = false then fun _ => 0 else M.eRk
    | true => if i = true then fun _ => False else M.Indep) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {I : Type u} {E : Type v} [Finite I] [Finite E] {M : Matroid E}
    (A : I → Set E),
    (∃ f : I → E, Function.Injective f ∧ (∀ i, f i ∈ A i) ∧
      r.readout true E M (Set.range f)) ↔
    ∀ J : Finset I, (J.card : ℕ∞) ≤ r.readout false E M (⋃ i ∈ J, A i)

private theorem rejected_law (i : Bool) : ¬ arena.{u,v}.Law (rejected i) := by
  classical
  intro h
  cases i with
  | false =>
    have hh := h (I := ULift.{u} Unit) (E := ULift.{v} Unit)
      (M := freeOn Set.univ) (fun _ => Set.univ)
    have hl : ∃ f : ULift.{u} Unit → ULift.{v} Unit,
        Function.Injective f ∧ (∀ i, f i ∈ (Set.univ : Set (ULift.{v} Unit))) ∧
        (rejected false).readout true (ULift.{v} Unit) (freeOn Set.univ) (Set.range f) := by
      refine ⟨fun _ => ULift.up (), Function.injective_of_subsingleton _, ?_, ?_⟩
      · simp
      · simp [rejected, realize]
    have hz := hh.mp hl {ULift.up ()}
    norm_num [rejected, realize] at hz
  | true =>
    have hh := h (I := PEmpty.{u+1}) (E := PEmpty.{v+1})
      (M := loopyOn ∅) (fun e => nomatch e)
    have hr : ∀ J : Finset PEmpty.{u+1}, (J.card : ℕ∞) ≤
        (rejected true).readout false PEmpty.{v+1} (loopyOn ∅) (⋃ i ∈ J, (fun e => nomatch e) i) := by
      intro J
      have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
      subst J
      simp
    obtain ⟨f, _, _, hf⟩ := hh.mpr hr
    exact hf

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  cases i with
  | false =>
    refine ⟨ULift.{v} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
    intro h
    have hh := congrFun h ({ULift.up ()} : Set (ULift.{v} Unit))
    change (loopyOn {ULift.up ()}).eRk {ULift.up ()} =
      (freeOn {ULift.up ()}).eRk {ULift.up ()} at hh
    rw [eRk_loopyOn, eRk_freeOn subset_rfl, encard_singleton] at hh
    exact zero_ne_one hh
  | true =>
    refine ⟨ULift.{v} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
    intro h
    have hh := congrFun h ({ULift.up ()} : Set (ULift.{v} Unit))
    change (loopyOn {ULift.up ()}).Indep {ULift.up ()} =
      (freeOn {ULift.up ()}).Indep {ULift.up ()} at hh
    have hf : (freeOn ({ULift.up ()} : Set (ULift.{v} Unit))).Indep {ULift.up ()} := by simp
    rw [← hh] at hf
    simp at hf

def source_registration : Registration arena.{u,v}
    (type_of% (@rado_independent_transversal.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rado_independent_transversal, rejected true, rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      cases i <;> cases j <;> simp_all [actual, rejected, realize]
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@rado_independent_transversal.{u,v}) (Realization signature.{v}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.Rado.rado_independent_transversal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.Rado.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.Rado
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "arg", "arg", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Matroids.Rado
