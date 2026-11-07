import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Reconstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer (degree place seed base)
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
  (primitive phaseWeight source_eq_scale_primitive)
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer (aa)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private primitive_place
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Reconstruction
universe u

abbrev signature : Signature where
  Params := Σ A : Type u, Σ r : ℕ, Fin (3*degree r) → A
  State p := Fin (3*degree p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p i => p.2.2 i) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => p.2.2 (place 0 ⟨0,by dsimp [degree]; omega⟩))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [g : AddCommGroup A] (r : ℕ)
    (X : Fin (3*degree r) → A) (hX : SelectedAnnihilates r X) (i : Fin (3*degree r)),
    R.readout () ⟨A,r,X⟩ i=primitive r i •
      ((-3 : ℤ) • X (place 0 ⟨0,by dsimp [degree]; omega⟩)+
        (2 : ℤ) • X (place 2 ⟨0,by dsimp [degree]; omega⟩))

private def source0 (i : Fin (3*degree 0)) : ℤ :=
  _root_.D5.S3.Combinatorics.Circle.SourceWidth.actualSource (3*degree 0) (seed 0) i
private def i0 : Fin (3*degree 0) := place 0 ⟨0,by decide⟩
private def i1 : Fin (3*degree 0) := place 0 ⟨1,by decide⟩

private theorem lifted_annihilates : SelectedAnnihilates 0
    (fun i => (ULift.up (source0 i) : ULift.{u} ℤ)) := by
  intro k
  have hs : (∑ i ∈ selectedMask 0 k, source0 i)=0 := selected_literal_zero 0 k
  change (∑ i ∈ selectedMask 0 k,
    (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm (source0 i))=0
  rw [← map_sum,hs,map_zero]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let X : Fin (3*degree 0) → ULift.{u} ℤ := fun i => ULift.up (source0 i)
  have hx : SelectedAnnihilates 0 X := lifted_annihilates
  have he := h (A := ULift.{u} ℤ) 0 X hx i1
  change X i0=primitive 0 i1 • _ at he
  rw [← actual_selected_upper_reconstruction 0 X hx i1] at he
  have hv := congrArg ULift.down he
  change source0 i0=source0 i1 at hv
  dsimp only [source0,i0,i1] at hv
  rw [source_eq_scale_primitive,source_eq_scale_primitive,primitive_place,primitive_place] at hv
  norm_num [phaseWeight,aa,base,degree] at hv

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} ℤ,0,fun i => ULift.up (i.val : ℤ)⟩,i0,i1,?_⟩
  intro he
  have hv := congrArg ULift.down he
  norm_num [actual,realize,i0,i1,place,degree] at hv

def reconstruction_family : Registration arena.{u}
    (type_of% (@actual_selected_upper_reconstruction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_selected_upper_reconstruction.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def reconstruction_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_selected_upper_reconstruction.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.actual_selected_upper_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Reconstruction.reconstruction_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨reconstruction_family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Reconstruction
    definition := none
    coordinates := #[0,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Reconstruction
