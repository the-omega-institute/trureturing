import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! # Full-telescope source-bound audits of physical permutation rigidity -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer (degree seed place)
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
  (UpperIndex selectedMask terminalMask)
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
  (actual_selected_image_zero_perm_iff actual_zero_family_perm_iff)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private triple
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
namespace Selected
abbrev signature : Signature where
  Params := Σ r : ℕ, Equiv.Perm (Fin (3*(18*r+12)))
  State q := UpperIndex q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q k =>
    ∑ i ∈ (selectedMask q.1 k).image q.2,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (p : Equiv.Perm (Fin (3*(18*r+12)))),
    (∀ k : UpperIndex r, R.readout () ⟨r,p⟩ k=0) ↔ p=1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 1).mpr rfl (Sum.inr (Sum.inr (Sum.inr 0)))
  norm_num [rejected,realize] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0,Equiv.swap (⟨0,by decide⟩ : Fin 36) ⟨1,by decide⟩⟩,
    Sum.inr (Sum.inr (Sum.inr 0)), Sum.inr (Sum.inr (Sum.inr 2)),?_⟩
  norm_num [actual,realize,selectedMask,terminalMask,triple,place,degree,
    Finset.image_insert,Finset.image_empty,Equiv.swap_apply_def,
    actualSource,centered,modulus]
def family : Registration arena (type_of% (@actual_selected_image_zero_perm_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_selected_image_zero_perm_iff,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_selected_image_zero_perm_iff) (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.actual_selected_image_zero_perm_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.Selected.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q k =>
    ∑ i ∈ (selectedMask q.1 k).image q.2,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","fn","arg","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Selected
namespace Full
abbrev signature : Signature where
  Params := Σ r : ℕ, Equiv.Perm (Fin (3*(18*r+12)))
  State q := Finset (Fin (3*(18*q.1+12)))
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role q A => if !role then
    ∑ i ∈ A.image q.2,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i
    else ∑ i ∈ A,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i)
    (fun e => nomatch e)
def rejected (role : Bool) : Realization signature :=
  realize signature (fun j q A => if j=role then 1 else actual.readout j q A)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (p : Equiv.Perm (Fin (3*(18*r+12)))),
    (∀ A : Finset (Fin (3*(18*r+12))),
      R.readout false ⟨r,p⟩ A=0 ↔ R.readout true ⟨r,p⟩ A=0) ↔ p=1
private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have he := (h 0 1).mpr rfl ∅
  cases role <;> norm_num [rejected,actual,realize] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩,∅,{⟨0,by decide⟩},?_⟩
  cases i <;> simp [actual,realize] <;> norm_num [actualSource,centered,modulus]
def family : Registration arena (type_of% (@actual_zero_family_perm_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_family_perm_iff,rejected true,rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_law i⟩
      intro j hji
      simp only [rejected,realize,ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_zero_family_perm_iff) (Realization signature) Nat Bool where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.actual_zero_family_perm_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.Full.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun role q A => if !role then
    ∑ i ∈ A.image q.2,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i
    else ∑ i ∈ A,
      actualSource (3*(18*q.1+12))
        ((2^(18*q.1+12)-1)*(2^((18*q.1+12)+1)-3)) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","fn","arg","body","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","fn","arg","body","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Full
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
