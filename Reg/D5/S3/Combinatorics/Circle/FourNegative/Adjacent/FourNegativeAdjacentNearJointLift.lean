import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Both original centered-source readouts over the full two-coordinate telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
noncomputable section

abbrev Params := Σ _ : ℕ, ℕ
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (2*p.1+2*p.2)) → Prop
    | true => List (Fin (2*p.1+2*p.2+1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (2*p.1+2*p.2) seed
    | true => OriginalOrder (2*p.1+2*p.2+1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed => if j=side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s : ℕ) (_hr : 2≤r) (_hs : 2≤s) (_hnear : r≤s+1 ∧ s≤r+1),
    ∃ sigma : List (Fin (2*r+2*s)), ∃ j : ℕ, j≤2*r+2*s ∧
      R.readout false ⟨r,s⟩ (1+2^r+2^(2*r)+2^(2*r+s)) sigma ∧
      R.readout true ⟨r,s⟩ (2*(1+2^r+2^(2*r)+2^(2*r+s)))
        (earWord (2*r+2*s) sigma j)

private theorem actual_law : arena.Law actual := by
  intro r s hr hs hnear
  exact actualSource_four_negative_adjacent_near_joint_lift r s hr hs hnear

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,hj,hold,hnew⟩ := h 2 2 (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,hj,hold,hnew⟩ := h 2 2 (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private def identityWord : List (Fin 8) := List.finRange 8
private theorem zero_old : OriginalOrder 8 0 identityWord := by
  have hf : actualSource 8 0 = fun _ => (0 : ℤ) := by
    funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨List.Perm.refl _,?_,?_⟩
  · simp [hf]
  · intro n; simp [hf,modulus]
private theorem zero_new : OriginalOrder 9 0 (earWord 8 identityWord 0) := by
  have hf : actualSource 9 0 = fun _ => (0 : ℤ) := by
    funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨by decide,?_,?_⟩
  · simp [hf]
  · intro n; simp [hf,modulus]
private theorem bad_old : ¬ OriginalOrder 8 2 identityWord := by
  intro h; have hh := h.2.2 7
  norm_num [identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem bad_new : ¬ OriginalOrder 9 1 (earWord 8 identityWord 0) := by
  intro h; have hh := h.2.2 1
  norm_num [earWord,identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,2⟩,0,2,?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 8 0 identityWord = OriginalOrder 8 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2,2⟩,0,1,?_⟩
    intro he
    have hp := congrFun he (earWord 8 identityWord 0)
    change OriginalOrder 9 0 (earWord 8 identityWord 0) = OriginalOrder 9 1 (earWord 8 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_four_negative_adjacent_near_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side,?_,rfl,deleted_law side⟩
      intro j hj
      simp [deleted,realize,hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift.actualSource_four_negative_adjacent_near_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift.actualSource_four_negative_adjacent_near_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","body","arg","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","arg","body","arg","body","arg","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
