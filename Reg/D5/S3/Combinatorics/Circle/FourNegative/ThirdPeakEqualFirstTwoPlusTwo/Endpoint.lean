import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
noncomputable section

abbrev Params := Σ _ : ℕ, ℕ
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (2*p.1+2*p.2+2)) → Prop
    | true => List (Fin (2*p.1+2*p.2+2+1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (2*p.1+2*p.2+2) seed
    | true => OriginalOrder (2*p.1+2*p.2+2+1) seed) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)
def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j=side then rejected.readout j p seed else actual.readout j p seed) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀
    (a d : ℕ) (ha : 2≤a) (had : a+2≤d),
    let k:=2*a+2*d+2
    let s:=1+2^a+2^(2*a)+2^(2*a+d+2)
    ∃ sigma : List (Fin k), ∃ j : ℕ,
      j<k ∧ (sigma.map Fin.val)[j]?=some (k-1) ∧
      ((earWord k sigma j).map Fin.val)[j]?=some k ∧
      ((earWord k sigma j).map Fin.val)[j+1]?=some (k-1) ∧
      R.readout false ⟨a,d⟩ s sigma ∧
      R.readout true ⟨a,d⟩ (2*s) (earWord k sigma j) ∧
      (sigma.map (fun p => actualSource (k+1) (2*s) p.castSucc)).sum=-(s:ℤ) ∧
      actualSource (k+1) (2*s) (Fin.last k)=(s:ℤ) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource k s)).sum∈Set.Icc (0:ℤ) (modulus k/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord k sigma j)).flatten).take n).map
        (actualSource (k+1) (2*s))).sum∈Set.Icc (0:ℤ) (modulus k)) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map (actualSource k s)).sum=0 ∧
        (((List.replicate m (earWord k sigma j)).flatten).map
          (actualSource (k+1) (2*s))).sum=0)

private theorem actual_law : arena.Law actual := by
  exact actualSource_third_peak_equal_first_two_plus_two_joint_lift
private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,_,_,_,_,hold,_⟩ := h 2 4 (by decide) (by decide)
  simp [rejected,realize] at hold
private theorem deleted_law (side : Bool) : ¬arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,_,_,_,_,hold,hnew,_⟩ := h 2 4 (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private def identityWord : List (Fin 14) := List.finRange 14
private theorem zero_old : OriginalOrder 14 0 identityWord := by
  have hf : actualSource 14 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨List.Perm.refl _,?_,?_⟩
  · simp [hf]
  · intro n
    simp [hf,modulus]
private theorem zero_new : OriginalOrder 15 0 (earWord 14 identityWord 0) := by
  have hf : actualSource 15 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨by decide,?_,?_⟩
  · simp [hf]
  · intro n
    simp [hf,modulus]
private theorem bad_old : ¬OriginalOrder 14 2 identityWord := by
  intro h
  have hh := h.2.2 13
  norm_num [identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem bad_new : ¬OriginalOrder 15 1 (earWord 14 identityWord 0) := by
  intro h
  have hh := h.2.2 1
  norm_num [earWord,identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,4⟩,0,2,?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 14 0 identityWord=OriginalOrder 14 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2,4⟩,0,1,?_⟩
    intro he
    have hp := congrFun he (earWord 14 identityWord 0)
    change OriginalOrder 15 0 (earWord 14 identityWord 0)=
      OriginalOrder 15 1 (earWord 14 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_third_peak_equal_first_two_plus_two_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side,?_,rfl,deleted_law side⟩
      intro j hj
      simp [deleted,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.actualSource_third_peak_equal_first_two_plus_two_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.actualSource_third_peak_equal_first_two_plus_two_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Endpoint.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Endpoint
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Endpoint
