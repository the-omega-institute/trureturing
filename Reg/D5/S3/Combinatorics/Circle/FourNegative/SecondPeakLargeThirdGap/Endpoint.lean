import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
noncomputable section

abbrev Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (p.1+p.2.1+p.2.2.1+p.2.2.2)) → Prop
    | true => List (Fin (p.1+p.2.1+p.2.2.1+p.2.2.2+1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (p.1+p.2.1+p.2.2.1+p.2.2.2) seed
    | true => OriginalOrder (p.1+p.2.1+p.2.2.1+p.2.2.2+1) seed) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)
def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j=side then rejected.readout j p seed else actual.readout j p seed) (fun e => nomatch e)

/-- The whole original eight-binder family, with its two dependent physical readouts. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_ha : 2≤a) (_had : a+1≤d)
      (_hdc : a+d+1≤c) (_hcb : c+1≤b),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,
      j≤a+b+c+d ∧
      R.readout false ⟨a,b,c,d⟩ (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      R.readout true ⟨a,b,c,d⟩ (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j)

private theorem actual_law : arena.Law actual := by
  exact actualSource_second_peak_large_third_gap_joint_lift
private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,_,hold,_⟩ := h 2 7 6 3 (by decide) (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold
private theorem deleted_law (side : Bool) : ¬arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,_,hold,hnew⟩ := h 2 7 6 3 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private def identityWord : List (Fin 18) := List.finRange 18
private theorem zero_old : OriginalOrder 18 0 identityWord := by
  have hf : actualSource 18 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨List.Perm.refl _,?_,?_⟩
  · simp [hf]
  · intro n
    simp [hf,modulus]
private theorem zero_new : OriginalOrder 19 0 (earWord 18 identityWord 0) := by
  have hf : actualSource 19 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨by decide,?_,?_⟩
  · simp [hf]
  · intro n
    simp [hf,modulus]
private theorem bad_old : ¬OriginalOrder 18 2 identityWord := by
  intro h
  have hh := h.2.2 17
  norm_num [identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem bad_new : ¬OriginalOrder 19 1 (earWord 18 identityWord 0) := by
  intro h
  have hh := h.2.2 1
  norm_num [earWord,identityWord,List.finRange_succ,actualSource,centered,modulus] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,7,6,3⟩,0,2,?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 18 0 identityWord=OriginalOrder 18 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2,7,6,3⟩,0,1,?_⟩
    intro he
    have hp := congrFun he (earWord 18 identityWord 0)
    change OriginalOrder 19 0 (earWord 18 identityWord 0)=
      OriginalOrder 19 1 (earWord 18 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_second_peak_large_third_gap_joint_lift)) where
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
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.actualSource_second_peak_large_third_gap_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.actualSource_second_peak_large_third_gap_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Endpoint.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Endpoint
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Endpoint
