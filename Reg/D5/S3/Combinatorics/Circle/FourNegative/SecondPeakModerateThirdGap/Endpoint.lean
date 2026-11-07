import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
noncomputable section

abbrev Params := Σ _a : ℕ, Σ _b : ℕ, Σ _c : ℕ, ℕ
private def size (p : Params) : ℕ := p.1+p.2.1+p.2.2.1+p.2.2.2

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (size p)) → Prop
    | true => List (Fin (size p+1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (size p) seed
    | true => OriginalOrder (size p+1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j=side then rejected.readout j p seed else actual.readout j p seed) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_ha : 2≤a) (_had : a<d) (_hdc : d<c)
      (_hcb : c<b) (_hmoder : c≤a+d),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      R.readout false ⟨a,b,c,d⟩
        (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      R.readout true ⟨a,b,c,d⟩
        (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ,
        (((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
          Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ,
        (((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
          (actualSource (a+b+c+d+1)
            (2*(1+2^a+2^(a+b)+2^(a+b+c)))))).sum ∈
          Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1)
            (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0)

private theorem actual_law : arena.Law actual := by
  intro a b c d ha had hdc hcb hmoder
  exact actualSource_second_peak_moderate_third_gap_joint_lift a b c d ha had hdc hcb hmoder

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,_,hold,_⟩ := h 2 5 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [rejected,realize] using hold

private theorem deleted_law (side : Bool) : ¬arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,_,hold,hnew,_⟩ := h 2 5 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  cases side
  · simpa [deleted,rejected,realize] using hold
  · simpa [deleted,rejected,realize] using hnew

private theorem bad_old : ¬OriginalOrder 14 2 (List.finRange 14) := by
  intro h
  have hh := h.2.2 13
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hh

private theorem bad_new : ¬OriginalOrder 15 2 (List.finRange 15) := by
  intro h
  have hh := h.2.2 14
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,5,4,3⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 14)
    change OriginalOrder 14 0 (List.finRange 14)=OriginalOrder 14 2 (List.finRange 14) at hp
    have hz : OriginalOrder 14 0 (List.finRange 14) := by
      have hf : actualSource 14 0=fun _ => (0:ℤ) := by
        funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
      refine ⟨List.Perm.refl _,?_,?_⟩
      · simp [hf]
      · intro n; simp [hf,modulus]
    exact bad_old (hp.mp hz)
  · refine ⟨⟨2,5,4,3⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 15)
    change OriginalOrder 15 0 (List.finRange 15)=
      OriginalOrder 15 2 (List.finRange 15) at hp
    have hz : OriginalOrder 15 0 (List.finRange 15) := by
      have hf : actualSource 15 0=fun _ => (0:ℤ) := by
        funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
      refine ⟨List.Perm.refl _,?_,?_⟩
      · simp [hf]
      · intro n; simp [hf,modulus]
    exact bad_new (hp.mp hz)

def source_registration : Registration arena
    (type_of% (@actualSource_second_peak_moderate_third_gap_joint_lift)) where
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
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.actualSource_second_peak_moderate_third_gap_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.actualSource_second_peak_moderate_third_gap_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Endpoint.source_registration
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Endpoint
