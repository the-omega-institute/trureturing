import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Registration for both actual readouts over the complete two-coordinate
telescope. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open _root_.D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
noncomputable section

abbrev Params := Σ _s : ℕ, ℕ
private def size (p : Params) : ℕ := 3*p.1+p.2
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
  Law R := ∀ (s t : ℕ) (_hs : 2 ≤ s) (_ht : 2 ≤ t),
    ∃ sigma : List (Fin (3*s+t)), ∃ cut : ℕ, cut ≤ 3*s+t ∧
      R.readout false ⟨s,t⟩ (1+2^s+2^(s+s)+2^(s+s+t)) sigma ∧
      R.readout true ⟨s,t⟩ (2*(1+2^s+2^(s+s)+2^(s+s+t)))
        (earWord (3*s+t) sigma cut)

private theorem actual_law : arena.Law actual := by
  intro s t hs ht
  exact actualSource_equal_first_two_last_joint_lift s t hs ht

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,hj,hold,_⟩ := h 2 2 (by decide) (by decide)
  exact hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,hj,hold,hnew⟩ := h 2 2 (by decide) (by decide)
  cases side
  · simpa [deleted,rejected,realize] using hold
  · simpa [deleted,rejected,realize] using hnew

private theorem bad_old : ¬ OriginalOrder 8 2 (List.finRange 8) := by
  intro h
  have hh := h.2.2 7
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hh

private theorem bad_new : ¬ OriginalOrder 9 2 (List.finRange 9) := by
  intro h
  have hh := h.2.2 8
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,2⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 8)
    change OriginalOrder 8 0 (List.finRange 8) = OriginalOrder 8 2 (List.finRange 8) at hp
    have hz : OriginalOrder 8 0 (List.finRange 8) := by
      have hf : actualSource 8 0 = fun _ => (0 : ℤ) := by
        funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
      have hz (xs : List (Fin 8)) : (xs.map (actualSource 8 0)).sum = 0 := by
        rw [hf]; induction xs <;> simp_all
      exact ⟨List.Perm.refl _,hz _,fun n => by rw [hz]; norm_num [modulus]⟩
    exact bad_old (hp.mp hz)
  · refine ⟨⟨2,2⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 9)
    change OriginalOrder 9 0 (List.finRange 9) = OriginalOrder 9 2 (List.finRange 9) at hp
    have hz : OriginalOrder 9 0 (List.finRange 9) := by
      have hf : actualSource 9 0 = fun _ => (0 : ℤ) := by
        funext i; fin_cases i <;> norm_num [actualSource,centered,modulus]
      have hz (xs : List (Fin 9)) : (xs.map (actualSource 9 0)).sum = 0 := by
        rw [hf]; induction xs <;> simp_all
      exact ⟨List.Perm.refl _,hz _,fun n => by rw [hz]; norm_num [modulus]⟩
    exact bad_new (hp.mp hz)

def source_registration : Registration arena (type_of% (@actualSource_equal_first_two_last_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side,?_,rfl,deleted_law side⟩
      intro j hj; simp [deleted,realize,hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.actualSource_equal_first_two_last_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.actualSource_equal_first_two_last_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body","arg","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","arg","body","arg","body","arg","fn","arg","fn","fn"]
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
end Reg.D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
