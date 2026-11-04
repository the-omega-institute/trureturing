import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The full three-parameter tied-maximum telescope, both original orders, every repeated prefix and both zero totals. Source only; no compilation or audit identity is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
noncomputable section

abbrev Params := Σ _a : ℕ, Σ _b : ℕ, ℕ
private def size (p : Params) : ℕ := p.1+p.2.1+p.2.2+p.2.2
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (size p)) → Prop
    | true => List (Fin (size p + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (size p) seed
    | true => OriginalOrder (size p + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j = side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b s : ℕ) (_ha : 2≤a) (_hb : 2≤b) (_hs : max a b≤s),
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      R.readout false ⟨a,b,s⟩ (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      R.readout true ⟨a,b,s⟩ (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum ∈
        Set.Icc (0 : ℤ) (modulus (a+b+s+s)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).take n).map
        (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum ∈
        Set.Icc (0 : ℤ) (modulus (a+b+s+s))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).map
          (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum=0)

private theorem actual_law : arena.Law actual := by
  exact actualSource_last_two_maximum_joint_lift

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,_,hold,_⟩ := h 2 2 2 (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,_,hold,hnew,_⟩ := h 2 2 2 (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private theorem bad_old : ¬ OriginalOrder 3 2 (List.finRange 3) := by
  intro h
  have hh := h.2.2 2
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 4 2 (List.finRange 4) := by
  intro h
  have hh := h.2.2 3
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨1,0,1⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he (List.finRange 3)
    change OriginalOrder 3 0 (List.finRange 3) = OriginalOrder 3 2 (List.finRange 3) at hp
    have hz : OriginalOrder 3 0 (List.finRange 3) := by
      have hf : actualSource 3 0 = fun _ => (0 : ℤ) := by
        funext i
        fin_cases i <;> norm_num [actualSource, centered, modulus]
      have hz (xs : List (Fin 3)) : (xs.map (actualSource 3 0)).sum = 0 := by
        rw [hf]
        induction xs <;> simp_all
      refine ⟨List.Perm.refl _, hz _, ?_⟩
      intro n
      rw [hz]
      norm_num [modulus]
    exact bad_old (hp.mp hz)
  · refine ⟨⟨1,0,1⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he (List.finRange 4)
    change OriginalOrder 4 0 (List.finRange 4) = OriginalOrder 4 2 (List.finRange 4) at hp
    have hz : OriginalOrder 4 0 (List.finRange 4) := by
      have hf : actualSource 4 0 = fun _ => (0 : ℤ) := by
        funext i
        fin_cases i <;> norm_num [actualSource, centered, modulus]
      have hz (xs : List (Fin 4)) : (xs.map (actualSource 4 0)).sum = 0 := by
        rw [hf]
        induction xs <;> simp_all
      refine ⟨List.Perm.refl _, hz _, ?_⟩
      intro n
      rw [hz]
      norm_num [modulus]
    exact bad_new (hp.mp hz)

def source_registration : Registration arena
    (type_of% (@actualSource_last_two_maximum_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side, ?_, rfl, deleted_law side⟩
      intro j hj; simp [deleted, realize, hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.actualSource_last_two_maximum_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.actualSource_last_two_maximum_joint_lift.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Endpoint.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Endpoint
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","fn","arg","fn"]
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
end Reg.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Endpoint
