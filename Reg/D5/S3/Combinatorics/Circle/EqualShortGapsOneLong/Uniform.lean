import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Uniform
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! All three unbounded parameters and the identical explicit physical word. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Uniform
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
noncomputable section

abbrev Params := Σ _a : ℕ, Σ _p : ℕ, ℕ

private def dimension (x : Params) : ℕ := size x.1 x.2.1 x.2.2

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side x := match side with
    | false => List (Fin (dimension x)) → Prop
    | true => List (Fin (dimension x + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side x seed => match side with
    | false => OriginalOrder (dimension x) seed
    | true => OriginalOrder (dimension x + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j x seed =>
    if j = side then rejected.readout j x seed else actual.readout j x seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d),
    R.readout false ⟨a, p, d⟩ (geom a p)
      (physicalWord a p d (by dsimp [size]; omega)) ∧
    R.readout true ⟨a, p, d⟩ (2 * geom a p)
      (earWord (size a p d)
        (physicalWord a p d (by dsimp [size]; omega)) (cut a p d))

private theorem actual_law : arena.Law actual := by
  intro a p d ha hp hd
  exact actualSource_uniform_one_long_joint a p d ha hp hd

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 1 2 (by decide) (by decide) (by decide)).1
  simp [rejected, realize] at hh

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  have hh := h 2 1 2 (by decide) (by decide) (by decide)
  cases side
  · have hold := hh.1
    simp [deleted, rejected, realize] at hold
  · have hnew := hh.2
    simp [deleted, rejected, realize] at hnew

private theorem bad_old : ¬ OriginalOrder 4 2 (List.finRange 4) := by
  intro h
  have hh := h.2.2 3
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 5 2 (List.finRange 5) := by
  intro h
  have hh := h.2.2 4
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 1, 4⟩, 0, 2, ?_⟩
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
    exact bad_old (hp.mp hz)
  · refine ⟨⟨2, 1, 4⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he (List.finRange 5)
    change OriginalOrder 5 0 (List.finRange 5) = OriginalOrder 5 2 (List.finRange 5) at hp
    have hz : OriginalOrder 5 0 (List.finRange 5) := by
      have hf : actualSource 5 0 = fun _ => (0 : ℤ) := by
        funext i
        fin_cases i <;> norm_num [actualSource, centered, modulus]
      have hz (xs : List (Fin 5)) : (xs.map (actualSource 5 0)).sum = 0 := by
        rw [hf]
        induction xs <;> simp_all
      refine ⟨List.Perm.refl _, hz _, ?_⟩
      intro n
      rw [hz]
      norm_num [modulus]
    exact bad_new (hp.mp hz)

def source_registration : Registration arena
    (type_of% (@actualSource_uniform_one_long_joint)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side, ?_, rfl, deleted_law side⟩
      intro j hj
      simp [deleted, realize, hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.actualSource_uniform_one_long_joint)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.actualSource_uniform_one_long_joint.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Uniform.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Uniform
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Uniform
