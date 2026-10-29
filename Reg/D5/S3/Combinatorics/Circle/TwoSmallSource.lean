import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TwoSmallSource
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.TwoSmallSource

namespace Reg.D5.S3.Combinatorics.Circle.TwoSmallSource
universe u
noncomputable section

/-- The negated weight family observed by the lower prefix bound. -/
abbrev signature : Signature where
  Params := Σ α : Type u, α → ℤ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p i => -p.2 i) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Only the lower bound observes the selected negated weights; all hypotheses
and both upper bounds keep their original weight operands. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (f : α → ℤ) (C : ℤ) (L : List α)
    (hs : InStrip f C 0 L) (hm : (L.map f).sum = 0),
    ∃ j ≤ L.length, ∀ n : ℕ,
      0 ≤ (((L.rotate j).take n).map (R.readout () ⟨α, f⟩)).sum ∧
      (((L.rotate j).take n).map (fun x => -f x)).sum ≤ C ∧
      (((L.rotate j).take n).map (fun x => -f x)).sum ≤ ((L.take j).map f).sum

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs : InStrip (fun _ : ULift.{u} Unit => (0 : ℤ)) 0 0 [ULift.up ()] := by
    simp [InStrip]
  obtain ⟨j, _, hj⟩ := h (fun _ : ULift.{u} Unit => (0 : ℤ)) 0 [ULift.up ()] hs (by simp)
  have hh := (hj 1).1
  simpa [List.rotate_singleton, rejected, realize] using hh

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 2), fun x => (x.down.val : ℤ)⟩,
    ULift.up (0 : Fin 2), ULift.up (1 : Fin 2), ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena.{u}
    (type_of% (@negate_rotation_prefix_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@negate_rotation_prefix_bound.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Circle.TwoSmallSource.negate_rotation_prefix_bound.{u_1})
    (type_of% (realize signature.{u_1} (fun _ p i => -p.2 i) (fun e => nomatch e)))
    Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.TwoSmallSource.negate_rotation_prefix_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoSmallSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ p i => -p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.TwoSmallSource
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Circle.TwoSmallSource
