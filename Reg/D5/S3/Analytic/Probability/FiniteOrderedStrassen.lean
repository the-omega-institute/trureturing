import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.FiniteOrderedStrassen
import Reg.Support.DependentFamily

/-! Typed source-bound audit of the finite ordered Strassen theorem. -/

namespace Reg.D5.S3.Analytic.Probability.FiniteOrderedStrassen

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Probability.FiniteOrderedStrassen
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ left right => left ≤ right) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ left right => left < right) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {α : Type u} [Fintype α] [PartialOrder α]
    (p q : α → ℝ)
    (_hp_nonneg : ∀ x, 0 ≤ p x)
    (_hq_nonneg : ∀ x, 0 ≤ q x)
    (_hsum : ∑ x : α, p x = ∑ x : α, q x),
    (∀ U : Finset α, (∀ ⦃x y : α⦄, x ∈ U → x ≤ y → y ∈ U) →
      r.readout () () (∑ x ∈ U, p x) (∑ x ∈ U, q x)) ↔
    ∃ π : α → α → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∀ x, ∑ y : α, π x y = p x) ∧
      (∀ y, ∑ x : α, π x y = q y) ∧
      (∀ x y, ¬ x ≤ y → π x y = 0)

theorem source_bridge :
    (type_of% @forall_isUpperSet_sum_le_iff_exists_coupling.{u}) ↔
      arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp (@forall_isUpperSet_sum_le_iff_exists_coupling.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h (α := ULift.{u} Empty) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (by intro x; exact le_refl 0) (by intro x; exact le_refl 0) (by simp)
  have hright : ∃ π : ULift.{u} Empty → ULift.{u} Empty → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∀ x, ∑ y : ULift.{u} Empty, π x y = 0) ∧
      (∀ y, ∑ x : ULift.{u} Empty, π x y = 0) ∧
      (∀ x y, ¬ x ≤ y → π x y = 0) := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_, ?_⟩ <;> intro x
    · intro y; exact le_refl 0
    · exact Empty.elim x.down
    · exact Empty.elim x.down
    · intro y _; exact Empty.elim x.down
  have hleft := hbad.mpr hright
  have hcut := hleft (∅ : Finset (ULift.{u} Empty)) (by simp)
  norm_num [rejected, realize] at hcut

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration :
    Registration arena.{u} (type_of% @forall_isUpperSet_sum_le_iff_exists_coupling.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@forall_isUpperSet_sum_le_iff_exists_coupling.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.FiniteOrderedStrassen.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.FiniteOrderedStrassen.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left ≤ right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.FiniteOrderedStrassen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.Probability.FiniteOrderedStrassen
