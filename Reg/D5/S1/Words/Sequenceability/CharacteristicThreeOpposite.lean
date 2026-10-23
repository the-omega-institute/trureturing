import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.Sequenceability.CharacteristicThreeOpposite
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The complete original telescope is retained; the interval sum is the observed state. -/

namespace Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOpposite

open Function Finset
open _root_.D5.S1.Words.Sequenceability.CharacteristicThreeOpposite
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

structure Inputs where
  A : Type u
  group : AddCommGroup A
  module : @Module (ZMod 3) A _ group.toAddCommMonoid
  finite : Finite A

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ P y => by letI := P.group; exact y ≠ 0) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.group
    letI := P.module
    letI := P.finite
    2 ≤ Module.finrank (ZMod 3) P.A → ∀ (x : P.A), x ≠ 0 →
    let M := 3 ^ Module.finrank (ZMod 3) P.A - 3
    ∃ w : ℕ → P.A,
      Injective (fun i : Fin M => w i.val) ∧
      Set.range (fun i : Fin M => w i.val) = {y | y ≠ 0 ∧ y ≠ x ∧ y ≠ -x} ∧
      Injective (fun k : Fin M => ∑ i ∈ range k.val, w i) ∧
      (∑ i ∈ range M, w i) = 0 ∧
      (∀ a b : ℕ, a < b → b ≤ M → (a ≠ 0 ∨ b ≠ M) →
        R.readout () P (∑ i ∈ Ico a b, w i))

abbrev sourceScope := type_of% (@exists_opposite_ordering.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    letI := P.group
    letI := P.module
    letI := P.finite
    exact @h P.A P.group P.module P.finite
  · intro h A group module finite
    exact h ⟨A, group, module, finite⟩

private theorem actual_law : arena.{u}.Law actual := source_bridge.mp (@exists_opposite_ordering.{u})

abbrev sample : Inputs.{u} where
  A := ULift.{u} (Fin 2 → ZMod 3)
  group := inferInstance
  module := inferInstance
  finite := inferInstance

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc : Module.finrank (ZMod 3) sample.A = 2 := by
    simp [sample, finrank_ulift, Module.finrank_fintype_fun_eq_card]
  have hd : 2 ≤ Module.finrank (ZMod 3) sample.A := hc.ge
  have hx : (1 : sample.A) ≠ 0 := one_ne_zero
  obtain ⟨w, _, _, _, _, hi⟩ := h sample hd 1 hx
  exact hi 0 1 (by decide)
    (by rw [hc]; decide) (Or.inr (by rw [hc]; decide))

noncomputable def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sample, 0, 1, ?_⟩
    intro he
    have hh : actual.readout i sample 1 := one_ne_zero
    rw [← he] at hh
    exact hh rfl

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_opposite_ordering.{u}) (Realization signature.{u}) (type_of% (@Ne.{u+1})) Unit where
  unitName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOpposite.unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOpposite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P y => by letI := P.group; exact y ≠ 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicThreeOpposite
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOpposite
