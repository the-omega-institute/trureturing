import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The complete original telescope is retained; the interval sum is the observed state. -/

namespace Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOrdering

open Function Finset
open _root_.D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

structure Inputs where
  K : Type u
  A : Type v
  field : Field K
  fintype : Fintype K
  char : @CharP K field.toAddMonoidWithOne 3
  group : AddCommGroup A

abbrev signature : Signature where
  Params := Inputs.{u,v}
  State P := P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize signature
  (fun _ P y => by letI := P.group; exact y ≠ 0) (fun e => nomatch e)

def rejected : Realization signature.{u,v} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ P : Inputs.{u,v},
    letI := P.field
    letI := P.fintype
    letI := P.char
    letI := P.group
    ∀ (φ : P.K × ZMod 3 ≃+ P.A) (x : P.A), φ (0, 1) = x →
    let M := 3 * (Fintype.card P.K - 1)
    ∃ w : ℕ → P.A,
      Injective (fun i : Fin M => w i.val) ∧
      Set.range (fun i : Fin M => w i.val) = {y | y ≠ 0 ∧ y ≠ x ∧ y ≠ -x} ∧
      Injective (fun k : Fin M => ∑ i ∈ range k.val, w i) ∧
      (∑ i ∈ range M, w i) = 0 ∧
      (∀ a b : ℕ, a < b → b ≤ M → (a ≠ 0 ∨ b ≠ M) →
        R.readout () P (∑ i ∈ Ico a b, w i))

abbrev sourceScope := type_of% (@exists_transported_ordering.{u,v})

private theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h P
    letI := P.field
    letI := P.fintype
    letI := P.char
    letI := P.group
    exact @h P.K P.A P.field P.fintype P.char P.group
  · intro h K A field fintype char group
    exact h ⟨K, A, field, fintype, char, group⟩

private theorem actual_law : arena.{u,v}.Law actual := source_bridge.mp (@exists_transported_ordering.{u,v})

abbrev sample : Inputs.{u,v} where
  K := ULift.{u} (ZMod 3)
  A := ULift.{v} (ZMod 3 × ZMod 3)
  field := inferInstance
  fintype := inferInstance
  char := inferInstance
  group := inferInstance

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let φ : (sample.{u,v}).K × ZMod 3 ≃+ (sample.{u,v}).A := {
    toFun := fun z => ⟨(z.1.down, z.2)⟩
    invFun := fun z => (⟨z.down.1⟩, z.down.2)
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    map_add' := by intro z t; rfl }
  obtain ⟨w, _, _, _, _, hi⟩ := h (sample.{u,v}) φ (φ (0, 1)) rfl
  have hc : Fintype.card (sample.{u,v}).K = 3 := by
    change Fintype.card (ULift.{u} (ZMod 3)) = 3
    simp only [Fintype.card_ulift, ZMod.card]
  exact hi 0 1 (by decide) (by rw [hc]; decide) (Or.inr (by rw [hc]; decide))

noncomputable def family : Registration arena.{u,v} sourceScope.{u,v} where
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
    refine ⟨(sample.{u,v}), 0, 1, ?_⟩
    intro he
    have hh : actual.readout i (sample.{u,v}) 1 := one_ne_zero
    rw [← he] at hh
    exact hh rfl

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_transported_ordering.{u,v}) (Realization signature.{u,v}) (type_of% (@Ne.{v+1})) Unit where
  unitName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOrdering.unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOrdering.family
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
    owner := `D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
    definition := none
    coordinates := #[0, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "body", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
