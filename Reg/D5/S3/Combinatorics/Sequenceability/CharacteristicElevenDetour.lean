import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! The entire original telescope is reconstructed; interval nonvanishing
is the observed predicate on the actual full vector interval sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour

open _root_.D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

universe u

structure Inputs where
  K : Type u
  field : Field K
  finite : Finite K
  characteristic : @CharP K field.toAddMonoidWithOne 11

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := ZMod 11 × P.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ P y => by letI := P.field; exact y ≠ 0) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.field
    letI := P.finite
    letI := P.characteristic
    ∀ (u : P.K), u ≠ 0 →
    let M := 10 * Nat.card P.K + 1
    ∃ v : ℕ → ZMod 11 × P.K,
      v 0 = (0, 0) ∧ v M = (0, u) ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
        ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        R.readout () P (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i))) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u)

abbrev sourceScope := type_of% (@exists_characteristic_eleven_relative_path.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    letI := P.field
    letI := P.finite
    letI := P.characteristic
    exact @h P.K P.field P.finite P.characteristic
  · intro h K field finite characteristic
    exact h ⟨K, field, finite, characteristic⟩

private theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp (@exists_characteristic_eleven_relative_path.{u})

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev sample : Inputs.{u} where
  K := ULift.{u} (ZMod 11)
  field := inferInstance
  finite := inferInstance
  characteristic := inferInstance

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨v, _, _, _, _, _, _, hi, _⟩ := h sample 1 one_ne_zero
  exact hi 0 1 (by decide) (by omega)

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
    refine ⟨sample, (0, 0), (1, 0), ?_⟩
    intro he
    have hh : actual.readout i sample (1, 0) := by
      intro h
      exact one_ne_zero (congrArg Prod.fst h)
    rw [← he] at hh
    exact hh rfl

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_eleven_relative_path.{u}) (Realization signature.{u})
    (type_of% (@Ne.{u+1})) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour.unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour.family
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
    (fun _ P y => by letI := P.field; exact y ≠ 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour
