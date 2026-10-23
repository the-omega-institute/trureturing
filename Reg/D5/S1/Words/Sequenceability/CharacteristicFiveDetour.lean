import D5.S1.Words.Sequenceability.CharacteristicFiveDetour
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.CharacteristicFiveDetour

open _root_.D5.S1.Words.Sequenceability.CharacteristicFiveDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev Params := Σ K : Type u, (ℕ → ZMod 5 × K)
abbrev signature : Signature where
  Params := Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 5 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => p.2 n) (fun e => nomatch e)

def bad : Realization signature.{u} :=
  realize signature (fun _ p _ => p.2 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 5] (u : K), u ≠ 0 →
    let M := 4 * Nat.card K + 1
    ∃ v : ℕ → ZMod 5 × K,
      v 0 = (0, 0) ∧ R.readout () ⟨K, v⟩ M = (0, u) ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
        ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u)

private theorem bad_law : ¬ arena.{u}.Law bad := by
  intro h
  let K := ULift.{u} (ZMod 5)
  obtain ⟨w, hw⟩ := h K 1 one_ne_zero
  have he : ((0 : ZMod 5), (0 : K)) = (0, 1) := hw.1.symm.trans hw.2.1
  exact zero_ne_one (congrArg Prod.snd he)

def family : Registration arena.{u}
    (type_of% (@exists_characteristic_five_relative_path.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_characteristic_five_relative_path.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 5)
    let w : ℕ → ZMod 5 × K := fun n => if n = 0 then (0, 0) else (0, 1)
    refine ⟨⟨K, w⟩, 0, 1, ?_⟩
    simp [actual, realize, w]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_five_relative_path.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicFiveDetour.exists_characteristic_five_relative_path.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicFiveDetour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicFiveDetour
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.universes true in
#check @exists_characteristic_five_relative_path

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.Sequenceability.CharacteristicFiveDetour

end
