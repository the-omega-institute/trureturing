import D5.S3.Combinatorics.Sequenceability.CharacteristicSevenRelativePath
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.CharacteristicSevenRelativePath

open _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev PathParams := Σ K : Type u, Field K

abbrev pathSignature : Signature where
  Params := PathParams.{u}
  State p := (ℕ → ZMod 7 × p.1) × (ℕ → ZMod 7 × p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def pathActual : Realization pathSignature.{u} :=
  realize pathSignature (fun _ _ p => p.2) (fun e => nomatch e)

def pathBad : Realization pathSignature.{u} :=
  realize pathSignature (fun _ p _ _ => by
    letI := p.2
    exact (0, 0)) (fun e => nomatch e)

abbrev pathArena : Arena where
  signature := pathSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7]
    (u : K) (_hu : u ≠ 0),
    let N := 6 * Nat.card K + 1;
    ∃ v w : ℕ → ZMod 7 × K,
      v 0 = (0, 0) ∧ v N = (0, u) ∧
      Function.Injective (fun i : Fin (N + 1) => v i.val) ∧
      Set.range (fun i : Fin (N - 1) => v (i.val + 1)) = {z | z.1 ≠ 0} ∧
      (∀ n < N, (R.readout () ⟨K, f⟩ (v, w)) n = v (n + 1) - v n) ∧
      Function.Injective (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val) ∧
      Set.range (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val) = {z | z.1 ≠ 0 ∨ z = (0, u)} ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).length = 6 * Nat.card K + 2 ∧
      (List.ofFn (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val)).length = 6 * Nat.card K + 1 ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).Nodup ∧
      (List.ofFn (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val)).Nodup ∧
      (∀ n ≤ N, (∑ i ∈ Finset.range n, (R.readout () ⟨K, f⟩ (v, w)) i) = v n) ∧
      Function.Injective (fun n : Fin (N + 1) => ∑ i ∈ Finset.range n.val, (R.readout () ⟨K, f⟩ (v, w)) i) ∧
      (∀ a b : ℕ, a < b → b ≤ N → (∑ i ∈ Finset.Ico a b, (R.readout () ⟨K, f⟩ (v, w)) i) ≠ 0) ∧
      (∑ i ∈ Finset.range N, (R.readout () ⟨K, f⟩ (v, w)) i) = (0, u)

private theorem path_bad_law : ¬ pathArena.{u}.Law pathBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨v, w, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htotal⟩ :=
    h K 1 (by simp)
  have hz : (0 : K) = 1 := by
    simpa [pathBad, realize] using congrArg Prod.snd htotal
  exact zero_ne_one hz

def pathFamily : Registration pathArena.{u}
    (type_of% (@exists_characteristic_seven_relative_path.{u})) where
  actual := pathActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_seven_relative_path, pathBad, path_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pathBad, ?_, rfl, path_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance⟩, ((fun _ => (0, (0 : K))), (fun _ => (0, 0))),
      ((fun _ => (0, (0 : K))), (fun _ => (0, 1))), ?_⟩
    intro he
    have hz : (0 : K) = 1 := congrArg (fun f => (f 0).2) he
    exact zero_ne_one hz

def pathAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_seven_relative_path.{u}) (Realization pathSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.exists_characteristic_seven_relative_path.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenRelativePath.pathFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pathArena⟩
  objectArena := .source ⟨pathArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathArena ⟨pathFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pathSignature pathActual.readout pathActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.CharacteristicSevenRelativePath
