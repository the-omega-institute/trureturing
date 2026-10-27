import D5.S3.Combinatorics.Sequenceability.UniformRelativePath
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Exact-telescope dependent-family registration of the universal endpoint readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S3.Combinatorics.Sequenceability.UniformRelativePath

open _root_.D5.S3.Combinatorics.Sequenceability.UniformRelativePath
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev PathParams := Σ K : Type u, Field K × ℕ

abbrev signature : Signature where
  Params := PathParams.{u}
  State p := ℕ → ZMod p.2.2 × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.2.2 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p v => v ((p.2.2 - 1) * Nat.card p.1 + 1))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by letI := p.2.1; exact (0, 0))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (K : Type u) [f : Field K] [Finite K] [CharP K p] (u : K), u ≠ 0 →
      let M := (p - 1) * Nat.card K + 1
      ∃ v : ℕ → ZMod p × K,
        v 0 = (0, 0) ∧ R.readout () ⟨K, f, p⟩ v = (0, u) ∧
        Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
        Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
        Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
          ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
        Function.Injective (fun k : Fin (M + 1) =>
          ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
        (∀ a b : ℕ, a < b → b ≤ M →
          (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
        (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K := ULift.{u} (ZMod 5)
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨v, _, hend, _⟩ := h 5 (by decide) (by decide) K 1 one_ne_zero
  have hz : (0 : K) = 1 := congrArg Prod.snd hend
  exact zero_ne_one hz

def family : Registration arena.{u} (type_of% (@exists_uniform_relative_path.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_uniform_relative_path, rejected, rejected_law⟩
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
    let K := ULift.{u} (ZMod 5)
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    refine ⟨⟨K, inferInstance, 5⟩, (fun _ => (0, 0)), (fun _ => (0, 1)), ?_⟩
    intro he
    exact zero_ne_one (congrArg Prod.snd he : (0 : K) = 1)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_uniform_relative_path.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.UniformRelativePath.exists_uniform_relative_path.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.UniformRelativePath.family
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
    owner := `D5.S3.Combinatorics.Sequenceability.UniformRelativePath
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.UniformRelativePath

end
