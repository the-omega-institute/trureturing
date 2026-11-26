import D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

namespace Reg.D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit

open _root_.D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

universe u

noncomputable section

abbrev signature : Signature where
  Params := Σ ι : Type u, Σ _ : Finset ι, Σ _ : ι → ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x ↦ weight p.2.1 p.2.2.1 p.2.2.2 x) (fun e ↦ nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} (s : Finset ι) (b : ι → ℕ) {r : ℕ} {x : ℝ},
    2 ≤ r → (∀ i ∈ s, 1 ≤ b i) → (((r + ∑ i ∈ s, b i : ℕ) : ℝ) - 1 ≤ x) →
    (descPochhammer ℝ s.card).eval (x - 1) / (x + 1) ≤ weight s b r x ∧
      0 < R.readout () ⟨ι, s, b, r⟩ x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := @law PUnit.{u+1} ∅ (fun _ ↦ 1) 2 1 (by decide) (by simp) (by norm_num)
  exact lt_irrefl (0 : ℝ) h.2

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  refine ⟨⟨PUnit.{u+1}, {PUnit.unit}, fun _ ↦ 1, 2⟩, 2, 3, ?_⟩
  change weight {PUnit.unit} (fun _ ↦ 1) 2 2 ≠
    weight {PUnit.unit} (fun _ ↦ 1) 2 3
  have hp : ({PUnit.unit} : Finset PUnit.{u+1}).powerset = {∅, {PUnit.unit}} := by
    simpa [Finset.powerset_empty] using Finset.powerset_insert (∅ : Finset PUnit.{u+1}) PUnit.unit
  have hn : (∅ : Finset PUnit.{u+1}) ∉ ({{PUnit.unit}} : Finset (Finset PUnit.{u+1})) := by simp
  norm_num [weight, hp, Finset.sum_insert hn, descPochhammer_one]

def family : Registration arena.{u} (type_of% @weight_bounds.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_bounds.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_bounds.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit
