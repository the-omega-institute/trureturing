import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.KingmanPointwise
import Reg.Support.DependentFamily

/-! Complete source reconstruction and actual laws for the dependent observation families. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Probability.KingmanEstimates
open _root_.D5.S3.Analytic.Probability.KingmanPointwise
open _root_.D5.S3.Analytic.Probability.BirkhoffPointwise
open MeasureTheory Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Analytic.Probability.KingmanPointwise

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : α → α, ℕ → α → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x n => p.2.2 n x / (n : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α}, MeasurePreserving T μ μ → ∀ X : ℕ → α → ℝ,
    (∀ n, Integrable (X n) μ) → (∀ n, ∀ᵐ x ∂μ, 0 ≤ X n x) →
    (∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n ((T^[m]) x)) →
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (R.readout () ⟨α, T, X⟩ x) atTop (nhds (g x))

theorem source_bridge :
    (type_of% @kingman_subadditive.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := @kingman_subadditive.{u}

end Reg.D5.S3.Analytic.Probability.KingmanPointwise

end

-- Transient exact applications; these are not retained declarations.
example [MeasurableSpace Empty] (X : ℕ → Empty → ℝ) :
    ∃ g : Empty → ℝ, Integrable g (0 : Measure Empty) ∧
      (∀ᵐ x ∂(0 : Measure Empty), g (id x) = g x) ∧
      ∀ᵐ x ∂(0 : Measure Empty),
        Tendsto (fun n : ℕ => X n x / (n : ℝ)) atTop (nhds (g x)) :=
  kingman_subadditive (MeasurePreserving.id 0) X
    (fun _ => by simp) (fun _ => by simp) (fun _ _ => by simp)

example (a : ℝ) (ha : 0 ≤ a) :
    ∃ g : Unit → ℝ, Integrable g (Measure.dirac ()) ∧
      (∀ᵐ x ∂Measure.dirac (), g (id x) = g x) ∧
      ∀ᵐ x ∂Measure.dirac (),
        Tendsto (fun n : ℕ => (if n = 0 then a else (n : ℝ)) / (n : ℝ))
          atTop (nhds (g x)) := by
  let X : ℕ → Unit → ℝ := fun n _ => if n = 0 then a else (n : ℝ)
  apply kingman_subadditive (MeasurePreserving.id (Measure.dirac ())) X
  · intro n
    exact integrable_const _
  · intro n
    filter_upwards with x
    dsimp only [X]
    split_ifs
    · exact ha
    · exact Nat.cast_nonneg _
  · intro m n
    filter_upwards with x
    by_cases hm : m = 0
    · subst m
      simp only [X, zero_add, Function.iterate_zero_apply, ite_eq_left rfl]
      exact le_add_of_nonneg_left ha
    by_cases hn : n = 0
    · subst n
      simp only [X, add_zero, ite_eq_left rfl]
      exact le_add_of_nonneg_right ha
    simp [X, hm, hn, Nat.add_ne_zero_left hm, Nat.cast_add]
