/- GID: D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A shortest fixed-tree tail assigns each weld arrival leaf a unique crossing index. -/

import D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
import Mathlib.Probability.ProbabilityMassFunction.Basic

open D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound

private abbrev Leaf (k : ℕ) := {y // y ∈ leafWords k}
private abbrev Vertex (k : ℕ) := {y : List Bool // y.length ≤ k}

private def vertex {k : ℕ} (z : Vertex k) (y : Leaf k) : Vertex k :=
  ⟨y.1, (((weighted_leaf_distance k z).2.1 y.1).mp y.2).le⟩

private def leaves (k : ℕ) (z : Vertex k) : Finset (Leaf k) :=
  ⟨(leafWords k).attach, (weighted_leaf_distance k z).1.attach⟩

private theorem mem_leaves {k : ℕ} (z : Vertex k) (y : Leaf k) : y ∈ leaves k z :=
  List.mem_attach _ _

/-- Total dyadic leaf weight for the depth of the target vertex. -/
noncomputable def totalLeafWeight {k : ℕ} (target : {x : List Bool // x.length ≤ k}) : ℝ≥0∞ :=
  ENNReal.ofReal (3 / 2 - (1 / 2 : ℝ) ^ (target.1.length + 1))

private theorem weight_sum (k : ℕ) (z : Vertex k) :
    (∑ y ∈ leaves k z, ((2 : ℝ≥0∞) ^ (boundedWordTree k).dist z (vertex z y))⁻¹) =
      totalLeafWeight z := by
  classical
  unfold totalLeafWeight
  let weight := fun y : Leaf k => (1 / 2 : ℝ) ^ (boundedWordTree k).dist z (vertex z y)
  have hReal : (∑ y ∈ leaves k z, weight y) = 3 / 2 - (1 / 2 : ℝ) ^ (z.1.length + 1) := by
    change ((leafWords k).attach.map weight).sum = _
    have h := congrArg (Rat.castHom ℝ) (weighted_leaf_distance k z).2.2
    rw [map_list_sum, List.map_map] at h
    simpa [weight, vertex, Function.comp_def, map_div, map_pow] using h
  rw [← hReal, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by dsimp [weight]; positivity)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [show weight y = (1 / 2 : ℝ) ^ (boundedWordTree k).dist z (vertex z y) from rfl,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
  simp [div_eq_mul_inv, ENNReal.inv_pow]

/-- Each possible arrival leaf fixes the position of the last crossing.
The union therefore charges each leaf with the weight of one tail length. -/
theorem mass_of_weighted_tail {Ω : Type*} (μ : PMF Ω)
    (k r : ℕ) (target : Vertex k) (budget : ℝ≥0∞)
    (cross : ℕ → Leaf k → Set Ω) (tail : ℕ → Leaf k → Set Ω) (collision : Set Ω)
    (hCover : ∀ ω ∈ collision, ∃ (j : ℕ) (y : Leaf k),
      j + 1 + (boundedWordTree k).dist target (vertex target y) = r ∧
      ω ∈ cross j y ∧ ω ∈ tail j y)
    (hCross : ∀ j y, μ.toOuterMeasure (cross j y) ≤ budget)
    (hTail : ∀ j y, μ.toOuterMeasure (cross j y ∩ tail j y) ≤
      μ.toOuterMeasure (cross j y) *
        ((2 : ℝ≥0∞) ^ (boundedWordTree k).dist target (vertex target y))⁻¹) :
    let totalWeight := totalLeafWeight target
    μ.toOuterMeasure collision ≤ budget * totalWeight := by
  classical
  intro totalWeight
  let index := fun y : Leaf k => r - ((boundedWordTree k).dist target (vertex target y) + 1)
  let events := fun y : Leaf k => cross (index y) y ∩ tail (index y) y
  have hSubset : collision ⊆ ⋃ y ∈ leaves k target, events y := by
    intro ω hω
    obtain ⟨j, y, hj, hC, hT⟩ := hCover ω hω
    have hIdx : index y = j := by dsimp [index]; omega
    refine Set.mem_iUnion₂.mpr ⟨y, mem_leaves target y, ?_⟩
    change ω ∈ cross (index y) y ∩ tail (index y) y
    rw [hIdx]
    exact ⟨hC, hT⟩
  calc
    μ.toOuterMeasure collision ≤ μ.toOuterMeasure (⋃ y ∈ leaves k target, events y) :=
      μ.toOuterMeasure.mono hSubset
    _ ≤ ∑ y ∈ leaves k target, μ.toOuterMeasure (events y) :=
      MeasureTheory.measure_biUnion_finset_le (μ := μ.toOuterMeasure) _ _
    _ ≤ ∑ y ∈ leaves k target,
        budget * ((2 : ℝ≥0∞) ^ (boundedWordTree k).dist target (vertex target y))⁻¹ := by
      apply Finset.sum_le_sum
      intro y _
      apply (hTail (index y) y).trans
      gcongr
      exact hCross (index y) y
    _ = _ := by rw [← Finset.mul_sum, weight_sum]

end D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound
