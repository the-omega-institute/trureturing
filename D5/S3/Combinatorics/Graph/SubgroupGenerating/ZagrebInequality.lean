/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Chebyshev]
   utility: none
   digest: Every finite group's literal generating graph satisfies the Zagreb inequality. -/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
import Mathlib.Algebra.Order.Chebyshev

/-! The full finite-group Zagreb inequality on the actual unordered-edge graph. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
noncomputable section

/-- The first Zagreb index sums squared degrees over every vertex, including isolates. -/
def firstZagreb {V : Type} [Fintype V] (g : SimpleGraph V) : ℝ := by
  classical
  exact ∑ v : V, (g.degree v : ℝ)^2

/-- A symmetric product of the degrees of the two endpoints of an unordered edge. -/
def endpointProduct {V : Type} [Fintype V] (g : SimpleGraph V) : Sym2 V → ℝ := by
  classical
  exact Sym2.lift ⟨fun u v => (g.degree u : ℝ) * (g.degree v : ℝ), fun _ _ => mul_comm _ _⟩

/-- The second Zagreb index counts each actual unordered edge once. -/
def secondZagreb {V : Type} [Fintype V] (g : SimpleGraph V) : ℝ := by
  classical
  exact ∑ e ∈ g.edgeFinset, endpointProduct g e

variable {G : Type} [Group G] [Fintype G]
attribute [local instance] CyclicExtensionRefutation.subgroupFintype

private def pairEdge (p : G × G) : Sym2 (Vertex G) :=
  s(Sum.inl p, Sum.inr (Subgroup.closure ({p.1,p.2} : Set G)))

omit [Fintype G] in
private theorem pairEdge_injective : Function.Injective (pairEdge (G := G)) := by
  intro p q h
  simp only [pairEdge, Sym2.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr, false_and,
    or_false] at h
  exact h.1

private theorem actual_edges :
    (sgbGraph G).edgeFinset = (Finset.univ : Finset (G × G)).image pairEdge := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    cases u with
    | inl p =>
      cases v with
      | inl q => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sgbGraph,
          pairEdge]
      | inr H => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sgbGraph,
          pairEdge, eq_comm]
    | inr H =>
      cases v with
      | inl p => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sgbGraph,
          pairEdge, eq_comm]
      | inr K => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sgbGraph,
          pairEdge]

private theorem first_formula : firstZagreb (sgbGraph G) =
    (Fintype.card G : ℝ)^2 + ∑ H : Subgroup G, (pairCount H : ℝ)^2 := by
  classical
  simp [firstZagreb, Fintype.sum_sum_type, degree_pair, degree_subgroup,
    Fintype.card_prod, Nat.cast_mul, pow_two]

private theorem second_formula : secondZagreb (sgbGraph G) =
    ∑ H : Subgroup G, (pairCount H : ℝ)^2 := by
  classical
  rw [secondZagreb, actual_edges, Finset.sum_image (fun p _ q _ h => pairEdge_injective h)]
  simp only [endpointProduct, pairEdge, Sym2.lift_mk, degree_pair, degree_subgroup,
    Nat.cast_one, one_mul]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (G × G))) (t := (Finset.univ : Finset (Subgroup G)))
    (g := fun p => Subgroup.closure ({p.1,p.2} : Set G))
    (f := fun p => (pairCount (Subgroup.closure ({p.1,p.2} : Set G)) : ℝ))
    (fun _ _ => Finset.mem_univ _)
  rw [← h]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_congr rfl (fun p hp => congrArg (fun K : Subgroup G => (pairCount K : ℝ))
    (Finset.mem_filter.mp hp).2)]
  simp [pairCount, generatingPairs, pow_two]

/-- Every finite group's literal graph satisfies Hansen--Vukicevic, including the trivial group. -/
theorem hansen_vukicevic :
    firstZagreb (sgbGraph G) / (Fintype.card (Vertex G) : ℝ) ≤
      secondZagreb (sgbGraph G) / ((sgbGraph G).edgeFinset.card : ℝ) := by
  classical
  have hs : (∑ H : Subgroup G, (pairCount H : ℝ)) = (Fintype.card G : ℝ)^2 := by
    exact_mod_cast (sum_pairCount (G := G))
  have hc := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Subgroup G))) (f := fun H => (pairCount H : ℝ))
  simp only [Finset.card_univ] at hc
  rw [hs] at hc
  rw [first_formula, second_formula, edge_count]
  have hm : (0 : ℝ) < (Fintype.card G : ℝ)^2 := by positivity
  have hn : (0 : ℝ) < (Fintype.card G : ℝ)^2 + Fintype.card (Subgroup G) := by positivity
  simp only [Fintype.card_sum, Fintype.card_prod, Nat.cast_add,
    Nat.cast_pow, ← pow_two]
  apply (div_le_div_iff₀ hn hm).mpr
  nlinarith

#print axioms hansen_vukicevic

end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
