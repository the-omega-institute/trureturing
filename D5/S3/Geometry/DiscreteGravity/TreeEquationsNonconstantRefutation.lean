/- GID: D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim; result=D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result; claim=D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim
   digest: A positive nonconstant solution on a cubic tree refutes the tEoM conjecture. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-- The source's sum of reciprocal incident edge lengths. -/
def cVal {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ :=
  ∑ j ∈ g.neighborFinset i, 1 / ell i j

/-- The source's sum of reciprocal squared incident edge lengths. -/
def dVal {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ :=
  ∑ j ∈ g.neighborFinset i, 1 / ell i j ^ 2

/-- The ratio occurring in the tree equation of motion. -/
def ratio {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ := cVal g ell i / dVal g ell i

/-- The tree equation of motion on the edge `ij`. -/
def tEoM {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i j : v) : ℝ :=
  (1 / ell i j) * (ratio g ell i ^ 2 + ratio g ell j ^ 2) -
    ratio g ell i - ratio g ell j

/-- The positive-length nonconstant-solution conjecture on every realization of T₂. -/
def claim : Prop :=
  ∀ (v : Type) (g : SimpleGraph v) [g.LocallyFinite] [DecidableRel g.Adj],
    g.IsTree → (∀ i, g.degree i = 3) → ∀ ell : v → v → ℝ,
    (∀ i j, g.Adj i j → ell i j = ell j i) →
    (∀ i j, g.Adj i j → 0 < ell i j) →
    (∀ i j, g.Adj i j → tEoM g ell i j = 0) →
    ∃ c, ∀ i j, g.Adj i j → ell i j = c

private def parent : Sum ℤ (ℤ × List Bool) → Sum ℤ (ℤ × List Bool) :=
  Sum.elim (fun n => Sum.inl (n - 1))
    (fun p => p.2.casesOn (Sum.inl p.1) (fun _ w => Sum.inr (p.1, w)))

private def rank : Sum ℤ (ℤ × List Bool) → ℤ :=
  Sum.elim id (fun p => p.1 + 1 + p.2.length)

private lemma parent_rank (i : Sum ℤ (ℤ × List Bool)) :
    rank (parent i) = rank i - 1 := by
  sorry

private def graph : SimpleGraph (Sum ℤ (ℤ × List Bool)) where
  Adj i j := parent i = j ∨ parent j = i
  symm _ _ h := h.symm
  loopless i h := by
    have hr := parent_rank i
    rcases h with h | h <;> rw [h] at hr <;> omega

private instance graph_decidable : DecidableRel graph.Adj := Classical.decRel _

private def neighbors (i : Sum ℤ (ℤ × List Bool)) : Finset (Sum ℤ (ℤ × List Bool)) :=
  Sum.elim (fun n => {Sum.inl (n - 1), Sum.inl (n + 1), Sum.inr (n, [])})
    (fun p => {parent (Sum.inr p), Sum.inr (p.1, false :: p.2),
      Sum.inr (p.1, true :: p.2)}) i

private lemma mem_neighbors (i j : Sum ℤ (ℤ × List Bool)) :
    j ∈ neighbors i ↔ graph.Adj i j := by
  sorry

private instance graph_finite : graph.LocallyFinite :=
  fun i => Fintype.ofFinset (neighbors i) (mem_neighbors i)

private lemma neighbor_eq (i : Sum ℤ (ℤ × List Bool)) :
    graph.neighborFinset i = neighbors i := by
  sorry

private lemma graph_degree (i : Sum ℤ (ℤ × List Bool)) : graph.degree i = 3 := by
  sorry

private lemma graph_connected : graph.Connected := by
  sorry

private lemma graph_acyclic : graph.IsAcyclic := by
  sorry

private lemma graph_tree : graph.IsTree := ⟨graph_connected, graph_acyclic⟩

private def scale (n : ℤ) : ℝ := (2 : ℝ) ^ n

private lemma scale_positive (n : ℤ) : 0 < scale n := by
  sorry

private lemma scale_next (n : ℤ) : scale (n + 1) = 2 * scale n := by
  sorry

private def lengths : Sum ℤ (ℤ × List Bool) → Sum ℤ (ℤ × List Bool) → ℝ :=
  Sum.elim
    (fun n => Sum.elim (fun m => (5 / 3 : ℝ) * scale (min n m))
      (fun p => scale p.1))
    (fun p => Sum.elim (fun _ => scale p.1) (fun q => scale (min p.1 q.1)))

private lemma lengths_symmetric (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → lengths i j = lengths j i := by
  sorry

private lemma lengths_positive (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → 0 < lengths i j := by
  sorry

private lemma ratio_spine (n : ℤ) : ratio graph lengths (Sum.inl n) = scale n := by
  sorry

private lemma ratio_branch (n : ℤ) (w : List Bool) :
    ratio graph lengths (Sum.inr (n, w)) = scale n := by
  sorry

private lemma residuals (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → tEoM graph lengths i j = 0 := by
  sorry

private lemma nonconstant :
    ¬ ∃ c, ∀ i j, graph.Adj i j → lengths i j = c := by
  sorry

/-- The preregistered cubic tree carries a positive nonconstant tEoM solution. -/
theorem result : ¬ claim := by
  intro h
  exact nonconstant (h _ graph graph_tree graph_degree lengths
    lengths_symmetric lengths_positive residuals)

end D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation
