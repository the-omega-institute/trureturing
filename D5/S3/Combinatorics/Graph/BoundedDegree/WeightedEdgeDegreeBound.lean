/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/WeightedEdgeDegreeBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/WeightedEdgeDegreeBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Nonnegative edge weights bound the size of an induced bounded-degree set. -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Edge weights certify upper bounds for induced bounded-degree sets. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.WeightedEdgeDegreeBound

open Finset

/-- If every selected vertex can pay its share of the weighted edges with
its degree budget, the total edge and slack weights bound cardinality.
The sum over ordered pairs counts each edge twice. -/
theorem card_le_of_weights {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (R S : Finset V) (hS : S ⊆ R) (d : ℕ)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ d)
    (vertexWeight slackWeight : V → ℤ) (edgeWeight : V → V → ℤ) (scale : ℤ)
    (hvertexWeight : ∀ x ∈ R, 0 ≤ vertexWeight x) (hslackWeight : ∀ x ∈ R, 0 ≤ slackWeight x)
    (hedgeWeight : ∀ x ∈ R, ∀ y ∈ R, 0 ≤ edgeWeight x y)
    (hsym : ∀ x ∈ R, ∀ y ∈ R, edgeWeight x y = edgeWeight y x)
    (hzero : ∀ x ∈ R, ∀ y ∈ R, ¬G.Adj x y → edgeWeight x y = 0)
    (hcapacity : ∀ x ∈ R, ∀ y ∈ R, G.Adj x y → edgeWeight x y ≤ vertexWeight x + vertexWeight y)
    (hcover : ∀ x ∈ R, scale + d * vertexWeight x ≤ (∑ y ∈ R, edgeWeight x y) + slackWeight x) :
    2 * scale * (S.card : ℤ) ≤ (∑ x ∈ R, ∑ y ∈ R, edgeWeight x y) + 2 * ∑ x ∈ R, slackWeight x := by
  classical
  let z (x : V) : ℤ := if x ∈ S then 1 else 0
  let burden (x y : V) : ℤ := if G.Adj x y then vertexWeight x * z x * z y else 0
  have hz : (∑ x ∈ R, z x) = S.card := by
    have hf : R.filter (· ∈ S) = S := by
      ext x
      exact mem_filter.trans ⟨And.right, fun h => ⟨hS h, h⟩⟩
    simp only [z, sum_boole, hf]
  have localCapacity (x : V) (hx : x ∈ R) :
      (∑ y ∈ R, burden x y) ≤ d * (vertexWeight x * z x) := by
    by_cases hxS : x ∈ S
    · have hf : (R.filter (G.Adj x)).filter (· ∈ S) = S.filter (G.Adj x) := by
        ext y
        simp only [mem_filter]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hS h.1, h.2⟩, h.1⟩⟩
      have he : (∑ y ∈ R, burden x y) =
          vertexWeight x * ((S.filter (G.Adj x)).card : ℤ) := by
        simp only [burden, z, ite_eq_left hxS, mul_one, ← sum_filter]
        rw [← mul_sum, sum_boole, hf]
      rw [he, show z x = 1 by simp [z, hxS], mul_one, mul_comm (d : ℤ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg x hxS) (hvertexWeight x hx)
    · simp [burden, z, hxS]
  have hrow (x : V) (hx : x ∈ R) (y : V) (hy : y ∈ R) :
      edgeWeight x y * (z x + z y) ≤ edgeWeight x y + burden x y + burden y x := by
    by_cases ha : G.Adj x y
    · have hyx := ha.symm
      by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S <;>
        simp only [burden, z, ha, hyx, ite_true, hxS, hyS, ite_false,
          mul_one, mul_zero, zero_add, add_zero]
      all_goals first | exact le_rfl | linarith [hcapacity x hx y hy ha, hedgeWeight x hx y hy]
    · have hb : ¬G.Adj y x := fun h => ha h.symm
      simp [burden, ha, hb, hzero x hx y hy ha]
  have hslackWeightBound (x : V) (hx : x ∈ R) : slackWeight x * z x ≤ slackWeight x := by
    by_cases hxS : x ∈ S <;> simp [z, hxS, hslackWeight x hx]
  have hcover' (x : V) (hx : x ∈ R) :
      scale * z x + d * (vertexWeight x * z x) ≤ (∑ y ∈ R, edgeWeight x y * z x) + slackWeight x * z x := by
    by_cases hxS : x ∈ S
    · simpa [z, hxS] using hcover x hx
    · simp [z, hxS]
  have hswap :
      (∑ x ∈ R, ∑ y ∈ R, edgeWeight x y * z y) = ∑ x ∈ R, ∑ y ∈ R, edgeWeight x y * z x := by
    rw [sum_comm]
    exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [hsym y hy x hx]
  have hsum := sum_le_sum (s := R) fun x hx => sum_le_sum (s := R) fun y hy => hrow x hx y hy
  simp only [mul_add, sum_add_distrib] at hsum
  rw [hswap, sum_comm (f := fun x y => burden y x)] at hsum
  have hd := sum_le_sum (s := R) localCapacity
  have hcoverSum := sum_le_sum (s := R) hcover'
  have hslack := sum_le_sum (s := R) hslackWeightBound
  simp only [sum_add_distrib, ← mul_sum, hz] at hcoverSum hd
  linarith

end D5.S3.Combinatorics.Graph.BoundedDegree.WeightedEdgeDegreeBound
