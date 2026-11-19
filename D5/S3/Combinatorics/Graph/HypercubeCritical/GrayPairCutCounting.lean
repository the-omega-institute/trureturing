import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Cut counting in the residual graph of a pair of Gray supports. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GrayPairCutCounting

open scoped BigOperators
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def neighborsIn (A : Finset V) (v : V) : Finset V :=
  A.filter (G.Adj v)

private theorem cut_eq_reverse (A B : Finset V) :
    (∑ v ∈ A, (neighborsIn G B v).card) = ∑ w ∈ B, (neighborsIn G A w).card := by
  simp only [neighborsIn, card_filter]
  rw [sum_comm]
  exact sum_congr rfl fun w _ => sum_congr rfl fun v _ => by
    rw [G.adj_comm v w]

/-- Inside a finite regular region, each selected vertex must send enough
edges to the omitted vertices to keep its selected degree at most `k`. -/
theorem selected_card_mul_le (R S : Finset V) (hSR : S ⊆ R) (d k : ℕ)
    (hR : ∀ v ∈ R, (R.filter (G.Adj v)).card = d)
    (hS : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ k) :
    (d - k) * S.card ≤ d * (R.card - S.card) := by
  let T := R \ S
  have hpart (v : V) : neighborsIn G S v ∪ neighborsIn G T v = neighborsIn G R v := by
    ext w
    simp only [neighborsIn, mem_union, mem_filter, T, mem_sdiff]
    by_cases hw : w ∈ S
    · simp [hw, hSR hw]
    · simp [hw]
  have hdis (v : V) : Disjoint (neighborsIn G S v) (neighborsIn G T v) := by
    rw [disjoint_left]
    intro w hws hwt
    exact (mem_sdiff.mp (mem_filter.mp hwt).1).2 (mem_filter.mp hws).1
  have hlo : (d - k) * S.card ≤ ∑ v ∈ S, (neighborsIn G T v).card := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro v hv
    have he := hpart v
    have hc := congrArg card he
    rw [card_union_of_disjoint (hdis v)] at hc
    have hrv := hR v (hSR hv)
    have hsv := hS v hv
    simp only [neighborsIn] at hc
    omega
  have hhi : (∑ w ∈ T, (neighborsIn G S w).card) ≤ d * (R.card - S.card) := by
    rw [← card_sdiff_of_subset hSR, mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro w hw
    rw [← hR w (mem_sdiff.mp hw).1]
    exact card_le_card (filter_subset_filter _ hSR)
  rw [cut_eq_reverse] at hlo
  exact hlo.trans hhi

/-- A four-leaf star forces one omission from every set of induced maximum
degree at most three. The ambient graph may have additional edges. -/
theorem star_has_omission (S leaves : Finset V) (center : V)
    (hleaves : leaves.card = 4) (hadj : ∀ v ∈ leaves, G.Adj center v)
    (hS : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ 3) :
    (insert center leaves \ S).Nonempty := by
  by_contra hempty
  have hs : insert center leaves ⊆ S := by
    intro v hv
    by_contra h
    exact hempty ⟨v, mem_sdiff.mpr ⟨hv, h⟩⟩
  have hsleaves : leaves ⊆ S.filter (G.Adj center) := by
    intro v hv
    exact mem_filter.mpr ⟨hs (mem_insert_of_mem hv), hadj v hv⟩
  have hl := card_le_card hsleaves
  have hu := hS center (hs (mem_insert_self _ _))
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.GrayPairCutCounting
