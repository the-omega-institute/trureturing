/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourReplication
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourReplication
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Cardinality weights on ordinary dominating sets factor through one-leaf hub replication. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.MinusFourReplication

open Finset DominatingSetAverage LocalDominatingStemBoundReplication

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordinary dominating subsets, each counted once with its cardinality weight. -/
noncomputable def evaluation (H : SimpleGraph V) (x : ℤ) : ℤ :=
  ∑ S ∈ domSets H, x ^ S.card

private theorem subtype_sum (F : Finset (Finset V)) (x : ℤ) :
    (∑ S : ↥F, x ^ S.val.card) = ∑ S ∈ F, x ^ S.card := by
  classical
  simpa only [Finset.univ_eq_attach] using sum_attach F (fun S => x ^ S.card)

private theorem independent_weights (F : Finset (Finset V)) (x : ℤ) (r : ℕ) :
    (∑ f : Fin r → ↥F, x ^ (∑ i, (f i).val.card)) =
      (∑ S ∈ F, x ^ S.card) ^ r := by
  classical
  simp_rw [← prod_pow_eq_pow_sum]
  rw [← Fintype.sum_pow, subtype_sum]

private theorem hub_weights (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    (∑ S ∈ domSetsAt (replicated H U r) (hub r), x ^ S.card) =
      x * (1 + x) * (∑ S ∈ partialSets H U, x ^ S.card) ^ r := by
  classical
  have he := Fintype.sum_equiv (hubEquiv H U r).symm
    (fun p => x ^ (assemble r true p.1 (fun i => (p.2 i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  rw [subtype_sum] at he
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [assemble_card, pow_add]
  simp only [Bool.false_eq_true, ↓reduceIte, pow_one, pow_zero, mul_one]
  simp_rw [← sum_mul, independent_weights]
  ring

private theorem omitted_weights (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    (∑ S ∈ omittedSets H U r, x ^ S.card) =
      x * (evaluation H x) ^ r := by
  classical
  have he := Fintype.sum_equiv (omittedEquiv H U r).symm
    (fun f => x ^ (assemble r false true (fun i => (f i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  rw [subtype_sum] at he
  rw [← he]
  simp_rw [assemble_card]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, pow_add, pow_one]
  rw [← sum_mul, independent_weights]
  simp only [evaluation, mul_comm]

/-- The two hub cases preserve cardinality weights, including zero copies. -/
theorem replicated_evaluation (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    evaluation (replicated H U r) x =
      x * (1 + x) * (∑ S ∈ partialSets H U, x ^ S.card) ^ r +
        x * (evaluation H x) ^ r := by
  classical
  rw [← hub_weights, ← omitted_weights]
  exact (sum_filter_add_sum_filter_not (domSets (replicated H U r))
    (fun S => hub r ∈ S) (fun S => x ^ S.card)).symm

private theorem partial_eq_of_leaf (H : SimpleGraph V) (v w : V)
    (hw : Leaf H w) (hvw : H.Adj w v) : partialSets H {v} = domSets H := by
  classical
  apply Subset.antisymm
  · intro S hS
    have hp := (mem_partialSets H {v} S).mp hS
    apply mem_domSets.mpr
    intro a
    by_cases ha : a = v
    · subst a
      have hne : w ≠ v := hvw.ne
      rcases (leaf_dominated_iff hw hvw S).mp (hp w (by simpa using hne)) with h | h
      · exact Or.inr ⟨w, h, hvw.symm⟩
      · exact Or.inl h
    · exact hp a (by simpa using ha)
  · exact domSets_subset_partialSets H {v}

/-- A leaf at the attachment support prevents the hub from creating new partial sets. -/
theorem support_replication_evaluation (H : SimpleGraph V) (v w : V)
    (hw : Leaf H w) (hvw : H.Adj w v) (r : ℕ) (x : ℤ) :
    evaluation (replicated H {v} r) x = x * (x + 2) * (evaluation H x) ^ r := by
  rw [replicated_evaluation, partial_eq_of_leaf H v w hw hvw]
  unfold evaluation
  ring

/-- Every copied vertex reaches the hub through the specified support. -/
theorem support_replication_connected (H : SimpleGraph V) (v : V)
    (hH : H.Connected) (r : ℕ) : (replicated H {v} r).Connected := by
  classical
  apply SimpleGraph.connected_iff_exists_forall_reachable.mpr
  refine ⟨hub r, ?_⟩
  intro a
  cases a with
  | inl a =>
    let f : H →g replicated H {v} r := {
      toFun := fun w => Sum.inl (a.1, w)
      map_rel' := fun h => ⟨rfl, h⟩ }
    have hh : (replicated H {v} r).Adj (hub r) (Sum.inl (a.1, v)) :=
      ⟨rfl, mem_singleton_self v⟩
    exact hh.reachable.trans ((hH v a.2).map f)
  | inr a =>
    fin_cases a
    · exact SimpleGraph.Reachable.refl
    · exact (show (replicated H {v} r).Adj (hub r) (pendant r) from by
        simp [replicated, hub, pendant]).reachable

end D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
