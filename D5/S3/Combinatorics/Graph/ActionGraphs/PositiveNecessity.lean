/- GID: D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity
   mirror-E: none(waiver:strict-positive-convolution-necessity)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.claim; result=D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.result; claim=D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.claim
   digest: Finite directed paths give an entire generalized action-graph family without strictly positive convolution coefficients. -/
/-
The source's three graph axioms are stated for arbitrary finite vertex types,
native Digraph adjacency, actual descendant-induced relations, and RelIso.
The tree condition uses SimpleGraph.IsTree after forgetting orientation;
root reachability and the absence of directed cycles specify its outward orientation.
The path's successor adjacency is supplied by CovBy, with its correspondence
to consecutive natural labels verified inside the consumers.
Direct D5 dependencies: none.
result: proof_shape: bind-only; admission_basis: open-problem-resolution (#23113).
path_family_legal: proof_shape: bind-only; consumer: result.
-/

import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.NormNum

/-! # Strictly positive convolution necessity for generalized action graphs -/

namespace D5.S3.Combinatorics.Graph.ActionGraphs.PositiveNecessity

open Relation

/-- The finite rooted directed trees and the three axioms of Definition 1.1. -/
def IsGeneralizedActionGraph (s : ℕ → ℕ) (V : ℕ → Type)
    (G : ∀ n, Digraph (V n)) (root : ∀ n, V n)
    (label : ∀ n, V n → ℕ) (step : ∀ n, V n ↪ V (n + 1)) : Prop :=
  (∀ n, Finite (V n) ∧ (G n).toSimpleGraphInclusive.IsTree ∧
    (∀ v, ReflTransGen (G n).Adj (root n) v) ∧
    (∀ v, ¬ TransGen (G n).Adj v v)) ∧
  ((Nat.card (V 0) = s 0 ∧ (∀ v, label 0 v = 0) ∧
      (∀ v w, ¬ (G 0).Adj v w)) ∧
    (∀ n, step n (root n) = root (n + 1) ∧
      (∀ v, label (n + 1) (step n v) = label n v) ∧
      (∀ v w, (G (n + 1)).Adj (step n v) (step n w) ↔ (G n).Adj v w) ∧
      Nat.card {v : V (n + 1) // v ∉ Set.range (step n)} = s (n + 1) ∧
      (∀ v, v ∉ Set.range (step n) → label (n + 1) v = n + 1))) ∧
  (∀ n (v : V n), ∃ k, k ≤ n ∧
    ∃ e : (G k).Adj ≃r
      (fun a b : {w : V n // ReflTransGen (G n).Adj v w} => (G n).Adj a.1 b.1),
      e (root k) = ⟨v, ReflTransGen.refl⟩ ∧
      ∃ shift : ℕ, ∀ w, label n (e w).1 = label k w + shift) ∧
  (∀ n (v : V n), (∀ w, ¬ (G n).Adj v w) → label n v = n)

/-- The full strictly-positive necessity question in Section 4. -/
def claim : Prop :=
  ∀ s : ℕ → ℕ, (∀ n, 0 < s n) →
    (∃ (V : ℕ → Type) (G : ∀ n, Digraph (V n)) (root : ∀ n, V n)
      (label : ∀ n, V n → ℕ) (step : ∀ n, V n ↪ V (n + 1)),
      IsGeneralizedActionGraph s V G root label step) →
    s 0 = 1 ∧ ∃ z : ℕ → ℕ, (∀ i, 1 ≤ i → 0 < z i) ∧
      ∀ n, 1 ≤ n → s n = ∑ i ∈ Finset.Icc 1 n, z i * s (n - i)

private theorem path_family_legal :
    IsGeneralizedActionGraph (fun _ => 1) (fun n => Fin (n + 1))
      (fun _ => ⟨CovBy⟩) (fun _ => 0) (fun _ => Fin.val)
      (fun _ => Fin.castSuccEmb) := by
  classical
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · have h : (⟨CovBy⟩ : Digraph (Fin (n + 1))).toSimpleGraphInclusive =
          SimpleGraph.pathGraph (n + 1) := by
        ext a b
        simp only [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj,
          SimpleGraph.pathGraph, SimpleGraph.hasse_adj]
        exact and_iff_right_of_imp
          (fun h => h.elim (fun h => h.lt.ne) (fun h => h.lt.ne'))
      rw [h]
      exact SimpleGraph.isTree_pathGraph_add_one n
    · intro v
      exact le_iff_reflTransGen_covBy.mp (Fin.zero_le v)
    · intro v h
      exact (lt_irrefl v) (lt_iff_transGen_covBy.mpr h)
  · simp
  · intro n
    refine ⟨rfl, (fun _ => rfl), ?_, ?_, ?_⟩
    · intro v w
      simp
    · have h : {v : Fin (n + 1 + 1) // v ∉ Set.range
          (Fin.castSuccEmb : Fin (n + 1) ↪ Fin (n + 1 + 1))} =
          {v : Fin (n + 1 + 1) // v = Fin.last (n + 1)} := by
        congr 1
        funext v
        simp only [Fin.coe_castSuccEmb, Fin.range_castSucc, Set.mem_ofPred_eq,
          not_lt, Fin.ext_iff, Fin.val_last]
        exact propext (by omega)
      rw [h]
      simp
    · intro v hv
      simp only [Fin.coe_castSuccEmb, Fin.range_castSucc, Set.mem_ofPred_eq,
        not_lt] at hv
      change v.val = n + 1
      have := v.isLt
      omega
  · intro n v
    refine ⟨n - v.val, Nat.sub_le _ _, ?_⟩
    let f : Fin (n - v.val + 1) →
        {w : Fin (n + 1) // ReflTransGen CovBy v w} := fun j =>
      ⟨⟨v.val + j.val, by have := v.isLt; have := j.isLt; omega⟩,
        le_iff_reflTransGen_covBy.mp (by change v.val ≤ v.val + j.val; omega)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        apply Fin.ext
        have := congrArg (fun x => x.val.val) h
        dsimp [f] at this
        omega
      · intro w
        have hw : v ≤ w.val := le_iff_reflTransGen_covBy.mpr w.property
        change v.val ≤ w.val.val at hw
        refine ⟨⟨w.val.val - v.val, by have := w.val.isLt; omega⟩, ?_⟩
        apply Subtype.ext
        apply Fin.ext
        dsimp [f]
        omega
    let e : CovBy (α := Fin (n - v.val + 1)) ≃r
        (fun a b : {w : Fin (n + 1) // ReflTransGen CovBy v w} =>
          a.val ⋖ b.val) :=
      { Equiv.ofBijective f hf with
        map_rel_iff' := by
          intro a b
          change (f a).val ⋖ (f b).val ↔ a ⋖ b
          simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
          dsimp [f]
          omega }
    refine ⟨e, ?_, v.val, ?_⟩
    · apply Subtype.ext
      apply Fin.ext
      simp [e, f]
    · intro w
      change v.val + w.val = w.val + v.val
      omega
  · intro n v hv
    change (∀ w, ¬ v ⋖ w) at hv
    change v.val = n
    by_contra h
    have hvn : v.val < n := by have := v.isLt; omega
    exact hv ⟨v.val + 1, by omega⟩ (by simp)

/-- Constant-one vertex additions form legal graphs but force the second coefficient to zero. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨_, z, hz, heq⟩ := h (fun _ => 1) (by simp)
    ⟨(fun n => Fin (n + 1)), (fun _ => ⟨CovBy⟩), (fun _ => 0),
      (fun _ => Fin.val), (fun _ => Fin.castSuccEmb), path_family_legal⟩
  have h1 := heq 1 (by omega)
  have h2 := heq 2 (by omega)
  norm_num [Finset.sum_Icc_succ_top] at h1 h2
  have hpos := hz 2 (by omega)
  omega

end D5.S3.Combinatorics.Graph.ActionGraphs.PositiveNecessity
