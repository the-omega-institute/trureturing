/- GID: D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeltaY/SharpThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sym]
   utility: none
   digest: Zhou’s minimum-degree threshold for strong reverse moves is exactly six. -/

import D5.S3.Combinatorics.Graph.DeltaY.TwoColorInvariant
import Mathlib.Data.Finset.Sym

/-!
The common reachability threshold is six. A five-step ordinary history of a
minimum-degree-five graph takes its edge count from nineteen to eighteen.
Strong histories preserve the count, including after graph isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

namespace DeltaY

open Finset Relation

universe u v

private def seed : State :=
  ⟨{0, 1, 2, 3, 4, 5, 6},
    {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(1, 5),
      s(1, 6), s(2, 3), s(2, 4), s(2, 5), s(2, 6), s(3, 4), s(3, 5), s(3, 6),
      s(4, 5), s(4, 6), s(5, 6)}⟩

private def triple012 : Triple := ⟨0, 1, 2, by decide, by decide, by decide⟩
private def triple034 : Triple := ⟨0, 3, 4, by decide, by decide, by decide⟩
private def triple578 : Triple := ⟨5, 7, 8, by decide, by decide, by decide⟩
private def triple157 : Triple := ⟨1, 5, 7, by decide, by decide, by decide⟩
private def triple369 : Triple := ⟨3, 6, 9, by decide, by decide, by decide⟩

private def after1 := seed.forward triple012 7
private def after2 := after1.forward triple034 8
private def after3 := after2.reverse triple578 0
private def after4 := after3.forward triple157 9
private def after5 := after4.reverse triple369 1

def P (d : ℕ) : Prop :=
  ∀ G : FiniteGraph.{u}, G.MinDegree d →
    ∀ H : FiniteGraph.{u}, SourceFamily false G H ↔ SourceFamily true G H

private theorem P_six : P.{u} 6 := by
  intro G hd H
  constructor
  · rintro ⟨K, h, e⟩
    exact ⟨K, (source_degree_six_histories hd).mp h, e⟩
  · rintro ⟨K, h, e⟩
    exact ⟨K, (source_degree_six_histories hd).mpr h, e⟩

private theorem P_below_six (d : ℕ) (hd : d < 6) : ¬ P.{u} d := by
  intro hp
  -- Certify the seven-vertex seed and its degree.
  have seed_exact :
      seed.active = range 7 ∧
        seed.edges = ((range 7).sym2.filter fun e => ¬ e.IsDiag) \ {s(0, 6), s(1, 4)} := by
    decide
  have seed_valid : seed.Valid := by
    intro x y h
    unfold State.Adj at h
    rw [seed_exact.2] at h
    obtain ⟨hm, hn⟩ := mem_filter.mp (mem_sdiff.mp h).1
    obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hm
    exact ⟨seed_exact.1 ▸ hx, seed_exact.1 ▸ hy, fun he => hn (by simp [he])⟩
  have seed_minimum_deg : seed.MinDegree 5 ∧ seed.degree 0 = 5 := by
    change (∀ x ∈ seed.active, 5 ≤ seed.degree x) ∧ seed.degree 0 = 5
    decide
  -- The first four moves are strong, including the reverse at 0.
  have witness_step1 : Move true seed after1 := by
    apply Move.forward
    change triple012.verts ⊆ seed.active ∧ 7 ∉ seed.active ∧ triple012.pairs ⊆ seed.edges
    decide
  have witness_step2 : Move true after1 after2 := by
    apply Move.forward
    change triple034.verts ⊆ after1.active ∧ 8 ∉ after1.active ∧ triple034.pairs ⊆ after1.edges
    decide
  have witness_step3 : Move true after2 after3 := by
    apply Move.reverse
    · change 0 ∈ after2.active ∧ after2.neighbors 0 = triple578.verts
      decide
    · intro _
      change Disjoint after2.edges triple578.pairs
      decide
  have witness_step4 : Move true after3 after4 := by
    apply Move.forward
    change triple157.verts ⊆ after3.active ∧ 9 ∉ after3.active ∧ triple157.pairs ⊆ after3.edges
    decide
  -- The reverse at 1 has exactly one preexisting neighbor pair.
  have witness_last_pair_overlap :
      after4.neighbors 1 = triple369.verts ∧
        after4.Adj 3 6 ∧ ¬ after4.Adj 3 9 ∧ ¬ after4.Adj 6 9 := by
    decide
  have witness_step5 : Move false after4 after5 := by
    apply Move.reverse
    · exact ⟨by decide, witness_last_pair_overlap.1⟩
    · intro he
      contradiction
  have witness_counts :
      [seed.edges.card, after1.edges.card, after2.edges.card, after3.edges.card,
        after4.edges.card, after5.edges.card] = [19, 19, 19, 19, 19, 18] := by
    decide
  have witness_history : Reach false seed after5 :=
    (strong_to_ordinary ((((ReflTransGen.single witness_step1).tail witness_step2).tail
      witness_step3).tail witness_step4)).tail witness_step5
  -- An isomorphic endpoint of a strong history would preserve the count.
  let S := seed.asFiniteGraph.{u} seed_valid
  have hE := reach_valid witness_history seed_valid
  let E := after5.asFiniteGraph.{u} hE
  have hsd : S.MinDegree d := by
    intro x
    rw [FiniteGraph.Degree, iso_degree_of_state seed_valid (asFiniteGraph_iso seed_valid)]
    exact (show d ≤ 5 by omega).trans (seed_minimum_deg.1 _ (x.down).2)
  have hreach : SourceFamily false S E :=
    ⟨E, realize_source_history seed_valid witness_history, ⟨SimpleGraph.Iso.refl⟩⟩
  obtain ⟨K, hK, ⟨i⟩⟩ := (hp S hsd E).mp hreach
  have hcancel : S.edgeCount = E.edgeCount :=
    (source_strong_edge_count hK).symm.trans (finiteGraph_iso_edges i)
  have no : seed.edges.card ≠ after5.edges.card := by
    have hc := witness_counts
    simp only [List.cons.injEq] at hc
    omega
  exact no ((iso_edges_of_state seed_valid (asFiniteGraph_iso seed_valid)).symm.trans
    (hcancel.trans (iso_edges_of_state hE (asFiniteGraph_iso hE))))

theorem zhou_sharp_threshold : P.{u} 6 ∧ ∀ d : ℕ, d < 6 → ¬ P.{u} d :=
  ⟨P_six, P_below_six⟩

end DeltaY
