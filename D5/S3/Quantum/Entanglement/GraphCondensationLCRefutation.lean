/- GID: D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphCondensationLCRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.claim; result=D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.result; claim=D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.claim
   digest: Refutes Conjecture 16 on LC-equivalence of condensed graphs (2406.09956). -/

/-
proof_shape: result: content
escape_witness: form (2), induction over local-complementation sequences inside result:
  the family consisting of the complete graph and the stars is invariant, whereas the
  condensation of the second six-vertex graph belongs to none of these graphs.
admission_basis: open-problem-resolution (#11473; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lc
  D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lcSeq
  Frozen module statement_id: sha256:81981077a3cd56f484109eb63008d9318f6a36c1c70e0df494f9f09515aef166
  Definitions only; no frozen theorem is applied.
-/

import Mathlib.Combinatorics.SimpleGraph.Star
import D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Quantum.Entanglement.GraphCondensationLCRefutation

open GraphStateMonogamyForbiddenSubgraph (lc lcSeq)

/-- Definition 13: replace C by a fresh vertex, retaining outside edges and joining the
fresh vertex to an outside vertex precisely when it has a neighbour in C. -/
def condense {V : Type} (G : SimpleGraph V) (C : Finset V) :
    SimpleGraph (Option {v : V // v ∉ C}) where
  Adj a b := match a, b with
    | none, none => False
    | some i, some j => G.Adj i.val j.val
    | some i, none => ∃ s ∈ C, G.Adj i.val s
    | none, some j => ∃ s ∈ C, G.Adj j.val s
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by intro a; cases a <;> simp [G.loopless.irrefl]⟩

/-- LC-equivalence means reaching the second graph by finitely many local complementations. -/
def LCEquivalent {V : Type} (G H : SimpleGraph V) : Prop :=
  ∃ s : List V, H = lcSeq G s

open Classical in
/-- Conjecture 16, with the outside-neighbour bound imposed on both connected graphs. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V) (C : Finset V),
    G.Connected → H.Connected →
    (∀ s ∈ C, (Finset.univ.filter fun i => i ∉ C ∧ G.Adj s i).card ≤ 1) →
    (∀ s ∈ C, (Finset.univ.filter fun i => i ∉ C ∧ H.Adj s i).card ≤ 1) →
    LCEquivalent G H → LCEquivalent (condense G C) (condense H C)

private def firstGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b => (a.val, b.val) ∈
    ([(0, 1), (0, 2), (0, 5), (1, 4), (2, 3)] : List (ℕ × ℕ))

private def secondGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b => (a.val, b.val) ∈
    ([(0, 5), (1, 4), (2, 3), (3, 5), (4, 5)] : List (ℕ × ℕ))

private instance firstGraphDec : DecidableRel firstGraph.Adj :=
  fun a b => by unfold firstGraph; infer_instance

private instance secondGraphDec : DecidableRel secondGraph.Adj :=
  fun a b => by unfold secondGraph; infer_instance

private def condensationSet : Finset (Fin 6) := {0, 1, 2}

/-- A six-vertex counterexample refutes Conjecture 16. -/
theorem result : ¬ claim := by
  intro hclaim
  have hfirst : firstGraph.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
    refine ⟨0, ?_⟩
    intro v
    fin_cases v
    · exact .rfl
    · exact (show firstGraph.Adj 0 1 by decide).reachable
    · exact (show firstGraph.Adj 0 2 by decide).reachable
    · exact (show firstGraph.Adj 0 2 by decide).reachable.trans
        (show firstGraph.Adj 2 3 by decide).reachable
    · exact (show firstGraph.Adj 0 1 by decide).reachable.trans
        (show firstGraph.Adj 1 4 by decide).reachable
    · exact (show firstGraph.Adj 0 5 by decide).reachable
  have hsecond : secondGraph.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
    refine ⟨5, ?_⟩
    intro v
    fin_cases v
    · exact (show secondGraph.Adj 5 0 by decide).reachable
    · exact (show secondGraph.Adj 5 4 by decide).reachable.trans
        (show secondGraph.Adj 4 1 by decide).reachable
    · exact (show secondGraph.Adj 5 3 by decide).reachable.trans
        (show secondGraph.Adj 3 2 by decide).reachable
    · exact (show secondGraph.Adj 5 3 by decide).reachable
    · exact (show secondGraph.Adj 5 4 by decide).reachable
    · exact .rfl
  have hseq : LCEquivalent firstGraph secondGraph := by
    refine ⟨[0, 1, 2, 3, 4, 5], ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      dsimp only [lcSeq, List.foldl_cons, List.foldl_nil, lc, firstGraph,
        secondGraph, SimpleGraph.fromRel]
    all_goals simp
  classical
  have hbound : ∀ G ∈ ([firstGraph, secondGraph] : List (SimpleGraph (Fin 6))),
      ∀ s ∈ condensationSet,
        (Finset.univ.filter fun i => i ∉ condensationSet ∧ G.Adj s i).card ≤ 1 := by
    classical
    intro G hG s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with rfl | rfl
    all_goals
      apply Finset.card_le_one_iff_subset_singleton.mpr
      refine ⟨![5, 4, 3, 0, 0, 0] s, ?_⟩
      intro i hi
      fin_cases s <;> fin_cases i <;>
        simp_all [condensationSet, firstGraph, secondGraph, SimpleGraph.fromRel]
  have hcond := hclaim (Fin 6) firstGraph secondGraph condensationSet hfirst hsecond
    (hbound firstGraph (by simp)) (hbound secondGraph (by simp)) hseq
  -- Stars and the complete graph form a family closed under local complementation.
  have closed : ∀ {V : Type} (G : SimpleGraph V),
      (G = ⊤ ∨ ∃ c, G = SimpleGraph.starGraph c) → ∀ v, lc G v = ⊤ ∨ ∃ c, lc G v = SimpleGraph.starGraph c := by
    intro V G h v
    rcases h with rfl | ⟨c, rfl⟩
    · right
      refine ⟨v, ?_⟩
      ext a b
      by_cases hab : a = b <;> by_cases hav : a = v <;> by_cases hbv : b = v <;>
        simp_all [lc, SimpleGraph.starGraph_adj, SimpleGraph.top_adj, eq_comm]
    · by_cases hvc : v = c
      · subst v
        left
        ext a b
        by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
          simp_all [lc, SimpleGraph.starGraph_adj, SimpleGraph.top_adj, eq_comm]
      · right
        refine ⟨c, ?_⟩
        ext a b
        by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
          simp_all [lc, SimpleGraph.starGraph_adj, eq_comm]
  have invariant : ∀ {V : Type} (s : List V) (G : SimpleGraph V),
      (G = ⊤ ∨ ∃ c, G = SimpleGraph.starGraph c) → lcSeq G s = ⊤ ∨ ∃ c, lcSeq G s = SimpleGraph.starGraph c := by
    intro V s
    induction s with
    | nil => intro G h; exact h
    | cons v s ih => intro G h; exact ih (lc G v) (closed G h v)
  have hstar : condense firstGraph condensationSet = SimpleGraph.starGraph none := by
    ext a b
    cases a with
    | none =>
      cases b with
      | none => simp [condense, SimpleGraph.starGraph_adj]
      | some b =>
        rcases b with ⟨b, hb⟩
        fin_cases b <;> simp [condensationSet] at hb <;>
          simp [condense, SimpleGraph.starGraph_adj, firstGraph, SimpleGraph.fromRel, condensationSet]
    | some a =>
      rcases a with ⟨a, ha⟩
      cases b with
      | none =>
        fin_cases a <;> simp [condensationSet] at ha <;>
          simp [condense, SimpleGraph.starGraph_adj, firstGraph, SimpleGraph.fromRel, condensationSet]
      | some b =>
        rcases b with ⟨b, hb⟩
        fin_cases a <;> fin_cases b <;> simp [condensationSet] at ha hb <;>
          simp [condense, SimpleGraph.starGraph_adj, firstGraph, SimpleGraph.fromRel]
  obtain ⟨s, hs⟩ := hcond
  have hfam := invariant s (condense firstGraph condensationSet) (Or.inr ⟨none, hstar⟩)
  rw [← hs] at hfam
  let v3 : {v : Fin 6 // v ∉ condensationSet} := ⟨3, by decide⟩
  let v4 : {v : Fin 6 // v ∉ condensationSet} := ⟨4, by decide⟩
  let v5 : {v : Fin 6 // v ∉ condensationSet} := ⟨5, by decide⟩
  rcases hfam with htop | ⟨c, hc⟩
  · have h34 := congrArg (fun G => G.Adj (some v3) (some v4)) htop
    simp [condense, secondGraph, SimpleGraph.fromRel, v3, v4] at h34
  · cases c with
    | none =>
      have h35 := congrArg (fun G => G.Adj (some v3) (some v5)) hc
      simp [condense, secondGraph, SimpleGraph.fromRel, SimpleGraph.starGraph_adj, v3, v5] at h35
    | some c =>
      rcases c with ⟨c, hcC⟩
      fin_cases c <;> simp [condensationSet] at hcC
      · have h04 := congrArg (fun G => G.Adj none (some v4)) hc
        simp [condense, secondGraph, SimpleGraph.fromRel, condensationSet, SimpleGraph.starGraph_adj, v4] at h04
        exact (by decide : (4 : Fin 6) ≠ 3) (congrArg Subtype.val h04)
      · have h03 := congrArg (fun G => G.Adj none (some v3)) hc
        simp [condense, secondGraph, SimpleGraph.fromRel, condensationSet, SimpleGraph.starGraph_adj, v3] at h03
        exact (by decide : (3 : Fin 6) ≠ 4) (congrArg Subtype.val h03)
      · have h03 := congrArg (fun G => G.Adj none (some v3)) hc
        simp [condense, secondGraph, SimpleGraph.fromRel, condensationSet, SimpleGraph.starGraph_adj, v3] at h03
        exact (by decide : (3 : Fin 6) ≠ 5) (congrArg Subtype.val h03)

end D5.S3.Quantum.Entanglement.GraphCondensationLCRefutation
