/- GID: D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.claim; result=D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.result; claim=D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.claim
   digest: A 29-vertex digraph at radius four refutes the even extension of Theorem 1.6. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
The even-radius question immediately after Theorem 1.6 in Penev, Stein and
Trujillo-Negrete, arXiv:2608.00825v1. The quantifiers and endpoint follow
preregistration issue #31451.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.PenevEvenQKernelRefutation

universe u

private abbrev asQuiver {V : Type u} (G : Digraph V) : Quiver.{0} V :=
  ⟨fun a b => PLift (G.Adj a b)⟩

private def Loopless {V : Type u} (G : Digraph V) : Prop :=
  ∀ v, ¬ G.Adj v v

private def Bipartite {V : Type u} (G : Digraph V) : Prop :=
  ∃ color : V → Bool, ∀ ⦃a b⦄, G.Adj a b → color a ≠ color b

private def SourceFree {V : Type u} (G : Digraph V) : Prop :=
  ∀ v, ∃ u, G.Adj u v

private def HasOutBranching {V : Type u} (G : Digraph V) : Prop :=
  ∃ T : Digraph V, T ≤ G ∧ Nonempty (@Quiver.Arborescence V (asQuiver T))

private def WalkWithin {V : Type u} (G : Digraph V) (q : ℕ) (a b : V) : Prop :=
  letI := asQuiver G
  ∃ p : Quiver.Path a b, p.length ≤ q

private def PathWithin {V : Type u} (G : Digraph V) (q : ℕ) (a b : V) : Prop :=
  letI := asQuiver G
  ∃ p : Quiver.Path a b, p.vertices.Nodup ∧ p.length ≤ q

private theorem PathWithin.toWalk {V : Type u} {G : Digraph V} {q : ℕ} {a b : V}
    (h : PathWithin G q a b) : WalkWithin G q a b := by
  obtain ⟨p, _, hlen⟩ := h
  exact ⟨p, hlen⟩

private def Independent {V : Type u} (G : Digraph V) (Q : Finset V) : Prop :=
  ∀ ⦃a b⦄, a ∈ Q → b ∈ Q → ¬ G.Adj a b

private def Covers {V : Type u} (G : Digraph V) (q : ℕ) (Q : Finset V) : Prop :=
  ∀ v, ∃ a ∈ Q, PathWithin G q a v

/-- The preregistered even extension of Theorem 1.6 on all finite digraphs.
Opposite arcs may coexist. The bound is the printed inequality multiplied by q + 1. -/
def claim : Prop :=
  ∀ (q : ℕ), Even q → 4 ≤ q →
  ∀ (V : Type) [Fintype V] (G : Digraph V),
    Loopless G → Bipartite G → SourceFree G → HasOutBranching G →
    ∃ Q : Finset V, Independent G Q ∧ Covers G q Q ∧
      (q + 1) * Q.card ≤ Fintype.card V + (q + 1)

/-- The 31 arcs on the supplied 29 vertices. -/
private def arcs : List (Fin 29 × Fin 29) :=
  [(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0),
   (6, 7), (6, 11), (6, 20), (7, 8), (8, 9), (9, 10),
   (11, 12), (12, 13), (13, 14), (14, 15), (15, 6), (15, 16),
   (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (22, 23),
   (23, 24), (24, 6), (24, 25), (25, 26), (26, 27), (27, 28)]

private def witness : Digraph (Fin 29) :=
  ⟨fun a b => (a, b) ∈ arcs⟩

private theorem witness_loopless : Loopless witness := by
  change ∀ v : Fin 29, (v, v) ∉ arcs
  decide

private def color (v : Fin 29) : Bool :=
  decide ((v.val + (if 6 ≤ v.val ∧ v.val ≤ 19 then 0 else 1)) % 2 = 0)

private theorem witness_bipartite : Bipartite witness := by
  refine ⟨color, ?_⟩
  change ∀ a b : Fin 29, (a, b) ∈ arcs → color a ≠ color b
  decide

private theorem witness_sourceFree : SourceFree witness := by
  change ∀ v : Fin 29, ∃ u : Fin 29, (u, v) ∈ arcs
  decide

private def parent (v : Fin 29) : Fin 29 :=
  if v = 6 then 0 else if v = 11 ∨ v = 20 then 6 else ⟨v.val - 1, by omega⟩

private theorem hasOutBranching_of_parent {V : Type u} {G : Digraph V}
    (root : V) (height : V → ℕ) (parent : V → V)
    (parent_lt : ∀ b, b ≠ root → height (parent b) < height b)
    (parent_arc : ∀ b, b ≠ root → G.Adj (parent b) b) : HasOutBranching G := by
  let tree : Digraph V := ⟨fun a b => b ≠ root ∧ a = parent b⟩
  refine ⟨tree, ?_, ⟨?_⟩⟩
  · intro a b e
    rcases e with ⟨hb, rfl⟩
    exact parent_arc b hb
  · letI := asQuiver tree
    refine Quiver.arborescenceMk root height ?_ ?_ ?_
    · intro a b e
      have e := e.down
      rw [e.2]
      exact parent_lt b e.1
    · intro a b c e f
      have h : a = b := e.down.2.trans f.down.2.symm
      subst b
      change PLift (tree.Adj a c) at e f
      exact ⟨rfl, heq_of_eq (Subsingleton.elim e f)⟩
    · intro b
      by_cases h : b = root
      · exact Or.inl h
      · exact Or.inr ⟨parent b, ⟨⟨h, rfl⟩⟩⟩

private theorem witness_hasOutBranching : HasOutBranching witness := by
  refine hasOutBranching_of_parent 0 Fin.val parent ?_ ?_
  · decide
  · change ∀ b : Fin 29, b ≠ 0 → (parent b, b) ∈ arcs
    decide

private def inNeighbors (b : Fin 29) : List (Fin 29) :=
  arcs.filterMap fun (a, c) => if c = b then some a else none

private theorem mem_inNeighbors {a b : Fin 29} :
    a ∈ inNeighbors b ↔ witness.Adj a b := by
  change _ ↔ (a, b) ∈ arcs
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := List.mem_filterMap.mp h
    by_cases hb : y = b
    · subst y
      simp at heq
      simpa [heq] using hxy
    · simp [hb] at heq
  · intro h
    exact List.mem_filterMap.mpr ⟨(a, b), h, by simp⟩

/-- Every predecessor at distance at most the given radius, including distance zero. -/
private def predecessors : ℕ → Fin 29 → List (Fin 29)
  | 0, b => [b]
  | n + 1, b => b :: (inNeighbors b).flatMap (predecessors n)

private theorem mem_predecessors_iff_walk (q : ℕ) (a b : Fin 29) :
    a ∈ predecessors q b ↔ WalkWithin witness q a b := by
  let := asQuiver witness
  change _ ↔ ∃ p : Quiver.Path a b, p.length ≤ q
  induction q generalizing b with
  | zero =>
    simp only [predecessors, List.mem_singleton, Nat.le_zero]
    exact ⟨fun h => h ▸ ⟨Quiver.Path.nil, rfl⟩,
      fun ⟨p, hp⟩ => p.eq_of_length_zero hp⟩
  | succ n ih =>
    simp only [predecessors, List.mem_cons, List.mem_flatMap, mem_inNeighbors]
    constructor
    · rintro (rfl | ⟨c, hc, h⟩)
      · exact ⟨Quiver.Path.nil, Nat.zero_le _⟩
      · obtain ⟨p, hp⟩ := (ih c).mp h
        exact ⟨p.cons ⟨hc⟩, Nat.succ_le_succ hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl rfl
      | @cons c b p e =>
        exact Or.inr ⟨c, e.down, (ih c).mpr ⟨p, Nat.le_of_succ_le_succ hp⟩⟩

private theorem pred_of_cover {Q : Finset (Fin 29)} (hQ : Covers witness 4 Q) (v : Fin 29) :
    ∃ a ∈ Q, a ∈ predecessors 4 v := by
  obtain ⟨a, ha, hp⟩ := hQ v
  exact ⟨a, ha, (mem_predecessors_iff_walk 4 a v).mpr hp.toWalk⟩

private def missedCycleVertex (a : Fin 29) : Fin 29 :=
  ⟨(a.val + 5) % 6, (Nat.mod_lt _ (by decide)).trans (by decide)⟩

private theorem cycle_predecessor (v : Fin 6) (a : Fin 29) :
    a ∈ predecessors 4 ⟨v.val, v.isLt.trans (by decide)⟩ → a.val < 6 := by
  revert v a
  decide

private theorem missed_cycle_is_uncovered (a : Fin 29) :
    a.val < 6 → a ∉ predecessors 4 (missedCycleVertex a) := by
  revert a
  decide

private theorem two_cycle_centers {Q : Finset (Fin 29)} (hQ : Covers witness 4 Q) :
    2 ≤ (Q.filter fun a => a.val < 6).card := by
  obtain ⟨a, haQ, ha⟩ := pred_of_cover hQ 0
  have haCycle := cycle_predecessor 0 a ha
  obtain ⟨b, hbQ, hb⟩ := pred_of_cover hQ (missedCycleVertex a)
  have hbCycle : b.val < 6 := cycle_predecessor ⟨_, Nat.mod_lt _ (by decide)⟩ b hb
  have hne : a ≠ b := fun h => missed_cycle_is_uncovered a haCycle (h.symm ▸ hb)
  have hsub : ({a, b} : Finset (Fin 29)) ⊆ Q.filter (fun v => v.val < 6) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨haQ, haCycle⟩
    · exact Finset.mem_filter.mpr ⟨hbQ, hbCycle⟩
  simpa [hne] using Finset.card_le_card hsub

private def tailDemand (hubSelected : Bool) (i : Fin 5) : Fin 29 :=
  if hubSelected then [6, 15, 19, 24, 28].get i else [10, 14, 19, 23, 28].get i

private def tailCandidates (hubSelected : Bool) (i : Fin 5) : List (Fin 29) :=
  if hubSelected && i == 0 then [6]
  else (predecessors 4 (tailDemand hubSelected i)).filter fun v =>
    if hubSelected then v != 15 && v != 24 else v != 6

private theorem tailCandidates_offCycle :
    ∀ (hubSelected : Bool) (i : Fin 5) (a : Fin 29),
      a ∈ tailCandidates hubSelected i → 6 ≤ a.val := by
  decide

private theorem tailCandidates_disjoint :
    ∀ (hubSelected : Bool) (i j : Fin 5) (a : Fin 29),
      i ≠ j → a ∈ tailCandidates hubSelected i → a ∉ tailCandidates hubSelected j := by
  decide

private theorem five_offCycle_centers {Q : Finset (Fin 29)}
    (hi : Independent witness Q) (hc : Covers witness 4 Q) :
    5 ≤ (Q.filter fun v => 6 ≤ v.val).card := by
  have arc15 : (15, 6) ∈ arcs := by decide
  have arc24 : (24, 6) ∈ arcs := by decide
  let hubSelected := decide ((6 : Fin 29) ∈ Q)
  have hasCenter (i : Fin 5) : ∃ a ∈ Q, a ∈ tailCandidates hubSelected i := by
    by_cases hh : (6 : Fin 29) ∈ Q
    · have htrue : hubSelected = true := decide_eq_true hh
      by_cases hz : i = 0
      · exact ⟨6, hh, by simp [tailCandidates, htrue, hz]⟩
      · obtain ⟨a, haQ, ha⟩ := pred_of_cover hc (tailDemand hubSelected i)
        have h15 : a ≠ 15 := fun e => hi haQ hh (e.symm ▸ arc15)
        have h24 : a ≠ 24 := fun e => hi haQ hh (e.symm ▸ arc24)
        exact ⟨a, haQ, by simpa [tailCandidates, htrue, hz, h15, h24] using ha⟩
    · have hfalse : hubSelected = false := decide_eq_false hh
      obtain ⟨a, haQ, ha⟩ := pred_of_cover hc (tailDemand hubSelected i)
      have h6 : a ≠ 6 := fun e => hh (e ▸ haQ)
      exact ⟨a, haQ, by simpa [tailCandidates, hfalse, h6] using ha⟩
  let center (i : Fin 5) := Classical.choose (hasCenter i)
  have hmem (i : Fin 5) : center i ∈ Q := (Classical.choose_spec (hasCenter i)).1
  have hpred (i : Fin 5) : center i ∈ tailCandidates hubSelected i :=
    (Classical.choose_spec (hasCenter i)).2
  let f (i : Fin 5) : ↥(Q.filter fun v => 6 ≤ v.val) :=
    ⟨center i, Finset.mem_filter.mpr ⟨hmem i, tailCandidates_offCycle _ i _ (hpred i)⟩⟩
  have hf : Function.Injective f := by
    intro i j heq
    have e : center i = center j := congrArg Subtype.val heq
    by_cases he : i = j
    · exact he
    · exact False.elim (tailCandidates_disjoint hubSelected i j (center i) he
        (hpred i) (e.symm ▸ hpred j))
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_coe] at h
  exact h

/-- Count the disjoint cycle and off-cycle portions of an arbitrary cover. -/
private theorem witness_lower_bound {Q : Finset (Fin 29)} (hi : Independent witness Q)
    (hc : Covers witness 4 Q) : 7 ≤ Q.card := by
  have hcycle := two_cycle_centers hc
  have htail := five_offCycle_centers hi hc
  have hpartition := Finset.card_filter_add_card_filter_not (s := Q) (p := fun v => v.val < 6)
  simp only [Nat.not_lt] at hpartition
  omega

private theorem witness_violates_bound :
    ¬ ∃ Q : Finset (Fin 29), Independent witness Q ∧ Covers witness 4 Q ∧
      (4 + 1) * Q.card ≤ Fintype.card (Fin 29) + (4 + 1) := by
  rintro ⟨Q, hi, hc, hcap⟩
  have hmin := witness_lower_bound hi hc
  simp only [Fintype.card_fin] at hcap
  omega

/-- The intact radius-four instance needs seven centers, while the bound allows six. -/
theorem result : ¬ claim := by
  intro h
  exact witness_violates_bound
    (h 4 ⟨2, rfl⟩ (by decide) (Fin 29) witness witness_loopless
      witness_bipartite witness_sourceFree witness_hasOutBranching)

end D5.S3.Combinatorics.Graph.Domination.PenevEvenQKernelRefutation
