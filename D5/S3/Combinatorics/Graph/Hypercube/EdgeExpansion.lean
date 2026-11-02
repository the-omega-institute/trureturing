/- GID: D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/EdgeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every vertex set of the Boolean cube has at least its smaller side many boundary edges. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The cube is the iterated Cartesian product of the two-vertex graph. Boundary
edges are oriented from the chosen set to its complement, so each is counted once. -/

namespace D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion

open scoped symmDiff
open scoped Classical

noncomputable section

/-- Recursive coordinates for the Boolean cube. -/
@[reducible] def Vertex : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Vertex n

instance vertexFintype (n : ℕ) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Bool × Vertex n))

instance vertexDecidableEq (n : ℕ) : DecidableEq (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Bool × Vertex n))

/-- The vertices lying in one of the two coordinate halves. -/
def slice (n : ℕ) (b : Bool) (W : Finset (Vertex (n + 1))) : Finset (Vertex n) :=
  Finset.univ.filter fun x => (show Vertex (n + 1) from (b, x)) ∈ W

/-- Count boundary edges recursively: the two internal boundaries and the matching
between the halves. An edge in that matching crosses precisely on the symmetric difference. -/
def edgeBoundary : (n : ℕ) → Finset (Vertex n) → ℕ
  | 0, _ => 0
  | n + 1, W => edgeBoundary n (slice n false W) + edgeBoundary n (slice n true W) +
      (slice n false W ∆ slice n true W).card

/-- Two recursive bit strings differ in exactly one coordinate. -/
def Adjacent : (n : ℕ) → Vertex n → Vertex n → Prop
  | 0, _, _ => False
  | n + 1, (b, x), (c, y) => (b = c ∧ Adjacent n x y) ∨ (b ≠ c ∧ x = y)

private theorem adjacent_symm (n : ℕ) (x y : Vertex n) :
    Adjacent n x y → Adjacent n y x := by
  induction n with
  | zero => exact False.elim
  | succ n ih =>
      rcases x with ⟨b, x⟩
      rcases y with ⟨c, y⟩
      rintro (⟨hbc, hxy⟩ | ⟨hbc, hxy⟩)
      · exact Or.inl ⟨hbc.symm, ih x y hxy⟩
      · exact Or.inr ⟨Ne.symm hbc, hxy.symm⟩

private theorem adjacent_irrefl (n : ℕ) (x : Vertex n) : ¬ Adjacent n x x := by
  induction n with
  | zero => exact not_false
  | succ n ih =>
      rcases x with ⟨b, x⟩
      simp [Adjacent, ih]

/-- The Boolean cube, with the two halves joined by the coordinate matching. -/
def cubeGraph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := Adjacent n
  symm := ⟨adjacent_symm n⟩
  loopless := ⟨adjacent_irrefl n⟩

/-- Actual crossing edges, oriented from the endpoint in W to the endpoint outside W.
The opposite orientation cannot belong to this set. -/
def boundaryEdges (n : ℕ) (W : Finset (Vertex n)) : Finset (Vertex n × Vertex n) :=
  Finset.univ.filter fun p => (cubeGraph n).Adj p.1 p.2 ∧ p.1 ∈ W ∧ p.2 ∉ W

private theorem mem_boundaryEdges (n : ℕ) (W : Finset (Vertex n))
    (p : Vertex n × Vertex n) :
    p ∈ boundaryEdges n W ↔ Adjacent n p.1 p.2 ∧ p.1 ∈ W ∧ p.2 ∉ W := by
  change p ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ p)

private theorem mem_slice (n : ℕ) (b : Bool) (W : Finset (Vertex (n + 1)))
    (x : Vertex n) : x ∈ slice n b W ↔ (b, x) ∈ W := by
  change x ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ x)

private theorem vertex_card (n : ℕ) : Fintype.card (Vertex n) = 2 ^ n := by
  induction n with
  | zero =>
      change Fintype.card Unit = 1
      exact Fintype.card_unique
  | succ n ih =>
      change Fintype.card (Bool × Vertex n) = 2 ^ (n + 1)
      rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
      omega

private theorem card_le (n : ℕ) (W : Finset (Vertex n)) : W.card ≤ 2 ^ n := by
  simpa [vertex_card] using Finset.card_le_univ W

private theorem slice_cards (n : ℕ) (W : Finset (Vertex (n + 1))) :
    W.card = (slice n false W).card + (slice n true W).card := by
  let f : Vertex n → Vertex (n + 1) := fun x => (false, x)
  let t : Vertex n → Vertex (n + 1) := fun x => (true, x)
  have hf : Function.Injective f := fun x y h => congrArg Prod.snd h
  have ht : Function.Injective t := fun x y h => congrArg Prod.snd h
  have hd : Disjoint ((slice n false W).image f) ((slice n true W).image t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have := congrArg Prod.fst (ha.trans hb.symm)
    simp [f, t] at this
  have hw : W = (slice n false W).image f ∪ (slice n true W).image t := by
    ext x
    rcases x with ⟨b, x⟩
    cases b <;>
      simp only [Finset.mem_union, Finset.mem_image, slice, Finset.mem_filter,
        Finset.mem_univ, true_and, f, t] <;> aesop
  calc
    W.card = ((slice n false W).image f ∪ (slice n true W).image t).card :=
      congrArg Finset.card hw
    _ = (slice n false W).card + (slice n true W).card := by
      rw [Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ ht]

private theorem matching_bound {α : Type*} [DecidableEq α] (A B : Finset α) :
    A.card ≤ B.card + (A ∆ B).card ∧ B.card ≤ A.card + (A ∆ B).card := by
  have hA : A ⊆ B ∪ (A ∆ B) := by
    intro x hx
    by_cases hB : x ∈ B
    · exact Finset.mem_union_left _ hB
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hx, hB⟩))
  have hB : B ⊆ A ∪ (A ∆ B) := by
    intro x hx
    by_cases hA : x ∈ A
    · exact Finset.mem_union_left _ hA
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hx, hA⟩))
  exact ⟨(Finset.card_le_card hA).trans (Finset.card_union_le _ _),
    (Finset.card_le_card hB).trans (Finset.card_union_le _ _)⟩

private theorem boundary_edges_succ (n : ℕ) (W : Finset (Vertex (n + 1))) :
    (boundaryEdges (n + 1) W).card =
      (boundaryEdges n (slice n false W)).card +
      (boundaryEdges n (slice n true W)).card +
      (slice n false W ∆ slice n true W).card := by
  let A := slice n false W
  let B := slice n true W
  let lift (b : Bool) (p : Vertex n × Vertex n) : Vertex (n + 1) × Vertex (n + 1) :=
    ((b, p.1), (b, p.2))
  let matching (x : Vertex n) : Vertex (n + 1) × Vertex (n + 1) :=
    ((decide (x ∉ A), x), (!decide (x ∉ A), x))
  have hl (b : Bool) : Function.Injective (lift b) := by
    intro p q h
    exact congrArg (fun r => (r.1.2, r.2.2)) h
  have hm : Function.Injective matching := by
    intro x y h
    exact congrArg (fun r => r.1.2) h
  have hd : Disjoint ((boundaryEdges n A).image (lift false))
      ((boundaryEdges n B).image (lift true)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hq
    have := congrArg (fun r => r.1.1) (hx.trans hy.symm)
    simp [lift] at this
  have hdM (b : Bool) (S : Finset (Vertex n × Vertex n)) :
      Disjoint (S.image (lift b)) ((A ∆ B).image matching) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hq
    have h := congrArg (fun r => (r.1.1, r.2.1)) (hx.trans hy.symm)
    cases b <;> by_cases hyA : y ∈ A <;> simp [lift, matching, hyA] at h
  have hw : boundaryEdges (n + 1) W =
      (boundaryEdges n A).image (lift false) ∪
      (boundaryEdges n B).image (lift true) ∪ (A ∆ B).image matching := by
    ext p
    rw [mem_boundaryEdges (n + 1) W]
    rcases p with ⟨⟨b, x⟩, ⟨c, y⟩⟩
    cases b <;> cases c <;>
      simp only [Finset.mem_union, Finset.mem_image,
        mem_boundaryEdges n A, mem_boundaryEdges n B]
    all_goals
      simp [Adjacent, lift, matching, A, B, mem_slice,
        Finset.mem_symmDiff, Prod.mk.injEq] <;> aesop
  calc
    (boundaryEdges (n + 1) W).card =
        ((boundaryEdges n A).image (lift false) ∪
          (boundaryEdges n B).image (lift true) ∪ (A ∆ B).image matching).card :=
      congrArg Finset.card hw
    _ = (boundaryEdges n A).card + (boundaryEdges n B).card + (A ∆ B).card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdM _ _, hdM _ _⟩),
        Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (hl false),
        Finset.card_image_of_injective _ (hl true), Finset.card_image_of_injective _ hm]

private theorem boundary_count (n : ℕ) (W : Finset (Vertex n)) :
    edgeBoundary n W = (boundaryEdges n W).card := by
  induction n with
  | zero => simp [edgeBoundary, boundaryEdges, cubeGraph, Adjacent]
  | succ n ih =>
      rw [boundary_edges_succ, edgeBoundary, ih, ih]

/-- Every subset of the Boolean n-cube has at least the smaller side's cardinality
many edges leaving it. Dimension zero and empty or full sets are included. -/
private theorem recursive_expansion (n : ℕ) (W : Finset (Vertex n)) :
    min W.card (2 ^ n - W.card) ≤ edgeBoundary n W := by
  induction n with
  | zero =>
      have hW := card_le 0 W
      simp only [pow_zero] at hW ⊢
      simp only [edgeBoundary]
      omega
  | succ n ih =>
      let A := slice n false W
      let B := slice n true W
      have hA := card_le n A
      have hB := card_le n B
      have heA := ih A
      have heB := ih B
      have hm := matching_bound A B
      have hc := slice_cards n W
      change W.card = A.card + B.card at hc
      change min W.card (2 ^ (n + 1) - W.card) ≤
        edgeBoundary n A + edgeBoundary n B + (A ∆ B).card
      rw [hc, pow_succ]
      omega

/-- Every set of cube vertices has at least its smaller side many crossing edges.
Each edge occurs once, directed from W to its complement. -/
theorem edge_expansion (n : ℕ) (W : Finset (Vertex n)) :
    min W.card (2 ^ n - W.card) ≤ (boundaryEdges n W).card := by
  rw [← boundary_count]
  exact recursive_expansion n W

end

end D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion
