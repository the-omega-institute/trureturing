/- GID: D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance
   mirror-E: none(waiver:symbolic-distance-identity)
   anchors: []
   utility: none
   digest: The dyadic distance weights of the leaves of a complete binary tree have an exact sum. -/

import D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-! The dyadic distance sum over the leaves of a complete binary tree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph
open D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry

namespace D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

/-- Words joined by extension by one bit. -/
def wordTree : SimpleGraph (List Bool) :=
  SimpleGraph.fromRel (fun p q => ∃ b : Bool, q = p ++ [b])

private theorem child_adj (p : List Bool) (b : Bool) : wordTree.Adj p (p ++ [b]) := by
  rw [wordTree, fromRel_adj]
  refine ⟨?_, Or.inl ⟨b, rfl⟩⟩
  intro h
  have := congrArg List.length h
  simp at this

private def wordDist : List Bool → List Bool → ℕ
  | [], ys => ys.length
  | _ :: xs, [] => xs.length + 1
  | x :: xs, y :: ys => if x = y then wordDist xs ys else xs.length + ys.length + 2

private theorem wordDist_eq_prefixDistance (x y : List Bool) :
    wordDist x y = distance x y := by
  induction x generalizing y with
  | nil => simp [wordDist, distance, lcp]
  | cons a xs ih =>
    cases y with
    | nil => simp [wordDist, distance, lcp]
    | cons b ys =>
      by_cases h : a = b
      · have hLeft := (shortest_pop_append xs ys).1.1.length_le
        have hRight := (shortest_pop_append xs ys).1.2.1.length_le
        rw [wordDist, ite_eq_left h, ih]
        simp only [distance, lcp, ite_eq_left h, List.length_cons]
        omega
      · simp [wordDist, distance, lcp, h]
        omega

private theorem step_adj {x y : Word} (h : Step x y) : wordTree.Adj x y := by
  cases h with
  | append _ b => exact child_adj _ b
  | pop _ b => exact (child_adj _ b).symm

private theorem adj_step {x y : Word} (h : wordTree.Adj x y) : Step x y := by
  rw [wordTree, fromRel_adj] at h
  rcases h.2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact .append x b
  · exact .pop y b

private def pathWalk {x y : Word} : Path x y → wordTree.Walk x y
  | .nil _ => .nil
  | .cons h p => .cons (step_adj h) (pathWalk p)

private def walkPath {x y : Word} : wordTree.Walk x y → Path x y
  | .nil => .nil _
  | .cons h p => .cons (adj_step h) (walkPath p)

private theorem pathWalk_length {x y : Word} (p : Path x y) :
    (pathWalk p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathWalk, Path.length, ih]

private theorem walkPath_length {x y : Word} (p : wordTree.Walk x y) :
    (walkPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkPath, Path.length, ih]

private theorem pathWalk_support {x y : Word} {k : ℕ} (p : Path x y)
    (h : p.Within k) : ∀ z ∈ (pathWalk p).support, z.length ≤ k := by
  induction p with
  | nil w =>
    intro z hz
    change z ∈ [w] at hz
    obtain rfl := List.mem_singleton.mp hz
    exact h
  | @cons x v y edge p ih =>
    intro z hz
    change z ∈ x :: (pathWalk p).support at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact ih h.2 z hz

/-- The complete tree truncated at depth k. -/
abbrev boundedWordTree (k : ℕ) : SimpleGraph {x : List Bool // x.length ≤ k} :=
  wordTree.induce {x : List Bool | x.length ≤ k}

private theorem finite_distance_eq (k : ℕ) (x y : {x : List Bool // x.length ≤ k}) :
    (boundedWordTree k).dist x y = wordDist x.1 y.1 := by
  obtain ⟨_, hLower, p, hp, hCap⟩ := shortest_pop_append x.1 y.1
  let vertices : Set (List Bool) := {x | x.length ≤ k}
  let pFull := pathWalk p
  have hIn : ∀ z ∈ pFull.support, z ∈ vertices := fun z hz =>
    (pathWalk_support p hCap z hz).trans (max_le x.2 y.2)
  let pIn : (boundedWordTree k).Walk x y := pFull.induce vertices hIn
  have hLen : pIn.length = p.length := by
    change (pFull.induce vertices hIn).length = p.length
    rw [← Walk.length_map (Embedding.induce vertices).toHom, Walk.map_induce]
    exact pathWalk_length p
  obtain ⟨q, hq⟩ := (show (boundedWordTree k).Reachable x y from ⟨pIn⟩).exists_walk_length_eq_dist
  have hShortest : distance x.1 y.1 ≤ q.length := by
    let qFull := q.map (Embedding.induce vertices).toHom
    calc
      _ ≤ (walkPath qFull).length := hLower (walkPath qFull)
      _ = qFull.length := walkPath_length qFull
      _ = q.length := Walk.length_map _ _
  rw [wordDist_eq_prefixDistance]
  exact ((boundedWordTree k).dist_le pIn).trans_eq (hLen.trans hp) |>.antisymm (hq ▸ hShortest)

/-- The list of leaves of the complete tree of depth k. -/
def leafWords : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (leafWords k).map (false :: ·) ++ (leafWords k).map (true :: ·)

private theorem length_leafWords (k : ℕ) : (leafWords k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [leafWords, ih, pow_succ, Nat.mul_two]

private theorem length_of_mem_leafWords {k : ℕ} {x : List Bool} (hx : x ∈ leafWords k) :
    x.length = k := by
  induction k generalizing x with
  | zero =>
    have h : x = [] := by simpa [leafWords] using hx
    simp [h]
  | succ k ih =>
    rw [leafWords, List.mem_append] at hx
    rcases hx with hx | hx <;> obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx <;> simp [ih hy]

private theorem sum_constant_on {A : Type*} (xs : List A) (f : A → ℚ) (c : ℚ)
    (h : ∀ x ∈ xs, f x = c) : (xs.map f).sum = (xs.length : ℚ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    ring

private theorem cancel_pow_two (k : ℕ) :
    (↑(2 ^ k : ℕ) : ℚ) * (1 / 2 : ℚ) ^ k = 1 := by
  push_cast
  rw [← mul_pow]
  norm_num

private theorem weight_other_branch (a b : Bool) (h : a ≠ b) (xs : List Bool) (k : ℕ) :
    ((leafWords k).map (fun ys => (1 / 2 : ℚ) ^ wordDist (a :: xs) (b :: ys))).sum =
      (1 / 2 : ℚ) ^ (xs.length + 2) := by
  rw [sum_constant_on _ _ ((1 / 2 : ℚ) ^ (xs.length + k + 2)), length_leafWords]
  · rw [show xs.length + k + 2 = k + (xs.length + 2) by omega, pow_add,
      ← mul_assoc, cancel_pow_two, one_mul]
  · intro y hy
    simp [wordDist, h, length_of_mem_leafWords hy]

private theorem weight_wordDist (k : ℕ) (x : List Bool) (hx : x.length ≤ k) :
    ((leafWords k).map (fun y => (1 / 2 : ℚ) ^ wordDist x y)).sum =
      3 / 2 - (1 / 2 : ℚ) ^ (x.length + 1) := by
  induction x generalizing k with
  | nil =>
    rw [sum_constant_on _ _ ((1 / 2 : ℚ) ^ k), length_leafWords, cancel_pow_two]
    · norm_num
    · intro y hy
      simp [wordDist, length_of_mem_leafWords hy]
  | cons a xs ih =>
    cases k with
    | zero => simp at hx
    | succ k =>
      have hxs : xs.length ≤ k := by simpa using hx
      have hs := ih k hxs
      have hWeight :
          ((leafWords k).map (fun ys => (1 / 2 : ℚ) ^ wordDist (a :: xs) (a :: ys))).sum =
            3 / 2 - (1 / 2 : ℚ) ^ (xs.length + 1) := by
        simpa only [wordDist, ite_true] using hs
      rw [leafWords, List.map_append, List.sum_append, List.map_map, List.map_map]
      cases a with
      | false =>
        rw [Function.comp_def, Function.comp_def, hWeight, weight_other_branch false true (by decide)]
        simp only [List.length_cons, pow_succ _ (xs.length + 1)]
        ring
      | true =>
        rw [Function.comp_def, Function.comp_def, weight_other_branch true false (by decide), hWeight]
        simp only [List.length_cons, pow_succ _ (xs.length + 1)]
        ring

private theorem leafWord_of_length {k : ℕ} {x : List Bool} (hx : x.length = k) :
    x ∈ leafWords k := by
  induction k generalizing x with
  | zero =>
    have h := List.length_eq_zero_iff.mp hx
    simp [h, leafWords]
  | succ k ih =>
    rcases x with _ | ⟨b, x⟩
    · simp at hx
    · have h : x.length = k := by simpa using hx
      cases b <;> simp [leafWords, List.mem_append, List.mem_map, ih h]

private theorem nodup_leafWords (k : ℕ) : (leafWords k).Nodup := by
  induction k with
  | zero => simp [leafWords]
  | succ k ih =>
    rw [leafWords]
    apply (ih.map List.cons_injective).append (ih.map List.cons_injective)
    apply List.disjoint_iff_ne.mpr
    intro x hx y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
    simp

/-- The leaf list contains each depth-k word once, and the dyadic distance sum depends
only on the depth of the starting vertex. -/
theorem weighted_leaf_distance (k : ℕ) (x : {x : List Bool // x.length ≤ k}) :
    (leafWords k).Nodup ∧
    (∀ y : List Bool, y ∈ leafWords k ↔ y.length = k) ∧
    ((leafWords k).attach.map (fun y => (1 / 2 : ℚ) ^
      (boundedWordTree k).dist x ⟨y.1, (length_of_mem_leafWords y.2).le⟩)).sum =
      3 / 2 - (1 / 2 : ℚ) ^ (x.1.length + 1) := by
  refine ⟨nodup_leafWords k, fun y => ⟨length_of_mem_leafWords, leafWord_of_length⟩, ?_⟩
  have he :
      (leafWords k).attach.map (fun y => (1 / 2 : ℚ) ^
        (boundedWordTree k).dist x ⟨y.1, (length_of_mem_leafWords y.2).le⟩) =
      (leafWords k).map (fun y => (1 / 2 : ℚ) ^ wordDist x.1 y) := by
    calc
      _ = (leafWords k).attach.map ((fun y => (1 / 2 : ℚ) ^ wordDist x.1 y) ∘ Subtype.val) := by
        apply List.map_congr_left
        intro y _
        rw [finite_distance_eq]
        rfl
      _ = _ := by rw [← List.map_map]; simp
  rw [he, weight_wordDist k x.1 x.2]

end D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
