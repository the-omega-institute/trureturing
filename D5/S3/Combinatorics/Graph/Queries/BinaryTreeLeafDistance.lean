/- GID: D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance
   mirror-E: none(waiver:symbolic-distance-identity)
   anchors: []
   utility: none
   digest: The inverse powers of two of distances from a vertex to the leaves of a complete binary tree have an exact sum. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-! The dyadic distance sum over the leaves of a complete binary tree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph

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

private theorem wordDist_self (x : List Bool) : wordDist x x = 0 := by
  induction x with
  | nil => rfl
  | cons b xs ih => simp [wordDist, ih]

private theorem child_difference (x y : List Bool) (b : Bool) :
    wordDist x y ≤ wordDist (x ++ [b]) y + 1 ∧
      wordDist (x ++ [b]) y ≤ wordDist x y + 1 := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp [wordDist]
    | cons c rest =>
      by_cases h : b = c
      · simp [wordDist, h]
        omega
      · simp [wordDist, h]
  | cons a rest ih =>
    cases y with
    | nil => simp [wordDist]
    | cons c tail =>
      by_cases h : a = c
      · simpa only [List.cons_append, wordDist, ite_eq_left h] using ih tail
      · simp [wordDist, h]
        omega

private theorem wordDist_le_walk {x y : List Bool} (p : wordTree.Walk x y) :
    wordDist x y ≤ p.length := by
  induction p with
  | nil => exact (wordDist_self _).le
  | @cons x z y edge walk ih =>
    have hStep : wordDist x y ≤ wordDist z y + 1 := by
      rw [wordTree, fromRel_adj] at edge
      rcases edge.2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact (child_difference x y b).1
      · exact (child_difference z y b).2
    simp only [Walk.length_cons]
    omega

private abbrev branch (b : Bool) : wordTree →g wordTree where
  toFun := List.cons b
  map_rel' := by
    intro x y edge
    rw [wordTree, fromRel_adj] at edge
    rcases edge.2 with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact child_adj (b :: x) a
    · exact (child_adj (b :: y) a).symm

private def fromRoot : ∀ x, wordTree.Walk [] x
  | [] => .nil
  | b :: xs => .cons (child_adj [] b) ((fromRoot xs).map (branch b))

private theorem fromRoot_length (x : List Bool) : (fromRoot x).length = x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    change ((fromRoot xs).map (branch b)).length + 1 = xs.length + 1
    rw [Walk.length_map, ih]

private theorem fromRoot_support (x : List Bool) :
    ∀ z ∈ (fromRoot x).support, z.length ≤ x.length := by
  induction x with
  | nil => simp [fromRoot]
  | cons b xs ih =>
    intro z hz
    change z ∈ [] :: ((fromRoot xs).map (branch b)).support at hz
    rcases List.mem_cons.mp hz with rfl | hm
    · simp
    · rw [Walk.support_map] at hm
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      exact Nat.succ_le_succ (ih y hy)

private theorem wordDist_achieved (x y : List Bool) :
    ∃ p : wordTree.Walk x y, p.length = wordDist x y ∧
      ∀ z ∈ p.support, z.length ≤ max x.length y.length := by
  induction x generalizing y with
  | nil =>
    exact ⟨fromRoot y, fromRoot_length y, fun z hz =>
      (fromRoot_support y z hz).trans (le_max_right _ _)⟩
  | cons a xs ih =>
    cases y with
    | nil =>
      refine ⟨(fromRoot (a :: xs)).reverse, by simp [fromRoot_length, wordDist], ?_⟩
      intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      exact (fromRoot_support (a :: xs) z hz).trans (le_max_left _ _)
    | cons b ys =>
      by_cases h : a = b
      · subst b
        obtain ⟨p, hp, hSupp⟩ := ih ys
        refine ⟨p.map (branch a), by simp [wordDist, hp], ?_⟩
        intro z hz
        change z ∈ (p.map (branch a)).support at hz
        rw [Walk.support_map] at hz
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
        have hc' := hSupp c hc
        change c.length + 1 ≤ max (xs.length + 1) (ys.length + 1)
        omega
      · refine ⟨(fromRoot (a :: xs)).reverse.append (fromRoot (b :: ys)), ?_, ?_⟩
        · simp [wordDist, h, fromRoot_length]
          omega
        · intro z hz
          rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hz
          exact hz.elim
            (fun hz => (fromRoot_support (a :: xs) z hz).trans (le_max_left _ _))
            (fun hz => (fromRoot_support (b :: ys) z hz).trans (le_max_right _ _))

/-- The complete tree truncated at depth k. -/
abbrev boundedWordTree (k : ℕ) : SimpleGraph {x : List Bool // x.length ≤ k} :=
  wordTree.induce {x : List Bool | x.length ≤ k}

private theorem finite_distance_eq (k : ℕ) (x y : {x : List Bool // x.length ≤ k}) :
    (boundedWordTree k).dist x y = wordDist x.1 y.1 := by
  obtain ⟨p, hp, hSupp⟩ := wordDist_achieved x.1 y.1
  let vertices : Set (List Bool) := {x | x.length ≤ k}
  have hIn : ∀ z ∈ p.support, z ∈ vertices := fun z hz =>
    (hSupp z hz).trans (max_le x.2 y.2)
  let pIn : (boundedWordTree k).Walk x y := p.induce vertices hIn
  have hLen : pIn.length = p.length := by
    change (p.induce vertices hIn).length = p.length
    rw [← Walk.length_map (Embedding.induce vertices).toHom, Walk.map_induce]
    rfl
  obtain ⟨q, hq⟩ := (show (boundedWordTree k).Reachable x y from ⟨pIn⟩).exists_walk_length_eq_dist
  have hLower : wordDist x.1 y.1 ≤ q.length := by
    have hm := wordDist_le_walk (q.map (Embedding.induce vertices).toHom)
    rwa [Walk.length_map] at hm
  exact ((boundedWordTree k).dist_le pIn).trans_eq (hLen.trans hp) |>.antisymm (hq ▸ hLower)

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
