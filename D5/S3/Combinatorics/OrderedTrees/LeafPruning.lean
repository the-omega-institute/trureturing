/- GID: D5/S3/Combinatorics/OrderedTrees/LeafPruning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrderedTrees/LeafPruning
   mirror-E: none(waiver:ordered-tree-leaf-pruning)
   anchors: [mathlib/module/Mathlib.Data.Nat.Basic]
   utility: none
   digest: Original-leaf pruning preserves child order and reduces vertex height by one. -/

import OmegaBuild.Commands
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Lean.Elab.Tactic.Omega

compile_only_with_mathlib

/-! Ordered child-list shapes, their exact finite size fibers, and simultaneous leaf pruning. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OrderedTrees.LeafPruning

mutual
  /-- A finite rooted tree with an ordered list of child trees. -/
  inductive Tree where
    | node : Forest → Tree
    deriving DecidableEq
  /-- An ordered list of finite rooted trees. -/
  inductive Forest where
    | nil : Forest
    | cons : Tree → Forest → Forest
    deriving DecidableEq
end

mutual
  /-- Number of vertices in a nonempty tree. -/
  def Tree.vertices : Tree → ℕ
    | .node f => f.forest_vertices + 1
  /-- Total number of vertices in an ordered forest. -/
  def Forest.forest_vertices : Forest → ℕ
    | .nil => 0
    | .cons t f => t.vertices + f.forest_vertices
end

mutual
  /-- Vertex height: a singleton has height one. -/
  def Tree.height : Tree → ℕ
    | .node f => f.forest_height + 1
  /-- Maximum vertex height in a forest, zero for the empty forest. -/
  def Forest.forest_height : Forest → ℕ
    | .nil => 0
    | .cons t f => max t.height f.forest_height
end

mutual
  /-- Number of nonleaf vertices. -/
  def Tree.internal : Tree → ℕ
    | .node .nil => 0
    | .node f@(.cons _ _) => f.forest_internal + 1
  /-- Total number of nonleaf vertices in a forest. -/
  def Forest.forest_internal : Forest → ℕ
    | .nil => 0
    | .cons t f => t.internal + f.forest_internal
end

mutual
  /-- Keep the root and remove all its original leaf descendants simultaneously.
  On a nonleaf tree this is exactly one step of original-leaf removal. -/
  def Tree.prune : Tree → Tree
    | .node f => .node f.prune_forest
  /-- Delete original leaf trees and prune the retained trees in child-list order. -/
  def Forest.prune_forest : Forest → Forest
    | .nil => .nil
    | .cons (.node .nil) f => f.prune_forest
    | .cons t@(.node (.cons _ _)) f => .cons t.prune f.prune_forest
end

/-- Child/sibling encoding, used only to enumerate the finite size fibers. -/
def Forest.encode : Forest → BinaryTree Unit
  | .nil => .nil
  | .cons (.node children) rest => .node () children.encode rest.encode

/-- Decode a child/sibling code into an ordered forest. -/
def Forest.decode : BinaryTree Unit → Forest
  | .nil => .nil
  | .node _ children rest => .cons (.node (Forest.decode children)) (Forest.decode rest)

private theorem decode_encode : ∀ f : Forest, Forest.decode f.encode = f
  | .nil => rfl
  | .cons (.node c) f => by
      simp only [Forest.encode, Forest.decode, decode_encode c, decode_encode f]
termination_by f => sizeOf f

private theorem encode_decode (b : BinaryTree Unit) : (Forest.decode b).encode = b := by
  induction b with
  | nil => rfl
  | node u c f hc hf =>
      cases u
      simp only [Forest.decode, Forest.encode, hc, hf]

private theorem encode_vertices : ∀ f : Forest, f.encode.numNodes = f.forest_vertices
  | .nil => rfl
  | .cons (.node c) f => by
      simp only [Forest.encode, BinaryTree.numNodes, Forest.forest_vertices, Tree.vertices,
        encode_vertices c, encode_vertices f]
      omega
termination_by f => sizeOf f

/-- Exact finite collection of all ordered tree shapes with the specified vertex count. -/
def trees (n : ℕ) : Finset Tree :=
  if n = 0 then ∅ else
    (BinaryTree.treesOfNumNodesEq (n - 1)).image (fun b => .node (Forest.decode b))

/-- Membership in the finite enumerator is exactly actual vertex size. -/
private theorem mem_trees (t : Tree) (n : ℕ) : t ∈ trees n ↔ t.vertices = n := by
  cases t with
  | node f =>
      by_cases hn : n = 0
      · subst n
        simp [trees, Tree.vertices]
      · simp only [trees, ite_eq_right hn, Finset.mem_image]
        constructor
        · rintro ⟨b, hb, heq⟩
          have hsize := (BinaryTree.mem_treesOfNumNodesEq.mp hb)
          have hf : Forest.decode b = f := Tree.node.inj heq
          have hcount := encode_vertices (Forest.decode b)
          rw [encode_decode, hsize, hf] at hcount
          simp only [Tree.vertices]
          omega
        · intro hsize
          refine ⟨f.encode, ?_, ?_⟩
          · apply BinaryTree.mem_treesOfNumNodesEq.mpr
            rw [encode_vertices]
            simp only [Tree.vertices] at hsize
            omega
          · rw [decode_encode]

/-- Actual ordered-tree count, filtering by vertex height equal to nonleaf count. -/
def count (n : ℕ) : ℕ := ((trees n).filter (fun t => t.height = t.internal)).card

/-- The count is the cardinality of the finite set of actual shapes with the original predicate. -/
theorem count_spec (n : ℕ) :
    Set.Finite {t : Tree | t.vertices = n ∧ t.height = t.internal} ∧
      count n = Set.ncard {t : Tree | t.vertices = n ∧ t.height = t.internal} := by
  have hs : {t : Tree | t.vertices = n ∧ t.height = t.internal} =
      ((trees n).filter (fun t => t.height = t.internal) : Set Tree) := by
    ext t
    simp only [Finset.mem_coe, Finset.mem_filter, mem_trees, Set.mem_ofPred_eq]
  constructor
  · rw [hs]
    exact Finset.finite_toSet _
  · rw [hs, Set.ncard_coe_finset]
    rfl

private theorem forest_prune_vertices : ∀ f : Forest, f.prune_forest.forest_vertices = f.forest_internal
  | .nil => by simp [Forest.prune_forest, Forest.forest_vertices, Forest.forest_internal]
  | .cons (.node .nil) f => by
      simpa [Forest.prune_forest, Forest.forest_internal, Tree.internal] using forest_prune_vertices f
  | .cons (.node (.cons t g)) f => by
      simp only [Forest.prune_forest, Tree.prune, Forest.forest_vertices, Tree.vertices,
        Forest.forest_internal, Tree.internal]
      rw [forest_prune_vertices (.cons t g), forest_prune_vertices f]
      simp only [Forest.forest_internal]
termination_by f => sizeOf f

private theorem forest_prune_height : ∀ f : Forest, f.prune_forest.forest_height = f.forest_height - 1
  | .nil => by simp [Forest.prune_forest, Forest.forest_height]
  | .cons (.node .nil) f => by
      simp only [Forest.prune_forest, Forest.forest_height, Tree.height]
      rw [forest_prune_height f]
      omega
  | .cons (.node (.cons t g)) f => by
      simp only [Forest.prune_forest, Tree.prune, Forest.forest_height, Tree.height]
      have hc := forest_prune_height (.cons t g)
      have hf := forest_prune_height f
      simp only [Forest.forest_height] at hc
      rw [hc, hf]
      cases t with
      | node h => simp only [Tree.height]; omega
termination_by f => sizeOf f

/-- The vertices retained after pruning a nonleaf tree are exactly its nonleaf vertices. -/
private theorem prune_vertices (t : Tree) (h : t ≠ .node .nil) :
    t.prune.vertices = t.internal := by
  cases t with
  | node f =>
      cases f with
      | nil => exact (h rfl).elim
      | cons a f =>
          simp only [Tree.prune, Tree.vertices, Tree.internal]
          rw [forest_prune_vertices]

/-- Pruning a nonleaf tree reduces its vertex height by exactly one. -/
private theorem prune_height (t : Tree) (h : t ≠ .node .nil) :
    t.prune.height + 1 = t.height := by
  cases t with
  | node f =>
      cases f with
      | nil => exact (h rfl).elim
      | cons a f =>
          simp only [Tree.prune, Tree.height]
          rw [forest_prune_height]
          cases a with
          | node g => simp only [Forest.forest_height, Tree.height]; omega

/-- The original height/nonleaf predicate is exactly the excess-one skeleton predicate.
The singleton is excluded by the original predicate itself. -/
theorem height_eq_internal_iff (t : Tree) :
    t.height = t.internal ↔
      t ≠ .node .nil ∧ t.prune.vertices = t.prune.height + 1 := by
  constructor
  · intro heq
    have hn : t ≠ .node .nil := by
      intro ht
      subst t
      simp [Tree.height, Forest.forest_height, Tree.internal] at heq
    exact ⟨hn, by rw [prune_vertices t hn, prune_height t hn, heq]⟩
  · rintro ⟨hn, heq⟩
    rw [prune_vertices t hn, prune_height t hn] at heq
    exact heq.symm


/-- Add a specified number of unary ancestors above an ordered tree. -/
def stem : ℕ → Tree → Tree
  | 0, t => t
  | n + 1, t => .node (.cons (stem n t) .nil)

/-- A path with `n` unary vertices and one terminal vertex. -/
def path (n : ℕ) : Tree := stem n (.node .nil)

/-- A unary stem ending in an ordered binary fork with two path arms. -/
def fork (b l r : ℕ) : Tree :=
  stem b (.node (.cons (path l) (.cons (path r) .nil)))

private theorem forest_height_le_vertices : ∀ f : Forest,
    f.forest_height ≤ f.forest_vertices
  | .nil => by simp [Forest.forest_height, Forest.forest_vertices]
  | .cons (.node c) f => by
      have hc := forest_height_le_vertices c
      have hf := forest_height_le_vertices f
      simp only [Forest.forest_height, Forest.forest_vertices, Tree.height, Tree.vertices]
      omega
termination_by f => sizeOf f

private theorem tree_bounds (t : Tree) :
    1 ≤ t.height ∧ t.height ≤ t.vertices := by
  cases t with
  | node f =>
      have h := forest_height_le_vertices f
      simp only [Tree.height, Tree.vertices]
      omega

private theorem stem_stats (b : ℕ) (t : Tree) :
    (stem b t).vertices = b + t.vertices ∧ (stem b t).height = b + t.height := by
  induction b with
  | zero => simp [stem]
  | succ b ih =>
      simp only [stem, Tree.vertices, Tree.height, Forest.forest_vertices,
        Forest.forest_height, Nat.add_zero, Nat.max_zero, ih.1, ih.2]
      constructor <;> omega

private theorem path_stats (n : ℕ) :
    (path n).vertices = n + 1 ∧ (path n).height = n + 1 := by
  simpa [path, Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height]
    using stem_stats n (.node .nil)

private theorem path_classification : ∀ t : Tree,
    t.vertices = t.height → ∃ n, t = path n
  | .node .nil, _ => ⟨0, rfl⟩
  | .node (.cons a .nil), h => by
      have ha : a.vertices = a.height := by
        simpa [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height] using h
      obtain ⟨n, hn⟩ := path_classification a ha
      refine ⟨n + 1, ?_⟩
      simp [path, stem, hn, path]
  | .node (.cons a (.cons b f)), h => by
      have ha := tree_bounds a
      have hb := tree_bounds b
      have hf := forest_height_le_vertices f
      simp only [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height] at h
      omega
termination_by t => sizeOf t

private theorem fork_stats (b l r : ℕ) :
    (fork b l r).vertices = b + l + r + 3 ∧
      (fork b l r).height = b + max l r + 2 := by
  have hs := stem_stats b (.node (.cons (path l) (.cons (path r) .nil)))
  have hl := path_stats l
  have hr := path_stats r
  simp only [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height,
    Nat.add_zero, Nat.max_zero, hl.1, hl.2, hr.1, hr.2] at hs
  change _ ∧ _
  constructor <;> dsimp [fork] <;> omega

private theorem skeleton_classification : ∀ t : Tree,
    t.vertices = t.height + 1 →
      ∃ b l r, (l = 0 ∨ r = 0) ∧ t = fork b l r
  | .node .nil, h => by
      simp [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height] at h
  | .node (.cons a .nil), h => by
      have ha : a.vertices = a.height + 1 := by
        simpa [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height] using h
      obtain ⟨b, l, r, hz, he⟩ := skeleton_classification a ha
      refine ⟨b + 1, l, r, hz, ?_⟩
      simp [fork, stem, he, fork]
  | .node (.cons a (.cons b .nil)), h => by
      have ha := tree_bounds a
      have hb := tree_bounds b
      simp only [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height,
        Nat.add_zero, Nat.max_zero] at h
      have ea : a.vertices = a.height := by omega
      have eb : b.vertices = b.height := by omega
      obtain ⟨l, el⟩ := path_classification a ea
      obtain ⟨r, er⟩ := path_classification b eb
      refine ⟨0, l, r, ?_, ?_⟩
      · have hl := path_stats l
        have hr := path_stats r
        rw [el, er] at h
        omega
      · simp [fork, stem, el, er]
  | .node (.cons a (.cons b (.cons c f))), h => by
      have ha := tree_bounds a
      have hb := tree_bounds b
      have hc := tree_bounds c
      have hf := forest_height_le_vertices f
      simp only [Tree.vertices, Tree.height, Forest.forest_vertices, Forest.forest_height] at h
      omega
termination_by t => sizeOf t

/-- An ordered tree has excess one exactly when it is a stem above one binary fork,
with two path arms and at least one arm having no unary vertex. -/
theorem excess_one_iff_fork (t : Tree) :
    t.vertices = t.height + 1 ↔
      ∃ b l r, (l = 0 ∨ r = 0) ∧ t = fork b l r := by
  constructor
  · exact skeleton_classification t
  · rintro ⟨b, l, r, hz, rfl⟩
    have hs := fork_stats b l r
    rcases hz with hz | hz <;> subst_vars <;> omega

/-- The original actual-tree predicate is equivalent to its pruned tree having
this exhaustive stem/fork/path form. -/
theorem height_eq_internal_iff_fork (t : Tree) :
    t.height = t.internal ↔ t ≠ .node .nil ∧
      ∃ b l r, (l = 0 ∨ r = 0) ∧ t.prune = fork b l r := by
  rw [height_eq_internal_iff, excess_one_iff_fork]


private theorem path_injective {m n : ℕ} (h : path m = path n) : m = n := by
  have hs := congrArg Tree.vertices h
  rw [(path_stats m).1, (path_stats n).1] at hs
  omega

private theorem fork_injective : ∀ b c l r p q : ℕ,
    fork b l r = fork c p q → b = c ∧ l = p ∧ r = q
  | 0, 0, l, r, p, q, h => by
      have hchild := Forest.cons.inj (Tree.node.inj h)
      have hright := Forest.cons.inj hchild.2
      exact ⟨rfl, path_injective hchild.1, path_injective hright.1⟩
  | 0, c + 1, l, r, p, q, h => by
      have htail := (Forest.cons.inj (Tree.node.inj h)).2
      cases htail
  | b + 1, 0, l, r, p, q, h => by
      have htail := (Forest.cons.inj (Tree.node.inj h)).2
      cases htail
  | b + 1, c + 1, l, r, p, q, h => by
      have hh := (Forest.cons.inj (Tree.node.inj h)).1
      obtain ⟨hb, hl, hr⟩ := fork_injective b c l r p q hh
      exact ⟨by omega, hl, hr⟩

/-- All excess-one skeletons with `u` unary vertices, with the equal-arm case
included only in the first family. -/
def skeletons (u : ℕ) : Finset Tree :=
  ((Finset.range (u + 1)).image (fun l => fork (u - l) l 0)) ∪
    ((Finset.range u).image (fun j => fork (u - (j + 1)) 0 (j + 1)))

/-- The skeleton enumeration is exhaustive at every size and has exactly
`2*u+1` distinct ordered shapes. The equal-arm tie contributes once. -/
theorem skeletons_spec (u : ℕ) :
    (∀ t : Tree, t ∈ skeletons u ↔
      t.vertices = u + 3 ∧ t.vertices = t.height + 1) ∧
      (skeletons u).card = 2 * u + 1 := by
  constructor
  · intro t
    constructor
    · intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
        have hbound := Finset.mem_range.mp hl
        have hs := fork_stats (u - l) l 0
        constructor
        · omega
        · apply (excess_one_iff_fork _).mpr
          exact ⟨u - l, l, 0, Or.inr rfl, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
        have hbound := Finset.mem_range.mp hj
        have hs := fork_stats (u - (j + 1)) 0 (j + 1)
        constructor
        · omega
        · apply (excess_one_iff_fork _).mpr
          exact ⟨u - (j + 1), 0, j + 1, Or.inl rfl, rfl⟩
    · rintro ⟨hsize, hexcess⟩
      obtain ⟨b, l, r, hz, rfl⟩ := (excess_one_iff_fork t).mp hexcess
      have hs := fork_stats b l r
      change _ ∈ _ ∪ _
      rcases hz with hl | hr
      · subst l
        by_cases hr : r = 0
        · subst r
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
          have hb : u = b := by omega
          simp [hb]
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
          have hr' : r - 1 + 1 = r := by omega
          have hb : u - r = b := by omega
          rw [hr', hb]
      · subst r
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨l, Finset.mem_range.mpr (by omega), ?_⟩
        have hb : u - l = b := by omega
        rw [hb]
  · have hdisjoint : Disjoint
        ((Finset.range (u + 1)).image (fun l => fork (u - l) l 0))
        ((Finset.range u).image (fun j => fork (u - (j + 1)) 0 (j + 1))) := by
      apply Finset.disjoint_left.mpr
      intro t ht ht'
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ht'
      have h := fork_injective _ _ _ _ _ _ he
      omega
    have hleft : Function.Injective (fun l => fork (u - l) l 0) := by
      intro l k he
      exact (fork_injective _ _ _ _ _ _ he).2.1
    have hright : Function.Injective (fun j => fork (u - (j + 1)) 0 (j + 1)) := by
      intro j k he
      have h := (fork_injective _ _ _ _ _ _ he).2.2
      omega
    rw [skeletons, Finset.card_union_of_disjoint hdisjoint,
      Finset.card_image_of_injective _ hleft, Finset.card_image_of_injective _ hright,
      Finset.card_range, Finset.card_range]
    omega


mutual
  /-- Ordered leaf-gap data: terminal vertices carry one mandatory original leaf;
  a branch carries its initial gap, first internal child and remaining gaps. -/
  inductive Decoration where
    | tip : ℕ → Decoration
    | branch : ℕ → Decoration → DecorationForest → Decoration
    deriving DecidableEq
  /-- The gap after a retained child, followed by the next retained child or the end. -/
  inductive DecorationForest where
    | last : ℕ → DecorationForest
    | more : ℕ → Decoration → DecorationForest → DecorationForest
    deriving DecidableEq
end

private def addLeaves : ℕ → Forest → Forest
  | 0, f => f
  | n + 1, f => .cons (.node .nil) (addLeaves n f)

private def DecorationForest.shift (k : ℕ) : DecorationForest → DecorationForest
  | .last n => .last (k + n)
  | .more n t f => .more (k + n) t f

mutual
  /-- Insert the indicated original leaves, with positive terminal leaf counts. -/
  def Decoration.inflate : Decoration → Tree
    | .tip n => .node (addLeaves (n + 1) .nil)
    | .branch n t f => .node (addLeaves n (.cons t.inflate f.inflate_forest))
  /-- Insert every ordered leaf run in a decorated child forest. -/
  def DecorationForest.inflate_forest : DecorationForest → Forest
    | .last n => addLeaves n .nil
    | .more n t f => addLeaves n (.cons t.inflate f.inflate_forest)
end

mutual
  /-- Erase the leaf-gap counts to obtain the retained skeleton. -/
  def Decoration.skeleton : Decoration → Tree
    | .tip _ => .node .nil
    | .branch _ t f => .node (.cons t.skeleton f.skeleton_forest)
  /-- Erase the gap counts while retaining child order. -/
  def DecorationForest.skeleton_forest : DecorationForest → Forest
    | .last _ => .nil
    | .more _ t f => .cons t.skeleton f.skeleton_forest
end

mutual
  private def Tree.decorate : Tree → Decoration
    | .node f => match f.decorate_forest with
      | .last n => .tip (n - 1)
      | .more n t f => .branch n t f
  private def Forest.decorate_forest : Forest → DecorationForest
    | .nil => .last 0
    | .cons (.node .nil) f => f.decorate_forest.shift 1
    | .cons t@(.node (.cons _ _)) f => .more 0 t.decorate f.decorate_forest
end

private theorem addLeaves_add (m n : ℕ) (f : Forest) :
    addLeaves (m + n) f = addLeaves m (addLeaves n f) := by
  induction m with
  | zero => simp only [Nat.zero_add, addLeaves]
  | succ m ih => simpa only [Nat.succ_add, addLeaves] using congrArg (Forest.cons (.node .nil)) ih

private theorem addLeaves_eq_nil (n : ℕ) (f : Forest) :
    addLeaves n f = .nil ↔ n = 0 ∧ f = .nil := by
  cases n <;> simp [addLeaves]

private theorem inflate_nonleaf (d : Decoration) : d.inflate ≠ .node .nil := by
  cases d with
  | tip n => simp [Decoration.inflate, addLeaves]
  | branch n t f =>
      intro h
      have hh := (addLeaves_eq_nil n (.cons t.inflate f.inflate_forest)).mp (Tree.node.inj h)
      cases hh.2

private theorem shift_add (m n : ℕ) (d : DecorationForest) :
    (d.shift n).shift m = d.shift (m + n) := by
  cases d <;> simp [DecorationForest.shift, Nat.add_assoc]

private theorem decorate_addLeaves (n : ℕ) (f : Forest) :
    (addLeaves n f).decorate_forest = f.decorate_forest.shift n := by
  induction n with
  | zero =>
      simp only [addLeaves]
      cases he : f.decorate_forest <;> simp [DecorationForest.shift]
  | succ n ih =>
      simp only [addLeaves, Forest.decorate_forest, ih, shift_add]
      congr 1
      omega

private theorem decorate_cons_nonleaf (t : Tree) (f : Forest) (h : t ≠ .node .nil) :
    (Forest.cons t f).decorate_forest = .more 0 t.decorate f.decorate_forest := by
  cases t with
  | node c => cases c with
    | nil => exact (h rfl).elim
    | cons a c => simp only [Forest.decorate_forest]

private theorem inflate_shift (n : ℕ) (d : DecorationForest) :
    (d.shift n).inflate_forest = addLeaves n d.inflate_forest := by
  cases d <;> simp only [DecorationForest.shift, DecorationForest.inflate_forest, addLeaves_add]

mutual
  private theorem decorate_inflate (d : Decoration) : d.inflate.decorate = d := by
    cases d with
    | tip n => simp [Decoration.inflate, Tree.decorate, decorate_addLeaves,
        Forest.decorate_forest, DecorationForest.shift]
    | branch n t f =>
        simp only [Decoration.inflate, Tree.decorate, decorate_addLeaves,
          decorate_cons_nonleaf _ _ (inflate_nonleaf t), decorate_inflate t,
          decorate_inflate_forest f, DecorationForest.shift, Nat.add_zero]
  private theorem decorate_inflate_forest (d : DecorationForest) :
      d.inflate_forest.decorate_forest = d := by
    cases d with
    | last n => simp [DecorationForest.inflate_forest, decorate_addLeaves,
        Forest.decorate_forest, DecorationForest.shift]
    | more n t f =>
        simp only [DecorationForest.inflate_forest, decorate_addLeaves,
          decorate_cons_nonleaf _ _ (inflate_nonleaf t), decorate_inflate t,
          decorate_inflate_forest f, DecorationForest.shift, Nat.add_zero]
end

private theorem reconstruct_node (f : Forest) (hn : f ≠ .nil)
    (hf : f.decorate_forest.inflate_forest = f) :
    (Tree.node f).decorate.inflate = .node f := by
  cases he : f.decorate_forest with
  | last n =>
      rw [he] at hf
      have hp : 0 < n := by
        by_contra h
        have hz : n = 0 := by omega
        simp [DecorationForest.inflate_forest, hz, addLeaves] at hf
        exact hn hf.symm
      simp only [Tree.decorate, he, Decoration.inflate]
      have hh : n - 1 + 1 = n := by omega
      rw [hh]
      exact congrArg Tree.node hf
  | more n t d =>
      rw [he] at hf
      simpa only [Tree.decorate, he, Decoration.inflate, DecorationForest.inflate_forest]
        using congrArg Tree.node hf

private theorem inflate_decorate_forest : ∀ f : Forest,
    f.decorate_forest.inflate_forest = f
  | .nil => by simp [Forest.decorate_forest, DecorationForest.inflate_forest, addLeaves]
  | .cons (.node .nil) f => by
      simp only [Forest.decorate_forest, inflate_shift, inflate_decorate_forest f, addLeaves]
  | .cons (.node (.cons a c)) f => by
      have hc := inflate_decorate_forest (.cons a c)
      have ht := reconstruct_node (.cons a c) (by intro h; cases h) hc
      simp only [Forest.decorate_forest, DecorationForest.inflate_forest, addLeaves,
        ht, inflate_decorate_forest f]
termination_by f => sizeOf f

/-- Leaf-gap data and actual nonsingleton ordered trees are mutually inverse.
No quotient by sibling permutations is used. -/
def decorationEquiv : Decoration ≃ {t : Tree // t ≠ .node .nil} where
  toFun d := ⟨d.inflate, inflate_nonleaf d⟩
  invFun t := t.val.decorate
  left_inv := decorate_inflate
  right_inv t := by
    apply Subtype.ext
    cases t with
    | mk t h =>
        cases t with
        | node f =>
            exact reconstruct_node f (by intro he; exact h (congrArg Tree.node he))
              (inflate_decorate_forest f)

private theorem prune_addLeaves (n : ℕ) (f : Forest) :
    (addLeaves n f).prune_forest = f.prune_forest := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [addLeaves, Forest.prune_forest] using ih

private theorem prune_cons_nonleaf (t : Tree) (f : Forest) (h : t ≠ .node .nil) :
    (Forest.cons t f).prune_forest = .cons t.prune f.prune_forest := by
  cases t with
  | node c => cases c with
    | nil => exact (h rfl).elim
    | cons a c => simp only [Forest.prune_forest]

mutual
  /-- Pruning an inflated gap decoration recovers exactly its ordered skeleton. -/
  theorem inflate_prune (d : Decoration) : d.inflate.prune = d.skeleton := by
    cases d with
    | tip n => simp [Decoration.inflate, Tree.prune, prune_addLeaves,
        Forest.prune_forest, Decoration.skeleton]
    | branch n t f =>
        simp only [Decoration.inflate, Tree.prune, prune_addLeaves,
          prune_cons_nonleaf _ _ (inflate_nonleaf t), inflate_prune t,
          inflate_prune_forest f, Decoration.skeleton]
  private theorem inflate_prune_forest (d : DecorationForest) :
      d.inflate_forest.prune_forest = d.skeleton_forest := by
    cases d with
    | last n => simp [DecorationForest.inflate_forest, prune_addLeaves,
        Forest.prune_forest, DecorationForest.skeleton_forest]
    | more n t f =>
        simp only [DecorationForest.inflate_forest, prune_addLeaves,
          prune_cons_nonleaf _ _ (inflate_nonleaf t), inflate_prune t,
          inflate_prune_forest f, DecorationForest.skeleton_forest]
end

mutual
  /-- Sum of the freely chosen nonnegative leaf-gap counts. Mandatory terminal
  leaves are excluded from this sum. -/
  def Decoration.gapTotal : Decoration → ℕ
    | .tip n => n
    | .branch n t f => n + t.gapTotal + f.gap_total_forest
  /-- Sum of all free gap counts in a decorated child forest. -/
  def DecorationForest.gap_total_forest : DecorationForest → ℕ
    | .last n => n
    | .more n t f => n + t.gapTotal + f.gap_total_forest
end

mutual
  /-- Number of independently variable nonnegative leaf gaps. -/
  def Decoration.slots : Decoration → ℕ
    | .tip _ => 1
    | .branch _ t f => 1 + t.slots + f.forest_slots
  /-- Number of gap positions, including the final child gap. -/
  def DecorationForest.forest_slots : DecorationForest → ℕ
    | .last _ => 1
    | .more _ t f => 1 + t.slots + f.forest_slots
end

private theorem addLeaves_vertices (n : ℕ) (f : Forest) :
    (addLeaves n f).forest_vertices = n + f.forest_vertices := by
  induction n with
  | zero => simp [addLeaves]
  | succ n ih =>
      simp only [addLeaves, Forest.forest_vertices, Tree.vertices, ih]
      omega

mutual
  private theorem decoration_statistics (d : Decoration) :
      d.inflate.vertices + d.skeleton.internal = 2 * d.skeleton.vertices + d.gapTotal ∧
        d.slots + 1 = 2 * d.skeleton.vertices := by
    cases d with
    | tip n =>
        simp [Decoration.inflate, Decoration.skeleton, Decoration.gapTotal,
          Decoration.slots, Tree.vertices, Tree.internal, Forest.forest_vertices,
          addLeaves_vertices]
        omega
    | branch n t f =>
        have ht := decoration_statistics t
        have hf := decoration_forest_statistics f
        simp only [Decoration.inflate, Tree.vertices, addLeaves_vertices,
          Decoration.skeleton, Tree.internal, Forest.forest_vertices,
          Forest.forest_internal, Decoration.gapTotal, Decoration.slots]
        constructor <;> omega
  private theorem decoration_forest_statistics (d : DecorationForest) :
      d.inflate_forest.forest_vertices + d.skeleton_forest.forest_internal =
          2 * d.skeleton_forest.forest_vertices + d.gap_total_forest ∧
        d.forest_slots = 2 * d.skeleton_forest.forest_vertices + 1 := by
    cases d with
    | last n =>
        simp [DecorationForest.inflate_forest, DecorationForest.skeleton_forest,
          DecorationForest.gap_total_forest, DecorationForest.forest_slots,
          Forest.forest_vertices, Forest.forest_internal, addLeaves_vertices]
    | more n t f =>
        have ht := decoration_statistics t
        have hf := decoration_forest_statistics f
        simp only [DecorationForest.inflate_forest, addLeaves_vertices,
          DecorationForest.skeleton_forest, Forest.forest_vertices,
          Forest.forest_internal, DecorationForest.gap_total_forest,
          DecorationForest.forest_slots]
        constructor <;> omega
end

private theorem stem_internal (b : ℕ) (t : Tree) :
    (stem b t).internal = b + t.internal := by
  induction b with
  | zero => simp [stem]
  | succ b ih =>
      simp only [stem, Tree.internal, Forest.forest_internal, Nat.add_zero, ih]
      omega

private theorem fork_internal (b l r : ℕ) : (fork b l r).internal = b + l + r + 1 := by
  simp only [fork, stem_internal, Tree.internal, Forest.forest_internal,
    Nat.add_zero, path, stem_internal]
  omega

/-- Every actual tree in the original counting class has reversible leaf-gap
coordinates with `u+5+sum(gaps)` vertices and `2*u+5` free slots, where
`u` is the sum of the stem and the two arm lengths and one arm is zero. -/
theorem actual_count_coordinates (t : Tree) (h : t.height = t.internal) :
    ∃ d : Decoration, ∃ b l r : ℕ,
      d.inflate = t ∧ d.skeleton = fork b l r ∧ (l = 0 ∨ r = 0) ∧
        t.vertices = b + l + r + 5 + d.gapTotal ∧
        d.slots = 2 * (b + l + r) + 5 := by
  obtain ⟨hn, b, l, r, hz, hs⟩ := (height_eq_internal_iff_fork t).mp h
  let d := decorationEquiv.symm ⟨t, hn⟩
  have hd : d.inflate = t := congrArg Subtype.val (decorationEquiv.apply_symm_apply ⟨t, hn⟩)
  have hsk : d.skeleton = fork b l r := by
    rw [← inflate_prune d, hd, hs]
  have hstats := decoration_statistics d
  rw [hsk, hd] at hstats
  have hv := (fork_stats b l r).1
  have hi := fork_internal b l r
  refine ⟨d, b, l, r, hd, hsk, hz, ?_, ?_⟩ <;> omega


/-- No actual tree in the counting class has fewer than five vertices. -/
theorem count_eq_zero_of_lt_five (n : ℕ) (hn : n < 5) : count n = 0 := by
  unfold count
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨htree, hmatch⟩ := Finset.mem_filter.mp ht
  have hsize := (mem_trees t n).mp htree
  obtain ⟨d, b, l, r, _, _, _, hcoord, _⟩ := actual_count_coordinates t hmatch
  omega

/-- Size and free-gap count for a decoration whose skeleton belongs to `skeletons u`. -/
theorem decoration_weight (d : Decoration) (u : ℕ) (hs : d.skeleton ∈ skeletons u) :
    d.inflate.vertices = u + 5 + d.gapTotal ∧ d.slots = 2 * u + 5 := by
  obtain ⟨hvertices, hexcess⟩ := ((skeletons_spec u).1 d.skeleton).mp hs
  obtain ⟨b, l, r, _, he⟩ := (excess_one_iff_fork _).mp hexcess
  have hstats := decoration_statistics d
  rw [he, fork_internal, (fork_stats b l r).1] at hstats
  rw [he, (fork_stats b l r).1] at hvertices
  omega

end D5.S3.Combinatorics.OrderedTrees.LeafPruning
