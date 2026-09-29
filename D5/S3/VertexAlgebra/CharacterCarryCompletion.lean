/- GID: D5/S3/VertexAlgebra/CharacterCarryCompletion
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/CharacterCarryCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonlinear section has a unique recorded composition and a tree expansion. -/

/-
proof_shape: recorded_composition: content; tree_expansion: content
escape_witness: The character correction is derived from the section and cancels in the
  expansion of every binary tree, including trees with different parentheses.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.VertexAlgebra.CharacterCarryCompletion

variable {E C : Type*} [AddCommGroup E] [AddCommGroup C]

def carry (ell : E → C) (g h : E) : C := ell g + ell h - ell (g + h)

def compose (ell : E → C) (x y : E × C) : E × C :=
  (x.1 + y.1, x.2 + y.2 + carry ell x.1 y.1)

def expand (ell : E → C) (x : E × C) : E × C :=
  (x.1, x.2 + ell x.1)

/-- The section correction is forced by expansion, and the resulting operation is associative. -/
theorem recorded_composition (ell : E → C) (h0 : ell 0 = 0) :
    (∀ x y, expand ell (compose ell x y) = expand ell x + expand ell y) ∧
    Function.Bijective (expand ell) ∧
    (∀ x y z, compose ell (compose ell x y) z = compose ell x (compose ell y z)) ∧
    (∀ x, compose ell (0, 0) x = x ∧ compose ell x (0, 0) = x) ∧
    (∀ x y, compose ell x y = compose ell y x) ∧
    (∀ x, ∃ y, compose ell x y = (0, 0) ∧ compose ell y x = (0, 0)) ∧
    (∀ op : E × C → E × C → E × C,
      (∀ x y, expand ell (op x y) = expand ell x + expand ell y) →
      ∀ x y, op x y = compose ell x y) := by
  have hExpand (x y : E × C) :
      expand ell (compose ell x y) = expand ell x + expand ell y := by
    apply Prod.ext
    · rfl
    · simp only [expand, compose, carry, Prod.snd_add]
      abel
  have hInjective : Function.Injective (expand ell) := by
    intro x y h
    have hg' : (expand ell x).1 = (expand ell y).1 :=
      congrArg (fun p : E × C => p.1) h
    have hg : x.1 = y.1 := hg'
    have hc' : (expand ell x).2 = (expand ell y).2 :=
      congrArg (fun p : E × C => p.2) h
    have hc : x.2 + ell x.1 = y.2 + ell y.1 :=
      hc'
    rw [hg] at hc
    exact Prod.ext hg (add_right_cancel hc)
  have hSurjective : Function.Surjective (expand ell) := by
    intro y
    refine ⟨(y.1, y.2 - ell y.1), ?_⟩
    apply Prod.ext
    · rfl
    · simp [expand]
  refine ⟨hExpand, ⟨hInjective, hSurjective⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hInjective
    rw [hExpand, hExpand, hExpand, hExpand, add_assoc]
  · intro x
    constructor
    · apply hInjective
      rw [hExpand]
      simp [expand, h0]
    · apply hInjective
      rw [hExpand]
      simp [expand, h0]
  · intro x y
    apply hInjective
    rw [hExpand, hExpand, add_comm]
  · intro x
    obtain ⟨y, hy⟩ := hSurjective (-expand ell x)
    refine ⟨y, ?_, ?_⟩
    · apply hInjective
      rw [hExpand, hy]
      simp [expand, h0]
    · apply hInjective
      rw [hExpand, hy]
      simp [expand, h0]
  · intro op hop x y
    apply hInjective
    rw [hop, hExpand]

inductive LabelTree (E : Type*) where
  | leaf : E → LabelTree E
  | fork : LabelTree E → LabelTree E → LabelTree E

def evaluate (ell : E → C) : LabelTree E → E × C
  | .leaf g => (g, 0)
  | .fork left right => compose ell (evaluate ell left) (evaluate ell right)

def total : LabelTree E → E
  | .leaf g => g
  | .fork left right => total left + total right

def characterTotal (ell : E → C) : LabelTree E → C
  | .leaf g => ell g
  | .fork left right => characterTotal ell left + characterTotal ell right

/-- Every finite parenthesization records precisely the lost section character. -/
theorem tree_expansion (ell : E → C) (tree : LabelTree E) :
    evaluate ell tree =
      (total tree, characterTotal ell tree - ell (total tree)) := by
  induction tree with
  | leaf g =>
      simp [evaluate, total, characterTotal]
  | fork left right ihLeft ihRight =>
      simp only [evaluate, total, characterTotal, ihLeft, ihRight, compose, carry]
      congr 1
      abel

end D5.S3.VertexAlgebra.CharacterCarryCompletion
