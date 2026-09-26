/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Forest
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/Forest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original rooted forest and postorder traversal -/

/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

/-!
Faithful excerpt port of `Algorithm/Data/Forest.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

inductive Forest (α : Type*)
  | nil : Forest α
  | node (a : α) (child sibling : Forest α) : Forest α
deriving Repr

namespace Forest
variable {α : Type*}

@[simp]
def roots : (f : Forest α) → Set α
  | .nil => ∅
  | .node a _ s => insert a s.roots

@[simp]
def support : (f : Forest α) → Set α
  | .nil => ∅
  | .node a c s => insert a (c.support ∪ s.support)

lemma roots_subset_support (f : Forest α) : f.roots ⊆ f.support := by
  induction f with
  | nil => rfl
  | node a c s _ ihs =>
    exact Set.insert_subset_insert (Set.subset_union_of_subset_right ihs _)

@[simp]
def post : (f : Forest α) → List α
  | .nil => ∅
  | .node a c s => c.post ++ a :: s.post

end Forest
