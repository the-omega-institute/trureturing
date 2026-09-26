/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/MultisetView
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/MultisetView
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite multiset collection interface -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Data.Multiset.AddSub

/-!
Faithful excerpt port of `Algorithm/Data/Classes/ToMultiset.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

variable {C α : Type*}

class Membership.IsEmpty (C : Type*) {α : outParam Type*} [Membership α C] where
  isEmpty : C → Bool
  isEmpty_iff_forall_not_mem {c} : isEmpty c ↔ ∀ a, a ∉ c
export Membership.IsEmpty (isEmpty isEmpty_iff_forall_not_mem)

class LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [Membership α C] [EmptyCollection C] : Prop where
  not_mem_empty (x : α) : x ∉ (∅ : C)
export LawfulEmptyCollection (not_mem_empty)

class ToMultiset (C : Type*) (α : outParam Type*) extends Membership α C, Membership.IsEmpty C where
  toMultiset : C → Multiset α
  mem c a := a ∈ toMultiset c
  mem_toMultiset {x c} : x ∈ toMultiset c ↔ x ∈ c := by rfl
export ToMultiset (toMultiset mem_toMultiset)

attribute [simp] mem_toMultiset

instance : Membership.IsEmpty (List α) where
  isEmpty := List.isEmpty
  isEmpty_iff_forall_not_mem := by simp [List.eq_nil_iff_forall_not_mem]

instance : ToMultiset (List α) α where
  toMultiset := (↑)
  mem_toMultiset := .rfl
