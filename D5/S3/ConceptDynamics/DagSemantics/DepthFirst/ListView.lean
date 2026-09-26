/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ListView
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/ListView
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original list collection interface and multiset view -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.MultisetView

/-!
Faithful excerpt port of `Algorithm/Data/Classes/ToList.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

variable {C α : Type*}

class ToList (C : Type*) (α : outParam Type*) extends Membership α C, Membership.IsEmpty C where
  toList : C → List α
  toArray : C → Array α
  toArray_eq_mk_toList a : toArray a = Array.mk (toList a)
  mem c a := a ∈ toList c
  mem_toList {x c} : x ∈ toList c ↔ x ∈ c := by rfl
export ToList (toList toArray toArray_eq_mk_toList mem_toList)

attribute [simp] toArray_eq_mk_toList mem_toList

section ToList

instance : ToList (List α) α where
  toList := id
  toArray := Array.mk
  toArray_eq_mk_toList _ := rfl

variable [ToList C α]

instance (priority := 100) ToList.toToMultiset : ToMultiset C α where
  toMultiset c := ↑(toList c)
  mem_toMultiset := mem_toList

end ToList
