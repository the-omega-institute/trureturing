/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Adjacency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/Adjacency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original adjacency graph, finite support and reachability -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.DefaultDictionary
import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ListView
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Finset.Union

/-!
Faithful excerpt port of `Algorithm/Data/Graph/AdjList.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

structure AdjList
    (V : Type*) (Info : Type*)
    (EColl : Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : Type*) [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅] where
  protected snd : Info → V
  protected star : StarColl

class AdjListClass (G : Type*)
    (V : outParam <| Type*) (Info : outParam <| Type*)
    (EColl : outParam <| Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : outParam <| Type*) [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅] where
  snd : G → Info → V
  star : G → StarColl

namespace AdjListClass

section ToMultiset
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToMultiset EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]

instance : AdjListClass (AdjList V Info EColl StarColl) V Info EColl StarColl where
  snd := AdjList.snd
  star := AdjList.star

variable {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}

instance : GetElem G V EColl (fun _ _ ↦ True) where
  getElem g v _ := (star g)[v]

variable (g) in
structure E where ofStar ::
  fst : V
  info : Info
  mem_star : info ∈ g[fst]

attribute [simp] E.mem_star

protected def E.snd (e : E g) : V := snd g e.info

/-- The vertices of `g`, equipped with its quiver structure. -/
structure ToQuiver (g : G) [AdjListClass G V Info EColl StarColl] where
  /-- Wrap a vertex of `g` as a vertex of its quiver. -/
  mk (g) ::
  /-- The underlying vertex. -/
  val : V

attribute [coe] ToQuiver.val

instance : CoeOut (ToQuiver g) V := ⟨ToQuiver.val⟩

section ToQuiver

instance : Quiver (ToQuiver g) where
  Hom v w := {e : E g // ToQuiver.mk g e.fst = v ∧ ToQuiver.mk g e.snd = w}

@[coe]
def ofHom {v w : ToQuiver g} (e : v ⟶ w) :
    E g :=
  e.1

instance {v w : ToQuiver g} : CoeOut (v ⟶ w) (E g) := ⟨ofHom⟩

def homOfStar {v : V} (x : Info) (hx : x ∈ g[v]) :
    ToQuiver.mk g v ⟶ ToQuiver.mk g (snd g x) :=
  ⟨.ofStar v x hx, rfl, rfl⟩

end ToQuiver

variable (g) in
def Adj (v w : V) : Prop := Nonempty (ToQuiver.mk g v ⟶ ToQuiver.mk g w)

variable (g) in
def Reachable (v w : V) : Prop := Nonempty (Quiver.Path (ToQuiver.mk g v) (ToQuiver.mk g w))

variable (g) in
/-- The vertices incident to an edge of `g`, including both sources and targets. -/
noncomputable def support : Finset V := by
  classical
  exact (toDFinsupp' (star g)).support.biUnion fun v ↦
    (toMultiset g[v]).toFinset.biUnion fun e ↦ {v, snd g e}

variable (g) in
lemma reachable_eq_reflTransGen : Reachable g = Relation.ReflTransGen (Adj g) := by
  ext v w
  constructor
  · intro ⟨h⟩
    change Relation.ReflTransGen (Adj g) v (ToQuiver.mk g w : V)
    generalize ToQuiver.mk g w = w' at *
    induction h with
    | nil => rfl
    | cons _ h ih => exact ih.tail ⟨h⟩
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | tail _ h ih => exact Nonempty.map2 .comp ih (h.map (·.toPath))

variable (g) in
def succSet (s : Set V) : Set V := {w | ∃ v ∈ s, Adj g v w} -- ⋃ v ∈ s, {w | Adj g v w}

end ToMultiset

section ToList
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] (g : G)

def succList (v : V) : List V := (toList g[v]).map (snd g)

end ToList

end AdjListClass
