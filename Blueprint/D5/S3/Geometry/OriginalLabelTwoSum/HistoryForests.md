# HistoryForests

## Abstract

Literal projected wheel-path rows, redundant supersets, cut intervals and original endpoint markers.

Literal FILTER-before-PROJECT original indexed rows on 2,3,...,m,1; AllMWheel.rim is exactly {1,2}. The actual row graph is decomposed into disjoint consecutive intervals. Forced singleton constraints and isolated residual ghosts remain coordinates. The arbitrary-width cut/walk proof forces empty original masks in the connected-original-endpoints case. The total physical parent-factor readback consumes the computed row and marker cases on arbitrary injective ambient coordinates. Its inputs contain no desired structural result, Output, native certificate or deformation.  The universal strong-history construction is separate from the local statement here.

## Source text

Lean module source and proofs:

/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests

   generality: G

   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryForests

   mirror-E: none(waiver:original-projected-path-forest)

   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]

   utility: none

   digest: Literal projected wheel-path rows, redundant supersets, cut intervals and original endpoint markers. -/

/-

    No strong Output, kernel, native or admission claim. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers

import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel

import Mathlib.Combinatorics.SimpleGraph.Paths

Definitions and proofs are in the paired Lean module.

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

Definitions and proofs are in the paired Lean module.

noncomputable section

local instance historyForestsPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests

open OriginalLabelTwoSum HistoryCorners AllMWheel

Definitions and proofs are in the paired Lean module.

section IndexedRows

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- Singleton constraints are labels, not a replacement ground. -/

def forced (r : Rows V) : Finset V := by classical exact r.ground.filter (fun x => ∃ c : r.chords, r.row c = {x})

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_forced (r : Rows V) (x : V) :

    x ∈ forced r ↔ ∃ c : r.chords, r.row c = {x} := by

  constructor

  · exact fun h => (Finset.mem_filter.mp h).2

  · rintro ⟨c, hc⟩

    exact Finset.mem_filter.mpr ⟨r.row_supported c (by simp [hc]), c, hc⟩

Definitions and proofs are in the paired Lean module.

/-- Only size-two superset ROWS touching a singleton are removed.

The index subtype retains every other original multiplicity and every label. -/

def prune (r : Rows V) : Rows V where

  ground := r.ground

  chords := {c : r.chords // (r.row c).card ≠ 2 ∨ Disjoint (r.row c) (forced r)}

  row c := r.row c.1

  row_supported c := r.row_supported c.1

Definitions and proofs are in the paired Lean module.

/-- This equality is raw: the empty face is not projected away. -/

theorem prune_root (r : Rows V) : (prune r).root = r.root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c, hc⟩

    exact ⟨c.1, hc⟩

  · rintro ⟨c, hc⟩

    by_cases hk : (r.row c).card ≠ 2 ∨ Disjoint (r.row c) (forced r)

    · exact ⟨⟨c, hk⟩, hc⟩

    · have hd : ¬ Disjoint (r.row c) (forced r) := fun h => hk (Or.inr h)

      obtain ⟨x, hxq, hxF⟩ := Finset.not_disjoint_iff.mp hd

      obtain ⟨d, hd⟩ := (mem_forced r x).mp hxF

      refine ⟨⟨d, Or.inl (by simp [hd])⟩, ?_⟩

      intro y hy

      obtain ⟨hyW, hyq⟩ := Finset.mem_sdiff.mp (hc hy)

      refine Finset.mem_sdiff.mpr ⟨hyW, ?_⟩

      intro hyd

      have hyx : y = x := by

        change y ∈ r.row d at hyd

        simpa only [hd, Finset.mem_singleton] using hyd

      exact hyq (hyx.symm ▸ hxq)

Definitions and proofs are in the paired Lean module.

/-- An existing empty ROW yields a simplex, even on zero ground (UNIT). -/

theorem empty_row_root (r : Rows V) (c : r.chords) (hc : r.row c = ∅) :

    r.root = delta r.ground := by

  apply SetLike.ext

  intro s

  exact ⟨r.root_supported s, fun hs => ⟨c, by simpa [hc] using hs⟩⟩

Definitions and proofs are in the paired Lean module.

/-- No surviving index yields VOID, including on zero ground. -/

theorem no_rows_root (r : Rows V) (h : IsEmpty r.chords) : r.root = ⊥ := by

  apply SetLike.ext

  intro s

  exact ⟨fun ⟨c, _⟩ => (h.false c).elim, fun h => h.elim⟩

end IndexedRows

Definitions and proofs are in the paired Lean module.

/-- The ACTUAL non-interface rim rows; this is not pathRows with indices forgotten. -/

def localRows (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m)) : Rows (Label m) :=

  cornerRows ((rimRows m (by omega)).without (interfaceRow m hm)) A B

Definitions and proofs are in the paired Lean module.

/-- The path coordinate is 2,3,...,m,1. Coordinate zero is not the hub. -/

def «at» (m : Nat) (hm : 3 ≤ m) (i : Fin m) : Label m :=

  if h : i.val + 1 = m then firstLabel m hm else ⟨i.val + 2, by omega⟩

Definitions and proofs are in the paired Lean module.

def position (m : Nat) (x : Label m) : Nat :=

  if x.val = 1 then m - 1 else x.val - 2

Definitions and proofs are in the paired Lean module.

private theorem at_ground (m : Nat) (hm : 3 ≤ m) (i : Fin m) :

    «at» m hm i ∈ ground m := by

  unfold «at»

  split_ifs <;> simp [ground, firstLabel, Fin.ext_iff] <;> omega

Definitions and proofs are in the paired Lean module.

private theorem position_at (m : Nat) (hm : 3 ≤ m) (i : Fin m) :

    position m («at» m hm i) = i.val := by

  unfold «at» position

  split_ifs <;> simp_all [firstLabel] <;> omega

Definitions and proofs are in the paired Lean module.

private theorem position_lt (m : Nat) (hm : 3 ≤ m) (x : Label m)

    (hx : x ∈ ground m) : position m x < m := by

  have hx0 : x.val ≠ 0 := by

    have hn := (Finset.mem_erase.mp hx).1

    exact (not_congr (Fin.ext_iff (a := x) (b := 0))).mp hn

  have := x.isLt

  unfold position

  split_ifs <;> omega

Definitions and proofs are in the paired Lean module.

private theorem at_position (m : Nat) (hm : 3 ≤ m) (x : Label m)

    (hx : x ∈ ground m) : «at» m hm ⟨position m x, position_lt m hm x hx⟩ = x := by

  have hx0 : x.val ≠ 0 := (not_congr (Fin.ext_iff (a := x) (b := 0))).mp

    (Finset.mem_erase.mp hx).1

  have hlt := x.isLt

  by_cases h1 : x.val = 1

  · have hp : position m x = m - 1 := by simp only [position, if_pos h1]

    have he : m - 1 + 1 = m := by omega

    simp only [hp, «at», dif_pos he]

    exact Fin.ext h1.symm

  · have hp : position m x = x.val - 2 := by simp only [position, if_neg h1]

    have he : x.val - 2 + 1 ≠ m := by omega

    simp only [hp, «at», dif_neg he]

    apply Fin.ext

    change x.val - 2 + 2 = x.val

    omega

Definitions and proofs are in the paired Lean module.

private theorem at_injective (m : Nat) (hm : 3 ≤ m) : Function.Injective («at» m hm) := by

  intro i j h

  apply Fin.ext

  simpa only [position_at] using congrArg (position m) h

Definitions and proofs are in the paired Lean module.

/-- One original cut, with its two ORIGINAL coordinate labels. -/

def cutRow (m : Nat) (hm : 3 ≤ m) (k : Fin (m - 1)) : Finset (Label m) :=

  {«at» m hm ⟨k.val, by omega⟩, «at» m hm ⟨k.val + 1, by omega⟩}

Definitions and proofs are in the paired Lean module.

private theorem cutRow_card (m : Nat) (hm : 3 ≤ m) (k : Fin (m - 1)) :

    (cutRow m hm k).card = 2 := by

  have hn : «at» m hm ⟨k.val, by omega⟩ ≠ «at» m hm ⟨k.val + 1, by omega⟩ := by

    intro h

    have hv := congrArg Fin.val (at_injective m hm h)

    change k.val = k.val + 1 at hv

    omega

  simp [cutRow, hn]

Definitions and proofs are in the paired Lean module.

/-- Every remaining ORIGINAL rim index is exactly one consecutive cut.

This theorem concerns indexed rows, before projection or deduplication. -/

private theorem original_row (m : Nat) (hm : 3 ≤ m)

    (i : {i : Fin m // i ≠ interfaceRow m hm}) :

    rimEdge m (by omega) i.1 = cutRow m hm ⟨i.1.val - 1, by

      have h0 : i.1.val ≠ 0 := fun h => i.2 (Fin.ext h)

      have := i.1.isLt

      omega⟩ := by

  have h0 : i.1.val ≠ 0 := fun h => i.2 (Fin.ext h)

  have hi := i.1.isLt

  have ha : «at» m hm (⟨i.1.val - 1, by omega⟩ : Fin m) = label m i.1 := by

    apply Fin.ext

    dsimp [«at», label]

    split_ifs with h

    · dsimp [firstLabel]; omega

    · dsimp; omega

  have hb : «at» m hm (⟨i.1.val - 1 + 1, by omega⟩ : Fin m) =

      label m (rimIndex m (by omega) i.1) := by

    apply Fin.ext

    dsimp [«at», label, rimIndex]

    split_ifs with h

    · have hlast : i.1.val + 1 = m := by omega

      simp [firstLabel, hlast]

    · have hlt : i.1.val + 1 < m := by omega

      rw [Nat.mod_eq_of_lt hlt]

      dsimp

      omega

  change {label m i.1, label m (rimIndex m (by omega) i.1)} =

    {«at» m hm (⟨i.1.val - 1, by omega⟩ : Fin m),

      «at» m hm (⟨i.1.val - 1 + 1, by omega⟩ : Fin m)}

  rw [ha, hb]

Definitions and proofs are in the paired Lean module.

/-- Exhaustive literal indexed projection, INCLUDING which original endpoint was deleted.

The linked-mask filter remains in c.2; no duplicate index is removed. -/

theorem projected_row_cases (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

    (c : (localRows m hm A B).chords) :

    ∃ k : Fin (m - 1),

      Disjoint (cutRow m hm k) A ∧

      (localRows m hm A B).row c = cutRow m hm k \ B ∧

      ((localRows m hm A B).row c = ∅ ∨

       (∃ x ∈ cutRow m hm k, (localRows m hm A B).row c = {x}) ∨

       (localRows m hm A B).row c = cutRow m hm k) := by

  let k : Fin (m - 1) := ⟨c.1.1.val - 1, by

    have h0 : c.1.1.val ≠ 0 := fun h => c.1.2 (Fin.ext h)

    have := c.1.1.isLt

    omega⟩

  have he := original_row m hm c.1

  have hr : (localRows m hm A B).row c = cutRow m hm k \ B := by

    change rimEdge m (by omega) c.1.1 \ B = _

    rw [he]

  refine ⟨k, by simpa only [Rows.without, rimRows, he] using c.2, hr, ?_⟩

  rw [hr]

  let a := «at» m hm (⟨k.val, by omega⟩ : Fin m)

  let b := «at» m hm (⟨k.val + 1, by omega⟩ : Fin m)

  by_cases ha : a ∈ B <;> by_cases hb : b ∈ B

  · left; ext x; simp [cutRow, a, b, Finset.mem_sdiff, ha, hb]; aesop

  · right; left; refine ⟨b, by simp [cutRow, b], ?_⟩

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = b

    constructor

    · rintro ⟨rfl | rfl, hn⟩; exact (hn ha).elim; rfl

    · rintro rfl; exact ⟨Or.inr rfl, hb⟩

  · right; left; refine ⟨a, by simp [cutRow, a], ?_⟩

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = a

    constructor

    · rintro ⟨rfl | rfl, hn⟩; rfl; exact (hn hb).elim

    · rintro rfl; exact ⟨Or.inl rfl, ha⟩

  · right; right

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = a ∨ x = b

    aesop

Definitions and proofs are in the paired Lean module.

section Forest

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- These are the actual surviving two-element rows after singleton absorption. -/

def alive (k : Fin (m - 1)) : Prop :=

  ∃ c : (localRows m hm A B).chords,

    (localRows m hm A B).row c = cutRow m hm k ∧

      Disjoint (cutRow m hm k) (forced (localRows m hm A B))

Definitions and proofs are in the paired Lean module.

/-- Graph built FROM the actual rows. There is no forest/certificate argument. -/

def reducedGraph : SimpleGraph (Fin m) where

  Adj a b := ∃ k : Fin (m - 1), alive m hm A B k ∧

    ((a.val = k.val ∧ b.val = k.val + 1) ∨

     (b.val = k.val ∧ a.val = k.val + 1))

  symm := ⟨by rintro a b ⟨k, hk, h⟩; exact ⟨k, hk, h.symm⟩⟩

  loopless := ⟨by rintro a ⟨k, hk, h | h⟩ <;> omega⟩

Definitions and proofs are in the paired Lean module.

/-- Exact interval of intact cuts; used only AFTER its equivalence to walks. -/

def interval (a b : Fin m) : Prop := ∀ k : Fin (m - 1),

  min a.val b.val ≤ k.val → k.val < max a.val b.val → alive m hm A B k

Definitions and proofs are in the paired Lean module.

private theorem interval_refl (a : Fin m) : interval m hm A B a a := by

  intro k hl hu

  simp only [min_self, max_self] at hl hu

  omega

Definitions and proofs are in the paired Lean module.

private theorem interval_symm {a b : Fin m} (h : interval m hm A B a b) :

    interval m hm A B b a := by

  simpa only [interval, min_comm, max_comm] using h

Definitions and proofs are in the paired Lean module.

private theorem interval_trans {a b c : Fin m}

    (h : interval m hm A B a b) (g : interval m hm A B b c) :

    interval m hm A B a c := by

  intro k hl hu

  by_cases h1 : min a.val b.val ≤ k.val ∧ k.val < max a.val b.val

  · exact h k h1.1 h1.2

  · apply g k <;> omega

Definitions and proofs are in the paired Lean module.

/-- A walk crossing an original path cut must use THAT surviving cut.

Induction is on a genuine mathlib Walk, not a bounded mask control. -/

private theorem walk_interval {a b : Fin m} (p : (reducedGraph m hm A B).Walk a b) :

    interval m hm A B a b := by

  induction p with

  | nil => exact interval_refl m hm A B _

  | @cons a b c hab p ih =>

      apply interval_trans m hm A B (b := b) ?_ ih

      obtain ⟨j, hj, h | h⟩ := hab

      · intro k hl hu

        have he : k = j := Fin.ext (by omega)

        exact he.symm ▸ hj

      · intro k hl hu

        have he : k = j := Fin.ext (by omega)

        exact he.symm ▸ hj

Definitions and proofs are in the paired Lean module.

private def ascend (a b : Fin m) (hab : a.val ≤ b.val)

    (h : interval m hm A B a b) : (reducedGraph m hm A B).Walk a b := by

  by_cases he : a = b

  · subst b; exact .nil

  · have hlt : a.val < b.val := by

      have hn : a.val ≠ b.val := fun he' => he (Fin.ext he')

      omega

    let next : Fin m := ⟨a.val + 1, by omega⟩

    let k : Fin (m - 1) := ⟨a.val, by omega⟩

    have hk : alive m hm A B k := h k (by simp [k] <;> omega) (by simp [k] <;> omega)

    have ht : interval m hm A B next b := by

      intro j hl hu

      apply h j <;> try dsimp [next] at * <;> omega

    exact .cons ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩

      (ascend next b (by try dsimp [next]; omega) ht)

termination_by b.val - a.val

 decreasing_by

   change b.val - (a.val + 1) < b.val - a.val

   omega

Definitions and proofs are in the paired Lean module.

/-- Exact graph connectivity, with neither direction supplied as input data. -/

theorem connected_iff_interval (a b : Fin m) :

    Nonempty ((reducedGraph m hm A B).Walk a b) ↔ interval m hm A B a b := by

  constructor

  · exact fun ⟨p⟩ => walk_interval m hm A B p

  · intro h

    by_cases hab : a.val ≤ b.val

    · exact ⟨ascend m hm A B a b hab h⟩

    · exact ⟨(ascend m hm A B b a (by omega)

        (interval_symm m hm A B h)).reverse⟩

Definitions and proofs are in the paired Lean module.

private theorem alive_supported (k : Fin (m - 1)) (h : alive m hm A B k) :

    cutRow m hm k ⊆ (localRows m hm A B).ground := by

  obtain ⟨c, hc, _⟩ := h

  exact hc ▸ (localRows m hm A B).row_supported c

Definitions and proofs are in the paired Lean module.

/-- Original surviving positions, including every isolated/forced ghost label. -/

def live : Finset (Fin m) := Finset.univ.filter

  (fun a => «at» m hm a ∈ (localRows m hm A B).ground)

Definitions and proofs are in the paired Lean module.

/-- Actual graph components, represented on the original finite coordinate order. -/

def component (a : Fin m) : Finset (Fin m) :=

  (live m hm A B).filter (fun b => Nonempty ((reducedGraph m hm A B).Walk a b))

Definitions and proofs are in the paired Lean module.

def components : Finset (Finset (Fin m)) :=

  (live m hm A B).image (component m hm A B)

Definitions and proofs are in the paired Lean module.

def block (a : Fin m) : Finset (Label m) :=

  (component m hm A B a).image («at» m hm)

Definitions and proofs are in the paired Lean module.

private theorem mem_component (a b : Fin m) :

    b ∈ component m hm A B a ↔ b ∈ live m hm A B ∧ interval m hm A B a b := by

  simp only [component, Finset.mem_filter, connected_iff_interval]

Definitions and proofs are in the paired Lean module.

private theorem self_component (a : Fin m) (ha : a ∈ live m hm A B) :

    a ∈ component m hm A B a :=

  (mem_component m hm A B a a).mpr ⟨ha, interval_refl m hm A B a⟩

Definitions and proofs are in the paired Lean module.

/-- Distinct components are disjoint; this also includes singleton constraints. -/

theorem component_partition (a b : Fin m) (ha : a ∈ live m hm A B)

    (hb : b ∈ live m hm A B) :

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b) := by

  by_cases h : interval m hm A B a b

  · left

    ext c

    rw [mem_component, mem_component]

    constructor

    · rintro ⟨hc, hac⟩

      exact ⟨hc, interval_trans m hm A B (interval_symm m hm A B h) hac⟩

    · rintro ⟨hc, hbc⟩

      exact ⟨hc, interval_trans m hm A B h hbc⟩

  · right

    apply Finset.disjoint_left.mpr

    intro c hc hd

    have hac := ((mem_component m hm A B a c).mp hc).2

    have hbc := ((mem_component m hm A B b c).mp hd).2

    exact h (interval_trans m hm A B hac (interval_symm m hm A B hbc))

Definitions and proofs are in the paired Lean module.

/-- Every position between two vertices of a component actually survives.

Thus these are consecutive original intervals, not paths through new shortcuts. -/

theorem component_consecutive (a x y z : Fin m)

    (hx : x ∈ component m hm A B a) (hy : y ∈ component m hm A B a)

    (hxz : x.val ≤ z.val) (hzy : z.val ≤ y.val) :

    z ∈ component m hm A B a := by

  obtain ⟨hxL, hax⟩ := (mem_component m hm A B a x).mp hx

  obtain ⟨hyL, hay⟩ := (mem_component m hm A B a y).mp hy

  have hxy := interval_trans m hm A B (interval_symm m hm A B hax) hay

  by_cases he : z = y

  · simpa [he] using hy

  · have hzy' : z.val < y.val := by

      have hn : z.val ≠ y.val := fun h => he (Fin.ext h)

      omega

    let k : Fin (m - 1) := ⟨z.val, by omega⟩

    have hk : alive m hm A B k := hxy k (by dsimp [k]; omega) (by dsimp [k]; omega)

    have hzL : z ∈ live m hm A B := by

      apply Finset.mem_filter.mpr

      refine ⟨Finset.mem_univ _, ?_⟩

      exact alive_supported m hm A B k hk (by simp [cutRow, k])

    apply (mem_component m hm A B a z).mpr

    refine ⟨hzL, interval_trans m hm A B hax ?_⟩

    intro j hl hu

    apply hxy j <;> omega

Definitions and proofs are in the paired Lean module.

/-- Component membership is exactly the original surviving graph relation. -/

theorem block_mem (a b : Fin m) : «at» m hm b ∈ block m hm A B a ↔

    b ∈ live m hm A B ∧ Nonempty ((reducedGraph m hm A B).Walk a b) := by

  rw [block, Finset.mem_image]

  constructor

  · rintro ⟨c, hc, he⟩

    have he' := at_injective m hm he

    subst c

    exact Finset.mem_filter.mp hc

  · intro h

    exact ⟨b, Finset.mem_filter.mpr h, rfl⟩

Definitions and proofs are in the paired Lean module.

end Forest

Definitions and proofs are in the paired Lean module.

section RowComponents

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

private theorem block_supported (a : Fin m) :

    block m hm A B a ⊆ (localRows m hm A B).ground := by

  rintro x hx

  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx

  exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hb).1)).2

Definitions and proofs are in the paired Lean module.

/-- Exact reduced indexed row readback. A singleton stays a constraint,

whereas only the redundant size-two rows have been removed. -/

theorem reduced_row_cases (c : (prune (localRows m hm A B)).chords) :

    (prune (localRows m hm A B)).row c = ∅ ∨

    (∃ a ∈ live m hm A B,

      (prune (localRows m hm A B)).row c = {«at» m hm a} ∧

        «at» m hm a ∈ forced (localRows m hm A B)) ∨

    (∃ k : Fin (m - 1), alive m hm A B k ∧

      (prune (localRows m hm A B)).row c = cutRow m hm k) := by

  obtain ⟨k, hkA, hr, h0 | h1 | h2⟩ := projected_row_cases m hm A B c.1

  · exact Or.inl h0

  · obtain ⟨x, hx, he⟩ := h1

    have hxU : x ∈ (localRows m hm A B).ground :=

      (localRows m hm A B).row_supported c.1 (by simp [he])

    have hxG : x ∈ ground m := (Finset.mem_sdiff.mp hxU).1

    let a : Fin m := ⟨position m x, position_lt m hm x hxG⟩

    have hat : «at» m hm a = x := at_position m hm x hxG

    exact Or.inr (Or.inl ⟨a, by simp [live, hat, hxU], by simpa [prune, hat] using he,

      by rw [hat, mem_forced]; exact ⟨c.1, he⟩⟩)

  · have hd : Disjoint (cutRow m hm k) (forced (localRows m hm A B)) := by

      rcases c.2 with hn | hd

      · exact (hn (by rw [h2]; exact cutRow_card m hm k)).elim

      · simpa only [h2] using hd

    exact Or.inr (Or.inr ⟨k, ⟨c.1, h2, hd⟩, h2⟩)

Definitions and proofs are in the paired Lean module.

private theorem adj_unforced {a b : Fin m} (h : (reducedGraph m hm A B).Adj a b) :

    «at» m hm a ∉ forced (localRows m hm A B) ∧

    «at» m hm b ∉ forced (localRows m hm A B) := by

  obtain ⟨k, ⟨c, hc, hd⟩, hor⟩ := h

  have ha : «at» m hm a ∈ cutRow m hm k := by

    rcases hor with h | h

    · have he : a = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      simp [cutRow, he]

    · have he : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, he]

  have hb : «at» m hm b ∈ cutRow m hm k := by

    rcases hor with h | h

    · have he : b = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, he]

    · have he : b = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      simp [cutRow, he]

  exact ⟨fun hf => Finset.disjoint_left.mp hd ha hf,

    fun hf => Finset.disjoint_left.mp hd hb hf⟩

Definitions and proofs are in the paired Lean module.

/-- Forced labels are actual one-vertex graph components, not deleted vertices. -/

theorem forced_component (a : Fin m) (ha : a ∈ live m hm A B)

    (hf : «at» m hm a ∈ forced (localRows m hm A B)) :

    component m hm A B a = {a} := by

  ext b

  constructor

  · intro hb

    obtain ⟨p⟩ := (Finset.mem_filter.mp hb).2

    have he : a = b := by

      cases p with

      | nil => rfl

      | cons hab p => exact ((adj_unforced m hm A B hab).1 hf).elim

    exact Finset.mem_singleton.mpr he.symm

  · intro hb

    have he := Finset.mem_singleton.mp hb

    subst b

    exact self_component m hm A B a ha

Definitions and proofs are in the paired Lean module.

/-- Every reduced nonempty row belongs to a derived consecutive component. -/

private theorem row_block (c : (prune (localRows m hm A B)).chords)

    (hne : (prune (localRows m hm A B)).row c ≠ ∅) :

    ∃ a ∈ live m hm A B, (prune (localRows m hm A B)).row c ⊆ block m hm A B a := by

  rcases reduced_row_cases m hm A B c with h0 | h1 | h2

  · exact (hne h0).elim

  · obtain ⟨a, ha, he, hf⟩ := h1

    refine ⟨a, ha, ?_⟩

    rw [he]

    exact Finset.singleton_subset_iff.mpr

      ((block_mem m hm A B a a).mpr ⟨ha, ⟨.nil⟩⟩)

  · obtain ⟨k, hk, he⟩ := h2

    let a : Fin m := ⟨k.val, by omega⟩

    let b : Fin m := ⟨k.val + 1, by omega⟩

    have ha : a ∈ live m hm A B := by

      apply Finset.mem_filter.mpr

      exact ⟨Finset.mem_univ _, alive_supported m hm A B k hk (by simp [cutRow, a])⟩

    have hb : b ∈ live m hm A B := by

      apply Finset.mem_filter.mpr

      exact ⟨Finset.mem_univ _, alive_supported m hm A B k hk (by simp [cutRow, b])⟩

    refine ⟨a, ha, ?_⟩

    rw [he]

    intro x hx

    rcases (show x = «at» m hm a ∨ x = «at» m hm b by simpa [cutRow, a, b] using hx) with rfl | rfl

    · exact (block_mem m hm A B a a).mpr ⟨ha, ⟨.nil⟩⟩

    · exact (block_mem m hm A B a b).mpr

        ⟨hb, ⟨.cons ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩ .nil⟩⟩

Definitions and proofs are in the paired Lean module.

/-- Component rows retain their actual original filtered index as a subtype. -/

def componentRows (a : Fin m) : Rows (Label m) where

  ground := block m hm A B a

  chords := {c : (prune (localRows m hm A B)).chords //

    (prune (localRows m hm A B)).row c ⊆ block m hm A B a}

  row c := (prune (localRows m hm A B)).row c.1

  row_supported c := c.2

Definitions and proofs are in the paired Lean module.

/-- Union of component noncovers padded by ALL other HistoryCorners.residual coordinates.

The existential over starts merely repeats equal components, without altering rows. -/

def componentUnion : Family (Label m) where

  carrier := {s | ∃ a ∈ live m hm A B,

    s ∈ rawJoin (componentRows m hm A B a).root

      (delta ((localRows m hm A B).ground \ block m hm A B a))}

  lower' := by

    rintro s t h ⟨a, ha, hs⟩

    exact ⟨a, ha, (rawJoin (componentRows m hm A B a).root

      (delta ((localRows m hm A B).ground \ block m hm A B a))).lower h hs⟩

Definitions and proofs are in the paired Lean module.

/-- Exact finite linear-forest decomposition, consumed by the parent readback.

No component, forest or equality is an input; only the separate empty-row branch

is excluded, because that branch is already a simplex. -/

theorem component_root (h0 : ∀ c : (localRows m hm A B).chords,

    (localRows m hm A B).row c ≠ ∅) :

    (localRows m hm A B).root = componentUnion m hm A B := by

  rw [← prune_root]

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c, hc⟩

    obtain ⟨a, ha, hrow⟩ := row_block m hm A B c (h0 c.1)

    refine ⟨a, ha, s ∩ block m hm A B a, ⟨⟨c, hrow⟩, ?_⟩,

      s \ block m hm A B a, ?_, ?_⟩

    · intro x hx

      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2,

        (Finset.mem_sdiff.mp (hc (Finset.mem_inter.mp hx).1)).2⟩

    · intro x hx

      obtain ⟨hxs, hxC⟩ := Finset.mem_sdiff.mp hx

      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hc hxs)).1, hxC⟩

    · ext x

      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]

      tauto

  · rintro ⟨a, ha, u, ⟨c, hc⟩, v, hv, rfl⟩

    refine ⟨c.1, ?_⟩

    intro x hx

    rcases Finset.mem_union.mp hx with hxu | hxv

    · obtain ⟨hxC, hxq⟩ := Finset.mem_sdiff.mp (hc hxu)

      exact Finset.mem_sdiff.mpr ⟨block_supported m hm A B a hxC, hxq⟩

    · obtain ⟨hxU, hxC⟩ := Finset.mem_sdiff.mp (hv hxv)

      exact Finset.mem_sdiff.mpr ⟨hxU, fun hxq => hxC (c.2 hxq)⟩

Definitions and proofs are in the paired Lean module.

/-- An isolated unforced HistoryCorners.residual coordinate is retained as its own component,

including when the surviving indexed row type is empty. -/

theorem isolated_component (a : Fin m) (ha : a ∈ live m hm A B)

    (h : ∀ b, ¬ (reducedGraph m hm A B).Adj a b) :

    component m hm A B a = {a} := by

  ext b

  constructor

  · intro hb

    obtain ⟨p⟩ := (Finset.mem_filter.mp hb).2

    have he : a = b := by

      cases p with

      | nil => rfl

      | cons hab p => exact (h _ hab).elim

    exact Finset.mem_singleton.mpr he.symm

  · intro hb

    have he := Finset.mem_singleton.mp hb

    subst b

    exact self_component m hm A B a ha

end RowComponents

Definitions and proofs are in the paired Lean module.

section Untouched

variable (m : Nat) (hm : 3 ≤ m)

Definitions and proofs are in the paired Lean module.

def leftEnd : Fin m := ⟨0, by omega⟩

def rightEnd : Fin m := ⟨m - 1, by omega⟩

Definitions and proofs are in the paired Lean module.

private theorem at_leftEnd : «at» m hm (leftEnd m hm) = secondLabel m hm := by

  simp [«at», leftEnd, secondLabel, show 0 + 1 ≠ m by omega]

private theorem at_rightEnd : «at» m hm (rightEnd m hm) = firstLabel m hm := by

  simp [«at», rightEnd, firstLabel, show m - 1 + 1 = m by omega]

Definitions and proofs are in the paired Lean module.

private theorem unmasked_forced : forced (localRows m hm ∅ ∅) = ∅ := by

  apply Finset.eq_empty_iff_forall_notMem.mpr

  intro x hx

  obtain ⟨c, hc⟩ := (mem_forced _ x).mp hx

  have ho := original_row m hm c.1

  have hcard : ((localRows m hm ∅ ∅).row c).card = 2 := by

    change (rimEdge m (by omega) c.1.1 \ ∅).card = 2

    rw [Finset.sdiff_empty, ho]

    exact cutRow_card m hm _

  rw [hc, Finset.card_singleton] at hcard

  omega

Definitions and proofs are in the paired Lean module.

private theorem unmasked_root : (localRows m hm ∅ ∅).root = pathRoot m hm := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c, hc⟩

    exact ⟨c.1, by simpa [localRows, cornerRows, HistoryCorners.residual] using hc⟩

  · rintro ⟨c, hc⟩

    exact ⟨⟨c, by simp⟩, by simpa [localRows, cornerRows, HistoryCorners.residual] using hc⟩

Definitions and proofs are in the paired Lean module.

/-- The critical arbitrary-width theorem. Connecting the ORIGINAL two path

endpoints in the actual reduced row graph forces every original cut to survive,

then every original label to survive. The masks are LOCAL original subsets.

No intactness, singleton absence or path certificate is a premise. -/

theorem endpoints_connected_untouched (A B : Finset (Label m))

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (h : Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))) :

    A = ∅ ∧ B = ∅ ∧ forced (localRows m hm A B) = ∅ ∧

      component m hm A B (leftEnd m hm) = Finset.univ ∧

      components m hm A B = {Finset.univ} ∧

      block m hm A B (leftEnd m hm) = ground m ∧

      (localRows m hm A B).root = pathRoot m hm := by

  have hcuts : ∀ k : Fin (m - 1), alive m hm A B k := by

    intro k

    apply (connected_iff_interval m hm A B _ _).mp h k <;>

      dsimp [leftEnd, rightEnd] <;> omega

  have hall : ∀ a : Fin m, «at» m hm a ∈ (localRows m hm A B).ground := by

    intro a

    by_cases ha : a.val < m - 1

    · let k : Fin (m - 1) := ⟨a.val, ha⟩

      exact alive_supported m hm A B k (hcuts k) (by simp [cutRow, k])

    · let k : Fin (m - 1) := ⟨m - 2, by omega⟩

      have he : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext (by have := a.isLt; dsimp [k]; omega)

      exact alive_supported m hm A B k (hcuts k) (by simp [cutRow, he])

  have hremain : ∀ x ∈ ground m, x ∈ (localRows m hm A B).ground := by

    intro x hx

    have hh := hall ⟨position m x, position_lt m hm x hx⟩

    rw [at_position m hm x hx] at hh

    exact hh

  have hAe : A = ∅ := by

    apply Finset.eq_empty_iff_forall_notMem.mpr

    intro x hx

    exact (Finset.mem_sdiff.mp (hremain x (hA hx))).2 (Finset.mem_union_left _ hx)

  have hBe : B = ∅ := by

    apply Finset.eq_empty_iff_forall_notMem.mpr

    intro x hx

    exact (Finset.mem_sdiff.mp (hremain x (hB hx))).2 (Finset.mem_union_right _ hx)

  have hcomp : ∀ a : Fin m, component m hm A B a = Finset.univ := by

    intro a

    ext b

    simp only [mem_component, live, Finset.mem_filter, Finset.mem_univ, true_and]

    exact ⟨fun _ => trivial, fun _ => ⟨hall b, fun k _ _ => hcuts k⟩⟩

  refine ⟨hAe, hBe, by simpa only [hAe, hBe] using unmasked_forced m hm,

    hcomp _, ?_, ?_, by simpa only [hAe, hBe] using unmasked_root m hm⟩

  · ext C

    simp only [components, Finset.mem_image, Finset.mem_singleton]

    constructor

    · rintro ⟨a, ha, rfl⟩; exact hcomp a

    · rintro rfl

      exact ⟨leftEnd m hm, by simp [live, hall], hcomp _⟩

  · rw [block, hcomp]

    ext x

    simp only [Finset.mem_image, Finset.mem_univ, true_and]

    exact ⟨fun ⟨a, ha⟩ => ha ▸ at_ground m hm a,

      fun hx => ⟨⟨position m x, position_lt m hm x hx⟩, at_position m hm x hx⟩⟩

end Untouched

Definitions and proofs are in the paired Lean module.

section Markers

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Surviving ORIGINAL interface markers, not endpoints invented after projection. -/

def markers : Finset (Label m) := rim m hm ∩ (localRows m hm A B).ground

Definitions and proofs are in the paired Lean module.

private theorem residual_without_markers :

    (localRows m hm A B).ground \ markers m hm A B =

      (localRows m hm A B).ground \ rim m hm := by

  ext x

  simp only [markers, Finset.mem_sdiff, Finset.mem_inter]

  tauto

Definitions and proofs are in the paired Lean module.

/-- This data is constructed from actual masks. Its proof fields are OUTPUTS;

there is no constructor argument of this type in classifyMarkers. -/

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

def classifyMarkers (hA : A ⊆ ground m) (hB : B ⊆ ground m) :

    MarkerCase m hm A B := by

  classical

  by_cases h : Disjoint A (rim m hm)

  · by_cases hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B)

    · by_cases hf : firstLabel m hm ∈ (localRows m hm A B).ground

      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground

        · have hR : markers m hm A B = rim m hm := by

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · exact fun hh => hh.1

            · rintro (rfl | rfl) <;> simp_all

          by_cases hc : Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))

          · obtain ⟨hAe, hBe, hFe, full, sole, labels, root⟩ :=

              endpoints_connected_untouched m hm A B hA hB hc

            exact .intact hAe hBe hFe full sole labels root

          · exact .separated h hF hR hc

        · have hR : markers m hm A B = {«at» m hm (rightEnd m hm)} := by

            rw [at_rightEnd]

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · rintro ⟨rfl | rfl, hx⟩; rfl; exact (hs hx).elim

            · rintro rfl; exact ⟨Or.inl rfl, hf⟩

          exact .oneMarker h (rightEnd m hm) (by simp [live, at_rightEnd, hf])

            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR

      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground

        · have hR : markers m hm A B = {«at» m hm (leftEnd m hm)} := by

            rw [at_leftEnd]

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · rintro ⟨rfl | rfl, hx⟩; exact (hf hx).elim; rfl

            · rintro rfl; exact ⟨Or.inr rfl, hs⟩

          exact .oneMarker h (leftEnd m hm) (by simp [live, at_leftEnd, hs])

            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR

        · apply MarkerCase.noMarker h hF

          ext x

          simp only [markers, rim, Finset.mem_inter, Finset.mem_insert,

            Finset.mem_singleton, Finset.notMem_empty, iff_false]

          rintro ⟨rfl | rfl, hx⟩

          · exact hf hx

          · exact hs hx

    · have hFR : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty := by

        obtain ⟨x, hxF, hxR⟩ := Finset.not_disjoint_iff.mp hF

        exact ⟨x, Finset.mem_inter.mpr ⟨hxF, hxR⟩⟩

      exact .absorbed h hFR

  · exact .absent h

Definitions and proofs are in the paired Lean module.

/-- The two surviving separated markers really occupy disjoint components. -/

theorem separated_components

    (hL : leftEnd m hm ∈ live m hm A B) (hR : rightEnd m hm ∈ live m hm A B)

    (h : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))) :

    Disjoint (component m hm A B (leftEnd m hm))

      (component m hm A B (rightEnd m hm)) := by

  rcases component_partition m hm A B _ _ hL hR with he | hd

  · have hx := self_component m hm A B (rightEnd m hm) hR

    rw [← he] at hx

    exact (h ((Finset.mem_filter.mp hx).2)).elim

  · exact hd

Definitions and proofs are in the paired Lean module.

/-- Literal last-wheel parent factor on an arbitrary physical ambient type.

The old X,D,L coordinates need not fit inside the wheel's finite label type. -/

def decorated {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)

    (X : Finset V) (D L : Family V) : Family V :=

  (rawJoin (delta X) (renameFamily f (localRows m hm A B).root) ⊔

    rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

    if Disjoint A (rim m hm) then

      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) else ⊥

Definitions and proofs are in the paired Lean module.

/-- A singleton at an actual surviving interface marker absorbs the D fibre.

No old label or HistoryCorners.residual local ghost is removed by this family equality. -/

theorem forced_marker_absorbs {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D : Family V) (hD : Supported X D)

    (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty) :

    rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) ≤

      rawJoin (delta X) (renameFamily f (localRows m hm A B).root) := by

  obtain ⟨z, hz⟩ := hF

  obtain ⟨hzF, hzR⟩ := Finset.mem_inter.mp hz

  obtain ⟨c, hc⟩ := (mem_forced _ z).mp hzF

  have hzrim : z ∈ rim m hm := (Finset.mem_inter.mp hzR).1

  rintro s ⟨u, hu, v, hv, rfl⟩

  obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hv

  refine ⟨u, hD u hu, t.image f, ⟨t, ⟨c, ?_⟩, rfl⟩, rfl⟩

  intro x hx

  obtain ⟨hxU, hxr⟩ := Finset.mem_sdiff.mp (ht hx)

  refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩

  intro hxq

  have he : x = z := by simpa [hc] using hxq

  exact hxr (he.symm ▸ hzrim)

Definitions and proofs are in the paired Lean module.

/-- The computed case is consumed in the actual ambient factor normal form. -/

def markerNormalForm {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)

    (X : Finset V) (D L : Family V) : MarkerCase m hm A B → Family V

  | .absent _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin L (delta ((localRows m hm A B).ground.image f))

  | .absorbed _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin L (delta ((localRows m hm A B).ground.image f))

  | .noMarker _ _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin D (delta ((localRows m hm A B).ground.image f))

  | .oneMarker _ a _ _ _ =>

      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

      rawJoin D (delta (((localRows m hm A B).ground \ {«at» m hm a}).image f))

  | .separated _ _ _ _ =>

      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f))

  | .intact _ _ _ _ _ _ _ =>

      (rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔ rawJoin L (delta ((ground m).image f))) ⊔

      rawJoin D (delta ((tailGround m hm).image f))

Definitions and proofs are in the paired Lean module.

/-- Exhaustive actual-mask consumer. Earlier face factors have only their genuine

support and L≤D; no classification, forest, equality, Output or collapse is assumed. -/

theorem decorated_readback {V : Type*} [Fintype V] [DecidableEq V]

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D) :

    decorated m hm A B f X D L =

      markerNormalForm m hm A B f X D L (classifyMarkers m hm A B hA hB) := by

  have hE := congrArg (renameFamily f) (component_root m hm A B h0)

  generalize he : classifyMarkers m hm A B hA hB = c

  cases c with

  | absent h => simp only [decorated, markerNormalForm, if_neg h, sup_bot_eq, hE]

  | absorbed h hf =>

      have hle := forced_marker_absorbs m hm A B f X D hD hf

      rw [decorated, if_pos h, sup_eq_left.mpr (hle.trans le_sup_left)]

      simp only [markerNormalForm, hE]

  | noMarker h hf hr =>

      have hg : (localRows m hm A B).ground \ rim m hm = (localRows m hm A B).ground := by

        rw [← residual_without_markers m hm A B, hr, Finset.sdiff_empty]

      have hle : rawJoin L (delta ((localRows m hm A B).ground.image f)) ≤

          rawJoin D (delta ((localRows m hm A B).ground.image f)) := by

        rintro s ⟨u, hu, v, hv, rfl⟩

        exact ⟨u, hLD hu, v, hv, rfl⟩

      simp only [decorated, markerNormalForm, if_pos h, hg, hE]

      rw [sup_assoc, sup_eq_right.mpr hle]

  | oneMarker h a ha hf hr =>

      have hg : (localRows m hm A B).ground \ rim m hm =

          (localRows m hm A B).ground \ {«at» m hm a} := by

        rw [← residual_without_markers m hm A B, hr]

      simp only [decorated, markerNormalForm, if_pos h, hg, hE]

  | separated h hf hr apart =>

      simp only [decorated, markerNormalForm, if_pos h, hE]

  | intact ha hb hf full sole labels root =>

      have hg : (localRows m hm A B).ground = ground m := by

        simp [localRows, cornerRows, HistoryCorners.residual, ha, hb, Rows.without, rimRows]

      have hAR : Disjoint A (rim m hm) := by simp [ha]

      simp only [decorated, markerNormalForm, if_pos hAR, root, hg, tailGround]

end Markers

Definitions and proofs are in the paired Lean module.

section PhysicalTransport

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- Injective transport of the literal FILTER-then-PROJECT indexed corner.

Reuse renameRows/renameRows_root; no second relabel engine is defined. -/

theorem corner_rows_transport (f : U ↪ V) (r : Rows U) (A B : Finset U) :

    (cornerRows (renameRows f r) (A.image f) (B.image f)).root =

      renameFamily f (cornerRows r A B).root := by

  have hg : HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) =

      (HistoryCorners.residual r.ground A B).image f := by

    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]

  apply SetLike.ext

  intro s

  change (∃ c : {c : r.chords // Disjoint ((r.row c).image f) (A.image f)},

    s ⊆ HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) \

      ((r.row c.1).image f \ B.image f)) ↔

    ∃ t, (∃ c : {c : r.chords // Disjoint (r.row c) A},

      t ⊆ HistoryCorners.residual r.ground A B \ (r.row c.1 \ B)) ∧ t.image f = s

  simp only [Finset.disjoint_image f.injective, hg,

    ← Finset.image_sdiff _ _ f.injective]

  constructor

  · rintro ⟨c, hc⟩

    obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hc

    exact ⟨t, ⟨⟨c.1, (Finset.disjoint_image f.injective).mp c.2⟩, ht⟩, rfl⟩

  · rintro ⟨t, ⟨c, hc⟩, rfl⟩

    exact ⟨⟨c.1, (Finset.disjoint_image f.injective).mpr c.2⟩,

      Finset.image_subset_image hc⟩

Definitions and proofs are in the paired Lean module.

/-- This is the actual physical wheel consumer: the source is its real path-row

root with precisely the interface rim row removed, not a supplied row model. -/

theorem physical_corner_transport (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A B : Finset (Label m)) (hA : A ⊆ ground m) :

    corner ((ground m).image f) (A.image f) (B.image f)

      (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =

      renameFamily f (localRows m hm A B).root := by

  let r := (rimRows m (by omega)).without (interfaceRow m hm)

  have hr : ((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root =

      (renameRows f r).root :=

    (PhysicalMWheel.ambient_without m hm f).trans (renameRows_root f r).symm

  rw [hr]

  change corner (renameRows f r).ground (A.image f) (B.image f) (renameRows f r).root = _

  rw [corner_root (renameRows f r) (A.image f) (B.image f)

    (Finset.image_subset_image hA), corner_rows_transport]

  rfl

Definitions and proofs are in the paired Lean module.

/-- Every disjoint ambient local mask is read back to ORIGINAL coordinates.

The full image of the ground is preserved, even at labels absent from every face. -/

theorem physical_original_masks (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A' B' : Finset V) (hA' : A' ⊆ (ground m).image f)

    (hB' : B' ⊆ (ground m).image f) (hAB' : Disjoint A' B') :

    ∃ A B : Finset (Label m), A ⊆ ground m ∧ B ⊆ ground m ∧ Disjoint A B ∧

      A.image f = A' ∧ B.image f = B' ∧

      corner ((ground m).image f) A' B'

        (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =

        renameFamily f (localRows m hm A B).root := by

  obtain ⟨A, hA, rfl⟩ := Finset.subset_image_iff.mp hA'

  obtain ⟨B, hB, rfl⟩ := Finset.subset_image_iff.mp hB'

  exact ⟨A, B, hA, hB, (Finset.disjoint_image f.injective).mp hAB',

    rfl, rfl, physical_corner_transport m hm f A B hA⟩

end PhysicalTransport

Definitions and proofs are in the paired Lean module.

section ExactPathReadback

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Reuse the frozen path edge theorem and pathRows_mem; equality of roots does

not replace the indexed localRows presentation used by all classification data. -/

theorem local_path_root (hA : A ⊆ ground m) :

    (localRows m hm A B).root = corner (ground m) A B

      (HistoryPaths.pathRows (pathRootPath m hm)).root := by

  have hp : pathRoot m hm = (HistoryPaths.pathRows (pathRootPath m hm)).root := by

    apply SetLike.ext

    intro s

    rw [HistoryPaths.pathRows_mem, pathRootPath_vertices, pathRootPath_row_edges]

    constructor

    · rintro ⟨i, hi⟩

      refine ⟨hi.trans Finset.sdiff_subset, rimEdge m (by omega) i.1,

        Finset.mem_image.mpr ⟨i.1, Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩, rfl⟩, ?_⟩

      exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_sdiff.mp (hi hxs)).2 hx)

    · rintro ⟨hs, q, hq, hdis⟩

      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq

      refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩

      intro x hx

      exact Finset.mem_sdiff.mpr ⟨hs hx, fun hq => Finset.disjoint_left.mp hdis hq hx⟩

  rw [← hp]

  exact (corner_root ((rimRows m (by omega)).without (interfaceRow m hm)) A B hA).symm

Definitions and proofs are in the paired Lean module.

/-- Each derived consecutive component has exactly its consecutive path edges.

Together with component_consecutive this is a linear forest, including isolated

HistoryCorners.residual labels and the singleton constraint components. -/

theorem component_edges (a x y : Fin m)

    (hx : x ∈ component m hm A B a) (hy : y ∈ component m hm A B a) :

    (reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val := by

  constructor

  · rintro ⟨k, hk, h | h⟩ <;> omega

  · intro h

    have hxy := interval_trans m hm A B

      (interval_symm m hm A B ((mem_component m hm A B a x).mp hx).2)

      ((mem_component m hm A B a y).mp hy).2

    rcases h with h | h

    · let k : Fin (m - 1) := ⟨x.val, by have := y.isLt; omega⟩

      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),

        Or.inl ⟨rfl, h.symm⟩⟩

    · let k : Fin (m - 1) := ⟨y.val, by have := x.isLt; omega⟩

      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),

        Or.inr ⟨rfl, h.symm⟩⟩

Definitions and proofs are in the paired Lean module.

/-- The graph edges are EXACTLY the surviving size-two indexed rows.

No graph connectivity or desired edge relation is assumed. -/

theorem graph_actual_rows (a b : Fin m) :

    (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

      ∃ c : (prune (localRows m hm A B)).chords,

        (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b} := by

  constructor

  · rintro ⟨k, ⟨c, hc, hd⟩, hor⟩

    have hn : a ≠ b := by intro he; subst b; rcases hor with h | h <;> omega

    refine ⟨hn, ⟨c, Or.inr (by simpa only [hc] using hd)⟩, ?_⟩

    change (localRows m hm A B).row c = _

    rw [hc]

    rcases hor with h | h

    · have ha : a = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      have hb : b = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, ha, hb]

    · have hb : b = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      have ha : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, ha, hb, Finset.pair_comm]

  · rintro ⟨hab, c, hc⟩

    have hne : «at» m hm a ≠ «at» m hm b := fun h => hab (at_injective m hm h)

    have hcard : ((prune (localRows m hm A B)).row c).card = 2 := by simp [hc, hne]

    rcases reduced_row_cases m hm A B c with h0 | h1 | h2

    · rw [h0, Finset.card_empty] at hcard; omega

    · obtain ⟨i, hi, he, hf⟩ := h1

      rw [he, Finset.card_singleton] at hcard; omega

    · obtain ⟨k, hk, he⟩ := h2

      have hea : «at» m hm a ∈ cutRow m hm k := by rw [← he, hc]; simp

      have heb : «at» m hm b ∈ cutRow m hm k := by rw [← he, hc]; simp

      have ha : a.val = k.val ∨ a.val = k.val + 1 := by

        rcases (show «at» m hm a = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨

          «at» m hm a = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by

            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using hea) with h | h

        · exact Or.inl (congrArg Fin.val (at_injective m hm h))

        · exact Or.inr (congrArg Fin.val (at_injective m hm h))

      have hb : b.val = k.val ∨ b.val = k.val + 1 := by

        rcases (show «at» m hm b = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨

          «at» m hm b = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by

            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using heb) with h | h

        · exact Or.inl (congrArg Fin.val (at_injective m hm h))

        · exact Or.inr (congrArg Fin.val (at_injective m hm h))

      have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)

      exact ⟨k, hk, by omega⟩

/-- The component partition covers every retained original position. -/

theorem components_cover (a : Fin m) : a ∈ live m hm A B ↔

    ∃ C ∈ components m hm A B, a ∈ C := by

  constructor

  · intro ha

    exact ⟨component m hm A B a,

      Finset.mem_image.mpr ⟨a, ha, rfl⟩, self_component m hm A B a ha⟩

  · rintro ⟨C, hC, ha⟩

    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hC

    exact (Finset.mem_filter.mp ha).1

Definitions and proofs are in the paired Lean module.

/-- This cover is on the ORIGINAL HistoryCorners.residual ground, not on the face support. -/

theorem original_labels (x : Label m) : x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a := by

  constructor

  · intro hx

    have hxG : x ∈ ground m := (Finset.mem_sdiff.mp hx).1

    let a : Fin m := ⟨position m x, position_lt m hm x hxG⟩

    have he : «at» m hm a = x := at_position m hm x hxG

    have ha : a ∈ live m hm A B := by simp [live, he, hx]

    exact ⟨a, ha, he ▸ (block_mem m hm A B a a).mpr ⟨ha, ⟨.nil⟩⟩⟩

  · rintro ⟨a, ha, hx⟩

    exact block_supported m hm A B a hx

Definitions and proofs are in the paired Lean module.

/-- Both original surviving markers occupy extreme positions in their blocks. -/

theorem marker_positions : markers m hm A B ⊆

    {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)} := by

  intro x hx

  have hr := (Finset.mem_inter.mp hx).1

  simpa only [at_leftEnd, at_rightEnd, rim, Finset.mem_insert, Finset.mem_singleton,

    or_comm] using hr

end ExactPathReadback

Definitions and proofs are in the paired Lean module.

section TotalParent

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Exhaustive row terminal state. These constructors contain facts DERIVED from

actual indices, not hypotheses passed to the structural constructor. -/

inductive RowCase : Type

  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)

  | void (none : IsEmpty (localRows m hm A B).chords)

  | forest (some : Nonempty (localRows m hm A B).chords)

      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

Definitions and proofs are in the paired Lean module.

def classifyRows : RowCase m hm A B := by

  classical

  by_cases h : ∃ c : (localRows m hm A B).chords, (localRows m hm A B).row c = ∅

  · exact .simplex (Classical.choose h) (Classical.choose_spec h)

  · have h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅ :=

      fun c hc => h ⟨c, hc⟩

    by_cases hI : Nonempty (localRows m hm A B).chords

    · exact .forest hI h0

    · exact .void ⟨fun c => hI ⟨c⟩⟩

Definitions and proofs are in the paired Lean module.

/-- Raw local root for every computed row state, including zero-ground VOID/UNIT. -/

def rowRootForm : RowCase m hm A B → Family (Label m)

  | .simplex _ _ => delta (localRows m hm A B).ground

  | .void _ => ⊥

  | .forest _ _ => componentUnion m hm A B

Definitions and proofs are in the paired Lean module.

private theorem row_root_readback : (localRows m hm A B).root =

    rowRootForm m hm A B (classifyRows m hm A B) := by

  generalize he : classifyRows m hm A B = c

  cases c with

  | simplex c hc => exact empty_row_root _ c hc

  | void h => exact no_rows_root _ h

  | forest hI h0 => exact component_root m hm A B h0

Definitions and proofs are in the paired Lean module.

/-- An empty local row gives the entire parent simplex; the old factors have

only support hypotheses. No simplex/Output assertion is supplied as a premise. -/

private theorem decorated_simplex {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D)

    (c : (localRows m hm A B).chords) (hc : (localRows m hm A B).row c = ∅) :

    decorated m hm A B f X D L = delta (X ∪ (localRows m hm A B).ground.image f) := by

  have hE : renameFamily f (localRows m hm A B).root =

      delta ((localRows m hm A B).ground.image f) := by

    rw [empty_row_root _ c hc]

    exact (rename_operations f (localRows m hm A B).ground (delta ∅) (delta ∅) ∅).1

  have hDU : (((localRows m hm A B).ground \ rim m hm).image f) ⊆

      (localRows m hm A B).ground.image f := Finset.image_subset_image Finset.sdiff_subset

  apply SetLike.ext

  intro s

  constructor

  · intro hs

    change s ∈ (rawJoin (delta X) (renameFamily f (localRows m hm A B).root) ⊔

      rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

      (if Disjoint A (rim m hm) then rawJoin D

        (delta (((localRows m hm A B).ground \ rim m hm).image f)) else ⊥) at hs

    rw [hE] at hs

    rcases hs with (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩) | hs

    · exact Finset.union_subset_union hu hv

    · exact Finset.union_subset_union (hD u (hLD hu)) hv

    · by_cases h : Disjoint A (rim m hm)

      · rw [if_pos h] at hs

        obtain ⟨u, hu, v, hv, rfl⟩ := hs

        exact Finset.union_subset_union (hD u hu) (hv.trans hDU)

      · rw [if_neg h] at hs

        exact hs.elim

  · intro hs

    apply Or.inl

    apply Or.inl

    rw [hE]

    refine ⟨s ∩ X, Finset.inter_subset_right,

      s ∩ (localRows m hm A B).ground.image f, Finset.inter_subset_right, ?_⟩

    ext x

    constructor

    · intro hx

      rcases Finset.mem_union.mp (hs hx) with hxX | hxU

      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxX⟩)

      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxU⟩)

    · simp only [Finset.mem_union, Finset.mem_inter]; tauto

Definitions and proofs are in the paired Lean module.

/-- Total parent normal form, including the empty-row simplex branch. -/

def parentNormalForm {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (r : RowCase m hm A B) (c : MarkerCase m hm A B) : Family V :=

  match r with

  | .simplex _ _ => delta (X ∪ (localRows m hm A B).ground.image f)

  | .void _ => markerNormalForm m hm A B f X D L c

  | .forest _ _ => markerNormalForm m hm A B f X D L c

Definitions and proofs are in the paired Lean module.

private theorem total_parent_readback {V : Type*} [Fintype V] [DecidableEq V]

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D) :

    decorated m hm A B f X D L = parentNormalForm m hm A B f X D L

      (classifyRows m hm A B) (classifyMarkers m hm A B hA hB) := by

  generalize he : classifyRows m hm A B = r

  cases r with

  | simplex c hc => exact decorated_simplex m hm A B f X D L hD hLD c hc

  | void h =>

      exact decorated_readback m hm A B hA hB

        (fun c => (h.false c).elim) f X D L hD hLD

  | forest hi h0 => exact decorated_readback m hm A B hA hB h0 f X D L hD hLD

Definitions and proofs are in the paired Lean module.

/-- Exact structural result on actual masks. All geometry fields are conclusions

of parentStructure. The record contains no native certificate or deformation. -/

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

def parentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D) : ParentStructure m hm A B f X D L where

  rowState := classifyRows m hm A B

  markerState := classifyMarkers m hm A B hA hB

  localRoot := row_root_readback m hm A B

  parentRoot := total_parent_readback m hm A B hA hB f X D L hD hLD

  literalPath := local_path_root m hm A B hA

  cover := components_cover m hm A B

  originalGround := original_labels m hm A B

  originalMarkers := marker_positions m hm A B

  graphRows := graph_actual_rows m hm A B

  partition := component_partition m hm A B

  consecutive := component_consecutive m hm A B

  componentPaths := component_edges m hm A B

  forcedSingletons := forced_component m hm A B

  isolatedGhosts := isolated_component m hm A B

  separatedEnds := separated_components m hm A B

end TotalParent

Definitions and proofs are in the paired Lean module.

section PhysicalParent

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- The physical source corner, at arbitrary ambient original masks. -/

def physicalDecorated (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A B X : Finset V) (D L : Family V) : Family V :=

  let U := HistoryCorners.residual ((ground m).image f) A B

  (rawJoin (delta X) (corner ((ground m).image f) A B

    (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root)) ⊔

    rawJoin L (delta U)) ⊔

    if Disjoint A ((rim m hm).image f) then rawJoin D (delta (U \ (rim m hm).image f)) else ⊥

Definitions and proofs are in the paired Lean module.

/-- Final total physical consumer: masks are pulled back from the REAL ambient

wheel ground, the literal physical corner is identified, and its exact parent

factor receives the computed structural normal form. This proves no strong Output. -/

theorem physical_parent_readback (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A' B' X : Finset V) (D L : Family V)

    (hA' : A' ⊆ (ground m).image f) (hB' : B' ⊆ (ground m).image f)

    (hAB' : Disjoint A' B') (hD : Supported X D) (hLD : L ≤ D) :

    ∃ (A B : Finset (Label m)) (hA : A ⊆ ground m) (hB : B ⊆ ground m),

      Disjoint A B ∧ A.image f = A' ∧ B.image f = B' ∧

      ∃ s : ParentStructure m hm A B f X D L,

        physicalDecorated m hm f A' B' X D L =

          parentNormalForm m hm A B f X D L s.rowState s.markerState := by

  obtain ⟨A, B, hA, hB, hAB, hAi, hBi, hcorner⟩ :=

    physical_original_masks m hm f A' B' hA' hB' hAB'

  let s := parentStructure m hm A B hA hB f X D L hD hLD

  refine ⟨A, B, hA, hB, hAB, hAi, hBi, s, ?_⟩

  have hground : HistoryCorners.residual ((ground m).image f) A' B' =

      (localRows m hm A B).ground.image f := by

    rw [← hAi, ← hBi]

    change HistoryCorners.residual ((ground m).image f) (A.image f) (B.image f) = (HistoryCorners.residual (ground m) A B).image f

    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]

  have hswitch : Disjoint A' ((rim m hm).image f) ↔ Disjoint A (rim m hm) := by

    rw [← hAi]

    exact Finset.disjoint_image f.injective

  have hphysical : physicalDecorated m hm f A' B' X D L = decorated m hm A B f X D L := by

    simp only [physicalDecorated, decorated, hcorner, hground, hswitch,

      Finset.image_sdiff _ _ f.injective]

  exact hphysical.trans s.parentRoot

end PhysicalParent

Definitions and proofs are in the paired Lean module.

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests

Definitions and proofs are in the paired Lean module.

**Definition 1.1 (forced).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def forced (r : Rows V) : Finset V := by classical exact r.ground.filter (fun x => ∃ c : r.chords, r.row c = {x})

**Theorem 1.2 (mem_forced).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.mem_forced`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.mem_forced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

@[simp] theorem mem_forced (r : Rows V) (x : V) :

    x ∈ forced r ↔ ∃ c : r.chords, r.row c = {x} := by

  constructor

  · exact fun h => (Finset.mem_filter.mp h).2

  · rintro ⟨c, hc⟩

    exact Finset.mem_filter.mpr ⟨r.row_supported c (by simp [hc]), c, hc⟩

Definitions and proofs are in the paired Lean module.

/-- Only size-two superset ROWS touching a singleton are removed.

The index subtype retains every other original multiplicity and every label. -/

**Definition 1.3 (prune).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def prune (r : Rows V) : Rows V where

  ground := r.ground

  chords := {c : r.chords // (r.row c).card ≠ 2 ∨ Disjoint (r.row c) (forced r)}

  row c := r.row c.1

  row_supported c := r.row_supported c.1

Definitions and proofs are in the paired Lean module.

/-- This equality is raw: the empty face is not projected away. -/

**Theorem 1.4 (prune_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem prune_root (r : Rows V) : (prune r).root = r.root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c, hc⟩

    exact ⟨c.1, hc⟩

  · rintro ⟨c, hc⟩

    by_cases hk : (r.row c).card ≠ 2 ∨ Disjoint (r.row c) (forced r)

    · exact ⟨⟨c, hk⟩, hc⟩

    · have hd : ¬ Disjoint (r.row c) (forced r) := fun h => hk (Or.inr h)

      obtain ⟨x, hxq, hxF⟩ := Finset.not_disjoint_iff.mp hd

      obtain ⟨d, hd⟩ := (mem_forced r x).mp hxF

      refine ⟨⟨d, Or.inl (by simp [hd])⟩, ?_⟩

      intro y hy

      obtain ⟨hyW, hyq⟩ := Finset.mem_sdiff.mp (hc hy)

      refine Finset.mem_sdiff.mpr ⟨hyW, ?_⟩

      intro hyd

      have hyx : y = x := by

        change y ∈ r.row d at hyd

        simpa only [hd, Finset.mem_singleton] using hyd

      exact hyq (hyx.symm ▸ hxq)

Definitions and proofs are in the paired Lean module.

/-- An existing empty ROW yields a simplex, even on zero ground (UNIT). -/

**Theorem 1.5 (empty_row_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.empty_row_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.empty_row_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem empty_row_root (r : Rows V) (c : r.chords) (hc : r.row c = ∅) :

    r.root = delta r.ground := by

  apply SetLike.ext

  intro s

  exact ⟨r.root_supported s, fun hs => ⟨c, by simpa [hc] using hs⟩⟩

Definitions and proofs are in the paired Lean module.

/-- No surviving index yields VOID, including on zero ground. -/

**Theorem 1.6 (no_rows_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.no_rows_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.no_rows_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem no_rows_root (r : Rows V) (h : IsEmpty r.chords) : r.root = ⊥ := by

  apply SetLike.ext

  intro s

  exact ⟨fun ⟨c, _⟩ => (h.false c).elim, fun h => h.elim⟩

end IndexedRows

Definitions and proofs are in the paired Lean module.

/-- The ACTUAL non-interface rim rows; this is not pathRows with indices forgotten. -/

**Definition 1.7 (localRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.localRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.localRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def localRows (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m)) : Rows (Label m) :=

  cornerRows ((rimRows m (by omega)).without (interfaceRow m hm)) A B

Definitions and proofs are in the paired Lean module.

/-- The path coordinate is 2,3,...,m,1. Coordinate zero is not the hub. -/

**Definition 1.8 (at).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.at`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.at` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def «at» (m : Nat) (hm : 3 ≤ m) (i : Fin m) : Label m :=

  if h : i.val + 1 = m then firstLabel m hm else ⟨i.val + 2, by omega⟩

**Definition 1.9 (position).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.position`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def position (m : Nat) (x : Label m) : Nat :=

  if x.val = 1 then m - 1 else x.val - 2

**Definition 1.10 (cutRow).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.cutRow`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.cutRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def cutRow (m : Nat) (hm : 3 ≤ m) (k : Fin (m - 1)) : Finset (Label m) :=

  {«at» m hm ⟨k.val, by omega⟩, «at» m hm ⟨k.val + 1, by omega⟩}

**Theorem 1.11 (projected_row_cases).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.projected_row_cases`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.projected_row_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem projected_row_cases (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

    (c : (localRows m hm A B).chords) :

    ∃ k : Fin (m - 1),

      Disjoint (cutRow m hm k) A ∧

      (localRows m hm A B).row c = cutRow m hm k \ B ∧

      ((localRows m hm A B).row c = ∅ ∨

       (∃ x ∈ cutRow m hm k, (localRows m hm A B).row c = {x}) ∨

       (localRows m hm A B).row c = cutRow m hm k) := by

  let k : Fin (m - 1) := ⟨c.1.1.val - 1, by

    have h0 : c.1.1.val ≠ 0 := fun h => c.1.2 (Fin.ext h)

    have := c.1.1.isLt

    omega⟩

  have he := original_row m hm c.1

  have hr : (localRows m hm A B).row c = cutRow m hm k \ B := by

    change rimEdge m (by omega) c.1.1 \ B = _

    rw [he]

  refine ⟨k, by simpa only [Rows.without, rimRows, he] using c.2, hr, ?_⟩

  rw [hr]

  let a := «at» m hm (⟨k.val, by omega⟩ : Fin m)

  let b := «at» m hm (⟨k.val + 1, by omega⟩ : Fin m)

  by_cases ha : a ∈ B <;> by_cases hb : b ∈ B

  · left; ext x; simp [cutRow, a, b, Finset.mem_sdiff, ha, hb]; aesop

  · right; left; refine ⟨b, by simp [cutRow, b], ?_⟩

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = b

    constructor

    · rintro ⟨rfl | rfl, hn⟩; exact (hn ha).elim; rfl

    · rintro rfl; exact ⟨Or.inr rfl, hb⟩

  · right; left; refine ⟨a, by simp [cutRow, a], ?_⟩

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = a

    constructor

    · rintro ⟨rfl | rfl, hn⟩; rfl; exact (hn hb).elim

    · rintro rfl; exact ⟨Or.inl rfl, ha⟩

  · right; right

    ext x; simp only [cutRow, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]

    change ((x = a ∨ x = b) ∧ x ∉ B) ↔ x = a ∨ x = b

    aesop

Definitions and proofs are in the paired Lean module.

section Forest

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- These are the actual surviving two-element rows after singleton absorption. -/

**Definition 1.12 (alive).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.alive`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.alive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def alive (k : Fin (m - 1)) : Prop :=

  ∃ c : (localRows m hm A B).chords,

    (localRows m hm A B).row c = cutRow m hm k ∧

      Disjoint (cutRow m hm k) (forced (localRows m hm A B))

Definitions and proofs are in the paired Lean module.

/-- Graph built FROM the actual rows. There is no forest/certificate argument. -/

**Definition 1.13 (reducedGraph).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reducedGraph`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reducedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def reducedGraph : SimpleGraph (Fin m) where

  Adj a b := ∃ k : Fin (m - 1), alive m hm A B k ∧

    ((a.val = k.val ∧ b.val = k.val + 1) ∨

     (b.val = k.val ∧ a.val = k.val + 1))

  symm := ⟨by rintro a b ⟨k, hk, h⟩; exact ⟨k, hk, h.symm⟩⟩

  loopless := ⟨by rintro a ⟨k, hk, h | h⟩ <;> omega⟩

Definitions and proofs are in the paired Lean module.

/-- Exact interval of intact cuts; used only AFTER its equivalence to walks. -/

**Definition 1.14 (interval).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.interval`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.interval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def interval (a b : Fin m) : Prop := ∀ k : Fin (m - 1),

  min a.val b.val ≤ k.val → k.val < max a.val b.val → alive m hm A B k

**Theorem 1.15 (connected_iff_interval).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.connected_iff_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.connected_iff_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem connected_iff_interval (a b : Fin m) :

    Nonempty ((reducedGraph m hm A B).Walk a b) ↔ interval m hm A B a b := by

  constructor

  · exact fun ⟨p⟩ => walk_interval m hm A B p

  · intro h

    by_cases hab : a.val ≤ b.val

    · exact ⟨ascend m hm A B a b hab h⟩

    · exact ⟨(ascend m hm A B b a (by omega)

        (interval_symm m hm A B h)).reverse⟩

**Definition 1.16 (live).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.live`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.live` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def live : Finset (Fin m) := Finset.univ.filter

  (fun a => «at» m hm a ∈ (localRows m hm A B).ground)

Definitions and proofs are in the paired Lean module.

/-- Actual graph components, represented on the original finite coordinate order. -/

**Definition 1.17 (component).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def component (a : Fin m) : Finset (Fin m) :=

  (live m hm A B).filter (fun b => Nonempty ((reducedGraph m hm A B).Walk a b))

**Definition 1.18 (components).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.components`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.components` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def components : Finset (Finset (Fin m)) :=

  (live m hm A B).image (component m hm A B)

**Definition 1.19 (block).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def block (a : Fin m) : Finset (Label m) :=

  (component m hm A B a).image («at» m hm)

**Theorem 1.20 (component_partition).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem component_partition (a b : Fin m) (ha : a ∈ live m hm A B)

    (hb : b ∈ live m hm A B) :

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b) := by

  by_cases h : interval m hm A B a b

  · left

    ext c

    rw [mem_component, mem_component]

    constructor

    · rintro ⟨hc, hac⟩

      exact ⟨hc, interval_trans m hm A B (interval_symm m hm A B h) hac⟩

    · rintro ⟨hc, hbc⟩

      exact ⟨hc, interval_trans m hm A B h hbc⟩

  · right

    apply Finset.disjoint_left.mpr

    intro c hc hd

    have hac := ((mem_component m hm A B a c).mp hc).2

    have hbc := ((mem_component m hm A B b c).mp hd).2

    exact h (interval_trans m hm A B hac (interval_symm m hm A B hbc))

Definitions and proofs are in the paired Lean module.

/-- Every position between two vertices of a component actually survives.

Thus these are consecutive original intervals, not paths through new shortcuts. -/

**Theorem 1.21 (component_consecutive).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_consecutive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_consecutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem component_consecutive (a x y z : Fin m)

    (hx : x ∈ component m hm A B a) (hy : y ∈ component m hm A B a)

    (hxz : x.val ≤ z.val) (hzy : z.val ≤ y.val) :

    z ∈ component m hm A B a := by

  obtain ⟨hxL, hax⟩ := (mem_component m hm A B a x).mp hx

  obtain ⟨hyL, hay⟩ := (mem_component m hm A B a y).mp hy

  have hxy := interval_trans m hm A B (interval_symm m hm A B hax) hay

  by_cases he : z = y

  · simpa [he] using hy

  · have hzy' : z.val < y.val := by

      have hn : z.val ≠ y.val := fun h => he (Fin.ext h)

      omega

    let k : Fin (m - 1) := ⟨z.val, by omega⟩

    have hk : alive m hm A B k := hxy k (by dsimp [k]; omega) (by dsimp [k]; omega)

    have hzL : z ∈ live m hm A B := by

      apply Finset.mem_filter.mpr

      refine ⟨Finset.mem_univ _, ?_⟩

      exact alive_supported m hm A B k hk (by simp [cutRow, k])

    apply (mem_component m hm A B a z).mpr

    refine ⟨hzL, interval_trans m hm A B hax ?_⟩

    intro j hl hu

    apply hxy j <;> omega

Definitions and proofs are in the paired Lean module.

/-- Component membership is exactly the original surviving graph relation. -/

**Theorem 1.22 (block_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem block_mem (a b : Fin m) : «at» m hm b ∈ block m hm A B a ↔

    b ∈ live m hm A B ∧ Nonempty ((reducedGraph m hm A B).Walk a b) := by

  rw [block, Finset.mem_image]

  constructor

  · rintro ⟨c, hc, he⟩

    have he' := at_injective m hm he

    subst c

    exact Finset.mem_filter.mp hc

  · intro h

    exact ⟨b, Finset.mem_filter.mpr h, rfl⟩

Definitions and proofs are in the paired Lean module.

end Forest

Definitions and proofs are in the paired Lean module.

section RowComponents

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

**Theorem 1.23 (reduced_row_cases).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reduced_row_cases`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reduced_row_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem reduced_row_cases (c : (prune (localRows m hm A B)).chords) :

    (prune (localRows m hm A B)).row c = ∅ ∨

    (∃ a ∈ live m hm A B,

      (prune (localRows m hm A B)).row c = {«at» m hm a} ∧

        «at» m hm a ∈ forced (localRows m hm A B)) ∨

    (∃ k : Fin (m - 1), alive m hm A B k ∧

      (prune (localRows m hm A B)).row c = cutRow m hm k) := by

  obtain ⟨k, hkA, hr, h0 | h1 | h2⟩ := projected_row_cases m hm A B c.1

  · exact Or.inl h0

  · obtain ⟨x, hx, he⟩ := h1

    have hxU : x ∈ (localRows m hm A B).ground :=

      (localRows m hm A B).row_supported c.1 (by simp [he])

    have hxG : x ∈ ground m := (Finset.mem_sdiff.mp hxU).1

    let a : Fin m := ⟨position m x, position_lt m hm x hxG⟩

    have hat : «at» m hm a = x := at_position m hm x hxG

    exact Or.inr (Or.inl ⟨a, by simp [live, hat, hxU], by simpa [prune, hat] using he,

      by rw [hat, mem_forced]; exact ⟨c.1, he⟩⟩)

  · have hd : Disjoint (cutRow m hm k) (forced (localRows m hm A B)) := by

      rcases c.2 with hn | hd

      · exact (hn (by rw [h2]; exact cutRow_card m hm k)).elim

      · simpa only [h2] using hd

    exact Or.inr (Or.inr ⟨k, ⟨c.1, h2, hd⟩, h2⟩)

**Theorem 1.24 (forced_component).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced_component`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem forced_component (a : Fin m) (ha : a ∈ live m hm A B)

    (hf : «at» m hm a ∈ forced (localRows m hm A B)) :

    component m hm A B a = {a} := by

  ext b

  constructor

  · intro hb

    obtain ⟨p⟩ := (Finset.mem_filter.mp hb).2

    have he : a = b := by

      cases p with

      | nil => rfl

      | cons hab p => exact ((adj_unforced m hm A B hab).1 hf).elim

    exact Finset.mem_singleton.mpr he.symm

  · intro hb

    have he := Finset.mem_singleton.mp hb

    subst b

    exact self_component m hm A B a ha

Definitions and proofs are in the paired Lean module.

/-- Every reduced nonempty row belongs to a derived consecutive component. -/

**Definition 1.25 (componentRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def componentRows (a : Fin m) : Rows (Label m) where

  ground := block m hm A B a

  chords := {c : (prune (localRows m hm A B)).chords //

    (prune (localRows m hm A B)).row c ⊆ block m hm A B a}

  row c := (prune (localRows m hm A B)).row c.1

  row_supported c := c.2

Definitions and proofs are in the paired Lean module.

/-- Union of component noncovers padded by ALL other HistoryCorners.residual coordinates.

The existential over starts merely repeats equal components, without altering rows. -/

**Definition 1.26 (componentUnion).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentUnion`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def componentUnion : Family (Label m) where

  carrier := {s | ∃ a ∈ live m hm A B,

    s ∈ rawJoin (componentRows m hm A B a).root

      (delta ((localRows m hm A B).ground \ block m hm A B a))}

  lower' := by

    rintro s t h ⟨a, ha, hs⟩

    exact ⟨a, ha, (rawJoin (componentRows m hm A B a).root

      (delta ((localRows m hm A B).ground \ block m hm A B a))).lower h hs⟩

Definitions and proofs are in the paired Lean module.

/-- Exact finite linear-forest decomposition, consumed by the parent readback.

No component, forest or equality is an input; only the separate empty-row branch

is excluded, because that branch is already a simplex. -/

**Theorem 1.27 (component_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem component_root (h0 : ∀ c : (localRows m hm A B).chords,

    (localRows m hm A B).row c ≠ ∅) :

    (localRows m hm A B).root = componentUnion m hm A B := by

  rw [← prune_root]

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c, hc⟩

    obtain ⟨a, ha, hrow⟩ := row_block m hm A B c (h0 c.1)

    refine ⟨a, ha, s ∩ block m hm A B a, ⟨⟨c, hrow⟩, ?_⟩,

      s \ block m hm A B a, ?_, ?_⟩

    · intro x hx

      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2,

        (Finset.mem_sdiff.mp (hc (Finset.mem_inter.mp hx).1)).2⟩

    · intro x hx

      obtain ⟨hxs, hxC⟩ := Finset.mem_sdiff.mp hx

      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hc hxs)).1, hxC⟩

    · ext x

      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]

      tauto

  · rintro ⟨a, ha, u, ⟨c, hc⟩, v, hv, rfl⟩

    refine ⟨c.1, ?_⟩

    intro x hx

    rcases Finset.mem_union.mp hx with hxu | hxv

    · obtain ⟨hxC, hxq⟩ := Finset.mem_sdiff.mp (hc hxu)

      exact Finset.mem_sdiff.mpr ⟨block_supported m hm A B a hxC, hxq⟩

    · obtain ⟨hxU, hxC⟩ := Finset.mem_sdiff.mp (hv hxv)

      exact Finset.mem_sdiff.mpr ⟨hxU, fun hxq => hxC (c.2 hxq)⟩

Definitions and proofs are in the paired Lean module.

/-- An isolated unforced HistoryCorners.residual coordinate is retained as its own component,

including when the surviving indexed row type is empty. -/

**Theorem 1.28 (isolated_component).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.isolated_component`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.isolated_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem isolated_component (a : Fin m) (ha : a ∈ live m hm A B)

    (h : ∀ b, ¬ (reducedGraph m hm A B).Adj a b) :

    component m hm A B a = {a} := by

  ext b

  constructor

  · intro hb

    obtain ⟨p⟩ := (Finset.mem_filter.mp hb).2

    have he : a = b := by

      cases p with

      | nil => rfl

      | cons hab p => exact (h _ hab).elim

    exact Finset.mem_singleton.mpr he.symm

  · intro hb

    have he := Finset.mem_singleton.mp hb

    subst b

    exact self_component m hm A B a ha

end RowComponents

Definitions and proofs are in the paired Lean module.

section Untouched

variable (m : Nat) (hm : 3 ≤ m)

**Definition 1.29 (leftEnd).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.leftEnd`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.leftEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def leftEnd : Fin m := ⟨0, by omega⟩

**Definition 1.30 (rightEnd).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.rightEnd`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.rightEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def rightEnd : Fin m := ⟨m - 1, by omega⟩

**Theorem 1.31 (endpoints_connected_untouched).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.endpoints_connected_untouched`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.endpoints_connected_untouched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem endpoints_connected_untouched (A B : Finset (Label m))

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (h : Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))) :

    A = ∅ ∧ B = ∅ ∧ forced (localRows m hm A B) = ∅ ∧

      component m hm A B (leftEnd m hm) = Finset.univ ∧

      components m hm A B = {Finset.univ} ∧

      block m hm A B (leftEnd m hm) = ground m ∧

      (localRows m hm A B).root = pathRoot m hm := by

  have hcuts : ∀ k : Fin (m - 1), alive m hm A B k := by

    intro k

    apply (connected_iff_interval m hm A B _ _).mp h k <;>

      dsimp [leftEnd, rightEnd] <;> omega

  have hall : ∀ a : Fin m, «at» m hm a ∈ (localRows m hm A B).ground := by

    intro a

    by_cases ha : a.val < m - 1

    · let k : Fin (m - 1) := ⟨a.val, ha⟩

      exact alive_supported m hm A B k (hcuts k) (by simp [cutRow, k])

    · let k : Fin (m - 1) := ⟨m - 2, by omega⟩

      have he : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext (by have := a.isLt; dsimp [k]; omega)

      exact alive_supported m hm A B k (hcuts k) (by simp [cutRow, he])

  have hremain : ∀ x ∈ ground m, x ∈ (localRows m hm A B).ground := by

    intro x hx

    have hh := hall ⟨position m x, position_lt m hm x hx⟩

    rw [at_position m hm x hx] at hh

    exact hh

  have hAe : A = ∅ := by

    apply Finset.eq_empty_iff_forall_notMem.mpr

    intro x hx

    exact (Finset.mem_sdiff.mp (hremain x (hA hx))).2 (Finset.mem_union_left _ hx)

  have hBe : B = ∅ := by

    apply Finset.eq_empty_iff_forall_notMem.mpr

    intro x hx

    exact (Finset.mem_sdiff.mp (hremain x (hB hx))).2 (Finset.mem_union_right _ hx)

  have hcomp : ∀ a : Fin m, component m hm A B a = Finset.univ := by

    intro a

    ext b

    simp only [mem_component, live, Finset.mem_filter, Finset.mem_univ, true_and]

    exact ⟨fun _ => trivial, fun _ => ⟨hall b, fun k _ _ => hcuts k⟩⟩

  refine ⟨hAe, hBe, by simpa only [hAe, hBe] using unmasked_forced m hm,

    hcomp _, ?_, ?_, by simpa only [hAe, hBe] using unmasked_root m hm⟩

  · ext C

    simp only [components, Finset.mem_image, Finset.mem_singleton]

    constructor

    · rintro ⟨a, ha, rfl⟩; exact hcomp a

    · rintro rfl

      exact ⟨leftEnd m hm, by simp [live, hall], hcomp _⟩

  · rw [block, hcomp]

    ext x

    simp only [Finset.mem_image, Finset.mem_univ, true_and]

    exact ⟨fun ⟨a, ha⟩ => ha ▸ at_ground m hm a,

      fun hx => ⟨⟨position m x, position_lt m hm x hx⟩, at_position m hm x hx⟩⟩

end Untouched

Definitions and proofs are in the paired Lean module.

section Markers

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Surviving ORIGINAL interface markers, not endpoints invented after projection. -/

**Definition 1.32 (markers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markers`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def markers : Finset (Label m) := rim m hm ∩ (localRows m hm A B).ground

**Definition 1.33 (MarkerCase).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.MarkerCase`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.MarkerCase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.34 (classifyMarkers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyMarkers`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyMarkers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def classifyMarkers (hA : A ⊆ ground m) (hB : B ⊆ ground m) :

    MarkerCase m hm A B := by

  classical

  by_cases h : Disjoint A (rim m hm)

  · by_cases hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B)

    · by_cases hf : firstLabel m hm ∈ (localRows m hm A B).ground

      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground

        · have hR : markers m hm A B = rim m hm := by

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · exact fun hh => hh.1

            · rintro (rfl | rfl) <;> simp_all

          by_cases hc : Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))

          · obtain ⟨hAe, hBe, hFe, full, sole, labels, root⟩ :=

              endpoints_connected_untouched m hm A B hA hB hc

            exact .intact hAe hBe hFe full sole labels root

          · exact .separated h hF hR hc

        · have hR : markers m hm A B = {«at» m hm (rightEnd m hm)} := by

            rw [at_rightEnd]

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · rintro ⟨rfl | rfl, hx⟩; rfl; exact (hs hx).elim

            · rintro rfl; exact ⟨Or.inl rfl, hf⟩

          exact .oneMarker h (rightEnd m hm) (by simp [live, at_rightEnd, hf])

            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR

      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground

        · have hR : markers m hm A B = {«at» m hm (leftEnd m hm)} := by

            rw [at_leftEnd]

            ext x

            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]

            constructor

            · rintro ⟨rfl | rfl, hx⟩; exact (hf hx).elim; rfl

            · rintro rfl; exact ⟨Or.inr rfl, hs⟩

          exact .oneMarker h (leftEnd m hm) (by simp [live, at_leftEnd, hs])

            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR

        · apply MarkerCase.noMarker h hF

          ext x

          simp only [markers, rim, Finset.mem_inter, Finset.mem_insert,

            Finset.mem_singleton, Finset.notMem_empty, iff_false]

          rintro ⟨rfl | rfl, hx⟩

          · exact hf hx

          · exact hs hx

    · have hFR : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty := by

        obtain ⟨x, hxF, hxR⟩ := Finset.not_disjoint_iff.mp hF

        exact ⟨x, Finset.mem_inter.mpr ⟨hxF, hxR⟩⟩

      exact .absorbed h hFR

  · exact .absent h

Definitions and proofs are in the paired Lean module.

/-- The two surviving separated markers really occupy disjoint components. -/

**Theorem 1.35 (separated_components).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated_components`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem separated_components

    (hL : leftEnd m hm ∈ live m hm A B) (hR : rightEnd m hm ∈ live m hm A B)

    (h : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))) :

    Disjoint (component m hm A B (leftEnd m hm))

      (component m hm A B (rightEnd m hm)) := by

  rcases component_partition m hm A B _ _ hL hR with he | hd

  · have hx := self_component m hm A B (rightEnd m hm) hR

    rw [← he] at hx

    exact (h ((Finset.mem_filter.mp hx).2)).elim

  · exact hd

Definitions and proofs are in the paired Lean module.

/-- Literal last-wheel parent factor on an arbitrary physical ambient type.

The old X,D,L coordinates need not fit inside the wheel's finite label type. -/

**Definition 1.36 (decorated).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def decorated {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)

    (X : Finset V) (D L : Family V) : Family V :=

  (rawJoin (delta X) (renameFamily f (localRows m hm A B).root) ⊔

    rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

    if Disjoint A (rim m hm) then

      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) else ⊥

Definitions and proofs are in the paired Lean module.

/-- A singleton at an actual surviving interface marker absorbs the D fibre.

No old label or HistoryCorners.residual local ghost is removed by this family equality. -/

**Theorem 1.37 (forced_marker_absorbs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forced_marker_absorbs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forced_marker_absorbs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem forced_marker_absorbs {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D : Family V) (hD : Supported X D)

    (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty) :

    rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) ≤

      rawJoin (delta X) (renameFamily f (localRows m hm A B).root) := by

  obtain ⟨z, hz⟩ := hF

  obtain ⟨hzF, hzR⟩ := Finset.mem_inter.mp hz

  obtain ⟨c, hc⟩ := (mem_forced _ z).mp hzF

  have hzrim : z ∈ rim m hm := (Finset.mem_inter.mp hzR).1

  rintro s ⟨u, hu, v, hv, rfl⟩

  obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hv

  refine ⟨u, hD u hu, t.image f, ⟨t, ⟨c, ?_⟩, rfl⟩, rfl⟩

  intro x hx

  obtain ⟨hxU, hxr⟩ := Finset.mem_sdiff.mp (ht hx)

  refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩

  intro hxq

  have he : x = z := by simpa [hc] using hxq

  exact hxr (he.symm ▸ hzrim)

Definitions and proofs are in the paired Lean module.

/-- The computed case is consumed in the actual ambient factor normal form. -/

**Definition 1.38 (markerNormalForm).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerNormalForm`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerNormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def markerNormalForm {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)

    (X : Finset V) (D L : Family V) : MarkerCase m hm A B → Family V

  | .absent _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin L (delta ((localRows m hm A B).ground.image f))

  | .absorbed _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin L (delta ((localRows m hm A B).ground.image f))

  | .noMarker _ _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

      rawJoin D (delta ((localRows m hm A B).ground.image f))

  | .oneMarker _ a _ _ _ =>

      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

      rawJoin D (delta (((localRows m hm A B).ground \ {«at» m hm a}).image f))

  | .separated _ _ _ _ =>

      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔

        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔

      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f))

  | .intact _ _ _ _ _ _ _ =>

      (rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔ rawJoin L (delta ((ground m).image f))) ⊔

      rawJoin D (delta ((tailGround m hm).image f))

Definitions and proofs are in the paired Lean module.

/-- Exhaustive actual-mask consumer. Earlier face factors have only their genuine

support and L≤D; no classification, forest, equality, Output or collapse is assumed. -/

**Theorem 1.39 (decorated_readback).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated_readback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated_readback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem decorated_readback {V : Type*} [Fintype V] [DecidableEq V]

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D) :

    decorated m hm A B f X D L =

      markerNormalForm m hm A B f X D L (classifyMarkers m hm A B hA hB) := by

  have hE := congrArg (renameFamily f) (component_root m hm A B h0)

  generalize he : classifyMarkers m hm A B hA hB = c

  cases c with

  | absent h => simp only [decorated, markerNormalForm, if_neg h, sup_bot_eq, hE]

  | absorbed h hf =>

      have hle := forced_marker_absorbs m hm A B f X D hD hf

      rw [decorated, if_pos h, sup_eq_left.mpr (hle.trans le_sup_left)]

      simp only [markerNormalForm, hE]

  | noMarker h hf hr =>

      have hg : (localRows m hm A B).ground \ rim m hm = (localRows m hm A B).ground := by

        rw [← residual_without_markers m hm A B, hr, Finset.sdiff_empty]

      have hle : rawJoin L (delta ((localRows m hm A B).ground.image f)) ≤

          rawJoin D (delta ((localRows m hm A B).ground.image f)) := by

        rintro s ⟨u, hu, v, hv, rfl⟩

        exact ⟨u, hLD hu, v, hv, rfl⟩

      simp only [decorated, markerNormalForm, if_pos h, hg, hE]

      rw [sup_assoc, sup_eq_right.mpr hle]

  | oneMarker h a ha hf hr =>

      have hg : (localRows m hm A B).ground \ rim m hm =

          (localRows m hm A B).ground \ {«at» m hm a} := by

        rw [← residual_without_markers m hm A B, hr]

      simp only [decorated, markerNormalForm, if_pos h, hg, hE]

  | separated h hf hr apart =>

      simp only [decorated, markerNormalForm, if_pos h, hE]

  | intact ha hb hf full sole labels root =>

      have hg : (localRows m hm A B).ground = ground m := by

        simp [localRows, cornerRows, HistoryCorners.residual, ha, hb, Rows.without, rimRows]

      have hAR : Disjoint A (rim m hm) := by simp [ha]

      simp only [decorated, markerNormalForm, if_pos hAR, root, hg, tailGround]

end Markers

Definitions and proofs are in the paired Lean module.

section PhysicalTransport

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- Injective transport of the literal FILTER-then-PROJECT indexed corner.

Reuse renameRows/renameRows_root; no second relabel engine is defined. -/

**Theorem 1.40 (corner_rows_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.corner_rows_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.corner_rows_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem corner_rows_transport (f : U ↪ V) (r : Rows U) (A B : Finset U) :

    (cornerRows (renameRows f r) (A.image f) (B.image f)).root =

      renameFamily f (cornerRows r A B).root := by

  have hg : HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) =

      (HistoryCorners.residual r.ground A B).image f := by

    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]

  apply SetLike.ext

  intro s

  change (∃ c : {c : r.chords // Disjoint ((r.row c).image f) (A.image f)},

    s ⊆ HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) \

      ((r.row c.1).image f \ B.image f)) ↔

    ∃ t, (∃ c : {c : r.chords // Disjoint (r.row c) A},

      t ⊆ HistoryCorners.residual r.ground A B \ (r.row c.1 \ B)) ∧ t.image f = s

  simp only [Finset.disjoint_image f.injective, hg,

    ← Finset.image_sdiff _ _ f.injective]

  constructor

  · rintro ⟨c, hc⟩

    obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hc

    exact ⟨t, ⟨⟨c.1, (Finset.disjoint_image f.injective).mp c.2⟩, ht⟩, rfl⟩

  · rintro ⟨t, ⟨c, hc⟩, rfl⟩

    exact ⟨⟨c.1, (Finset.disjoint_image f.injective).mpr c.2⟩,

      Finset.image_subset_image hc⟩

Definitions and proofs are in the paired Lean module.

/-- This is the actual physical wheel consumer: the source is its real path-row

root with precisely the interface rim row removed, not a supplied row model. -/

**Theorem 1.41 (physical_corner_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_corner_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_corner_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem physical_corner_transport (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A B : Finset (Label m)) (hA : A ⊆ ground m) :

    corner ((ground m).image f) (A.image f) (B.image f)

      (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =

      renameFamily f (localRows m hm A B).root := by

  let r := (rimRows m (by omega)).without (interfaceRow m hm)

  have hr : ((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root =

      (renameRows f r).root :=

    (PhysicalMWheel.ambient_without m hm f).trans (renameRows_root f r).symm

  rw [hr]

  change corner (renameRows f r).ground (A.image f) (B.image f) (renameRows f r).root = _

  rw [corner_root (renameRows f r) (A.image f) (B.image f)

    (Finset.image_subset_image hA), corner_rows_transport]

  rfl

Definitions and proofs are in the paired Lean module.

/-- Every disjoint ambient local mask is read back to ORIGINAL coordinates.

The full image of the ground is preserved, even at labels absent from every face. -/

**Theorem 1.42 (physical_original_masks).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_original_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_original_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem physical_original_masks (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A' B' : Finset V) (hA' : A' ⊆ (ground m).image f)

    (hB' : B' ⊆ (ground m).image f) (hAB' : Disjoint A' B') :

    ∃ A B : Finset (Label m), A ⊆ ground m ∧ B ⊆ ground m ∧ Disjoint A B ∧

      A.image f = A' ∧ B.image f = B' ∧

      corner ((ground m).image f) A' B'

        (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =

        renameFamily f (localRows m hm A B).root := by

  obtain ⟨A, hA, rfl⟩ := Finset.subset_image_iff.mp hA'

  obtain ⟨B, hB, rfl⟩ := Finset.subset_image_iff.mp hB'

  exact ⟨A, B, hA, hB, (Finset.disjoint_image f.injective).mp hAB',

    rfl, rfl, physical_corner_transport m hm f A B hA⟩

end PhysicalTransport

Definitions and proofs are in the paired Lean module.

section ExactPathReadback

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Reuse the frozen path edge theorem and pathRows_mem; equality of roots does

not replace the indexed localRows presentation used by all classification data. -/

**Theorem 1.43 (local_path_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.local_path_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.local_path_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem local_path_root (hA : A ⊆ ground m) :

    (localRows m hm A B).root = corner (ground m) A B

      (HistoryPaths.pathRows (pathRootPath m hm)).root := by

  have hp : pathRoot m hm = (HistoryPaths.pathRows (pathRootPath m hm)).root := by

    apply SetLike.ext

    intro s

    rw [HistoryPaths.pathRows_mem, pathRootPath_vertices, pathRootPath_row_edges]

    constructor

    · rintro ⟨i, hi⟩

      refine ⟨hi.trans Finset.sdiff_subset, rimEdge m (by omega) i.1,

        Finset.mem_image.mpr ⟨i.1, Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩, rfl⟩, ?_⟩

      exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_sdiff.mp (hi hxs)).2 hx)

    · rintro ⟨hs, q, hq, hdis⟩

      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq

      refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩

      intro x hx

      exact Finset.mem_sdiff.mpr ⟨hs hx, fun hq => Finset.disjoint_left.mp hdis hq hx⟩

  rw [← hp]

  exact (corner_root ((rimRows m (by omega)).without (interfaceRow m hm)) A B hA).symm

Definitions and proofs are in the paired Lean module.

/-- Each derived consecutive component has exactly its consecutive path edges.

Together with component_consecutive this is a linear forest, including isolated

HistoryCorners.residual labels and the singleton constraint components. -/

**Theorem 1.44 (component_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.component_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.component_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem component_edges (a x y : Fin m)

    (hx : x ∈ component m hm A B a) (hy : y ∈ component m hm A B a) :

    (reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val := by

  constructor

  · rintro ⟨k, hk, h | h⟩ <;> omega

  · intro h

    have hxy := interval_trans m hm A B

      (interval_symm m hm A B ((mem_component m hm A B a x).mp hx).2)

      ((mem_component m hm A B a y).mp hy).2

    rcases h with h | h

    · let k : Fin (m - 1) := ⟨x.val, by have := y.isLt; omega⟩

      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),

        Or.inl ⟨rfl, h.symm⟩⟩

    · let k : Fin (m - 1) := ⟨y.val, by have := x.isLt; omega⟩

      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),

        Or.inr ⟨rfl, h.symm⟩⟩

Definitions and proofs are in the paired Lean module.

/-- The graph edges are EXACTLY the surviving size-two indexed rows.

No graph connectivity or desired edge relation is assumed. -/

**Theorem 1.45 (graph_actual_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graph_actual_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graph_actual_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem graph_actual_rows (a b : Fin m) :

    (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

      ∃ c : (prune (localRows m hm A B)).chords,

        (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b} := by

  constructor

  · rintro ⟨k, ⟨c, hc, hd⟩, hor⟩

    have hn : a ≠ b := by intro he; subst b; rcases hor with h | h <;> omega

    refine ⟨hn, ⟨c, Or.inr (by simpa only [hc] using hd)⟩, ?_⟩

    change (localRows m hm A B).row c = _

    rw [hc]

    rcases hor with h | h

    · have ha : a = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      have hb : b = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, ha, hb]

    · have hb : b = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1

      have ha : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2

      simp [cutRow, ha, hb, Finset.pair_comm]

  · rintro ⟨hab, c, hc⟩

    have hne : «at» m hm a ≠ «at» m hm b := fun h => hab (at_injective m hm h)

    have hcard : ((prune (localRows m hm A B)).row c).card = 2 := by simp [hc, hne]

    rcases reduced_row_cases m hm A B c with h0 | h1 | h2

    · rw [h0, Finset.card_empty] at hcard; omega

    · obtain ⟨i, hi, he, hf⟩ := h1

      rw [he, Finset.card_singleton] at hcard; omega

    · obtain ⟨k, hk, he⟩ := h2

      have hea : «at» m hm a ∈ cutRow m hm k := by rw [← he, hc]; simp

      have heb : «at» m hm b ∈ cutRow m hm k := by rw [← he, hc]; simp

      have ha : a.val = k.val ∨ a.val = k.val + 1 := by

        rcases (show «at» m hm a = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨

          «at» m hm a = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by

            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using hea) with h | h

        · exact Or.inl (congrArg Fin.val (at_injective m hm h))

        · exact Or.inr (congrArg Fin.val (at_injective m hm h))

      have hb : b.val = k.val ∨ b.val = k.val + 1 := by

        rcases (show «at» m hm b = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨

          «at» m hm b = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by

            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using heb) with h | h

        · exact Or.inl (congrArg Fin.val (at_injective m hm h))

        · exact Or.inr (congrArg Fin.val (at_injective m hm h))

      have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)

      exact ⟨k, hk, by omega⟩

/-- The component partition covers every retained original position. -/

**Theorem 1.46 (components_cover).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.components_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.components_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem components_cover (a : Fin m) : a ∈ live m hm A B ↔

    ∃ C ∈ components m hm A B, a ∈ C := by

  constructor

  · intro ha

    exact ⟨component m hm A B a,

      Finset.mem_image.mpr ⟨a, ha, rfl⟩, self_component m hm A B a ha⟩

  · rintro ⟨C, hC, ha⟩

    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hC

    exact (Finset.mem_filter.mp ha).1

Definitions and proofs are in the paired Lean module.

/-- This cover is on the ORIGINAL HistoryCorners.residual ground, not on the face support. -/

**Theorem 1.47 (original_labels).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.original_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.original_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem original_labels (x : Label m) : x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a := by

  constructor

  · intro hx

    have hxG : x ∈ ground m := (Finset.mem_sdiff.mp hx).1

    let a : Fin m := ⟨position m x, position_lt m hm x hxG⟩

    have he : «at» m hm a = x := at_position m hm x hxG

    have ha : a ∈ live m hm A B := by simp [live, he, hx]

    exact ⟨a, ha, he ▸ (block_mem m hm A B a a).mpr ⟨ha, ⟨.nil⟩⟩⟩

  · rintro ⟨a, ha, hx⟩

    exact block_supported m hm A B a hx

Definitions and proofs are in the paired Lean module.

/-- Both original surviving markers occupy extreme positions in their blocks. -/

**Theorem 1.48 (marker_positions).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.marker_positions`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.marker_positions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem marker_positions : markers m hm A B ⊆

    {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)} := by

  intro x hx

  have hr := (Finset.mem_inter.mp hx).1

  simpa only [at_leftEnd, at_rightEnd, rim, Finset.mem_insert, Finset.mem_singleton,

    or_comm] using hr

end ExactPathReadback

Definitions and proofs are in the paired Lean module.

section TotalParent

variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

Definitions and proofs are in the paired Lean module.

/-- Exhaustive row terminal state. These constructors contain facts DERIVED from

actual indices, not hypotheses passed to the structural constructor. -/

**Definition 1.49 (RowCase).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.RowCase`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.RowCase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

inductive RowCase : Type

  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)

  | void (none : IsEmpty (localRows m hm A B).chords)

  | forest (some : Nonempty (localRows m hm A B).chords)

      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

**Definition 1.50 (classifyRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def classifyRows : RowCase m hm A B := by

  classical

  by_cases h : ∃ c : (localRows m hm A B).chords, (localRows m hm A B).row c = ∅

  · exact .simplex (Classical.choose h) (Classical.choose_spec h)

  · have h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅ :=

      fun c hc => h ⟨c, hc⟩

    by_cases hI : Nonempty (localRows m hm A B).chords

    · exact .forest hI h0

    · exact .void ⟨fun c => hI ⟨c⟩⟩

Definitions and proofs are in the paired Lean module.

/-- Raw local root for every computed row state, including zero-ground VOID/UNIT. -/

**Definition 1.51 (rowRootForm).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowRootForm`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowRootForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def rowRootForm : RowCase m hm A B → Family (Label m)

  | .simplex _ _ => delta (localRows m hm A B).ground

  | .void _ => ⊥

  | .forest _ _ => componentUnion m hm A B

**Definition 1.52 (parentNormalForm).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentNormalForm`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentNormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def parentNormalForm {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (r : RowCase m hm A B) (c : MarkerCase m hm A B) : Family V :=

  match r with

  | .simplex _ _ => delta (X ∪ (localRows m hm A B).ground.image f)

  | .void _ => markerNormalForm m hm A B f X D L c

  | .forest _ _ => markerNormalForm m hm A B f X D L c

**Definition 1.53 (ParentStructure).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.ParentStructure`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.ParentStructure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.54 (parentStructure).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentStructure`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentStructure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def parentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (hA : A ⊆ ground m) (hB : B ⊆ ground m)

    (f : Label m ↪ V) (X : Finset V) (D L : Family V)

    (hD : Supported X D) (hLD : L ≤ D) : ParentStructure m hm A B f X D L where

  rowState := classifyRows m hm A B

  markerState := classifyMarkers m hm A B hA hB

  localRoot := row_root_readback m hm A B

  parentRoot := total_parent_readback m hm A B hA hB f X D L hD hLD

  literalPath := local_path_root m hm A B hA

  cover := components_cover m hm A B

  originalGround := original_labels m hm A B

  originalMarkers := marker_positions m hm A B

  graphRows := graph_actual_rows m hm A B

  partition := component_partition m hm A B

  consecutive := component_consecutive m hm A B

  componentPaths := component_edges m hm A B

  forcedSingletons := forced_component m hm A B

  isolatedGhosts := isolated_component m hm A B

  separatedEnds := separated_components m hm A B

end TotalParent

Definitions and proofs are in the paired Lean module.

section PhysicalParent

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- The physical source corner, at arbitrary ambient original masks. -/

**Definition 1.55 (physicalDecorated).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physicalDecorated`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physicalDecorated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

def physicalDecorated (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A B X : Finset V) (D L : Family V) : Family V :=

  let U := HistoryCorners.residual ((ground m).image f) A B

  (rawJoin (delta X) (corner ((ground m).image f) A B

    (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root)) ⊔

    rawJoin L (delta U)) ⊔

    if Disjoint A ((rim m hm).image f) then rawJoin D (delta (U \ (rim m hm).image f)) else ⊥

Definitions and proofs are in the paired Lean module.

/-- Final total physical consumer: masks are pulled back from the REAL ambient

wheel ground, the literal physical corner is identified, and its exact parent

factor receives the computed structural normal form. This proves no strong Output. -/

**Theorem 1.56 (physical_parent_readback).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_parent_readback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_parent_readback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Exact public source declaration and body. ParentStructure is constructed from actual masks and consumed by physical_parent_readback. The classification is derived from the original masks.

theorem physical_parent_readback (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)

    (A' B' X : Finset V) (D L : Family V)

    (hA' : A' ⊆ (ground m).image f) (hB' : B' ⊆ (ground m).image f)

    (hAB' : Disjoint A' B') (hD : Supported X D) (hLD : L ≤ D) :

    ∃ (A B : Finset (Label m)) (hA : A ⊆ ground m) (hB : B ⊆ ground m),

      Disjoint A B ∧ A.image f = A' ∧ B.image f = B' ∧

      ∃ s : ParentStructure m hm A B f X D L,

        physicalDecorated m hm f A' B' X D L =

          parentNormalForm m hm A B f X D L s.rowState s.markerState := by

  obtain ⟨A, B, hA, hB, hAB, hAi, hBi, hcorner⟩ :=

    physical_original_masks m hm f A' B' hA' hB' hAB'

  let s := parentStructure m hm A B hA hB f X D L hD hLD

  refine ⟨A, B, hA, hB, hAB, hAi, hBi, s, ?_⟩

  have hground : HistoryCorners.residual ((ground m).image f) A' B' =

      (localRows m hm A B).ground.image f := by

    rw [← hAi, ← hBi]

    change HistoryCorners.residual ((ground m).image f) (A.image f) (B.image f) = (HistoryCorners.residual (ground m) A B).image f

    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]

  have hswitch : Disjoint A' ((rim m hm).image f) ↔ Disjoint A (rim m hm) := by

    rw [← hAi]

    exact Finset.disjoint_image f.injective

  have hphysical : physicalDecorated m hm f A' B' X D L = decorated m hm A B f X D L := by

    simp only [physicalDecorated, decorated, hcorner, hground, hswitch,

      Finset.image_sdiff _ _ f.injective]

  exact hphysical.trans s.parentRoot

end PhysicalParent

**Definition 1.57 (MarkerCase.absent).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absent`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.58 (MarkerCase.absorbed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absorbed`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absorbed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.59 (MarkerCase.noMarker).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.noMarker`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.noMarker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.60 (MarkerCase.oneMarker).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.oneMarker`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.oneMarker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.61 (MarkerCase.separated).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.62 (MarkerCase.intact).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.intact`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.intact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive MarkerCase : Type

  | absent (h : ¬ Disjoint A (rim m hm))

  | absorbed (h : Disjoint A (rim m hm))

      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)

  | noMarker (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = ∅)

  | oneMarker (h : Disjoint A (rim m hm))

      (a : Fin m) (ha : a ∈ live m hm A B)

      (hF : «at» m hm a ∉ forced (localRows m hm A B))

      (hR : markers m hm A B = {«at» m hm a})

  | separated (h : Disjoint A (rim m hm))

      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))

      (hR : markers m hm A B = rim m hm)

      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))

  | intact (hA : A = ∅) (hB : B = ∅)

      (hF : forced (localRows m hm A B) = ∅)

      (full : component m hm A B (leftEnd m hm) = Finset.univ)

      (sole : components m hm A B = {Finset.univ})

      (labels : block m hm A B (leftEnd m hm) = ground m)

      (root : (localRows m hm A B).root = pathRoot m hm)

Definitions and proofs are in the paired Lean module.

/-- TOTAL exhaustive classification for every width and every local original mask.

A surviving marker is forced precisely by a singleton row, never by support loss. -/

**Definition 1.63 (RowCase.simplex).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.simplex`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive RowCase : Type

  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)

  | void (none : IsEmpty (localRows m hm A B).chords)

  | forest (some : Nonempty (localRows m hm A B).chords)

      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

**Definition 1.64 (RowCase.void).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.void`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.void` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive RowCase : Type

  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)

  | void (none : IsEmpty (localRows m hm A B).chords)

  | forest (some : Nonempty (localRows m hm A B).chords)

      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

**Definition 1.65 (RowCase.forest).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forest`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

inductive RowCase : Type

  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)

  | void (none : IsEmpty (localRows m hm A B).chords)

  | forest (some : Nonempty (localRows m hm A B).chords)

      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

**Definition 1.66 (ParentStructure.mk).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.mk`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.mk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.67 (ParentStructure.rowState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowState`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.68 (ParentStructure.markerState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerState`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.69 (ParentStructure.localRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.localRoot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.localRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.70 (ParentStructure.parentRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentRoot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.71 (ParentStructure.literalPath).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.literalPath`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.literalPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.72 (ParentStructure.cover).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.cover`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.cover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.73 (ParentStructure.originalGround).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalGround`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalGround` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.74 (ParentStructure.originalMarkers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalMarkers`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalMarkers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.75 (ParentStructure.graphRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graphRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graphRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.76 (ParentStructure.partition).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.partition`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.77 (ParentStructure.consecutive).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.consecutive`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.consecutive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.78 (ParentStructure.componentPaths).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.componentPaths`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.componentPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.79 (ParentStructure.forcedSingletons).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forcedSingletons`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forcedSingletons` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.80 (ParentStructure.isolatedGhosts).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.isolatedGhosts`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.isolatedGhosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

**Definition 1.81 (ParentStructure.separatedEnds).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separatedEnds`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separatedEnds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Constructor or projection in its full enclosing source:

structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]

    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where

  rowState : RowCase m hm A B

  markerState : MarkerCase m hm A B

  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState

  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState

  literalPath : (localRows m hm A B).root = corner (ground m) A B

    (HistoryPaths.pathRows (pathRootPath m hm)).root

  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C

  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔

    ∃ a ∈ live m hm A B, x ∈ block m hm A B a

  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}

  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧

    ∃ c : (prune (localRows m hm A B)).chords,

      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}

  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →

    component m hm A B a = component m hm A B b ∨

      Disjoint (component m hm A B a) (component m hm A B b)

  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →

    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a

  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →

    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)

  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →

    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}

  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →

    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}

  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →

    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →

    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

Definitions and proofs are in the paired Lean module.

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,

injection, earlier families and their support/order, never a desired structural result. -/

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.alive`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.at`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.block_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.componentUnion`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_consecutive`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_partition`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.component_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.components`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.connected_iff_interval`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.cutRow`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.empty_row_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.endpoints_connected_untouched`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.forced_component`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.interval`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.isolated_component`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.leftEnd`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.live`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.localRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.mem_forced`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.no_rows_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.position`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.projected_row_cases`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.prune_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reducedGraph`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.reduced_row_cases`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents.rightEnd`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.MarkerCase`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.ParentStructure`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.RowCase`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absent`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.absorbed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyMarkers`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.classifyRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.componentPaths`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.component_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.components_cover`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.consecutive`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.corner_rows_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.cover`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.decorated_readback`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forcedSingletons`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forced_marker_absorbs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.forest`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graphRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.graph_actual_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.intact`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.isolatedGhosts`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.literalPath`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.localRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.local_path_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerNormalForm`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markerState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.marker_positions`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.markers`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.mk`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.noMarker`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.oneMarker`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalGround`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.originalMarkers`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.original_labels`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentNormalForm`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.parentStructure`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.partition`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physicalDecorated`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_corner_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_original_masks`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.physical_parent_readback`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowRootForm`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.rowState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separatedEnds`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.separated_components`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.simplex`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests.void`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners](HistoryCorners.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents](HistoryForestComponents.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers](HistoryMarkers.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths](HistoryPaths.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalMWheel](PhysicalMWheel.md)
