/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents
   mirror-E: none(waiver:original-projected-path-forest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Literal projected wheel-path rows, redundant supersets, cut intervals and original endpoint markers. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance historyForestsPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
open OriginalLabelTwoSum HistoryCorners AllMWheel

section IndexedRows
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Singleton constraints are labels, not a replacement ground. -/
def forced (r : Rows V) : Finset V := by classical exact r.ground.filter (fun x => ∃ c : r.chords, r.row c = {x})

@[simp] theorem mem_forced (r : Rows V) (x : V) :
    x ∈ forced r ↔ ∃ c : r.chords, r.row c = {x} := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · rintro ⟨c, hc⟩
    exact Finset.mem_filter.mpr ⟨r.row_supported c (by simp [hc]), c, hc⟩

/-- Only size-two superset ROWS touching a singleton are removed.
The index subtype retains every other original multiplicity and every label. -/
def prune (r : Rows V) : Rows V where
  ground := r.ground
  chords := {c : r.chords // (r.row c).card ≠ 2 ∨ Disjoint (r.row c) (forced r)}
  row c := r.row c.1
  row_supported c := r.row_supported c.1

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

/-- An existing empty ROW yields a simplex, even on zero ground (UNIT). -/
theorem empty_row_root (r : Rows V) (c : r.chords) (hc : r.row c = ∅) :
    r.root = delta r.ground := by
  apply SetLike.ext
  intro s
  exact ⟨r.root_supported s, fun hs => ⟨c, by simpa [hc] using hs⟩⟩

/-- No surviving index yields VOID, including on zero ground. -/
theorem no_rows_root (r : Rows V) (h : IsEmpty r.chords) : r.root = ⊥ := by
  apply SetLike.ext
  intro s
  exact ⟨fun ⟨c, _⟩ => (h.false c).elim, fun h => h.elim⟩
end IndexedRows

/-- The ACTUAL non-interface rim rows; this is not pathRows with indices forgotten. -/
def localRows (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m)) : Rows (Label m) :=
  cornerRows ((rimRows m (by omega)).without (interfaceRow m hm)) A B

/-- The path coordinate is 2,3,...,m,1. Coordinate zero is not the hub. -/
def «at» (m : Nat) (hm : 3 ≤ m) (i : Fin m) : Label m :=
  if h : i.val + 1 = m then firstLabel m hm else ⟨i.val + 2, by omega⟩

def position (m : Nat) (x : Label m) : Nat :=
  if x.val = 1 then m - 1 else x.val - 2

private theorem at_ground (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    «at» m hm i ∈ ground m := by
  unfold «at»
  split_ifs <;> simp [ground, firstLabel, Fin.ext_iff] <;> omega

private theorem position_at (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    position m («at» m hm i) = i.val := by
  unfold «at» position
  split_ifs <;> simp_all [firstLabel] <;> omega

private theorem position_lt (m : Nat) (hm : 3 ≤ m) (x : Label m)
    (hx : x ∈ ground m) : position m x < m := by
  have hx0 : x.val ≠ 0 := by
    have hn := (Finset.mem_erase.mp hx).1
    exact (not_congr (Fin.ext_iff (a := x) (b := 0))).mp hn
  have := x.isLt
  unfold position
  split_ifs <;> omega

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

private theorem at_injective (m : Nat) (hm : 3 ≤ m) : Function.Injective («at» m hm) := by
  intro i j h
  apply Fin.ext
  simpa only [position_at] using congrArg (position m) h

/-- One original cut, with its two ORIGINAL coordinate labels. -/
def cutRow (m : Nat) (hm : 3 ≤ m) (k : Fin (m - 1)) : Finset (Label m) :=
  {«at» m hm ⟨k.val, by omega⟩, «at» m hm ⟨k.val + 1, by omega⟩}

private theorem cutRow_card (m : Nat) (hm : 3 ≤ m) (k : Fin (m - 1)) :
    (cutRow m hm k).card = 2 := by
  have hn : «at» m hm ⟨k.val, by omega⟩ ≠ «at» m hm ⟨k.val + 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (at_injective m hm h)
    change k.val = k.val + 1 at hv
    omega
  simp [cutRow, hn]

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

section Forest
variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

/-- These are the actual surviving two-element rows after singleton absorption. -/
def alive (k : Fin (m - 1)) : Prop :=
  ∃ c : (localRows m hm A B).chords,
    (localRows m hm A B).row c = cutRow m hm k ∧
      Disjoint (cutRow m hm k) (forced (localRows m hm A B))

/-- Graph built FROM the actual rows. There is no forest/certificate argument. -/
def reducedGraph : SimpleGraph (Fin m) where
  Adj a b := ∃ k : Fin (m - 1), alive m hm A B k ∧
    ((a.val = k.val ∧ b.val = k.val + 1) ∨
     (b.val = k.val ∧ a.val = k.val + 1))
  symm := ⟨by rintro a b ⟨k, hk, h⟩; exact ⟨k, hk, h.symm⟩⟩
  loopless := ⟨by rintro a ⟨k, hk, h | h⟩ <;> omega⟩

/-- Exact interval of intact cuts; used only AFTER its equivalence to walks. -/
def interval (a b : Fin m) : Prop := ∀ k : Fin (m - 1),
  min a.val b.val ≤ k.val → k.val < max a.val b.val → alive m hm A B k

private theorem interval_refl (a : Fin m) : interval m hm A B a a := by
  intro k hl hu
  simp only [min_self, max_self] at hl hu
  omega

private theorem interval_symm {a b : Fin m} (h : interval m hm A B a b) :
    interval m hm A B b a := by
  simpa only [interval, min_comm, max_comm] using h

private theorem interval_trans {a b c : Fin m}
    (h : interval m hm A B a b) (g : interval m hm A B b c) :
    interval m hm A B a c := by
  intro k hl hu
  by_cases h1 : min a.val b.val ≤ k.val ∧ k.val < max a.val b.val
  · exact h k h1.1 h1.2
  · apply g k <;> omega

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

private theorem alive_supported (k : Fin (m - 1)) (h : alive m hm A B k) :
    cutRow m hm k ⊆ (localRows m hm A B).ground := by
  obtain ⟨c, hc, _⟩ := h
  exact hc ▸ (localRows m hm A B).row_supported c

/-- Original surviving positions, including every isolated/forced ghost label. -/
def live : Finset (Fin m) := Finset.univ.filter
  (fun a => «at» m hm a ∈ (localRows m hm A B).ground)

/-- Actual graph components, represented on the original finite coordinate order. -/
def component (a : Fin m) : Finset (Fin m) :=
  (live m hm A B).filter (fun b => Nonempty ((reducedGraph m hm A B).Walk a b))

def components : Finset (Finset (Fin m)) :=
  (live m hm A B).image (component m hm A B)

def block (a : Fin m) : Finset (Label m) :=
  (component m hm A B a).image («at» m hm)

private theorem mem_component (a b : Fin m) :
    b ∈ component m hm A B a ↔ b ∈ live m hm A B ∧ interval m hm A B a b := by
  simp only [component, Finset.mem_filter, connected_iff_interval]

private theorem self_component (a : Fin m) (ha : a ∈ live m hm A B) :
    a ∈ component m hm A B a :=
  (mem_component m hm A B a a).mpr ⟨ha, interval_refl m hm A B a⟩

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

end Forest

section RowComponents
variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

private theorem block_supported (a : Fin m) :
    block m hm A B a ⊆ (localRows m hm A B).ground := by
  rintro x hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hb).1)).2

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

/-- Component rows retain their actual original filtered index as a subtype. -/
def componentRows (a : Fin m) : Rows (Label m) where
  ground := block m hm A B a
  chords := {c : (prune (localRows m hm A B)).chords //
    (prune (localRows m hm A B)).row c ⊆ block m hm A B a}
  row c := (prune (localRows m hm A B)).row c.1
  row_supported c := c.2

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

section Untouched
variable (m : Nat) (hm : 3 ≤ m)

def leftEnd : Fin m := ⟨0, by omega⟩
def rightEnd : Fin m := ⟨m - 1, by omega⟩

private theorem at_leftEnd : «at» m hm (leftEnd m hm) = secondLabel m hm := by
  simp [«at», leftEnd, secondLabel, show 0 + 1 ≠ m by omega]
private theorem at_rightEnd : «at» m hm (rightEnd m hm) = firstLabel m hm := by
  simp [«at», rightEnd, firstLabel, show m - 1 + 1 = m by omega]

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

private theorem unmasked_root : (localRows m hm ∅ ∅).root = pathRoot m hm := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, by simpa [localRows, cornerRows, HistoryCorners.residual] using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, by simp⟩, by simpa [localRows, cornerRows, HistoryCorners.residual] using hc⟩

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


end D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
