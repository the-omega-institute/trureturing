/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryLocalLeaves
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryLocalLeaves
   mirror-E: none(waiver:original-mask-history-recursion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Original-mask local leaf constructions. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
import D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed

/-! These are actual proof bodies for the physical induction. The local solver
recurses on the complete remaining local ground, and allCornersOutput supplies
its external old-corner input by genuine MixedHistory induction.
The only external physical recursive supplier is on the graph of the OLD history.
The local reduction lemmas consume only the explicitly displayed smaller corner.
All grounds are full original residual grounds; rows keep their original indices.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory

local instance historyRecursionPropDecidable :
    (p : Prop) → Decidable p := Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private def groundOutput {W U : Finset V} {K : Family V}
    (h : W = U) (o : Output W K) : Output U K := by
  subst U
  exact o

private theorem corner_supported (W A B : Finset V) (K : Family V) :
    Supported (HistoryCorners.residual W A B) (corner W A B K) := fun _ h => h.1

private theorem linked_le_deleted (X : Finset V) (e : V) (J : Family V) :
    rawLink X e J ≤ restrict X J := by
  intro s hs
  exact ⟨J.lower (Finset.subset_insert _ _) hs.2, hs.1⟩

private theorem empty_corner_rows (r : Rows V) :
    (cornerRows r ∅ ∅).root = r.root := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, by simpa only [cornerRows, HistoryCorners.residual, Finset.union_empty,
      Finset.sdiff_empty] using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, by simp⟩, by simpa only [cornerRows, HistoryCorners.residual,
      Finset.union_empty, Finset.sdiff_empty] using hc⟩

private theorem join_delta (X Y : Finset V) :
    rawJoin (delta X) (delta Y) = delta (X ∪ Y) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Finset.union_subset_union ha hb
  · intro hs
    refine ⟨s ∩ X, Finset.inter_subset_right, s ∩ Y,
      Finset.inter_subset_right, ?_⟩
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    exact ⟨fun hx => (Finset.mem_union.mp (hs hx)).elim
      (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩), by tauto⟩

private theorem join_comm (K L : Family V) : rawJoin K L = rawJoin L K := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨u,hu,t,ht,rfl⟩
    exact ⟨t,ht,u,hu,Finset.union_comm _ _⟩
  · rintro ⟨t,ht,u,hu,rfl⟩
    exact ⟨u,hu,t,ht,Finset.union_comm _ _⟩

private def insertClosedOutput (W : Finset V) (K : Family V) (a : V)
    (hs : Supported W K) (hc : ∀ s ∈ K, insert a s ∈ K) : Output W K := by
  classical
  by_cases h0 : (∅ : Finset V) ∈ K
  · exact .strong (coneCertificate W K a hs (by simpa using hc ∅ h0) hc)
  · exact .void (by
      apply SetLike.ext
      intro s
      exact ⟨fun h => (h0 (K.lower (Finset.empty_subset _) h)).elim,
        fun h => h.elim⟩)

private def simplexJoinOutput (X Y : Finset V) (K : Family V)
    (hK : Supported X K) (o : Output X K) :
    Output (X ∪ Y) (rawJoin K (delta Y)) := by
  classical
  by_cases hY : Y.Nonempty
  · let a := hY.choose
    have ha := hY.choose_spec
    refine insertClosedOutput _ _ a ?_ ?_
    · rintro s ⟨u,hu,t,ht,rfl⟩
      exact Finset.union_subset (fun x hx => Finset.mem_union_left _ (hK u hu hx))
        (fun x hx => Finset.mem_union_right _ (ht hx))
    · rintro s ⟨u,hu,t,ht,rfl⟩
      refine ⟨u,hu,insert a t,Finset.insert_subset ha ht,?_⟩
      ext x
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
  · have he : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    rw [he,Finset.union_empty,(rawJoin_unit K).2]
    exact o

/-- The avoiding-row factor is the actual singleton LINK, not deletion.
The equality includes the raw empty face and keeps every avoiding row index. -/
theorem avoiding_corner (r : Rows V) (a : V) (ha : a ∈ r.ground) :
    (avoiding r a).root = corner r.ground {a} ∅ r.root := by
  apply SetLike.ext
  intro s
  have hg : HistoryCorners.residual r.ground {a} ∅ = r.ground.erase a := by
    ext x
    simp only [HistoryCorners.residual, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, or_false, Finset.mem_erase]
    tauto
  rw [show s ∈ corner r.ground {a} ∅ r.root ↔
      s ⊆ r.ground.erase a ∧ insert a s ∈ r.root by
    change (s ⊆ HistoryCorners.residual r.ground {a} ∅ ∧ s ∪ {a} ∈ r.root) ↔ _
    rw [hg, Finset.union_singleton]]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨hc.trans Finset.sdiff_subset, c.1,
      Finset.insert_subset (Finset.mem_sdiff.mpr ⟨ha,c.2⟩) ?_⟩
    intro x hx
    obtain ⟨hxW, hxq⟩ := Finset.mem_sdiff.mp (hc hx)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hxW,hxq⟩
  · rintro ⟨hs, c, hc⟩
    have hac : a ∉ r.row c := (Finset.mem_sdiff.mp
      (hc (Finset.mem_insert_self _ _))).2
    exact ⟨⟨c,hac⟩, fun x hx => Finset.mem_sdiff.mpr
      ⟨hs hx,(Finset.mem_sdiff.mp (hc (Finset.mem_insert_of_mem hx))).2⟩⟩

/-- The next singleton request uses ORIGINAL masks A+a,B. -/
theorem singleton_original_corner (r : Rows V) (A B : Finset V)
    (hA : A ⊆ r.ground) (a : V) (ha : a ∈ HistoryCorners.residual r.ground A B) :
    (avoiding (cornerRows r A B) a).root =
      corner r.ground (A ∪ {a}) B r.root := by
  rw [avoiding_corner (cornerRows r A B) a ha,
    ← corner_root r A B hA]
  change corner (HistoryCorners.residual r.ground A B) {a} ∅
    (corner r.ground A B r.root) = _
  simpa only [Finset.union_empty] using
    corner_compose r.ground A B {a} ∅ r.root
      (Finset.singleton_subset_iff.mpr ha)

/-- Actual singleton cap from its strictly smaller original corner. -/
def singletonCornerOutput (r : Rows V) (A B : Finset V)
    (hA : A ⊆ r.ground) (a : V) (ha : a ∈ HistoryCorners.residual r.ground A B)
    (c : (cornerRows r A B).chords) (hc : (cornerRows r A B).row c = {a})
    (o : Output ((HistoryCorners.residual r.ground A B).erase a)
      (corner r.ground (A ∪ {a}) B r.root)) :
    Output (HistoryCorners.residual r.ground A B) (corner r.ground A B r.root) := by
  have small := changeOutput o (singleton_original_corner r A B hA a ha).symm
  exact changeOutput (singletonOutput (cornerRows r A B) a ha c hc small)
    (corner_root r A B hA).symm

/-- Removing one, two or three ACTUAL local labels gives the exact strict
decreases. These are not cardinalities of face support. -/
theorem local_decreases (W : Finset V) (a b c : V)
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (W.erase a).card + 1 = W.card ∧
    ((W.erase a).erase b).card + 2 = W.card ∧
    (((W.erase a).erase b).erase c).card + 3 = W.card ∧
    (W.erase a).card < W.card ∧
    ((W.erase a).erase b).card < W.card ∧
    (((W.erase a).erase b).erase c).card < W.card := by
  have hb' : b ∈ W.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hc' : c ∈ (W.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbc.symm,Finset.mem_erase.mpr ⟨hac.symm,hc⟩⟩
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb'
  have h3 := Finset.card_erase_add_one hc'
  omega

/-- The original next masks stay supported and disjoint. -/
theorem next_masks (W A B C D : Finset V) (hA : A ⊆ W) (hB : B ⊆ W)
    (hAB : Disjoint A B) (hC : C ⊆ HistoryCorners.residual W A B)
    (hD : D ⊆ HistoryCorners.residual W A B) (hCD : Disjoint C D) :
    A ∪ C ⊆ W ∧ B ∪ D ⊆ W ∧ Disjoint (A ∪ C) (B ∪ D) := by
  refine ⟨Finset.union_subset hA (hC.trans Finset.sdiff_subset),
    Finset.union_subset hB (hD.trans Finset.sdiff_subset), ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.disjoint_left.mp hAB hx hy
    · exact (Finset.mem_sdiff.mp (hD hy)).2 (Finset.mem_union_left _ hx)
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_sdiff.mp (hC hx)).2 (Finset.mem_union_right _ hy)
    · exact Finset.disjoint_left.mp hCD hx hy

private theorem avoiding_join_le (r : Rows V) (a : V) (ha : a ∈ r.ground) :
    rawJoin (delta {a}) (avoiding r a).root ≤ r.root := by
  rintro s ⟨u, hu, t, ⟨d, ht⟩, rfl⟩
  refine ⟨d.1, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · have he : x = a := Finset.mem_singleton.mp (hu hx)
    subst x
    exact Finset.mem_sdiff.mpr ⟨ha,d.2⟩
  · obtain ⟨hxW,hxq⟩ := Finset.mem_sdiff.mp (ht hx)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hxW,hxq⟩

private theorem avoiding_split (r : Rows V) (a : V) (d : r.chords)
    (had : a ∉ r.row d) (s : Finset V) (hs : s ⊆ r.ground \ r.row d) :
    s ∈ rawJoin (delta {a}) (avoiding r a).root := by
  refine ⟨s ∩ {a}, Finset.inter_subset_right, s.erase a, ⟨⟨d,had⟩, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨hxa,hxs⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxW,hxq⟩ := Finset.mem_sdiff.mp (hs hxs)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxa,hxW⟩,hxq⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_singleton,
      Finset.mem_erase]
    tauto

/-- Derive the one-leaf family from ACTUAL indexed row equations. Only rows
containing a must be ab; duplicate copies of ab are allowed. -/
theorem oneLeaf_rows (r : Rows V) (a b : V) (ha : a ∈ r.ground)
    (d : r.chords) (hd : r.row d = {a,b})
    (leaf : ∀ c : r.chords, a ∈ r.row c → r.row c = {a,b}) :
    r.root = oneLeafFamily ((r.ground.erase a).erase b) a (avoiding r a).root := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨c,hc⟩
    by_cases hac : a ∈ r.row c
    · left
      rw [leaf c hac] at hc
      intro x hx
      obtain ⟨hxW,hxn⟩ := Finset.mem_sdiff.mp (hc hx)
      exact Finset.mem_erase.mpr ⟨fun h => hxn (by simp [h]),
        Finset.mem_erase.mpr ⟨fun h => hxn (by simp [h]),hxW⟩⟩
    · exact Or.inr (avoiding_split r a c hac s hc)
  · rintro (hs | hs)
    · refine ⟨d, ?_⟩
      rw [hd]
      intro x hx
      obtain ⟨hxb,hxaW⟩ := Finset.mem_erase.mp (hs hx)
      obtain ⟨hxa,hxW⟩ := Finset.mem_erase.mp hxaW
      refine Finset.mem_sdiff.mpr ⟨hxW, ?_⟩
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ⟨hxa,hxb⟩
    · exact avoiding_join_le r a ha hs

private theorem deletion_corner (U : Finset V) (b : V) (hb : b ∉ U) (K : Family V) :
    restrict U K = corner (insert b U) ∅ {b} K := by
  apply SetLike.ext
  intro s
  have hg : HistoryCorners.residual (insert b U) ∅ {b} = U := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_union,
      Finset.notMem_empty,false_or,Finset.mem_singleton]
    exact ⟨fun h => h.1.resolve_left h.2, fun h =>
      ⟨Or.inr h,fun he => hb (he ▸ h)⟩⟩
  change (s ∈ K ∧ s ⊆ U) ↔ s ⊆ HistoryCorners.residual (insert b U) ∅ {b} ∧ s ∪ ∅ ∈ K
  rw [hg,Finset.union_empty]
  tauto

/-- ONE-LEAF's smaller request is the original LINK-a, DELETE-b corner.
This theorem does not change deletion into a link. -/
theorem oneLeaf_factor (r : Rows V) (a b : V) (ha : a ∈ r.ground)
    (hb : b ∈ r.ground) (hab : a ≠ b) :
    restrict ((r.ground.erase a).erase b) (avoiding r a).root =
      corner r.ground {a} {b} r.root := by
  have hb' : b ∈ r.ground.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  rw [deletion_corner _ b (by simp)]
  rw [Finset.insert_erase hb', avoiding_corner r a ha]
  have hg : HistoryCorners.residual r.ground {a} ∅ = r.ground.erase a := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  have comp := corner_compose r.ground {a} ∅ ∅ {b} r.root (Finset.empty_subset _)
  rw [hg] at comp
  simpa only [Finset.union_empty,Finset.empty_union] using
    comp

/-- Real one-leaf constructor; the only output input is on the displayed
two-vertex-smaller ground and the precise original masks proved above. -/
def oneLeafRowsOutput (r : Rows V) (a b : V)
    (ha : a ∈ r.ground) (hb : b ∈ r.ground) (hab : a ≠ b)
    (d : r.chords) (hd : r.row d = {a,b})
    (leaf : ∀ c : r.chords, a ∈ r.row c → r.row c = {a,b})
    (o : Output ((r.ground.erase a).erase b) (corner r.ground {a} {b} r.root)) :
    Output r.ground r.root := by
  let U := (r.ground.erase a).erase b
  have hb' : b ∈ r.ground.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hg : insert a (insert b U) = r.ground := by
    rw [show insert b U = r.ground.erase a from Finset.insert_erase hb',
      Finset.insert_erase ha]
  have hs : Supported (insert b U) (avoiding r a).root := by
    rw [Finset.insert_erase hb']
    exact (avoiding r a).root_supported
  have out := oneLeafOutput U a b (avoiding r a).root
    (by rw [Finset.insert_erase hb']; simp) (by simp [U]) hs
    (changeOutput o (oneLeaf_factor r a b ha hb hab).symm)
  exact changeOutput (groundOutput hg out) (oneLeaf_rows r a b ha d hd leaf).symm

/-- Exact composition for the three labels in the TWO-LEAF factor. -/
theorem twoLeaf_factor (r : Rows V) (a b c : V)
    (ha : a ∈ r.ground) (hb : b ∈ r.ground) (hc : c ∈ r.ground)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rawLink (((r.ground.erase a).erase b).erase c) c
      (avoiding (avoiding r a) b).root =
      corner r.ground {a,b,c} ∅ r.root := by
  let U := ((r.ground.erase a).erase b).erase c
  have hb' : b ∈ r.ground.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hc' : c ∈ (r.ground.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbc.symm,Finset.mem_erase.mpr ⟨hac.symm,hc⟩⟩
  have hcorner : rawLink U c (avoiding (avoiding r a) b).root =
      corner ((r.ground.erase a).erase b) {c} ∅
        (avoiding (avoiding r a) b).root := by
    apply SetLike.ext
    intro s
    have hg : HistoryCorners.residual ((r.ground.erase a).erase b) {c} ∅ = U := by
      ext x
      simp only [U,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
        Finset.notMem_empty,or_false,Finset.mem_erase]
      tauto
    change (s ⊆ U ∧ insert c s ∈ _) ↔
      s ⊆ HistoryCorners.residual ((r.ground.erase a).erase b) {c} ∅ ∧ s ∪ {c} ∈ _
    rw [hg,Finset.union_singleton]
  rw [hcorner, avoiding_corner (avoiding r a) b hb', avoiding_corner r a ha]
  have hground : HistoryCorners.residual r.ground {a} ∅ = r.ground.erase a := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  have h1 := corner_compose r.ground {a} ∅ {b} ∅ r.root (by
    rw [hground]
    exact Finset.singleton_subset_iff.mpr hb')
  rw [hground,Finset.union_empty] at h1
  change corner ((r.ground.erase a).erase b) {c} ∅
    (corner (r.ground.erase a) {b} ∅ (corner r.ground {a} ∅ r.root)) = _
  rw [h1]
  have h2 := corner_compose r.ground ({a} ∪ {b}) ∅ {c} ∅ r.root (by
    intro x hx
    have he : x = c := Finset.mem_singleton.mp hx
    subst x
    simp [HistoryCorners.residual,hc,hac.symm,hbc.symm])
  have hground2 : HistoryCorners.residual r.ground ({a} ∪ {b}) ∅ = (r.ground.erase a).erase b := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  rw [hground2] at h2
  simpa only [Finset.union_empty,Finset.singleton_union,Finset.insert_union,
    Finset.insert_empty] using h2

/-- ONE-LEAF factor after an existing corner: ORIGINAL link/delete masks. -/
theorem oneLeaf_original_corner (r : Rows V) (A B : Finset V) (hA : A ⊆ r.ground)
    (a b : V) (ha : a ∈ HistoryCorners.residual r.ground A B) (hb : b ∈ HistoryCorners.residual r.ground A B)
    (hab : a ≠ b) :
    restrict (((HistoryCorners.residual r.ground A B).erase a).erase b)
      (avoiding (cornerRows r A B) a).root =
      corner r.ground (A ∪ {a}) (B ∪ {b}) r.root := by
  change restrict (((cornerRows r A B).ground.erase a).erase b)
    (avoiding (cornerRows r A B) a).root = _
  rw [oneLeaf_factor (cornerRows r A B) a b ha hb hab,
    ← corner_root r A B hA]
  change corner (HistoryCorners.residual r.ground A B) {a} {b}
    (corner r.ground A B r.root) = _
  exact corner_compose r.ground A B {a} {b} r.root
    (Finset.singleton_subset_iff.mpr ha)

/-- TWO-LEAF factor after an existing corner: the THREE labels enter the
original LINK mask; B is unchanged. No support-ground compression occurs. -/
theorem twoLeaf_original_corner (r : Rows V) (A B : Finset V) (hA : A ⊆ r.ground)
    (a b c : V) (ha : a ∈ HistoryCorners.residual r.ground A B)
    (hb : b ∈ HistoryCorners.residual r.ground A B) (hc : c ∈ HistoryCorners.residual r.ground A B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rawLink ((((HistoryCorners.residual r.ground A B).erase a).erase b).erase c) c
      (avoiding (avoiding (cornerRows r A B) a) b).root =
      corner r.ground (A ∪ {a,b,c}) B r.root := by
  change rawLink ((((cornerRows r A B).ground.erase a).erase b).erase c) c
    (avoiding (avoiding (cornerRows r A B) a) b).root = _
  rw [twoLeaf_factor (cornerRows r A B) a b c ha hb hc hab hac hbc,
    ← corner_root r A B hA]
  change corner (HistoryCorners.residual r.ground A B) {a,b,c} ∅
    (corner r.ground A B r.root) = _
  simpa only [Finset.union_empty] using
    corner_compose r.ground A B {a,b,c} ∅ r.root (by
      intro x hx
      rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc)

private theorem join_sup (K L M : Family V) :
    rawJoin K (L ⊔ M) = rawJoin K L ⊔ rawJoin K M := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨u,hu,t,ht | ht,rfl⟩
    · exact Or.inl ⟨u,hu,t,ht,rfl⟩
    · exact Or.inr ⟨u,hu,t,ht,rfl⟩
  · rintro (⟨u,hu,t,ht,rfl⟩ | ⟨u,hu,t,ht,rfl⟩)
    · exact ⟨u,hu,t,Or.inl ht,rfl⟩
    · exact ⟨u,hu,t,Or.inr ht,rfl⟩

private theorem join_assoc (K L M : Family V) :
    rawJoin (rawJoin K L) M = rawJoin K (rawJoin L M) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨u,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩
    exact ⟨a,ha,b ∪ c,⟨b,hb,c,hc,rfl⟩,Finset.union_assoc _ _ _⟩
  · rintro ⟨a,ha,u,⟨b,hb,c,hc,rfl⟩,rfl⟩
    exact ⟨a ∪ b,⟨a,ha,b,hb,rfl⟩,c,hc,(Finset.union_assoc _ _ _).symm⟩

/-- TWO-LEAF is proved from the actual ab and bc indexed rows. After the
two adjacent row layers, all remaining rows avoid a and b. -/
theorem twoLeaf_rows (r : Rows V) (a b c : V)
    (ha : a ∈ r.ground) (hb : b ∈ r.ground) (hc : c ∈ r.ground)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (dab dbc : r.chords) (habrow : r.row dab = {a,b}) (hbcrow : r.row dbc = {b,c})
    (leafa : ∀ d : r.chords, a ∈ r.row d → r.row d = {a,b})
    (leafb : ∀ d : r.chords, b ∈ r.row d → r.row d = {a,b} ∨ r.row d = {b,c}) :
    r.root = twoLeafFamily (((r.ground.erase a).erase b).erase c) a b c
      (avoiding (avoiding r a) b).root := by
  let U := ((r.ground.erase a).erase b).erase c
  have hc' : c ∈ (r.ground.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbc.symm,Finset.mem_erase.mpr ⟨hac.symm,hc⟩⟩
  have hdbc : a ∉ r.row dbc := by simp [hbcrow,hab,hac]
  have hb' : b ∈ (avoiding r a).ground := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hleaf : ∀ d : (avoiding r a).chords,
      b ∈ (avoiding r a).row d → (avoiding r a).row d = {b,c} := by
    intro d hd
    rcases leafb d.1 hd with he | he
    · exact (d.2 (by simp [he])).elim
    · exact he
  have hK := oneLeaf_rows (avoiding r a) b c hb' ⟨dbc,hdbc⟩ hbcrow hleaf
  rw [oneLeaf_rows r a b ha dab habrow leafa, hK]
  change oneLeafFamily ((r.ground.erase a).erase b) a
    (oneLeafFamily U b (avoiding (avoiding r a) b).root) =
      twoLeafFamily U a b c (avoiding (avoiding r a) b).root
  have hU : (r.ground.erase a).erase b = insert c U := (Finset.insert_erase hc').symm
  calc
    oneLeafFamily ((r.ground.erase a).erase b) a
        (oneLeafFamily U b (avoiding (avoiding r a) b).root) =
        oneLeafFamily (insert c U) a
          (oneLeafFamily U b (avoiding (avoiding r a) b).root) :=
      congrArg (fun T => oneLeafFamily T a
        (oneLeafFamily U b (avoiding (avoiding r a) b).root)) hU
    _ = twoLeafFamily U a b c (avoiding (avoiding r a) b).root := by
      unfold oneLeafFamily twoLeafFamily
      rw [join_sup,join_delta,← join_assoc,join_delta]
      simp only [Finset.singleton_union,Finset.insert_empty,sup_assoc]

/-- Real TWO-LEAF constructor from the three-vertex-smaller LINK factor.
It preserves b on the OUTER declared ground exactly as the native API does. -/
def twoLeafRowsOutput (r : Rows V) (a b c : V)
    (ha : a ∈ r.ground) (hb : b ∈ r.ground) (hc : c ∈ r.ground)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (dab dbc : r.chords) (habrow : r.row dab = {a,b}) (hbcrow : r.row dbc = {b,c})
    (leafa : ∀ d : r.chords, a ∈ r.row d → r.row d = {a,b})
    (leafb : ∀ d : r.chords, b ∈ r.row d → r.row d = {a,b} ∨ r.row d = {b,c})
    (o : Output (((r.ground.erase a).erase b).erase c)
      (corner r.ground {a,b,c} ∅ r.root)) : Output r.ground r.root := by
  let U := ((r.ground.erase a).erase b).erase c
  have hb' : b ∈ r.ground.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hc' : c ∈ (r.ground.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbc.symm,Finset.mem_erase.mpr ⟨hac.symm,hc⟩⟩
  have hIc : insert c U = (r.ground.erase a).erase b := Finset.insert_erase hc'
  have hIb : insert b (insert c U) = r.ground.erase a := by
    rw [hIc,Finset.insert_erase hb']
  have hg : insert a (insert b (insert c U)) = r.ground := by
    rw [hIb,Finset.insert_erase ha]
  have hs : Supported (insert c U) (avoiding (avoiding r a) b).root := by
    rw [hIc]
    exact (avoiding (avoiding r a) b).root_supported
  have out := twoLeafOutput U a b c (avoiding (avoiding r a) b).root
    (by rw [hIb]; simp) (by rw [hIc]; simp) (by simp [U]) hs
    (changeOutput o (twoLeaf_factor r a b c ha hb hc hab hac hbc).symm)
  exact changeOutput (groundOutput hg out)
    (twoLeaf_rows r a b c ha hb hc hab hac hbc dab dbc habrow hbcrow leafa leafb).symm

/-- A nontrivial ACTUAL component has a derived left leaf. This uses the
component equations and current row graph, never a supplied leaf oracle.
The later obligation is to select a usable unmarked leaf OR the intact branch. -/
theorem component_left_leaf (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) (a b : Fin m)
    (ha : a ∈ HistoryForests.live m hm A B)
    (hb : b ∈ HistoryForests.component m hm A B a) (hab : a ≠ b) :
    ∃ x y : Fin m,
      x ∈ HistoryForests.component m hm A B a ∧
      y ∈ HistoryForests.component m hm A B a ∧
      (HistoryForests.reducedGraph m hm A B).Adj x y ∧
      (∀ t, (HistoryForests.reducedGraph m hm A B).Adj x t → t = y) := by
  classical
  let C := HistoryForests.component m hm A B a
  have haa : a ∈ C := Finset.mem_filter.mpr ⟨ha,⟨.nil⟩⟩
  have hC : C.Nonempty := ⟨a,haa⟩
  let x := C.min' hC
  have hx : x ∈ C := Finset.min'_mem C hC
  have hz : ∃ z ∈ C, x.val < z.val := by
    by_cases hxa : x = a
    · refine ⟨b,hb,?_⟩
      have hle : x ≤ b := Finset.min'_le C b hb
      have hne : x.val ≠ b.val := fun he => hab (hxa ▸ Fin.ext he)
      change x.val ≤ b.val at hle
      omega
    · refine ⟨a,haa,?_⟩
      have hle : x ≤ a := Finset.min'_le C a haa
      have hne : x.val ≠ a.val := fun he => hxa (Fin.ext he)
      change x.val ≤ a.val at hle
      omega
  obtain ⟨z,hzC,hxz⟩ := hz
  let y : Fin m := ⟨x.val+1,by have := z.isLt; omega⟩
  have hy : y ∈ C := HistoryForests.component_consecutive m hm A B a x z y
    hx hzC (by dsimp [y]; omega) (by dsimp [y]; omega)
  have hxy : (HistoryForests.reducedGraph m hm A B).Adj x y :=
    (HistoryForests.component_edges m hm A B a x y hx hy).mpr (Or.inl rfl)
  refine ⟨x,y,hx,hy,hxy,?_⟩
  intro t hxt
  have htLive : t ∈ HistoryForests.live m hm A B := by
    obtain ⟨hne,d,hd⟩ := (HistoryForests.graph_actual_rows m hm A B x t).mp hxt
    have ht := (HistoryForests.prune (HistoryForests.localRows m hm A B)).row_supported d
      (hd.symm ▸ (by simp : HistoryForests.«at» m hm t ∈
        ({HistoryForests.«at» m hm x,HistoryForests.«at» m hm t} : Finset _)))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
  obtain ⟨p⟩ := (Finset.mem_filter.mp hx).2
  have htC : t ∈ C := Finset.mem_filter.mpr
    ⟨htLive,⟨p.append (.cons hxt .nil)⟩⟩
  have hle : x ≤ t := Finset.min'_le C t htC
  change x.val ≤ t.val at hle
  have hstep := (HistoryForests.component_edges m hm A B a x t hx htC).mp hxt
  apply Fin.ext
  dsimp [y]
  rcases hstep with hstep | hstep <;> omega

/- The following bridge works with literal row indices, before any normal-form
or native projection. Its old-row case is essential: a graph leaf alone does
not certify a leaf of the physical indexed row family. -/
private theorem path_at_injective (m : Nat) (hm : 3 ≤ m) :
    Function.Injective (HistoryForests.«at» m hm) := by
  have hp : ∀ x : Fin m,
      HistoryForests.position m (HistoryForests.«at» m hm x) = x.val := by
    intro x
    unfold HistoryForests.«at» HistoryForests.position
    split_ifs <;> simp_all [AllMWheel.firstLabel] <;> omega
  intro x y h
  apply Fin.ext
  simpa only [hp] using congrArg (HistoryForests.position m) h

private theorem path_rim_positions (m : Nat) (hm : 3 ≤ m) (x : Fin m) :
    HistoryForests.«at» m hm x ∈ AllMWheel.rim m hm ↔
      x = HistoryForests.leftEnd m hm ∨ x = HistoryForests.rightEnd m hm := by
  have hl : HistoryForests.«at» m hm (HistoryForests.leftEnd m hm) =
      AllMWheel.secondLabel m hm := by
    simp [HistoryForests.«at», HistoryForests.leftEnd, AllMWheel.secondLabel,
      show 0 + 1 ≠ m by omega]
  have hr : HistoryForests.«at» m hm (HistoryForests.rightEnd m hm) =
      AllMWheel.firstLabel m hm := by
    simp [HistoryForests.«at», HistoryForests.rightEnd, AllMWheel.firstLabel,
      show m - 1 + 1 = m by omega]
  rw [AllMWheel.rim, ← hl, ← hr]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inr (path_at_injective m hm h)
    · exact Or.inl (path_at_injective m hm h)
  · rintro (rfl | rfl) <;> simp

private theorem sizeTwo_forced_empty (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m))
    (hrows : ∀ d : (HistoryForests.localRows m hm A B).chords,
      ((HistoryForests.localRows m hm A B).row d).card = 2) :
    HistoryForests.forced (HistoryForests.localRows m hm A B) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨d,hd⟩ := (HistoryForests.mem_forced _ a).mp ha
  have hc := hrows d
  rw [hd, Finset.card_singleton] at hc
  omega

private theorem sizeTwo_row_positions (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m))
    (hrows : ∀ d : (HistoryForests.localRows m hm A B).chords,
      ((HistoryForests.localRows m hm A B).row d).card = 2)
    (d : (HistoryForests.localRows m hm A B).chords) :
    ∃ x y : Fin m,
      (HistoryForests.localRows m hm A B).row d =
        {HistoryForests.«at» m hm x, HistoryForests.«at» m hm y} ∧
      (HistoryForests.reducedGraph m hm A B).Adj x y := by
  classical
  obtain ⟨k,hkA,hk,h0 | h1 | h2⟩ := HistoryForests.projected_row_cases m hm A B d
  · have hc := hrows d
    rw [h0, Finset.card_empty] at hc
    omega
  · obtain ⟨z,hz,he⟩ := h1
    have hc := hrows d
    rw [he, Finset.card_singleton] at hc
    omega
  · let x : Fin m := ⟨k.val, by omega⟩
    let y : Fin m := ⟨k.val + 1, by omega⟩
    have he : (HistoryForests.localRows m hm A B).row d =
        {HistoryForests.«at» m hm x, HistoryForests.«at» m hm y} := h2
    refine ⟨x,y,he,?_⟩
    apply (HistoryForests.graph_actual_rows m hm A B x y).mpr
    refine ⟨by intro h; have := congrArg Fin.val h; dsimp [x,y] at this; omega,
      ⟨d,Or.inr ?_⟩,he⟩
    rw [sizeTwo_forced_empty m hm A B hrows]
    exact Finset.disjoint_empty_right _

private theorem adjacent_live (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) {x y : Fin m}
    (hxy : (HistoryForests.reducedGraph m hm A B).Adj x y) :
    x ∈ HistoryForests.live m hm A B ∧ y ∈ HistoryForests.live m hm A B := by
  obtain ⟨hne,d,hd⟩ := (HistoryForests.graph_actual_rows m hm A B x y).mp hxy
  constructor <;> apply Finset.mem_filter.mpr <;> refine ⟨Finset.mem_univ _,?_⟩
  · exact (HistoryForests.prune (HistoryForests.localRows m hm A B)).row_supported d
      (hd.symm ▸ (by simp))
  · exact (HistoryForests.prune (HistoryForests.localRows m hm A B)).row_supported d
      (hd.symm ▸ (by simp))

private theorem adjacent_component (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) (a x y : Fin m)
    (hx : x ∈ HistoryForests.component m hm A B a)
    (hxy : (HistoryForests.reducedGraph m hm A B).Adj x y) :
    y ∈ HistoryForests.component m hm A B a := by
  obtain ⟨p⟩ := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨(adjacent_live m hm A B hxy).2,
    ⟨p.append (.cons hxy .nil)⟩⟩

private theorem component_extreme_leaf (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) (a x z : Fin m)
    (hx : x ∈ HistoryForests.component m hm A B a)
    (hz : z ∈ HistoryForests.component m hm A B a) (hxz : x ≠ z)
    (extreme : (∀ t ∈ HistoryForests.component m hm A B a, x.val ≤ t.val) ∨
      (∀ t ∈ HistoryForests.component m hm A B a, t.val ≤ x.val)) :
    ∃ y : Fin m,
      (HistoryForests.reducedGraph m hm A B).Adj x y ∧
      ∀ t, (HistoryForests.reducedGraph m hm A B).Adj x t → t = y := by
  classical
  have hn : x.val ≠ z.val := fun h => hxz (Fin.ext h)
  rcases extreme with low | high
  · have hl := low z hz
    let y : Fin m := ⟨x.val + 1, by have := z.isLt; omega⟩
    have hy := HistoryForests.component_consecutive m hm A B a x z y hx hz
      (by dsimp [y]; omega) (by dsimp [y]; omega)
    refine ⟨y,(HistoryForests.component_edges m hm A B a x y hx hy).mpr
      (Or.inl rfl),?_⟩
    intro t ht
    have htC := adjacent_component m hm A B a x t hx ht
    have hxt := (HistoryForests.component_edges m hm A B a x t hx htC).mp ht
    have hlow := low t htC
    apply Fin.ext
    dsimp [y]
    rcases hxt with hxt | hxt <;> omega
  · have hl := high z hz
    let y : Fin m := ⟨x.val - 1, by have := x.isLt; omega⟩
    have hy := HistoryForests.component_consecutive m hm A B a z x y hz hx
      (by dsimp [y]; omega) (by dsimp [y]; omega)
    refine ⟨y,(HistoryForests.component_edges m hm A B a x y hx hy).mpr
      (Or.inr (by dsimp [y]; omega)),?_⟩
    intro t ht
    have htC := adjacent_component m hm A B a x t hx ht
    have hxt := (HistoryForests.component_edges m hm A B a x t hx htC).mp ht
    have hhigh := high t htC
    apply Fin.ext
    dsimp [y]
    rcases hxt with hxt | hxt <;> omega

/-- Choose an actual minimum or maximum component end outside BOTH original
markers. If both extreme ends were the original ends, their walk would force
both masks empty, contrary to the genuine local cut. -/
theorem unmarked_path_leaf (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m))
    (hA : A ⊆ AllMWheel.ground m) (hB : B ⊆ AllMWheel.ground m)
    (hcut : A ≠ ∅ ∨ B ≠ ∅)
    (hrows : ∀ d : (HistoryForests.localRows m hm A B).chords,
      ((HistoryForests.localRows m hm A B).row d).card = 2)
    (hsome : Nonempty (HistoryForests.localRows m hm A B).chords) :
    ∃ x y : Fin m,
      HistoryForests.«at» m hm x ∈ (HistoryForests.localRows m hm A B).ground \
        AllMWheel.rim m hm ∧
      HistoryForests.«at» m hm y ∈ (HistoryForests.localRows m hm A B).ground ∧
      x ≠ y ∧
      (∃ d : (HistoryForests.localRows m hm A B).chords,
        (HistoryForests.localRows m hm A B).row d =
          {HistoryForests.«at» m hm x, HistoryForests.«at» m hm y}) ∧
      (∀ d : (HistoryForests.localRows m hm A B).chords,
        HistoryForests.«at» m hm x ∈ (HistoryForests.localRows m hm A B).row d →
        (HistoryForests.localRows m hm A B).row d =
          {HistoryForests.«at» m hm x, HistoryForests.«at» m hm y}) := by
  classical
  obtain ⟨d⟩ := hsome
  obtain ⟨a,b,habrow,hab⟩ := sizeTwo_row_positions m hm A B hrows d
  let C := HistoryForests.component m hm A B a
  have ha : a ∈ C := Finset.mem_filter.mpr
    ⟨(adjacent_live m hm A B hab).1,⟨.nil⟩⟩
  have hb : b ∈ C := adjacent_component m hm A B a a b ha hab
  have hab' : a ≠ b := (HistoryForests.graph_actual_rows m hm A B a b).mp hab |>.1
  have hC : C.Nonempty := ⟨a,ha⟩
  let lo := C.min' hC
  let hi := C.max' hC
  have hlo : lo ∈ C := Finset.min'_mem C hC
  have hhi : hi ∈ C := Finset.max'_mem C hC
  have low : ∀ t ∈ C, lo.val ≤ t.val := fun t ht => Finset.min'_le C t ht
  have high : ∀ t ∈ C, t.val ≤ hi.val := fun t ht => Finset.le_max' C t ht
  have hlt : lo.val < hi.val := by
    have hla := low a ha
    have hlb := low b hb
    have hah := high a ha
    have hbh := high b hb
    have hn : a.val ≠ b.val := fun h => hab' (Fin.ext h)
    omega
  have hends : lo ≠ HistoryForests.leftEnd m hm ∨ hi ≠ HistoryForests.rightEnd m hm := by
    by_contra h
    have helo : lo = HistoryForests.leftEnd m hm := by tauto
    have hehi : hi = HistoryForests.rightEnd m hm := by tauto
    obtain ⟨p⟩ := (Finset.mem_filter.mp hlo).2
    obtain ⟨q⟩ := (Finset.mem_filter.mp hhi).2
    have hu := HistoryForests.endpoints_connected_untouched m hm A B hA hB
      (by simpa only [helo,hehi] using (show Nonempty
        ((HistoryForests.reducedGraph m hm A B).Walk lo hi) from ⟨p.reverse.append q⟩))
    exact hcut.elim (fun h => h hu.1) (fun h => h hu.2.1)
  have chosen : ∃ x y : Fin m,
      (HistoryForests.reducedGraph m hm A B).Adj x y ∧
      HistoryForests.«at» m hm x ∉ AllMWheel.rim m hm ∧
      (∀ t, (HistoryForests.reducedGraph m hm A B).Adj x t → t = y) := by
    rcases hends with hleft | hright
    · obtain ⟨y,hxy,hy⟩ := component_extreme_leaf m hm A B a lo hi hlo hhi
        (fun h => by have := congrArg Fin.val h; omega) (Or.inl low)
      refine ⟨lo,y,hxy,?_,hy⟩
      intro hr
      rcases (path_rim_positions m hm lo).mp hr with he | he
      · exact hleft he
      · have := hi.isLt
        dsimp [HistoryForests.rightEnd] at he
        have heval := congrArg Fin.val he
        change lo.val = m - 1 at heval
        omega
    · obtain ⟨y,hxy,hy⟩ := component_extreme_leaf m hm A B a hi lo hhi hlo
        (fun h => by have := congrArg Fin.val h; omega) (Or.inr high)
      refine ⟨hi,y,hxy,?_,hy⟩
      intro hr
      rcases (path_rim_positions m hm hi).mp hr with he | he
      · have := congrArg Fin.val he
        dsimp [HistoryForests.leftEnd] at this
        omega
      · exact hright he
  obtain ⟨x,y,hxy,hxr,leaf⟩ := chosen
  obtain ⟨hne,d,hd⟩ := (HistoryForests.graph_actual_rows m hm A B x y).mp hxy
  refine ⟨x,y,Finset.mem_sdiff.mpr
    ⟨(Finset.mem_filter.mp (adjacent_live m hm A B hxy).1).2,hxr⟩,
    (Finset.mem_filter.mp (adjacent_live m hm A B hxy).2).2,hne,⟨d.1,hd⟩,?_⟩
  intro c hc
  obtain ⟨u,v,he,huv⟩ := sizeTwo_row_positions m hm A B hrows c
  rw [he] at hc
  rcases (show HistoryForests.«at» m hm x = HistoryForests.«at» m hm u ∨
      HistoryForests.«at» m hm x = HistoryForests.«at» m hm v by simpa using hc) with h | h
  · have hxu := path_at_injective m hm h
    subst u
    rw [leaf v huv] at he
    exact he
  · have hxv := path_at_injective m hm h
    subst v
    have huy := leaf u huv.symm
    simpa only [huy,Finset.pair_comm] using he


end D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
