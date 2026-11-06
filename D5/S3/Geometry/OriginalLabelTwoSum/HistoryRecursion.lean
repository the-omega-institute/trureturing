/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryRecursion
   generality: G
   digest: Original-mask usable physical leaves, decreasing local solver and mixed-history recursion.
   SOURCE_ONLY_UNCOMPILED; no elaboration, kernel, native or delivery acceptance. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
import D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed

/-! These are actual proof bodies for the physical induction. The local solver
recurses on the complete remaining local ground, and allCornersOutput supplies
its external old-corner input by genuine MixedHistory induction.
The only external physical recursive supplier is on the graph of the OLD history.
The local reduction lemmas consume only the explicitly displayed smaller corner.
All grounds are full original HistoryCorners.residual grounds; rows keep their original indices.
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
  rw [oneLeaf_factor (cornerRows r A B) a b ha hb hab,
    ← corner_root r A B hA]
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
  rw [twoLeaf_factor (cornerRows r A B) a b c ha hb hc hab hac hbc,
    ← corner_root r A B hA]
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
      (hd.symm ▸ (by change a = Classical.choose singleton; rfl))
  · exact (HistoryForests.prune (HistoryForests.localRows m hm A B)).row_supported d
      (hd.symm ▸ (by change a = Classical.choose singleton; rfl))

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
        have := congrArg Fin.val he
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

private def projectedRimIndexEquiv {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A) :
    (HistoryFactors.projectedRimRows g i A B).chords ≃
      (HistoryForests.localRows i.width i.atLeastThree C D).chords where
  toFun c := ⟨c.1,by
    have hd := c.2
    change Disjoint
      ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1)
      (HistoryFactors.localMask g i A) at hd
    rw [PhysicalMWheel.ambient_row, ← hC] at hd
    exact (Finset.disjoint_image i.labels.injective).mp hd⟩
  invFun c := ⟨c.1,by
    change Disjoint
      ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1)
      (HistoryFactors.localMask g i A)
    rw [PhysicalMWheel.ambient_row, ← hC]
    exact (Finset.disjoint_image i.labels.injective).mpr c.2⟩
  left_inv c := Subtype.ext rfl
  right_inv c := Subtype.ext rfl

private theorem projectedRim_row_image {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A)
    (hD : D.image i.labels = HistoryFactors.localMask g i B)
    (c : (HistoryFactors.projectedRimRows g i A B).chords) :
    (HistoryFactors.projectedRimRows g i A B).row c =
      ((HistoryForests.localRows i.width i.atLeastThree C D).row
        (projectedRimIndexEquiv g i A B C D hC c)).image i.labels := by
  change (PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1 \
    HistoryFactors.localMask g i B =
      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1 \ D).image i.labels
  rw [PhysicalMWheel.ambient_row, ← hD, Finset.image_sdiff _ _ i.labels.injective]

private theorem projectedRim_ground_image {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A)
    (hD : D.image i.labels = HistoryFactors.localMask g i B) :
    HistoryFactors.localResidual g i A B =
      (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels := by
  change HistoryCorners.residual ((AllMWheel.ground i.width).image i.labels)
    (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B) =
      (HistoryCorners.residual (AllMWheel.ground i.width) C D).image i.labels
  rw [← hC, ← hD, HistoryCorners.residual, HistoryCorners.residual,
    Finset.image_sdiff _ _ i.labels.injective, Finset.image_union]

/-- Every surviving local index embeds in the full physical corner with its
literal projected row. No duplicate, singleton or empty row is discarded. -/
theorem physical_rim_indexed {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (c : (HistoryFactors.projectedRimRows g i A B).chords) :
    ∃ d : (cornerRows (wheelStepRows g i) A B).chords,
      (cornerRows (wheelStepRows g i) A B).row d =
        (HistoryFactors.projectedRimRows g i A B).row c := by
  have hq : (HistoryFactors.localRows g i).row c.1 ⊆ HistoryFactors.wheelGround g i :=
    (HistoryFactors.localRows g i).row_supported c.1
  have hr : (HistoryFactors.localRows g i).row c.1 =
      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image i.labels :=
    PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels c.1.1
  let d : (cornerRows (wheelStepRows g i) A B).chords := ⟨.inr c.1,by
    change Disjoint
      ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image i.labels) A
    rw [← hr]
    apply Finset.disjoint_left.mpr
    intro x hx hxA
    exact Finset.disjoint_left.mp c.2 hx (Finset.mem_inter.mpr ⟨hxA,hq hx⟩)⟩
  refine ⟨d,?_⟩
  change (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image
    i.labels \ B = (HistoryFactors.localRows g i).row c.1 \ HistoryFactors.localMask g i B
  rw [← hr]
  ext x
  simp only [HistoryFactors.localMask,Finset.mem_sdiff,Finset.mem_inter]
  exact ⟨fun h => ⟨h.1,fun hb => h.2 hb.1⟩,
    fun h => ⟨h.1,fun hb => h.2 ⟨hb,hq h.1⟩⟩⟩

/-- A fresh local coordinate outside the ORIGINAL interface cannot occur in
any old substituted row. Consequently EVERY current physical index containing
it comes from an actual projected rim index, with exactly the same row. -/
theorem physical_local_incidence {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (a : V)
    (ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (c : (cornerRows (wheelStepRows g i) A B).chords)
    (hc : a ∈ (cornerRows (wheelStepRows g i) A B).row c) :
    ∃ d : (HistoryFactors.projectedRimRows g i A B).chords,
      (cornerRows (wheelStepRows g i) A B).row c =
        (HistoryFactors.projectedRimRows g i A B).row d := by
  have haY : a ∈ HistoryFactors.wheelGround g i :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha).1).1
  have haOld : a ∉ g.ground := fun h => Finset.disjoint_left.mp i.fresh h haY
  have haR : a ∉ HistoryFactors.interface g i := (Finset.mem_sdiff.mp ha).2
  rcases c with ⟨c,hcA⟩
  cases c with
  | inl d =>
      have hsub : a ∈ substitute i.e (HistoryFactors.interface g i) (g.rows.row d) :=
        (Finset.mem_sdiff.mp hc).1
      unfold substitute at hsub
      split_ifs at hsub with he
      · rcases Finset.mem_union.mp hsub with ho | hn
        · exact (haOld (g.rows.row_supported d (Finset.mem_of_mem_erase ho))).elim
        · exact (haR hn).elim
      · exact (haOld (g.rows.row_supported d hsub)).elim
  | inr d =>
      have hq : (HistoryFactors.localRows g i).row d ⊆ HistoryFactors.wheelGround g i :=
        (HistoryFactors.localRows g i).row_supported d
      have hr : (HistoryFactors.localRows g i).row d =
          (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels :=
        PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels d.1
      let e : (HistoryFactors.projectedRimRows g i A B).chords := ⟨d,by
        rw [hr]
        exact hcA.mono_right Finset.inter_subset_left⟩
      refine ⟨e,?_⟩
      change (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image
        i.labels \ B = (HistoryFactors.localRows g i).row d \ HistoryFactors.localMask g i B
      rw [← hr]
      ext x
      simp only [HistoryFactors.localMask,Finset.mem_sdiff,Finset.mem_inter]
      exact ⟨fun h => ⟨h.1,fun hb => h.2 hb.1⟩,
        fun h => ⟨h.1,fun hb => h.2 ⟨hb,hq h.1⟩⟩⟩

/-- The usable physical leaf, with incidence transferred to ALL current indexed
rows, including substituted old rows. The masks, HistoryCorners.residual ground and both
original marker coordinates are the actual physical ones. -/
theorem physical_unmarked_leaf
    {G : Type} (g : GraphData G V) (i : PhysicalHistory.WheelInput g)
    (A B : Finset V)
    (hA : A ⊆ (PhysicalHistory.physicalWheelStep g i).data.ground)
    (hB : B ⊆ (PhysicalHistory.physicalWheelStep g i).data.ground)
    (hAB : Disjoint A B)
    (hcut : HistoryFactors.localMask g i A ≠ ∅ ∨
            HistoryFactors.localMask g i B ≠ ∅)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (hsome : Nonempty (HistoryFactors.projectedRimRows g i A B).chords) :
    let r := HistoryCorners.cornerRows (PhysicalHistory.wheelStepRows g i) A B
    ∃ a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i,
      ∃ b ∈ HistoryFactors.localResidual g i A B,
        a ≠ b ∧ ∃ d : r.chords,
          r.row d = {a,b} ∧
          ∀ c : r.chords, a ∈ r.row c → r.row c = {a,b} := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi
  have hg := projectedRim_ground_image g i A B C D hCi hDi
  have hcut' : C ≠ ∅ ∨ D ≠ ∅ := by
    rcases hcut with h | h
    · exact Or.inl (fun he => h (hCi.symm.trans (by simp [he])))
    · exact Or.inr (fun he => h (hDi.symm.trans (by simp [he])))
  have hrows' : ∀ c : (HistoryForests.localRows i.width i.atLeastThree C D).chords,
      ((HistoryForests.localRows i.width i.atLeastThree C D).row c).card = 2 := by
    intro c
    have hc := hrows (e.symm c)
    rw [hr] at hc
    simpa only [e,Equiv.apply_symm_apply,
      Finset.card_image_of_injective _ i.labels.injective] using hc
  have hsome' : Nonempty (HistoryForests.localRows i.width i.atLeastThree C D).chords :=
    hsome.map e
  obtain ⟨x,y,hx,hy,hxy,⟨d,hd⟩,leaf⟩ :=
    unmarked_path_leaf i.width i.atLeastThree C D hC hD hcut' hrows' hsome'
  let a := i.labels (HistoryForests.«at» i.width i.atLeastThree x)
  let b := i.labels (HistoryForests.«at» i.width i.atLeastThree y)
  have ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hg.symm ▸ Finset.mem_image.mpr ⟨_,(Finset.mem_sdiff.mp hx).1,rfl⟩,?_⟩
    intro haR
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp haR
    have he' : z = HistoryForests.«at» i.width i.atLeastThree x := i.labels.injective he
    exact (Finset.mem_sdiff.mp hx).2 (he' ▸ hz)
  have hb : b ∈ HistoryFactors.localResidual g i A B :=
    hg.symm ▸ Finset.mem_image.mpr ⟨_,hy,rfl⟩
  have hab : a ≠ b := fun h => hxy
    (path_at_injective _ _ (i.labels.injective h))
  have hd' : (HistoryFactors.projectedRimRows g i A B).row (e.symm d) = {a,b} := by
    rw [hr]
    simpa only [e,Equiv.apply_symm_apply,hd,Finset.image_insert,Finset.image_singleton]
  obtain ⟨d',hd'phys⟩ := physical_rim_indexed g i A B (e.symm d)
  refine ⟨a,ha,b,hb,hab,d',hd'phys.trans hd',?_⟩
  intro c hc
  obtain ⟨q,hq⟩ := physical_local_incidence g i A B a ha c hc
  have hm : a ∈ ((HistoryForests.localRows i.width i.atLeastThree C D).row (e q)).image
      i.labels := by
    rw [← hr q,← hq]
    exact hc
  obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hm
  have he' : z = HistoryForests.«at» i.width i.atLeastThree x := i.labels.injective he
  rw [hq,hr,leaf (e q) (he' ▸ hz)]
  simp only [Finset.image_insert,Finset.image_singleton]

private theorem graph_edge_steps (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) {x y : Fin m}
    (h : (HistoryForests.reducedGraph m hm A B).Adj x y) :
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  obtain ⟨k,hk,h | h⟩ := h <;> omega

/-- Each actual size-two projected rim row has its original consecutive path
positions. This is an indexed row statement, stronger than an equality of roots. -/
theorem physical_rim_positions {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (d : (HistoryFactors.projectedRimRows g i A B).chords) :
    ∃ x y : Fin i.width,
      (HistoryFactors.projectedRimRows g i A B).row d =
        {i.labels (HistoryForests.«at» i.width i.atLeastThree x),
          i.labels (HistoryForests.«at» i.width i.atLeastThree y)} ∧
      (x.val + 1 = y.val ∨ y.val + 1 = x.val) := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi
  have hrows' : ∀ c : (HistoryForests.localRows i.width i.atLeastThree C D).chords,
      ((HistoryForests.localRows i.width i.atLeastThree C D).row c).card = 2 := by
    intro c
    have hc := hrows (e.symm c)
    rw [hr] at hc
    simpa only [e,Equiv.apply_symm_apply,
      Finset.card_image_of_injective _ i.labels.injective] using hc
  obtain ⟨x,y,hxy,hedge⟩ := sizeTwo_row_positions i.width i.atLeastThree C D hrows' (e d)
  refine ⟨x,y,?_,graph_edge_steps i.width i.atLeastThree C D hedge⟩
  rw [hr,hxy]
  simp only [Finset.image_insert,Finset.image_singleton]

private theorem physical_incident_positions {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b : V) (hab : a ≠ b)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {b,a}) :
    ∃ x y : Fin i.width,
      b = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∧
      a = i.labels (HistoryForests.«at» i.width i.atLeastThree y) ∧
      (x.val + 1 = y.val ∨ y.val + 1 = x.val) := by
  have hbrow : b ∈ (cornerRows (wheelStepRows g i) A B).row d := by simp [hd]
  obtain ⟨q,hq⟩ := physical_local_incidence g i A B b hb d hbrow
  obtain ⟨x,y,he,hs⟩ := physical_rim_positions g i A B hrows q
  have hba : ({b,a} : Finset V) =
      {i.labels (HistoryForests.«at» i.width i.atLeastThree x),
        i.labels (HistoryForests.«at» i.width i.atLeastThree y)} := hd.symm.trans (hq.trans he)
  have hb' : b = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∨
      b = i.labels (HistoryForests.«at» i.width i.atLeastThree y) := by
    have hh : b ∈ ({b,a} : Finset V) := by simp
    rw [hba] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have ha' : a = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∨
      a = i.labels (HistoryForests.«at» i.width i.atLeastThree y) := by
    have hh : a ∈ ({b,a} : Finset V) := by simp
    rw [hba] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  rcases hb' with hb' | hb'
  · refine ⟨x,y,hb',ha'.resolve_left (fun he => hab (he.trans hb'.symm)),hs⟩
  · exact ⟨y,x,hb',ha'.resolve_right (fun he => hab (he.trans hb'.symm)),hs.symm⟩

private theorem physical_second_neighbour_unique {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b c t : V)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (hab : a ≠ b) (hbc : b ≠ c) (hbt : b ≠ t) (hac : a ≠ c) (hat : a ≠ t)
    (dab dbc dbt : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b})
    (hbcrow : (cornerRows (wheelStepRows g i) A B).row dbc = {b,c})
    (hbtrow : (cornerRows (wheelStepRows g i) A B).row dbt = {b,t}) : t = c := by
  obtain ⟨x,y,hbx,hay,hxy⟩ := physical_incident_positions g i A B hrows a b hab hb dab
    (by simpa only [Finset.pair_comm] using habrow)
  obtain ⟨x',z,hbx',hcz,hxz⟩ := physical_incident_positions g i A B hrows c b hbc.symm hb dbc hbcrow
  obtain ⟨x'',w,hbx'',htw,hxw⟩ := physical_incident_positions g i A B hrows t b hbt.symm hb dbt hbtrow
  have hxx' : x = x' := path_at_injective _ _ (i.labels.injective (hbx.symm.trans hbx'))
  have hxx'' : x = x'' := path_at_injective _ _ (i.labels.injective (hbx.symm.trans hbx''))
  subst x'
  subst x''
  have hyz : y.val ≠ z.val := fun he => hac (hay.trans
    ((congrArg (fun k => i.labels (HistoryForests.«at» i.width i.atLeastThree k))
      (Fin.ext he)).trans hcz.symm))
  have hyw : y.val ≠ w.val := fun he => hat (hay.trans
    ((congrArg (fun k => i.labels (HistoryForests.«at» i.width i.atLeastThree k))
      (Fin.ext he)).trans htw.symm))
  have hwz : w = z := Fin.ext (by omega)
  rw [hwz] at htw
  exact htw.trans hcz.symm

/-- Actual second-edge selection. When b is unmarked, either its only row is
ab, or there is a genuine bc index and EVERY row containing b is ab or bc.
The proof uses original consecutive positions, including all old-row exclusions. -/
theorem physical_neighbour_cases {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b : V) (hab : a ≠ b)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (dab : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b}) :
    (∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      b ∈ (cornerRows (wheelStepRows g i) A B).row d →
      (cornerRows (wheelStepRows g i) A B).row d = {a,b}) ∨
    ∃ c ∈ HistoryFactors.localResidual g i A B,
      a ≠ c ∧ b ≠ c ∧
      ∃ dbc : (cornerRows (wheelStepRows g i) A B).chords,
        (cornerRows (wheelStepRows g i) A B).row dbc = {b,c} ∧
        ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
          b ∈ (cornerRows (wheelStepRows g i) A B).row d →
          (cornerRows (wheelStepRows g i) A B).row d = {a,b} ∨
            (cornerRows (wheelStepRows g i) A B).row d = {b,c} := by
  classical
  let r := cornerRows (wheelStepRows g i) A B
  have other : ∀ (d : r.chords), b ∈ r.row d →
      ∃ c ∈ HistoryFactors.localResidual g i A B, b ≠ c ∧ r.row d = {b,c} := by
    intro d hd
    obtain ⟨q,hq⟩ := physical_local_incidence g i A B b hb d hd
    obtain ⟨x,y,he,hs⟩ := physical_rim_positions g i A B hrows q
    let u := i.labels (HistoryForests.«at» i.width i.atLeastThree x)
    let v := i.labels (HistoryForests.«at» i.width i.atLeastThree y)
    have huv : u ≠ v := by
      intro h
      have hh := congrArg Fin.val (path_at_injective _ _ (i.labels.injective h))
      omega
    have hb' : b = u ∨ b = v := by
      rw [hq,he] at hd
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hd
    have hu : u ∈ HistoryFactors.localResidual g i A B :=
      (HistoryFactors.projectedRimRows g i A B).row_supported q (he.symm ▸ (by simp))
    have hv : v ∈ HistoryFactors.localResidual g i A B :=
      (HistoryFactors.projectedRimRows g i A B).row_supported q (he.symm ▸ (by simp))
    rcases hb' with rfl | rfl
    · exact ⟨v,hv,huv,hq.trans he⟩
    · exact ⟨u,hu,huv.symm,by simpa only [Finset.pair_comm] using hq.trans he⟩
  by_cases honly : ∀ d : r.chords, b ∈ r.row d → r.row d = {a,b}
  · exact Or.inl honly
  · push_neg at honly
    obtain ⟨d,hd,hne⟩ := honly
    obtain ⟨c,hc,hbc,hdc⟩ := other d hd
    have hac : a ≠ c := by
      intro he
      exact hne (by simpa only [← he,Finset.pair_comm] using hdc)
    refine Or.inr ⟨c,hc,hac,hbc,d,hdc,?_⟩
    intro q hq
    by_cases he : r.row q = {a,b}
    · exact Or.inl he
    · obtain ⟨t,ht,hbt,hqt⟩ := other q hq
      have hat : a ≠ t := by
        intro h
        exact he (by simpa only [← h,Finset.pair_comm] using hqt)
      have htc := physical_second_neighbour_unique g i A B hrows a b c t hb
        hab hbc hbt hac hat dab d q habrow hdc hqt
      exact Or.inr (htc ▸ hqt)

/-- Exhaustive cases for the actual projected indexed rows. Only the fixed
two endpoints of each original rim edge are used; the width is arbitrary. -/
theorem physical_projected_row_cases {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (d : (HistoryFactors.projectedRimRows g i A B).chords) :
    (HistoryFactors.projectedRimRows g i A B).row d = ∅ ∨
      (∃ a, (HistoryFactors.projectedRimRows g i A B).row d = {a}) ∨
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2 := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi d
  obtain ⟨k,hkA,hk,h0 | h1 | h2⟩ :=
    HistoryForests.projected_row_cases i.width i.atLeastThree C D (e d)
  · exact Or.inl (by rw [hr,h0,Finset.image_empty])
  · obtain ⟨a,ha,he⟩ := h1
    exact Or.inr (Or.inl ⟨i.labels a,by rw [hr,he,Finset.image_singleton]⟩)
  · apply Or.inr
    apply Or.inr
    have hn : HistoryForests.«at» i.width i.atLeastThree (⟨k.val,by omega⟩ : Fin i.width) ≠
        HistoryForests.«at» i.width i.atLeastThree (⟨k.val + 1,by omega⟩ : Fin i.width) := by
      intro h
      have := congrArg Fin.val (path_at_injective _ _ h)
      omega
    rw [hr,h2,Finset.card_image_of_injective _ i.labels.injective]
    simp only [HistoryForests.cutRow,Finset.card_pair hn]

section EarlierHistory
variable {n : Nat} {G : Type} {g : GraphData G V}

/-- Exact current LOCAL-ground update for the recursive original masks.
The old X is not moved into this measure and HistoryCorners.residual ghosts are not dropped. -/
theorem localResidual_update (i : WheelInput g) (A B C D : Finset V) :
    HistoryFactors.localResidual g i (A ∪ C) (B ∪ D) =
      HistoryCorners.residual (HistoryFactors.localResidual g i A B) C D := by
  ext x
  simp only [HistoryFactors.localResidual,HistoryFactors.localMask,HistoryCorners.residual,
    Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter]
  tauto

/-- The three exact ORIGINAL recursive mask choices lower the ACTUAL local
HistoryCorners.residual cardinality by one, two and three. The masks do not delete old ghosts. -/
theorem localCorner_decreases (i : WheelInput g) (A B : Finset V) (a b c : V)
    (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B)
    (hc : c ∈ HistoryFactors.localResidual g i A B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (HistoryFactors.localResidual g i (A ∪ {a}) B).card + 1 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card + 2 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card + 3 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) B).card <
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card <
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card <
      (HistoryFactors.localResidual g i A B).card := by
  let W := HistoryFactors.localResidual g i A B
  have h1 : HistoryFactors.localResidual g i (A ∪ {a}) B = W.erase a := by
    have he := localResidual_update i A B {a} ∅
    simp only [Finset.union_empty] at he
    rw [he]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  have h2 : HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b}) =
      (W.erase a).erase b := by
    rw [localResidual_update]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_erase]
    tauto
  have h3 : HistoryFactors.localResidual g i (A ∪ {a,b,c}) B =
      ((W.erase a).erase b).erase c := by
    have he := localResidual_update i A B {a,b,c} ∅
    simp only [Finset.union_empty] at he
    rw [he]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  rw [h1,h2,h3]
  exact local_decreases W a b c ha hb hc hab hac hbc

/-- The factor and forest packages really describe the same PHYSICAL target.
Every structural datum is constructed; there is no Output field or premise. -/
theorem step_parent_readback (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B) :
    ∃ (C D : Finset (AllMWheel.Label i.width))
      (hC : C ⊆ AllMWheel.ground i.width) (hD : D ⊆ AllMWheel.ground i.width),
      Disjoint C D ∧ C.image i.labels = HistoryFactors.localMask g i A ∧
      D.image i.labels = HistoryFactors.localMask g i B ∧
      ∃ s : HistoryForests.ParentStructure i.width i.atLeastThree C D i.labels
        (HistoryFactors.oldResidual g i A B)
        (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B),
        corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root =
        HistoryForests.parentNormalForm i.width i.atLeastThree C D i.labels
          (HistoryFactors.oldResidual g i A B)
          (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B)
          s.rowState s.markerState := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hD : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) := by
    rw [r.deleted_readback]
    exact fun _ hs => hs.2
  have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
    rw [r.linked_readback,r.deleted_readback]
    exact linked_le_deleted _ _ _
  obtain ⟨C,D,hC,hD',hCD,hCi,hDi,s,hs⟩ :=
    HistoryForests.physical_parent_readback i.width i.atLeastThree i.labels
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
      (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B)
      Finset.inter_subset_right Finset.inter_subset_right
      (hAB.mono Finset.inter_subset_left Finset.inter_subset_left) hD hLD
  refine ⟨C,D,hC,hD',hCD,hCi,hDi,s,?_⟩
  have hp : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryForests.physicalDecorated i.width i.atLeastThree i.labels
        (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
        (HistoryFactors.oldResidual g i A B)
        (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B) := by
    rw [r.factorization]
    unfold HistoryForests.physicalDecorated
    rw [corner_root (HistoryFactors.localRows g i)
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
      Finset.inter_subset_right]
    rfl
  exact hp.trans hs

private def priorOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (insert i.e (HistoryFactors.oldResidual g i A B))
      (HistoryFactors.prior g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.prior_ground
    (old _ _ r.prior_masks.1 r.prior_masks.2.1 r.prior_masks.2.2)

private def deletedOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryFactors.oldResidual g i A B) (HistoryFactors.deleted g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.factor_grounds.1
    (old _ _ r.deleted_masks.1 r.deleted_masks.2.1 r.deleted_masks.2.2)

private def linkedOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryFactors.oldResidual g i A B) (HistoryFactors.linked g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.factor_grounds.2
    (old _ _ r.linked_masks.1 r.linked_masks.2.1 r.linked_masks.2.2)

/-- A REAL empty projected rim row makes the ENTIRE target a simplex. The
result on zero total ground is UNIT; on nonempty ground it has a cone list. -/
def stepEmptyRowOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (c : (HistoryFactors.projectedRimRows g i A B).chords)
    (hc : (HistoryFactors.projectedRimRows g i A B).row c = ∅) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      delta (HistoryCorners.residual (physicalWheelStep g i).data.ground A B) := by
    apply le_antisymm
    · exact corner_supported _ _ _ _
    · intro s hs
      rw [r.factorization, r.empty_row c hc, join_delta]
      exact Or.inl (Or.inl (r.ground ▸ hs))
  exact changeOutput (HistoryIsolated.simplexOutput _) he.symm

/-- With no remaining local label, use the exact earlier deletion or link.
An existing local index on zero ground instead gives UNIT locally and the
full simplex on X. VOID and UNIT are inspected before native projection. -/
def stepZeroLocalOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hV : HistoryFactors.localResidual g i A B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  by_cases hi : Nonempty (HistoryFactors.projectedRimRows g i A B).chords
  · let c := Classical.choice hi
    have hc : (HistoryFactors.projectedRimRows g i A B).row c = ∅ :=
      Finset.subset_empty.mp (by
        simpa only [r.row_ground, hV] using
          (HistoryFactors.projectedRimRows g i A B).row_supported c)
    exact stepEmptyRowOutput h i A B hA hB hAB c hc
  · have hE : (HistoryFactors.projectedRimRows g i A B).root = ⊥ :=
      r.no_rows ⟨fun c => hi ⟨c⟩⟩
    have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B =
        HistoryFactors.oldResidual g i A B := by
      rw [r.ground, hV, Finset.union_empty]
    have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
      rw [r.linked_readback, r.deleted_readback]
      exact linked_le_deleted _ _ _
    by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
    · have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root = HistoryFactors.deleted g i A B := by
        rw [r.factorization, hE, hV, if_pos hR,
          Finset.empty_sdiff, (rawJoin_void _).2, bot_sup_eq,
          (rawJoin_unit _).2, (rawJoin_unit _).2]
        exact sup_eq_right.mpr hLD
      exact changeOutput (groundOutput hg.symm
        (deletedOutput h i A B hA hB hAB old)) he.symm
    · have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root = HistoryFactors.linked g i A B := by
        rw [r.factorization, hE, hV, if_neg hR, (rawJoin_void _).2,
          bot_sup_eq, (rawJoin_unit _).2, sup_bot_eq]
      exact changeOutput (groundOutput hg.symm
        (linkedOutput h i A B hA hB hAB old)) he.symm

/-- An actual unmarked isolated LOCAL label is a cone apex for the full
physical corner. Old substituted rows and every old ghost remain present in
factorization; the VOID case is kept literal rather than inventing a point. -/
def stepUnusedLocalOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (a : V) (ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (havoid : ∀ c : (HistoryFactors.projectedRimRows g i A B).chords,
      a ∉ (HistoryFactors.projectedRimRows g i A B).row c) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  obtain ⟨haV,haR⟩ := Finset.mem_sdiff.mp ha
  refine insertClosedOutput _ _ a (corner_supported _ _ _ _) ?_
  intro s hs
  rw [r.factorization] at hs ⊢
  rcases hs with (⟨u,hu,t,ht,rfl⟩ | ⟨u,hu,t,ht,rfl⟩) | hs
  · obtain ⟨c,ht⟩ := ht
    refine Or.inl (Or.inl ⟨u,hu,insert a t,⟨c,?_⟩,?_⟩)
    · exact Finset.insert_subset (Finset.mem_sdiff.mpr
        ⟨r.row_ground.symm ▸ haV,havoid c⟩) ht
    · ext x
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
  · refine Or.inl (Or.inr ⟨u,hu,insert a t,Finset.insert_subset haV ht,?_⟩)
    ext x
    simp only [Finset.mem_union,Finset.mem_insert]
    tauto
  · by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
    · rw [if_pos hR] at hs ⊢
      obtain ⟨u,hu,t,ht,rfl⟩ := hs
      refine Or.inr ⟨u,hu,insert a t,Finset.insert_subset
        (Finset.mem_sdiff.mpr ⟨haV,haR⟩) ht,?_⟩
      ext x
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
    · rw [if_neg hR] at hs
      exact hs.elim

/-- With no local row and an absorbed interface, the exact target is the
simplex join of the genuine earlier LINK. Nonempty local ground gives a cone;
zero local ground retains the LINK tag, including VOID and UNIT. -/
def stepAbsorbedNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : ¬ Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hs : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.linked g i A B) := by
    rw [r.linked_readback]
    exact fun _ hx => hx.1
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      rawJoin (HistoryFactors.linked g i A B)
        (delta (HistoryFactors.localResidual g i A B)) := by
    rw [r.factorization,r.no_rows hrows,if_neg hR,
      (rawJoin_void _).2,bot_sup_eq,sup_bot_eq]
  exact changeOutput (groundOutput r.ground.symm
    (simplexJoinOutput _ _ _ hs (linkedOutput h i A B hA hB hAB old))) he.symm

/-- With no local row and no retained original endpoint marker, the exact
factor is the simplex join of the earlier DELETION. All local ghosts remain
on that simplex ground; this is not a compression to face support. -/
def stepNoMarkersNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (hmark : Disjoint (HistoryFactors.localResidual g i A B) (HistoryFactors.interface g i))
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hD : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) := by
    rw [r.deleted_readback]
    exact fun _ hx => hx.2
  have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
    rw [r.linked_readback,r.deleted_readback]
    exact linked_le_deleted _ _ _
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      rawJoin (HistoryFactors.deleted g i A B)
        (delta (HistoryFactors.localResidual g i A B)) := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,r.no_markers hmark,
      (rawJoin_void _).2,bot_sup_eq]
    apply sup_eq_right.mpr
    rintro s ⟨u,hu,t,ht,rfl⟩
    exact ⟨u,hLD hu,t,ht,rfl⟩
  exact changeOutput (groundOutput r.ground.symm
    (simplexJoinOutput _ _ _ hD (deletedOutput h i A B hA hB hAB old))) he.symm

/-- A single isolated retained original endpoint is the literal earlier J
with e renamed to that coordinate. The physical factor equality is proved here;
the native main/core lists are those of the existing marker constructor. -/
def stepSingleMarkerNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (a : V) (haR : a ∈ HistoryFactors.interface g i)
    (hV : HistoryFactors.localResidual g i A B = {a})
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have haX : a ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (Finset.mem_singleton_self a))
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hz : ({a} : Finset V) \ HistoryFactors.interface g i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : x = a := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp hx).2 (he.symm ▸ haR)
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = insert a X := by
    rw [r.ground,hV,Finset.union_singleton]
  have hf : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryIsolated.singleFamily (restrict X J) (rawLink X i.e J) a := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,hV,hz,
      (rawJoin_void _).2,bot_sup_eq,(rawJoin_unit _).2,
      r.deleted_readback,r.linked_readback]
    unfold HistoryIsolated.singleFamily
    rw [join_comm (rawLink X i.e J) (delta {a})]
    exact sup_comm _ _
  exact changeOutput (groundOutput hg.symm
    (HistoryMarkers.singleMarkerOutput X i.e a J heX haX hJ
      (priorOutput h i A B hA hB hAB old))) hf.symm

/-- Both isolated original endpoint markers use the actual twin strip followed
by the earlier J renamed to a. The b-coordinate is retained on the outer ground;
the separate C-ALONE list is inherited unchanged from the real twin API. -/
def stepTwinMarkersNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (a b : V) (hab : a ≠ b) (haR : a ∈ HistoryFactors.interface g i)
    (hbR : b ∈ HistoryFactors.interface g i)
    (hV : HistoryFactors.localResidual g i A B = {a,b})
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have haX : a ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (by simp : a ∈ ({a,b} : Finset V)))
  have hbX : b ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (by simp : b ∈ ({a,b} : Finset V)))
  have hbI : b ∉ insert a X := by
    intro hx
    exact (Finset.mem_insert.mp hx).elim (fun he => hab he.symm) hbX
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hz : ({a,b} : Finset V) \ HistoryFactors.interface g i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : x = a ∨ x = b := by simpa using (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp hx).2 (he.elim
      (fun he => he.symm ▸ haR) (fun he => he.symm ▸ hbR))
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = insert b (insert a X) := by
    rw [r.ground,hV]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hf : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryIsolated.twinFamily (restrict X J) (rawLink X i.e J) a b := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,hV,hz,
      (rawJoin_void _).2,bot_sup_eq,(rawJoin_unit _).2,
      r.deleted_readback,r.linked_readback]
    unfold HistoryIsolated.twinFamily
    rw [join_comm (rawLink X i.e J) (delta {a,b})]
    exact sup_comm _ _
  exact changeOutput (groundOutput hg.symm
    (HistoryMarkers.twinMarkerOutput X i.e a b J heX haX hbI hJ
      (priorOutput h i A B hA hB hAB old))) hf.symm

/-- Actual untouched-path physical attach branch, at EVERY width and every old
mask. The two outputs passed to intactOutput are selected only on g at rank n.
The result is on the physical attach of rank n+1, including interior ports.
The empty-X branch consumes the separate existing arbitrary-coordinate terminal. -/
def stepIntactOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  let X := HistoryFactors.oldResidual g i A B
  let Y := HistoryFactors.wheelGround g i
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hV : HistoryFactors.localResidual g i A B = Y := by
    simp only [HistoryFactors.localResidual, hLA, hLB, HistoryCorners.residual,
      Finset.union_empty, Finset.sdiff_empty, Y]
  have hE : (HistoryFactors.projectedRimRows g i A B).root =
      renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree) := by
    change (cornerRows (HistoryFactors.localRows g i)
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)).root = _
    rw [hLA, hLB, empty_corner_rows]
    exact PhysicalMWheel.ambient_without i.width i.atLeastThree i.labels
  have htail : Y \ HistoryFactors.interface g i =
      (AllMWheel.tailGround i.width i.atLeastThree).image i.labels := by
    exact (Finset.image_sdiff _ _ i.labels.injective).symm
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = X ∪ Y := by
    rw [r.ground, hV]
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X Y :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hparent : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      parentOf X Y ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)
        i.e (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) J := by
    rw [r.factorization, hE, hV, r.deleted_readback, r.linked_readback,
      if_pos (by rw [hLA]; simp), htail]
    unfold parentOf phi
    ac_rfl
  have oJ : Output (insert i.e X) J := priorOutput h i A B hA hB hAB old
  have oL : Output X (rawLink X i.e J) := changeOutput
    (linkedOutput h i A B hA hB hAB old) r.linked_readback
  have out : Output (X ∪ Y)
      (parentOf X Y ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)
        i.e (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) J) := by
    by_cases hX : X.Nonempty
    · exact HistoryIntact.intactOutput i.width i.atLeastThree X i.e J i.labels
        i.zero heX hX hXY hJ oJ oL
    · have hX0 : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
      rw [hX0, Finset.empty_union]
      have hJ0 : Supported ({i.e} : Finset V) J := by
        simpa only [hX0, Finset.insert_empty] using hJ
      exact HistoryIntact.emptyOldEmbeddedIntactOutput i.width i.atLeastThree i.e
        J i.labels i.zero hJ0
  exact changeOutput (groundOutput hg.symm out) hparent.symm

private theorem groundOutput_mainPairsOf {W U : Finset V} {K : Family V}
    (h : W = U) (o : Output W K) :
    HistoryIntact.mainPairsOf (groundOutput h o) = HistoryIntact.mainPairsOf o := by
  subst U
  rfl

private theorem groundOutput_corePairsOf {W U : Finset V} {K : Family V}
    (h : W = U) (o : Output W K) :
    HistoryIntact.corePairsOf (groundOutput h o) = HistoryIntact.corePairsOf o := by
  subst U
  rfl

section IntactOriginalLists
open AllMWheel HistoryIntact HistoryIntactProduct HistoryIsolated HistoryCycles
open private zeroFilling goodOneFilling from D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact

/-- Literal main list at the actual physical intact terminal.
The residue-zero expansion consumes the completed ORIGINAL marker readback. -/
theorem stepIntactOutput_main_faces (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root))
    (hX : (HistoryFactors.oldResidual g i A B).Nonempty) :
    let X := HistoryFactors.oldResidual g i A B
    let J := HistoryFactors.prior g i A B
    let oJ := priorOutput h i A B hA hB hAB old
    let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
    let oL := changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback
    mainPairsOf (stepIntactOutput h i A B hA hB hAB hLA hLB old) =
      if h0 : i.width % 3 = 0 then
        (zeroOneSequence i.width i.atLeastThree h0 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence i.width i.atLeastThree h0 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oJ).map (fun p =>
          ((eta0 i.width i.atLeastThree).image i.labels ∪ p.1.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))),
           (eta0 i.width i.atLeastThree).image i.labels ∪ p.2.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))))) ++
        (mainPairsOf oL).map (fun p =>
          (zeroOtherTop i.width i.atLeastThree i.labels ∪ p.1, zeroOtherTop i.width i.atLeastThree i.labels ∪ p.2))
      else if h2 : i.width % 3 = 2 then
        (twoZeroSequence i.width i.atLeastThree h2 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (twoPathSequence i.width i.atLeastThree h2 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oL).map (fun p => (twoPathTop i.width i.atLeastThree i.labels ∪ p.1, twoPathTop i.width i.atLeastThree i.labels ∪ p.2))
      else match oJ with
        | .void _ => []
        | .unit _ => (fill0 i.width i.atLeastThree).main.pairs.map
            (fun P => (P.lower.image i.labels, P.upper.image i.labels))
        | .strong c =>
            (mainPairsOf oJ).flatMap (fun p =>
              replayFacePairs ((ground i.width).image i.labels) ((tailGround i.width i.atLeastThree).image i.labels) i.e
                (renameFamily i.labels (pathRoot i.width i.atLeastThree)) p
                (rightGammaPairs ((ground i.width).image i.labels) (renameFamily i.labels (pathRoot i.width i.atLeastThree)))) ++
            (fibres c.critical).flatMap (fun q =>
              (selectFilling i.e (zeroFilling i.width i.atLeastThree i.labels) (goodOneFilling i.width i.atLeastThree i.labels) q).main.pairs.map
                (fun P => (criticalPart i.e q ∪ P.lower, criticalPart i.e q ∪ P.upper))) := by
  classical
  dsimp only
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X ((ground i.width).image i.labels) :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  simpa only [stepIntactOutput, dif_pos hX,
    HistoryIntact.changeOutput_mainPairsOf, groundOutput_mainPairsOf] using
    HistoryIntact.intactOutput_main_faces i.width i.atLeastThree X i.e J i.labels
      i.zero heX hX hXY hJ (priorOutput h i A B hA hB hAB old)
      (changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback)

/-- Literal core list at the actual physical intact terminal.
The residue-zero expansion consumes the completed ORIGINAL marker readback. -/
theorem stepIntactOutput_core_faces (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root))
    (hX : (HistoryFactors.oldResidual g i A B).Nonempty) :
    let X := HistoryFactors.oldResidual g i A B
    let J := HistoryFactors.prior g i A B
    let oJ := priorOutput h i A B hA hB hAB old
    let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
    let oL := changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback
    let Y := (ground i.width).image i.labels
    let E := renameFamily i.labels (pathRoot i.width i.atLeastThree)
    let cone := (fibres (((X ∪ Y).erase hX.choose).powerset.filter
      (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) E))).map
      (fun s => (s, insert hX.choose s))
    corePairsOf (stepIntactOutput h i A B hA hB hAB hLA hLB old) =
      if h0 : i.width % 3 = 0 then
        (corePairsOf oJ).map (fun p =>
          ((eta0 i.width i.atLeastThree).image i.labels ∪ p.1.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))),
           (eta0 i.width i.atLeastThree).image i.labels ∪ p.2.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))))) ++
        (match oJ with
          | .void _ => []
          | .unit _ => []
          | .strong c => [((eta0 i.width i.atLeastThree).image i.labels,
              insert (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree)) c.vertex) ((eta0 i.width i.atLeastThree).image i.labels))]) ++
        (corePairsOf oL).map (fun p => (zeroOtherTop i.width i.atLeastThree i.labels ∪ p.1, zeroOtherTop i.width i.atLeastThree i.labels ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(zeroOtherTop i.width i.atLeastThree i.labels, insert c.vertex (zeroOtherTop i.width i.atLeastThree i.labels))]) ++ cone
      else if h2 : i.width % 3 = 2 then
        (corePairsOf oL).map (fun p => (twoPathTop i.width i.atLeastThree i.labels ∪ p.1, twoPathTop i.width i.atLeastThree i.labels ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(twoPathTop i.width i.atLeastThree i.labels, insert c.vertex (twoPathTop i.width i.atLeastThree i.labels))]) ++ cone
      else match oJ with
        | .void _ => cone
        | .unit _ => cone
        | .strong c =>
            (fibres c.critical).flatMap (fun q =>
              (selectFilling i.e (zeroFilling i.width i.atLeastThree i.labels) (goodOneFilling i.width i.atLeastThree i.labels) q).separate.pairs.map
                (fun P => (criticalPart i.e q ∪ P.lower, criticalPart i.e q ∪ P.upper))) ++
            (corePairsOf oJ).flatMap (fun p =>
              replayFacePairs Y ((tailGround i.width i.atLeastThree).image i.labels) i.e E p (rightGammaPairs Y E)) ++
            finishFacePairs X Y ((tailGround i.width i.atLeastThree).image i.labels) ((rim i.width i.atLeastThree).image i.labels)
              i.e c.vertex E (Finset.image_nonempty.mpr ⟨firstLabel i.width i.atLeastThree, by simp [rim]⟩)
              (rightGammaPairs Y E) := by
  classical
  dsimp only
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X ((ground i.width).image i.labels) :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  simpa only [stepIntactOutput, dif_pos hX,
    HistoryIntact.changeOutput_corePairsOf, groundOutput_corePairsOf] using
    HistoryIntact.intactOutput_core_faces i.width i.atLeastThree X i.e J i.labels
      i.zero heX hX hXY hJ (priorOutput h i A B hA hB hAB old)
      (changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback)

end IntactOriginalLists

private theorem local_subset_current (i : WheelInput g) (A B : Finset V) :
    HistoryFactors.localResidual g i A B ⊆
      HistoryCorners.residual (physicalWheelStep g i).data.ground A B := by
  intro x hx
  change x ∈ HistoryCorners.residual (g.ground.erase i.e ∪ HistoryFactors.wheelGround g i) A B
  simp only [HistoryFactors.localResidual,HistoryFactors.localMask,HistoryCorners.residual,
    Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter] at hx ⊢
  tauto

private def stepSingletonFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {a})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a}) B)
      (corner (physicalWheelStep g i).data.ground (A ∪ {a}) B
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have hg : HistoryCorners.residual W (A ∪ {a}) B = (HistoryCorners.residual W A B).erase a := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have small' := changeOutput (groundOutput hg small)
    (congrArg (corner W (A ∪ {a}) B) hr)
  have out := singletonCornerOutput (wheelStepRows g i) A B hA a
    (local_subset_current i A B ha) d hd small'
  exact changeOutput out (congrArg (corner W A B) hr).symm

private def stepOneLeafFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a b : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B) (hab : a ≠ b)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {a,b})
    (leaf : ∀ c : (cornerRows (wheelStepRows g i) A B).chords,
      a ∈ (cornerRows (wheelStepRows g i) A B).row c →
        (cornerRows (wheelStepRows g i) A B).row c = {a,b})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a}) (B ∪ {b}))
      (corner (physicalWheelStep g i).data.ground (A ∪ {a}) (B ∪ {b})
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have ha' := local_subset_current i A B ha
  have hb' := local_subset_current i A B hb
  have hg : HistoryCorners.residual W (A ∪ {a}) (B ∪ {b}) = ((HistoryCorners.residual W A B).erase a).erase b := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have he : corner (HistoryCorners.residual W A B) {a} {b} (cornerRows (wheelStepRows g i) A B).root =
      corner W (A ∪ {a}) (B ∪ {b}) (wheelStepRows g i).root := by
    rw [← corner_root (wheelStepRows g i) A B hA]
    exact corner_compose W A B {a} {b} _ (Finset.singleton_subset_iff.mpr ha')
  have small' := changeOutput (groundOutput hg small)
    ((congrArg (corner W (A ∪ {a}) (B ∪ {b})) hr).trans he.symm)
  have out := oneLeafRowsOutput (cornerRows (wheelStepRows g i) A B) a b
    ha' hb' hab d hd leaf small'
  exact changeOutput out ((corner_root (wheelStepRows g i) A B hA).symm.trans
    (congrArg (corner W A B) hr).symm)

private def stepTwoLeafFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a b c : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B)
    (hc : c ∈ HistoryFactors.localResidual g i A B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (dab dbc : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b})
    (hbcrow : (cornerRows (wheelStepRows g i) A B).row dbc = {b,c})
    (leafa : ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      a ∈ (cornerRows (wheelStepRows g i) A B).row d →
        (cornerRows (wheelStepRows g i) A B).row d = {a,b})
    (leafb : ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      b ∈ (cornerRows (wheelStepRows g i) A B).row d →
        (cornerRows (wheelStepRows g i) A B).row d = {a,b} ∨
          (cornerRows (wheelStepRows g i) A B).row d = {b,c})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a,b,c}) B)
      (corner (physicalWheelStep g i).data.ground (A ∪ {a,b,c}) B
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have ha' := local_subset_current i A B ha
  have hb' := local_subset_current i A B hb
  have hc' := local_subset_current i A B hc
  have hg : HistoryCorners.residual W (A ∪ {a,b,c}) B =
      (((HistoryCorners.residual W A B).erase a).erase b).erase c := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have he : corner (HistoryCorners.residual W A B) {a,b,c} ∅ (cornerRows (wheelStepRows g i) A B).root =
      corner W (A ∪ {a,b,c}) B (wheelStepRows g i).root := by
    rw [← corner_root (wheelStepRows g i) A B hA]
    simpa only [Finset.union_empty] using
      corner_compose W A B {a,b,c} ∅ (wheelStepRows g i).root (by
        intro x hx
        rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
        · exact ha'
        · exact hb'
        · exact hc')
  have small' := changeOutput (groundOutput hg small)
    ((congrArg (corner W (A ∪ {a,b,c}) B) hr).trans he.symm)
  have out := twoLeafRowsOutput (cornerRows (wheelStepRows g i) A B) a b c
    ha' hb' hc' hab hac hbc dab dbc habrow hbcrow leafa leafb small'
  exact changeOutput out ((corner_root (wheelStepRows g i) A B hA).symm.trans
    (congrArg (corner W A B) hr).symm)

private theorem subset_pair_cases (W : Finset V) (p q : V) (hW : W ⊆ {p,q}) :
    W = ∅ ∨ W = {p} ∨ W = {q} ∨ W = {p,q} := by
  classical
  by_cases hp : p ∈ W <;> by_cases hq : q ∈ W
  · exact Or.inr (Or.inr (Or.inr (Finset.Subset.antisymm hW (by simp [hp,hq]))))
  · apply Or.inr
    apply Or.inl
    ext x
    constructor
    · intro hx
      rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
      · simpa only [Finset.mem_singleton] using he
      · exact (hq (he ▸ hx)).elim
    · intro hx
      exact (Finset.mem_singleton.mp hx).symm ▸ hp
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    ext x
    constructor
    · intro hx
      rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
      · exact (hp (he ▸ hx)).elim
      · simpa only [Finset.mem_singleton] using he
    · intro hx
      exact (Finset.mem_singleton.mp hx).symm ▸ hq
  · apply Or.inl
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
    · exact hp (he ▸ hx)
    · exact hq (he ▸ hx)

/-- Total no-local-row terminal, including all retained marker and ghost states.
The only old outputs selected here are exact supported/disjoint corners on g. -/
def stepNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
  · by_cases hmark : Disjoint (HistoryFactors.localResidual g i A B) (HistoryFactors.interface g i)
    · exact stepNoMarkersNoRowsOutput h i A B hA hB hAB hrows hR hmark old
    · by_cases hunused : (HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i).Nonempty
      · let a := hunused.choose
        have ha := hunused.choose_spec
        exact stepUnusedLocalOutput h i A B hA hB hAB a ha
          (fun d => (hrows.false d).elim)
      · have hsub : HistoryFactors.localResidual g i A B ⊆ HistoryFactors.interface g i := by
          intro x hx
          by_contra hn
          exact hunused ⟨x,Finset.mem_sdiff.mpr ⟨hx,hn⟩⟩
        let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
        rw [r.interface_eq] at hsub
        by_cases hz : HistoryFactors.localResidual g i A B = ∅
        · exact stepZeroLocalOutput h i A B hA hB hAB hz old
        by_cases hp : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.firstLabel i.width i.atLeastThree)}
        · exact stepSingleMarkerNoRowsOutput h i A B hA hB hAB hrows hR _
            (by rw [r.interface_eq]; simp) hp old
        by_cases hq : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.secondLabel i.width i.atLeastThree)}
        · exact stepSingleMarkerNoRowsOutput h i A B hA hB hAB hrows hR _
            (by rw [r.interface_eq]; simp) hq old
        have hpq : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.firstLabel i.width i.atLeastThree),
              i.labels (AllMWheel.secondLabel i.width i.atLeastThree)} :=
          (((subset_pair_cases _ _ _ hsub).resolve_left hz).resolve_left hp).resolve_left hq
        have hpq' : i.labels (AllMWheel.firstLabel i.width i.atLeastThree) ≠
            i.labels (AllMWheel.secondLabel i.width i.atLeastThree) := by
          intro he
          have hh := congrArg Fin.val (i.labels.injective he)
          change 1 = 2 at hh
          omega
        exact stepTwinMarkersNoRowsOutput h i A B hA hB hAB hrows hR _ _ hpq'
          (by rw [r.interface_eq]; simp) (by rw [r.interface_eq]; simp) hpq old
  · exact stepAbsorbedNoRowsOutput h i A B hA hB hAB hrows hR old

/-- The total physical local solver. Recursive calls at the CURRENT history
rank use only the exact original masks proved below and strictly decrease the
cardinality of the ACTUAL remaining local ground. The external supplier ranges
only over corners of the strictly earlier graph g. -/
def stepOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  have parent := step_parent_readback h i A B hA hB hAB
  let C := Classical.choose parent
  have parentC := Classical.choose_spec parent
  let D := Classical.choose parentC
  have parentD := Classical.choose_spec parentC
  have hC := Classical.choose parentD
  have parentHC := Classical.choose_spec parentD
  have hD := Classical.choose parentHC
  have parentHD := Classical.choose_spec parentHC
  have hCD := parentHD.1
  have hCi := parentHD.2.1
  have hDi := parentHD.2.2.1
  let s := Classical.choose parentHD.2.2.2
  have hparent := Classical.choose_spec parentHD.2.2.2
  cases hs : s.rowState with
  | simplex c hc =>
      let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
      have hg := projectedRim_ground_image g i A B C D hCi hDi
      have hground : HistoryCorners.residual (physicalWheelStep g i).data.ground A B =
          HistoryFactors.oldResidual g i A B ∪
            (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels :=
        r.ground.trans (congrArg (fun Y => HistoryFactors.oldResidual g i A B ∪ Y) hg)
      have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root =
          delta (HistoryCorners.residual (physicalWheelStep g i).data.ground A B) := by
        rw [hparent,hs]
        change delta (HistoryFactors.oldResidual g i A B ∪
          (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels) = _
        rw [← hground]
      exact changeOutput (HistoryIsolated.simplexOutput _) he.symm
  | void hi =>
      let e := projectedRimIndexEquiv g i A B C D hCi
      exact stepNoRowsOutput h i A B hA hB hAB ⟨fun d => hi.false (e d)⟩ old
  | forest hi hzero =>
      by_cases hV : HistoryFactors.localResidual g i A B = ∅
      · exact stepZeroLocalOutput h i A B hA hB hAB hV old
      · by_cases h0 : ∃ d : (HistoryFactors.projectedRimRows g i A B).chords,
            (HistoryFactors.projectedRimRows g i A B).row d = ∅
        · let d := Classical.choose h0
          have hd := Classical.choose_spec h0
          exact stepEmptyRowOutput h i A B hA hB hAB d hd
        · by_cases h1 : ∃ (d : (HistoryFactors.projectedRimRows g i A B).chords) (a : V),
              (HistoryFactors.projectedRimRows g i A B).row d = {a}
          · let d := Classical.choose h1
            have singleton := Classical.choose_spec h1
            let a := Classical.choose singleton
            have hd := Classical.choose_spec singleton
            have ha : a ∈ HistoryFactors.localResidual g i A B :=
              (HistoryFactors.projectedRimRows g i A B).row_supported d (hd.symm ▸ (by change a = Classical.choose singleton; rfl))
            have ha' := local_subset_current i A B ha
            have indexed := physical_rim_indexed g i A B d
            let q := Classical.choose indexed
            have hq := Classical.choose_spec indexed
            have hm := next_masks (physicalWheelStep g i).data.ground A B {a} ∅ hA hB hAB
              (Finset.singleton_subset_iff.mpr ha') (Finset.empty_subset _) (by simp)
            have hdis : Disjoint (A ∪ {a}) B := by simpa only [Finset.union_empty] using hm.2.2
            have hdec : (HistoryFactors.localResidual g i (A ∪ {a}) B).card <
                (HistoryFactors.localResidual g i A B).card := by
              have he := localResidual_update i A B {a} ∅
              simp only [Finset.union_empty] at he
              have he' : HistoryCorners.residual (HistoryFactors.localResidual g i A B) {a} ∅ =
                  (HistoryFactors.localResidual g i A B).erase a := by
                ext x
                simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
                  Finset.notMem_empty,or_false,Finset.mem_erase]
                tauto
              rw [he,he']
              have hc := Finset.card_erase_add_one ha
              omega
            exact stepSingletonFrom i A B hA a ha q (hq.trans hd)
              (stepOutput h i (A ∪ {a}) B hm.1 hB hdis old)
          · have hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
                ((HistoryFactors.projectedRimRows g i A B).row d).card = 2 := by
              intro d
              rcases physical_projected_row_cases g i A B d with he | ⟨a,he⟩ | he
              · exact (h0 ⟨d,he⟩).elim
              · exact (h1 ⟨d,a,he⟩).elim
              · exact he
            by_cases hsome : Nonempty (HistoryFactors.projectedRimRows g i A B).chords
            · by_cases hcut : HistoryFactors.localMask g i A ≠ ∅ ∨ HistoryFactors.localMask g i B ≠ ∅
              · have leafExists :=
                  physical_unmarked_leaf g i A B hA hB hAB hcut hrows hsome
                let a := Classical.choose leafExists
                have aleaf := Classical.choose_spec leafExists
                have ha := aleaf.1
                let b := Classical.choose aleaf.2
                have bleaf := Classical.choose_spec aleaf.2
                have hb := bleaf.1
                have hab := bleaf.2.1
                let d := Classical.choose bleaf.2.2
                have dleaf := Classical.choose_spec bleaf.2.2
                have hd := dleaf.1
                have leaf := dleaf.2
                have haV := (Finset.mem_sdiff.mp ha).1
                have ha' := local_subset_current i A B haV
                have hb' := local_subset_current i A B hb
                have cases :
                    (b ∈ HistoryFactors.interface g i ∨
                      ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                        b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                          (cornerRows (wheelStepRows g i) A B).row q = {a,b}) ∨
                    ∃ c ∈ HistoryFactors.localResidual g i A B, a ≠ c ∧ b ≠ c ∧
                      ∃ dbc : (cornerRows (wheelStepRows g i) A B).chords,
                        (cornerRows (wheelStepRows g i) A B).row dbc = {b,c} ∧
                        ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                          b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                            (cornerRows (wheelStepRows g i) A B).row q = {a,b} ∨
                              (cornerRows (wheelStepRows g i) A B).row q = {b,c} := by
                  by_cases hbR : b ∈ HistoryFactors.interface g i
                  · exact Or.inl (Or.inl hbR)
                  · rcases physical_neighbour_cases g i A B hrows a b hab
                      (Finset.mem_sdiff.mpr ⟨hb,hbR⟩) d hd with only | second
                    · exact Or.inl (Or.inr only)
                    · exact Or.inr second
                by_cases one :
                    b ∈ HistoryFactors.interface g i ∨
                      ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                        b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                          (cornerRows (wheelStepRows g i) A B).row q = {a,b}
                · have hm := next_masks (physicalWheelStep g i).data.ground A B {a} {b}
                    hA hB hAB (Finset.singleton_subset_iff.mpr ha')
                    (Finset.singleton_subset_iff.mpr hb') (by simpa using hab)
                  have hdec : (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card <
                      (HistoryFactors.localResidual g i A B).card := by
                    rw [localResidual_update]
                    have he : HistoryCorners.residual (HistoryFactors.localResidual g i A B) {a} {b} =
                        ((HistoryFactors.localResidual g i A B).erase a).erase b := by
                      ext x
                      simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
                        Finset.mem_erase]
                      tauto
                    rw [he]
                    have hbE : b ∈ (HistoryFactors.localResidual g i A B).erase a :=
                      Finset.mem_erase.mpr ⟨hab.symm,hb⟩
                    have hca := Finset.card_erase_add_one haV
                    have hcb := Finset.card_erase_add_one hbE
                    omega
                  exact stepOneLeafFrom i A B hA a b haV hb hab d hd leaf
                    (stepOutput h i (A ∪ {a}) (B ∪ {b}) hm.1 hm.2.1 hm.2.2 old)
                · have second := cases.resolve_left one
                  let c := Classical.choose second
                  have csecond := Classical.choose_spec second
                  have hc := csecond.1
                  have hac := csecond.2.1
                  have hbc := csecond.2.2.1
                  let dbc := Classical.choose csecond.2.2.2
                  have dbcsecond := Classical.choose_spec csecond.2.2.2
                  have hbcrow := dbcsecond.1
                  have leafb := dbcsecond.2
                  have hc' := local_subset_current i A B hc
                  have hm := next_masks (physicalWheelStep g i).data.ground A B {a,b,c} ∅
                    hA hB hAB (by
                      intro x hx
                      rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
                      · exact ha'
                      · exact hb'
                      · exact hc') (Finset.empty_subset _) (by simp)
                  have hdis : Disjoint (A ∪ {a,b,c}) B := by
                    simpa only [Finset.union_empty] using hm.2.2
                  have hdec : (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card <
                      (HistoryFactors.localResidual g i A B).card :=
                    (localCorner_decreases i A B a b c haV hb hc hab hac hbc).2.2.2.2.2
                  exact stepTwoLeafFrom i A B hA a b c haV hb hc hab hac hbc d dbc hd hbcrow leaf leafb
                    (stepOutput h i (A ∪ {a,b,c}) B hm.1 hB hdis old)
              · have hLA : HistoryFactors.localMask g i A = ∅ := by tauto
                have hLB : HistoryFactors.localMask g i B = ∅ := by tauto
                exact stepIntactOutput h i A B hA hB hAB hLA hLB old
            · exact stepNoRowsOutput h i A B hA hB hAB ⟨fun d => hsome ⟨d⟩⟩ old
termination_by (HistoryFactors.localResidual g i A B).card
decreasing_by all_goals assumption

end EarlierHistory

/-- The actual prescribed K4 seed, using the bound all-mask seed proof and
the actual physical label/root bridge. Only this FIXED seed uses finite reasoning. -/
def seedOutput (f : K4.SeedLabel ↪ V) (A B : Finset V)
    (hA : A ⊆ (seedGraph f).ground) :
    Output (HistoryCorners.residual (seedGraph f).ground A B)
      (corner (seedGraph f).ground A B (seedGraph f).rows.root) := by
  have out := HistorySeed.seedCornerOutput f A B hA
  have hr : (seedGraph f).rows.root = renameFamily f K4.seedGraphData.rows.root :=
    PhysicalLabels.root K4.seedGraphData f s(0,0)
  rw [hr]
  exact out

/-- Simultaneous all-original-mask construction for EVERY actual finite
MixedHistory. In the attach case ih supplies corners of old at rank n; the
target is the actual physical attach at rank n+1, at every retained port.
No desired Output, forest classification or collapse is an input of this theorem. -/
def allCornersOutput {n : Nat} {G : Type} {g : GraphData G V}
    (h : MixedHistory n G g) :
    ∀ (A B : Finset V), A ⊆ g.ground → B ⊆ g.ground → Disjoint A B →
      Output (HistoryCorners.residual g.ground A B) (corner g.ground A B g.rows.root) := by
  induction h with
  | seed f =>
      intro A B hA hB hAB
      exact seedOutput f A B hA
  | attach old i ih =>
      intro A B hA hB hAB
      exact stepOutput old i A B hA hB hAB ih

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
