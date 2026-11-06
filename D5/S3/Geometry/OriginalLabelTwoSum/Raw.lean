/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Raw
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Raw
   mirror-E: none(waiver:original-label-two-sum-raw)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Literal downward face families preserve original grounds and the empty-face distinction before native projection. -/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! UNCOMPILED source. The mathematical specification is the recovered ORIGINAL
Gamma/two-filling proposal, independently verified in the frozen input. This is
not the released matching-staircase proposal. `Family` is mathlib's LowerSet,
not a new augmented-complex authority. Empty membership is data in that set.
The graph-path binding is a separate obligation from `row_transport` below. -/
noncomputable section
open Set Finset
open scoped unitInterval ContinuousMap
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteConeCollapse FiniteSimplicialJoin

abbrev Family (V : Type*) := LowerSet (Finset V)
variable {V : Type*} [DecidableEq V]

/-- Ground support includes every face, including the empty face when present. -/
def Supported (W : Finset V) (K : Family V) : Prop := ∀ s ∈ K, s ⊆ W

/-- The raw simplex on the given original labels. In particular delta empty is UNIT. -/
def delta (W : Finset V) : Family V where
  carrier := {s | s ⊆ W}
  lower' := fun _ _ h hs => h.trans hs

/-- Original rows are indexed, even when two rows have identical complements. -/
structure Rows (V : Type*) [DecidableEq V] where
  ground : Finset V
  chords : Type*
  row : chords → Finset V
  row_supported : ∀ c, row c ⊆ ground

/-- No row means VOID; an empty complement of an existing row contributes UNIT. -/
def Rows.root (r : Rows V) : Family V where
  carrier := {s | ∃ c, s ⊆ r.ground \ r.row c}
  lower' := by
    rintro s t h ⟨c, hs⟩
    exact ⟨c, h.trans hs⟩

/-- Row deletion is restriction of the index type, and does not delete a vertex. -/
def Rows.without (r : Rows V) (c : r.chords) : Rows V where
  ground := r.ground
  chords := {d : r.chords // d ≠ c}
  row d := r.row d.1
  row_supported d := r.row_supported d.1

/-- Literal simplicial deletion on the specified surviving ground. -/
def restrict (X : Finset V) (K : Family V) : Family V := K ⊓ delta X

/-- Link preserves absence of the raw empty face. -/
def rawLink (X : Finset V) (e : V) (K : Family V) : Family V where
  carrier := {s | s ⊆ X ∧ insert e s ∈ K}
  lower' := by
    rintro s t h ⟨hs, hk⟩
    exact ⟨h.trans hs, K.lower (Finset.insert_subset_insert e h) hk⟩

/-- Augmented join on the same original ambient type; support/disjointness is
proved by consumers. It does not silently supply an empty factor. -/
def rawJoin (K L : Family V) : Family V where
  carrier := {s | ∃ a ∈ K, ∃ b ∈ L, s = a ∪ b}
  lower' := by
    rintro s t h ⟨a, ha, b, hb, rfl⟩
    refine ⟨t ∩ a, K.lower Finset.inter_subset_right ha,
      t ∩ b, L.lower Finset.inter_subset_right hb, ?_⟩
    ext v
    constructor
    · intro hv
      have hvab := h hv
      simp only [Finset.mem_union] at hvab
      simp only [Finset.mem_union, Finset.mem_inter]
      exact hvab.elim (fun h => Or.inl ⟨hv,h⟩) (fun h => Or.inr ⟨hv,h⟩)
    · simp only [Finset.mem_union, Finset.mem_inter]
      tauto

/-- Projection discards just the empty face, after all raw operations. -/
def project (K : Family V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ∈ K}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t h ht => ⟨ht, K.lower h hs.2⟩⟩

/-- Reuse the native owner's augmentation ONLY when a raw-empty witness is
available at the call site. It is not an inverse projection on VOID. -/
def nativeAug [Fintype V] (K : PreAbstractSimplicialComplex V) : Family V where
  carrier := AugmentedFace K
  lower' := fun _ _ h hs => augmented_downward hs h

@[simp] theorem project_nativeAug [Fintype V] (K : PreAbstractSimplicialComplex V) :
    project (nativeAug K) = K := by
  ext s
  change s.Nonempty ∧ (s = ∅ ∨ s ∈ K) ↔ s ∈ K
  constructor
  · rintro ⟨hn,rfl | hs⟩
    · exact False.elim (Finset.not_nonempty_empty hn)
    · exact hs
  · intro hs
    exact ⟨(K.isRelLowerSet_faces hs).1,Or.inr hs⟩

/-- This reconstruction REQUIRES raw empty membership, rather than identifying
VOID with UNIT through their common nonempty projection. -/
theorem reconstruct_nonvoid [Fintype V] (K : Family V) (h0 : (∅ : Finset V) ∈ K) :
    nativeAug (project K) = K := by
  apply SetLike.ext
  intro s
  constructor
  · rintro (rfl | hs)
    · exact h0
    · exact hs.2
  · intro hs
    by_cases he : s = ∅
    · exact Or.inl he
    · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr he,hs⟩

/-- The native skeleton determines the raw family only once raw empty membership
is supplied. This theorem is used for non-VOID filling and Gamma endpoints. -/
theorem raw_ext {K L : Family V} (h0 : (∅ : Finset V) ∈ K ↔ ∅ ∈ L)
    (h : project K = project L) : K = L := by
  apply SetLike.ext
  intro s
  by_cases hs : s = ∅
  · simpa [hs] using h0
  · have hn := Finset.nonempty_iff_ne_empty.mpr hs
    have : s ∈ project K ↔ s ∈ project L := by rw [h]
    change (s.Nonempty ∧ s ∈ K) ↔ (s.Nonempty ∧ s ∈ L) at this
    simpa only [hn, true_and] using this

@[simp] theorem mem_delta (W s : Finset V) : s ∈ delta W ↔ s ⊆ W := Iff.rfl
@[simp] theorem mem_project (K : Family V) (s : Finset V) :
    s ∈ project K ↔ s.Nonempty ∧ s ∈ K := Iff.rfl

/-- The full original ground is independent of which singleton faces occur. -/
structure Root (V : Type*) [DecidableEq V] where
  ground : Finset V
  faces : Family V
  supported : Supported ground faces

def Rows.asRoot (r : Rows V) : Root V where
  ground := r.ground
  faces := r.root
  supported := by
    rintro s ⟨c, hc⟩
    exact hc.trans Finset.sdiff_subset

/-- The exact parent formula; R is never a fake coordinate e. -/
def phi (X Y Z : Finset V) (D L E : Family V) : Family V :=
  (rawJoin D (delta Z) ⊔ rawJoin L (delta Y)) ⊔ rawJoin (delta X) E

/-- Complement roots are supported even when their row family is empty. -/
theorem Rows.root_supported (r : Rows V) : Supported r.ground r.root :=
  r.asRoot.supported

@[simp] theorem rawJoin_void (K : Family V) :
    rawJoin (⊥ : Family V) K = ⊥ ∧ rawJoin K ⊥ = ⊥ := by
  constructor <;> apply SetLike.ext <;> intro s <;>
    simp [rawJoin]

@[simp] theorem rawJoin_unit (K : Family V) :
    rawJoin (delta ∅) K = K ∧ rawJoin K (delta ∅) = K := by
  constructor <;> apply SetLike.ext <;> intro s <;>
    simp [rawJoin, delta, Finset.subset_empty]

/-- Split coordinates are unique on disjoint original grounds. -/
theorem join_split {X Y : Finset V} (hXY : Disjoint X Y)
    {K L : Family V} (hK : Supported X K) (hL : Supported Y L)
    (s : Finset V) : s ∈ rawJoin K L ↔
      s ⊆ X ∪ Y ∧ s ∩ X ∈ K ∧ s ∩ Y ∈ L := by
  have disj : ∀ v, v ∈ X → v ∈ Y → False :=
    fun v hx hy => Finset.disjoint_left.mp hXY hx hy
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    have haX := hK a ha
    have hbY := hL b hb
    have hax : (a ∪ b) ∩ X = a := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h, hx⟩
        exact h.elim id (fun hv => False.elim (disj v hx (hbY hv)))
      · exact fun hv => ⟨Or.inl hv,haX hv⟩
    have hby : (a ∪ b) ∩ Y = b := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h,hy⟩
        exact h.elim (fun hv => False.elim (disj v (haX hv) hy)) id
      · exact fun hv => ⟨Or.inr hv,hbY hv⟩
    exact ⟨Finset.union_subset_union haX hbY, hax.symm ▸ ha, hby.symm ▸ hb⟩
  · rintro ⟨hs,hx,hy⟩
    refine ⟨s ∩ X,hx,s ∩ Y,hy,?_⟩
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp (hs hv) with hx | hy
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hv,hx⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hv,hy⟩))
    · simp only [Finset.mem_union, Finset.mem_inter]
      tauto

/-- Every original row is retained in this literal substitution. This is raw
presentation transport, not a claimed graph unique-path substitution theorem. -/
def substitute (e : V) (R q : Finset V) : Finset V :=
  if e ∈ q then (q.erase e) ∪ R else q

/-- Indexed complementary rows after replacement, on the actual new ground. -/
def transportedRows (X Y : Finset V) (e : V) (R : Finset V)
    (left : Rows V) (right : Rows V) (c : right.chords)
    (hleft : left.ground = insert e X) (hright : right.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) (hR : R ⊆ Y) : Rows V where
  ground := X ∪ Y
  chords := left.chords ⊕ {d : right.chords // d ≠ c}
  row
    | .inl d => substitute e R (left.row d)
    | .inr d => right.row d.1
  row_supported := by
    intro d
    cases d with
    | inl d =>
      have hq := left.row_supported d
      rw [hleft] at hq
      dsimp [substitute]
      split_ifs with h
      · exact Finset.union_subset_union
          (by
            intro v hv
            rcases Finset.mem_insert.mp (hq (Finset.mem_of_mem_erase hv)) with heq | hx
            · exact ((Finset.mem_erase.mp hv).1 heq).elim
            · exact hx) hR
      · intro v hv
        have := hq hv
        rcases Finset.mem_insert.mp this with he | hx
        · subst v; exact False.elim (h hv)
        · exact Finset.mem_union_left _ hx
    | inr d =>
      exact fun v hv => Finset.mem_union_right _ (hright ▸ right.row_supported d.1 hv)

/-- Literal transport membership. The proof keeps the original chord indices;
redundant rows and UNIT-producing complements are not discarded. -/
theorem row_transport (X Y : Finset V) (e : V) (R : Finset V)
    (left right : Rows V) (c : right.chords)
    (hleft : left.ground = insert e X) (hright : right.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y) (hR : R ⊆ Y)
    (hc : right.row c = R) :
    (transportedRows X Y e R left right c hleft hright heX heY hR).root =
      phi X Y (Y \ R) (restrict X left.root) (rawLink X e left.root)
        (right.without c).root := by
  apply SetLike.ext
  intro s
  have hYX : ∀ v ∈ Y, v ∉ X := fun v hv hx =>
    Finset.disjoint_left.mp hXY hx hv
  have hXY' : ∀ v ∈ X, v ∉ Y := fun v hv hy => hYX v hy hv
  have hE : Supported Y (right.without c).root := by
    simpa [Rows.without, hright] using (right.without c).root_supported
  have hD : Supported X (restrict X left.root) := fun _ hs => hs.2
  have hL : Supported X (rawLink X e left.root) := fun _ hs => hs.1
  have hdZ : Supported (Y \ R) (delta (Y \ R)) := fun _ hs => hs
  have hdY : Supported Y (delta Y) := fun _ hs => hs
  have hdX : Supported X (delta X) := fun _ hs => hs
  have hxz : Disjoint X (Y \ R) := hXY.mono_right Finset.sdiff_subset
  -- Expanding the three joins exposes only subset/complement membership.
  -- `aesop` here closes first-order finite-set membership, not a collapse claim.
  simp only [Rows.root, transportedRows, phi, LowerSet.mem_mk,
    LowerSet.mem_sup_iff, rawJoin, restrict, rawLink, delta, Rows.without]
  constructor
  · rintro ⟨d,hs⟩
    cases d with
    | inr d =>
      right
      refine ⟨s ∩ X, Finset.inter_subset_right, s ∩ Y, ⟨d,?_⟩, ?_⟩
      · intro v hv
        have hv' := hs (Finset.mem_inter.mp hv).1
        exact Finset.mem_sdiff.mpr ⟨hright.symm ▸ (Finset.mem_inter.mp hv).2,
          (Finset.mem_sdiff.mp hv').2⟩
      · ext v
        have hsg : s ⊆ X ∪ Y := hs.trans Finset.sdiff_subset
        simp only [Finset.mem_union, Finset.mem_inter]
        exact ⟨fun hv => (Finset.mem_union.mp (hsg hv)).elim
          (fun h => Or.inl ⟨hv,h⟩) (fun h => Or.inr ⟨hv,h⟩), by tauto⟩
    | inl d =>
      left
      by_cases hed : e ∈ left.row d
      · left
        refine ⟨s ∩ X, ⟨⟨d,?_⟩, Finset.inter_subset_right⟩,
          s ∩ Y, ?_, ?_⟩
        · intro v hv
          refine Finset.mem_sdiff.mpr ⟨by
            rw [hleft]
            exact Finset.mem_insert_of_mem (Finset.mem_inter.mp hv).2, ?_⟩
          intro hq
          have hv' := (Finset.mem_sdiff.mp (hs (Finset.mem_inter.mp hv).1)).2
          apply hv'
          simp only [substitute, hed, if_pos, Finset.mem_union, Finset.mem_erase]
          exact Or.inl ⟨fun h => heX (h ▸ (Finset.mem_inter.mp hv).2),hq⟩
        · intro v hv
          refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2,?_⟩
          intro hr
          have hnot := (Finset.mem_sdiff.mp (hs (Finset.mem_inter.mp hv).1)).2
          exact hnot (by simp [substitute,hed,hr])
        · ext v
          have hsg := hs.trans Finset.sdiff_subset
          simp only [Finset.mem_union, Finset.mem_inter]
          exact ⟨fun hv => (Finset.mem_union.mp (hsg hv)).elim
            (fun h => Or.inl ⟨hv,h⟩) (fun h => Or.inr ⟨hv,h⟩),by tauto⟩
      · right
        refine ⟨s ∩ X, ⟨Finset.inter_subset_right, ⟨d,?_⟩⟩,
          s ∩ Y, Finset.inter_subset_right, ?_⟩
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact Finset.mem_sdiff.mpr ⟨by simp [hleft],hed⟩
          · have hnot := (Finset.mem_sdiff.mp (hs (Finset.mem_inter.mp hv).1)).2
            exact Finset.mem_sdiff.mpr ⟨by
              rw [hleft];exact Finset.mem_insert_of_mem (Finset.mem_inter.mp hv).2,
              by simpa [substitute,hed] using hnot⟩
        · ext v
          have hsg := hs.trans Finset.sdiff_subset
          simp only [Finset.mem_union, Finset.mem_inter]
          exact ⟨fun hv => (Finset.mem_union.mp (hsg hv)).elim
            (fun h => Or.inl ⟨hv,h⟩) (fun h => Or.inr ⟨hv,h⟩),by tauto⟩
  · rintro ((⟨a,⟨⟨d,ha⟩,haX⟩,b,hb,rfl⟩ |
      ⟨a,⟨haX,⟨d,ha⟩⟩,b,hb,rfl⟩) | ⟨a,ha,b,⟨d,hb⟩,rfl⟩)
    · by_cases hed : e ∈ left.row d
      · refine ⟨Sum.inl d,?_⟩
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · have hh := Finset.mem_sdiff.mp (ha hv)
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (haX hv),?_⟩
          simp only [substitute,hed,if_pos,Finset.mem_union,Finset.mem_erase]
          exact fun h => h.elim (fun h => hh.2 h.2)
            (fun h => hXY' v (haX hv) (hR h))
        · have hh := Finset.mem_sdiff.mp (hb hv)
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hh.1,?_⟩
          simp only [substitute,hed,if_pos,Finset.mem_union,Finset.mem_erase]
          exact fun h => h.elim (fun h => hYX v hh.1 (by
            have := left.row_supported d h.2
            rw [hleft] at this
            exact (Finset.mem_insert.mp this).resolve_left h.1)) hh.2
      · refine ⟨Sum.inl d,?_⟩
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (haX hv),by
            simpa [substitute,hed] using (Finset.mem_sdiff.mp (ha hv)).2⟩
        · refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
            (Finset.mem_sdiff.mp (hb hv)).1,?_⟩
          simp only [substitute,hed,if_neg]
          intro hq
          have := left.row_supported d hq
          rw [hleft] at this
          rcases Finset.mem_insert.mp this with rfl | hx
          · exact heY ((Finset.mem_sdiff.mp (hb hv)).1)
          · exact hYX v ((Finset.mem_sdiff.mp (hb hv)).1) hx
    · have hed : e ∉ left.row d := (Finset.mem_sdiff.mp (ha (by simp))).2
      refine ⟨Sum.inl d,?_⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (haX hv),by
          simpa [substitute,hed] using (Finset.mem_sdiff.mp
            (ha (Finset.mem_insert_of_mem hv))).2⟩
      · refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (hb hv),?_⟩
        simp only [substitute,hed,if_neg]
        intro hq
        have := left.row_supported d hq
        rw [hleft] at this
        rcases Finset.mem_insert.mp this with rfl | hx
        · exact heY (hb hv)
        · exact hYX v (hb hv) hx
    · refine ⟨Sum.inr d,?_⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (ha hv),
          fun h => hXY' v (ha hv) (hright ▸ right.row_supported d.1 h)⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
          (hright ▸ (Finset.mem_sdiff.mp (hb hv)).1),
          (Finset.mem_sdiff.mp (hb hv)).2⟩

end D5.S3.Geometry.OriginalLabelTwoSum
