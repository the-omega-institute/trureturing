/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryIntactLayers
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryIntactLayers
   mirror-E: none(waiver:intact-separated-layers)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Relative padding constructs main and core-only strips without requiring its fixed base to be a cone. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
import D5.S3.Geometry.OriginalLabelTwoSum.Compiler

/-! SOURCE_ONLY_UNCOMPILED. These are relative lists derived from smaller
factor outputs. The fixed base is NOT assumed to collapse. A final common
cone is used only after both relative core strips have actually ended.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactLayers
open OriginalLabelTwoSum HistoryLeafCap
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

def coreLayer {U : Finset V} {M : Family V} (d : Finset V) : Output U M → Family V
  | .void _ => ⊥
  | .unit _ => ⊥
  | .strong c => rawJoin (delta d) c.core

def topLayer {U : Finset V} {M : Family V} (d : Finset V) :
    Output U M → Finset (Finset V)
  | .void _ => ∅
  | .unit _ => {d}
  | .strong c => c.critical.image (fun q => d ∪ q)

def mainFaces {U : Finset V} {M : Family V} (d : Finset V) :
    Output U M → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => c.main.pairs.map (fun P => (d ∪ P.lower, d ∪ P.upper))

def stripFaces {U : Finset V} {M : Family V} (d : Finset V) :
    Output U M → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => c.separate.pairs.map (fun P => (d ∪ P.lower, d ∪ P.upper)) ++
      [(d, insert c.vertex d)]

private theorem split_union {d U s : Finset V} (hs : s ⊆ d ∪ U) :
    s = (s ∩ d) ∪ (s ∩ U) := by
  ext v
  simp only [Finset.mem_union, Finset.mem_inter]
  exact ⟨fun hv => (Finset.mem_union.mp (hs hv)).elim
    (fun h => Or.inl ⟨hv, h⟩) (fun h => Or.inr ⟨hv, h⟩), by tauto⟩

private theorem right_part {d U a q t : Finset V} (hd : Disjoint d U)
    (ha : a ⊆ d) (hq : q ⊆ U) (h : q ⊆ a ∪ t) : q ⊆ t := by
  intro v hv
  exact (Finset.mem_union.mp (h hv)).resolve_left
    (fun hva => Finset.disjoint_left.mp hd (ha hva) (hq hv))

private theorem interval_pair {d s : Finset V} {p : V}
    (hl : d ⊆ s) (hu : s ⊆ insert p d) : s = d ∨ s = insert p d := by
  by_cases hp : p ∈ s
  · exact Or.inr (Finset.Subset.antisymm hu (Finset.insert_subset hp hl))
  · left
    apply Finset.Subset.antisymm _ hl
    intro v hv
    exact (Finset.mem_insert.mp (hu hv)).resolve_left (fun he => hp (he ▸ hv))

/-- The relative output is constructed below; none of its list fields is an
input to either constructor. Its separate domain has no critical tops. -/
structure RelativeLayer (B R C : Family V) (Q : Finset (Finset V))
    (ps qs : List (Finset V × Finset V)) where
  cells : CriticalData (B ⊔ C) Q
  main : Sequence (project (B ⊔ R)) (project (endpoint (B ⊔ C) Q))
  separate : Sequence (project (B ⊔ C)) (project B)
  main_faces : orderedPairs main = ps
  separate_faces : orderedPairs separate = qs

private def strongRelative (U d : Finset V) (B M : Family V)
    (c : Certificate U M) (hd : d.Nonempty) (hdu : Disjoint d U)
    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)
    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :
    RelativeLayer B (rawJoin (delta d) M) (coreLayer d (.strong c))
      (topLayer d (.strong c)) (mainFaces d (.strong c)) (stripFaces d (.strong c)) := by
  classical
  let C := B ⊔ rawJoin (delta d) c.core
  let Q := c.critical.image (fun q => d ∪ q)
  have hpU : c.vertex ∈ U := c.core_supported {c.vertex} c.vertex_mem (by simp)
  have hpD : c.vertex ∉ d := fun h => Finset.disjoint_left.mp hdu h hpU
  have hC0 : (∅ : Finset V) ∈ c.core := c.core.lower (Finset.empty_subset _) c.vertex_mem
  have hM0 : (∅ : Finset V) ∈ M := by
    have hm : {c.vertex} ∈ M := (c.main.monotone ⟨by simp, Or.inl c.vertex_mem⟩).2
    exact M.lower (Finset.empty_subset _) hm
  have hN0 : (∅ : Finset V) ∈ endpoint c.core c.critical := Or.inl hC0
  have noBase : ∀ (N : Family V) t, t ⊆ U → d ∪ t ∈ B → t ∈ N := by
    intro N t _ ht
    exact False.elim (hmissing _ ht Finset.subset_union_left)
  let P := liftFibre M (endpoint c.core c.critical) B d U hM0 hN0 c.main hdu
    c.supported (fun z hz t ht => hboundary z hz t (c.supported t ht))
    (noBase (endpoint c.core c.critical))
  have hEnd : B ⊔ rawJoin (delta d) (endpoint c.core c.critical) = endpoint C Q := by
    apply SetLike.ext
    intro s
    constructor
    · rintro (hs | ⟨a, ha, t, ht, rfl⟩)
      · exact Or.inl (Or.inl hs)
      · rcases ht with ht | ⟨q, hq, htq⟩
        · exact Or.inl (Or.inr ⟨a, ha, t, ht, rfl⟩)
        · exact Or.inr ⟨d ∪ q, Finset.mem_image.mpr ⟨q, hq, rfl⟩,
            Finset.union_subset_union ha htq⟩
    · rintro ((hs | ⟨a, ha, t, ht, rfl⟩) | ⟨q, hq, hs⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨a, ha, t, Or.inl ht, rfl⟩
      · obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
        exact Or.inr ⟨s ∩ d, Finset.inter_subset_right, s ∩ q,
          Or.inr ⟨q, hqSource, Finset.inter_subset_right⟩, split_union hs⟩
  have hCells : CriticalData C Q := by
    constructor
    · intro q hq
      obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
      exact hd.mono Finset.subset_union_left
    · intro q hq hC
      obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
      rcases hC with hBq | ⟨a, ha, t, ht, he⟩
      · exact hmissing _ hBq Finset.subset_union_left
      · have hqt : q ⊆ t := right_part hdu ha (c.critical_supported q hqSource)
          (by rw [← he]; exact Finset.subset_union_right)
        exact c.cells.absent q hqSource (c.core.lower hqt ht)
    · intro q hq s hs
      obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
      have hqU := c.critical_supported q hqSource
      have hsDU := hs.subset.trans (Finset.union_subset_union le_rfl hqU)
      have hsplit := split_union hsDU
      by_cases hdS : d ⊆ s
      · right
        have htq : s ∩ U ⊆ q := right_part hdu le_rfl Finset.inter_subset_right
          (Finset.inter_subset_left.trans hs.subset)
        have hproper : s ∩ U ⊂ q := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨htq, ?_⟩
          intro he
          have hqs : q ⊆ s := by rw [← he]; exact Finset.inter_subset_left
          exact hs.ne (Finset.Subset.antisymm hs.subset (Finset.union_subset hdS hqs))
        exact ⟨s ∩ d, Finset.inter_subset_right, s ∩ U,
          c.cells.boundary q hqSource _ hproper, hsplit⟩
      · left
        have hproper : s ∩ d ⊂ d := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.inter_subset_right, ?_⟩
          intro he
          apply hdS
          rw [← he]
          exact Finset.inter_subset_left
        rw [hsplit]
        exact hboundary (s ∩ d) hproper (s ∩ U) Finset.inter_subset_right
    · intro q hq t ht hqt
      obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨t, htSource, rfl⟩ := Finset.mem_image.mp ht
      exact congrArg (fun s => d ∪ s) (c.cells.antichain q hqSource t htSource
        (right_part hdu le_rfl (c.critical_supported q hqSource)
          (Finset.subset_union_right.trans hqt)))
  let T := liftFibre c.core (delta {c.vertex}) B d U hC0 (by simp) c.separate hdu
    c.core_supported (fun z hz t ht => hboundary z hz t (c.core_supported t ht))
    (noBase (delta {c.vertex}))
  let H := B ⊔ rawJoin (delta d) (delta {c.vertex})
  have hUpper : insert c.vertex d ∈ H := by
    refine Or.inr ⟨d, (show d ⊆ d from le_rfl), {c.vertex},
      (show ({c.vertex} : Finset V) ⊆ {c.vertex} from le_rfl), ?_⟩
    ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  have hFree : ∀ s ∈ H, d ⊆ s → s = d ∨ s = insert c.vertex d := by
    intro s hs hds
    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
    · exact False.elim (hmissing s hs hds)
    · apply interval_pair hds
      intro v hv
      rcases Finset.mem_union.mp hv with hva | hvt
      · exact Finset.mem_insert_of_mem (ha hva)
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (ht hvt)))
  let R := emitPair H d c.vertex hd hpD hUpper hFree
  have hRetained : R.retained = project B := by
    dsimp only [R]
    rw [emitPair_retained]
    congr 1
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨hs, hn⟩
      have hnot : ¬ d ⊆ s := fun h => hn d (by simp) h
      rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
      · exact hs
      · have hproper : a ⊂ d := Finset.ssubset_iff_subset_ne.mpr ⟨ha, by
          intro he
          apply hnot
          rw [he]
          exact Finset.subset_union_left⟩
        exact hboundary a hproper t (ht.trans (Finset.singleton_subset_iff.mpr hpU))
    · intro hs
      exact ⟨Or.inl hs, by
        intro a ha h
        have he : a = d := Finset.mem_singleton.mp ha
        subst a
        exact hmissing s hs h⟩
  let Rseq : Sequence (project H) (project B) :=
    Sequence.step R ((Sequence.refl (project B)).cast hRetained.symm rfl)
  refine {
    cells := hCells
    main := P.cast rfl (congrArg project hEnd)
    separate := T.append Rseq
    main_faces := ?_
    separate_faces := ?_ }
  · change (P.cast rfl (congrArg project hEnd)).pairs.map
        (fun P => (P.lower, P.upper)) = _
    rw [Sequence.pairs_cast]
    exact liftFibre_pairs M (endpoint c.core c.critical) B d U hM0 hN0 c.main hdu
      c.supported (fun z hz t ht => hboundary z hz t (c.supported t ht))
      (noBase (endpoint c.core c.critical)) |>.trans (by rfl)
  · change (T.append Rseq).pairs.map (fun P => (P.lower, P.upper)) = _
    rw [Sequence.pairs_append, List.map_append]
    rw [liftFibre_pairs]
    simp only [Rseq, Sequence.pairs, Sequence.pairs_cast, List.map_cons, List.map_nil,
      R, emitPair, CollapsePair.upper, stripFaces]

/-- Relative padding for EVERY tag. UNIT contributes one absent pad top and
no list; VOID contributes no layer. A strong factor contributes its genuine
main and C-only lists, then the single ordinary point-layer pair. -/
def relativeLayer (U d : Finset V) (B M : Family V) (o : Output U M)
    (hd : d.Nonempty) (hdu : Disjoint d U)
    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)
    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :
    RelativeLayer B (rawJoin (delta d) M) (coreLayer d o) (topLayer d o)
      (mainFaces d o) (stripFaces d o) := by
  classical
  cases o with
  | void h =>
      subst M
      change RelativeLayer B (rawJoin (delta d) ⊥) ⊥ ∅ [] []
      have hR : B ⊔ rawJoin (delta d) (⊥ : Family V) = B := by
        rw [(rawJoin_void _).2, sup_bot_eq]
      have hE : endpoint (B ⊔ (⊥ : Family V)) ∅ = B := by
        apply SetLike.ext
        intro s
        simp [endpoint, facets]
      exact {
        cells := ⟨by simp, by simp, by simp, by simp⟩
        main := (Sequence.refl (project B)).cast (congrArg project hR).symm
          (congrArg project hE).symm
        separate := (Sequence.refl (project B)).cast (by rw [sup_bot_eq]) rfl
        main_faces := by simp [orderedPairs, orderedPair, Sequence.pairs_cast,
          Sequence.pairs, mainFaces]
        separate_faces := by simp [orderedPairs, orderedPair, Sequence.pairs_cast,
          Sequence.pairs, stripFaces] }
  | unit h =>
      subst M
      change RelativeLayer B (rawJoin (delta d) (delta ∅)) ⊥ {d} [] []
      have hR : B ⊔ rawJoin (delta d) (delta (∅ : Finset V)) =
          endpoint (B ⊔ ⊥) {d} := by
        rw [(rawJoin_unit _).2]
        apply SetLike.ext
        intro s
        simp [endpoint, facets, delta, LowerSet.mem_mk, Set.mem_setOf_eq]
      exact {
        cells := {
          nonempty := by
            intro s hs
            have he := Finset.mem_singleton.mp hs
            subst s
            exact hd
          absent := by
            intro s hs hB
            have he := Finset.mem_singleton.mp hs
            subst s
            exact hmissing d (by simpa only [sup_bot_eq] using hB) le_rfl
          boundary := by
            intro s hs t ht
            have he := Finset.mem_singleton.mp hs
            subst s
            change t ∈ B ⊔ (⊥ : Family V)
            rw [sup_bot_eq]
            simpa only [Finset.union_empty] using
              (hboundary t ht ∅ (Finset.empty_subset U))
          antichain := by
            intro s hs t ht _
            exact (Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm }

        main := (Sequence.refl _).cast rfl (congrArg project hR)
        separate := (Sequence.refl (project B)).cast (by rw [sup_bot_eq]) rfl
        main_faces := by simp [orderedPairs, orderedPair, Sequence.pairs_cast,
          Sequence.pairs, mainFaces]
        separate_faces := by simp [orderedPairs, orderedPair, Sequence.pairs_cast,
          Sequence.pairs, stripFaces] }
  | strong c => exact strongRelative U d B M c hd hdu hmissing hboundary

/-- Both the recovered core and every retained top stay inside the actual
pad over the declared factor ground. This includes every ghost in U. -/
theorem layer_bound (U d : Finset V) (M : Family V) (o : Output U M) :
    coreLayer d o ⊔ facets (topLayer d o) ≤ rawJoin (delta d) (delta U) := by
  cases o with
  | void h =>
      rintro s (hs | ⟨q, hq, _⟩)
      · exact hs.elim
      · simp [topLayer] at hq
  | unit h =>
      rintro s (hs | ⟨q, hq, hsq⟩)
      · exact hs.elim
      · have he := Finset.mem_singleton.mp hq
        subst q
        exact ⟨s, hsq, ∅, Finset.empty_subset _, by simp⟩
  | strong c =>
      rintro s (⟨a, ha, t, ht, rfl⟩ | ⟨q, hq, hsq⟩)
      · exact ⟨a, ha, t, c.core_supported t ht, rfl⟩
      · obtain ⟨q, hqSource, rfl⟩ := Finset.mem_image.mp hq
        exact ⟨s ∩ d, Finset.inter_subset_right, s ∩ U, Finset.inter_subset_right,
          split_union (hsq.trans (Finset.union_subset_union le_rfl
            (c.critical_supported q hqSource)))⟩

private theorem facets_union (Q R : Finset (Finset V)) :
    facets (Q ∪ R) = facets Q ⊔ facets R := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨q, hq, hs⟩
    exact (Finset.mem_union.mp hq).elim
      (fun h => Or.inl ⟨q, h, hs⟩) (fun h => Or.inr ⟨q, h, hs⟩)
  · rintro (⟨q, hq, hs⟩ | ⟨q, hq, hs⟩)
    · exact ⟨q, Finset.mem_union_left _ hq, hs⟩
    · exact ⟨q, Finset.mem_union_right _ hq, hs⟩

/-- Absolute one-layer output, obtained by the relative strip followed by
the genuine fixed-base cone. Both ordered readbacks are part of this result. -/
def oneLayer (W U d : Finset V) (B M : Family V) (o : Output U M) (x : V)
    (hM : Supported U M) (hd : d.Nonempty) (hdu : Disjoint d U)
    (hW : d ∪ U ⊆ W) (hB : Supported W B) (hx : ({x} : Finset V) ∈ B)
    (hcone : ∀ s ∈ B, insert x s ∈ B)
    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)
    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :
    {c : Certificate W (B ⊔ rawJoin (delta d) M) //
      orderedPairs c.main = mainFaces d o ∧
      orderedPairs c.separate = stripFaces d o ++
        (fibres ((W.erase x).powerset.filter (fun s => s.Nonempty ∧ s ∈ B))).map
          (fun s => (s, insert x s))} := by
  let T := relativeLayer U d B M o hd hdu hmissing hboundary
  have hb := layer_bound U d M o
  have padSupport : Supported W (rawJoin (delta d) (delta U)) := by
    rintro s ⟨a, ha, t, ht, rfl⟩
    exact (Finset.union_subset_union ha ht).trans hW
  let c : Certificate W (B ⊔ rawJoin (delta d) M) := {
    supported := by
      rintro s (hs | ⟨a, ha, t, ht, rfl⟩)
      · exact hB s hs
      · exact (Finset.union_subset_union ha (hM t ht)).trans hW
    core := B ⊔ coreLayer d o
    critical := topLayer d o
    vertex := x
    vertex_mem := Or.inl hx
    core_supported := by
      rintro s (hs | hs)
      · exact hB s hs
      · exact padSupport s (hb (Or.inl hs))
    critical_supported := by
      intro q hq
      exact padSupport q (hb (Or.inr ⟨q, hq, le_rfl⟩))
    cells := T.cells
    main := T.main
    separate := T.separate.append (collapseCone W B x hB hx hcone) }
  refine ⟨c, T.main_faces, ?_⟩
  change orderedPairs (T.separate.append (collapseCone W B x hB hx hcone)) = _
  rw [orderedPairs_append, T.separate_faces, collapseCone_orderedPairs]

/-- Two independent padded layers. The cross hypotheses are literal absence
from the OTHER full pad over its original ground; no output or collapse of
that enlarged base is assumed. Main order is factor one then factor two.
The separate order is core one, core two, and only then the common cone.
The subtype exposes both complete global lists of the returned certificate. -/
def twoLayers (W : Finset V) (B : Family V) (x : V)
    (U d : Finset V) (M : Family V) (o : Output U M)
    (U' d' : Finset V) (M' : Family V) (o' : Output U' M')
    (hM : Supported U M) (hM' : Supported U' M')
    (hd : d.Nonempty) (hd' : d'.Nonempty)
    (hdu : Disjoint d U) (hdu' : Disjoint d' U')
    (hW : d ∪ U ⊆ W) (hW' : d' ∪ U' ⊆ W)
    (hB : Supported W B) (hx : ({x} : Finset V) ∈ B)
    (hcone : ∀ s ∈ B, insert x s ∈ B)
    (hmissing : ∀ s ∈ B ⊔ rawJoin (delta d') (delta U'), ¬ d ⊆ s)
    (hmissing' : ∀ s ∈ B ⊔ rawJoin (delta d) (delta U), ¬ d' ⊆ s)
    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B)
    (hboundary' : ∀ z ⊂ d', ∀ t ⊆ U', z ∪ t ∈ B) :
    {c : Certificate W ((B ⊔ rawJoin (delta d) M) ⊔ rawJoin (delta d') M') //
      orderedPairs c.main = mainFaces d o ++ mainFaces d' o' ∧
      orderedPairs c.separate = stripFaces d o ++ stripFaces d' o' ++
        (fibres ((W.erase x).powerset.filter (fun s => s.Nonempty ∧ s ∈ B))).map
          (fun s => (s, insert x s))} := by
  classical
  let A := coreLayer d o
  let A' := coreLayer d' o'
  let Q := topLayer d o
  let Q' := topLayer d' o'
  let R := rawJoin (delta d) M
  let R' := rawJoin (delta d') M'
  let C := (B ⊔ A) ⊔ A'
  have hA : A ⊔ facets Q ≤ rawJoin (delta d) (delta U) := layer_bound U d M o
  have hA' : A' ⊔ facets Q' ≤ rawJoin (delta d') (delta U') := layer_bound U' d' M' o'
  have hAc : A ≤ rawJoin (delta d) (delta U) := fun _ hs => hA (Or.inl hs)
  have hAc' : A' ≤ rawJoin (delta d') (delta U') := fun _ hs => hA' (Or.inl hs)
  have hR : R ≤ rawJoin (delta d) (delta U) := by
    rintro s ⟨a, ha, t, ht, rfl⟩
    exact ⟨a, ha, t, hM t ht, rfl⟩
  have hR' : R' ≤ rawJoin (delta d') (delta U') := by
    rintro s ⟨a, ha, t, ht, rfl⟩
    exact ⟨a, ha, t, hM' t ht, rfl⟩
  have miss {H : Family V} (hH : H ≤ B ⊔ rawJoin (delta d') (delta U')) :
      ∀ s ∈ H, ¬ d ⊆ s := fun s hs => hmissing s (hH hs)
  have miss' {H : Family V} (hH : H ≤ B ⊔ rawJoin (delta d) (delta U)) :
      ∀ s ∈ H, ¬ d' ⊆ s := fun s hs => hmissing' s (hH hs)
  have bd {H : Family V} (hBH : B ≤ H) :
      ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ H :=
    fun z hz t ht => hBH (hboundary z hz t ht)
  have bd' {H : Family V} (hBH : B ≤ H) :
      ∀ z ⊂ d', ∀ t ⊆ U', z ∪ t ∈ H :=
    fun z hz t ht => hBH (hboundary' z hz t ht)
  let P := relativeLayer U d (B ⊔ R') M o hd hdu
    (miss (sup_le le_sup_left (hR'.trans le_sup_right))) (bd le_sup_left)
  let P' := relativeLayer U' d' ((B ⊔ A) ⊔ facets Q) M' o' hd' hdu'
    (miss' (by
      rintro s ((hs | hs) | hs)
      · exact Or.inl hs
      · exact Or.inr (hA (Or.inl hs))
      · exact Or.inr (hA (Or.inr hs))))
    (bd' (le_sup_left.trans le_sup_left))
  let T := relativeLayer U d (B ⊔ A') M o hd hdu
    (miss (sup_le le_sup_left (hAc'.trans le_sup_right)))
    (bd le_sup_left)
  let T' := relativeLayer U' d' (B ⊔ A) M' o' hd' hdu'
    (miss' (sup_le le_sup_left (hAc.trans le_sup_right)))
    (bd' le_sup_left)
  let Tbase := relativeLayer U' d' B M' o' hd' hdu'
    (miss' le_sup_left) (bd' le_rfl)
  have hSC : (B ⊔ A') ⊔ A = C := by dsimp [C]; ac_rfl
  have hCells : CriticalData C (Q ∪ Q') := by
    have hc : CriticalData C Q := by
      have hh : CriticalData ((B ⊔ A') ⊔ A) Q := T.cells
      rw [hSC] at hh
      exact hh
    have hc' : CriticalData C Q' := T'.cells
    constructor
    · intro q hq
      exact (Finset.mem_union.mp hq).elim (hc.nonempty q) (hc'.nonempty q)
    · intro q hq hqC
      exact (Finset.mem_union.mp hq).elim
        (fun h => hc.absent q h hqC) (fun h => hc'.absent q h hqC)
    · intro q hq s hs
      exact (Finset.mem_union.mp hq).elim
        (fun h => hc.boundary q h s hs) (fun h => hc'.boundary q h s hs)
    · intro q hq r hr hqr
      by_contra hne
      have hp : q ⊂ r := Finset.ssubset_iff_subset_ne.mpr ⟨hqr, hne⟩
      have hqC : q ∈ C := (Finset.mem_union.mp hr).elim
        (fun h => hc.boundary r h q hp) (fun h => hc'.boundary r h q hp)
      exact (Finset.mem_union.mp hq).elim
        (fun h => hc.absent q h hqC) (fun h => hc'.absent q h hqC)
  have hPsource : (B ⊔ R') ⊔ R = (B ⊔ R) ⊔ R' := by ac_rfl
  have hPtarget : endpoint ((B ⊔ R') ⊔ A) Q = ((B ⊔ A) ⊔ facets Q) ⊔ R' := by
    dsimp [endpoint]
    ac_rfl
  have hP'target : endpoint (((B ⊔ A) ⊔ facets Q) ⊔ A') Q' =
      endpoint C (Q ∪ Q') := by
    dsimp [endpoint, C]
    rw [facets_union]
    ac_rfl
  have padSupport {a T : Finset V} (haT : a ∪ T ⊆ W) :
      Supported W (rawJoin (delta a) (delta T)) := by
    rintro s ⟨b, hb, t, ht, rfl⟩
    exact (Finset.union_subset_union hb ht).trans haT
  have hCS : Supported W C := by
    rintro s ((hs | hs) | hs)
    · exact hB s hs
    · exact padSupport hW s (hA (Or.inl hs))
    · exact padSupport hW' s (hA' (Or.inl hs))
  let main := (P.main.cast (congrArg project hPsource)
    (congrArg project hPtarget)).append (P'.main.cast rfl (congrArg project hP'target))
  let separate := (T.separate.cast (congrArg project hSC) rfl).append
    (Tbase.separate.append (collapseCone W B x hB hx hcone))
  let c : Certificate W ((B ⊔ R) ⊔ R') := {
    supported := by
      rintro s ((hs | hs) | hs)
      · exact hB s hs
      · exact padSupport hW s (hR hs)
      · exact padSupport hW' s (hR' hs)
    core := C
    critical := Q ∪ Q'
    vertex := x
    vertex_mem := Or.inl (Or.inl hx)
    core_supported := hCS
    critical_supported := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact padSupport hW q (hA (Or.inr ⟨q, hq, le_rfl⟩))
      · exact padSupport hW' q (hA' (Or.inr ⟨q, hq, le_rfl⟩))
    cells := hCells
    main := main
    separate := separate }
  refine ⟨c, ?_, ?_⟩
  · change main.pairs.map (fun P => (P.lower, P.upper)) = _
    rw [Sequence.pairs_append, List.map_append, Sequence.pairs_cast,
      Sequence.pairs_cast]
    exact congrArg₂ List.append P.main_faces P'.main_faces
  · change separate.pairs.map (fun P => (P.lower, P.upper)) = _
    simp only [separate, Sequence.pairs_append, List.map_append, Sequence.pairs_cast]
    change orderedPairs T.separate ++
      (orderedPairs Tbase.separate ++ orderedPairs (collapseCone W B x hB hx hcone)) = _
    rw [T.separate_faces, Tbase.separate_faces, collapseCone_orderedPairs]
    exact (List.append_assoc _ _ _).symm

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactLayers

