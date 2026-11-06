/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryIntact
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryIntact
   mirror-E: none(waiver:physical-history-intact-terminal)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Original-coordinate intact terminals, exact excluded-residue normalizations and actual relative product lists. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactProduct
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactLayers
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Consumer

/-! SOURCE_ONLY_UNCOMPILED. The canonical predecessor below is preserved.
Its empty-X terminal is extended to arbitrary original-coordinate embeddings.
For nonempty X all three residues use actual native constructors and the
excluded-residue normalizations have globally expanded pair lists. The
public intactOutput below has the intended local predecessor telescope.
No elaboration, kernel acceptance or physical-history induction is claimed.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance historyIntactPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
open OriginalLabelTwoSum AllMWheel HistoryLeafCap HistoryIsolated HistoryCycles

private theorem parent_void (m : Nat) (hm : 3 ≤ m) :
    parentOf ∅ (ground m) (tailGround m hm) 0 (pathRoot m hm) ⊥ = pathRoot m hm := by
  have hD : restrict (∅ : Finset (Label m)) (⊥ : Family (Label m)) = ⊥ := by
    simp [restrict]
  have hL : rawLink ∅ (0 : Label m) ⊥ = ⊥ := by
    apply SetLike.ext
    intro s
    simp [rawLink]
  simp only [parentOf, phi, hD, hL, (rawJoin_void _).1, bot_sup_eq,
    (rawJoin_unit _).1]

private theorem parent_unit (m : Nat) (hm : 3 ≤ m) :
    parentOf ∅ (ground m) (tailGround m hm) 0 (pathRoot m hm) (delta ∅) = A1 m hm := by
  have hD : restrict (∅ : Finset (Label m)) (delta ∅) = delta ∅ := by
    simp [restrict]
  have hL : rawLink ∅ (0 : Label m) (delta ∅) = ⊥ := by
    apply SetLike.ext
    intro s
    simp [rawLink]
  simp only [parentOf, phi, hD, hL, (rawJoin_unit _).1, (rawJoin_void _).1,
    sup_bot_eq, bot_sup_eq, A1, sup_comm]

private theorem parent_point (m : Nat) (hm : 3 ≤ m) :
    parentOf ∅ (ground m) (tailGround m hm) 0 (pathRoot m hm) (delta {0}) = delta (ground m) := by
  have hD : restrict (∅ : Finset (Label m)) (delta {0}) = delta ∅ := by
    apply SetLike.ext
    intro s
    simp [restrict, delta, Finset.subset_empty]
  have hL : rawLink ∅ (0 : Label m) (delta {0}) = delta ∅ := by
    apply SetLike.ext
    intro s
    change (s ⊆ ∅ ∧ insert 0 s ⊆ {0}) ↔ s ⊆ ∅
    constructor
    · exact And.left
    · intro hs
      exact ⟨hs, Finset.insert_subset (by simp) (hs.trans (Finset.empty_subset _))⟩
  have hZY : delta (tailGround m hm) ≤ delta (ground m) :=
    fun s hs => hs.trans Finset.sdiff_subset
  have hEY : pathRoot m hm ≤ delta (ground m) :=
    ((rimRows m (by omega)).without (interfaceRow m hm)).root_supported
  simp only [parentOf, phi, hD, hL, (rawJoin_unit _).1,
    sup_eq_right.mpr hZY, sup_eq_left.mpr hEY]

/-- Actual empty-X intact output at every width, without a supplied J output
or desired final certificate. All three raw earlier families are classified;
VOID/UNIT are not confused by projecting to their nonempty faces. -/
def emptyOldIntactOutput (m : Nat) (hm : 3 ≤ m) (J : Family (Label m))
    (hJ : Supported ({0} : Finset (Label m)) J) :
    Output (ground m) (parentOf ∅ (ground m) (tailGround m hm) 0 (pathRoot m hm) J) := by
  classical
  by_cases hp : ({0} : Finset (Label m)) ∈ J
  · have hPoint : J = delta {0} := by
      apply SetLike.ext
      intro s
      exact ⟨hJ s, fun hs => J.lower hs hp⟩
    exact changeOutput (simplexOutput (ground m))
      ((parent_point m hm).symm.trans (congrArg (parentOf ∅ (ground m)
        (tailGround m hm) 0 (pathRoot m hm)) hPoint).symm)
  · by_cases h0 : (∅ : Finset (Label m)) ∈ J
    · have hUnit : J = delta ∅ := by
        apply SetLike.ext
        intro s
        constructor
        · intro hs
          have he : s = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro v hv
            have hv0 : v = 0 := Finset.mem_singleton.mp (hJ s hs hv)
            exact hp (J.lower (Finset.singleton_subset_iff.mpr (hv0 ▸ hv)) hs)
          exact (mem_delta _ _).mpr (by simpa only [he] using Finset.empty_subset (∅ : Finset (Label m)))
        · intro hs
          exact J.lower hs h0
      exact changeOutput (.strong (cycleCertificate m hm))
        ((parent_unit m hm).symm.trans (congrArg (parentOf ∅ (ground m)
          (tailGround m hm) 0 (pathRoot m hm)) hUnit).symm)
    · have hVoid : J = ⊥ := by
        apply SetLike.ext
        intro s
        exact ⟨fun hs => (h0 (J.lower (Finset.empty_subset _) hs)).elim,
          fun hs => hs.elim⟩
      exact changeOutput (.strong (pathRootCertificate m hm))
        ((parent_void m hm).symm.trans (congrArg (parentOf ∅ (ground m)
          (tailGround m hm) 0 (pathRoot m hm)) hVoid).symm)

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open HistoryIntactProduct
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual ordinary main pairs, with no fictional pair for either tag. -/
def mainPairsOf {W : Finset V} {K : Family V} : Output W K → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => orderedPairs c.main

/-- Actual C-ALONE pairs, again keeping VOID and UNIT distinct as tags. -/
def corePairsOf {W : Finset V} {K : Family V} : Output W K → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => orderedPairs c.separate

@[simp] theorem changeOutput_mainPairsOf {W : Finset V} {K L : Family V}
    (o : Output W K) (h : K = L) : mainPairsOf (changeOutput o h) = mainPairsOf o := by
  subst L
  rfl

@[simp] theorem changeOutput_corePairsOf {W : Finset V} {K L : Family V}
    (o : Output W K) (h : K = L) : corePairsOf (changeOutput o h) = corePairsOf o := by
  subst L
  rfl

private theorem join_comm (K L : Family V) : rawJoin K L = rawJoin L K := by
  apply SetLike.ext
  intro s
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;>
    exact ⟨b, hb, a, ha, Finset.union_comm _ _⟩

private theorem join_mono {K L M N : Family V} (hKL : K ≤ L) (hMN : M ≤ N) :
    rawJoin K M ≤ rawJoin L N := by
  rintro s ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hKL ha, b, hMN hb, rfl⟩

private theorem join_sup (K L M : Family V) :
    rawJoin K (L ⊔ M) = rawJoin K L ⊔ rawJoin K M := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨a, ha, b, hb | hb, rfl⟩
    · exact Or.inl ⟨a, ha, b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact ⟨a, ha, b, Or.inl hb, rfl⟩
    · exact ⟨a, ha, b, Or.inr hb, rfl⟩

private theorem facets_single (d : Finset V) : facets {d} = delta d := by
  apply SetLike.ext
  intro s
  simp [facets]

private theorem rename_support {U : Type*} [Fintype U] [DecidableEq U]
    (f : U ↪ V) {W : Finset U} {K : Family U} (h : Supported W K) :
    Supported (W.image f) (renameFamily f K) := by
  rintro s ⟨t, ht, rfl⟩
  exact Finset.image_subset_image (h t ht)

private theorem tail_subset (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    (tailGround m hm).image f ⊆ (ground m).image f :=
  Finset.image_subset_image Finset.sdiff_subset

private theorem local_support (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    Supported ((ground m).image f) (renameFamily f (pathRoot m hm)) :=
  rename_support f (((rimRows m (by omega)).without (interfaceRow m hm)).root_supported)

private theorem local_empty (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    (∅ : Finset V) ∈ renameFamily f (pathRoot m hm) :=
  ⟨∅, (pathFilling m hm).empty_mem, by simp⟩

private theorem base_support (X Y : Finset V) (E : Family V)
    (hE : Supported Y E) : Supported (X ∪ Y) (rawJoin (delta X) E) := by
  rintro s ⟨a, ha, b, hb, rfl⟩
  exact Finset.union_subset_union ha (hE b hb)

private theorem base_vertex (X : Finset V) (E : Family V) (x : V)
    (hx : x ∈ X) (hE0 : (∅ : Finset V) ∈ E) :
    ({x} : Finset V) ∈ rawJoin (delta X) E :=
  ⟨{x}, Finset.singleton_subset_iff.mpr hx, ∅, hE0, by simp⟩

private theorem base_cone (X : Finset V) (E : Family V) (x : V) (hx : x ∈ X) :
    ∀ s ∈ rawJoin (delta X) E, insert x s ∈ rawJoin (delta X) E := by
  rintro s ⟨a, ha, b, hb, rfl⟩
  exact ⟨insert x a, Finset.insert_subset hx ha, b, hb, by simp⟩

private theorem local_part {X Y a t u v : Finset V} (hXY : Disjoint X Y)
    (ht : t ⊆ Y) (hu : u ⊆ X) (h : a ∪ t ⊆ u ∪ v) : t ⊆ v := by
  intro w hw
  exact (Finset.mem_union.mp (h (Finset.mem_union_right _ hw))).resolve_left
    (fun hwu => Finset.disjoint_left.mp hXY (hu hwu) (ht hw))

private theorem old_part {X Y a t u v : Finset V} (hXY : Disjoint X Y)
    (ha : a ⊆ X) (hv : v ⊆ Y) (h : a ∪ t ⊆ u ∪ v) : a ⊆ u := by
  intro w hw
  exact (Finset.mem_union.mp (h (Finset.mem_union_left _ hw))).resolve_right
    (fun hwv => Finset.disjoint_left.mp hXY (ha hw) (hv hwv))

private theorem base_local {X Y : Finset V} {E : Family V} (hXY : Disjoint X Y)
    {a t : Finset V} (ht : t ⊆ Y) (h : a ∪ t ∈ rawJoin (delta X) E) : t ∈ E := by
  obtain ⟨u, hu, v, hv, he⟩ := h
  exact E.lower (local_part hXY ht hu (by rw [← he])) hv

private theorem parent_supported (X Y Z : Finset V) (e : V) (E J : Family V)
    (hZ : Z ⊆ Y) (hE : Supported Y E) :
    Supported (X ∪ Y) (parentOf X Y Z e E J) := by
  rintro s ((⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩) | ⟨a, ha, b, hb, rfl⟩)
  · exact Finset.union_subset_union ha.2 (hb.trans hZ)
  · exact Finset.union_subset_union ha.1 hb
  · exact Finset.union_subset_union ha (hE b hb)

private theorem parent_void_general (X Y Z : Finset V) (e : V) (E : Family V) :
    parentOf X Y Z e E ⊥ = rawJoin (delta X) E := by
  have hl : rawLink X e (⊥ : Family V) = ⊥ := by
    apply SetLike.ext
    intro s
    simp [rawLink]
  simp [parentOf, phi, restrict, hl, rawJoin_void]

private theorem parent_unit_general (X Y Z : Finset V) (e : V) (E : Family V) :
    parentOf X Y Z e E (delta ∅) = rawJoin (delta X) E ⊔ delta Z := by
  have hd : restrict X (delta (∅ : Finset V)) = delta ∅ := by
    apply SetLike.ext
    intro s
    change (s ⊆ ∅ ∧ s ⊆ X) ↔ s ⊆ ∅
    exact ⟨And.left, fun hs => ⟨hs, hs.trans (Finset.empty_subset _)⟩⟩
  have hl : rawLink X e (delta (∅ : Finset V)) = ⊥ := by
    apply SetLike.ext
    intro s
    simp [rawLink]
  simp only [parentOf, phi, hd, hl, (rawJoin_unit _).1,
    (rawJoin_void _).1, sup_bot_eq, bot_sup_eq, sup_comm]

private def retargetFilling {W : Finset V} {A B : Family V}
    (g : Filling W A) (h : A = B) : Filling W B where
  empty_mem := h ▸ g.empty_mem
  collar := g.collar
  critical := g.critical
  contains := by rw [← h]; exact g.contains
  supported := g.supported
  critical_supported := g.critical_supported
  cells := g.cells
  main := g.main
  separate := g.separate.cast rfl (congrArg project h)

private theorem zero_interface (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    renameFamily f (A0 m hm) =
      renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f) := by
  change renameFamily f (pathRoot m hm ⊓ delta (tailGround m hm)) = _
  rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
    (delta (tailGround m hm)) ∅).2.2.1,
    (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]

private def zeroFilling (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    Filling ((tailGround m hm).image f)
      (renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f)) :=
  retargetFilling (renameFilling f (fill0 m hm)) (zero_interface m hm f)

/-- All empty-old-ground inputs on arbitrary original coordinates. The
ambient V may contain arbitrary ghosts outside the wheel image. No inverse
embedding of J and no choice of a point in empty X is used. -/
def emptyOldEmbeddedIntactOutput (m : Nat) (hm : 3 ≤ m) (e : V)
    (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (hJ : Supported ({e} : Finset V) J) :
    Output ((ground m).image f)
      (parentOf ∅ ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hEY : E ≤ delta Y := local_support m hm f
  have hP : parentOf ∅ Y Z e E (delta {e}) = delta Y := by
    have hd : restrict (∅ : Finset V) (delta {e}) = delta ∅ := by
      apply SetLike.ext
      intro s
      simp [restrict, delta, Finset.subset_empty]
    have hl : rawLink (∅ : Finset V) e (delta {e}) = delta ∅ := by
      apply SetLike.ext
      intro s
      change (s ⊆ ∅ ∧ insert e s ⊆ {e}) ↔ s ⊆ ∅
      constructor
      · exact And.left
      · intro hs
        exact ⟨hs, Finset.insert_subset (by simp) (hs.trans (Finset.empty_subset _))⟩
    have hZZ : delta Z ≤ delta Y := fun _ h => h.trans hZY
    simp only [parentOf, phi, hd, hl, (rawJoin_unit _).1,
      sup_eq_right.mpr hZZ, sup_eq_left.mpr hEY]
  by_cases hp : ({e} : Finset V) ∈ J
  · have he : J = delta {e} := by
      apply SetLike.ext
      intro s
      exact ⟨hJ s, fun hs => J.lower hs hp⟩
    exact changeOutput (simplexOutput Y) (by rw [he, hP])
  · by_cases h0 : (∅ : Finset V) ∈ J
    · have he : J = delta ∅ := by
        apply SetLike.ext
        intro s
        constructor
        · intro hs
          have hs0 : s = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro v hv
            have hve : v = e := Finset.mem_singleton.mp (hJ s hs hv)
            exact hp (J.lower (Finset.singleton_subset_iff.mpr (hve ▸ hv)) hs)
          exact (mem_delta _ _).mpr (by simpa only [hs0] using Finset.empty_subset (∅ : Finset V))
        · intro hs
          exact J.lower hs h0
      have hh : renameFamily f (A1 m hm) = E ⊔ delta Z := by
        change renameFamily f (pathRoot m hm ⊔ delta (tailGround m hm)) = _
        rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
          (delta (tailGround m hm)) ∅).2.1,
          (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]
      exact changeOutput (.strong (renameCertificate f (cycleCertificate m hm))) (by
        rw [he, parent_unit_general, (rawJoin_unit _).1]
        exact hh)
    · have he : J = ⊥ := by
        apply SetLike.ext
        intro s
        exact ⟨fun hs => (h0 (J.lower (Finset.empty_subset _) hs)).elim,
          fun hs => hs.elim⟩
      exact changeOutput (.strong (renameCertificate f (pathRootCertificate m hm))) (by
        rw [he, parent_void_general, (rawJoin_unit _).1])

private theorem local_in_base (X : Finset V) (E : Family V) :
    E ≤ rawJoin (delta X) E := by
  intro s hs
  exact ⟨∅, Finset.empty_subset _, s, hs, by simp⟩

/-- Full readbacks for the three ACTUAL embedded empty-X inputs. The point
case uses the very same finite simplex choice, on the wheel image, as the
selected simplexOutput. It never selects a point in empty X. The cycle and
path cases expose the literal injective images of BOTH original native lists.
-/
theorem emptyOldEmbedded_lists (m : Nat) (hm : 3 ≤ m) (e : V) (J : Family V)
    (f : Label m ↪ V) (hf0 : f 0 = e) (hJ : Supported ({e} : Finset V) J) :
    let hn : ((ground m).image f).Nonempty :=
      Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff]⟩
    (({e} : Finset V) ∈ J →
      mainPairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) = [] ∧
      corePairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) =
        (fibres ((((ground m).image f).erase hn.choose).powerset.filter
          (fun s => s.Nonempty ∧ s ⊆ (ground m).image f))).map
          (fun s => (s, insert hn.choose s))) ∧
    (({e} : Finset V) ∉ J → (∅ : Finset V) ∈ J →
      mainPairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) =
        (cycleCertificate m hm).main.pairs.map (fun P => (P.lower.image f, P.upper.image f)) ∧
      corePairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) =
        (cycleCertificate m hm).separate.pairs.map (fun P => (P.lower.image f, P.upper.image f))) ∧
    (({e} : Finset V) ∉ J → (∅ : Finset V) ∉ J →
      mainPairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) =
        (pathRootCertificate m hm).main.pairs.map (fun P => (P.lower.image f, P.upper.image f)) ∧
      corePairsOf (emptyOldEmbeddedIntactOutput m hm e J f hf0 hJ) =
        (pathRootCertificate m hm).separate.pairs.map (fun P => (P.lower.image f, P.upper.image f))) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    have hn : ((ground m).image f).Nonempty :=
      Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff]⟩
    constructor
    · simp only [emptyOldEmbeddedIntactOutput, dif_pos hp, changeOutput_mainPairsOf]
      simp only [simplexOutput, dif_pos hn, mainPairsOf, coneCertificate, orderedPairs, orderedPair,
        Sequence.pairs_cast, Sequence.pairs, List.map_nil]
    · simp only [emptyOldEmbeddedIntactOutput, dif_pos hp, changeOutput_corePairsOf]
      simp only [simplexOutput, dif_pos hn, corePairsOf, coneCertificate]
      simpa only [mem_delta] using collapseCone_orderedPairs ((ground m).image f)
        (delta ((ground m).image f)) hn.choose (fun _ h => h)
        (Finset.singleton_subset_iff.mpr hn.choose_spec)
        (fun s hs => Finset.insert_subset hn.choose_spec hs)
  · intro hp h0
    simp only [emptyOldEmbeddedIntactOutput, dif_neg hp, dif_pos h0,
      changeOutput_mainPairsOf, changeOutput_corePairsOf]
    simp only [mainPairsOf, corePairsOf, renameCertificate, orderedPairs, Sequence.pairs_cast]
    unfold orderedPair
    simp only [renameSequence_pairs, and_self]
  · intro hp h0
    simp only [emptyOldEmbeddedIntactOutput, dif_neg hp, dif_neg h0,
      changeOutput_mainPairsOf, changeOutput_corePairsOf]
    simp only [mainPairsOf, corePairsOf, renameCertificate, orderedPairs, Sequence.pairs_cast]
    unfold orderedPair
    simp only [renameSequence_pairs, and_self]

private theorem zero_collar (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    (zeroFilling m hm f).collar =
      renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f) :=
  zero_interface m hm f

private theorem zero_tops (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    (zeroFilling m hm f).critical =
      if m % 3 = 2 then ∅ else {(eta0 m hm).image f} := by
  change (fill0 m hm).critical.image (fun s => s.image f) = _
  rw [fill0_critical]
  split_ifs <;> simp

private def replaceCertificate {W : Finset V} {K L : Family V}
    (c : Certificate W K) (h : K = L) : Certificate W L where
  supported := h ▸ c.supported
  core := c.core
  critical := c.critical
  vertex := c.vertex
  vertex_mem := c.vertex_mem
  core_supported := c.core_supported
  critical_supported := c.critical_supported
  cells := c.cells
  main := c.main.cast (congrArg project h) rfl
  separate := c.separate

/-- UNIT old family, in either residue admitting eta. The actual zero filling
runs inside Delta(Z), fixing the entire original base. Its endpoint is the
base plus the ONE eta top, whose boundary and absence are recovered from the
actual filling; the separate list is the genuine base cone list. -/
def unitIntactCertificate (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2)
    (X : Finset V) (e : V) (f : Label m ↪ V) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f)) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) (delta ∅)) := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let d := (eta0 m hm).image f
  let g := zeroFilling m hm f
  let N := (E ⊓ delta Z) ⊔ delta d
  let x := hX.choose
  have hx : x ∈ X := hX.choose_spec
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hgC : g.collar = E ⊓ delta Z := zero_collar m hm f
  have hgQ : g.critical = {d} := by rw [zero_tops, if_neg hr]
  have hdCells : CriticalData (E ⊓ delta Z) {d} := by
    rw [← hgC, ← hgQ]
    exact g.cells
  have hdZ : d ⊆ Z := g.critical_supported d (by rw [hgQ]; simp)
  have hd : d.Nonempty := hdCells.nonempty d (by simp)
  have hdE : d ∉ E := fun he => hdCells.absent d (by simp) ⟨he, hdZ⟩
  let S : Sequence (project (delta Z)) (project N) :=
    g.main.cast rfl (by rw [hgC, hgQ, endpoint, facets_single])
  let T := relativeProduct ∅ Z (delta ∅) ⊥ B (delta Z) N
    (by simp) (fun _ hs => hs)
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl g.empty_mem) (fun _ hs => hs) S (by
      intro a ha _ t ht hB
      have hae : a = ∅ := Finset.subset_empty.mp ha
      exact Or.inl ⟨base_local hXY (ht.trans hZY) hB, ht⟩)
  have hN : B ⊔ rawJoin (delta ∅) N = B ⊔ delta d := by
    rw [(rawJoin_unit N).1]
    have ha : E ⊓ delta Z ≤ B := fun s hs => local_in_base X E hs.1
    exact sup_assoc B (E ⊓ delta Z) (delta d) |>.symm.trans
      (congrArg (fun A => A ⊔ delta d) (sup_eq_left.mpr ha))
  have hEnd : B ⊔ delta d = endpoint B {d} := by rw [endpoint, facets_single]
  exact {
    supported := parent_supported X Y Z e E (delta ∅) hZY (local_support m hm f)
    core := B
    critical := {d}
    vertex := x
    vertex_mem := base_vertex X E x hx (local_empty m hm f)
    core_supported := base_support X Y E (local_support m hm f)
    critical_supported := by
      intro s hs
      have he := Finset.mem_singleton.mp hs
      subst s
      exact (hdZ.trans hZY).trans Finset.subset_union_right
    cells := {
      nonempty := by intro s hs; have he := Finset.mem_singleton.mp hs
                     subst s; exact hd
      absent := by
        intro s hs hsB
        have he := Finset.mem_singleton.mp hs
        subst s
        exact hdE (base_local (a := ∅) hXY (hdZ.trans hZY)
          (by simpa only [Finset.empty_union] using hsB))
      boundary := by
        intro s hs t ht
        have he := Finset.mem_singleton.mp hs
        subst s
        exact local_in_base X E (hdCells.boundary d (by simp) t ht).1
      antichain := by intro s hs t ht _; exact
        (Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm }
    main := T.1.cast (by rw [(rawJoin_unit (delta Z)).1, parent_unit_general])
      (congrArg project (hN.trans hEnd))
    separate := collapseCone (X ∪ Y) B x (base_support X Y E (local_support m hm f))
      (base_vertex X E x hx (local_empty m hm f)) (base_cone X E x hx) }

/-- UNIT main is exactly the ACTUAL renamed zero-filling list; the single
old empty fibre neither invents an ordinary empty lower face nor duplicates
any pair. This applies to both residues where eta exists. -/
theorem unitIntact_main_faces (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2)
    (X : Finset V) (e : V) (f : Label m ↪ V) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f)) :
    orderedPairs (unitIntactCertificate m hm hr X e f hX hXY).main =
      (fill0 m hm).main.pairs.map (fun P => (P.lower.image f, P.upper.image f)) := by
  unfold orderedPairs orderedPair
  simp only [unitIntactCertificate, Sequence.pairs_cast, relativeProduct_pairs]
  simp [fibres, mem_delta, zeroFilling, retargetFilling, renameFilling,
    Sequence.pairs_cast, renameSequence_pairs]
  have hF : ({x ∈ {∅} | x = ∅} : Finset (Finset V)) = {∅} :=
    Finset.filter_eq_self.mpr (by intro x hx; exact Finset.mem_singleton.mp hx)
  simp only [hF, Finset.toList_singleton, List.mergeSort_singleton,
    List.map_cons, List.map_nil, Finset.union_empty, ← List.map_eq_flatMap]
  simpa only [CollapsePair.upper, Finset.image_insert] using
    renameSequence_pairs f (fill0 m hm).main

/-- UNIT separate execution starts at B alone and is the actual common cone. -/
theorem unitIntact_core_faces (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2)
    (X : Finset V) (e : V) (f : Label m ↪ V) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f)) :
    orderedPairs (unitIntactCertificate m hm hr X e f hX hXY).separate =
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) := by
  exact collapseCone_orderedPairs (X ∪ (ground m).image f)
    (rawJoin (delta X) (renameFamily f (pathRoot m hm))) hX.choose
    (base_support X _ _ (local_support m hm f))
    (base_vertex X _ _ hX.choose_spec (local_empty m hm f))
    (base_cone X _ _ hX.choose_spec)

/-- Good residue, with ALL old tags. The strong branch consumes the original
compiler and its actual collar at its real Gamma hypothesis. Source core=e
is allowed. The VOID and UNIT branches are explicit original-family cases;
no certificate of UNIT is manufactured. -/
def goodIntactCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f))
    (oJ : Output (insert e X) J) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  classical
  cases oJ with
  | void h =>
      let E := renameFamily f (pathRoot m hm)
      let x := hX.choose
      have hx : x ∈ X := hX.choose_spec
      exact replaceCertificate
        (coneCertificate (X ∪ (ground m).image f) (rawJoin (delta X) E) x
          (base_support X _ E (local_support m hm f))
          (base_vertex X E x hx (local_empty m hm f)) (base_cone X E x hx)) (by
            rw [h, parent_void_general])
  | unit h =>
      have hr : m % 3 ≠ 2 := by obtain ⟨k, hk⟩ := hg; omega
      exact replaceCertificate (unitIntactCertificate m hm hr X e f hX hXY) (by rw [h])
  | strong c => exact AllMWheel.oneStep m hm hg c f hf0 heX hXY

/-- Good-residue VOID has the genuine base cone, with empty main. -/
theorem goodVoid_lists (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hv : J = ⊥) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.void hv)).main = [] ∧
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.void hv)).separate =
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) := by
  constructor
  · unfold orderedPairs orderedPair
    simp only [goodIntactCertificate, replaceCertificate, coneCertificate,
      Sequence.pairs_cast, Sequence.pairs, List.map_nil]
  · exact collapseCone_orderedPairs (X ∪ (ground m).image f)
      (rawJoin (delta X) (renameFamily f (pathRoot m hm))) hX.choose
      (base_support X _ _ (local_support m hm f))
      (base_vertex X _ _ hX.choose_spec (local_empty m hm f))
      (base_cone X _ _ hX.choose_spec)

/-- Good-residue UNIT uses the original P0 main and the independent base
cone, as in the constructed unit terminal, for every original ghost. -/
theorem goodUnit_lists (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hu : J = delta ∅) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.unit hu)).main =
      (fill0 m hm).main.pairs.map (fun P => (P.lower.image f, P.upper.image f)) ∧
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.unit hu)).separate =
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) := by
  have hr : m % 3 ≠ 2 := by obtain ⟨k, hk⟩ := hg; omega
  constructor
  · simpa only [goodIntactCertificate, replaceCertificate, orderedPairs, orderedPair,
      Sequence.pairs_cast] using unitIntact_main_faces m hm hr X e f hX hXY
  · exact unitIntact_core_faces m hm hr X e f hX hXY

/-- The real path-filling top in residue two, transported to the original
wheel coordinates. It differs from the cycle-filling top in this residue. -/
def twoPathTop (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) : Finset V :=
  (ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)).image f

private theorem twoPathCells (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (f : Label m ↪ V) :
    CriticalData (renameFamily f (pathRoot m hm)) {twoPathTop m hm f} := by
  let g := renameFilling f (pathFilling m hm)
  have hq : g.critical = {twoPathTop m hm f} := by
    change (pathFilling m hm).critical.image (fun s => s.image f) = _
    rw [pathFilling_critical, if_neg (by omega : m % 3 ≠ 1)]
    simp only [Finset.image_singleton, twoPathTop]
  rw [← hq]
  exact g.cells

/-- Actual P0 with NO retained top in residue two. The endpoint is the
literal E intersect Delta(Z), with both forbidden endpoint ghosts retained. -/
def twoZeroSequence (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (f : Label m ↪ V) :
    Sequence (project (delta ((tailGround m hm).image f)))
      (project (renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f))) := by
  let g := zeroFilling m hm f
  exact g.main.cast rfl (by
    rw [zero_collar, zero_tops, if_pos h2]
    congr 1
    apply SetLike.ext
    intro s
    simp [endpoint, facets])

/-- Actual F_m on the full wheel ground, not a desired core certificate. -/
def twoPathSequence (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (f : Label m ↪ V) :
    Sequence (project (delta ((ground m).image f)))
      (project (renameFamily f (pathRoot m hm) ⊔ delta (twoPathTop m hm f))) := by
  let g := renameFilling f (pathFilling m hm)
  have hq : g.critical = {twoPathTop m hm f} := by
    change (pathFilling m hm).critical.image (fun s => s.image f) = _
    rw [pathFilling_critical, if_neg (by omega : m % 3 ≠ 1)]
    simp only [Finset.image_singleton, twoPathTop]
  exact g.main.cast rfl (by rw [hq, endpoint, facets_single]; rfl)

/-- Exact original-ground normalization in residue two. Its first rectangle
blocks use D minus L; its second blocks use L. The list is computed from the
actual selected P0 and path filling, with each local pair followed by all
descending old fibres. This pair-major schedule is independently proved by
relativeProduct and does not change the local pair order. -/
def twoNormalization (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hXY : Disjoint X ((ground m).image f)) :
    {T : Sequence
        (project (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) J))
        (project (rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (rawLink X e J) (delta (twoPathTop m hm f)))) //
      T.pairs.map (fun P => (P.lower, P.upper)) =
        (twoZeroSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (twoPathSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a)))} := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let D := restrict X J
  let L := rawLink X e J
  let A0' := E ⊓ delta Z
  let N := E ⊔ delta (twoPathTop m hm f)
  let middle := B ⊔ rawJoin L (delta Y)
  have hD : Supported X D := fun _ hs => hs.2
  have hL : Supported X L := fun _ hs => hs.1
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hXZ : Disjoint X Z := Finset.disjoint_left.mpr
    (fun v hv hz => Finset.disjoint_left.mp hXY hv (hZY hz))
  have hA0 : (∅ : Finset V) ∈ A0' := ⟨local_empty m hm f, Finset.empty_subset _⟩
  let T0 := relativeProduct X Z D L middle (delta Z) A0' hXZ hD
    (by
      rintro s ⟨a, ha, t, ht, rfl⟩
      exact Or.inr ⟨a, ha, t, ht.trans hZY, rfl⟩)
    (Finset.empty_subset _) hA0 (fun _ hs => hs) (twoZeroSequence m hm h2 f) (by
      intro a ha hna t ht h
      rcases h with hB | ⟨u, hu, v, hv, he⟩
      · exact ⟨base_local hXY (ht.trans hZY) hB, ht⟩
      · exact False.elim (hna (L.lower
          (old_part hXY (hD a ha) hv (by rw [← he])) hu)))
  have hSource : middle ⊔ rawJoin D (delta Z) = parentOf X Y Z e E J := by
    dsimp [middle, B, D, L, parentOf, phi]
    ac_rfl
  have hTarget : middle ⊔ rawJoin D A0' = middle := by
    apply sup_eq_left.mpr
    rintro s ⟨a, ha, t, ht, rfl⟩
    exact Or.inl ⟨a, hD a ha, t, ht.1, rfl⟩
  let T1 := relativeProduct X Y L ⊥ B (delta Y) N hXY hL
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl (local_empty m hm f)) (fun _ hs => hs)
    (twoPathSequence m hm h2 f) (by
      intro a _ _ t ht hB
      exact Or.inl (base_local hXY ht hB))
  have hFinal : B ⊔ rawJoin L N = B ⊔ rawJoin L (delta (twoPathTop m hm f)) := by
    rw [join_sup]
    have hLE : rawJoin L E ≤ B := join_mono hL le_rfl
    rw [← sup_assoc, sup_eq_left.mpr hLE]
  refine ⟨(T0.1.cast (congrArg project hSource) (congrArg project hTarget)).append
    (T1.1.cast rfl (congrArg project hFinal)), ?_⟩
  rw [Sequence.pairs_append, List.map_append, Sequence.pairs_cast,
    Sequence.pairs_cast, T0.2, T1.2]
  have hbot (K : Family V) :
      (fun a : Finset V => a ∈ K ∧ a ∉ (⊥ : Family V)) = (fun a => a ∈ K) := by
    funext a
    apply propext
    change (a ∈ K ∧ ¬ False) ↔ a ∈ K
    tauto
  simp only [hbot, D, L]

/-- Explicit factor-main list used by the residue-two recovery. Tags emit no
factor pair, and UNIT is not represented by an empty ordinary lower face. -/
def layerMainFaces {U : Finset V} {M : Family V} (d : Finset V) :
    Output U M → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => c.main.pairs.map (fun P => (d ∪ P.lower, d ∪ P.upper))

/-- Explicit separate-layer list, followed by the common original-ground
cone list. The point-layer pair occurs only for a genuine strong factor. -/
def layerCoreFaces {U : Finset V} {M : Family V}
    (W d : Finset V) (B : Family V) (x : V) (o : Output U M) :
    List (Finset V × Finset V) :=
  (match o with
    | .void _ => []
    | .unit _ => []
    | .strong c =>
        c.separate.pairs.map (fun P => (d ∪ P.lower, d ∪ P.upper)) ++
          [(d, insert c.vertex d)]) ++
    (fibres ((W.erase x).powerset.filter (fun s => s.Nonempty ∧ s ∈ B))).map
      (fun s => (s, insert x s))


/- These readbacks eliminate only equality transport of the declared ground.
   No native sequence is reconstructed, reordered or replaced. -/
private theorem ground_mainPairsOf {W W' : Finset V} {K : Family V}
    (h : W = W') (o : Output W K) :
    mainPairsOf (Eq.mp (congrArg (fun T : Finset V => Output T K) h) o) = mainPairsOf o := by
  subst W'
  rfl

private theorem ground_corePairsOf {W W' : Finset V} {K : Family V}
    (h : W = W') (o : Output W K) :
    corePairsOf (Eq.mp (congrArg (fun T : Finset V => Output T K) h) o) = corePairsOf o := by
  subst W'
  rfl

private def pointFaces {W : Finset V} {K : Family V}
    (d : Finset V) (g : V → V) : Output W K → List (Finset V × Finset V)
  | .void _ => []
  | .unit _ => []
  | .strong c => [(d, insert (g c.vertex) d)]

private theorem ground_pointFaces {W W' : Finset V} {K : Family V}
    (h : W = W') (o : Output W K) (d : Finset V) (g : V → V) :
    pointFaces d g (Eq.mp (congrArg (fun T : Finset V => Output T K) h) o) = pointFaces d g o := by
  subst W'
  rfl

private theorem changeOutput_pointFaces {W : Finset V} {K L : Family V}
    (o : Output W K) (h : K = L) (d : Finset V) (g : V → V) :
    pointFaces d g (changeOutput o h) = pointFaces d g o := by
  subst L
  rfl

private theorem renameOutput_lists {W : Finset V} {K : Family V}
    (g : V ↪ V) (o : Output W K) :
    mainPairsOf (HistoryMarkers.renameOutput g o) =
        (mainPairsOf o).map (fun p => (p.1.image g, p.2.image g)) ∧
    corePairsOf (HistoryMarkers.renameOutput g o) =
        (corePairsOf o).map (fun p => (p.1.image g, p.2.image g)) := by
  cases o with
  | void h => subst K; exact ⟨rfl, rfl⟩
  | unit h => subst K; exact ⟨rfl, rfl⟩
  | strong c =>
      constructor
      · simp only [HistoryMarkers.renameOutput, mainPairsOf, renameCertificate,
          orderedPairs, Sequence.pairs_cast, List.map_map, Function.comp_def]
        unfold orderedPair
        exact renameSequence_pairs g c.main
      · simp only [HistoryMarkers.renameOutput, corePairsOf, renameCertificate,
          orderedPairs, Sequence.pairs_cast, List.map_map, Function.comp_def]
        unfold orderedPair
        exact renameSequence_pairs g c.separate

private theorem renameOutput_pointFaces {W : Finset V} {K : Family V}
    (g : V ↪ V) (o : Output W K) (d : Finset V) :
    pointFaces d id (HistoryMarkers.renameOutput g o) = pointFaces d g o := by
  cases o with
  | void h => subst K; rfl
  | unit h => subst K; rfl
  | strong c => rfl

private theorem layer_main_readback {U : Finset V} {M : Family V}
    (d : Finset V) (o : Output U M) :
    HistoryIntactLayers.mainFaces d o =
      (mainPairsOf o).map (fun p => (d ∪ p.1, d ∪ p.2)) := by
  cases o <;> simp only [HistoryIntactLayers.mainFaces, mainPairsOf,
    orderedPairs, orderedPair, List.map_nil, List.map_map, Function.comp_def]

private theorem layer_strip_readback {U : Finset V} {M : Family V}
    (d : Finset V) (o : Output U M) :
    HistoryIntactLayers.stripFaces d o =
      (corePairsOf o).map (fun p => (d ∪ p.1, d ∪ p.2)) ++ pointFaces d id o := by
  cases o <;> simp only [HistoryIntactLayers.stripFaces, corePairsOf,
    pointFaces, orderedPairs, orderedPair, List.map_nil, List.nil_append,
    List.map_map, Function.comp_def, id_eq]

private theorem two_layer_main_readback {U : Finset V} {M : Family V}
    (d : Finset V) (o : Output U M) :
    layerMainFaces d o = (mainPairsOf o).map (fun p => (d ∪ p.1, d ∪ p.2)) := by
  cases o <;> simp only [layerMainFaces, mainPairsOf, orderedPairs, orderedPair,
    List.map_nil, List.map_map, Function.comp_def]

private theorem two_layer_core_readback {U : Finset V} {M : Family V}
    (W d : Finset V) (B : Family V) (x : V) (o : Output U M) :
    layerCoreFaces W d B x o =
      (corePairsOf o).map (fun p => (d ∪ p.1, d ∪ p.2)) ++ pointFaces d id o ++
      (fibres ((W.erase x).powerset.filter (fun s => s.Nonempty ∧ s ∈ B))).map
        (fun s => (s, insert x s)) := by
  cases o <;> simp only [layerCoreFaces, corePairsOf, pointFaces,
    orderedPairs, orderedPair, List.map_nil, List.nil_append,
    List.map_map, Function.comp_def, id_eq]

private theorem faces_flatMap {A : Type*} (ps : List A)
    (face : A → Finset V × Finset V)
    (block : (Finset V × Finset V) → List (Finset V × Finset V)) :
    (ps.map face).flatMap block = ps.flatMap (fun p => block (face p)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]

private def twoRecovered (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (oL : Output X (rawLink X e J)) :
    {c : Certificate (X ∪ (ground m).image f)
        (rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (rawLink X e J) (delta (twoPathTop m hm f))) //
      orderedPairs c.main = layerMainFaces (twoPathTop m hm f) oL ∧
      orderedPairs c.separate = layerCoreFaces (X ∪ (ground m).image f)
        (twoPathTop m hm f) (rawJoin (delta X) (renameFamily f (pathRoot m hm)))
        hX.choose oL} := by
  classical
  let Y := (ground m).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let d := twoPathTop m hm f
  let x := hX.choose
  have hx : x ∈ X := hX.choose_spec
  have hc := twoPathCells m hm h2 f
  have hdY : d ⊆ Y := Finset.image_subset_image Finset.sdiff_subset
  have hd : d.Nonempty := hc.nonempty d (by simp [d])
  have hdE : d ∉ E := hc.absent d (by simp [d])
  have hdX : Disjoint d X := Finset.disjoint_left.mpr
    (fun v hv hx' => Finset.disjoint_left.mp hXY hx' (hdY hv))
  let R := HistoryIntactLayers.oneLayer (X ∪ Y) X d B (rawLink X e J) oL x
    (fun _ hs => hs.1) hd hdX
    (Finset.union_subset (hdY.trans Finset.subset_union_right) Finset.subset_union_left)
    (base_support X Y E (local_support m hm f))
    (base_vertex X E x hx (local_empty m hm f)) (base_cone X E x hx)
    (by
      intro s hs hds
      obtain ⟨a, ha, t, ht, he⟩ := hs
      exact hdE (E.lower (local_part (a := ∅) hXY hdY ha
        (by rw [← he]; simpa only [Finset.empty_union] using hds)) ht))
    (by
      intro z hz t ht
      exact ⟨t, ht, z, hc.boundary d (by simp [d]) z hz, Finset.union_comm _ _⟩)
  refine ⟨replaceCertificate R.1 (by rw [join_comm (delta d) (rawLink X e J)]), ?_, ?_⟩
  · have h := R.2.1
    have hf : HistoryIntactLayers.mainFaces d oL = layerMainFaces d oL := by
      cases oL <;> rfl
    simpa only [replaceCertificate, orderedPairs, orderedPair, Sequence.pairs_cast, hf] using h
  · have h := R.2.2
    have hf : HistoryIntactLayers.stripFaces d oL ++
        (fibres (((X ∪ Y).erase x).powerset.filter (fun s => s.Nonempty ∧ s ∈ B))).map
          (fun s => (s, insert x s)) = layerCoreFaces (X ∪ Y) d B x oL := by
      cases oL <;> rfl
    exact h.trans hf

/-- Complete nonempty-X intact terminal in residue TWO, for every legitimate
L tag and every original-coordinate embedding. Only the actual strictly
earlier L output is needed in this residue. Its main is normalization then
the padded L main. Its separate sequence is the padded L core list, the
point-layer pair when L is strong, and finally the base cone; no critical top
is ever reinserted into that separate execution domain. -/
def twoIntactCertificate (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (oL : Output X (rawLink X e J)) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  let T := twoNormalization m hm h2 X e J f hXY
  let c := (twoRecovered m hm h2 X e J f hX hXY oL).1
  exact {
    supported := parent_supported X _ _ e _ J (tail_subset m hm f) (local_support m hm f)
    core := c.core
    critical := c.critical
    vertex := c.vertex
    vertex_mem := c.vertex_mem
    core_supported := c.core_supported
    critical_supported := c.critical_supported
    cells := c.cells
    main := T.1.append c.main
    separate := c.separate }

private theorem twoRecovered_main_faces (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (oL : Output X (rawLink X e J)) :
    orderedPairs (twoRecovered m hm h2 X e J f hX hXY oL).1.main =
      layerMainFaces (twoPathTop m hm f) oL :=
  (twoRecovered m hm h2 X e J f hX hXY oL).2.1

/-- GLOBAL main-list readback of the actual residue-two certificate. It
expands both normalization blocks and the actual smaller-factor main list. -/
theorem twoIntact_main_faces (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (oL : Output X (rawLink X e J)) :
    orderedPairs (twoIntactCertificate m hm h2 X e J f hX hXY oL).main =
      (twoZeroSequence m hm h2 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (twoPathSequence m hm h2 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      layerMainFaces (twoPathTop m hm f) oL := by
  have hT := (twoNormalization m hm h2 X e J f hXY).2
  have hR := twoRecovered_main_faces m hm h2 X e J f hX hXY oL
  have h := congrArg₂ (fun (xs ys : List (Finset V × Finset V)) => xs ++ ys) hT hR
  unfold orderedPairs orderedPair at h ⊢
  simpa only [twoIntactCertificate, Sequence.pairs_append, List.map_append,
    List.append_assoc] using h

/-- GLOBAL C-ALONE readback of the actual residue-two certificate. Its final
cone is on the whole original ground, filtering by actual B membership; a
strip ghost never becomes a newly selectable coordinate point. -/
theorem twoIntact_core_faces (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (oL : Output X (rawLink X e J)) :
    orderedPairs (twoIntactCertificate m hm h2 X e J f hX hXY oL).separate =
      layerCoreFaces (X ∪ (ground m).image f) (twoPathTop m hm f)
        (rawJoin (delta X) (renameFamily f (pathRoot m hm))) hX.choose oL := by
  exact (twoRecovered m hm h2 X e J f hX hXY oL).2.2

private theorem chosen_snoc_two {U : Type*} [DecidableEq U]
    (vs : List U) (z : U) (hn : vs.length % 3 = 2) :
    FiniteIndependentPathGreedy.pathChosen (vs ++ [z]) =
      FiniteIndependentPathGreedy.pathChosen vs := by
  match vs with
  | [] => simp at hn
  | [a] => simp at hn
  | [a, b] => simp [FiniteIndependentPathGreedy.pathChosen]
  | a :: b :: c :: vs =>
      have ht : vs.length % 3 = 2 := by simp only [List.length_cons] at hn; omega
      simp only [List.cons_append, FiniteIndependentPathGreedy.pathChosen,
        chosen_snoc_two vs z ht]
termination_by vs.length

private theorem zero_chosen (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) :
    FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm) = labelsCongruent m 0 3 := by
  rw [pathRootPath, chosen_snoc_two _ _ (by simp only [labelInterval_length]; omega)]
  ext x
  simp only [pathChosen_labelInterval, labelsCongruent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have := x.isLt
  omega

private theorem zero_rho (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) :
    eta1 m hm = insert (firstLabel m hm) (eta0 m hm) := by
  ext x
  simp only [eta1, eta0, tailGround, tailCritical, if_neg (by omega : m % 3 ≠ 2),
    ground, rim, labelsCongruent, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
    true_and, and_true, Fin.ext_iff, firstLabel, secondLabel,
    ne_eq, Fin.val_zero, Fin.val_mk]
  have := x.isLt
  omega

/-- The two ACTUAL residue-zero local tops: rho is the first-marker extension
of eta; d is the path-filling top and has its entire proper boundary in E. -/
def zeroOtherTop (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) : Finset V :=
  (ground m \ labelsCongruent m 0 3).image f

private theorem zeroOtherCells (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (f : Label m ↪ V) :
    CriticalData (renameFamily f (pathRoot m hm)) {zeroOtherTop m hm f} := by
  let g := renameFilling f (pathFilling m hm)
  have hq : g.critical = {zeroOtherTop m hm f} := by
    change (pathFilling m hm).critical.image (fun s => s.image f) = _
    rw [pathFilling_critical, if_neg (by omega : m % 3 ≠ 1), zero_chosen m hm h0]
    simp only [Finset.image_singleton, zeroOtherTop]
  rw [← hq]
  exact g.cells

private theorem one_interface (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    renameFamily f (A1 m hm) =
      renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f) := by
  change renameFamily f (pathRoot m hm ⊔ delta (tailGround m hm)) = _
  rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
    (delta (tailGround m hm)) ∅).2.1,
    (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]

private def goodOneFilling (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    Filling ((ground m).image f)
      (renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f)) :=
  retargetFilling (renameFilling f (fill1 m hm)) (one_interface m hm f)

/-- The good strong branch consumes the ORIGINAL compiler list expansion at
the actual fillings, including child pairs which involve the removed port.
rightGammaPairs is the selected compiler's classical choice; this theorem
does not identify that choice with a particular witness of gammaGood. -/
theorem goodStrong_main_faces (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (c : Certificate (insert e X) J) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.strong c)).main =
      c.main.pairs.flatMap (fun P =>
        replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) (orderedPair P)
          (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).main.pairs.map
          (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) := by
  change orderedPairs (AllMWheel.oneStep m hm hg c f hf0 heX hXY).main = _
  unfold AllMWheel.oneStep
  apply compileParent_main_orderedPairs

/-- Exact good strong C-ALONE readback. Collars precede the original child
core replay and the actual compiler terminal. The e=source-core-vertex case
uses the compiler's real Gamma permission, with no new supplier premise. -/
theorem goodStrong_core_faces (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (c : Certificate (insert e X) J) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.strong c)).separate =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).separate.pairs.map
          (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) ++
      c.separate.pairs.flatMap (fun P =>
        replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) (orderedPair P)
          (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
      finishFacePairs X ((ground m).image f) ((tailGround m hm).image f)
        ((rim m hm).image f) e c.vertex (renameFamily f (pathRoot m hm))
        (Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩)
        (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm))) := by
  change orderedPairs (AllMWheel.oneStep m hm hg c f hf0 heX hXY).separate = _
  unfold AllMWheel.oneStep
  rw [compileParent_separate_orderedPairs, finishPairSchedule_faces]
  rfl

/-- The original excluded-cycle filling in residue zero, including BOTH
critical tops and its exact ordinary native sequence. -/
def zeroOneSequence (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) (f : Label m ↪ V) :
    Sequence (project (delta ((ground m).image f)))
      (project ((renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f)) ⊔
        (delta ((eta1 m hm).image f) ⊔ delta (zeroOtherTop m hm f)))) := by
  let g := renameFilling f (fill1Excluded m hm (by omega))
  have hq : g.critical = {(eta1 m hm).image f, zeroOtherTop m hm f} := by
    change (fill1Excluded m hm (by omega)).critical.image (fun s => s.image f) = _
    rw [fill1Excluded_critical]
    simp only [cycleCritical, if_pos h0, Finset.image_insert, Finset.image_singleton,
      eta1, zeroOtherTop]
  have hf : facets {(eta1 m hm).image f, zeroOtherTop m hm f} =
      delta ((eta1 m hm).image f) ⊔ delta (zeroOtherTop m hm f) := by
    apply SetLike.ext
    intro s
    simp [facets]
  have hcollar : g.collar = renameFamily f (pathRoot m hm) ⊔
      delta ((tailGround m hm).image f) := one_interface m hm f
  exact g.main.cast rfl (congrArg project
    (congrArg₂ (fun A B : Family V => A ⊔ B) hcollar ((congrArg facets hq).trans hf)))

/-- The original zero filling with eta retained, at every residue-zero width
including m=3 where its genuine local list is empty. -/
def zeroZeroSequence (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) (f : Label m ↪ V) :
    Sequence (project (delta ((tailGround m hm).image f)))
      (project ((renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f)) ⊔
        delta ((eta0 m hm).image f))) := by
  let g := zeroFilling m hm f
  exact g.main.cast rfl (by
    rw [zero_collar, zero_tops, if_neg (by omega : m % 3 ≠ 2), endpoint, facets_single])

private theorem join_assoc (K L M : Family V) :
    rawJoin (rawJoin K L) M = rawJoin K (rawJoin L M) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b ∪ c, ⟨b, hb, c, hc, rfl⟩, Finset.union_assoc _ _ _⟩
  · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a ∪ b, ⟨a, ha, b, hb, rfl⟩, c, hc, (Finset.union_assoc _ _ _).symm⟩

private theorem join_delta (a b : Finset V) :
    rawJoin (delta a) (delta b) = delta (a ∪ b) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Finset.union_subset_union hx hy
  · intro hs
    refine ⟨s ∩ a, Finset.inter_subset_right, s ∩ b, Finset.inter_subset_right, ?_⟩
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    exact ⟨fun hv => (Finset.mem_union.mp (hs hv)).elim
      (fun ha => Or.inl ⟨hv, ha⟩) (fun hb => Or.inr ⟨hv, hb⟩), by tauto⟩

private theorem marker_pad (D L : Family V) (r : V) (d : Finset V) :
    rawJoin (HistoryIsolated.singleFamily D L r) (delta d) =
      rawJoin D (delta d) ⊔ rawJoin L (delta (insert r d)) := by
  rw [join_comm, HistoryIsolated.singleFamily, join_sup,
    join_comm (delta d) D, join_comm (delta d) (rawJoin (delta {r}) L),
    join_assoc, join_comm L (delta d), ← join_assoc, join_delta,
    Finset.singleton_union, join_comm (delta (insert r d)) L]

/-- The residue-zero parent is normalized to the EXACT two factor layers,
B union Jhat*Delta(eta) union L*Delta(d). Jhat is the actual coordinate swap
of J, not its collapsed surrogate. BOTH emitted blocks have complete native
ordered readbacks. This is a normalization theorem, not the missing two-factor
strong recovery or the universal history theorem. -/
def zeroNormalization (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) :
    {T : Sequence
        (project (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) J))
        (project ((rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J)
            (delta ((eta0 m hm).image f))) ⊔
          rawJoin (rawLink X e J) (delta (zeroOtherTop m hm f)))) //
      T.pairs.map (fun P => (P.lower, P.upper)) =
        (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a)))} := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let D := restrict X J
  let L := rawLink X e J
  let eta := (eta0 m hm).image f
  let rho := (eta1 m hm).image f
  let d := zeroOtherTop m hm f
  let r := f (firstLabel m hm)
  let N1 := (E ⊔ delta Z) ⊔ (delta rho ⊔ delta d)
  let N0 := (E ⊓ delta Z) ⊔ delta eta
  let C1 := B ⊔ rawJoin D (delta Z)
  let C0 := B ⊔ rawJoin L (delta rho ⊔ delta d)
  have hD : Supported X D := fun _ hs => hs.2
  have hL : Supported X L := fun _ hs => hs.1
  have hLD : L ≤ D := fun s hs => ⟨J.lower (Finset.subset_insert _ _) hs.2, hs.1⟩
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hrY : r ∈ Y := Finset.mem_image.mpr
    ⟨firstLabel m hm, by simp [ground, firstLabel], rfl⟩
  have hrX : r ∉ X := fun hr => Finset.disjoint_left.mp hXY hr hrY
  have hrZ : r ∉ Z := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have hi' := (f.injective he)
    subst i
    simpa [tailGround, rim] using hi
  have hRho : rho = insert r eta := by
    dsimp [rho, eta, r]
    rw [zero_rho m hm h0, Finset.image_insert]
  have hdCells : CriticalData E {d} := zeroOtherCells m hm h0 f
  have hdZ : ¬ d ⊆ Z := by
    intro h
    have h2d : f (secondLabel m hm) ∈ d := Finset.mem_image.mpr
      ⟨secondLabel m hm, by simp [ground, labelsCongruent, secondLabel], rfl⟩
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (h h2d)
    have hi' := f.injective he
    subst i
    simpa [tailGround, rim] using hi
  let T1 := relativeProduct X Y L ⊥ C1 (delta Y) N1 hXY hL
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl (Or.inl (local_empty m hm f)))
    (fun _ hs => hs) (zeroOneSequence m hm h0 f) (by
      intro a _ _ t ht h
      rcases h with hB | ⟨u, hu, v, hv, he⟩
      · exact Or.inl (Or.inl (base_local hXY ht hB))
      · exact Or.inl (Or.inr ((local_part hXY ht (hD u hu) (by rw [← he])).trans hv)))
  have hS1 : C1 ⊔ rawJoin L (delta Y) = parentOf X Y Z e E J := by
    dsimp [C1, B, D, L, parentOf, phi]
    ac_rfl
  have hT1 : C1 ⊔ rawJoin L N1 = C0 ⊔ rawJoin D (delta Z) := by
    dsimp [C1, C0, N1]
    rw [join_sup, join_sup]
    have hLE : rawJoin L E ≤ B := join_mono hL le_rfl
    have hLZ : rawJoin L (delta Z) ≤ rawJoin D (delta Z) := join_mono hLD le_rfl
    have h : (B ⊔ rawJoin D (delta Z)) ⊔
          ((rawJoin L E ⊔ rawJoin L (delta Z)) ⊔ rawJoin L (delta rho ⊔ delta d)) =
        ((B ⊔ rawJoin L E) ⊔
          (rawJoin D (delta Z) ⊔ rawJoin L (delta Z))) ⊔
          rawJoin L (delta rho ⊔ delta d) := by ac_rfl
    rw [h, sup_eq_left.mpr hLE, sup_eq_left.mpr hLZ]
    ac_rfl
  have hXZ : Disjoint X Z := Finset.disjoint_left.mpr
    (fun v hv hz => Finset.disjoint_left.mp hXY hv (hZY hz))
  let T0 := relativeProduct X Z D ⊥ C0 (delta Z) N0 hXZ hD
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl ⟨local_empty m hm f, Finset.empty_subset _⟩)
    (fun _ hs => hs) (zeroZeroSequence m hm h0 f) (by
      intro a _ _ t ht h
      rcases h with hB | ⟨u, hu, v, hv | hv, he⟩
      · exact Or.inl ⟨base_local hXY (ht.trans hZY) hB, ht⟩
      · have htr : t ⊆ rho := (local_part hXY (ht.trans hZY) (hL u hu)
          (by rw [← he])).trans hv
        right
        intro w hw
        exact (Finset.mem_insert.mp (hRho ▸ htr hw)).resolve_left
          (fun (heq : w = r) => hrZ (heq ▸ ht hw))
      · have htd : t ⊆ d := (local_part hXY (ht.trans hZY) (hL u hu)
          (by rw [← he])).trans hv
        have hp : t ⊂ d := Finset.ssubset_iff_subset_ne.mpr
          ⟨htd, fun heq => hdZ (heq ▸ ht)⟩
        exact Or.inl ⟨hdCells.boundary d (by simp) t hp, ht⟩)
  have hT0 : C0 ⊔ rawJoin D N0 =
      (B ⊔ rawJoin
        (renameFamily (HistoryMarkers.markerMap e r) J) (delta eta)) ⊔ rawJoin L (delta d) := by
    have hDA : rawJoin D (E ⊓ delta Z) ≤ B := join_mono hD (fun _ h => h.1)
    rw [HistoryMarkers.single_marker_family X e r J heX hrX hJ, marker_pad]
    dsimp [C0, N0]
    rw [join_sup, join_sup]
    have hs : (B ⊔ (rawJoin L (delta rho) ⊔ rawJoin L (delta d))) ⊔
        (rawJoin D (E ⊓ delta Z) ⊔ rawJoin D (delta eta)) =
        ((B ⊔ rawJoin D (E ⊓ delta Z)) ⊔ rawJoin D (delta eta)) ⊔
          (rawJoin L (delta rho) ⊔ rawJoin L (delta d)) := by ac_rfl
    rw [hs, sup_eq_left.mpr hDA, ← hRho]
    dsimp only [D, L]
    ac_rfl
  refine ⟨(T1.1.cast (congrArg project hS1) (congrArg project hT1)).append
    (T0.1.cast rfl (congrArg project hT0)), ?_⟩
  rw [Sequence.pairs_append, List.map_append, Sequence.pairs_cast,
    Sequence.pairs_cast, T1.2, T0.2]
  have hbot (K : Family V) :
      (fun a : Finset V => a ∈ K ∧ a ∉ (⊥ : Family V)) = (fun a => a ∈ K) := by
    funext a
    apply propext
    change (a ∈ K ∧ ¬ False) ↔ a ∈ K
    tauto
  simp only [hbot, D, L]

private theorem zeroCycleCells (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (f : Label m ↪ V) :
    CriticalData (renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f))
      {(eta1 m hm).image f, zeroOtherTop m hm f} := by
  let g := renameFilling f (fill1Excluded m hm (by omega))
  have hq : g.critical = {(eta1 m hm).image f, zeroOtherTop m hm f} := by
    change (fill1Excluded m hm (by omega)).critical.image (fun s => s.image f) = _
    rw [fill1Excluded_critical]
    simp only [cycleCritical, if_pos h0, Finset.image_insert, Finset.image_singleton,
      eta1, zeroOtherTop]
  have hc : g.collar = renameFamily f (pathRoot m hm) ⊔
      delta ((tailGround m hm).image f) := one_interface m hm f
  rw [← hc, ← hq]
  exact g.cells

/-- The actual J predecessor, with e replaced by the FIRST original wheel
coordinate, retaining every old coordinate and ghost in X. -/
def zeroMarkerOutput (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V) (J : Family V)
    (f : Label m ↪ V) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) (oJ : Output (insert e X) J) :
    Output (insert (f (firstLabel m hm)) X)
      (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J) := by
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  exact changeOutput (HistoryMarkers.singleMarkerOutput X e _ J heX hr hJ oJ)
    (HistoryMarkers.single_marker_family X e _ J heX hr hJ).symm


/-- Both lists of the actual marker output are the injective images of the
ORIGINAL oJ lists. Ground equality and the two family equalities change no
pair. renameSequence_pairs is used independently for main and C ALONE. -/
theorem zeroMarkerOutput_lists (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (heX : e ∉ X)
    (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) (oJ : Output (insert e X) J) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    mainPairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        (mainPairsOf oJ).map (fun p => (p.1.image g, p.2.image g)) ∧
    corePairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        (corePairsOf oJ).map (fun p => (p.1.image g, p.2.image g)) := by
  dsimp only
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  have hg := HistoryMarkers.marker_ground X e (f (firstLabel m hm)) heX hr
  have h := renameOutput_lists (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ
  constructor
  · calc
      mainPairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
          mainPairsOf (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
        simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
          changeOutput_mainPairsOf] using ground_mainPairsOf hg
            (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ)
      _ = _ := h.1
  · calc
      corePairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
          corePairsOf (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
        simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
          changeOutput_corePairsOf] using ground_corePairsOf hg
            (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ)
      _ = _ := h.2

private theorem zeroMarkerOutput_pointFaces (m : Nat) (hm : 3 ≤ m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (heX : e ∉ X)
    (hXY : Disjoint X ((ground m).image f)) (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (d : Finset V) :
    pointFaces d id (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
      pointFaces d (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ := by
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  have hg := HistoryMarkers.marker_ground X e (f (firstLabel m hm)) heX hr
  calc
    pointFaces d id (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        pointFaces d id (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
      simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
        changeOutput_pointFaces] using ground_pointFaces hg
          (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) d id
    _ = _ := renameOutput_pointFaces (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ d

/-- Recovery of BOTH literal residue-zero layers, with all tag combinations.
The first factor is the actual renamed J; the second is its actual old link.
The other full layer is fixed during each main lift. On C ALONE the first
core is stripped, then the second, and the common original-ground cone runs
exactly once. The displayed list equations belong to the constructed value.
-/
def zeroRecovered (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    {c : Certificate (X ∪ (ground m).image f)
        ((rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J)
            (delta ((eta0 m hm).image f))) ⊔
          rawJoin (rawLink X e J) (delta (zeroOtherTop m hm f))) //
      orderedPairs c.main =
        HistoryIntactLayers.mainFaces ((eta0 m hm).image f)
          (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
        HistoryIntactLayers.mainFaces (zeroOtherTop m hm f) oL ∧
      orderedPairs c.separate =
        HistoryIntactLayers.stripFaces ((eta0 m hm).image f)
          (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
        HistoryIntactLayers.stripFaces (zeroOtherTop m hm f) oL ++
        (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
          (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
          (fun s => (s, insert hX.choose s))} := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let r := f (firstLabel m hm)
  let eta := (eta0 m hm).image f
  let rho := (eta1 m hm).image f
  let d := zeroOtherTop m hm f
  let U := insert r X
  let M := renameFamily (HistoryMarkers.markerMap e r) J
  let L := rawLink X e J
  let ohat := zeroMarkerOutput m hm X e J f heX hXY hJ oJ
  let x := hX.choose
  have hx : x ∈ X := hX.choose_spec
  have hrY : r ∈ Y := Finset.mem_image.mpr
    ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩
  have hrX : r ∉ X := fun h => Finset.disjoint_left.mp hXY h hrY
  have hrZ : r ∉ Z := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have hi' := f.injective he
    subst i
    simpa [tailGround, rim] using hi
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hRho : rho = insert r eta := by
    dsimp [rho, eta, r]
    rw [zero_rho m hm h0, Finset.image_insert]
  let g := zeroFilling m hm f
  have hgQ : g.critical = {eta} := by rw [zero_tops, if_neg (by omega : m % 3 ≠ 2)]
  have hEtaZ : eta ⊆ Z := g.critical_supported eta (by rw [hgQ]; simp)
  have hEtaCells : CriticalData (E ⊓ delta Z) {eta} := by
    rw [← zero_collar m hm f, ← hgQ]
    exact g.cells
  have hEtaE : eta ∉ E := fun h => hEtaCells.absent eta (by simp) ⟨h, hEtaZ⟩
  have hdCells : CriticalData E {d} := zeroOtherCells m hm h0 f
  have hdY : d ⊆ Y := Finset.image_subset_image Finset.sdiff_subset
  have hdE : d ∉ E := hdCells.absent d (by simp)
  have hrEta : r ∉ eta := fun h => hrZ (hEtaZ h)
  have hEtaU : Disjoint eta U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    rcases Finset.mem_insert.mp hu with he | hx'
    · exact hrEta (he ▸ hv)
    · exact Finset.disjoint_left.mp hXY hx' (hZY (hEtaZ hv))
  have hdX : Disjoint d X := Finset.disjoint_left.mpr
    (fun v hv hx' => Finset.disjoint_left.mp hXY hx' (hdY hv))
  have hM : Supported U M := by
    change Supported U (renameFamily (HistoryMarkers.markerMap e r) J)
    rw [HistoryMarkers.single_marker_family X e r J heX hrX hJ]
    rintro s (hs | ⟨a, ha, t, ht, rfl⟩)
    · exact hs.2.trans (Finset.subset_insert _ _)
    · exact Finset.union_subset
        (ha.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
        (ht.1.trans (Finset.subset_insert _ _))
  have hL : Supported X L := fun _ hs => hs.1
  have hCycle := zeroCycleCells m hm h0 f
  have hEtaNotD : ¬ eta ⊆ d := by
    let i : Label m := ⟨3, by omega⟩
    have hiEta : i ∈ eta0 m hm := by
      simp [i, eta0, tailGround, rim, tailCritical, h0, labelsCongruent,
        firstLabel, secondLabel, ground]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨i, hiEta, rfl⟩))
    have hi' := f.injective he
    subst j
    simpa [i, labelsCongruent] using (Finset.mem_sdiff.mp hj).2
  have hDNotRho : ¬ d ⊆ rho := by
    have hiD : secondLabel m hm ∈ ground m \ labelsCongruent m 0 3 := by
      simp [ground, labelsCongruent, secondLabel]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp
      (h (Finset.mem_image.mpr ⟨secondLabel m hm, hiD, rfl⟩))
    have hi' := f.injective he
    subst j
    simpa [eta1, labelsCongruent, secondLabel] using hj
  have hMissing : ∀ s ∈ B ⊔ rawJoin (delta d) (delta X), ¬ eta ⊆ s := by
    intro s hs hsub
    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
    · exact hEtaE (base_local (a := ∅) hXY (hEtaZ.trans hZY)
        (by change ∅ ∪ _ ∈ B; rw [Finset.empty_union]; exact B.lower hsub hs))
    · exact hEtaNotD ((local_part (a := ∅) hXY (hEtaZ.trans hZY) ht
        (by simpa only [Finset.empty_union, Finset.union_comm] using hsub)).trans ha)
  have hMissing' : ∀ s ∈ B ⊔ rawJoin (delta eta) (delta U), ¬ d ⊆ s := by
    intro s hs hsub
    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
    · exact hdE (base_local (a := ∅) hXY hdY
        (by change ∅ ∪ _ ∈ B; rw [Finset.empty_union]; exact B.lower hsub hs))
    · apply hDNotRho
      intro v hv
      rcases Finset.mem_union.mp (hsub hv) with hva | hvt
      · rw [hRho]; exact Finset.mem_insert_of_mem (ha hva)
      · rcases Finset.mem_insert.mp (ht hvt) with hvr | hvX
        · rw [hRho]; exact Finset.mem_insert.mpr (Or.inl hvr)
        · exact False.elim (Finset.disjoint_left.mp hXY hvX (hdY hv))
  have hBoundary : ∀ z ⊂ eta, ∀ t ⊆ U, z ∪ t ∈ B := by
    intro z hz t ht
    by_cases hrt : r ∈ t
    · have hp : insert r z ⊂ rho := by
        rw [hRho]
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.insert_subset_insert r hz.subset, ?_⟩
        intro he
        apply hz.ne
        apply Finset.Subset.antisymm hz.subset
        intro v hv
        exact (Finset.mem_insert.mp (he.symm ▸ Finset.mem_insert_of_mem hv)).resolve_left
          (fun (hvr : v = r) => hrEta (hvr ▸ hv))
      have hLocal : insert r z ∈ E :=
        (hCycle.boundary rho (by simp [rho]) _ hp).resolve_right
          (fun hZ => hrZ (hZ (Finset.mem_insert_self _ _)))
      have htX : t.erase r ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hv).2)).resolve_left
          (Finset.mem_erase.mp hv).1
      exact ⟨t.erase r, htX, insert r z, hLocal, by
        rw [Finset.union_insert, ← Finset.insert_union, Finset.insert_erase hrt]
        exact Finset.union_comm _ _⟩
    · have htX : t ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (ht hv)).resolve_left (fun hvr => hrt (hvr ▸ hv))
      exact ⟨t, htX, z, (hEtaCells.boundary eta (by simp) z hz).1,
        Finset.union_comm _ _⟩
  let R := HistoryIntactLayers.twoLayers (X ∪ Y) B x U eta M ohat X d L oL
    hM hL (hEtaCells.nonempty eta (by simp)) (hdCells.nonempty d (by simp)) hEtaU hdX
    (Finset.union_subset ((hEtaZ.trans hZY).trans Finset.subset_union_right)
      (Finset.insert_subset (Finset.mem_union_right _ hrY) Finset.subset_union_left))
    (Finset.union_subset (hdY.trans Finset.subset_union_right) Finset.subset_union_left)
    (base_support X Y E (local_support m hm f))
    (base_vertex X E x hx (local_empty m hm f)) (base_cone X E x hx)
    hMissing hMissing' hBoundary (by
      intro z hz t ht
      exact ⟨t, ht, z, hdCells.boundary d (by simp) z hz, Finset.union_comm _ _⟩)
  have hSource : (B ⊔ rawJoin (delta eta) M) ⊔ rawJoin (delta d) L =
      (B ⊔ rawJoin M (delta eta)) ⊔ rawJoin L (delta d) := by
    rw [join_comm (delta eta) M, join_comm (delta d) L]
  refine ⟨replaceCertificate R.1 hSource, ?_, ?_⟩
  · simpa only [replaceCertificate, orderedPairs, orderedPair, Sequence.pairs_cast]
      using R.2.1
  · exact R.2.2

/-- Residue zero: both normalization blocks precede BOTH recovered factor
mains. The independent separate sequence is the one in zeroRecovered. -/
def zeroIntactCertificate (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  let T := zeroNormalization m hm h0 X e J f heX hXY hJ
  let c := (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).1
  exact {
    supported := parent_supported X _ _ e _ J (tail_subset m hm f) (local_support m hm f)
    core := c.core
    critical := c.critical
    vertex := c.vertex
    vertex_mem := c.vertex_mem
    core_supported := c.core_supported
    critical_supported := c.critical_supported
    cells := c.cells
    main := T.1.append c.main
    separate := c.separate }

/-- Complete ordered main readback of the constructed zero-residue value. -/
theorem zeroIntact_main_faces (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).main =
      (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      HistoryIntactLayers.mainFaces ((eta0 m hm).image f)
        (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
      HistoryIntactLayers.mainFaces (zeroOtherTop m hm f) oL := by
  have hT := (zeroNormalization m hm h0 X e J f heX hXY hJ).2
  have hR := (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).2.1
  have h := congrArg₂ (fun (xs ys : List (Finset V × Finset V)) => xs ++ ys) hT hR
  unfold orderedPairs orderedPair at h ⊢
  simpa only [zeroIntactCertificate, Sequence.pairs_append, List.map_append,
    List.append_assoc] using h

/-- Complete C-ALONE readback: the two core strips precede the sole cone. -/
theorem zeroIntact_core_faces (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).separate =
      HistoryIntactLayers.stripFaces ((eta0 m hm).image f)
        (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
      HistoryIntactLayers.stripFaces (zeroOtherTop m hm f) oL ++
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) :=
  (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).2.2


/-- Original-factor main readback. The normalization is local-pair-major,
then the original oJ list is renamed and padded, then original oL is padded.
This consumes the existing normalization/recovery proof without changing it. -/
theorem zeroIntact_main_original (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).main =
      (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (mainPairsOf oJ).map (fun p =>
        ((eta0 m hm).image f ∪ p.1.image g, (eta0 m hm).image f ∪ p.2.image g)) ++
      (mainPairsOf oL).map (fun p =>
        (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2)) := by
  dsimp only
  rw [zeroIntact_main_faces]
  simp only [layer_main_readback, (zeroMarkerOutput_lists m hm X e J f heX hXY hJ oJ).1,
    List.map_map, Function.comp_def]

/-- Original-factor C-ALONE readback. Only a strong factor contributes its
point-layer pair; the marker point is mapped by the same original swap.
The first core strip, second core strip and common cone keep their order. -/
theorem zeroIntact_core_original (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    let eta := (eta0 m hm).image f
    let d := zeroOtherTop m hm f
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).separate =
      (corePairsOf oJ).map (fun p => (eta ∪ p.1.image g, eta ∪ p.2.image g)) ++
      (match oJ with
        | .void _ => []
        | .unit _ => []
        | .strong c => [(eta, insert (g c.vertex) eta)]) ++
      (corePairsOf oL).map (fun p => (d ∪ p.1, d ∪ p.2)) ++
      (match oL with
        | .void _ => []
        | .unit _ => []
        | .strong c => [(d, insert c.vertex d)]) ++
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) := by
  dsimp only
  rw [zeroIntact_core_faces]
  simp only [layer_strip_readback,
    (zeroMarkerOutput_lists m hm X e J f heX hXY hJ oJ).2,
    zeroMarkerOutput_pointFaces, List.map_map, Function.comp_def, List.append_assoc]
  simp only [pointFaces, id_eq]
  congr 10

/-- The intended nonempty-X local terminal at EVERY m>=3, on actual original
coordinates. oJ and oL are the exact strictly-earlier predecessor factors;
they are NOT hypotheses of a final universal physical-history theorem.
No same-rank parent, core, link or deletion output is supplied here. -/
def intactOutput (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V) (J : Family V)
    (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f)) (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    Output (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  classical
  by_cases h0 : m % 3 = 0
  · exact .strong (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL)
  · by_cases h2 : m % 3 = 2
    · exact .strong (twoIntactCertificate m hm h2 X e J f hX hXY oL)
    · have hg : goodResidue m := ⟨m / 3, by omega⟩
      exact .strong (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY oJ)


/-- Full main-list readback of intactOutput, at every residue and every
actual tag, explicitly in the ORIGINAL oJ/oL lists. No list is permuted. -/
theorem intactOutput_main_faces (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    mainPairsOf (intactOutput m hm X e J f hf0 heX hX hXY hJ oJ oL) =
      if h0 : m % 3 = 0 then
        (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oJ).map (fun p =>
          ((eta0 m hm).image f ∪ p.1.image (HistoryMarkers.markerMap e (f (firstLabel m hm))),
           (eta0 m hm).image f ∪ p.2.image (HistoryMarkers.markerMap e (f (firstLabel m hm))))) ++
        (mainPairsOf oL).map (fun p =>
          (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2))
      else if h2 : m % 3 = 2 then
        (twoZeroSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (twoPathSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oL).map (fun p => (twoPathTop m hm f ∪ p.1, twoPathTop m hm f ∪ p.2))
      else match oJ with
        | .void _ => []
        | .unit _ => (fill0 m hm).main.pairs.map
            (fun P => (P.lower.image f, P.upper.image f))
        | .strong c =>
            (mainPairsOf oJ).flatMap (fun p =>
              replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
                (renameFamily f (pathRoot m hm)) p
                (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
            (fibres c.critical).flatMap (fun q =>
              (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).main.pairs.map
                (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) := by
  classical
  split_ifs with h0 h2
  · simpa only [intactOutput, dif_pos h0, mainPairsOf] using
      zeroIntact_main_original m hm h0 X e J f heX hX hXY hJ oJ oL
  · simpa only [intactOutput, dif_neg h0, dif_pos h2, mainPairsOf,
      two_layer_main_readback] using twoIntact_main_faces m hm h2 X e J f hX hXY oL
  · have hg : goodResidue m := ⟨m / 3, by omega⟩
    cases oJ with
    | void hv =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf] using
          (goodVoid_lists m hm hg X e J f hf0 heX hX hXY hv).1
    | unit hu =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf] using
          (goodUnit_lists m hm hg X e J f hf0 heX hX hXY hu).1
    | strong c =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf,
          orderedPairs, faces_flatMap] using
          goodStrong_main_faces m hm hg X e J f hf0 heX hX hXY c

/-- Full separate C-ALONE readback of intactOutput. The zero and two
branches finish their actual core strips before the common cone. The good
branch retains original collar order, original core replay and its actual
compiler terminal, including source-core vertex e. -/
theorem intactOutput_core_faces (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let Y := (ground m).image f
    let E := renameFamily f (pathRoot m hm)
    let cone := (fibres (((X ∪ Y).erase hX.choose).powerset.filter
      (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) E))).map
      (fun s => (s, insert hX.choose s))
    corePairsOf (intactOutput m hm X e J f hf0 heX hX hXY hJ oJ oL) =
      if h0 : m % 3 = 0 then
        (corePairsOf oJ).map (fun p =>
          ((eta0 m hm).image f ∪ p.1.image (HistoryMarkers.markerMap e (f (firstLabel m hm))),
           (eta0 m hm).image f ∪ p.2.image (HistoryMarkers.markerMap e (f (firstLabel m hm))))) ++
        (match oJ with
          | .void _ => []
          | .unit _ => []
          | .strong c => [((eta0 m hm).image f,
              insert (HistoryMarkers.markerMap e (f (firstLabel m hm)) c.vertex) ((eta0 m hm).image f))]) ++
        (corePairsOf oL).map (fun p => (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(zeroOtherTop m hm f, insert c.vertex (zeroOtherTop m hm f))]) ++ cone
      else if h2 : m % 3 = 2 then
        (corePairsOf oL).map (fun p => (twoPathTop m hm f ∪ p.1, twoPathTop m hm f ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(twoPathTop m hm f, insert c.vertex (twoPathTop m hm f))]) ++ cone
      else match oJ with
        | .void _ => cone
        | .unit _ => cone
        | .strong c =>
            (fibres c.critical).flatMap (fun q =>
              (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).separate.pairs.map
                (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) ++
            (corePairsOf oJ).flatMap (fun p =>
              replayFacePairs Y ((tailGround m hm).image f) e E p (rightGammaPairs Y E)) ++
            finishFacePairs X Y ((tailGround m hm).image f) ((rim m hm).image f)
              e c.vertex E (Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩)
              (rightGammaPairs Y E) := by
  classical
  dsimp only
  split_ifs with h0 h2
  · simpa only [intactOutput, dif_pos h0, corePairsOf] using
      zeroIntact_core_original m hm h0 X e J f heX hX hXY hJ oJ oL
  · simp only [intactOutput, dif_neg h0, dif_pos h2, corePairsOf]
    rw [twoIntact_core_faces, two_layer_core_readback]
    simp only [corePairsOf, pointFaces, id_eq, List.append_assoc]
    congr 10
  · have hg : goodResidue m := ⟨m / 3, by omega⟩
    cases oJ with
    | void hv =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf] using
          (goodVoid_lists m hm hg X e J f hf0 heX hX hXY hv).2
    | unit hu =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf] using
          (goodUnit_lists m hm hg X e J f hf0 heX hX hXY hu).2
    | strong c =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf,
          orderedPairs, faces_flatMap] using
          goodStrong_core_faces m hm hg X e J f hf0 heX hX hXY c

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact

