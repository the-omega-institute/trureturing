/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers
   mirror-E: none(waiver:physical-history-marker-coordinates)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Basic]
   utility: none
   digest: Isolated markers use actual original-coordinate swaps and renamed native certificates of the earlier model. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated
import D5.S3.Geometry.OriginalLabelTwoSum.Rename

/-! SOURCE_ONLY_UNCOMPILED. The old model J is used literally, with D its
restriction and L its actual link. A marker replaces e through an injective
coordinate map fixing EVERY label of X, including ghosts. The twin strip is
followed by that renamed output. No same-rank universal supplier is assumed.
The final history induction and forest/intact branches are still obligations.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
open OriginalLabelTwoSum HistoryLeafCap HistoryIsolated
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual coordinate replacement. When e=r this is the identity. -/
def markerMap (e r : V) : V ↪ V := (Equiv.swap e r).toEmbedding

private theorem markerMap_left (e r : V) : markerMap e r e = r := by
  change Equiv.swap e r e = r
  exact Equiv.swap_apply_left e r

private theorem markerMap_fixed (X : Finset V) (e r : V)
    (he : e ∉ X) (hr : r ∉ X) {x : V} (hx : x ∈ X) : markerMap e r x = x := by
  change Equiv.swap e r x = x
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  have hxr : x ≠ r := fun h => hr (h ▸ hx)
  simp [Equiv.swap_apply_def, hxe, hxr]

private theorem marker_image (X : Finset V) (e r : V)
    (he : e ∉ X) (hr : r ∉ X) {t : Finset V} (ht : t ⊆ X) :
    t.image (markerMap e r) = t := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
    rw [markerMap_fixed X e r he hr (ht hv)] at hvx
    exact hvx ▸ hv
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, markerMap_fixed X e r he hr (ht hx)⟩

theorem marker_ground (X : Finset V) (e r : V)
    (he : e ∉ X) (hr : r ∉ X) :
    (insert e X).image (markerMap e r) = insert r X := by
  rw [Finset.image_insert, markerMap_left, marker_image X e r he hr le_rfl]

/-- Transport a genuine tagged output, using the existing renameCertificate
and renameSequence. Both native lists are mapped through this SAME injection. -/
def renameOutput {W : Finset V} {K : Family V} (f : V ↪ V) (o : Output W K) :
    Output (W.image f) (renameFamily f K) := by
  cases o with
  | void h =>
      subst K
      exact .void (by
        apply SetLike.ext
        intro s
        exact ⟨fun ⟨t, ht, _⟩ => ht.elim, fun h => h.elim⟩)
  | unit h =>
      subst K
      exact .unit (by
        apply SetLike.ext
        intro s
        constructor
        · rintro ⟨t, ht, rfl⟩
          have he : t = ∅ := Finset.subset_empty.mp ht
          simp [he, delta]
        · intro hs
          have he : s = ∅ := Finset.subset_empty.mp hs
          subst s
          exact ⟨∅, (show (∅ : Finset V) ⊆ ∅ from le_rfl), by simp⟩)
  | strong c => exact .strong (renameCertificate f c)

/-- Exact isolated ONE-marker bridge to the actual earlier model. D and L
are not arbitrary factor certificates; they are the literal deletion and link. -/
theorem single_marker_family (X : Finset V) (e r : V) (J : Family V)
    (he : e ∉ X) (hr : r ∉ X) (hJ : Supported (insert e X) J) :
    renameFamily (markerMap e r) J =
      singleFamily (restrict X J) (rawLink X e J) r := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases het : e ∈ t
    · have hx : t.erase e ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (hJ t ht (Finset.mem_erase.mp hv).2)).resolve_left
          (Finset.mem_erase.mp hv).1
      have hi : t.image (markerMap e r) = insert r (t.erase e) := by
        conv_lhs => rw [← Finset.insert_erase het]
        rw [Finset.image_insert, markerMap_left, marker_image X e r he hr hx]
      exact Or.inr ⟨{r}, (show ({r} : Finset V) ⊆ {r} from le_rfl), t.erase e,
        ⟨hx, by simpa only [Finset.insert_erase het] using ht⟩,
        by simpa only [Finset.singleton_union] using hi⟩
    · have hx : t ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (hJ t ht hv)).resolve_left (fun h => het (h ▸ hv))
      rw [marker_image X e r he hr hx]
      exact Or.inl ⟨ht, hx⟩
  · rintro (hs | ⟨a, ha, t, ⟨htX, htJ⟩, rfl⟩)
    · exact ⟨s, hs.1, marker_image X e r he hr hs.2⟩
    · by_cases hra : r ∈ a
      · have hae : a = {r} := Finset.Subset.antisymm ha (Finset.singleton_subset_iff.mpr hra)
        subst a
        refine ⟨insert e t, htJ, ?_⟩
        rw [Finset.image_insert, markerMap_left, marker_image X e r he hr htX]
        simp only [Finset.singleton_union]
      · have hae : a = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          exact hra (Finset.mem_singleton.mp (ha hv) ▸ hv)
        subst a
        exact ⟨t, J.lower (Finset.subset_insert _ _) htJ,
          by simpa only [Finset.empty_union] using marker_image X e r he hr htX⟩

/-- A one-marker output constructed from the earlier J output by the actual
coordinate map, with all original ghosts preserved. -/
def singleMarkerOutput (X : Finset V) (e r : V) (J : Family V)
    (he : e ∉ X) (hr : r ∉ X) (hJ : Supported (insert e X) J)
    (o : Output (insert e X) J) :
    Output (insert r X) (singleFamily (restrict X J) (rawLink X e J) r) := by
  have out := renameOutput (markerMap e r) o
  have moved : Output (insert r X) (renameFamily (markerMap e r) J) :=
    Eq.mp (congrArg (fun T : Finset V => Output T (renameFamily (markerMap e r) J))
      (marker_ground X e r he hr)) out
  exact changeOutput moved (single_marker_family X e r J he hr hJ)

/-- Two isolated markers: actual twin strip followed by the renamed J main.
The source J is never replaced by its collapse endpoint. The s-coordinate
remains on the outer ground as a ghost after the strip. -/
def twinMarkerOutput (X : Finset V) (e r s : V) (J : Family V)
    (he : e ∉ X) (hr : r ∉ X) (hs : s ∉ insert r X)
    (hJ : Supported (insert e X) J) (o : Output (insert e X) J) :
    Output (insert s (insert r X))
      (twinFamily (restrict X J) (rawLink X e J) r s) :=
  twinOutput X (restrict X J) (rawLink X e J) r s
    (fun _ h => h.2) (fun _ h => h.1) hr hs
    (singleMarkerOutput X e r J he hr hJ o)

/-- Exact one-marker DELETION transition, retaining the full old ground. -/
theorem single_marker_delete (X : Finset V) (e r : V) (J : Family V)
    (hr : r ∉ X) :
    restrict X (singleFamily (restrict X J) (rawLink X e J) r) = restrict X J := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs | ⟨a, ha, t, ⟨htX, htJ⟩, rfl⟩, hsX⟩
    · exact hs
    · have ha0 : a = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hvr := Finset.mem_singleton.mp (ha hv)
        exact hr (hvr ▸ hsX (Finset.mem_union_left t hv))
      subst a
      exact ⟨by simpa only [Finset.empty_union] using J.lower (Finset.subset_insert _ _) htJ,
        hsX⟩
  · intro hs
    exact ⟨Or.inl hs, hs.2⟩

/-- Exact one-marker LINK transition. It filters crossing old rows; it is
not interchangeable with the deletion used in the preceding theorem. -/
theorem single_marker_link (X : Finset V) (e r : V) (J : Family V)
    (hr : r ∉ X) :
    rawLink X r (singleFamily (restrict X J) (rawLink X e J) r) = rawLink X e J := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hsX, hs | ⟨a, ha, t, ⟨htX, htJ⟩, hEq⟩⟩
    · exact False.elim (hr (hs.2 (Finset.mem_insert_self _ _)))
    · have hst : s ⊆ t := by
        intro v hv
        have huv : v ∈ a ∪ t := hEq ▸ Finset.mem_insert_of_mem hv
        exact (Finset.mem_union.mp huv).resolve_left (fun hva =>
          hr (Finset.mem_singleton.mp (ha hva) ▸ hsX hv))
      exact ⟨hsX, J.lower (Finset.insert_subset_insert e hst) htJ⟩
  · intro hs
    exact ⟨hs.1, Or.inr ⟨{r}, (show ({r} : Finset V) ⊆ {r} from le_rfl), s, hs, by simp⟩⟩

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
