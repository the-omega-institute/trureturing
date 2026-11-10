# HistoryMarkers

## Abstract

Isolated markers use actual original-coordinate swaps and renamed native certificates of the earlier model.

markerMap is the actual injective coordinate swap e/r, fixing every old label of X, including ghosts. single_marker_family identifies the renamed actual earlier J with its literal deletion/link one-marker family. renameOutput uses the existing renameCertificate and renameSequence for actual native lists. twinMarkerOutput executes the original twin strip and then this renamed J output, retaining the other marker as a ground ghost. The one-marker link and deletion equations are proved separately. These are local constructors from a legitimate earlier-model output, not a universal supplier premise.

 No full universal history or broad-goal completion is asserted.

**Definition 1.1 (markerMap).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.markerMap`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.markerMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

def markerMap (e r : V) : V ↪ V := (Equiv.swap e r).toEmbedding

**Definition 1.2 (renameOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.renameOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.renameOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

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

**Theorem 1.3 (single_marker_family).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_family`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

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

**Definition 1.4 (singleMarkerOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.singleMarkerOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.singleMarkerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

def singleMarkerOutput (X : Finset V) (e r : V) (J : Family V)

    (he : e ∉ X) (hr : r ∉ X) (hJ : Supported (insert e X) J)

    (o : Output (insert e X) J) :

    Output (insert r X) (singleFamily (restrict X J) (rawLink X e J) r) := by

  have out := renameOutput (markerMap e r) o

  have moved : Output (insert r X) (renameFamily (markerMap e r) J) :=

    Eq.mp (congrArg (fun T : Finset V => Output T (renameFamily (markerMap e r) J))

      (marker_ground X e r he hr)) out

  exact changeOutput moved (single_marker_family X e r J he hr hJ)

**Definition 1.5 (twinMarkerOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.twinMarkerOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.twinMarkerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

def twinMarkerOutput (X : Finset V) (e r s : V) (J : Family V)

    (he : e ∉ X) (hr : r ∉ X) (hs : s ∉ insert r X)

    (hJ : Supported (insert e X) J) (o : Output (insert e X) J) :

    Output (insert s (insert r X))

      (twinFamily (restrict X J) (rawLink X e J) r s) :=

  twinOutput X (restrict X J) (rawLink X e J) r s

    (fun _ h => h.2) (fun _ h => h.1) hr hs

    (singleMarkerOutput X e r J he hr hJ o)

**Theorem 1.6 (single_marker_delete).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_delete`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

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

**Theorem 1.7 (single_marker_link).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_link`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_link` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated, D5.S3.Geometry.OriginalLabelTwoSum.Rename. Exact public declaration and proof/source body:

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

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.markerMap`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.renameOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.singleMarkerOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_delete`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_family`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.single_marker_link`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryMarkers.twinMarkerOutput`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated](HistoryIsolated.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Rename](Rename.md)
