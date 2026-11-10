# HistorySeed

## Abstract

Every original-label K4 seed corner has its exact VOID, UNIT, or point-core output, including retained ambient ghosts.

discreteCornerOutput covers arbitrary masks on a finite discrete family: an empty link leaves exactly the retained vertices; one valid linked vertex leaves UNIT with every residual coordinate a ghost; at least two linked vertices leave VOID. A nonempty discrete output chooses a coordinate point core and the other singleton criticals, with both actual lists empty. seedCornerOutput uses K4.seedOriginalRoot, the actual seed's chord paths, and an arbitrary coordinate embedding into the original ambient type. decide is confined to identifying this fixed K4 base with its three-label discrete family. This is the history-length-zero base, not a proof by finite testing of positive histories.

The constructions retain the lexical parameters and hypotheses of the paired Lean module.

**Definition 1.1 (discrete).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discrete`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discrete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.Graph, D5.S3.Geometry.OriginalLabelTwoSum.Rename. 

Exact public SOURCE declaration and body:

def discrete (W : Finset V) : Family V where

  carrier := {s | s ⊆ W ∧ s.card ≤ 1}

  lower' := fun _ _ h hs => ⟨h.trans hs.1, (Finset.card_le_card h).trans hs.2⟩

**Definition 1.2 (discreteCornerOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discreteCornerOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discreteCornerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.Graph, D5.S3.Geometry.OriginalLabelTwoSum.Rename. 

Exact public SOURCE declaration and body:

def discreteCornerOutput (W A B : Finset V) (hA : A ⊆ W) :

    Output (residual W A B) (corner W A B (discrete W)) := by

  classical

  by_cases hA0 : A = ∅

  · subst A

    have he : corner W ∅ B (discrete W) = discrete (residual W ∅ B) := by

      apply SetLike.ext; intro s

      change (s ⊆ residual W ∅ B ∧ s ∪ ∅ ⊆ W ∧ (s ∪ ∅).card ≤ 1) ↔ _

      simp only [Finset.union_empty]

      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h =>

        ⟨h.1, h.1.trans Finset.sdiff_subset, h.2⟩⟩

    rw [he]

    exact discreteOutput _

  · by_cases hcard : A.card ≤ 1

    · have hAn : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0

      let a := hAn.choose

      have ha : a ∈ A := hAn.choose_spec

      exact .unit (by

        apply SetLike.ext; intro s

        constructor

        · rintro ⟨hs, hW, hc⟩

          have hs0 : s = ∅ := by

            apply Finset.eq_empty_iff_forall_notMem.mpr

            intro v hv

            rcases small_face (s ∪ A) hc with he | ⟨q, he⟩

            · have hmem : a ∈ s ∪ A := Finset.mem_union_right _ ha

              rw [he] at hmem

              exact (Finset.notMem_empty _ hmem)

            · have haq : a = q := Finset.mem_singleton.mp (he ▸ Finset.mem_union_right s ha)

              have hvq : v = q := Finset.mem_singleton.mp (he ▸ Finset.mem_union_left A hv)

              have hvA : v ∈ A := (hvq.trans haq.symm).symm ▸ ha

              exact (Finset.mem_sdiff.mp (hs hv)).2 (Finset.mem_union_left _ hvA)

          simp [hs0]

        · intro hs

          have he : s = ∅ := Finset.subset_empty.mp hs

          subst s

          exact ⟨Finset.empty_subset _, by simpa using hA, by simpa using hcard⟩)

    · exact .void (by

        apply SetLike.ext; intro s

        constructor

        · rintro ⟨hs, hW, hc⟩

          exact False.elim (hcard ((Finset.card_le_card Finset.subset_union_right).trans hc))

        · intro h; exact False.elim h)

**Definition 1.3 (seedCornerOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.seedCornerOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.seedCornerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.Graph, D5.S3.Geometry.OriginalLabelTwoSum.Rename. 

Exact public SOURCE declaration and body:

def seedCornerOutput (f : K4.SeedLabel ↪ V) (A B : Finset V)

    (hA : A ⊆ (Finset.univ : Finset K4.SeedLabel).image f) :

    Output (residual ((Finset.univ : Finset K4.SeedLabel).image f) A B)

      (corner ((Finset.univ : Finset K4.SeedLabel).image f) A B

        (renameFamily f K4.seedGraphData.rows.root)) := by

  have hseed : K4.root = discrete (Finset.univ : Finset K4.SeedLabel) := by

    apply SetLike.ext

    intro s

    simp only [K4.root, discrete, facets, LowerSet.mem_mk, Set.mem_setOf_eq]

    revert s

    decide

  rw [K4.seedOriginalRoot, hseed, rename_discrete]

  exact discreteCornerOutput _ A B hA

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discrete`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.discreteCornerOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed.seedCornerOutput`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Graph](Graph.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap](HistoryLeafCap.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Rename](Rename.md)
