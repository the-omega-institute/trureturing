# HistoryCertificate

## Abstract

Actual mixed-history roots contain a singleton and yield their computed strong main and separate-core sequences.

Every prescribed PhysicalHistory.MixedHistory n G g has a genuine singleton face in the literal raw root g.rows.root, including in the original ambient type V with its inactive ghosts. The seed has three tree-edge labels and singleton facets f 0, f 1, f 2; it does not have four tree-edge labels. An attachment uses mixed_ground_card old and card_erase_add_one at the retained port to obtain an old label in old.ground.erase i.e. Index 1 : Fin i.width exists at every width at least 3 and differs from the interface index 0. physicalWheelStep_rows_right identifies its actual surviving physical row. rimRows.row_supported and freshness place that row wholly in the fresh right ground, away from the chosen old label. This proves singleton membership in the actual raw complement root before any nonempty projection. No row index, duplicate row, projected empty or singleton row, or ghost coordinate is discarded.

certificate consumes exactly HistoryRecursion.allCornersOutput h at A = B = empty. Its private empty_corner proof uses actual root support, and the residual is the complete g.ground. The private strongOfSingleton eliminator contradicts literal VOID and literal UNIT using the derived singleton; it returns the strong branch itself. The resulting Certificate g.ground g.rows.root keeps its computed core, critical family and coordinate vertex, critical top absence, every proper boundary, antichain, and both ordered native sequences with real evolving cofaces. main has type Sequence (project g.rows.root) (project (endpoint c.core c.critical)); separate has type Sequence (project c.core) (project (delta {c.vertex})). The latter starts at C ALONE. No requested Certificate, Output, collapse, supplied singleton, leaf, classification or core supplier is an input of the public history declarations.

Existing original-coordinate geometric consumers apply directly to c.main and c.separate: FiniteRelativeSimplicialCollapse.Sequence.collapseHomotopy is relative from the identity to inclusion composed with sequenceRetraction; collapseHomotopy_fixed fixes every point of the full final realization; sequenceRetraction_inclusion recovers every final point after the literal coordinate inclusion. Sequence.pairs and frames are the actual ordered native objects, and pairs_cast and frames_cast preserve them under equality transport. FiniteConeCollapse.realization_mem_iff supplies a faceSimplex whose outside coordinates are zero; support in g.ground therefore keeps every inactive coordinate zero at every homotopy time. FiniteConeUnionWedge.realizationInclusion keeps the same coordinate function. This is reuse of existing APIs, with no additional renamed application theorem or homotopy wrapper. A general sphere-wedge identification of the multi-critical endpoint is not supplied by these SDR APIs and is not asserted here.

The singleton construction uses the original retained endpoint. Availability of an unrestricted arbitrary-plane certificate supplier is a separate mathematical obligation.

## Source text

Literal source, not compiled declaration metadata. Common context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCertificate; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory; variable {V : Type*} [Fintype V] [DecidableEq V]. Import: D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion. Private consumed plumbing, with no private DeclarationHandle: literal source declarations and bodies:

private theorem empty_corner {G : Type} (g : GraphData G V) :

    corner g.ground ∅ ∅ g.rows.root = g.rows.root := by

  apply SetLike.ext

  intro s

  change (s ⊆ HistoryCorners.residual g.ground ∅ ∅ ∧ s ∪ ∅ ∈ g.rows.root) ↔ s ∈ g.rows.root

  simp only [HistoryCorners.residual, Finset.union_empty, Finset.sdiff_empty]

  exact ⟨fun hs => hs.2, fun hs => ⟨g.rows.root_supported s hs, hs⟩⟩

Definitions and proofs are in the paired Lean module.

private def strongOfSingleton {W : Finset V} {K : Family V}

    (o : Output W K) (has : ∃ x : V, ({x} : Finset V) ∈ K) : Certificate W K := by

  cases o with

  | void he =>

      apply False.elim

      obtain ⟨x, hx⟩ := has

      rw [he] at hx

      exact hx

  | unit he =>

      apply False.elim

      obtain ⟨x, hx⟩ := has

      rw [he] at hx

      change ({x} : Finset V) ⊆ ∅ at hx

      exact Finset.notMem_empty x (hx (Finset.mem_singleton_self x))

  | strong c => exact c

**Theorem 1.1 (root_has_singleton).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.root_has_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.root_has_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not compiled declaration metadata. Common context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCertificate; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory; variable {V : Type*} [Fintype V] [DecidableEq V]. Import: D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion. Exact public SOURCE declaration and body:

theorem root_has_singleton {n : Nat} {G : Type} {g : GraphData G V}

    (h : MixedHistory n G g) : ∃ x : V, ({x} : Finset V) ∈ g.rows.root := by

  cases h with

  | seed f =>

      refine ⟨f 0, ?_⟩

      rw [seed_root]

      exact Or.inl (Or.inl (show ({f 0} : Finset V) ⊆ {f 0} from le_rfl))

  | @attach n G g old i =>

      have hcard := mixed_ground_card old

      have herase := Finset.card_erase_add_one i.retained

      have hold : (g.ground.erase i.e).Nonempty :=

        Finset.card_pos.mp (by omega)

      obtain ⟨x, hx⟩ := hold

      let d : Fin i.width := ⟨1, by have := i.atLeastThree; omega⟩

      have hd : d ≠ AllMWheel.interfaceRow i.width i.atLeastThree := by

        intro heq

        have hv := congrArg Fin.val heq

        change 1 = 0 at hv

        omega

      let c := (physicalWheelStep_chords g i).symm (.inr ⟨d, hd⟩)

      have hrow : (physicalWheelStep g i).data.rows.row c ⊆

          (AllMWheel.ground i.width).image i.labels := by

        change (physicalWheelStep g i).data.rows.row

          ((physicalWheelStep_chords g i).symm (.inr ⟨d, hd⟩)) ⊆ _

        rw [physicalWheelStep_rows_right]

        exact Finset.image_subset_image

          ((AllMWheel.rimRows i.width (by have := i.atLeastThree; omega)).row_supported d)

      have hxrow : x ∉ (physicalWheelStep g i).data.rows.row c := by

        intro hxc

        exact Finset.disjoint_left.mp i.fresh (Finset.mem_of_mem_erase hx) (hrow hxc)

      refine ⟨x, c, Finset.singleton_subset_iff.mpr ?_⟩

      refine Finset.mem_sdiff.mpr ⟨?_, hxrow⟩

      change x ∈ g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels

      exact Finset.mem_union_left _ hx

**Definition 1.2 (certificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.certificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not compiled declaration metadata. Common context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCertificate; open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory; variable {V : Type*} [Fintype V] [DecidableEq V]. Import: D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion. Exact public SOURCE declaration and body:

def certificate {n : Nat} {G : Type} {g : GraphData G V}

    (h : MixedHistory n G g) : Certificate g.ground g.rows.root := by

  have o := HistoryRecursion.allCornersOutput h ∅ ∅

    (Finset.empty_subset _) (Finset.empty_subset _) (by simp)

  have hground : HistoryCorners.residual g.ground ∅ ∅ = g.ground := by

    simp only [HistoryCorners.residual, Finset.union_empty, Finset.sdiff_empty]

  rw [hground, empty_corner g] at o

  exact strongOfSingleton o (root_has_singleton h)

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.certificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate.root_has_singleton`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryRecursion](HistoryRecursion.md)
