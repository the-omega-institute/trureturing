# HistoryCorners

## Abstract

Original indexed chord rows filter under links and project under deletions, without losing ghost labels or empty rows.

Linking filters the ORIGINAL chord index type by disjointness; deleting projects every surviving row. The augmented-family equality retains singleton and empty rows, duplicate chord indices, and all residual ghosts. corner_root requires the linked mask to lie in the original ground. corner_compose requires the next link mask to lie in the residual ground. singleton_cap is consumed by HistoryLeafCap.singletonOutput. These are actual set equalities, not a replacement of the root by a homology model. The physical-history graph/path induction is not constructed here.

The constructions retain the lexical parameters and hypotheses of the paired Lean module.

**Definition 1.1 (residual).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.residual`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

def residual (W A B : Finset V) : Finset V := W \ (A ∪ B)

**Definition 1.2 (corner).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

def corner (W A B : Finset V) (K : Family V) : Family V where

  carrier := {s | s ⊆ residual W A B ∧ s ∪ A ∈ K}

  lower' := by

    rintro s t h ⟨hs, hK⟩

    exact ⟨h.trans hs, K.lower (Finset.union_subset_union h le_rfl) hK⟩

**Definition 1.3 (cornerRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.cornerRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.cornerRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

def cornerRows (r : Rows V) (A B : Finset V) : Rows V where

  ground := residual r.ground A B

  chords := {c : r.chords // Disjoint (r.row c) A}

  row c := r.row c.1 \ B

  row_supported := by

    intro c x hx

    obtain ⟨hxq, hxB⟩ := Finset.mem_sdiff.mp hx

    refine Finset.mem_sdiff.mpr ⟨r.row_supported c.1 hxq, ?_⟩

    intro hxAB

    rcases Finset.mem_union.mp hxAB with hxA | hxB'

    · exact Finset.disjoint_left.mp c.2 hxq hxA

    · exact hxB hxB'

**Theorem 1.4 (corner_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

theorem corner_root (r : Rows V) (A B : Finset V) (hA : A ⊆ r.ground) :

    corner r.ground A B r.root = (cornerRows r A B).root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨hs, c, hc⟩

    obtain ⟨hd, ht⟩ := (corner_subset_iff r.ground A B (r.row c) s hA).mp ⟨hc, hs⟩

    exact ⟨⟨c, hd⟩, ht⟩

  · rintro ⟨c, hc⟩

    obtain ⟨ht, hs⟩ := (corner_subset_iff r.ground A B (r.row c.1) s hA).mpr ⟨c.2, hc⟩

    exact ⟨hs, c.1, ht⟩

**Theorem 1.5 (corner_compose).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

theorem corner_compose (W A B C D : Finset V) (K : Family V)

    (hC : C ⊆ residual W A B) :

    corner (residual W A B) C D (corner W A B K) =

      corner W (A ∪ C) (B ∪ D) K := by

  apply SetLike.ext

  intro s

  change (s ⊆ residual (residual W A B) C D ∧

      s ∪ C ⊆ residual W A B ∧ (s ∪ C) ∪ A ∈ K) ↔

    s ⊆ residual W (A ∪ C) (B ∪ D) ∧ s ∪ (A ∪ C) ∈ K

  have hground : residual (residual W A B) C D =

      residual W (A ∪ C) (B ∪ D) := by

    ext x

    simp only [residual, Finset.mem_sdiff, Finset.mem_union]

    tauto

  rw [hground]

  have hsground : ∀ s, s ⊆ residual W (A ∪ C) (B ∪ D) →

      s ⊆ residual W A B := by

    intro s hs x hx

    obtain ⟨hxW, hn⟩ := Finset.mem_sdiff.mp (hs hx)

    refine Finset.mem_sdiff.mpr ⟨hxW, ?_⟩

    simpa only [Finset.mem_union] using

      (show ¬ (x ∈ A ∨ x ∈ B) from fun h => hn (by

        simp only [Finset.mem_union]; tauto))

  have hu : (s ∪ C) ∪ A = s ∪ (A ∪ C) := by

    ext x; simp only [Finset.mem_union]; tauto

  rw [hu]

  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h =>

    ⟨h.1, Finset.union_subset (hsground s h.1) hC, h.2⟩⟩

**Definition 1.6 (avoiding).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.avoiding`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.avoiding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

def avoiding (r : Rows V) (a : V) : Rows V where

  ground := r.ground.erase a

  chords := {c : r.chords // a ∉ r.row c}

  row c := r.row c.1

  row_supported := by

    intro c x hx

    exact Finset.mem_erase.mpr ⟨fun he => c.2 (he ▸ hx), r.row_supported c.1 hx⟩

**Theorem 1.7 (singleton_cap).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.singleton_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.singleton_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners; open OriginalLabelTwoSum; variable {V : Type*} [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.Raw. 

Exact public SOURCE declaration and body:

theorem singleton_cap (r : Rows V) (a : V) (ha : a ∈ r.ground)

    (c : r.chords) (hc : r.row c = {a}) :

    r.root = delta (r.ground.erase a) ⊔

      rawJoin (delta {a}) (avoiding r a).root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨d, hd⟩

    by_cases has : a ∈ s

    · right

      have had : a ∉ r.row d := (Finset.mem_sdiff.mp (hd has)).2

      refine ⟨{a}, (by change ({a} : Finset V) ⊆ {a}; exact le_rfl), s.erase a, ⟨⟨d, had⟩, ?_⟩, ?_⟩

      · intro x hx

        obtain ⟨hxa, hxs⟩ := Finset.mem_erase.mp hx

        obtain ⟨hxW, hxq⟩ := Finset.mem_sdiff.mp (hd hxs)

        exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hxW⟩, hxq⟩

      · simpa using (Finset.insert_erase has).symm

    · left

      intro x hx

      exact Finset.mem_erase.mpr ⟨fun he => has (he ▸ hx),

        (Finset.mem_sdiff.mp (hd hx)).1⟩

  · rintro (hs | ⟨x, hx, t, ⟨d, ht⟩, rfl⟩)

    · refine ⟨c, ?_⟩

      intro x hx

      obtain ⟨hxa, hxW⟩ := Finset.mem_erase.mp (hs hx)

      exact Finset.mem_sdiff.mpr ⟨hxW, by simpa only [hc, Finset.mem_singleton] using hxa⟩

    · refine ⟨d.1, ?_⟩

      intro y hy

      rcases Finset.mem_union.mp hy with hyx | hyt

      · have he : y = a := Finset.mem_singleton.mp (hx hyx)

        subst y

        exact Finset.mem_sdiff.mpr ⟨ha, d.2⟩

      · obtain ⟨hyW, hyq⟩ := Finset.mem_sdiff.mp (ht hyt)

        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hyW).2, hyq⟩

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.avoiding`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.cornerRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_compose`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.corner_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.residual`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners.singleton_cap`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Raw](Raw.md)
