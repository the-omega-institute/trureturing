# HistoryIsolated

## Abstract

Empty rows, unused original labels and isolated twin markers have actual tagged outputs and strips.

emptyRowOutput proves that a surviving empty row supplies the full simplex on the complete original ground, UNIT only when that ground is empty. noRowsOutput returns literal VOID. unusedLabelOutput chooses an actual cone apex only if a row exists. The twin family D union Delta(rs)*L has an actual descending s-layer strip to the single-marker family D union Delta(r)*L, using the selected vertex-domination constructor and a literal deletion equality. twinOutput appends the smaller single-marker main, preserves its separate core-only list, and retains s as a ghost on the outer ground. This is a local induction step, not a universal same-rank supplier theorem. Coordinate renaming of the earlier physical row model and the exhaustive forest induction remain to be constructed.

The constructions retain the lexical parameters and hypotheses of the paired Lean module.

**Definition 1.1 (simplexOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.simplexOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.simplexOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def simplexOutput (W : Finset V) : Output W (delta W) := by

  classical

  by_cases hn : W.Nonempty

  · let p := hn.choose

    have hp : p ∈ W := hn.choose_spec

    exact .strong (coneCertificate W (delta W) p (fun _ h => h)

      (Finset.singleton_subset_iff.mpr hp) (fun s hs => Finset.insert_subset hp hs))

  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn

    exact .unit (by rw [he])

**Definition 1.2 (emptyRowOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.emptyRowOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.emptyRowOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def emptyRowOutput (r : Rows V) (c : r.chords) (hc : r.row c = ∅) :

    Output r.ground r.root := by

  have he : r.root = delta r.ground := by

    apply SetLike.ext

    intro s

    constructor

    · rintro ⟨d, hd⟩

      exact hd.trans Finset.sdiff_subset

    · intro hs

      change s ⊆ r.ground at hs

      exact ⟨c, by simpa only [hc, Finset.sdiff_empty] using hs⟩

  exact changeOutput (simplexOutput r.ground) he.symm

**Definition 1.3 (noRowsOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.noRowsOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.noRowsOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def noRowsOutput (r : Rows V) (h : IsEmpty r.chords) : Output r.ground r.root := by

  exact .void (by

    apply SetLike.ext

    intro s

    constructor

    · rintro ⟨c, _⟩

      exact False.elim (h.false c)

    · intro hs

      exact False.elim hs)

**Definition 1.4 (unusedLabelOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.unusedLabelOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.unusedLabelOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def unusedLabelOutput (r : Rows V) (a : V) (ha : a ∈ r.ground)

    (havoid : ∀ c, a ∉ r.row c) : Output r.ground r.root := by

  classical

  by_cases hc : Nonempty r.chords

  · let c := Classical.choice hc

    have hp : ({a} : Finset V) ∈ r.root :=

      ⟨c, Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨ha, havoid c⟩)⟩

    exact .strong (coneCertificate r.ground r.root a r.root_supported hp (by

      rintro s ⟨d, hd⟩

      exact ⟨d, Finset.insert_subset (Finset.mem_sdiff.mpr ⟨ha, havoid d⟩) hd⟩))

  · exact noRowsOutput r ⟨fun c => hc ⟨c⟩⟩

**Definition 1.5 (twinFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def twinFamily (D L : Family V) (r s : V) : Family V :=

  D ⊔ rawJoin (delta {r,s}) L

**Definition 1.6 (singleFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.singleFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.singleFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def singleFamily (D L : Family V) (r : V) : Family V :=

  D ⊔ rawJoin (delta {r}) L

**Definition 1.7 (twinStrip).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinStrip`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def twinStrip (X : Finset V) (D L : Family V) (r s : V)

    (hD : Supported X D) (hL : Supported X L)

    (hr : r ∉ X) (hs : s ∉ insert r X) :

    Sequence (project (twinFamily D L r s)) (project (singleFamily D L r)) := by

  have hrs : r ≠ s := fun he => hs (by simp [he])

  have hsX : s ∉ X := fun h => hs (Finset.mem_insert_of_mem h)

  have hExt : FiniteVertexDominationCollapse.Extends

      (project (twinFamily D L r s)) r s := by

    rintro t ⟨hn, ht | ⟨a, ha, b, hb, rfl⟩⟩ hst

    · exact False.elim (hsX (hD t ht hst))

    · exact ⟨Finset.insert_nonempty _ _, Or.inr

        ⟨insert r a, Finset.insert_subset (by simp) ha, b, hb, by simp⟩⟩

  exact (FiniteVertexDominationCollapse.sequence _ r s hrs hExt).cast rfl

    (twin_deletion X D L r s hD hL hr hs)

**Definition 1.8 (twinOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated; open OriginalLabelTwoSum HistoryLeafCap; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap. 

Exact public SOURCE declaration and body:

def twinOutput (X : Finset V) (D L : Family V) (r s : V)

    (hD : Supported X D) (hL : Supported X L)

    (hr : r ∉ X) (hs : s ∉ insert r X)

    (o : Output (insert r X) (singleFamily D L r)) :

    Output (insert s (insert r X)) (twinFamily D L r s) := by

  have hsupport : Supported (insert s (insert r X)) (twinFamily D L r s) := by

    rintro t (ht | ⟨a, ha, b, hb, rfl⟩)

    · exact (hD t ht).trans ((Finset.subset_insert r X).trans (Finset.subset_insert s _))

    · exact Finset.union_subset (ha.trans (by intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _); exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hv)))) ((hL b hb).trans ((Finset.subset_insert r X).trans (Finset.subset_insert s _)))

  have h0 : (∅ : Finset V) ∈ twinFamily D L r s ↔ ∅ ∈ singleFamily D L r := by

    constructor

    · rintro (h | ⟨a, ha, b, hb, he⟩)

      · exact Or.inl h

      · exact Or.inr ⟨∅, Finset.empty_subset _, ∅,

          L.lower (Finset.empty_subset _) hb, by simp⟩

    · rintro (h | ⟨a, ha, b, hb, he⟩)

      · exact Or.inl h

      · exact Or.inr ⟨∅, Finset.empty_subset _, ∅,

          L.lower (Finset.empty_subset _) hb, by simp⟩

  exact prependOutput _ _ _ hsupport h0 (twinStrip X D L r s hD hL hr hs)

    (widenOutput (Finset.subset_insert _ _) o)

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.emptyRowOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.noRowsOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.simplexOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.singleFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.twinStrip`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated.unusedLabelOutput`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap](HistoryLeafCap.md)
