/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryIsolated
   mirror-E: none(waiver:physical-history-isolated-labels)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Empty rows, unused original labels and isolated twin markers have actual tagged outputs and strips. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap

/-! SOURCE_ONLY_UNCOMPILED. D7's isolated cases. The twin constructor takes
the smaller ONE-marker output as a local induction input; no universal
physical-history theorem is asserted with such outputs as supplied fields.
The discarded twin stays on the declared outer ground as a ghost.
-/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated
open OriginalLabelTwoSum HistoryLeafCap
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Full simplex on its declared ground, UNIT precisely at empty ground. -/
def simplexOutput (W : Finset V) : Output W (delta W) := by
  classical
  by_cases hn : W.Nonempty
  · let p := hn.choose
    have hp : p ∈ W := hn.choose_spec
    exact .strong (coneCertificate W (delta W) p (fun _ h => h)
      (Finset.singleton_subset_iff.mpr hp) (fun s hs => Finset.insert_subset hp hs))
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact .unit (by rw [he])

/-- A surviving empty row supplies the FULL simplex, never just UNIT on a
nonempty ground. Duplicate original indices remain untouched. -/
def emptyRowOutput (r : Rows V) (c : r.chords) (hc : r.row c = ∅) :
    Output r.ground r.root := by
  have he : r.root = delta r.ground := by
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨d, hd⟩
      exact hd.trans Finset.sdiff_subset
    · intro hs
      exact ⟨c, by simpa only [hc, Finset.sdiff_empty] using hs⟩
  exact changeOutput (simplexOutput r.ground) he.symm

/-- No chord index means literal VOID, independently of the retained ghosts. -/
def noRowsOutput (r : Rows V) (h : IsEmpty r.chords) : Output r.ground r.root := by
  exact .void (by
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨c, _⟩
      exact False.elim (h.false c)
    · intro hs
      exact False.elim hs)

/-- An unmarked isolated label is a genuine cone apex whenever a row exists.
The empty index case is handled separately rather than materializing an apex. -/
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

/-- Literal two-isolated-marker family; D is the actual old deletion and L
the actual old link. The constructors below require only face support. -/
def twinFamily (D L : Family V) (r s : V) : Family V :=
  D ⊔ rawJoin (delta {r,s}) L

def singleFamily (D L : Family V) (r : V) : Family V :=
  D ⊔ rawJoin (delta {r}) L

private theorem twin_deletion (X : Finset V) (D L : Family V) (r s : V)
    (hD : Supported X D) (hL : Supported X L)
    (hr : r ∉ X) (hs : s ∉ insert r X) :
    deletion (project (twinFamily D L r s)) s = project (singleFamily D L r) := by
  have hsr : s ≠ r := fun he => hs (Finset.mem_insert.mpr (Or.inl he))
  have hsX : s ∉ X := fun h => hs (Finset.mem_insert_of_mem h)
  ext t
  constructor
  · rintro ⟨⟨hn, ht | ⟨a, ha, b, hb, rfl⟩⟩, hst⟩
    · exact ⟨hn, Or.inl ht⟩
    · refine ⟨hn, Or.inr ⟨a, ?_, b, hb, rfl⟩⟩
      intro v hv
      have hvs : v = r ∨ v = s := by simpa using ha hv
      exact Finset.mem_singleton.mpr (hvs.resolve_right (fun he =>
        hst (he ▸ Finset.mem_union_left b hv)))
  · rintro ⟨hn, ht | ⟨a, ha, b, hb, rfl⟩⟩
    · exact ⟨⟨hn, Or.inl ht⟩, fun h => hsX (hD t ht h)⟩
    · refine ⟨⟨hn, Or.inr ⟨a, ha.trans (by simp), b, hb, rfl⟩⟩, ?_⟩
      intro hst
      exact (Finset.mem_union.mp hst).elim
        (fun h => hsr (Finset.mem_singleton.mp (ha h))) (fun h => hsX (hL b hb h))

/-- The actual descending s-layer strip: (s+f, r+s+f). Domination supplies
each exact current coface proof, including f=empty when L contains it. -/
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

/-- D7 twin-marker reduction. Only the strictly smaller one-marker family is
an induction input. Main is strip then that main; C-only remains separate.
No deleted physical interface is restored and s stays a declared ghost. -/
def twinOutput (X : Finset V) (D L : Family V) (r s : V)
    (hD : Supported X D) (hL : Supported X L)
    (hr : r ∉ X) (hs : s ∉ insert r X)
    (o : Output (insert r X) (singleFamily D L r)) :
    Output (insert s (insert r X)) (twinFamily D L r s) := by
  have hsupport : Supported (insert s (insert r X)) (twinFamily D L r s) := by
    rintro t (ht | ⟨a, ha, b, hb, rfl⟩)
    · exact (hD t ht).trans (by simp)
    · exact Finset.union_subset (ha.trans (by simp)) ((hL b hb).trans (by simp))
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

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated
