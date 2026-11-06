/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryCorners
   mirror-E: none(waiver:physical-history-corners)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Original indexed chord rows filter under links and project under deletions, without losing ghost labels or empty rows. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Raw

/-! SOURCE_ONLY_UNCOMPILED. This is the literal-row part of D2--D3 of the
terminal independent all-corner proof. It is not a physical-history constructor
and has no kernel, native, registration, or admission receipt.

`cornerRows` retains the original chord index as a subtype. In particular it
neither removes duplicate rows nor replaces the residual ground by its support.
The cap reduction at the end is consumed by `HistoryLeafCap.singletonOutput`.
-/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
open OriginalLabelTwoSum
variable {V : Type*} [DecidableEq V]

/-- Every label outside the two masks remains, even if it is a ghost. -/
def residual (W A B : Finset V) : Finset V := W \ (A ∪ B)

/-- Augmented link of A, followed by deletion of B, on the original ground. -/
def corner (W A B : Finset V) (K : Family V) : Family V where
  carrier := {s | s ⊆ residual W A B ∧ s ∪ A ∈ K}
  lower' := by
    rintro s t h ⟨hs, hK⟩
    exact ⟨h.trans hs, K.lower (Finset.union_subset_union h le_rfl) hK⟩

/-- Link filters indices; deletion projects every surviving row, including
singleton and empty projections. No original row index is identified. -/
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

private theorem corner_subset_iff (W A B q s : Finset V) (hA : A ⊆ W) :
    s ∪ A ⊆ W \ q ∧ s ⊆ residual W A B ↔
      Disjoint q A ∧ s ⊆ residual W A B \ (q \ B) := by
  constructor
  · rintro ⟨h, hs⟩
    refine ⟨Finset.disjoint_left.mpr (fun x hxq hxA =>
      (Finset.mem_sdiff.mp (h (Finset.mem_union_right _ hxA))).2 hxq), ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hs hx, fun hxq =>
      (Finset.mem_sdiff.mp (h (Finset.mem_union_left _ hx))).2
        (Finset.mem_sdiff.mp hxq).1⟩
  · rintro ⟨hd, hs⟩
    refine ⟨?_, fun x hx => (Finset.mem_sdiff.mp (hs hx)).1⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxA
    · obtain ⟨hxR, hxq⟩ := Finset.mem_sdiff.mp (hs hxs)
      obtain ⟨hxW, hxAB⟩ := Finset.mem_sdiff.mp hxR
      refine Finset.mem_sdiff.mpr ⟨hxW, ?_⟩
      intro hq
      exact hxq (Finset.mem_sdiff.mpr ⟨hq, fun hB =>
        hxAB (Finset.mem_union_right _ hB)⟩)
    · exact Finset.mem_sdiff.mpr ⟨hA hxA, fun hq =>
        Finset.disjoint_left.mp hd hq hxA⟩

/-- Exact D2 row identity. This is an equality of augmented families, so VOID
and UNIT cannot be identified by their common nonempty projection. -/
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

/-- Composing genuine residual corners unions the original masks. No
coordinate relabeling occurs and the residual ground is not recomputed from
the faces that happen to remain. -/
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

/-- The surviving rows avoiding a singleton, on the ground with that label
removed. Rows containing it become redundant only in the cap BASE. -/
def avoiding (r : Rows V) (a : V) : Rows V where
  ground := r.ground.erase a
  chords := {c : r.chords // a ∉ r.row c}
  row c := r.row c.1
  row_supported := by
    intro c x hx
    exact Finset.mem_erase.mpr ⟨fun he => c.2 (he ▸ hx), r.row_supported c.1 hx⟩

/-- The singleton reduction retains a as a cap coordinate. It does not
delete the constraint or the label, and it preserves the raw empty face. -/
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
      refine ⟨{a}, le_rfl, s.erase a, ⟨⟨d, had⟩, ?_⟩, ?_⟩
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

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
