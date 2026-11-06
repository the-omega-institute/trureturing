/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistorySeed
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistorySeed
   mirror-E: none(waiver:physical-history-seed)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Every original-label K4 seed corner has its exact VOID, UNIT, or point-core output, including retained ambient ghosts. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
import D5.S3.Geometry.OriginalLabelTwoSum.Graph
import D5.S3.Geometry.OriginalLabelTwoSum.Rename

/-! SOURCE_ONLY_UNCOMPILED. This is the complete history-length-zero case of
D14, with arbitrary original coordinate embedding and arbitrary masks. It is
not a replacement for the strictly earlier-history induction step.
-/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed
open OriginalLabelTwoSum HistoryCorners HistoryLeafCap
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The raw empty face is present even when there are no retained vertices. -/
def discrete (W : Finset V) : Family V where
  carrier := {s | s ⊆ W ∧ s.card ≤ 1}
  lower' := fun _ _ h hs => ⟨h.trans hs.1, (Finset.card_le_card h).trans hs.2⟩

private theorem small_face (s : Finset V) (h : s.card ≤ 1) :
    s = ∅ ∨ ∃ a, s = {a} := by
  by_cases hn : s.Nonempty
  · obtain ⟨a, ha⟩ := hn
    right
    refine ⟨a, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr ha)⟩
    intro b hb
    by_cases he : b = a
    · exact Finset.mem_singleton.mpr he
    · have hp : ({b,a} : Finset V) ⊆ s := by simp [ha, hb]
      have hc := (Finset.card_le_card hp).trans h
      have hc2 : ({b,a} : Finset V).card = 2 := by simp [he]
      omega
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)

private theorem proper_singleton_empty {a : V} {s : Finset V} (h : s ⊂ {a}) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  have he : v = a := Finset.mem_singleton.mp (h.subset hv)
  exact h.ne (Finset.Subset.antisymm h.subset (Finset.singleton_subset_iff.mpr (he ▸ hv)))

private def discreteCertificate (W : Finset V) (p : V) (hp : p ∈ W) :
    Certificate W (discrete W) := by
  classical
  let Q := (W.erase p).image (fun q => ({q} : Finset V))
  have hEnd : discrete W = endpoint (delta {p}) Q := by
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨hs, hc⟩
      rcases small_face s hc with rfl | ⟨a, rfl⟩
      · exact Or.inl (Finset.empty_subset _)
      · by_cases he : a = p
        · subst a; exact Or.inl le_rfl
        · exact Or.inr ⟨{a}, Finset.mem_image.mpr ⟨a,
            Finset.mem_erase.mpr ⟨he, hs (by simp)⟩, rfl⟩, le_rfl⟩
    · rintro (hs | ⟨q, hq, hs⟩)
      · exact ⟨hs.trans (Finset.singleton_subset_iff.mpr hp),
          (Finset.card_le_card hs).trans (by simp)⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
        exact ⟨hs.trans (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mp ha).2),
          (Finset.card_le_card hs).trans (by simp)⟩
  refine {
    supported := fun _ h => h.1
    core := delta {p}
    critical := Q
    vertex := p
    vertex_mem := le_rfl
    core_supported := fun _ h => h.trans (Finset.singleton_subset_iff.mpr hp)
    critical_supported := ?_
    cells := ?_
    main := (Sequence.refl (project (discrete W))).cast rfl (congrArg project hEnd)
    separate := Sequence.refl _ }
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.singleton_subset_iff.mpr (Finset.mem_erase.mp ha).2
  · constructor
    · intro q hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      simp
    · intro q hq hs
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_erase.mp ha).1 (Finset.mem_singleton.mp (hs (by simp)))
    · intro q hq t ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      rw [proper_singleton_empty ht]
      exact Finset.empty_subset _
    · intro q hq t ht hqt
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
      exact congrArg (fun a => ({a} : Finset V))
        (Finset.mem_singleton.mp (hqt (by simp)))

private def discreteOutput (W : Finset V) : Output W (discrete W) := by
  classical
  by_cases hn : W.Nonempty
  · exact .strong (discreteCertificate W hn.choose hn.choose_spec)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst W
    exact .unit (by
      apply SetLike.ext; intro s
      exact ⟨fun h => h.1, fun h => ⟨h, by
        have he : s = ∅ := Finset.subset_empty.mp h
        simp [he]⟩⟩)

/-- Every mask of a discrete raw family, not just a finite list of examples.
With a nonempty valid link the answer is UNIT on the full residual ground;
two or more linked labels give VOID. With no link the remaining vertices give
an actual point core and the other singleton criticals, both lists empty. -/
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
            apply Finset.eq_empty_iff_forall_not_mem.mpr
            intro v hv
            rcases small_face (s ∪ A) hc with he | ⟨q, he⟩
            · have hmem : a ∈ s ∪ A := Finset.mem_union_right _ ha
              rw [he] at hmem
              exact Finset.not_mem_empty _ hmem
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

private theorem rename_discrete {U : Type*} [Fintype U] [DecidableEq U]
    (f : U ↪ V) (W : Finset U) : renameFamily f (discrete W) = discrete (W.image f) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    refine ⟨Finset.image_subset_image ht, ?_⟩
    rcases small_face t hc with rfl | ⟨a, rfl⟩ <;> simp
  · rintro ⟨hs, hc⟩
    rcases small_face s hc with rfl | ⟨v, rfl⟩
    · exact ⟨∅, ⟨Finset.empty_subset _, by simp⟩, by simp⟩
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hs (by simp))
      exact ⟨{a}, ⟨Finset.singleton_subset_iff.mpr ha, by simp⟩, by simp [he]⟩

/-- The actual K4 marked star and its actual computed chord paths, transported
by the original coordinate embedding. Ambient labels outside the tree remain
ghosts. There is no hypothesis supplying a seed-corner output. -/
def seedCornerOutput (f : K4.SeedLabel ↪ V) (A B : Finset V)
    (hA : A ⊆ (Finset.univ : Finset K4.SeedLabel).image f) :
    Output (residual ((Finset.univ : Finset K4.SeedLabel).image f) A B)
      (corner ((Finset.univ : Finset K4.SeedLabel).image f) A B
        (renameFamily f K4.seedGraphData.rows.root)) := by
  have hseed : K4.root = discrete (Finset.univ : Finset K4.SeedLabel) := by
    apply SetLike.ext
    exact (by decide : ∀ s : Finset K4.SeedLabel,
      s ∈ K4.root ↔ s ∈ discrete (Finset.univ : Finset K4.SeedLabel))
  rw [K4.seedOriginalRoot, hseed, rename_discrete]
  exact discreteCornerOutput _ A B hA

end D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed
