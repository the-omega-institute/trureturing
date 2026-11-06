/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryAttachment
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryAttachment
   mirror-E: none(waiver:physical-history-bounded-attachment)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Size-bounded outside simplex attachment computes actual emitted main pairs and original-order separate core replay. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
import D5.S3.Geometry.FinitePrescribedPairProtection

/-! SOURCE_ONLY_UNCOMPILED. D8 of the terminal ordinary proof. This file
consumes the selected forward-scan owner, without changing its decisions or
reversing its skipped list. Restriction removes OLD critical tops from the
standalone replay domain. The returned core list starts on that core ALONE.

The size hypothesis is a sufficient attachment condition. It is not a claim
that every attachment or every strong certificate must satisfy this bound.
This local constructor does not close the physical-history induction.
-/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment
open OriginalLabelTwoSum HistoryLeafCap
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FinitePrescribedPairProtection
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restrict an actual sequence to a fixed subcomplex containing every pair
upper. Each step has its exact intersected current domain. -/
def restrictSequence {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (A : PreAbstractSimplicialComplex V)
    (hu : ∀ P ∈ S.pairs, P.upper ∈ A) : Sequence (K ⊓ A) (L ⊓ A) := by
  revert hu
  induction S with
  | refl K => intro hu; exact Sequence.refl _
  | step P T ih =>
      intro hu
      let Q := restrictPair P (P.ambient ⊓ A) inf_le_left
        ⟨P.upper_mem, hu P (by simp [Sequence.pairs])⟩
      have hret : Q.retained = P.retained ⊓ A := by
        ext s
        change ((s ∈ P.ambient ∧ s ∈ A) ∧ ¬ P.lower ⊆ s) ↔
          ((s ∈ P.ambient ∧ ¬ P.lower ⊆ s) ∧ s ∈ A)
        tauto
      exact Sequence.step Q ((ih (fun R hR =>
        hu R (by simp only [Sequence.pairs, List.mem_cons]; exact Or.inr hR))).cast
          hret.symm rfl)

/-- Restriction changes current domains, never the source pair order or labels. -/
theorem restrictSequence_pairs {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (A : PreAbstractSimplicialComplex V)
    (hu : ∀ P ∈ S.pairs, P.upper ∈ A) :
    (restrictSequence S A hu).pairs.map (fun P => (P.lower, P.upper)) =
      S.pairs.map (fun P => (P.lower, P.upper)) := by
  revert hu
  induction S with
  | refl K => intro hu; rfl
  | step P T ih =>
      intro hu
      simp [restrictSequence, Sequence.pairs, Sequence.pairs_cast,
        restrictPair, CollapsePair.upper, ih]

private theorem skipped_mem (ps : List (CollapsePair V)) (H : Finset (Finset V))
    {P : CollapsePair V} (hP : P ∈ skipped ps H) : P ∈ ps := by
  induction ps generalizing H with
  | nil => simp [skipped] at hP
  | cons Q ps ih =>
      apply List.mem_cons.mpr
      by_cases hb : blocked H Q
      · simp only [skipped, if_pos hb, List.mem_cons] at hP
        exact hP.elim Or.inl (fun h => Or.inr (ih _ h))
      · exact Or.inr (ih H (by simpa only [skipped, if_neg hb] using hP))

/-- The propagated bound uses absence from the CURRENT original domain.
An earlier skipped upper is absent from every later domain, so containment
of the current lower is proper even when the initial attachment bound is sharp. -/
theorem skipped_upper_bound {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (H : Finset (Finset V)) (M : Nat)
    (hout : ∀ q ∈ H, q ∉ K) (hsize : ∀ q ∈ H, q.card ≤ M) :
    ∀ P ∈ skipped S.pairs H, P.upper.card ≤ M := by
  induction S generalizing H with
  | refl K => simp [Sequence.pairs, skipped]
  | step P T ih =>
      have hold : ∀ q ∈ H, q ∉ P.retained := by
        intro q hq hs
        exact hout q hq (P.retained_le hs)
      by_cases hb : blocked H P
      · have hb' := hb
        obtain ⟨q, hq, hlq⟩ := hb'
        have hproper : P.lower ⊂ q := Finset.ssubset_iff_subset_ne.mpr
          ⟨hlq, fun he => hout q hq (he ▸ P.lower_mem)⟩
        have hlt := Finset.card_lt_card hproper
        have hup : P.upper.card = P.lower.card + 1 := by
          simp [CollapsePair.upper, P.apex_notMem]
        have hP : P.upper.card ≤ M := by have := hsize q hq; omega
        have hnew : ∀ r ∈ insert P.upper H, r ∉ P.retained := by
          intro r hr hs
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact hs.2 (Finset.subset_insert _ _)
          · exact hold r hr hs
        have hsnew : ∀ r ∈ insert P.upper H, r.card ≤ M := by
          intro r hr
          exact (Finset.mem_insert.mp hr).elim (fun he => he.symm ▸ hP) (hsize r)
        intro R hR
        simp only [Sequence.pairs, skipped, if_pos hb, List.mem_cons] at hR
        exact hR.elim (fun he => he.symm ▸ hP)
          (fun h => ih (insert P.upper H) hnew hsnew R h)
      · intro R hR
        exact ih H hold hsize R (by
          simpa only [Sequence.pairs, skipped, if_neg hb] using hR)

private theorem project_sup (K L : Family V) :
    project (K ⊔ L) = project K ⊔ project L := by
  ext s
  change (s.Nonempty ∧ (s ∈ K ∨ s ∈ L)) ↔
    (s.Nonempty ∧ s ∈ K) ∨ (s.Nonempty ∧ s ∈ L)
  tauto

private theorem project_facets (H : Finset (Finset V)) :
    project (facets H) = simplices H := by
  ext s
  rfl

private theorem endpoint_inter_core (C : Family V) (D : Finset (Finset V))
    (hD : CriticalData C D) (C' : Family V) (hCC : C ≤ C')
    (habs : ∀ q ∈ D, q ∉ C') :
    project (endpoint C D) ⊓ project C' = project C := by
  ext s
  constructor
  · rintro ⟨⟨hn, hs | ⟨q, hq, hs⟩⟩, _, hsC⟩
    · exact ⟨hn, hs⟩
    · refine ⟨hn, hD.boundary q hq s ?_⟩
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun he => habs q hq (he ▸ hsC)⟩
  · rintro ⟨hn, hs⟩
    exact ⟨⟨hn, Or.inl hs⟩, hn, hCC hs⟩

/-- The actual size-bounded outside attachment. No output for the enlarged
family, no core-collapse supplier, and no reordered replay is an input.
When the old critical family is empty, `hOld` is vacuous. -/
def boundedAttachment (W : Finset V) (K : Family V) (c : Certificate W K)
    (H : Finset (Finset V)) (M : Nat)
    (hH : ∀ q ∈ H, q ⊆ W) (hne : ∀ q ∈ H, q.Nonempty)
    (hout : ∀ q ∈ H, q ∉ K)
    (hbd : ∀ q ∈ H, ∀ s, s ⊂ q → s ∈ K)
    (hsize : ∀ q ∈ H, q.card ≤ M)
    (hOld : ∀ q ∈ c.critical, M ≤ q.card) :
    Certificate W (K ⊔ facets H) := by
  classical
  let S := c.main
  let T := skippedTops S.pairs H
  let C := c.core ⊔ facets T
  let D := c.critical ∪ H
  have h0 : (∅ : Finset V) ∈ c.core :=
    c.core.lower (Finset.empty_subset _) c.vertex_mem
  have hCK : c.core ≤ K := by
    intro s hs
    by_cases hn : s.Nonempty
    · exact (S.monotone ⟨hn, Or.inl hs⟩).2
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst s
      exact K.lower (Finset.empty_subset _)
        (S.monotone ⟨Finset.singleton_nonempty _, Or.inl c.vertex_mem⟩).2
  have hOutside : ∀ q ∈ H, q ∉ project K := fun q hq hs => hout q hq hs.2
  have hBound := skipped_upper_bound S H M hOutside hsize
  have hT : ∀ u ∈ T, ∃ P ∈ skipped S.pairs H, u = P.upper := by
    intro u hu
    obtain ⟨P, hP, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    exact ⟨P, hP, he.symm⟩
  have hTK : ∀ u ∈ T, u ∈ K := by
    intro u hu
    obtain ⟨P, hP, rfl⟩ := hT u hu
    have hmem := skipped_mem S.pairs H hP
    -- Each actual original current domain is contained in the source.
    have hSource : ∀ {A B : PreAbstractSimplicialComplex V} (R : Sequence A B),
        ∀ Q ∈ R.pairs, Q.ambient ≤ A := by
      intro A B R
      induction R with
      | refl A => simp [Sequence.pairs]
      | step Q R ih =>
          intro P hP
          rcases List.mem_cons.mp hP with rfl | hP
          · exact le_rfl
          · exact (ih P hP).trans Q.retained_le
    exact (hSource S P hmem P.upper_mem).2
  have hCK' : C ≤ K := by
    rintro s (hs | ⟨u, hu, hsu⟩)
    · exact hCK hs
    · exact K.lower hsu (hTK u hu)
  have hOldAbsent : ∀ q ∈ c.critical, q ∉ C := by
    intro q hq hC
    rcases hC with hC | ⟨u, hu, hqu⟩
    · exact c.cells.absent q hq hC
    · obtain ⟨P, hP, rfl⟩ := hT u hu
      have hcq := hOld q hq
      have hcp := hBound P hP
      have he : q = P.upper := Finset.eq_of_subset_of_card_le hqu (by omega)
      have hqEnd : q ∈ project (endpoint c.core c.critical) :=
        ⟨c.cells.nonempty q hq, Or.inr ⟨q, hq, le_rfl⟩⟩
      have hqRet := S.final_le_each_retained (skipped_mem S.pairs H hP) hqEnd
      rw [he] at hqRet
      exact hqRet.2 (Finset.subset_insert _ _)
  have hCore : FinitePrescribedPairProtection.core S H =
      project (endpoint C c.critical) := by
    rw [FinitePrescribedPairProtection.core, ← project_facets, ← project_sup]
    congr 1
    apply SetLike.ext
    intro s
    change ((s ∈ c.core ∨ s ∈ facets c.critical) ∨ s ∈ facets T) ↔
      ((s ∈ c.core ∨ s ∈ facets T) ∨ s ∈ facets c.critical)
    tauto
  have hC0 : (∅ : Finset V) ∈ C := Or.inl h0
  have hBoundary : ∀ q ∈ H, ∀ s, s ⊂ q → s ∈ C := by
    intro q hq s hs
    by_cases hn : s.Nonempty
    · have hp := core_preserves S H ⟨hn, hbd q hq s hs⟩ ⟨q, hq, hs.subset⟩
      rw [hCore] at hp
      rcases hp.2 with hC | ⟨d, hd, hsd⟩
      · exact hC
      · apply Or.inl
        apply c.cells.boundary d hd s
        have hlt := Finset.card_lt_card hs
        have hqsz := hsize q hq
        have hdsz := hOld d hd
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsd, fun he => by
          have hec := congrArg Finset.card he
          omega⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simpa [he] using hC0
  have hCells : CriticalData C D := by
    constructor
    · intro q hq
      exact (Finset.mem_union.mp hq).elim (c.cells.nonempty q) (hne q)
    · intro q hq hs
      exact (Finset.mem_union.mp hq).elim (fun h => hOldAbsent q h hs)
        (fun h => hout q h (hCK' hs))
    · intro q hq s hs
      exact (Finset.mem_union.mp hq).elim
        (fun h => Or.inl (c.cells.boundary q h s hs)) (fun h => hBoundary q h s hs)
    · intro q hq r hr hqr
      by_contra he
      have hs : q ⊂ r := Finset.ssubset_iff_subset_ne.mpr ⟨hqr, he⟩
      have hqC : q ∈ C := (Finset.mem_union.mp hr).elim
        (fun h => Or.inl (c.cells.boundary r h q hs)) (fun h => hBoundary r h q hs)
      exact (Finset.mem_union.mp hq).elim (fun h => hOldAbsent q h hqC)
        (fun h => hout q h (hCK' hqC))
  let R := standaloneReplay S H
  have hRupper : ∀ P ∈ R.pairs, P.upper ∈ project C := by
    intro P hP
    have hm : (P.lower, P.upper) ∈ R.pairs.map (fun Q => (Q.lower, Q.upper)) :=
      List.mem_map.mpr ⟨P, hP, rfl⟩
    rw [standaloneReplay_pairs] at hm
    obtain ⟨Q, hQ, he⟩ := List.mem_map.mp hm
    have hu : Q.upper = P.upper := congrArg Prod.snd he
    refine ⟨P.lower_nonempty.mono (Finset.subset_insert _ _), Or.inr ?_⟩
    exact ⟨Q.upper, List.mem_toFinset.mpr (List.mem_map.mpr ⟨Q, hQ, rfl⟩),
      by rw [hu]⟩
  let Q := restrictSequence R (project C) hRupper
  have hRS : FinitePrescribedPairProtection.core S H ⊓ project C = project C := by
    apply inf_eq_right.mpr
    rw [hCore]
    intro s hs
    exact ⟨hs.1, Or.inl hs.2⟩
  have hRT : project (endpoint c.core c.critical) ⊓ project C = project c.core :=
    endpoint_inter_core c.core c.critical c.cells C (fun _ h => Or.inl h) hOldAbsent
  let sep := (Q.cast hRS hRT).append c.separate
  let main := protectedReplay S H
  have hMainSource : project K ⊔ simplices H = project (K ⊔ facets H) := by
    rw [project_sup, project_facets]
  have hMainTarget : FinitePrescribedPairProtection.core S H ⊔ simplices H =
      project (endpoint C D) := by
    rw [hCore, ← project_facets, ← project_sup]
    congr 1
    apply SetLike.ext
    intro s
    constructor
    · rintro ((hs | ⟨q, hq, hs⟩) | ⟨q, hq, hs⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨q, Finset.mem_union_left _ hq, hs⟩
      · exact Or.inr ⟨q, Finset.mem_union_right _ hq, hs⟩
    · rintro (hs | ⟨q, hq, hs⟩)
      · exact Or.inl (Or.inl hs)
      · exact (Finset.mem_union.mp hq).elim
          (fun h => Or.inl (Or.inr ⟨q, h, hs⟩)) (fun h => Or.inr ⟨q, h, hs⟩)
  exact {
    supported := by
      rintro s (hs | ⟨q, hq, hsq⟩)
      · exact c.supported s hs
      · exact hsq.trans (hH q hq)
    core := C
    critical := D
    vertex := c.vertex
    vertex_mem := Or.inl c.vertex_mem
    core_supported := fun s hs => c.supported s (hCK' hs)
    critical_supported := fun q hq =>
      (Finset.mem_union.mp hq).elim (c.critical_supported q) (hH q)
    cells := hCells
    main := main.cast hMainSource hMainTarget
    separate := sep }

/-- The returned main list is EXACTLY the emitted subsequence of the old
main in its original order, with the newly proved current ambient domains. -/
theorem boundedAttachment_main_pairs (W : Finset V) (K : Family V)
    (c : Certificate W K) (H : Finset (Finset V)) (M : Nat)
    (hH : ∀ q ∈ H, q ⊆ W) (hne : ∀ q ∈ H, q.Nonempty)
    (hout : ∀ q ∈ H, q ∉ K) (hbd : ∀ q ∈ H, ∀ s, s ⊂ q → s ∈ K)
    (hsize : ∀ q ∈ H, q.card ≤ M) (hOld : ∀ q ∈ c.critical, M ≤ q.card) :
    (boundedAttachment W K c H M hH hne hout hbd hsize hOld).main.pairs.map
        (fun P => (P.lower, P.upper)) =
      (emitted c.main.pairs H).map (fun P => (P.lower, P.upper)) := by
  simp only [boundedAttachment, Sequence.pairs_cast, protectedReplay_pairs]

/-- The separate list uses the skipped subsequence in ORIGINAL order followed
by the old C-only list. It is never interleaved with the emitted main list. -/
theorem boundedAttachment_separate_pairs (W : Finset V) (K : Family V)
    (c : Certificate W K) (H : Finset (Finset V)) (M : Nat)
    (hH : ∀ q ∈ H, q ⊆ W) (hne : ∀ q ∈ H, q.Nonempty)
    (hout : ∀ q ∈ H, q ∉ K) (hbd : ∀ q ∈ H, ∀ s, s ⊂ q → s ∈ K)
    (hsize : ∀ q ∈ H, q.card ≤ M) (hOld : ∀ q ∈ c.critical, M ≤ q.card) :
    (boundedAttachment W K c H M hH hne hout hbd hsize hOld).separate.pairs.map
        (fun P => (P.lower, P.upper)) =
      (skipped c.main.pairs H).map (fun P => (P.lower, P.upper)) ++
        c.separate.pairs.map (fun P => (P.lower, P.upper)) := by
  simp only [boundedAttachment, Sequence.pairs_append, Sequence.pairs_cast,
    List.map_append, restrictSequence_pairs, standaloneReplay_pairs]

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment
