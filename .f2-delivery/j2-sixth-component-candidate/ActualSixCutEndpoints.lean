/- UNCOMPILED replacement for the private actual_six_cut_slicing in
   NativeJ2SurvivingModel. Add import Walks.EdgeSlicingCutEndpoints.
   It uses the existing markedCut_injective and namespace/open context. -/

private theorem actual_six_cut_slicing_with_endpoints {m : ℕ} (hm : 5 ≤ m) :
    ∃ pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece
        (domainGraph (F2Domain m))),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (∀ v : {x : Configuration m // F2Domain m x},
        (pieces.flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e : Sym2 (Configuration m),
        e ∈ (pieces.flatMap fun z => z.walk.edges).map (Sym2.map Subtype.val) ↔
          SurvivingEdge m e) ∧
      pieces.length = 6 ∧
      ∀ z ∈ pieces,
        (∃ q : Fin 3 × Bool × Bool, z.start.val = port m q) ∧
        (∃ q : Fin 3 × Bool × Bool, z.finish.val = port m q) := by
  classical
  obtain ⟨base, w, hw, hinv, hports, hmarked⟩ :=
    native_j2_hamiltonian_cycle_with_marked_edges hm
  let cut : Fin 3 × Bool → Sym2 {x : Configuration m // F2Domain m x} := fun q =>
    s(⟨port m (q.1, q.2, false), hports (q.1, q.2, false)⟩,
      ⟨port m (q.1, q.2, true), hports (q.1, q.2, true)⟩)
  have hmap (q : Fin 3 × Bool) : Sym2.map Subtype.val (cut q) = markedEdge m q := rfl
  have hmapinj : Function.Injective
      (Sym2.map (Subtype.val : {x : Configuration m // F2Domain m x} → Configuration m)) :=
    Sym2.map.injective Subtype.val_injective
  have hcutinj : Function.Injective cut := by
    intro p q he
    apply markedCut_injective hm
    simpa only [hmap] using congrArg (Sym2.map Subtype.val) he
  let E : Finset (Sym2 {x : Configuration m // F2Domain m x}) := Finset.univ.image cut
  have hE : E.Nonempty := by
    exact ⟨cut (0, false), Finset.mem_image.mpr ⟨(0, false), Finset.mem_univ _, rfl⟩⟩
  have hE_marked (e : Sym2 {x : Configuration m // F2Domain m x}) :
      e ∈ E ↔ MarkedCut m (Sym2.map Subtype.val e) := by
    constructor
    · intro he
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      exact ⟨q, hmap q⟩
    · rintro ⟨q, hq⟩
      have he : e = cut q := hmapinj (hq.trans (hmap q).symm)
      rw [he]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  have hcuts : ∀ e ∈ E, e ∈ w.edgeSet := by
    intro e he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    have hq : Sym2.map Subtype.val (cut q) ∈ w.edges.map (Sym2.map Subtype.val) := by
      rw [hmap]
      exact hmarked q
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hq
    have heq' : e = cut q := hmapinj heq
    simpa only [← heq', SimpleGraph.Walk.mem_edgeSet] using he
  obtain ⟨pieces, hpath, hsupport, hedges, hlength, hendpoints⟩ :=
    D5.S3.Combinatorics.Graph.Walks.EdgeSlicingCutEndpoints.exists_cycle_edge_slicing_with_cut_endpoints
      E w hw hE hcuts
  refine ⟨pieces, hpath, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using hsupport v
  · intro e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      obtain ⟨hfw, hfE⟩ := (hedges f).mp hf
      have hn : (F2NativeEdge m (Sym2.map Subtype.val f) ∧
          ¬ F2DeletedEdge m (Sym2.map Subtype.val f)) ∨
          F2Seam m (Sym2.map Subtype.val f) :=
        (hinv _).mp (List.mem_map.mpr ⟨f, hfw, rfl⟩)
      exact ⟨hn, fun hmark => hfE ((hE_marked f).mpr hmark)⟩
    · rintro ⟨hn, hmark⟩
      obtain ⟨f, hfw, hfe⟩ := List.mem_map.mp ((hinv e).mpr hn)
      refine List.mem_map.mpr ⟨f, (hedges f).mpr ⟨hfw, ?_⟩, hfe⟩
      intro hfE
      apply hmark
      rw [← hfe]
      exact (hE_marked f).mp hfE
  · rw [hlength]
    simp only [E, Finset.card_image_of_injective _ hcutinj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

  · have hport (v : {x : Configuration m // F2Domain m x})
        (hv : ∃ e ∈ E, v ∈ e) : ∃ q : Fin 3 × Bool × Bool, v.val = port m q := by
      obtain ⟨e, he, hve⟩ := hv
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      change v ∈ s(⟨port m (q.1, q.2, false), hports (q.1, q.2, false)⟩,
        ⟨port m (q.1, q.2, true), hports (q.1, q.2, true)⟩) at hve
      rcases Sym2.mem_iff.mp hve with hv | hv
      · exact ⟨(q.1, q.2, false), congrArg Subtype.val hv⟩
      · exact ⟨(q.1, q.2, true), congrArg Subtype.val hv⟩
    intro z hz
    exact ⟨hport z.start (hendpoints z hz).1, hport z.finish (hendpoints z hz).2⟩
