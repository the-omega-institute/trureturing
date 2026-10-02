/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration
   mirror-E: none(waiver:original-site-piece-enumeration)
   anchors: []
   utility: none
   digest: Constructs inverse decreasing-site and selected-subset piece encodings. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215PieceEnumeration

open WeakAscent215Pure WeakAscent215Pieces

theorem original_piece_enumeration :
    (∀ {gap : ℕ} (data : OriginalPieces gap) (old : Bool),
      data.sites.Pairwise (fun left right => right < left) ∧
            data.pieces.length = data.sites.length + 1 ∧
            (data.replay old).length =
              data.sites.length + (data.pieces.map (fun h => h.val.length)).sum ∧
            spend (data.replay old) = (data.pieces.map (fun h => spend h.val)).sum) ∧
    (∃ family : ∀ gap : ℕ, OriginalPieces gap ≃
        (Σ selected : Finset (Fin gap), List.Vector PureHistory (selected.card + 1)),
      ∀ gap data, (family gap data).1 = data.sites.toFinset ∧
        (family gap data).2.toList = data.pieces) := by
  classical
  have shift_spend (offset : ℕ) (steps : List PureStep) :
      spend (steps.map (PureStep.shift offset)) = spend steps := by
    induction steps with
    | nil => rfl
    | cons first rest ih => cases first <;> simp [spend, PureStep.shift, ih]
  have spendAppend (front rest : List PureStep) :
      spend (front ++ rest) = spend front + spend rest := by
    induction front with
    | nil => simp [spend]
    | cons first front ih => cases first <;> simp [spend, ih, Nat.add_assoc]
  have data_properties {gap : ℕ} (data : OriginalPieces gap) (old : Bool) :
      data.sites.Pairwise (fun left right => right < left) ∧
      data.pieces.length = data.sites.length + 1 ∧
      (data.replay old).length =
        data.sites.length + (data.pieces.map (fun h => h.val.length)).sum ∧
      spend (data.replay old) = (data.pieces.map (fun h => spend h.val)).sum := by
    induction data generalizing old with
    | final history => simp [OriginalPieces.sites, OriginalPieces.pieces,
        OriginalPieces.replay, shift_spend]
    | @cut gap site history tail ih =>
      obtain ⟨horder, hpieces, hlength, hspend⟩ := ih false
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply List.pairwise_cons.mpr
        constructor
        · intro value hvalue
          obtain ⟨lower, _, rfl⟩ := List.mem_map.mp hvalue
          exact lower.is_lt
        · exact horder.map _ (fun _ _ h => h)
      · simp only [OriginalPieces.sites, OriginalPieces.pieces, List.length_cons, List.length_map]
        omega
      · simp only [OriginalPieces.replay, OriginalPieces.sites, OriginalPieces.pieces,
          List.length_append, List.length_cons, List.length_map, List.map_cons, List.sum_cons]
        omega
      · simp only [OriginalPieces.replay, OriginalPieces.pieces, spendAppend,
          shift_spend, spend, List.map_cons, List.sum_cons]
        rw [hspend]
  refine ⟨data_properties, ?_⟩
  have piece_properties (gap : ℕ) (data : OriginalPieces gap) :
      data.sites.Pairwise (fun left right => right < left) ∧
      data.pieces.length = data.sites.toFinset.card + 1 := by
    obtain ⟨horder, hlength, _, _⟩ := data_properties data true
    refine ⟨horder, ?_⟩
    rw [List.toFinset_card_of_nodup (horder.imp (fun bound => ne_of_gt bound))]
    exact hlength
  have pieces_injective {gap : ℕ} (left right : OriginalPieces gap)
      (hsites : left.sites = right.sites) (hpieces : left.pieces = right.pieces) :
      left = right := by
    induction left with
    | final history =>
      cases right with
      | final other =>
        simp only [OriginalPieces.pieces, List.cons.injEq, and_true] at hpieces
        exact congrArg OriginalPieces.final hpieces
      | cut site other tail => simp [OriginalPieces.sites] at hsites
    | @cut gap site history tail ih =>
      cases right with
      | final other => simp [OriginalPieces.sites] at hsites
      | cut otherSite other otherTail =>
        simp only [OriginalPieces.sites, List.cons.injEq] at hsites
        obtain ⟨hsite, htail⟩ := hsites
        subst otherSite
        have htail' : tail.sites = otherTail.sites :=
          (Fin.castLEEmb (Nat.le_of_lt site.is_lt)).injective.list_map htail
        simp only [OriginalPieces.pieces, List.cons.injEq] at hpieces
        obtain ⟨hhistory, hrest⟩ := hpieces
        subst other
        have hdata := ih otherTail htail' hrest
        subst otherTail
        rfl
  have build : ∀ size : ℕ, ∀ gap (sites : List (Fin gap)) (histories : List PureHistory),
      sites.length = size → sites.Pairwise (fun left right => right < left) →
      histories.length = sites.length + 1 →
      ∃ recursive : OriginalPieces gap,
        recursive.sites = sites ∧ recursive.pieces = histories := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro gap sites histories hsize horder hlength
      cases sites with
      | nil =>
        cases histories with
        | nil => simp at hlength
        | cons history rest =>
          have hrest : rest = [] := by simpa using hlength
          subst rest
          exact ⟨.final history, rfl, rfl⟩
      | cons site rest =>
        obtain ⟨hbelow, hrestorder⟩ := List.pairwise_cons.mp horder
        let lowered : List (Fin site.val) := rest.attach.map fun value =>
          ⟨value.val.val, hbelow value.val value.property⟩
        have hraise : lowered.map (Fin.castLE (Nat.le_of_lt site.is_lt)) = rest := by
          dsimp [lowered]
          rw [List.map_map]
          simp only [Function.comp_def]
          have hfunction :
              (fun value : {value : Fin gap // value ∈ rest} =>
                Fin.castLE (Nat.le_of_lt site.is_lt)
                  (⟨value.val.val, hbelow value.val value.property⟩ : Fin site.val)) =
              (fun value => value.val) := by
            funext value
            apply Fin.ext
            rfl
          rw [hfunction]
          simp
        have hlowerlength : lowered.length = rest.length := by simp [lowered]
        have hlowerorder : lowered.Pairwise (fun left right => right < left) := by
          have hraised : (lowered.map (Fin.castLE (Nat.le_of_lt site.is_lt))).Pairwise
              (fun left right => right < left) := by rw [hraise]; exact hrestorder
          exact List.pairwise_map.mp hraised
        cases histories with
        | nil => simp at hlength
        | cons history remaining =>
          have hremaining : remaining.length = lowered.length + 1 := by
            simp only [List.length_cons] at hlength
            omega
          have hshort : lowered.length < size := by simp only [List.length_cons] at hsize; omega
          obtain ⟨tail, htailSites, htailPieces⟩ :=
            ih lowered.length hshort site.val lowered remaining rfl hlowerorder hremaining
          refine ⟨.cut site history tail, ?_, ?_⟩
          · simp only [OriginalPieces.sites, htailSites, hraise]
          · simp only [OriginalPieces.pieces, htailPieces]
  let pack {gap : ℕ} (data : OriginalPieces gap) :
      Σ selected : Finset (Fin gap), List.Vector PureHistory (selected.card + 1) :=
    ⟨data.sites.toFinset, ⟨data.pieces, (piece_properties gap data).2⟩⟩
  have pack_injective (gap : ℕ) : Function.Injective (pack (gap := gap)) := by
    intro left right heq
    have hselected := congrArg Sigma.fst heq
    have hpieces := congrArg (fun data => data.2.toList) heq
    change left.sites.toFinset = right.sites.toFinset at hselected
    change left.pieces = right.pieces at hpieces
    have hsites : left.sites = right.sites := by
      apply (piece_properties gap left).1.eq_of_mem_iff (piece_properties gap right).1
      intro site
      have hmem : site ∈ left.sites.toFinset ↔ site ∈ right.sites.toFinset := by
        rw [hselected]
      simpa only [List.mem_toFinset] using hmem
    exact pieces_injective left right hsites hpieces
  have pack_surjective (gap : ℕ) : Function.Surjective (pack (gap := gap)) := by
    rintro ⟨selected, histories⟩
    let sites := selected.sort (· ≥ ·)
    have horder : sites.Pairwise (fun left right => right < left) :=
      selected.sortedGT_sort.pairwise
    have hlength : histories.toList.length = sites.length + 1 := by
      rw [List.Vector.toList_length]
      simp [sites]
    obtain ⟨recursive, hsites, hpieces⟩ :=
      build sites.length gap sites histories.toList rfl horder hlength
    refine ⟨recursive, ?_⟩
    have hselected : recursive.sites.toFinset = selected := by
      rw [hsites]
      exact selected.sort_toFinset _
    exact Sigma.subtype_ext hselected hpieces
  refine ⟨fun gap => Equiv.ofBijective (pack (gap := gap))
    ⟨pack_injective gap, pack_surjective gap⟩, ?_⟩
  intro gap data
  exact ⟨rfl, rfl⟩

end D5.S3.Combinatorics.WeakAscent.WeakAscent215PieceEnumeration
