/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition
   mirror-E: none(waiver:class-215-combinatorial-counting)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Powerset]
   utility: none
   digest: Extracts and replays first-record pieces and counts every bidegree. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Products
import D5.S3.Combinatorics.WeakAscent.WeakAscent215PieceEnumeration
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Decomposition

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Finite WeakAscent215Products
open WeakAscent215PieceEnumeration
open PowerSeries

theorem first_record_decomposition :
    (∃ replayEquiv : {history : PureHistory // history.val ≠ []} ≃
        (Σ gap : ℕ, Σ selected : Finset (Fin gap), List.Vector PureHistory (selected.card + 1)),
      ∀ data, ∃ recursive : OriginalPieces data.1,
        recursive.sites = data.2.1.sort (· ≥ ·) ∧
        recursive.pieces = data.2.2.toList ∧
        (replayEquiv.symm data).val.val = .record data.1 :: recursive.replay true ∧
        (replayEquiv.symm data).val.val.length =
          1 + data.2.1.card + (data.2.2.toList.map (fun h => h.val.length)).sum ∧
        spend (replayEquiv.symm data).val.val =
          data.1 + (data.2.2.toList.map (fun h => spend h.val)).sum) ∧
    (pureSeries + X * (1 + C X * pureSeries) = 1 + C X * pureSeries +
        X * (1 + C X * pureSeries) * pureSeries) := by
  classical
  have pure_inert_base (base stack ending : List Bool) (steps : List PureStep) :
      PureRun (base ++ stack) (steps.map (PureStep.shift base.length)) (base ++ ending) ↔
        PureRun stack steps ending := by
    have take_shift (values : List Bool) (site : ℕ) :
        (base ++ values).take (base.length + site) = base ++ values.take site := by
      rw [List.take_append]
      have htake : base.take (base.length + site) = base := by
        apply List.take_of_length_le
        omega
      rw [htake, Nat.add_sub_cancel_left]
    have read_shift (values : List Bool) (site : ℕ) :
        (base ++ values).getD (base.length + site) true = values.getD site true := by
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    induction steps generalizing stack ending with
    | nil =>
      simp only [List.map_nil]
      constructor
      · intro hrun
        have nil_eq (starting final : List Bool) (h : PureRun starting [] final) :
            starting = final := by
          cases h
          rfl
        have heq : stack = ending := List.append_cancel_left (nil_eq _ _ hrun)
        subst ending
        exact PureRun.nil _
      · intro hrun
        cases hrun
        exact PureRun.nil _
    | cons first rest ih =>
      cases first with
      | record gap =>
        simp only [List.map_cons, PureStep.shift]
        constructor
        · intro hrun
          cases hrun with
          | record _ _ _ _ htail =>
            have htail' : PureRun (base ++ (stack ++ List.replicate gap false ++ [true]))
                (rest.map (PureStep.shift base.length)) (base ++ ending) := by
              simpa only [List.append_assoc] using htail
            exact PureRun.record _ _ _ _ ((ih _ _).mp htail')
        · intro hrun
          cases hrun with
          | record _ _ _ _ htail =>
            apply PureRun.record
            simpa only [List.append_assoc] using (ih _ _).mpr htail
      | descend site =>
        simp only [List.map_cons, PureStep.shift]
        constructor
        · intro hrun
          cases hrun with
          | descend _ _ _ _ hsite hfresh htail =>
            have hsite' : site < stack.length := by simpa using hsite
            have hfresh' : stack.getD site true = false := by
              rwa [read_shift] at hfresh
            rw [take_shift] at htail
            exact PureRun.descend _ _ _ _ hsite' hfresh' ((ih _ _).mp htail)
        · intro hrun
          cases hrun with
          | descend _ _ _ _ hsite hfresh htail =>
            apply PureRun.descend
            · simpa using hsite
            · rwa [read_shift]
            · rw [take_shift]
              exact (ih _ _).mpr htail
  have firstCuts :
      ∃ replayEquiv : {history : PureHistory // history.val ≠ []} ≃
              (Σ gap : ℕ, Σ selected : Finset (Fin gap),
                List.Vector PureHistory (selected.card + 1)),
            ∀ data, ∃ recursive : OriginalPieces data.1,
              recursive.sites = data.2.1.sort (· ≥ ·) ∧
              recursive.pieces = data.2.2.toList ∧
              (replayEquiv.symm data).val.val = .record data.1 :: recursive.replay true ∧
              (replayEquiv.symm data).val.val.length =
                1 + data.2.1.card + (data.2.2.toList.map (fun h => h.val.length)).sum ∧
              spend (replayEquiv.symm data).val.val =
                data.1 + (data.2.2.toList.map (fun h => spend h.val)).sum := by
    classical
    let base (gap : ℕ) (old : Bool) := List.replicate gap false ++ if old then [true] else []
    have hbaselen (gap : ℕ) (old : Bool) :
        (base gap old).length = gap + if old then 1 else 0 := by
      cases old <;> simp [base]
    have take_base (gap site : ℕ) (old : Bool) (hsite : site ≤ gap) :
        (base gap old).take site = base site false := by
      simp only [base, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      rw [List.take_append_of_le_length (by simpa using hsite), List.take_replicate,
        Nat.min_eq_left hsite]
    have take_above (bottom top : List Bool) (site : ℕ) :
        (bottom ++ top).take (bottom.length + site) = bottom ++ top.take site := by
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    have split_run (steps : List PureStep) (bottom top ending : List Bool)
        (hrun : PureRun (bottom ++ top) steps ending) :
        (∃ normalized final, PureRun top normalized final ∧
          steps = normalized.map (PureStep.shift bottom.length) ∧ ending = bottom ++ final) ∨
        (∃ normalized final site rest, PureRun top normalized final ∧
          site < bottom.length ∧ bottom.getD site true = false ∧
          steps = normalized.map (PureStep.shift bottom.length) ++ .descend site :: rest ∧
          PureRun (bottom.take site) rest ending) := by
      induction steps generalizing top with
      | nil => cases hrun; exact Or.inl ⟨[], top, PureRun.nil _, rfl, rfl⟩
      | cons first rest ih =>
        cases first with
        | record gap =>
          cases hrun with
          | record _ _ _ _ htail =>
            have htail' : PureRun (bottom ++ (top ++ List.replicate gap false ++ [true]))
                rest ending := by simpa only [List.append_assoc] using htail
            rcases ih _ htail' with
              ⟨normalized, final, hnorm, heq, hfinal⟩ |
              ⟨normalized, final, site, suffix, hnorm, hsite, hfresh, heq, hsuffix⟩
            · left
              exact ⟨.record gap :: normalized, final, PureRun.record _ _ _ _ hnorm,
                by simp only [List.map_cons, PureStep.shift, heq], hfinal⟩
            · right
              exact ⟨.record gap :: normalized, final, site, suffix,
                PureRun.record _ _ _ _ hnorm, hsite, hfresh,
                by simp only [List.map_cons, PureStep.shift, heq, List.cons_append], hsuffix⟩
        | descend site =>
          cases hrun with
          | descend _ _ _ _ hsite hfresh htail =>
            by_cases hbelow : site < bottom.length
            · right
              refine ⟨[], top, site, rest, PureRun.nil _, hbelow, ?_, rfl, ?_⟩
              · rwa [List.getD_append _ _ _ _ hbelow] at hfresh
              · rwa [List.take_append_of_le_length (Nat.le_of_lt hbelow)] at htail
            · let lowered := site - bottom.length
              have hsiteeq : site = bottom.length + lowered := by dsimp [lowered]; omega
              have htop : lowered < top.length := by
                simp only [List.length_append] at hsite
                dsimp [lowered]; omega
              have htopfresh : top.getD lowered true = false := by
                rwa [List.getD_append_right _ _ _ _ (by omega)] at hfresh
              rw [hsiteeq, take_above] at htail
              rcases ih _ htail with
                ⟨normalized, final, hnorm, heq, hfinal⟩ |
                ⟨normalized, final, chosen, suffix, hnorm, hchosen, hfresh', heq, hsuffix⟩
              · left
                refine ⟨.descend lowered :: normalized, final,
                  PureRun.descend _ _ _ _ htop htopfresh hnorm, ?_, hfinal⟩
                simp only [List.map_cons, PureStep.shift, heq, hsiteeq]
              · right
                refine ⟨.descend lowered :: normalized, final, chosen, suffix,
                  PureRun.descend _ _ _ _ htop htopfresh hnorm, hchosen, hfresh', ?_, hsuffix⟩
                simp only [List.map_cons, PureStep.shift, heq, hsiteeq, List.cons_append]
    have extract : ∀ steps : List PureStep, ∀ gap old ending,
        PureRun (base gap old) steps ending →
        ∃ data : OriginalPieces gap, data.replay old = steps := by
      intro steps
      induction measure : steps.length using Nat.strong_induction_on generalizing steps with
      | h size ih =>
        intro gap old ending hrun
        have hrun' : PureRun (base gap old ++ []) steps ending := by simpa using hrun
        rcases split_run steps (base gap old) [] ending hrun' with
          ⟨normalized, final, hnorm, heq, _⟩ |
          ⟨normalized, final, site, rest, hnorm, hsite, hfresh, heq, hrest⟩
        · exact ⟨.final ⟨normalized, final, hnorm⟩, by
            simp only [OriginalPieces.replay, ← hbaselen]
            exact heq.symm⟩
        · have horiginal : site < gap := by
            by_contra hnot
            rw [hbaselen] at hsite
            cases old with
            | false => simp at hsite; omega
            | true =>
              simp at hsite
              have hlast : site = gap := by omega
              subst site
              change (List.replicate gap false ++ [true]).getD gap true = false at hfresh
              rw [List.getD_append_right _ _ _ _ (by simp)] at hfresh; simp at hfresh
          have hbottom := take_base gap site old (Nat.le_of_lt horiginal)
          rw [hbottom] at hrest
          have hshort : rest.length < size := by
            have hlen := congrArg List.length heq
            simp only [List.length_append, List.length_map, List.length_cons] at hlen
            omega
          obtain ⟨tail, htail⟩ := ih rest.length hshort rest rfl site false ending hrest
          refine ⟨.cut ⟨site, horiginal⟩ ⟨normalized, final, hnorm⟩ tail, ?_⟩
          simp only [OriginalPieces.replay, ← hbaselen, htail]
          exact heq.symm
    have append_runs (starting middle ending : List Bool) (front rest : List PureStep)
        (hfront : PureRun starting front middle) (hrest : PureRun middle rest ending) :
        PureRun starting (front ++ rest) ending := by
      induction hfront with
      | nil => exact hrest
      | record _ _ _ _ _ ih => exact PureRun.record _ _ _ _ (ih hrest)
      | descend _ _ _ _ hsite hfresh _ ih => exact PureRun.descend _ _ _ _ hsite hfresh (ih hrest)
    have replay_valid {gap : ℕ} (data : OriginalPieces gap) (old : Bool) :
        ∃ ending, PureRun (base gap old) (data.replay old) ending := by
      induction data generalizing old with
      | @final gap history =>
        obtain ⟨ending, hrun⟩ := history.property
        refine ⟨base gap old ++ ending, ?_⟩
        have hshift := (pure_inert_base (base gap old) [] ending history.val).mpr hrun
        simpa only [List.append_nil, hbaselen, OriginalPieces.replay] using hshift
      | @cut gap site history tail ih =>
        obtain ⟨middle, hrun⟩ := history.property
        obtain ⟨ending, htail⟩ := ih false
        have hshift := (pure_inert_base (base gap old) [] middle history.val).mpr hrun
        simp only [List.append_nil, hbaselen] at hshift
        refine ⟨ending, append_runs _ _ _ _ _ hshift ?_⟩
        apply PureRun.descend
        · simp only [List.length_append, hbaselen]
          omega
        · rw [List.getD_append _ _ _ _ (by rw [hbaselen]; omega)]
          change (List.replicate gap false ++ (if old then [true] else [])).getD
            site.val true = false
          rw [List.getD_append _ _ _ _ (by simp)]; exact List.getD_replicate false site.is_lt
        · have htake : (base gap old ++ middle).take site.val = base site.val false := by
            rw [List.take_append_of_le_length (by rw [hbaselen]; omega)]
            exact take_base gap site.val old (Nat.le_of_lt site.is_lt)
          rw [htake]; exact htail
    have split_unique (offset : ℕ) (left right : List PureStep)
        (leftTail rightTail : List PureStep)
        (hleft : leftTail = [] ∨ ∃ site rest,
          site < offset ∧ leftTail = .descend site :: rest)
        (hright : rightTail = [] ∨ ∃ site rest,
          site < offset ∧ rightTail = .descend site :: rest)
        (heq : left.map (PureStep.shift offset) ++ leftTail =
          right.map (PureStep.shift offset) ++ rightTail) :
        left = right ∧ leftTail = rightTail := by
      induction left generalizing right with
      | nil =>
        cases right with
        | nil => exact ⟨rfl, by simpa using heq⟩
        | cons first rest =>
          rcases hleft with rfl | ⟨site, suffix, hsite, rfl⟩
          · simp at heq
          · simp only [List.map_cons, List.cons_append] at heq
            have hstep := (List.cons.inj heq).1
            cases first <;> simp only [PureStep.shift] at hstep
            · cases hstep
            · have := PureStep.descend.inj hstep
              omega
      | cons first rest ih =>
        cases right with
        | nil =>
          rcases hright with rfl | ⟨site, suffix, hsite, rfl⟩
          · simp at heq
          · simp only [List.map_cons, List.cons_append] at heq
            have hstep := (List.cons.inj heq).1
            cases first <;> simp only [PureStep.shift] at hstep
            · cases hstep
            · have := PureStep.descend.inj hstep
              omega
        | cons other others =>
          simp only [List.map_cons, List.cons_append] at heq
          obtain ⟨hstep, htail⟩ := List.cons.inj heq
          have hfirst : first = other := by
            cases first <;> cases other <;> simp only [PureStep.shift] at hstep
            · exact congrArg PureStep.record (PureStep.record.inj hstep)
            · cases hstep
            · cases hstep
            · have := PureStep.descend.inj hstep
              congr 1
              omega
          obtain ⟨hrest, htails⟩ := ih others htail
          exact ⟨by rw [hfirst, hrest], htails⟩
    have replay_injective {gap : ℕ} (old : Bool) :
        Function.Injective (OriginalPieces.replay (gap := gap) old) := by
      intro left
      induction left generalizing old with
      | @final gap history =>
        intro right heq
        cases right with
        | final other =>
          obtain ⟨hpiece, _⟩ := split_unique (gap + if old then 1 else 0)
            history.val other.val [] []
            (Or.inl rfl) (Or.inl rfl) (by simpa only [OriginalPieces.replay,
              List.append_nil] using heq)
          exact congrArg OriginalPieces.final (Subtype.ext hpiece)
        | cut site other tail =>
          obtain ⟨_, htail⟩ := split_unique (gap + if old then 1 else 0)
            history.val other.val []
            (.descend site.val :: tail.replay false) (Or.inl rfl)
            (Or.inr ⟨site.val, _, by omega, rfl⟩)
            (by simpa only [OriginalPieces.replay, List.append_nil] using heq)
          cases htail
      | @cut gap site history tail ih =>
        intro right heq
        cases right with
        | final other =>
          obtain ⟨_, htail⟩ := split_unique (gap + if old then 1 else 0) history.val other.val
            (.descend site.val :: tail.replay false) []
            (Or.inr ⟨site.val, _, by omega, rfl⟩) (Or.inl rfl)
            (by simpa only [OriginalPieces.replay, List.append_nil] using heq)
          cases htail
        | cut otherSite other otherTail =>
          obtain ⟨hpiece, htails⟩ := split_unique (gap + if old then 1 else 0)
            history.val other.val
            (.descend site.val :: tail.replay false)
            (.descend otherSite.val :: otherTail.replay false)
            (Or.inr ⟨site.val, _, by omega, rfl⟩)
            (Or.inr ⟨otherSite.val, _, by omega, rfl⟩)
            (by simpa only [OriginalPieces.replay] using heq)
          have hsite : site = otherSite := Fin.ext (PureStep.descend.inj (List.cons.inj htails).1)
          subst otherSite
          have hhistory : history = other := Subtype.ext hpiece
          subst other
          have hrest := ih false (List.cons.inj htails).2
          subst otherTail
          rfl
    let encode : (Σ gap : ℕ, OriginalPieces gap) →
        {history : PureHistory // history.val ≠ []} := fun data =>
      ⟨⟨.record data.1 :: data.2.replay true, by
          obtain ⟨ending, hrun⟩ := replay_valid data.2 true
          refine ⟨ending, PureRun.record _ _ _ _ ?_⟩
          simpa [base] using hrun⟩, List.cons_ne_nil _ _⟩
    have encode_injective : Function.Injective encode := by
      rintro ⟨leftGap, left⟩ ⟨rightGap, right⟩ heq
      have hsteps := congrArg (fun h => h.val.val) heq
      change PureStep.record leftGap :: left.replay true =
        PureStep.record rightGap :: right.replay true at hsteps
      obtain ⟨hgap, hrest⟩ := List.cons.inj hsteps
      have hgap' := PureStep.record.inj hgap
      subst rightGap
      have hdata := replay_injective true hrest
      subst right
      rfl
    have encode_surjective : Function.Surjective encode := by
      intro history
      obtain ⟨ending, hrun⟩ := history.val.property
      cases hsteps : history.val.val with
      | nil => exact False.elim (history.property hsteps)
      | cons first rest =>
        rw [hsteps] at hrun
        cases first with
        | descend site => cases hrun with | descend _ _ _ _ hsite => simp at hsite
        | record gap =>
          cases hrun with
          | record _ _ _ _ htail =>
            have htail' : PureRun (base gap true) rest ending := by simpa [base] using htail
            obtain ⟨data, hdata⟩ := extract rest gap true ending htail'
            refine ⟨⟨gap, data⟩, ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            change .record gap :: data.replay true = history.val.val; rw [hdata, hsteps]
    let historyEquiv := (Equiv.ofBijective encode ⟨encode_injective, encode_surjective⟩).symm
    have hreplay (data : Σ gap : ℕ, OriginalPieces gap) :
        (historyEquiv.symm data).val.val = .record data.1 :: data.2.replay true := rfl
    have data_properties := fun {gap : ℕ} (data : OriginalPieces gap) (old : Bool) =>
      original_piece_enumeration.1 data old
    have hproperties (data : Σ gap : ℕ, OriginalPieces gap) :
        data.2.sites.Pairwise (fun left right => right < left) ∧
        data.2.pieces.length = data.2.sites.toFinset.card + 1 ∧
        (historyEquiv.symm data).val.val.length =
          1 + data.2.sites.toFinset.card + (data.2.pieces.map (fun h => h.val.length)).sum ∧
        spend (historyEquiv.symm data).val.val =
          data.1 + (data.2.pieces.map (fun h => spend h.val)).sum := by
      rcases data with ⟨gap, data⟩
      obtain ⟨horder, hpieces, hlength, hspend⟩ := data_properties data true
      have hnodup : data.sites.Nodup := horder.imp (fun h => ne_of_gt h)
      have hcard := List.toFinset_card_of_nodup hnodup
      refine ⟨horder, ?_, ?_, ?_⟩
      · change data.pieces.length = data.sites.toFinset.card + 1
        omega
      · change (.record gap :: data.replay true).length =
          1 + data.sites.toFinset.card + (data.pieces.map (fun h => h.val.length)).sum
        simp only [List.length_cons]
        omega
      · change spend (.record gap :: data.replay true) =
          gap + (data.pieces.map (fun h => spend h.val)).sum
        simp only [spend]
        rw [hspend]
    obtain ⟨piecesEquiv, hpiecesEquiv⟩ := original_piece_enumeration.2
    have subsetcorrespondence :
        ∃ replayEquiv : {history : PureHistory // history.val ≠ []} ≃
            (Σ gap : ℕ, Σ selected : Finset (Fin gap),
              List.Vector PureHistory (selected.card + 1)),
          ∀ data, ∃ recursive : OriginalPieces data.1,
            recursive.sites = data.2.1.sort (· ≥ ·) ∧
            recursive.pieces = data.2.2.toList ∧
            (replayEquiv.symm data).val.val = .record data.1 :: recursive.replay true ∧
            (replayEquiv.symm data).val.val.length =
              1 + data.2.1.card + (data.2.2.toList.map (fun h => h.val.length)).sum ∧
            spend (replayEquiv.symm data).val.val =
              data.1 + (data.2.2.toList.map (fun h => spend h.val)).sum := by
      let dataEquiv := Equiv.sigmaCongrRight piecesEquiv
      let replayEquiv := historyEquiv.trans dataEquiv
      refine ⟨replayEquiv, ?_⟩
      rintro ⟨gap, selected, histories⟩
      let recursive := (piecesEquiv gap).symm ⟨selected, histories⟩
      have roundtrip := (piecesEquiv gap).apply_symm_apply ⟨selected, histories⟩
      have hselected := (hpiecesEquiv gap recursive).1.symm.trans (congrArg Sigma.fst roundtrip)
      have hpieces := (hpiecesEquiv gap recursive).2.symm.trans
        (congrArg (fun data => data.2.toList) roundtrip)
      have horder := (hproperties ⟨gap, recursive⟩).1
      have hnodup : recursive.sites.Nodup := horder.imp (fun h => ne_of_gt h)
      have hsorted : recursive.sites = selected.sort (· ≥ ·) := by
        have hsort := (List.toFinset_sort (· ≥ ·) hnodup).mpr (horder.imp (fun h => le_of_lt h))
        rw [hselected] at hsort; exact hsort.symm
      have hinverse : (replayEquiv.symm ⟨gap, selected, histories⟩).val.val =
          .record gap :: recursive.replay true := hreplay ⟨gap, recursive⟩
      refine ⟨recursive, hsorted, hpieces, hinverse, ?_, ?_⟩
      · have hlength := (hproperties ⟨gap, recursive⟩).2.2.1
        rw [hreplay ⟨gap, recursive⟩] at hlength
        change (.record gap :: recursive.replay true).length = 1 + recursive.sites.toFinset.card +
            (recursive.pieces.map (fun h => h.val.length)).sum at hlength
        rw [hselected, hpieces] at hlength; rw [hinverse]; exact hlength
      · have hspend := (hproperties ⟨gap, recursive⟩).2.2.2
        rw [hreplay ⟨gap, recursive⟩] at hspend
        change spend (.record gap :: recursive.replay true) =
          gap + (recursive.pieces.map (fun h => spend h.val)).sum at hspend
        rw [hpieces] at hspend; rw [hinverse]; exact hspend
    exact subsetcorrespondence
  refine ⟨firstCuts, ?_⟩
  have orderedProducts (pieces size total : ℕ) :
      Finite {histories : List.Vector PureHistory pieces //
        (histories.toList.map (fun history => history.val.length)).sum = size ∧
        (histories.toList.map (fun history => spend history.val)).sum = total} ∧
      Nat.card {histories : List.Vector PureHistory pieces //
        (histories.toList.map (fun history => history.val.length)).sum = size ∧
        (histories.toList.map (fun history => spend history.val)).sum = total} =
          coeff size (coeff total (pureSeries ^ pieces)) := by
    classical
    let Fiber := fun size total : ℕ =>
      {history : PureHistory // history.val.length = size ∧ spend history.val = total}
    let Family := fun pieces size total : ℕ =>
      {histories : List.Vector PureHistory pieces //
        (histories.toList.map (fun history => history.val.length)).sum = size ∧
        (histories.toList.map (fun history => spend history.val)).sum = total}
    let (size total : ℕ) : Finite (Fiber size total) := by
      let values : Set (List PureStep) :=
        {steps | steps.length = size ∧ spend steps = total ∧
          ∃ ending, PureRun [] steps ending}
      let : Finite values := (pure_histories_finite size total).to_subtype
      apply Finite.of_injective (fun history : Fiber size total =>
        (⟨history.val.val, history.property.1, history.property.2,
          history.val.property⟩ : values))
      intro first second heq
      exact Subtype.ext (Subtype.ext (congrArg (fun value : values => value.val) heq))
    have split_family (pieces size total : ℕ) : Family (pieces + 1) size total ≃
        (Σ lengths : ↑(Finset.antidiagonal size), Σ spends : ↑(Finset.antidiagonal total),
          Fiber lengths.val.1 spends.val.1 × Family pieces lengths.val.2 spends.val.2) := by
      let split : Family (pieces + 1) size total →
          (Σ lengths : ↑(Finset.antidiagonal size), Σ spends : ↑(Finset.antidiagonal total),
            Fiber lengths.val.1 spends.val.1 × Family pieces lengths.val.2 spends.val.2) :=
        fun histories => by
          let first := histories.val.head
          let rest := histories.val.tail
          let restSize := (rest.toList.map (fun history => history.val.length)).sum
          let restSpend := (rest.toList.map (fun history => spend history.val)).sum
          have hhead : first ::ᵥ rest = histories.val := List.Vector.cons_head_tail _
          have hlength : first.val.length + restSize = size := by
            have h := histories.property.1
            rw [← hhead] at h; simpa [restSize] using h
          have hspend : spend first.val + restSpend = total := by
            have h := histories.property.2
            rw [← hhead] at h; simpa [restSpend] using h
          exact ⟨⟨(first.val.length, restSize), Finset.mem_antidiagonal.mpr hlength⟩,
            ⟨(spend first.val, restSpend), Finset.mem_antidiagonal.mpr hspend⟩,
            ⟨first, rfl, rfl⟩, ⟨rest, rfl, rfl⟩⟩
      let combine :
          (Σ lengths : ↑(Finset.antidiagonal size), Σ spends : ↑(Finset.antidiagonal total),
            Fiber lengths.val.1 spends.val.1 × Family pieces lengths.val.2 spends.val.2) →
          Family (pieces + 1) size total := fun data =>
        ⟨data.2.2.1.val ::ᵥ data.2.2.2.val, by
          constructor
          · simp only [List.Vector.toList_cons, List.map_cons, List.sum_cons]
            rw [data.2.2.1.property.1, data.2.2.2.property.1]
            exact Finset.mem_antidiagonal.mp data.1.property
          · simp only [List.Vector.toList_cons, List.map_cons, List.sum_cons]
            rw [data.2.2.1.property.2, data.2.2.2.property.2]
            exact Finset.mem_antidiagonal.mp data.2.1.property⟩
      refine ⟨split, combine, ?_, ?_⟩
      · intro histories
        apply Subtype.ext
        exact List.Vector.cons_head_tail histories.val
      · rintro ⟨⟨⟨firstSize, restSize⟩, hlength⟩,
          ⟨⟨⟨firstSpend, restSpend⟩, hspend⟩, first, rest⟩⟩
        rcases first with ⟨first, hfirstSize, hfirstSpend⟩
        rcases rest with ⟨rest, hrestSize, hrestSpend⟩
        dsimp only at hfirstSize hfirstSpend hrestSize hrestSpend
        subst firstSize
        subst firstSpend
        subst restSize
        subst restSpend
        dsimp [split, combine]; simp only [List.Vector.head_cons, List.Vector.tail_cons]; rfl
    have finite_families (pieces size total : ℕ) : Finite (Family pieces size total) := by
      induction pieces generalizing size total with
      | zero =>
        exact Finite.of_injective (fun histories : Family 0 size total => histories.val)
          Subtype.val_injective
      | succ pieces ih =>
        let (size total : ℕ) : Finite (Family pieces size total) := ih size total
        let (size total : ℕ) : Fintype (Family pieces size total) := Fintype.ofFinite _
        let (size total : ℕ) : Fintype (Fiber size total) := Fintype.ofFinite _
        exact Finite.of_equiv _ (split_family pieces size total).symm
    let (pieces size total : ℕ) : Finite (Family pieces size total) :=
      finite_families pieces size total
    refine ⟨inferInstance, ?_⟩
    induction pieces generalizing size total with
    | zero =>
      by_cases hsize : size = 0
      · subst size
        by_cases htotal : total = 0
        · subst total
          have : Nonempty (Family 0 0 0) := ⟨⟨List.Vector.nil, by simp⟩⟩
          change Nat.card (Family 0 0 0) = _; rw [Nat.card_unique]; simp [coeff_one]
        · have : IsEmpty (Family 0 0 total) := ⟨fun histories => by
            have hempty : histories.val.toList = [] :=
              List.length_eq_zero_iff.mp histories.val.property
            exact htotal (by simpa [hempty] using histories.property.2.symm)⟩
          change Nat.card (Family 0 0 total) = _; simp [coeff_one, htotal]
      · have : IsEmpty (Family 0 size total) := ⟨fun histories => by
          have hempty : histories.val.toList = [] :=
            List.length_eq_zero_iff.mp histories.val.property
          exact hsize (by simpa [hempty] using histories.property.1.symm)⟩
        change Nat.card (Family 0 size total) = _
        cases total <;> simp [coeff_one, hsize]
    | succ pieces ih =>
      let (size total : ℕ) : Fintype (Fiber size total) := Fintype.ofFinite _
      let (size total : ℕ) : Fintype (Family pieces size total) := Fintype.ofFinite _
      change Nat.card (Family (pieces + 1) size total) = _
      rw [Nat.card_congr (split_family pieces size total), Nat.card_sigma]
      simp_rw [Nat.card_sigma, Nat.card_prod]
      change (∑ lengths : ↑(Finset.antidiagonal size),
        ∑ spends : ↑(Finset.antidiagonal total),
          Nat.card (Fiber lengths.val.1 spends.val.1) *
            Nat.card (Family pieces lengths.val.2 spends.val.2)) = _
      have hcounts (size total : ℕ) : Nat.card (Family pieces size total) =
          coeff size (coeff total (pureSeries ^ pieces)) := ih size total
      simp_rw [hcounts]; rw [pow_succ', coeff_mul]; simp only [map_sum, coeff_mul]
      rw [Finset.sum_comm]
      have single_count (size total : ℕ) :
          coeff size (coeff total pureSeries) = Nat.card (Fiber size total) := by
        simp [pureSeries, Fiber]
      simp_rw [single_count]
      let term := fun (lengths spends : ℕ × ℕ) =>
        Nat.card (Fiber lengths.1 spends.1) * coeff lengths.2 (coeff spends.2 (pureSeries ^ pieces))
      change (∑ spends : ↑(Finset.antidiagonal total),
        ∑ lengths : ↑(Finset.antidiagonal size), term lengths.val spends.val) =
          ∑ spends ∈ Finset.antidiagonal total,
            ∑ lengths ∈ Finset.antidiagonal size, term lengths spends
      calc
        _ = ∑ spends : ↑(Finset.antidiagonal total),
            ∑ lengths ∈ Finset.antidiagonal size, term lengths spends.val := by
          apply Finset.sum_congr rfl
          intro spends hspend
          exact Finset.sum_coe_sort (Finset.antidiagonal size)
            (fun lengths => term lengths spends.val)
        _ = _ := Finset.sum_coe_sort (Finset.antidiagonal total)
          (fun spends => ∑ lengths ∈ Finset.antidiagonal size, term lengths spends)
  suffices coefficients : ∀ size total : ℕ, coeff (size + 1) (coeff total pureSeries) =
        ∑ gap ∈ Finset.range (total + 1), ∑ chosen ∈ Finset.range (gap + 1),
          gap.choose chosen * if chosen ≤ size then coeff (size - chosen)
              (coeff (total - gap) (pureSeries ^ (chosen + 1))) else 0 by
    classical
    let sizeVar : PowerSeries (PowerSeries ℕ) := C X
    let factor : PowerSeries (PowerSeries ℕ) := 1 + sizeVar * pureSeries
    let step : PowerSeries (PowerSeries ℕ) := X * factor
    let geometric := fun bound : ℕ => ∑ gap ∈ Finset.range (bound + 1), step ^ gap
    have cast_constant (count : ℕ) :
        C (C count) = (count : PowerSeries (PowerSeries ℕ)) := by
      rw [show C count = (count : PowerSeries ℕ) from
        map_natCast (C : ℕ →+* PowerSeries ℕ) count]
      exact map_natCast C count
    have binomial (gap : ℕ) : pureSeries * factor ^ gap = ∑ chosen ∈ Finset.range (gap + 1),
          C (X ^ chosen) * pureSeries ^ (chosen + 1) * C (C (gap.choose chosen)) := by
      dsimp [factor]; rw [add_comm (1 : PowerSeries (PowerSeries ℕ)), add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chosen hchosen
      simp only [one_pow, mul_one, mul_pow, sizeVar, ← map_pow, cast_constant]
      ring
    have expanded (size remaining gap : ℕ) :
        coeff size (coeff remaining (pureSeries * factor ^ gap)) =
          ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * if chosen ≤ size then
            coeff (size - chosen) (coeff remaining (pureSeries ^ (chosen + 1))) else 0 := by
      rw [binomial]; simp only [map_sum, coeff_mul_C, coeff_C_mul, coeff_X_pow_mul']
      apply Finset.sum_congr rfl
      intro chosen hchosen
      split_ifs <;> simp [mul_comm]
    have zero_size (total : ℕ) :
        coeff 0 (coeff total pureSeries) = if total = 0 then 1 else 0 := by
      let Fiber := {history : PureHistory // history.val.length = 0 ∧ spend history.val = total}
      have hempty (history : Fiber) : history.val.val = [] :=
        List.length_eq_zero_iff.mp history.property.1
      have hcoeff : coeff 0 (coeff total pureSeries) =
          Nat.card Fiber := by simp only [pureSeries, coeff_mk, Fiber]
      rw [hcoeff]
      by_cases htotal : total = 0
      · subst total
        let empty : Fiber := ⟨⟨[], [], PureRun.nil []⟩, rfl, rfl⟩
        let : Unique Fiber :=
          { default := empty
            uniq := fun history => Subtype.ext (Subtype.ext (hempty history)) }
        simp
      · have : IsEmpty Fiber := ⟨fun history => by
          have h := history.property.2
          rw [hempty history] at h; exact htotal h.symm⟩
        simp [htotal]
    have cutoff (bound degree : ℕ) (hdegree : degree ≤ bound) :
        coeff degree pureSeries = coeff degree (1 + sizeVar * pureSeries * geometric bound) := by
      apply PowerSeries.ext
      intro size
      have polynomial : sizeVar * pureSeries * geometric bound =
          ∑ gap ∈ Finset.range (bound + 1),
            X ^ gap * (sizeVar * (pureSeries * factor ^ gap)) := by
        dsimp [geometric, step]; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro gap hgap; rw [mul_pow]; ring
      rw [polynomial]; simp only [map_add, map_sum, coeff_X_pow_mul']
      have truncated : (∑ gap ∈ Finset.range (bound + 1), coeff size (if gap ≤ degree then
            coeff (degree - gap) (sizeVar * (pureSeries * factor ^ gap))
          else 0)) = ∑ gap ∈ Finset.range (degree + 1), coeff size
              (coeff (degree - gap) (sizeVar * (pureSeries * factor ^ gap))) := by
        rw [← Finset.sum_subset (s₁ := Finset.range (degree + 1))
          (s₂ := Finset.range (bound + 1)) (Finset.range_mono (by omega))]
        · apply Finset.sum_congr rfl
          intro gap hgap; simp only [Finset.mem_range] at hgap; rw [if_pos (by omega)]
        · intro gap hgap houtside
          simp only [Finset.mem_range] at houtside
          rw [if_neg (by omega), map_zero]
      rw [truncated]
      cases size with
      | zero => rw [zero_size]; simp [sizeVar, coeff_C_mul, coeff_zero_X_mul, coeff_one]
      | succ size =>
        simp only [sizeVar, coeff_C_mul, coeff_succ_X_mul]
        rw [coefficients]; simp only [expanded]
        have hunit : coeff (size + 1) (coeff degree (1 : PowerSeries (PowerSeries ℕ))) = 0 := by
          by_cases hzero : degree = 0 <;> simp [coeff_one, hzero]
        rw [hunit, zero_add]
    have congr_product (bound : ℕ) :
        coeff bound (step * pureSeries) = coeff bound
            (step * (1 + sizeVar * pureSeries * geometric bound)) := by
      rw [coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro pair hpair
      have h := Finset.mem_antidiagonal.mp hpair
      rw [cutoff bound pair.2 (by omega)]
    have geometric_identity (bound : ℕ) :
        geometric bound + step ^ (bound + 1) = 1 + step * geometric bound := by
      induction bound with
      | zero => simp [geometric]
      | succ bound ih =>
        have hnext : geometric (bound + 1) = geometric bound + step ^ (bound + 1) :=
          Finset.sum_range_succ _ _
        calc
          _ = geometric bound + step ^ (bound + 1) + step * step ^ (bound + 1) := by
            rw [hnext]; ring
          _ = 1 + step * geometric bound + step * step ^ (bound + 1) := by rw [ih]
          _ = _ := by rw [hnext]; ring
    apply PowerSeries.ext
    intro total
    change coeff total (pureSeries + step) =
      coeff total (1 + sizeVar * pureSeries + step * pureSeries)
    rw [map_add, map_add, cutoff total total le_rfl, congr_product]
    have cleared :
        (1 + sizeVar * pureSeries * geometric total) + step +
            sizeVar * pureSeries * step ^ (total + 1) =
          1 + sizeVar * pureSeries + step * (1 + sizeVar * pureSeries * geometric total) := by
      calc
        _ = 1 + step + sizeVar * pureSeries * (geometric total + step ^ (total + 1)) := by ring
        _ = _ := by rw [geometric_identity]; ring
    have discarded : coeff total (sizeVar * pureSeries * step ^ (total + 1)) = 0 := by
      have hhigh : sizeVar * pureSeries * step ^ (total + 1) = X ^ (total + 1) *
            (sizeVar * pureSeries * factor ^ (total + 1)) := by dsimp [step]; rw [mul_pow]; ring
      rw [hhigh, coeff_X_pow_mul', if_neg (by omega)]
    have h := congrArg (coeff total) cleared
    simpa only [map_add, discarded, add_zero] using h
  intro size total
  classical
  let Fiber := {history : PureHistory //
    history.val.length = size + 1 ∧ spend history.val = total}
  let Family := fun (chosen remaining : ℕ) =>
    {histories : List.Vector PureHistory (chosen + 1) //
      chosen + (histories.toList.map (fun history => history.val.length)).sum = size ∧
      (histories.toList.map (fun history => spend history.val)).sum = remaining}
  let Data := Σ gap : Fin (total + 1), Σ selected : Finset (Fin gap.val),
    Family selected.card (total - gap.val)
  let Raw := Σ gap : ℕ, Σ selected : Finset (Fin gap),
    List.Vector PureHistory (selected.card + 1)
  obtain ⟨cuts, hcuts⟩ := firstCuts
  let raw : Data → Raw := fun data => ⟨data.1.val, data.2.1, data.2.2.val⟩
  have raw_injective : Function.Injective raw := by
    rintro ⟨⟨firstGap, hfirstGap⟩, firstSet, firstPieces⟩
      ⟨⟨secondGap, hsecondGap⟩, secondSet, secondPieces⟩ heq
    obtain ⟨hgap, hrest⟩ := Sigma.mk.inj heq
    dsimp only at hgap
    subst secondGap
    have hrest' := eq_of_heq hrest
    obtain ⟨hselected, hpieces⟩ := Sigma.mk.inj hrest'
    dsimp only at hselected hpieces
    subst secondSet
    have hpieces' : firstPieces.val = secondPieces.val := eq_of_heq hpieces
    have := Subtype.ext hpieces'
    subst secondPieces
    rfl
  let encode : Data → Fiber := fun data => by
    refine ⟨(cuts.symm (raw data)).val, ?_, ?_⟩
    · obtain ⟨recursive, hsites, hpieces, hreplay, hsize, hspend⟩ := hcuts (raw data)
      change (cuts.symm (raw data)).val.val.length = 1 + data.2.1.card +
        (data.2.2.val.toList.map (fun history => history.val.length)).sum at hsize
      have h := data.2.2.property.1
      dsimp [Family] at h
      change (cuts.symm (raw data)).val.val.length = size + 1; omega
    · obtain ⟨recursive, hsites, hpieces, hreplay, hsize, hspend⟩ := hcuts (raw data)
      change spend (cuts.symm (raw data)).val.val = data.1.val +
        (data.2.2.val.toList.map (fun history => spend history.val)).sum at hspend
      have h := data.2.2.property.2
      have hgap := data.1.is_lt
      dsimp [Family] at h
      change spend (cuts.symm (raw data)).val.val = total; omega
  let decode : Fiber → Data := fun history => by
    have hnonempty : history.val.val ≠ [] := by
      intro heq
      have h := history.property.1
      rw [heq, List.length_nil] at h; omega
    let source : {history : PureHistory // history.val ≠ []} := ⟨history.val, hnonempty⟩
    let data := cuts source
    have weights : (cuts.symm data).val.val.length =
        1 + data.2.1.card + (data.2.2.toList.map (fun history => history.val.length)).sum ∧
        spend (cuts.symm data).val.val =
          data.1 + (data.2.2.toList.map (fun history => spend history.val)).sum := by
      obtain ⟨recursive, hsites, hpieces, hreplay, hsize, hspend⟩ := hcuts data
      exact ⟨hsize, hspend⟩
    have hsize := weights.1
    have hspend := weights.2
    have hsource : cuts.symm data = source := cuts.symm_apply_apply source
    rw [hsource] at hsize hspend
    change history.val.val.length = 1 + data.2.1.card +
      (data.2.2.toList.map (fun history => history.val.length)).sum at hsize
    change spend history.val.val = data.1 +
      (data.2.2.toList.map (fun history => spend history.val)).sum at hspend
    have hgap : data.1 < total + 1 := by have h := history.property.2; omega
    refine ⟨⟨data.1, hgap⟩, data.2.1, ⟨data.2.2, ?_, ?_⟩⟩
    · have h := history.property.1
      change data.2.1.card + (data.2.2.toList.map (fun history => history.val.length)).sum = size
      omega
    · have h := history.property.2
      change (data.2.2.toList.map (fun history => spend history.val)).sum = total - data.1; omega
  have raw_decode (history : Fiber) : raw (decode history) = cuts ⟨history.val, by
        intro heq
        have h := history.property.1
        rw [heq, List.length_nil] at h; omega⟩ := by dsimp [raw, decode]
  have encode_injective : Function.Injective encode := by
    intro first second heq
    apply raw_injective
    apply cuts.symm.injective
    apply Subtype.ext
    exact congrArg (fun history : Fiber => history.val) heq
  have encode_decode (history : Fiber) : encode (decode history) = history := by
    apply Subtype.ext
    change (cuts.symm (raw (decode history))).val = history.val
    rw [raw_decode, cuts.symm_apply_apply]
  let stratification : Fiber ≃ Data :=
    { toFun := decode
      invFun := encode
      left_inv := encode_decode
      right_inv := fun data => encode_injective (encode_decode (encode data)) }
  let values : Set (List PureStep) := {steps | steps.length = size + 1 ∧
    spend steps = total ∧ ∃ ending, PureRun [] steps ending}
  let : Finite values := (pure_histories_finite (size + 1) total).to_subtype
  let : Finite Fiber := Finite.of_injective
    (fun history => (⟨history.val.val, history.property.1,
      history.property.2, history.val.property⟩ : values))
    (fun first second heq =>
      Subtype.ext (Subtype.ext (congrArg (fun value : values => value.val) heq)))
  let : Finite Data := Finite.of_equiv Fiber stratification
  let (gap : Fin (total + 1)) (selected : Finset (Fin gap.val)) :
      Finite (Family selected.card (total - gap.val)) :=
    Finite.of_injective (fun histories => (⟨gap, selected, histories⟩ : Data))
      (fun first second heq => by
        exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj heq).2)).2)
  have family_count (gap : Fin (total + 1)) (selected : Finset (Fin gap.val)) :
      Nat.card (Family selected.card (total - gap.val)) = if selected.card ≤ size then
        coeff (size - selected.card) (coeff (total - gap.val) (pureSeries ^ (selected.card + 1)))
        else 0 := by
    by_cases hchosen : selected.card ≤ size
    · rw [if_pos hchosen]
      let weights : Family selected.card (total - gap.val) ≃
          {histories : List.Vector PureHistory (selected.card + 1) //
            (histories.toList.map (fun history => history.val.length)).sum =
              size - selected.card ∧
            (histories.toList.map (fun history => spend history.val)).sum = total - gap.val} :=
        Equiv.subtypeEquivRight fun histories => by
          constructor <;> rintro ⟨hsize, hspend⟩ <;> exact ⟨by omega, hspend⟩
      rw [Nat.card_congr weights]; exact (orderedProducts _ _ _).2
    · rw [if_neg hchosen]
      have : IsEmpty (Family selected.card (total - gap.val)) :=
        ⟨fun histories => by have h := histories.property.1; omega⟩
      exact Nat.card_of_isEmpty
  have sum_subsets (gap : ℕ) (value : ℕ → ℕ) :
      (∑ selected : Finset (Fin gap), value selected.card) =
        ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * value chosen := by
    calc
      _ = ∑ selected ∈ (Finset.univ : Finset (Fin gap)).powerset, value selected.card := by simp
      _ = _ := by
        rw [Finset.sum_powerset]
        simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_powersetCard,
          nsmul_eq_mul, Nat.cast_id]
  have coeff_fiber : coeff (size + 1) (coeff total pureSeries) =
      Nat.card Fiber := by simp only [pureSeries, coeff_mk, Fiber]
  let (gap : Fin (total + 1)) :
      Finite (Σ selected : Finset (Fin gap.val), Family selected.card (total - gap.val)) :=
    Finite.of_injective (fun data => (⟨gap, data⟩ : Data))
      (fun first second heq => eq_of_heq (Sigma.mk.inj heq).2)
  rw [coeff_fiber]; rw [Nat.card_congr stratification, Nat.card_sigma]
  simp_rw [Nat.card_sigma, family_count]
  calc
    _ = ∑ gap : Fin (total + 1), ∑ chosen ∈ Finset.range (gap.val + 1),
        gap.val.choose chosen * if chosen ≤ size then coeff (size - chosen)
            (coeff (total - gap.val) (pureSeries ^ (chosen + 1))) else 0 := by
      apply Finset.sum_congr rfl
      intro gap hgap
      exact sum_subsets gap.val (fun chosen => if chosen ≤ size then coeff (size - chosen)
          (coeff (total - gap.val) (pureSeries ^ (chosen + 1))) else 0)
    _ = _ := Fin.sum_univ_eq_sum_range (fun gap =>
      ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * if chosen ≤ size then
        coeff (size - chosen) (coeff (total - gap) (pureSeries ^ (chosen + 1))) else 0) (total + 1)
end D5.S3.Combinatorics.WeakAscent.WeakAscent215Decomposition
