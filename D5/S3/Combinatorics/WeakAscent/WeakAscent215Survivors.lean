/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Survivors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Survivors
   mirror-E: none(waiver:weighted-surviving-site-decomposition)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.NoZeroDivisors]
   utility: none
   digest: Counts marked surviving sites by cutting at original fresh sites in every bidegree. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215GroupedRenewal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Survivors

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Decomposition WeakAscent215Endpoints
open PowerSeries
open WeakAscent215Finite WeakAscent215Products WeakAscent215GroupedRenewal

theorem survivor_series : survivorSeries = pureSeries * recordSeries := by
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
  have survivorCuts :
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
                data.1 + (data.2.2.toList.map (fun h => spend h.val)).sum ∧
              finalPiece recursive = data.2.2.reverse.head ∧
              oldCount (replayEquiv.symm data).val = oldCount (finalPiece recursive) +
                if data.2.1 = ∅ then 1 else 0 := by
    have run_unique (stack : List Bool) (steps : List PureStep) (first second : List Bool)
        (hfirst : PureRun stack steps first) (hsecond : PureRun stack steps second) :
        first = second := by
      induction hfirst generalizing second with
      | nil stack => cases hsecond; rfl
      | record stack ending rest gap htail ih =>
        cases hsecond with
        | record _ _ _ _ htail' => exact ih _ htail'
      | descend stack ending rest site hsite hfresh htail ih =>
        cases hsecond with
        | descend _ _ _ _ _ _ htail' => exact ih _ htail'
    obtain ⟨replayEquiv, hdecode⟩ := first_record_decomposition.1
    let base (gap : ℕ) (old : Bool) := List.replicate gap false ++ if old then [true] else []
    have history_run (history : PureHistory) :
        PureRun [] history.val (Classical.choose history.property) :=
      Classical.choose_spec history.property
    have append_run (stack middle ending : List Bool) (front suffix : List PureStep)
        (first : PureRun stack front middle) (second : PureRun middle suffix ending) :
        PureRun stack (front ++ suffix) ending := by
      induction first with
      | nil stack => exact second
      | record stack middle rest gap tail ih => exact PureRun.record _ _ _ _ (ih second)
      | descend stack middle rest site hsite hfresh tail ih =>
        exact PureRun.descend _ _ _ _ hsite hfresh (ih second)
    have replay_survivors (gap : ℕ) (data : OriginalPieces gap) (old : Bool) :
        ∃ ending, PureRun (base gap old) (data.replay old) ending ∧
          ending.count true = oldCount (finalPiece data) +
            if data.sites = [] ∧ old = true then 1 else 0 := by
      induction data generalizing old with
      | @final gap history =>
        let final := Classical.choose history.property
        refine ⟨base gap old ++ final, ?_, ?_⟩
        · have hpure := (pure_inert_base (base gap old) [] final history.val).mpr
            (history_run history)
          cases old <;> simpa [OriginalPieces.replay, base, List.append_assoc] using hpure
        · cases old <;> simp [base, oldCount, finalPiece, OriginalPieces.sites, final,
            List.count_replicate]
      | @cut gap site history rest ih =>
        obtain ⟨ending, hrest, hcount⟩ := ih false
        let before := Classical.choose history.property
        have hbefore : PureRun (base gap old) (history.val.map
            (PureStep.shift (gap + if old then 1 else 0))) (base gap old ++ before) := by
          have hpure := (pure_inert_base (base gap old) [] before history.val).mpr
            (history_run history)
          cases old <;> simpa [base, List.append_assoc] using hpure
        have hsite : site.val < (base gap old ++ before).length := by
          cases old <;> simp only [base, Bool.false_eq_true, ↓reduceIte,
            List.length_append, List.length_replicate, List.length_cons,
            List.length_nil] <;> omega
        have hfresh : (base gap old ++ before).getD site.val true = false := by
          rw [List.getD_append _ _ _ _ (by cases old <;> simp [base])]
          rw [List.getD_append _ _ _ _ (by
            simp only [List.length_replicate]; exact site.is_lt)]
          exact List.getD_replicate false site.is_lt
        have htake : (base gap old ++ before).take site.val = base site.val false := by
          rw [List.take_append_of_le_length (by cases old <;> simp [base]; omega)]
          simp only [base, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [List.take_append_of_le_length (by
            simp only [List.length_replicate]; exact Nat.le_of_lt site.is_lt),
            List.take_replicate, Nat.min_eq_left (Nat.le_of_lt site.is_lt)]
        refine ⟨ending, ?_, ?_⟩
        · apply append_run _ _ _ _ _ hbefore
          apply PureRun.descend _ _ _ _ hsite hfresh
          rwa [htake]
        · simpa [oldCount, finalPiece, OriginalPieces.sites] using hcount
    refine ⟨replayEquiv, ?_⟩
    intro data
    obtain ⟨recursive, hsites, hpieces, hreplay, hsize, hspend⟩ := hdecode data
    have last_piece {gap : ℕ} (pieces : OriginalPieces gap) :
        pieces.pieces.getLast? = some (finalPiece pieces) := by
      induction pieces with
      | final history => rfl
      | cut site history rest ih =>
        simp only [OriginalPieces.pieces, List.getLast?_cons, ih, Option.getD_some, finalPiece]
    have hlast : finalPiece recursive = data.2.2.reverse.head := by
      apply Option.some.inj
      rw [← last_piece recursive, hpieces, ← List.head?_reverse]
      have hcons := congrArg List.Vector.toList (List.Vector.cons_head_tail data.2.2.reverse)
      rw [← List.Vector.toList_reverse, ← hcons]; rfl
    refine ⟨recursive, hsites, hpieces, hreplay, hsize, hspend, hlast, ?_⟩
    obtain ⟨ending, hrun, hcount⟩ := replay_survivors data.1 recursive true
    have hfull : PureRun [] (.record data.1 :: recursive.replay true) ending := by
      apply PureRun.record
      simpa [base] using hrun
    let actual := Classical.choose (replayEquiv.symm data).val.property
    have hactual : PureRun [] (replayEquiv.symm data).val.val actual :=
      history_run (replayEquiv.symm data).val
    rw [hreplay] at hactual
    have heq := run_unique [] _ _ _ hactual hfull
    change actual.count true = oldCount (finalPiece recursive) + if data.2.1 = ∅ then 1 else 0
    rw [heq]
    have hempty : recursive.sites = [] ↔ data.2.1 = ∅ := by
      rw [hsites]
      constructor
      · intro hnil
        have hlength := congrArg List.length hnil
        rw [Finset.length_sort, List.length_nil] at hlength; exact Finset.card_eq_zero.mp hlength
      · intro hempty
        rw [hempty, Finset.sort_empty]
    simpa [hempty] using hcount
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
  suffices coefficients : ∀ size total : ℕ, coeff (size + 1) (coeff total survivorSeries) =
      coeff (size + 1) (coeff total recordSeries) +
      ∑ gap ∈ Finset.range (total + 1), ∑ chosen ∈ Finset.range (gap + 1),
        gap.choose chosen * if chosen ≤ size then coeff (size - chosen)
            (coeff (total - gap) (survivorSeries * pureSeries ^ chosen))
        else 0 by
    classical
    let sizeVar : PowerSeries (PowerSeries ℕ) := C X
    let factor : PowerSeries (PowerSeries ℕ) := 1 + sizeVar * pureSeries
    let step : PowerSeries (PowerSeries ℕ) := X * factor
    let geometric := fun bound : ℕ => ∑ gap ∈ Finset.range (bound + 1), step ^ gap
    have zero_size (total : ℕ) :
        coeff 0 (coeff total survivorSeries) = 0 ∧
        coeff 0 (coeff total recordSeries) = 0 := by
      constructor
      · let Marked := Σ history : {history : PureHistory //
            history.val.length = 0 ∧ spend history.val = total}, Fin (oldCount history.val)
        have : IsEmpty Marked := ⟨fun data => by
          have hempty : data.1.val.val = [] := List.length_eq_zero_iff.mp data.1.property.1
          have hrun : PureRun [] [] (Classical.choose data.1.val.property) := by
            simpa only [hempty] using Classical.choose_spec data.1.val.property
          have nil_run (ending : List Bool) (run : PureRun [] [] ending) : ending = [] := by
            cases run
            rfl
          have hcount : oldCount data.1.val = 0 := by
            simp only [oldCount, nil_run _ hrun, List.count_nil]
          have hmark := data.2.is_lt
          omega⟩
        simp only [survivorSeries, coeff_mk]
        change Nat.card Marked = 0; exact Nat.card_of_isEmpty
      · let Ending := {history : PureHistory //
          history.val.length = 0 ∧ spend history.val = total ∧
          ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]}
        have : IsEmpty Ending := ⟨fun history => by
          obtain ⟨initialSteps, gap, heq⟩ := history.property.2.2
          have hlength := history.property.1
          rw [heq, List.length_append] at hlength
          simp only [List.length_cons, List.length_nil] at hlength
          omega⟩
        simp only [recordSeries, coeff_mk]
        change Nat.card Ending = 0; exact Nat.card_of_isEmpty
    have cast_constant (count : ℕ) :
        C (C count) = (count : PowerSeries (PowerSeries ℕ)) := by
      rw [show C count = (count : PowerSeries ℕ) from
        map_natCast (C : ℕ →+* PowerSeries ℕ) count]
      exact map_natCast C count
    have binomial (gap : ℕ) : survivorSeries * factor ^ gap =
        ∑ chosen ∈ Finset.range (gap + 1),
        C (X ^ chosen) * (survivorSeries * pureSeries ^ chosen) *
          C (C (gap.choose chosen)) := by
      dsimp [factor]
      rw [add_comm (1 : PowerSeries (PowerSeries ℕ)), add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chosen hchosen
      simp only [one_pow, mul_one, mul_pow, sizeVar, ← map_pow, cast_constant]
      ring
    have expanded (size remaining gap : ℕ) :
        coeff size (coeff remaining (survivorSeries * factor ^ gap)) =
          ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * if chosen ≤ size then
            coeff (size - chosen)
              (coeff remaining (survivorSeries * pureSeries ^ chosen)) else 0 := by
      rw [binomial]; simp only [map_sum, coeff_mul_C, coeff_C_mul]; simp only [coeff_X_pow_mul']
      apply Finset.sum_congr rfl
      intro chosen hchosen
      split_ifs <;> simp [mul_comm]
    have cutoff (bound degree : ℕ) (hdegree : degree ≤ bound) :
        coeff degree survivorSeries = coeff degree
          (recordSeries + sizeVar * survivorSeries * geometric bound) := by
      apply PowerSeries.ext
      intro size
      have polynomial : sizeVar * survivorSeries * geometric bound =
          ∑ gap ∈ Finset.range (bound + 1),
            X ^ gap * (sizeVar * (survivorSeries * factor ^ gap)) := by
        dsimp [geometric, step]; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro gap hgap; rw [mul_pow]; ring
      rw [polynomial]; simp only [map_add, map_sum, coeff_X_pow_mul']
      have truncated : (∑ gap ∈ Finset.range (bound + 1),
          coeff size (if gap ≤ degree then coeff (degree - gap)
              (sizeVar * (survivorSeries * factor ^ gap)) else 0)) =
          ∑ gap ∈ Finset.range (degree + 1), coeff size
            (coeff (degree - gap) (sizeVar * (survivorSeries * factor ^ gap))) := by
        rw [← Finset.sum_subset (s₁ := Finset.range (degree + 1))
          (s₂ := Finset.range (bound + 1)) (Finset.range_mono (by omega))]
        · apply Finset.sum_congr rfl
          intro gap hgap; simp only [Finset.mem_range] at hgap; rw [if_pos (by omega)]
        · intro gap hgap houtside
          simp only [Finset.mem_range] at houtside
          rw [if_neg (by omega), map_zero]
      rw [truncated]
      cases size with
      | zero =>
        rw [(zero_size degree).1, (zero_size degree).2]
        simp [sizeVar, coeff_C_mul, coeff_zero_X_mul]
      | succ size =>
        simp only [sizeVar, coeff_C_mul, coeff_succ_X_mul]
        rw [coefficients]; simp only [expanded]
    have congr_product (bound : ℕ) : coeff bound (step * survivorSeries) = coeff bound
          (step * (recordSeries + sizeVar * survivorSeries * geometric bound)) := by
      rw [coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro pair hpair
      have hdegrees := Finset.mem_antidiagonal.mp hpair
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
    have cleared : survivorSeries + step * recordSeries =
        sizeVar * survivorSeries + recordSeries + step * survivorSeries := by
      apply PowerSeries.ext
      intro total; rw [map_add, map_add, cutoff total total le_rfl, congr_product]
      have identity :
          (recordSeries + sizeVar * survivorSeries * geometric total) +
              step * recordSeries + sizeVar * survivorSeries * step ^ (total + 1) =
            sizeVar * survivorSeries + recordSeries +
              step * (recordSeries + sizeVar * survivorSeries * geometric total) := by
        calc
          _ = recordSeries + step * recordSeries + sizeVar * survivorSeries *
              (geometric total + step ^ (total + 1)) := by ring
          _ = _ := by rw [geometric_identity]; ring
      have discarded : coeff total (sizeVar * survivorSeries * step ^ (total + 1)) = 0 := by
        have hhigh : sizeVar * survivorSeries * step ^ (total + 1) = X ^ (total + 1) *
              (sizeVar * survivorSeries * factor ^ (total + 1)) := by
          dsimp [step]; rw [mul_pow]; ring
        rw [hhigh, coeff_X_pow_mul', if_neg (by omega)]
      have hcoeff := congrArg (coeff total) identity
      simpa only [map_add, discarded, add_zero] using hcoeff
    let castMap := PowerSeries.map (PowerSeries.map (Nat.castRingHom ℤ))
    let seriesD := castMap pureSeries
    let seriesE := castMap recordSeries
    let seriesH := castMap survivorSeries
    let mappedLength : PowerSeries (PowerSeries ℤ) := C X
    let mappedSpend : PowerSeries (PowerSeries ℤ) := X
    let mappedStep := mappedSpend * (1 + mappedLength * seriesD)
    have pureEquation : seriesD + mappedStep =
        1 + mappedLength * seriesD + mappedStep * seriesD := by
      have equation := congrArg castMap first_record_decomposition.2
      simpa only [castMap, map_add, map_mul, map_one,
        PowerSeries.map_C, PowerSeries.map_X] using equation
    have survivorEquation : seriesH + mappedStep * seriesE =
        mappedLength * seriesH + seriesE + mappedStep * seriesH := by
      have equation := congrArg castMap cleared
      simpa only [step, factor, sizeVar, castMap, map_add,
        map_mul, map_one, PowerSeries.map_C, PowerSeries.map_X,
        mappedStep, mappedLength, mappedSpend, seriesD, seriesE, seriesH,
        mul_assoc] using equation
    have difference : (1 - mappedLength - mappedStep) * (seriesH - seriesD * seriesE) = 0 := by
      calc
        _ = (seriesH + mappedStep * seriesE -
              (mappedLength * seriesH + seriesE + mappedStep * seriesH)) -
            seriesE * (seriesD + mappedStep -
              (1 + mappedLength * seriesD + mappedStep * seriesD)) := by ring
        _ = 0 := by rw [survivorEquation, pureEquation]; ring
    have nonzero : 1 - mappedLength - mappedStep ≠ 0 := by
      intro heq
      have constant := congrArg (fun series : PowerSeries (PowerSeries ℤ) =>
        PowerSeries.constantCoeff (PowerSeries.constantCoeff series)) heq
      simp [mappedLength, mappedSpend, mappedStep] at constant
    have heq : seriesH = seriesD * seriesE :=
      eq_of_sub_eq_zero ((mul_eq_zero.mp difference).resolve_left nonzero)
    apply PowerSeries.map_injective _
      (PowerSeries.map_injective (Nat.castRingHom ℤ) Nat.cast_injective)
    simpa only [map_mul] using heq
  intro size total
  classical
  let Fiber := fun size total : ℕ => {history : PureHistory //
    history.val.length = size ∧ spend history.val = total}
  let Family := fun pieces size total : ℕ =>
    {histories : List.Vector PureHistory pieces //
      (histories.toList.map (fun history => history.val.length)).sum = size ∧
      (histories.toList.map (fun history => spend history.val)).sum = total}
  let (size total : ℕ) : Finite (Fiber size total) := by
    let values : Set (List PureStep) := {steps | steps.length = size ∧ spend steps = total ∧
      ∃ ending, PureRun [] steps ending}
    let : Finite values := (pure_histories_finite size total).to_subtype
    exact Finite.of_injective (fun history : Fiber size total =>
      (⟨history.val.val, history.property.1, history.property.2,
        history.val.property⟩ : values))
      (fun first second heq =>
        Subtype.ext (Subtype.ext (congrArg (fun value : values => value.val) heq)))
  let (size total : ℕ) : Fintype (Fiber size total) := Fintype.ofFinite _
  let (pieces size total : ℕ) : Finite (Family pieces size total) :=
    (orderedProducts pieces size total).1
  let (pieces size total : ℕ) : Fintype (Family pieces size total) := Fintype.ofFinite _
  let Marked := fun size total : ℕ => Σ history : Fiber size total, Fin (oldCount history.val)
  have marked_count (pieces size total : ℕ) :
      Nat.card (Σ histories : Family (pieces + 1) size total,
        Fin (oldCount histories.val.reverse.head)) =
      coeff size (coeff total (survivorSeries * pureSeries ^ pieces)) := by
    let Source := Σ histories : Family (pieces + 1) size total,
      Fin (oldCount histories.val.reverse.head)
    let Target := Σ lengths : ↑(Finset.antidiagonal size),
      Σ spends : ↑(Finset.antidiagonal total),
        Marked lengths.val.1 spends.val.1 × Family pieces lengths.val.2 spends.val.2
    let split : Source → Target := fun source => by
      let reversed := source.1.val.reverse
      let first := reversed.head
      let rest := reversed.tail
      let restSize := (rest.toList.map (fun history => history.val.length)).sum
      let restSpend := (rest.toList.map (fun history => spend history.val)).sum
      have hhead : first ::ᵥ rest = reversed := List.Vector.cons_head_tail _
      have hsize : first.val.length + restSize = size := by
        have hlength := source.1.property.1
        have hrev : (reversed.toList.map (fun history => history.val.length)).sum = size :=
          by simpa [reversed, List.Vector.toList_reverse, List.map_reverse] using hlength
        rw [← hhead] at hrev; simpa [restSize] using hrev
      have hspend : spend first.val + restSpend = total := by
        have hspend := source.1.property.2
        have hrev : (reversed.toList.map (fun history => spend history.val)).sum = total :=
          by simpa [reversed, List.Vector.toList_reverse, List.map_reverse] using hspend
        rw [← hhead] at hrev; simpa [restSpend] using hrev
      exact ⟨⟨(first.val.length, restSize), Finset.mem_antidiagonal.mpr hsize⟩,
        ⟨(spend first.val, restSpend), Finset.mem_antidiagonal.mpr hspend⟩,
        ⟨⟨first, rfl, rfl⟩, source.2⟩, ⟨rest, rfl, rfl⟩⟩
    let combine : Target → Source := fun data => by
      let histories := (data.2.2.1.1.val ::ᵥ data.2.2.2.val).reverse
      have hsize : (histories.toList.map (fun history => history.val.length)).sum = size := by
          simp only [histories, List.Vector.toList_reverse, List.map_reverse,
            List.sum_reverse, List.Vector.toList_cons, List.map_cons, List.sum_cons]
          rw [data.2.2.1.1.property.1, data.2.2.2.property.1]
          exact Finset.mem_antidiagonal.mp data.1.property
      have hspend : (histories.toList.map (fun history => spend history.val)).sum = total := by
          simp only [histories, List.Vector.toList_reverse, List.map_reverse,
            List.sum_reverse, List.Vector.toList_cons, List.map_cons, List.sum_cons]
          rw [data.2.2.1.1.property.2, data.2.2.2.property.2]
          exact Finset.mem_antidiagonal.mp data.2.1.property
      refine ⟨⟨histories, hsize, hspend⟩, ?_⟩
      exact ⟨data.2.2.1.2.val, by
        simpa only [histories, List.Vector.reverse_reverse, List.Vector.head_cons]
          using data.2.2.1.2.is_lt⟩
    have combine_split (source : Source) : combine (split source) = source := by
      have hfirst : (combine (split source)).1 = source.1 := by
        apply Subtype.ext
        change (source.1.val.reverse.head ::ᵥ source.1.val.reverse.tail).reverse = _
        rw [List.Vector.cons_head_tail, List.Vector.reverse_reverse]
      exact Sigma.ext hfirst ((Fin.heq_ext_iff
        (congrArg (fun histories => oldCount histories.val.reverse.head) hfirst)).2 rfl)
    have combine_injective : Function.Injective combine := by
      rintro ⟨⟨⟨firstSize, restSize⟩, hsize⟩,
        ⟨⟨⟨firstSpend, restSpend⟩, hspend⟩,
          ⟨⟨first, hfirstSize, hfirstSpend⟩, mark⟩,
          ⟨rest, hrestSize, hrestSpend⟩⟩⟩
        ⟨⟨⟨nextSize, tailSize⟩, hnextSize⟩,
        ⟨⟨⟨nextSpend, tailSpend⟩, hnextSpend⟩,
          ⟨⟨next, hnSize, hnSpend⟩, nextMark⟩,
          ⟨tail, htSize, htSpend⟩⟩⟩ heq
      dsimp only at hfirstSize hfirstSpend hrestSize hrestSpend hnSize hnSpend htSize htSpend
      subst firstSize
      subst firstSpend
      subst restSize
      subst restSpend
      subst nextSize
      subst nextSpend
      subst tailSize
      subst tailSpend
      have hhist := congrArg (fun source : Source => source.1.val) heq
      change (first ::ᵥ rest).reverse = (next ::ᵥ tail).reverse at hhist
      have hforward := congrArg List.Vector.reverse hhist
      simp only [List.Vector.reverse_reverse] at hforward
      have hfirst := congrArg List.Vector.head hforward
      simp only [List.Vector.head_cons] at hfirst
      subst next
      have hrest := congrArg List.Vector.tail hforward
      simp only [List.Vector.tail_cons] at hrest
      subst tail
      have hmark := congrArg (fun source : Source => source.2.val) heq
      change mark.val = nextMark.val at hmark
      have heqMark : mark = nextMark := Fin.ext hmark
      subst nextMark
      rfl
    have split_combine (data : Target) : split (combine data) = data :=
      combine_injective (combine_split (combine data))
    let replayEquiv : Source ≃ Target := ⟨split, combine, combine_split, split_combine⟩
    change Nat.card Source = _; rw [Nat.card_congr replayEquiv, Nat.card_sigma]
    simp_rw [Nat.card_sigma, Nat.card_prod]
    have hfamily (pieces size total : ℕ) : Nat.card (Family pieces size total) =
        coeff size (coeff total (pureSeries ^ pieces)) :=
      (orderedProducts pieces size total).2
    have hmarked (size total : ℕ) : Nat.card (Marked size total) =
        coeff size (coeff total survivorSeries) := by
      simp only [survivorSeries, coeff_mk, Marked, Fiber]
    simp_rw [hfamily, hmarked]; rw [coeff_mul]; simp only [map_sum, coeff_mul]; rw [Finset.sum_comm]
    let term := fun (lengths spends : ℕ × ℕ) =>
      coeff lengths.1 (coeff spends.1 survivorSeries) *
        coeff lengths.2 (coeff spends.2 (pureSeries ^ pieces))
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
  let Shifted := fun chosen remaining : ℕ =>
    {histories : List.Vector PureHistory (chosen + 1) //
      chosen + (histories.toList.map (fun history => history.val.length)).sum = size ∧
      (histories.toList.map (fun history => spend history.val)).sum = remaining}
  let Data := Σ gap : Fin (total + 1), Σ selected : Finset (Fin gap.val),
    Shifted selected.card (total - gap.val)
  let Raw := Σ gap : ℕ, Σ selected : Finset (Fin gap),
    List.Vector PureHistory (selected.card + 1)
  obtain ⟨cuts, hcuts⟩ := survivorCuts
  have cut_weights (data : Raw) :
      (cuts.symm data).val.val.length = 1 + data.2.1.card +
          (data.2.2.toList.map (fun history => history.val.length)).sum ∧
      spend (cuts.symm data).val.val = data.1 +
          (data.2.2.toList.map (fun history => spend history.val)).sum ∧
      oldCount (cuts.symm data).val = oldCount data.2.2.reverse.head +
        if data.2.1 = ∅ then 1 else 0 := by
    obtain ⟨recursive, _, _, _, hsize, hspend, hlast, hcount⟩ := hcuts data
    exact ⟨hsize, hspend, by simpa only [hlast] using hcount⟩
  let raw : Data → Raw := fun data => ⟨data.1.val, data.2.1, data.2.2.val⟩
  have raw_injective : Function.Injective raw := by
    rintro ⟨⟨firstGap, hfirstGap⟩, firstSet, firstPieces⟩
      ⟨⟨secondGap, hsecondGap⟩, secondSet, secondPieces⟩ heq
    obtain ⟨hgap, hrest⟩ := Sigma.mk.inj heq
    dsimp only at hgap
    subst secondGap
    obtain ⟨hselected, hpieces⟩ := Sigma.mk.inj (eq_of_heq hrest)
    dsimp only at hselected hpieces
    subst secondSet
    have hpieces' : firstPieces.val = secondPieces.val := eq_of_heq hpieces
    have := Subtype.ext hpieces'
    subst secondPieces
    rfl
  let encode : Data → Fiber (size + 1) total := fun data => by
    have weights := cut_weights (raw data)
    refine ⟨(cuts.symm (raw data)).val, ?_, ?_⟩
    · have hlength := data.2.2.property.1
      change (cuts.symm (raw data)).val.val.length = size + 1
      have hsize := weights.1
      change (cuts.symm (raw data)).val.val.length = 1 + data.2.1.card +
        (data.2.2.val.toList.map (fun history => history.val.length)).sum at hsize
      omega
    · have htotal := data.2.2.property.2
      have hgap := data.1.is_lt
      have hspend := weights.2.1
      change spend (cuts.symm (raw data)).val.val = data.1.val +
        (data.2.2.val.toList.map (fun history => spend history.val)).sum at hspend
      change spend (cuts.symm (raw data)).val.val = total; omega
  let decode : Fiber (size + 1) total → Data := fun history => by
    have hnonempty : history.val.val ≠ [] := by
      intro heq
      have hlength := history.property.1
      rw [heq, List.length_nil] at hlength; omega
    let source : {history : PureHistory // history.val ≠ []} := ⟨history.val, hnonempty⟩
    let data := cuts source
    have weights := cut_weights data
    rw [cuts.symm_apply_apply source] at weights
    have hsize := weights.1
    have hspend := weights.2.1
    change history.val.val.length = 1 + data.2.1.card +
      (data.2.2.toList.map (fun history => history.val.length)).sum at hsize
    change spend history.val.val = data.1 +
      (data.2.2.toList.map (fun history => spend history.val)).sum at hspend
    refine ⟨⟨data.1, by have htotal := history.property.2; omega⟩,
      data.2.1, ⟨data.2.2, ?_, ?_⟩⟩
    · have hlength := history.property.1
      change data.2.1.card + (data.2.2.toList.map (fun history => history.val.length)).sum = size
      omega
    · have htotal := history.property.2
      change (data.2.2.toList.map (fun history => spend history.val)).sum = total - data.1; omega
  have encode_decode (history : Fiber (size + 1) total) :
      encode (decode history) = history := by
    apply Subtype.ext
    change (cuts.symm (raw (decode history))).val = history.val
    change (cuts.symm (cuts ⟨history.val, _⟩)).val = history.val; rw [cuts.symm_apply_apply]
  have encode_injective : Function.Injective encode := by
    intro first second heq
    apply raw_injective
    apply cuts.symm.injective
    exact Subtype.ext (congrArg (fun history : Fiber (size + 1) total => history.val) heq)
  let stratification : Fiber (size + 1) total ≃ Data := ⟨decode, encode, encode_decode,
      fun data => encode_injective (encode_decode (encode data))⟩
  let : Finite Data := Finite.of_equiv _ stratification
  let (gap : Fin (total + 1)) (selected : Finset (Fin gap.val)) :
      Finite (Shifted selected.card (total - gap.val)) :=
    Finite.of_injective (fun histories => (⟨gap, selected, histories⟩ : Data))
      (fun first second heq => eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj heq).2)).2)
  let (chosen remaining : ℕ) : Finite (Shifted chosen remaining) := by
    by_cases hchosen : chosen ≤ size
    · exact Finite.of_injective (fun histories : Shifted chosen remaining =>
          (⟨histories.val, by have hlength := histories.property.1; omega,
            histories.property.2⟩ : Family (chosen + 1) (size - chosen) remaining))
        (fun first second heq => Subtype.ext
          (congrArg (fun histories : Family (chosen + 1) (size - chosen) remaining =>
            histories.val) heq))
    · have : IsEmpty (Shifted chosen remaining) :=
        ⟨fun histories => by have hlength := histories.property.1; omega⟩
      infer_instance
  let (chosen remaining : ℕ) : Fintype (Shifted chosen remaining) := Fintype.ofFinite _
  have family_count (chosen remaining : ℕ) :
      Nat.card (Shifted chosen remaining) = if chosen ≤ size then coeff (size - chosen)
          (coeff remaining (pureSeries ^ (chosen + 1))) else 0 := by
    by_cases hchosen : chosen ≤ size
    · rw [if_pos hchosen]
      let weights : Shifted chosen remaining ≃ Family (chosen + 1) (size - chosen) remaining :=
        Equiv.subtypeEquivRight fun histories => by
          constructor <;> rintro ⟨hsize, hspend⟩ <;> exact ⟨by omega, hspend⟩
      rw [Nat.card_congr weights]; exact (orderedProducts _ _ _).2
    · rw [if_neg hchosen]
      have : IsEmpty (Shifted chosen remaining) :=
        ⟨fun histories => by have hlength := histories.property.1; omega⟩
      exact Nat.card_of_isEmpty
  have weighted_family (chosen remaining : ℕ) :
      (∑ histories : Shifted chosen remaining, oldCount histories.val.reverse.head) =
        if chosen ≤ size then coeff (size - chosen)
            (coeff remaining (survivorSeries * pureSeries ^ chosen)) else 0 := by
    by_cases hchosen : chosen ≤ size
    · rw [if_pos hchosen]
      let weights : Shifted chosen remaining ≃ Family (chosen + 1) (size - chosen) remaining :=
        Equiv.subtypeEquivRight fun histories => by
          constructor <;> rintro ⟨hsize, hspend⟩ <;> exact ⟨by omega, hspend⟩
      calc
        _ = ∑ histories : Family (chosen + 1) (size - chosen) remaining,
            oldCount histories.val.reverse.head :=
          Fintype.sum_equiv weights _ _ (fun _ => rfl)
        _ = Nat.card (Σ histories : Family (chosen + 1) (size - chosen) remaining,
            Fin (oldCount histories.val.reverse.head)) := by
          rw [Nat.card_sigma]; simp only [Nat.card_fin]
        _ = _ := marked_count chosen (size - chosen) remaining
    · rw [if_neg hchosen]
      have : IsEmpty (Shifted chosen remaining) :=
        ⟨fun histories => by have hlength := histories.property.1; omega⟩
      exact Finset.sum_of_isEmpty _
  have sum_subsets (gap : ℕ) (value : ℕ → ℕ) :
      (∑ selected : Finset (Fin gap), value selected.card) =
        ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * value chosen := by
    calc
      _ = ∑ selected ∈ (Finset.univ : Finset (Fin gap)).powerset, value selected.card := by simp
      _ = _ := by
        rw [Finset.sum_powerset]
        simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_powersetCard,
          nsmul_eq_mul, Nat.cast_id]
  have count : coeff (size + 1) (coeff total survivorSeries) =
      ∑ gap : Fin (total + 1), ∑ selected : Finset (Fin gap.val),
        ((if selected.card ≤ size then
          coeff (size - selected.card) (coeff (total - gap.val)
              (survivorSeries * pureSeries ^ selected.card)) else 0) +
        if selected = ∅ then Nat.card (Shifted selected.card (total - gap.val)) else 0) := by
    have hcoeff : coeff (size + 1) (coeff total survivorSeries) =
        Nat.card (Marked (size + 1) total) := by simp only [survivorSeries, coeff_mk, Marked, Fiber]
    rw [hcoeff]; rw [Nat.card_sigma]; simp only [Nat.card_fin]
    rw [← stratification.symm.sum_comp (fun history => oldCount history.val)]
    change (∑ data : Data, oldCount (encode data).val) = _; rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro gap hgap; rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro selected hselected
    have hcount (histories : Shifted selected.card (total - gap.val)) :
        oldCount (encode ⟨gap, selected, histories⟩).val =
          oldCount histories.val.reverse.head + if selected = ∅ then 1 else 0 :=
      (cut_weights (raw ⟨gap, selected, histories⟩)).2.2
    simp_rw [hcount]; rw [Finset.sum_add_distrib, weighted_family]
    congr 1
    by_cases hempty : selected = ∅ <;> simp [hempty, Nat.card_eq_fintype_card]
  have ending_count : coeff (size + 1) (coeff total recordSeries) = ∑ gap : Fin (total + 1),
        coeff size (coeff (total - gap.val) pureSeries) := by
    have firstZero : coeff (size + 1) (coeff 0 recordSeries) = coeff size (coeff 0 pureSeries) := by
      have hcoeff := congrArg (coeff 0) grouped_renewal.1
      simpa only [map_add, coeff_C_mul, coeff_succ_X_mul,
        coeff_zero_X_mul, add_zero] using congrArg (coeff (size + 1)) hcoeff
    have endingPartial (degree : ℕ) :
        coeff (size + 1) (coeff degree recordSeries) = ∑ gap ∈ Finset.range (degree + 1),
            coeff size (coeff (degree - gap) pureSeries) := by
      induction degree with
      | zero => simpa using firstZero
      | succ degree ih =>
        have hcoeff := congrArg (coeff (degree + 1)) grouped_renewal.1
        have hh := congrArg (coeff (size + 1)) hcoeff
        simp only [map_add, coeff_C_mul, coeff_succ_X_mul] at hh
        rw [hh, ih]
        conv_rhs => rw [Finset.sum_range_succ']
        simp only [Nat.sub_zero, Nat.add_sub_add_right]
        exact add_comm _ _
    rw [endingPartial]; exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [count]; simp_rw [Finset.sum_add_distrib]
  have original : (∑ gap : Fin (total + 1), ∑ selected : Finset (Fin gap.val),
      if selected = ∅ then Nat.card (Shifted selected.card (total - gap.val)) else 0) =
        coeff (size + 1) (coeff total recordSeries) := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [Finset.card_empty, family_count, zero_le, ↓reduceIte, Nat.sub_zero,
      zero_add, pow_one]
    exact ending_count.symm
  rw [original, add_comm]
  congr 1
  calc
    _ = ∑ gap : Fin (total + 1), ∑ chosen ∈ Finset.range (gap.val + 1),
        gap.val.choose chosen * if chosen ≤ size then coeff (size - chosen)
            (coeff (total - gap.val) (survivorSeries * pureSeries ^ chosen))
        else 0 := by
      apply Finset.sum_congr rfl
      intro gap hgap
      exact sum_subsets gap.val (fun chosen => if chosen ≤ size then coeff (size - chosen)
          (coeff (total - gap.val) (survivorSeries * pureSeries ^ chosen)) else 0)
    _ = _ := Fin.sum_univ_eq_sum_range (fun gap =>
      ∑ chosen ∈ Finset.range (gap + 1), gap.choose chosen * if chosen ≤ size then
        coeff (size - chosen) (coeff (total - gap) (survivorSeries * pureSeries ^ chosen)) else 0)
      (total + 1)
end D5.S3.Combinatorics.WeakAscent.WeakAscent215Survivors
