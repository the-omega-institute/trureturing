/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal
   mirror-E: none(waiver:bigraded-old-step-renewal)
   anchors: []
   utility: none
   digest: Groups old-step histories by both weights and counts eligible maximum repetitions. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Decomposition
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Endpoints
import D5.S3.Combinatorics.WeakAscent.WeakAscent215WeightedRenewal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215GroupedRenewal

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Decomposition WeakAscent215Endpoints
open WeakAscent215Renewal WeakAscent215Finite WeakAscent215Products
open WeakAscent215WeightedRenewal
noncomputable def recordSeries : PowerSeries (PowerSeries ℕ) :=
  PowerSeries.mk fun total => PowerSeries.mk fun size =>
    Nat.card {history : PureHistory // history.val.length = size ∧ spend history.val = total ∧
      ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]}
noncomputable def survivorSeries : PowerSeries (PowerSeries ℕ) :=
  PowerSeries.mk fun total => PowerSeries.mk fun size =>
    Nat.card (Σ history : {history : PureHistory //
      history.val.length = size ∧ spend history.val = total}, Fin (oldCount history.val))
noncomputable def fullSeries (inert : Bool) (budget : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun size => Nat.card {steps : List FullStep // steps.length = size ∧
    FullRun (if inert then [true] else []) budget inert steps}
noncomputable def budgetSeries (inert : Bool) : PowerSeries (PowerSeries ℕ) :=
  PowerSeries.mk fun budget => fullSeries inert (budget + 1)
theorem grouped_renewal :
    recordSeries = PowerSeries.C PowerSeries.X * pureSeries + PowerSeries.X * recordSeries ∧
    ∀ inert : Bool,
      let upper := survivorSeries + if inert then pureSeries else 0;
      let maximum := recordSeries + if inert then 1 else 0;
      let tail := PowerSeries.mk fun budget => fullSeries true (budget + 2);
      let oldSteps := PowerSeries.C PowerSeries.X * (upper * budgetSeries false) +
        PowerSeries.C PowerSeries.X * (maximum * tail);
      let balanced := budgetSeries inert +
        PowerSeries.C PowerSeries.X * (maximum * budgetSeries false);
      balanced + PowerSeries.X * oldSteps = pureSeries + oldSteps + PowerSeries.X * balanced := by
  suffices counting :
    recordSeries = PowerSeries.C PowerSeries.X * pureSeries + PowerSeries.X * recordSeries ∧
    ∀ (inert : Bool) (budget depth : ℕ),
    (PowerSeries.coeff (depth + 1) (fullSeries inert budget) = (∑ total ∈ Finset.range budget,
        PowerSeries.coeff (depth + 1) (PowerSeries.coeff total pureSeries)) +
      ∑ size ∈ Finset.range (depth + 1), ∑ total ∈ Finset.range budget,
        let maximum := PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
          if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0;
        let upper := PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
          if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0;
        (upper - maximum) * PowerSeries.coeff (depth - size) (fullSeries false (budget - total)) +
          maximum * PowerSeries.coeff (depth - size) (fullSeries true (budget - total + 1))) ∧
    ∀ size total : ℕ, PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
          (if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0) ≤
        PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
          if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0 by
    refine ⟨counting.1, ?_⟩
    intro inert
    classical
    let upper := survivorSeries + if inert then pureSeries else 0
    let maximum := recordSeries + if inert then 1 else 0
    let tail : PowerSeries (PowerSeries ℕ) :=
      PowerSeries.mk fun budget => fullSeries true (budget + 2)
    let sizeVar : PowerSeries (PowerSeries ℕ) := PowerSeries.C PowerSeries.X
    let slack : PowerSeries (PowerSeries ℕ) := PowerSeries.mk fun budget =>
      ∑ total ∈ Finset.range (budget + 1), PowerSeries.coeff total pureSeries
    have slack_recurrence : slack = pureSeries + PowerSeries.X * slack := by
      apply PowerSeries.ext
      intro budget
      cases budget with
      | zero => simp [slack]
      | succ budget =>
        simp only [slack, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul]
        rw [Finset.sum_range_succ, add_comm]
    have product_coefficient (first second : PowerSeries (PowerSeries ℕ)) (size total : ℕ) :
        PowerSeries.coeff size (PowerSeries.coeff total (first * second)) =
          ∑ length ∈ Finset.range (size + 1), ∑ spend ∈ Finset.range (total + 1),
            PowerSeries.coeff length (PowerSeries.coeff spend first) *
              PowerSeries.coeff (size - length) (PowerSeries.coeff (total - spend) second) := by
      rw [PowerSeries.coeff_mul]
      simp only [map_sum, PowerSeries.coeff_mul]
      rw [Finset.sum_comm]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun length remaining => ∑ pair ∈ Finset.antidiagonal total,
          PowerSeries.coeff length (PowerSeries.coeff pair.1 first) *
            PowerSeries.coeff remaining (PowerSeries.coeff pair.2 second)) size]
      apply Finset.sum_congr rfl
      intro length hlength
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun spend remaining => PowerSeries.coeff length (PowerSeries.coeff spend first) *
          PowerSeries.coeff (size - length) (PowerSeries.coeff remaining second)) total
    have maximum_coefficient (size total : ℕ) :
        PowerSeries.coeff size (PowerSeries.coeff total maximum) =
          PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
            if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0 := by
      cases inert <;> by_cases hsize : size = 0 <;> by_cases htotal : total = 0 <;>
        simp [maximum, PowerSeries.coeff_one, hsize, htotal]
    have upper_coefficient (size total : ℕ) :
        PowerSeries.coeff size (PowerSeries.coeff total upper) =
          PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
            if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0 := by
      cases inert <;> simp [upper]
    have pure_zero (total : ℕ) : PowerSeries.coeff 0 (PowerSeries.coeff total pureSeries) =
        if total = 0 then 1 else 0 := by
      let Fiber := {history : PureHistory // history.val.length = 0 ∧ spend history.val = total}
      have hempty (history : Fiber) : history.val.val = [] :=
        List.length_eq_zero_iff.mp history.property.1
      simp only [pureSeries, PowerSeries.coeff_mk]
      change Nat.card Fiber = _
      by_cases htotal : total = 0
      · subst total
        let empty : Fiber := ⟨⟨[], [], PureRun.nil []⟩, rfl, rfl⟩
        let : Unique Fiber :=
          { default := empty
            uniq := fun history => Subtype.ext (Subtype.ext (hempty history)) }
        simp
      · have : IsEmpty Fiber := ⟨fun history => by
          have hspend := history.property.2
          rw [hempty history] at hspend
          exact htotal hspend.symm⟩
        simp [htotal]
    have full_zero (budget : ℕ) : PowerSeries.coeff 0 (fullSeries inert (budget + 1)) = 1 := by
      let Fiber := {steps : List FullStep // steps.length = 0 ∧
        FullRun (if inert then [true] else []) (budget + 1) inert steps}
      let empty : Fiber := ⟨[], rfl, FullRun.nil _ _ _ (by omega)⟩
      let : Unique Fiber :=
        { default := empty
          uniq := fun history => Subtype.ext (List.length_eq_zero_iff.mp history.property.1) }
      simp only [fullSeries, PowerSeries.coeff_mk]
      exact Nat.card_unique
    have balance : budgetSeries inert + sizeVar * (maximum * budgetSeries false) =
        slack + sizeVar * (upper * budgetSeries false) + sizeVar * (maximum * tail) := by
      apply PowerSeries.ext
      intro budget
      apply PowerSeries.ext
      intro size
      simp only [map_add, sizeVar, PowerSeries.coeff_C_mul]
      cases size with
      | zero =>
        simp only [PowerSeries.coeff_zero_X_mul, add_zero]
        rw [budgetSeries, PowerSeries.coeff_mk, full_zero]
        simp only [slack, PowerSeries.coeff_mk, map_sum, pure_zero]
        simp
      | succ size =>
        simp only [PowerSeries.coeff_succ_X_mul, budgetSeries, PowerSeries.coeff_mk]
        rw [(counting.2 inert (budget + 1) size).1]
        rw [product_coefficient, product_coefficient, product_coefficient]
        simp only [maximum_coefficient, upper_coefficient,
          tail, PowerSeries.coeff_mk, slack, map_sum]
        rw [add_assoc, add_assoc]
        congr 1
        simp_rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro length hlength
        apply Finset.sum_congr rfl
        intro total htotal
        have hbound : total ≤ budget := by simp only [Finset.mem_range] at htotal; omega
        have first_shift : budget + 1 - total = budget - total + 1 := by omega
        simp only [first_shift, show budget - total + 1 + 1 = budget - total + 2 by omega]
        have hle := (counting.2 inert (budget + 1) size).2 length total
        calc
          _ = ((PowerSeries.coeff length (PowerSeries.coeff total survivorSeries) +
                (if inert then PowerSeries.coeff length (PowerSeries.coeff total pureSeries)
                  else 0)) -
              (PowerSeries.coeff length (PowerSeries.coeff total recordSeries) +
                (if inert = true ∧ length = 0 ∧ total = 0 then 1 else 0)) +
              (PowerSeries.coeff length (PowerSeries.coeff total recordSeries) +
                (if inert = true ∧ length = 0 ∧ total = 0 then 1 else 0))) *
              PowerSeries.coeff (size - length) (fullSeries false (budget - total + 1)) +
            (PowerSeries.coeff length (PowerSeries.coeff total recordSeries) +
              (if inert = true ∧ length = 0 ∧ total = 0 then 1 else 0)) *
              PowerSeries.coeff (size - length) (fullSeries true (budget - total + 2)) := by ring
          _ = _ := by rw [Nat.sub_add_cancel hle]
    change (budgetSeries inert + sizeVar * (maximum * budgetSeries false)) +
        PowerSeries.X * (sizeVar * (upper * budgetSeries false) + sizeVar * (maximum * tail)) =
      pureSeries + (sizeVar * (upper * budgetSeries false) +
        sizeVar * (maximum * tail)) + PowerSeries.X *
          (budgetSeries inert + sizeVar * (maximum * budgetSeries false))
    rw [balance]
    conv_lhs => rw [slack_recurrence]
    ring
  refine ⟨?_, ?_⟩
  · classical
    let Fiber := fun size total : ℕ => {history : PureHistory //
      history.val.length = size ∧ spend history.val = total}
    let (size total : ℕ) : Finite (Fiber size total) := by
      let values : Set (List PureStep) := {steps | steps.length = size ∧ spend steps = total ∧
        ∃ ending, PureRun [] steps ending}
      let : Finite values := (pure_histories_finite size total).to_subtype
      exact Finite.of_injective (fun history : Fiber size total =>
        (⟨history.val.val, history.property.1, history.property.2,
          history.val.property⟩ : values))
        (fun first second heq =>
          Subtype.ext (Subtype.ext (congrArg (fun value : values => value.val) heq)))
    obtain ⟨endings, hending⟩ := record_endings
    have ending_count (size total : ℕ) :
        PowerSeries.coeff (size + 1) (PowerSeries.coeff total recordSeries) =
          ∑ gap ∈ Finset.range (total + 1),
            PowerSeries.coeff size (PowerSeries.coeff (total - gap) pureSeries) := by
      let Ending := {history : PureHistory //
        history.val.length = size + 1 ∧ spend history.val = total ∧
          ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]}
      let Data := Σ gap : Fin (total + 1), Fiber size (total - gap.val)
      let append : Data → Ending := fun data =>
        ⟨(endings.symm (data.2.val, data.1.val)).val, by
          have hsize := (hending (data.2.val, data.1.val)).2.1
          rw [data.2.property.1] at hsize
          exact hsize, by
          have hspend := (hending (data.2.val, data.1.val)).2.2
          rw [data.2.property.2] at hspend
          have hgap := data.1.is_lt
          omega, (endings.symm (data.2.val, data.1.val)).property⟩
      let remove : Ending → Data := fun history => by
        let source := (⟨history.val, history.property.2.2⟩ :
          {history : PureHistory // ∃ initialSteps gap,
            history.val = initialSteps ++ [.record gap]})
        let data := endings source
        have hsize := (hending data).2.1
        have hspend := (hending data).2.2
        rw [endings.symm_apply_apply source] at hsize hspend
        have hgap : data.2 < total + 1 := by
          have h := history.property.2.1
          change spend history.val.val = spend data.1.val + data.2 at hspend
          omega
        refine ⟨⟨data.2, hgap⟩, ⟨data.1, ?_, ?_⟩⟩
        · have h := history.property.1
          change history.val.val.length = data.1.val.length + 1 at hsize
          omega
        · have h := history.property.2.1
          change spend history.val.val = spend data.1.val + data.2 at hspend
          change spend data.1.val = total - data.2
          omega
      have append_injective : Function.Injective append := by
        rintro ⟨⟨firstGap, hfirstGap⟩, firstHistory⟩
          ⟨⟨secondGap, hsecondGap⟩, secondHistory⟩ heq
        have hraw : (firstHistory.val, firstGap) = (secondHistory.val, secondGap) := by
          apply endings.symm.injective
          apply Subtype.ext
          exact congrArg (fun history : Ending => history.val) heq
        obtain ⟨hhistory, hgap⟩ := Prod.mk.inj hraw
        subst secondGap
        have hsecond : firstHistory = secondHistory := Subtype.ext hhistory
        subst secondHistory
        rfl
      have append_remove (history : Ending) : append (remove history) = history := by
        apply Subtype.ext
        change (endings.symm ((remove history).2.val, (remove history).1.val)).val = history.val
        have hraw : ((remove history).2.val, (remove history).1.val) =
            endings ⟨history.val, history.property.2.2⟩ := rfl
        rw [hraw, endings.symm_apply_apply]
      let replayEquiv : Ending ≃ Data := ⟨remove, append, append_remove,
          fun data => append_injective (append_remove (append data))⟩
      have coeff_ending : PowerSeries.coeff (size + 1)
          (PowerSeries.coeff total recordSeries) = Nat.card Ending := by
        simp only [recordSeries, PowerSeries.coeff_mk, Ending]
      rw [coeff_ending, Nat.card_congr replayEquiv]
      let (gap : Fin (total + 1)) : Fintype (Fiber size (total - gap.val)) := Fintype.ofFinite _
      rw [Nat.card_sigma]
      have count (gap : Fin (total + 1)) : Nat.card (Fiber size (total - gap.val)) =
          PowerSeries.coeff size (PowerSeries.coeff (total - gap.val) pureSeries) := by
        simp only [pureSeries, PowerSeries.coeff_mk, Fiber]
      simp_rw [count]
      exact Fin.sum_univ_eq_sum_range
        (fun gap => PowerSeries.coeff size (PowerSeries.coeff (total - gap) pureSeries))
        (total + 1)
    have no_zero (total : ℕ) :
        PowerSeries.coeff 0 (PowerSeries.coeff total recordSeries) = 0 := by
      let Ending := {history : PureHistory // history.val.length = 0 ∧
        spend history.val = total ∧
          ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]}
      have : IsEmpty Ending := ⟨fun history => by
        obtain ⟨initialSteps, gap, heq⟩ := history.property.2.2
        have hsize := history.property.1
        rw [heq, List.length_append, List.length_singleton] at hsize
        omega⟩
      simp only [recordSeries, PowerSeries.coeff_mk]
      exact Nat.card_of_isEmpty
    apply PowerSeries.ext
    intro total
    apply PowerSeries.ext
    intro size
    simp only [map_add, PowerSeries.coeff_C_mul]
    cases size with
    | zero =>
      rw [no_zero]
      cases total <;> simp [PowerSeries.coeff_zero_X_mul, no_zero, PowerSeries.coeff_succ_X_mul]
    | succ size =>
      rw [PowerSeries.coeff_succ_X_mul, ending_count]
      cases total with
      | zero => simp [PowerSeries.coeff_zero_X_mul]
      | succ total =>
        rw [PowerSeries.coeff_succ_X_mul, ending_count, Finset.sum_range_succ']
        simp only [Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro gap hgap
        have heq : total + 1 - (gap + 1) = total - gap := by omega
        rw [heq]
  intro inert budget depth
  classical
  let Fiber := fun size total : ℕ => {history : PureHistory //
    history.val.length = size ∧ spend history.val = total}
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
  have mode_append (mode : Bool) (initialSteps suffix : List PureStep) :
      finishMode mode (initialSteps ++ suffix) =
        finishMode (finishMode mode initialSteps) suffix := by
    induction initialSteps generalizing mode with
    | nil => rfl
    | cons first rest ih => cases first <;> simp only [List.cons_append, finishMode, ih]
  have record_iff (steps : List PureStep) :
      finishMode false steps = true ↔
        ∃ initialSteps gap, steps = initialSteps ++ [.record gap] := by
    induction steps using List.reverseRecOn with
    | nil => simp [finishMode]
    | append_singleton initialSteps last ih =>
      rw [mode_append]
      cases last with
      | record gap =>
        constructor
        · intro hmode
          exact ⟨initialSteps, gap, rfl⟩
        · intro hrecord
          rfl
      | descend site =>
        constructor
        · simp [finishMode]
        · rintro ⟨initial, gap, heq⟩
          have hlast := congrArg List.getLast? heq
          simp at hlast
  have mode_positive (stack ending : List Bool) (steps : List PureStep)
      (hrun : PureRun stack steps ending) (mode : Bool)
      (hinitial : mode = true → 0 < stack.count true)
      (hmode : finishMode mode steps = true) : 0 < ending.count true := by
    induction hrun generalizing mode with
    | nil stack => exact hinitial hmode
    | record stack ending rest gap htail ih =>
      apply ih true _ hmode
      intro htrue
      simp only [List.count_append, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte]
      omega
    | descend stack ending rest site hsite hfresh htail ih => exact ih false (by simp) hmode
  have eligible (size total : ℕ) (history : Fiber size total) :
      (if finishMode inert history.val.val then 1 else 0) ≤
        oldCount history.val + if inert then 1 else 0 := by
    cases inert with
    | true =>
      change (if finishMode true history.val.val then 1 else 0) ≤ oldCount history.val + 1
      split_ifs <;> omega
    | false =>
      by_cases hmode : finishMode false history.val.val = true
      · have hrun : PureRun [] history.val.val (Classical.choose history.val.property) :=
          Classical.choose_spec history.val.property
        have hpositive := mode_positive _ _ _ hrun false (by simp) hmode
        simpa [oldCount, hmode] using hpositive
      · simp [hmode]
  have pure_count (size total : ℕ) : Nat.card (Fiber size total) =
      PowerSeries.coeff size (PowerSeries.coeff total pureSeries) := by
    simp only [pureSeries, PowerSeries.coeff_mk, Fiber]
  have survivors (size total : ℕ) :
      (∑ history : Fiber size total, oldCount history.val) =
        PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) := by
    simp only [survivorSeries, PowerSeries.coeff_mk]
    change _ = Nat.card (Σ history : Fiber size total, Fin (oldCount history.val))
    rw [Nat.card_sigma]
    simp
  have sum_indicator (size total : ℕ) (predicate : Fiber size total → Prop) :
      (∑ history : Fiber size total, if predicate history then 1 else 0) =
        Nat.card {history : Fiber size total // predicate history} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have record_count (size total : ℕ) :
      (∑ history : Fiber size total,
        if ∃ initialSteps gap, history.val.val = initialSteps ++ [.record gap] then 1 else 0) =
        PowerSeries.coeff size (PowerSeries.coeff total recordSeries) := by
    rw [sum_indicator]
    simp only [recordSeries, PowerSeries.coeff_mk]
    let flatten : {history : Fiber size total //
        ∃ initialSteps gap, history.val.val = initialSteps ++ [.record gap]} ≃
        {history : PureHistory // history.val.length = size ∧ spend history.val = total ∧
          ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]} :=
      { toFun := fun history => ⟨history.val.val,
          history.val.property.1, history.val.property.2, history.property⟩
        invFun := fun history =>
          ⟨⟨history.val, history.property.1, history.property.2.1⟩, history.property.2.2⟩
        left_inv := fun history => rfl
        right_inv := fun history => rfl }
    exact Nat.card_congr flatten
  have emptyFiber : Nat.card (Fiber 0 0) = 1 := by
    let empty : Fiber 0 0 := ⟨⟨[], [], PureRun.nil []⟩, rfl, rfl⟩
    let : Unique (Fiber 0 0) :=
      { default := empty
        uniq := fun history => Subtype.ext (Subtype.ext
          (List.length_eq_zero_iff.mp history.property.1)) }
    exact Nat.card_unique
  have empty_iff (size total : ℕ) (history : Fiber size total) :
      history.val.val = [] ↔ size = 0 ∧ total = 0 := by
    constructor
    · intro heq
      have hsize := history.property.1
      have htotal := history.property.2
      rw [heq] at hsize htotal
      exact ⟨hsize.symm, htotal.symm⟩
    · rintro ⟨rfl, htotal⟩
      exact List.length_eq_zero_iff.mp history.property.1
  have maximum_count (size total : ℕ) :
      (∑ history : Fiber size total, if finishMode inert history.val.val then 1 else 0) =
        PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
          if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0 := by
    have separate (history : Fiber size total) :
        (if finishMode inert history.val.val then 1 else 0) =
          (if ∃ initialSteps gap, history.val.val = initialSteps ++ [.record gap] then 1 else 0) +
          if inert = true ∧ history.val.val = [] then 1 else 0 := by
      rw [← record_iff]
      cases hsteps : history.val.val with
      | nil => cases inert <;> simp [finishMode]
      | cons first rest =>
        have hmode : finishMode inert (first :: rest) = finishMode false (first :: rest) := by
          cases first <;> rfl
        have hnonempty : ¬ (inert = true ∧ first :: rest = []) := by simp
        rw [if_neg hnonempty, add_zero]
        by_cases hfinal : finishMode false (first :: rest) = true
        · have hactual := hmode.trans hfinal
          rw [if_pos hactual, if_pos hfinal]
        · have hactual : finishMode inert (first :: rest) ≠ true := by
            intro heq
            exact hfinal (hmode.symm.trans heq)
          rw [if_neg hactual, if_neg hfinal]
    simp_rw [separate, empty_iff]
    rw [Finset.sum_add_distrib, record_count, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.cast_id]
    split_ifs with hcondition
    · obtain ⟨hinert, rfl, rfl⟩ := hcondition
      rw [emptyFiber, one_mul]
    · simp
  have maximum_le (size total : ℕ) :
      PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
          (if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0) ≤
        PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
          if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0 := by
    have hsum := Finset.sum_le_sum
      (fun (history : Fiber size total) (_ : history ∈ Finset.univ) =>
        eligible size total history)
    rw [maximum_count, Finset.sum_add_distrib, survivors, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, pure_count] at hsum
    cases inert <;> simpa using hsum
  refine ⟨?_, maximum_le⟩
  let Prefix := {history : PureHistory //
    history.val.length ≤ depth ∧ spend history.val < budget}
  obtain ⟨enumeration, hrenewal⟩ := weighted_renewal inert budget depth
  let : Fintype Prefix := enumeration
  let Grouped := Σ size : Fin (depth + 1), Σ total : Fin budget, Fiber size.val total.val
  let regroup : Prefix → Grouped := fun history =>
    ⟨⟨history.val.val.length, by omega⟩, ⟨spend history.val.val, history.property.2⟩,
      ⟨history.val, rfl, rfl⟩⟩
  let ungroup : Grouped → Prefix := fun data =>
    ⟨data.2.2.val, by
      have hsize := data.2.2.property.1
      have hbound := data.1.is_lt
      omega, by
      rw [data.2.2.property.2]
      exact data.2.1.is_lt⟩
  have ungroup_regroup (history : Prefix) : ungroup (regroup history) = history := rfl
  have regroup_ungroup (data : Grouped) : regroup (ungroup data) = data := by
    rcases data with ⟨⟨size, hsize⟩, ⟨total, htotal⟩, history, hlength, hspend⟩
    dsimp only at hlength hspend
    subst size
    subst total
    rfl
  let grouping : Prefix ≃ Grouped := ⟨regroup, ungroup, ungroup_regroup, regroup_ungroup⟩
  let PureCap := {history : PureHistory //
    history.val.length = depth + 1 ∧ spend history.val < budget}
  let cap : PureCap ≃ (Σ total : Fin budget, Fiber (depth + 1) total.val) :=
    { toFun := fun history =>
        ⟨⟨spend history.val.val, history.property.2⟩,
          ⟨history.val, history.property.1, rfl⟩⟩
      invFun := fun data => ⟨data.2.val, data.2.property.1, by
        rw [data.2.property.2]
        exact data.1.is_lt⟩
      left_inv := fun history => rfl
      right_inv := fun data => by
        rcases data with ⟨⟨total, htotal⟩, history, hlength, hspend⟩
        dsimp only at hspend
        subst total
        rfl }
  have cap_count : Nat.card PureCap = ∑ total ∈ Finset.range budget,
      PowerSeries.coeff (depth + 1) (PowerSeries.coeff total pureSeries) := by
    rw [Nat.card_congr cap, Nat.card_sigma]
    simp_rw [pure_count]
    exact Fin.sum_univ_eq_sum_range
      (fun total => PowerSeries.coeff (depth + 1) (PowerSeries.coeff total pureSeries)) budget
  have aggregate (size total lower suffix : ℕ) :
      (∑ history : Fiber size total, (((oldCount history.val + if inert then 1 else 0) -
          if finishMode inert history.val.val then 1 else 0) * lower +
        (if finishMode inert history.val.val then 1 else 0) * suffix)) =
      let maximum := PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
        if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0;
      let upper := PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
        if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0;
      (upper - maximum) * lower + maximum * suffix := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_tsub_distrib _ (fun history hhistory => eligible size total history),
      Finset.sum_add_distrib, survivors, maximum_count, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, pure_count]
    cases inert <;> simp
  let term := fun history : Prefix =>
    ((oldCount history.val + if inert then 1 else 0) -
      if finishMode inert history.val.val then 1 else 0) *
        PowerSeries.coeff (depth - history.val.val.length)
          (fullSeries false (budget - spend history.val.val)) +
    (if finishMode inert history.val.val then 1 else 0) *
      PowerSeries.coeff (depth - history.val.val.length)
        (fullSeries true (budget - spend history.val.val + 1))
  have regroup_sum : (∑ history : Prefix, term history) =
      ∑ size : Fin (depth + 1), ∑ total : Fin budget, ∑ history : Fiber size.val total.val,
          (((oldCount history.val + if inert then 1 else 0) -
            if finishMode inert history.val.val then 1 else 0) *
              PowerSeries.coeff (depth - size.val) (fullSeries false (budget - total.val)) +
          (if finishMode inert history.val.val then 1 else 0) * PowerSeries.coeff (depth - size.val)
                (fullSeries true (budget - total.val + 1))) := by
    rw [Fintype.sum_equiv grouping term (fun data => term (ungroup data))
      (fun history => rfl), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro size hsize
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro total htotal
    apply Finset.sum_congr rfl
    intro history hhistory
    simp only [term, ungroup, history.property.1, history.property.2]
  have hmain : PowerSeries.coeff (depth + 1) (fullSeries inert budget) =
      Nat.card PureCap + ∑ history : Prefix, term history := by
    simpa only [fullSeries, PowerSeries.coeff_mk, PureCap, Prefix, term,
      Bool.false_eq_true, ↓reduceIte] using hrenewal
  rw [hmain, cap_count, regroup_sum]
  simp_rw [aggregate]
  congr 1
  let coefficientTerm := fun size total : ℕ =>
    let maximum := PowerSeries.coeff size (PowerSeries.coeff total recordSeries) +
      if inert = true ∧ size = 0 ∧ total = 0 then 1 else 0;
    let upper := PowerSeries.coeff size (PowerSeries.coeff total survivorSeries) +
      if inert then PowerSeries.coeff size (PowerSeries.coeff total pureSeries) else 0;
    (upper - maximum) * PowerSeries.coeff (depth - size) (fullSeries false (budget - total)) +
      maximum * PowerSeries.coeff (depth - size) (fullSeries true (budget - total + 1))
  change (∑ size : Fin (depth + 1), ∑ total : Fin budget, coefficientTerm size.val total.val) =
      ∑ size ∈ Finset.range (depth + 1),
        ∑ total ∈ Finset.range budget, coefficientTerm size total
  calc
    _ = ∑ size : Fin (depth + 1), ∑ total ∈ Finset.range budget,
        coefficientTerm size.val total := by
      apply Finset.sum_congr rfl
      intro size hsize
      exact Fin.sum_univ_eq_sum_range (coefficientTerm size.val) budget
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun size => ∑ total ∈ Finset.range budget, coefficientTerm size total) (depth + 1)
end D5.S3.Combinatorics.WeakAscent.WeakAscent215GroupedRenewal
