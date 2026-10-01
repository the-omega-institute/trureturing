/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal
   mirror-E: none(waiver:weighted-first-old-step-renewal)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Data.Fintype.Fin]
   utility: none
   digest: Counts first old choices by separating surviving lower sites from maximum repetition. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Endpoints
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Finite
import D5.S3.Combinatorics.WeakAscent.WeakAscent215HistoryFinite
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215WeightedRenewal

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Decomposition WeakAscent215Endpoints
open WeakAscent215Renewal WeakAscent215Finite WeakAscent215HistoryFinite

theorem weighted_renewal (inert : Bool) (budget depth : ℕ) :
    let base : List Bool := if inert then [true] else [];
    let Prefix := {history : PureHistory //
      history.val.length ≤ depth ∧ spend history.val < budget};
    let count := fun (stack : List Bool) (remaining : ℕ) (mode : Bool) (size : ℕ) =>
      Nat.card {steps : List FullStep // steps.length = size ∧
        FullRun stack remaining mode steps};
    ∃ enumeration : Fintype Prefix, letI := enumeration;
      count base budget inert (depth + 1) =
        Nat.card {history : PureHistory //
          history.val.length = depth + 1 ∧ spend history.val < budget} +
        ∑ purePrefix : Prefix,
          (((oldCount purePrefix.val + if inert then 1 else 0) -
            if finishMode inert purePrefix.val.val then 1 else 0) *
              count [] (budget - spend purePrefix.val.val) false
                (depth - purePrefix.val.val.length) +
          (if finishMode inert purePrefix.val.val then 1 else 0) *
              count [true] (budget - spend purePrefix.val.val + 1) true
                (depth - purePrefix.val.val.length)) := by
  classical
  dsimp only
  let base : List Bool := if inert then [true] else []
  let Prefix := {history : PureHistory //
    history.val.length ≤ depth ∧ spend history.val < budget}
  let count := fun (stack : List Bool) (remaining : ℕ) (mode : Bool) (size : ℕ) =>
    Nat.card {steps : List FullStep // steps.length = size ∧
      FullRun stack remaining mode steps}
  have base_old (site : ℕ) (hsite : site < base.length) : base.getD site true = true := by
    cases inert <;> simp_all [base]
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
  have pure_budget_iff (stack ending : List Bool) (budget : ℕ) (steps : List PureStep) :
      BudgetRun stack budget steps ending ↔
        PureRun stack steps ending ∧ spend steps < budget := by
    induction steps generalizing stack ending budget with
    | nil =>
      constructor
      · intro hrun
        cases hrun with
        | nil _ _ hbudget => exact ⟨PureRun.nil _, hbudget⟩
      · rintro ⟨hrun, hbudget⟩
        cases hrun
        exact BudgetRun.nil _ _ hbudget
    | cons first rest ih =>
      cases first with
      | record gap =>
        constructor
        · intro hrun
          cases hrun with
          | record _ _ _ _ _ hgap htail =>
            obtain ⟨hpure, hspend⟩ := (ih _ _ _).mp htail
            refine ⟨PureRun.record _ _ _ _ hpure, ?_⟩
            simp only [spend]
            omega
        · rintro ⟨hrun, hspend⟩
          cases hrun with
          | record _ _ _ _ htail =>
            simp only [spend] at hspend
            apply BudgetRun.record _ _ _ _ _ (by omega)
            exact (ih _ _ _).mpr ⟨htail, by omega⟩
      | descend site =>
        constructor
        · intro hrun
          cases hrun with
          | descend _ _ _ _ _ hsite hfresh htail =>
            obtain ⟨hpure, hspend⟩ := (ih _ _ _).mp htail
            exact ⟨PureRun.descend _ _ _ _ hsite hfresh hpure, hspend⟩
        · rintro ⟨hrun, hspend⟩
          cases hrun with
          | descend _ _ _ _ hsite hfresh htail =>
            apply BudgetRun.descend _ _ _ _ _ hsite hfresh
            exact (ih _ _ _).mpr ⟨htail, hspend⟩
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
  have shift_spend (steps : List PureStep) :
      spend (steps.map (PureStep.shift base.length)) = spend steps := by
    induction steps with
    | nil => rfl
    | cons first rest ih => cases first <;> simp [PureStep.shift, spend, ih]
  have shift_mode (steps : List PureStep) (mode : Bool) :
      finishMode mode (steps.map (PureStep.shift base.length)) = finishMode mode steps := by
    induction steps generalizing mode with
    | nil => rfl
    | cons first rest ih => cases first <;> simp [PureStep.shift, finishMode, ih]
  have shift_injective : Function.Injective (PureStep.shift base.length) := by
    intro first second heq
    cases first <;> cases second <;> simp_all [PureStep.shift]
  have decode (steps : List PureStep) (stack ending : List Bool)
      (hrun : PureRun (base ++ stack) steps ending) :
      ∃ normalized final, PureRun stack normalized final ∧
        steps = normalized.map (PureStep.shift base.length) ∧ ending = base ++ final := by
    induction steps generalizing stack ending with
    | nil =>
      cases hrun
      exact ⟨[], stack, PureRun.nil _, rfl, rfl⟩
    | cons first rest ih =>
      cases first with
      | record gap =>
        cases hrun with
        | record _ _ _ _ htail =>
          have htail' : PureRun (base ++ (stack ++ List.replicate gap false ++ [true]))
              rest ending := by simpa [List.append_assoc] using htail
          obtain ⟨normalized, final, hpure, hsteps, hfinal⟩ := ih _ _ htail'
          exact ⟨.record gap :: normalized, final, PureRun.record _ _ _ _ hpure,
            by simp [hsteps, PureStep.shift], hfinal⟩
      | descend site =>
        cases hrun with
        | descend _ _ _ _ hsite hfresh htail =>
          have hoffset : base.length ≤ site := by
            by_contra hsmall
            have hsmall' : site < base.length := by omega
            rw [List.getD_append _ _ _ _ hsmall', base_old site hsmall'] at hfresh
            contradiction
          have hread : stack.getD (site - base.length) true = false := by
            simpa only [List.getD_append_right _ _ _ _ hoffset] using hfresh
          have htake : (base ++ stack).take site = base ++ stack.take (site - base.length) := by
            rw [List.take_append, List.take_of_length_le hoffset]
          rw [htake] at htail
          obtain ⟨normalized, final, hpure, hsteps, hfinal⟩ := ih _ _ htail
          refine ⟨.descend (site - base.length) :: normalized, final,
            PureRun.descend _ _ _ _ (by simp only [List.length_append] at hsite; omega)
              hread hpure, ?_, hfinal⟩
          simp [hsteps, PureStep.shift, Nat.add_sub_of_le hoffset]
  have maximum_old (stack ending : List Bool) (steps : List PureStep) (mode : Bool)
      (hrun : PureRun stack steps ending)
      (hinitial : mode = true → stack.getD (stack.length - 1) false = true ∧
        0 < stack.length) :
      finishMode mode steps = true →
        ending.getD (ending.length - 1) false = true ∧ 0 < ending.length := by
    induction hrun generalizing mode with
    | nil stack => exact hinitial
    | record stack ending rest gap htail ih =>
      apply ih true
      intro hmode
      constructor
      · simp [List.length_append]
      · simp
    | descend stack ending rest site hsite hfresh htail ih =>
      exact ih false (by simp)
  have bounded_finite : Finite Prefix := by
    let family : Set (List PureStep) := ⋃ size : Fin (depth + 1), ⋃ total : Fin budget,
      {steps | steps.length = size.val ∧ spend steps = total.val ∧
        ∃ ending, PureRun [] steps ending}
    have hfinite : family.Finite :=
      Set.finite_iUnion fun size => Set.finite_iUnion fun total =>
        pure_histories_finite size.val total.val
    have hinj : Function.Injective (fun purePrefix : Prefix => purePrefix.val.val) := by
      intro first second heq
      exact Subtype.ext (Subtype.ext heq)
    let : Finite family := hfinite.to_subtype
    refine Finite.of_injective (fun purePrefix : Prefix =>
      (⟨purePrefix.val.val, ?_⟩ : family))
        (fun first second heq => hinj (congrArg (fun value : family => value.val) heq))
    apply Set.mem_iUnion.mpr
    refine ⟨⟨purePrefix.val.val.length, by have h := purePrefix.property.1; omega⟩, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨⟨spend purePrefix.val.val, purePrefix.property.2⟩,
      rfl, rfl, purePrefix.val.property⟩
  let : Finite Prefix := bounded_finite
  let : Fintype Prefix := Fintype.ofFinite Prefix
  refine ⟨inferInstance, ?_⟩
  let Normal := {history : PureHistory // spend history.val < budget}
  let BudgetPrefix := {steps : List PureStep // ∃ ending, BudgetRun base budget steps ending}
  let liftPrefix : Normal → BudgetPrefix := fun history =>
    ⟨history.val.val.map (PureStep.shift base.length), by
      obtain ⟨ending, hrun⟩ := history.val.property
      refine ⟨base ++ ending, (pure_budget_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
      · simpa using (pure_inert_base base [] ending history.val.val).mpr hrun
      · simpa only [shift_spend] using history.property⟩
  have lift_bijective : Function.Bijective liftPrefix := by
    constructor
    · intro first second heq
      apply Subtype.ext
      apply Subtype.ext
      exact List.map_injective_iff.mpr shift_injective (congrArg Subtype.val heq)
    · intro purePrefix
      obtain ⟨ending, hbudget⟩ := purePrefix.property
      obtain ⟨hrun, hspend⟩ := (pure_budget_iff _ _ _ _).mp hbudget
      have hrun' : PureRun (base ++ []) purePrefix.val ending := by simpa using hrun
      obtain ⟨normalized, final, hpure, hsteps, hfinal⟩ := decode _ _ _ hrun'
      refine ⟨⟨⟨normalized, final, hpure⟩, ?_⟩, ?_⟩
      · simpa only [hsteps, shift_spend] using hspend
      · exact Subtype.ext hsteps.symm
  let prefixEquiv : Normal ≃ BudgetPrefix := Equiv.ofBijective liftPrefix lift_bijective
  let ending := fun history : Normal => Classical.choose history.val.property
  have lifted_ending (history : Normal) :
      Classical.choose (prefixEquiv history).property = base ++ ending history := by
    apply run_unique base (prefixEquiv history).val
    · exact ((pure_budget_iff _ _ _ _).mp
        (Classical.choose_spec (prefixEquiv history).property)).1
    · simpa [prefixEquiv, liftPrefix, ending] using
        (pure_inert_base base [] (ending history) history.val.val).mpr
          (Classical.choose_spec history.val.property)
  have final_max (history : Normal) (hmode : finishMode inert history.val.val = true) :
      (base ++ ending history).getD ((base ++ ending history).length - 1) true = true ∧
        0 < (base ++ ending history).length := by
    have hpure := (pure_inert_base base [] (ending history) history.val.val).mpr
      (Classical.choose_spec history.val.property)
    have hinitial : inert = true → base.getD (base.length - 1) false = true ∧
        0 < base.length := by cases inert <;> simp [base]
    have hmax := maximum_old _ _ _ inert (by simpa using hpure) hinitial
      (by simpa only [shift_mode] using hmode)
    have hindex : (base ++ ending history).length - 1 < (base ++ ending history).length :=
      by omega
    rw [List.getD_eq_getElem _ _ hindex] at hmax ⊢
    exact hmax
  obtain ⟨split, hpure, hold⟩ := (first_old_decomposition base budget inert).1
  let terminal := fun purePrefix : BudgetPrefix => Classical.choose purePrefix.property
  let OldSites := fun purePrefix : BudgetPrefix =>
    {site : ℕ // site < (terminal purePrefix).length ∧
      (terminal purePrefix).getD site true = true}
  let repeats := fun (purePrefix : BudgetPrefix) (site : OldSites purePrefix) =>
    finishMode inert purePrefix.val && (site.val + 1 == (terminal purePrefix).length)
  let TailRun := fun (purePrefix : BudgetPrefix) (site : OldSites purePrefix)
      (steps : List FullStep) => FullRun
    (bif repeats purePrefix site then [true] else [])
    (bif repeats purePrefix site then budget - spend purePrefix.val + 1
      else budget - spend purePrefix.val)
    (repeats purePrefix site) steps
  let Short := {purePrefix : BudgetPrefix // purePrefix.val.length ≤ depth}
  let NoOld := {purePrefix : BudgetPrefix // purePrefix.val.length = depth + 1}
  let WithOld := Σ purePrefix : Short, Σ site : OldSites purePrefix.val,
    {suffix : List FullStep // suffix.length = depth - purePrefix.val.val.length ∧
      TailRun purePrefix.val site suffix}
  let Sized := {steps : List FullStep // steps.length = depth + 1 ∧
    FullRun base budget inert steps}
  let replay : NoOld ⊕ WithOld → Sized := fun data =>
    match data with
    | .inl purePrefix => ⟨(split.symm (.inl purePrefix.val)).val, by
        constructor
        · rw [hpure, List.length_map, purePrefix.property]
        · exact (split.symm (.inl purePrefix.val)).property⟩
    | .inr ⟨purePrefix, site, suffix⟩ =>
      ⟨(split.symm (.inr ⟨purePrefix.val, site, ⟨suffix.val, suffix.property.2⟩⟩)).val, by
        constructor
        · rw [hold, List.length_append, List.length_map, List.length_cons]
          change purePrefix.val.val.length + (suffix.val.length + 1) = depth + 1
          have hbound := purePrefix.property
          have hlength := suffix.property.1
          omega
        · exact (split.symm (.inr
            ⟨purePrefix.val, site, ⟨suffix.val, suffix.property.2⟩⟩)).property⟩
  have replay_bijective : Function.Bijective replay := by
    constructor
    · intro first second heq
      have hval := congrArg (fun data : Sized => data.val) heq
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          have h := split.symm.injective (Subtype.ext hval)
          have hp := Sum.inl.inj h
          exact congrArg Sum.inl (Subtype.ext hp)
        | inr second =>
          have h := split.symm.injective (Subtype.ext hval)
          cases h
      | inr first =>
        cases second with
        | inl second =>
          have h := split.symm.injective (Subtype.ext hval)
          cases h
        | inr second =>
          obtain ⟨firstPrefix, firstSite, firstSuffix⟩ := first
          obtain ⟨secondPrefix, secondSite, secondSuffix⟩ := second
          have h := Sum.inr.inj (split.symm.injective (Subtype.ext hval))
          have hp : firstPrefix = secondPrefix :=
            Subtype.ext (congrArg Sigma.fst h)
          subst secondPrefix
          have hinner := eq_of_heq (Sigma.mk.inj_iff.mp h).2
          have hs : firstSite = secondSite := congrArg Sigma.fst hinner
          subst secondSite
          have hsuffix : firstSuffix.val = secondSuffix.val :=
            congrArg (fun pair : {steps : List FullStep //
              TailRun firstPrefix.val firstSite steps} => pair.val)
              (eq_of_heq (Sigma.mk.inj_iff.mp hinner).2)
          have ht : firstSuffix = secondSuffix :=
            Subtype.ext hsuffix
          subst secondSuffix
          rfl
    · intro steps
      rcases hsplit : split ⟨steps.val, steps.property.2⟩ with purePrefix | data
      · have hinverse := congrArg Subtype.val (split.symm_apply_apply
          (⟨steps.val, steps.property.2⟩ : {steps // FullRun base budget inert steps}))
        rw [hsplit, hpure] at hinverse
        have hlength : purePrefix.val.length = depth + 1 := by
          have h := congrArg List.length hinverse
          simpa [steps.property.1] using h
        refine ⟨.inl ⟨purePrefix, hlength⟩, ?_⟩
        apply Subtype.ext
        dsimp [replay]
        rw [hpure]
        exact hinverse
      · obtain ⟨purePrefix, site, suffix⟩ := data
        have hinverse := congrArg Subtype.val (split.symm_apply_apply
          (⟨steps.val, steps.property.2⟩ : {steps // FullRun base budget inert steps}))
        rw [hsplit, hold] at hinverse
        have hlength := congrArg List.length hinverse
        simp only [List.length_append, List.length_map, List.length_cons,
          steps.property.1] at hlength
        have hshort : purePrefix.val.length ≤ depth := by omega
        have htail : suffix.val.length = depth - purePrefix.val.length := by omega
        refine ⟨.inr ⟨⟨purePrefix, hshort⟩, site,
          ⟨suffix.val, htail, suffix.property⟩⟩, ?_⟩
        apply Subtype.ext
        dsimp [replay]
        rw [hold]
        exact hinverse
  let sizedEquiv : NoOld ⊕ WithOld ≃ Sized := Equiv.ofBijective replay replay_bijective
  let nest : Prefix ≃ {history : Normal // history.val.val.length ≤ depth} :=
    { toFun := fun history => ⟨⟨history.val, history.property.2⟩, history.property.1⟩
      invFun := fun history => ⟨history.val.val, history.property, history.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let shortEquiv : Prefix ≃ Short := nest.trans
    (prefixEquiv.subtypeEquiv (by intro history; simp [prefixEquiv, liftPrefix]))
  let : Finite Short := Finite.of_equiv Prefix shortEquiv
  let : Fintype Short := Fintype.ofFinite Short
  let : Finite Sized := (full_histories_finite (depth + 1) base budget inert).to_subtype
  let : Finite NoOld := Finite.of_injective (fun data : NoOld => replay (.inl data))
    (fun first second heq => Sum.inl.inj (replay_bijective.1 heq))
  let : Fintype NoOld := Fintype.ofFinite NoOld
  let siteEquiv (purePrefix : BudgetPrefix) : OldSites purePrefix ≃
      {site : Fin (terminal purePrefix).length // (terminal purePrefix)[site.val] = true} :=
    { toFun := fun site => ⟨⟨site.val, site.property.1⟩, by
        simpa only [List.getD_eq_getElem _ _ site.property.1] using site.property.2⟩
      invFun := fun site => ⟨site.val.val, site.val.is_lt, by
        simpa only [List.getD_eq_getElem _ _ site.val.is_lt] using site.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let (purePrefix : BudgetPrefix) : Finite (OldSites purePrefix) :=
    Finite.of_equiv _ (siteEquiv purePrefix).symm
  let (purePrefix : BudgetPrefix) : Fintype (OldSites purePrefix) :=
    Fintype.ofFinite (OldSites purePrefix)
  let (purePrefix : Short) (site : OldSites purePrefix.val) :
      Finite {suffix : List FullStep //
        suffix.length = depth - purePrefix.val.val.length ∧ TailRun purePrefix.val site suffix} :=
    (full_histories_finite (depth - purePrefix.val.val.length)
      (bif repeats purePrefix.val site then [true] else [])
      (bif repeats purePrefix.val site then budget - spend purePrefix.val.val + 1
        else budget - spend purePrefix.val.val) (repeats purePrefix.val site)).to_subtype
  let (purePrefix : Short) (site : OldSites purePrefix.val) :
      Fintype {suffix : List FullStep //
        suffix.length = depth - purePrefix.val.val.length ∧ TailRun purePrefix.val site suffix} :=
    Fintype.ofFinite _
  let pureEquiv : {history : PureHistory //
      history.val.length = depth + 1 ∧ spend history.val < budget} ≃ NoOld :=
    ({ toFun := fun history => ⟨⟨history.val, history.property.2⟩, history.property.1⟩
       invFun := fun history => ⟨history.val.val, history.property, history.val.property⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      {history : PureHistory // history.val.length = depth + 1 ∧ spend history.val < budget} ≃
        {history : Normal // history.val.val.length = depth + 1}).trans
      (prefixEquiv.subtypeEquiv (by intro history; simp [prefixEquiv, liftPrefix]))
  have site_card (purePrefix : BudgetPrefix) :
      Nat.card (OldSites purePrefix) = (terminal purePrefix).count true := by
    rw [Nat.card_congr (siteEquiv purePrefix), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact Fin.card_filter_univ_eq_vector_get_eq_count true
      (⟨terminal purePrefix, rfl⟩ : List.Vector Bool (terminal purePrefix).length)
  have repeat_card (history : Normal) :
      Nat.card {site : OldSites (prefixEquiv history) // repeats (prefixEquiv history) site} =
        if finishMode inert history.val.val then 1 else 0 := by
    have hend := lifted_ending history
    have hmode : finishMode inert (prefixEquiv history).val =
        finishMode inert history.val.val := shift_mode _ _
    by_cases hm : finishMode inert history.val.val = true
    · rw [if_pos hm]
      have hmax := final_max history hm
      let maximum : OldSites (prefixEquiv history) :=
        ⟨(base ++ ending history).length - 1, by
          dsimp [OldSites, terminal]
          rw [hend]
          exact ⟨by omega, hmax.1⟩⟩
      have hrepeat : repeats (prefixEquiv history) maximum = true := by
        simp only [repeats, hmode, hm, Bool.true_and, beq_iff_eq]
        dsimp [maximum, terminal]
        rw [hend]
        omega
      have hunique (site : OldSites (prefixEquiv history))
          (hsite : repeats (prefixEquiv history) site = true) : site = maximum := by
        simp only [repeats, hmode, hm, Bool.true_and, beq_iff_eq] at hsite
        dsimp [terminal] at hsite
        simp only [hend] at hsite
        apply Subtype.ext
        dsimp [maximum]
        omega
      let correspondence : {site : OldSites (prefixEquiv history) //
          repeats (prefixEquiv history) site} ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨maximum, hrepeat⟩
          left_inv := fun site => Subtype.ext (hunique site.val site.property).symm
          right_inv := fun data => by cases data; rfl }
      simpa using Nat.card_congr correspondence
    · rw [if_neg hm]
      have hfalse : finishMode inert history.val.val = false := Bool.eq_false_iff.mpr hm
      have : IsEmpty {site : OldSites (prefixEquiv history) //
          repeats (prefixEquiv history) site} :=
        ⟨fun site => by simpa [repeats, hmode, hfalse] using site.property⟩
      exact Nat.card_of_isEmpty
  have weighted (history : Prefix) :
      (∑ site : OldSites (shortEquiv history).val,
        Nat.card {suffix : List FullStep //
          suffix.length = depth - (shortEquiv history).val.val.length ∧
            TailRun (shortEquiv history).val site suffix}) =
      ((oldCount history.val + if inert then 1 else 0) -
        if finishMode inert history.val.val then 1 else 0) *
          count [] (budget - spend history.val.val) false (depth - history.val.val.length) +
      (if finishMode inert history.val.val then 1 else 0) *
          count [true] (budget - spend history.val.val + 1) true
            (depth - history.val.val.length) := by
    let normal : Normal := ⟨history.val, history.property.2⟩
    have hlift : (shortEquiv history).val = prefixEquiv normal := rfl
    have hlength : (shortEquiv history).val.val.length = history.val.val.length :=
      List.length_map _
    have hspend : spend (shortEquiv history).val.val = spend history.val.val := shift_spend _
    have htotal : Nat.card (OldSites (shortEquiv history).val) =
        oldCount history.val + if inert then 1 else 0 := by
      rw [site_card, hlift]
      change (Classical.choose (prefixEquiv normal).property).count true = _
      rw [lifted_ending, List.count_append]
      cases inert <;> simp [base, oldCount, ending, normal, Nat.add_comm]
    have hrepeat := repeat_card normal
    change Nat.card {site : OldSites (shortEquiv history).val //
      repeats (shortEquiv history).val site} = _ at hrepeat
    have hrepeat' : Fintype.card {site : OldSites (shortEquiv history).val //
        repeats (shortEquiv history).val site} =
          if finishMode inert history.val.val then 1 else 0 := by
      rwa [Nat.card_eq_fintype_card] at hrepeat
    have hlower : Fintype.card {site : OldSites (shortEquiv history).val //
        ¬repeats (shortEquiv history).val site} =
          (oldCount history.val + if inert then 1 else 0) -
            if finishMode inert history.val.val then 1 else 0 := by
      rw [Fintype.card_subtype_compl, hrepeat', ← Nat.card_eq_fintype_card, htotal]
    have hterms (site : OldSites (shortEquiv history).val) :
        Nat.card {suffix : List FullStep //
          suffix.length = depth - (shortEquiv history).val.val.length ∧
            TailRun (shortEquiv history).val site suffix} =
        if repeats (shortEquiv history).val site then
          count [true] (budget - spend history.val.val + 1) true
            (depth - history.val.val.length)
        else count [] (budget - spend history.val.val) false
            (depth - history.val.val.length) := by
      cases hr : repeats (shortEquiv history).val site <;>
        simp [TailRun, hr, count, hlength, hspend]
    simp_rw [hterms]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Nat.nsmul_eq_mul]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype, hrepeat', hlower]
    exact Nat.add_comm _ _
  change Nat.card Sized = _
  rw [← Nat.card_congr sizedEquiv, Nat.card_sum, ← Nat.card_congr pureEquiv,
    Nat.card_sigma]
  congr 1
  simp_rw [Nat.card_sigma]
  exact (Fintype.sum_equiv shortEquiv _ _ (fun history => (weighted history).symm)).symm

end D5.S3.Combinatorics.WeakAscent.WeakAscent215WeightedRenewal
