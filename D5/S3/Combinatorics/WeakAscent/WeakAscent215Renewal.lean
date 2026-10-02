/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Renewal
   mirror-E: none(waiver:first-old-step-cut-and-replay)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.List]
   utility: none
   digest: Cuts full stack histories uniquely at their first old step and replays the pieces. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Pure
import Mathlib.Logic.Equiv.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Renewal

open WeakAscent215Pure

inductive FullStep where
  | pure (step : PureStep)
  | old (site : ℕ)

def finishMode : Bool → List PureStep → Bool
  | mode, [] => mode
  | _, .record _ :: rest => finishMode true rest
  | _, .descend _ :: rest => finishMode false rest

inductive FullRun : List Bool → ℕ → Bool → List FullStep → Prop where
  | nil (stack : List Bool) (budget : ℕ) (mode : Bool) (hbudget : 0 < budget) :
      FullRun stack budget mode []
  | record (stack : List Bool) (budget gap : ℕ) (mode : Bool) (rest : List FullStep)
      (hgap : gap < budget)
      (tail : FullRun (stack ++ List.replicate gap false ++ [true])
        (budget - gap) true rest) :
      FullRun stack budget mode (.pure (.record gap) :: rest)
  | descend (stack : List Bool) (budget site : ℕ) (mode : Bool) (rest : List FullStep)
      (hsite : site < stack.length) (hfresh : stack.getD site true = false)
      (tail : FullRun (stack.take site) budget false rest) :
      FullRun stack budget mode (.pure (.descend site) :: rest)
  | old (stack : List Bool) (budget site : ℕ) (mode : Bool) (rest : List FullStep)
      (hbudget : 0 < budget) (hsite : site < stack.length)
      (hold : stack.getD site true = true)
      (tail : FullRun
        (bif mode && (site + 1 == stack.length) then [true] else [])
        (bif mode && (site + 1 == stack.length) then budget + 1 else budget)
        (mode && (site + 1 == stack.length)) rest) :
      FullRun stack budget mode (.old site :: rest)

theorem first_old_decomposition (stack : List Bool) (budget : ℕ) (mode : Bool) :
    (let Prefix := {steps : List PureStep // ∃ ending, BudgetRun stack budget steps ending};
    let ending := fun purePrefix : Prefix => Classical.choose purePrefix.property;
    let repeats := fun (purePrefix : Prefix) (site : ℕ) =>
      finishMode mode purePrefix.val && (site + 1 == (ending purePrefix).length);
    let Pieces := Prefix ⊕ (Σ purePrefix : Prefix,
      Σ site : {site : ℕ // site < (ending purePrefix).length ∧
        (ending purePrefix).getD site true = true},
      {suffix : List FullStep // FullRun
        (bif repeats purePrefix site.val then [true] else [])
        (bif repeats purePrefix site.val then budget - spend purePrefix.val + 1
          else budget - spend purePrefix.val)
        (repeats purePrefix site.val) suffix});
    ∃ correspondence : {steps : List FullStep // FullRun stack budget mode steps} ≃ Pieces,
      (∀ purePrefix : Prefix, (correspondence.symm (.inl purePrefix)).val =
        purePrefix.val.map FullStep.pure) ∧
      (∀ data, (correspondence.symm (.inr data)).val =
        data.1.val.map FullStep.pure ++ .old data.2.1.val :: data.2.2.val)) ∧
    (let Histories (label : List Bool × ℕ × Bool) (size : ℕ) :=
    {steps : List FullStep // steps.length = size ∧ FullRun label.1 label.2.1 label.2.2 steps};
  let next (stack : List Bool) (height : ℕ) (ending : Bool) (count : ℕ)
      (choice : Fin height ⊕ Fin count) : List Bool × ℕ × Bool :=
    match choice with
    | .inl gap => (stack ++ List.replicate gap.val false ++ [true], height - gap.val, true)
    | .inr site =>
      if stack.getD site.val true = false then (stack.take site.val, height, false)
      else
        let repeats := ending && (site.val + 1 == stack.length)
        (bif repeats then [true] else [], bif repeats then height + 1 else height, repeats);
      ∀ count size : ℕ, 0 < budget → stack.length = count →
        Nonempty (Histories (stack, budget, mode) (size + 1) ≃
          Σ choice : Fin budget ⊕ Fin count,
                  Histories (next stack budget mode count choice) size)) := by
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
  have cutting :
      let Prefix := {steps : List PureStep // ∃ ending, BudgetRun stack budget steps ending};
          let ending := fun purePrefix : Prefix => Classical.choose purePrefix.property;
          let repeats := fun (purePrefix : Prefix) (site : ℕ) =>
            finishMode mode purePrefix.val && (site + 1 == (ending purePrefix).length);
          let Pieces := Prefix ⊕ (Σ purePrefix : Prefix,
            Σ site : {site : ℕ // site < (ending purePrefix).length ∧
              (ending purePrefix).getD site true = true},
            {suffix : List FullStep // FullRun
              (bif repeats purePrefix site.val then [true] else [])
              (bif repeats purePrefix site.val then budget - spend purePrefix.val + 1
                else budget - spend purePrefix.val)
              (repeats purePrefix site.val) suffix});
          ∃ correspondence :
            {steps : List FullStep // FullRun stack budget mode steps} ≃ Pieces,
            (∀ purePrefix : Prefix, (correspondence.symm (.inl purePrefix)).val =
              purePrefix.val.map FullStep.pure) ∧
            (∀ data, (correspondence.symm (.inr data)).val =
              data.1.val.map FullStep.pure ++ .old data.2.1.val :: data.2.2.val) := by
    dsimp only
    let Prefix := {steps : List PureStep // ∃ ending, BudgetRun stack budget steps ending}
    let ending := fun purePrefix : Prefix => Classical.choose purePrefix.property
    let repeats := fun (purePrefix : Prefix) (site : ℕ) =>
      finishMode mode purePrefix.val && (site + 1 == (ending purePrefix).length)
    let Pieces := Prefix ⊕ (Σ purePrefix : Prefix,
      Σ site : {site : ℕ // site < (ending purePrefix).length ∧
        (ending purePrefix).getD site true = true},
      {suffix : List FullStep // FullRun
        (bif repeats purePrefix site.val then [true] else [])
        (bif repeats purePrefix site.val then budget - spend purePrefix.val + 1
          else budget - spend purePrefix.val)
        (repeats purePrefix site.val) suffix})
    have ending_unique (initial first second : List Bool) (initialBudget : ℕ)
        (steps : List PureStep) (hfirst : BudgetRun initial initialBudget steps first)
        (hsecond : BudgetRun initial initialBudget steps second) : first = second := by
      induction hfirst with
      | nil stack budget hbudget => cases hsecond; rfl
      | record stack ending rest gap budget hgap htail ih =>
        cases hsecond with
        | record _ _ _ _ _ _ htail' => exact ih htail'
      | descend stack ending rest site budget hsite hfresh htail ih =>
        cases hsecond with
        | descend _ _ _ _ _ _ _ htail' => exact ih htail'
    have lift (initial final : List Bool) (initialBudget : ℕ) (steps : List PureStep)
        (hprefix : BudgetRun initial initialBudget steps final) (initialMode : Bool)
        (suffix : List FullStep)
        (hsuffix : FullRun final (initialBudget - spend steps)
          (finishMode initialMode steps) suffix) :
        FullRun initial initialBudget initialMode (steps.map FullStep.pure ++ suffix) := by
      induction hprefix generalizing initialMode with
      | nil stack budget hbudget => simpa [spend, finishMode] using hsuffix
      | record stack ending rest gap budget hgap htail ih =>
        simp only [List.map_cons, List.cons_append]
        apply FullRun.record _ _ _ _ _ hgap
        apply ih true
        simpa only [spend, finishMode, Nat.sub_sub] using hsuffix
      | descend stack ending rest site budget hsite hfresh htail ih =>
        simp only [List.map_cons, List.cons_append]
        exact FullRun.descend _ _ _ _ _ hsite hfresh
          (ih false (by simpa only [spend, finishMode] using hsuffix))
    have cut (initial : List Bool) (initialBudget : ℕ) (initialMode : Bool)
        (steps : List FullStep) (hrun : FullRun initial initialBudget initialMode steps) :
        (∃ purePrefix final, BudgetRun initial initialBudget purePrefix final ∧
          steps = purePrefix.map FullStep.pure) ∨
        (∃ purePrefix final site suffix, BudgetRun initial initialBudget purePrefix final ∧
          site < final.length ∧ final.getD site true = true ∧
          FullRun
            (bif finishMode initialMode purePrefix && (site + 1 == final.length)
              then [true] else [])
            (bif finishMode initialMode purePrefix && (site + 1 == final.length)
              then initialBudget - spend purePrefix + 1 else initialBudget - spend purePrefix)
            (finishMode initialMode purePrefix && (site + 1 == final.length)) suffix ∧
          steps = purePrefix.map FullStep.pure ++ .old site :: suffix) := by
      induction hrun with
      | nil initial initialBudget initialMode hbudget =>
        exact Or.inl ⟨[], initial, BudgetRun.nil _ _ hbudget, rfl⟩
      | record initial initialBudget gap initialMode rest hgap htail ih =>
        rcases ih with ⟨purePrefix, final, hprefix, heq⟩ |
          ⟨purePrefix, final, site, suffix, hprefix, hsite, hold, hsuffix, heq⟩
        · exact Or.inl ⟨.record gap :: purePrefix, final,
            BudgetRun.record _ _ _ _ _ hgap hprefix, by simp [heq]⟩
        · exact Or.inr ⟨.record gap :: purePrefix, final, site, suffix,
            BudgetRun.record _ _ _ _ _ hgap hprefix, hsite, hold,
            by simpa only [finishMode, spend, Nat.sub_sub] using hsuffix, by simp [heq]⟩
      | descend initial initialBudget site initialMode rest hsite hfresh htail ih =>
        rcases ih with ⟨purePrefix, final, hprefix, heq⟩ |
          ⟨purePrefix, final, oldSite, suffix, hprefix, holdSite, hold, hsuffix, heq⟩
        · exact Or.inl ⟨.descend site :: purePrefix, final,
            BudgetRun.descend _ _ _ _ _ hsite hfresh hprefix, by simp [heq]⟩
        · exact Or.inr ⟨.descend site :: purePrefix, final, oldSite, suffix,
            BudgetRun.descend _ _ _ _ _ hsite hfresh hprefix, holdSite, hold,
            by simpa only [finishMode, spend] using hsuffix, by simp [heq]⟩
      | old initial initialBudget site initialMode rest hbudget hsite hold htail ih =>
        exact Or.inr ⟨[], initial, site, rest, BudgetRun.nil _ _ hbudget, hsite, hold,
          by simpa only [spend, finishMode, Nat.sub_zero] using htail, rfl⟩
    let replay : Pieces → {steps : List FullStep // FullRun stack budget mode steps}
      | .inl purePrefix => ⟨purePrefix.val.map FullStep.pure, by
          have hprefix := Classical.choose_spec purePrefix.property
          have hbudget :=
            (pure_budget_iff stack (ending purePrefix) budget purePrefix.val).mp hprefix
          have htail : FullRun (ending purePrefix) (budget - spend purePrefix.val)
              (finishMode mode purePrefix.val) [] :=
            FullRun.nil _ _ _ (by omega)
          simpa only [List.append_nil] using lift _ _ _ _ hprefix mode [] htail⟩
      | .inr data => ⟨data.1.val.map FullStep.pure ++ .old data.2.1.val :: data.2.2.val, by
          have hprefix := Classical.choose_spec data.1.property
          have hbudget := (pure_budget_iff stack (ending data.1) budget data.1.val).mp hprefix
          exact lift _ _ _ _ (Classical.choose_spec data.1.property) mode _
            (FullRun.old _ _ _ _ _ (by omega) data.2.1.property.1 data.2.1.property.2
              data.2.2.property)⟩
    have no_old (purePrefix : List PureStep) (site : ℕ) :
        FullStep.old site ∉ purePrefix.map FullStep.pure := by
      simp only [List.mem_map]
      rintro ⟨step, hstep, heq⟩
      cases heq
    have map_injective : Function.Injective (List.map FullStep.pure) :=
      List.map_injective_iff.mpr (by intro first second heq; cases heq; rfl)
    have cut_unique (first second : List PureStep) (firstSite secondSite : ℕ)
        (firstSuffix secondSuffix : List FullStep)
        (heq : first.map FullStep.pure ++ .old firstSite :: firstSuffix =
          second.map FullStep.pure ++ .old secondSite :: secondSuffix) :
        first = second ∧ firstSite = secondSite ∧ firstSuffix = secondSuffix := by
      induction first generalizing second with
      | nil =>
        cases second with
        | nil => simpa only [List.map_nil, List.nil_append, List.cons.injEq, true_and,
            FullStep.old.injEq] using heq
        | cons step rest =>
          have hfirst := congrArg List.head? heq
          simp only [List.map_nil, List.nil_append, List.map_cons,
            List.cons_append, List.head?_cons, Option.some.injEq] at hfirst
          cases hfirst
      | cons step rest ih =>
        cases second with
        | nil =>
          have hfirst := congrArg List.head? heq
          simp only [List.map_nil, List.nil_append, List.map_cons,
            List.cons_append, List.head?_cons, Option.some.injEq] at hfirst
          cases hfirst
        | cons other tail =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq,
            FullStep.pure.injEq] at heq
          rcases ih tail heq.2 with ⟨hprefix, hsite, hsuffix⟩
          exact ⟨by rw [heq.1, hprefix], hsite, hsuffix⟩
    have replay_injective : Function.Injective replay := by
      intro first second heq
      have hvalues := congrArg Subtype.val heq
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          dsimp only [replay] at hvalues
          exact congrArg Sum.inl (Subtype.ext (map_injective hvalues))
        | inr second =>
          dsimp only [replay] at hvalues
          have hmem : FullStep.old second.2.1.val ∈ first.val.map FullStep.pure := by
            rw [hvalues]
            simp only [List.mem_append, List.mem_cons, true_or, or_true]
          exact (no_old _ _ hmem).elim
      | inr first =>
        cases second with
        | inl second =>
          dsimp only [replay] at hvalues
          have hmem : FullStep.old first.2.1.val ∈ second.val.map FullStep.pure := by
            rw [← hvalues]
            simp only [List.mem_append, List.mem_cons, true_or, or_true]
          exact (no_old _ _ hmem).elim
        | inr second =>
          dsimp only [replay] at hvalues
          rcases first with ⟨firstPrefix, firstSite, firstSuffix⟩
          rcases second with ⟨secondPrefix, secondSite, secondSuffix⟩
          have hcut := cut_unique _ _ _ _ _ _ hvalues
          have hprefix : firstPrefix = secondPrefix := Subtype.ext hcut.1
          cases hprefix
          have hsite : firstSite = secondSite := Subtype.ext hcut.2.1
          cases hsite
          have hsuffix : firstSuffix = secondSuffix := Subtype.ext hcut.2.2
          cases hsuffix
          rfl
    have replay_surjective : Function.Surjective replay := by
      intro history
      rcases cut stack budget mode history.val history.property with
        ⟨steps, final, hprefix, heq⟩ |
        ⟨steps, final, site, suffix, hprefix, hsite, hold, hsuffix, heq⟩
      · let purePrefix : Prefix := ⟨steps, final, hprefix⟩
        exact ⟨.inl purePrefix, Subtype.ext heq.symm⟩
      · let purePrefix : Prefix := ⟨steps, final, hprefix⟩
        have hend : ending purePrefix = final :=
          ending_unique _ _ _ _ _ (Classical.choose_spec purePrefix.property) hprefix
        let oldSite : {site : ℕ // site < (ending purePrefix).length ∧
            (ending purePrefix).getD site true = true} :=
          ⟨site, by rw [hend]; exact ⟨hsite, hold⟩⟩
        have htail : FullRun
            (bif repeats purePrefix oldSite.val then [true] else [])
            (bif repeats purePrefix oldSite.val then budget - spend purePrefix.val + 1
              else budget - spend purePrefix.val)
            (repeats purePrefix oldSite.val) suffix := by
          simpa only [repeats, purePrefix, oldSite, hend] using hsuffix
        exact ⟨.inr ⟨purePrefix, oldSite, ⟨suffix, htail⟩⟩, Subtype.ext heq.symm⟩
    let correspondence := (Equiv.ofBijective replay
      ⟨replay_injective, replay_surjective⟩).symm
    exact ⟨correspondence, fun _ => rfl, fun _ => rfl⟩
  refine ⟨cutting, ?_⟩
  let Histories (label : List Bool × ℕ × Bool) (size : ℕ) :=
    {steps : List FullStep // steps.length = size ∧ FullRun label.1 label.2.1 label.2.2 steps}
  let next (stack : List Bool) (height : ℕ) (ending : Bool) (count : ℕ)
      (choice : Fin height ⊕ Fin count) : List Bool × ℕ × Bool :=
    match choice with
    | .inl gap => (stack ++ List.replicate gap.val false ++ [true], height - gap.val, true)
    | .inr site =>
      if stack.getD site.val true = false then (stack.take site.val, height, false)
      else
        let repeats := ending && (site.val + 1 == stack.length)
        (bif repeats then [true] else [], bif repeats then height + 1 else height, repeats)
  let operation (stack : List Bool) (height count : ℕ) (choice : Fin height ⊕ Fin count) :=
    match choice with
    | .inl gap => FullStep.pure (.record gap.val)
    | .inr site => if stack.getD site.val true = false then .pure (.descend site.val)
      else .old site.val
  have history_split (stack : List Bool) (height : ℕ) (ending : Bool) (count size : ℕ)
      (hheight : 0 < height) (hcount : stack.length = count) :
      Nonempty (Histories (stack, height, ending) (size + 1) ≃
        Σ choice : Fin height ⊕ Fin count,
          Histories (next stack height ending count choice) size) := by
    have op_injective : Function.Injective (operation stack height count) := by
      intro first second heq
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          change FullStep.pure (.record first.val) = FullStep.pure (.record second.val) at heq
          have hval : first.val = second.val := by injection heq with hpure; injection hpure
          exact congrArg Sum.inl (Fin.ext hval)
        | inr second => dsimp only [operation] at heq; split at heq <;> simp at heq
      | inr first =>
        cases second with
        | inl second => dsimp only [operation] at heq; split at heq <;> simp at heq
        | inr second =>
          dsimp only [operation] at heq
          split at heq <;> split at heq
          · have hval : first.val = second.val := by injection heq with hpure; injection hpure
            exact congrArg Sum.inr (Fin.ext hval)
          · simp at heq
          · simp at heq
          · have hval : first.val = second.val := by injection heq
            exact congrArg Sum.inr (Fin.ext hval)
    have prepend_run (choice : Fin height ⊕ Fin count)
        (tail : Histories (next stack height ending count choice) size) :
        FullRun stack height ending (operation stack height count choice :: tail.val) := by
      have htail := tail.property.2
      cases choice with
      | inl gap => exact FullRun.record stack height gap.val ending tail.val gap.isLt htail
      | inr site =>
        have hsite : site.val < stack.length := by rw [hcount]; exact site.isLt
        by_cases hfresh : stack.getD site.val true = false
        · simp only [next, hfresh, if_true] at htail
          simpa only [operation, hfresh, if_true] using
            FullRun.descend stack height site.val ending tail.val hsite hfresh htail
        · have hold : stack.getD site.val true = true := Bool.eq_true_of_not_eq_false hfresh
          simp only [next, if_neg hfresh] at htail
          simpa only [operation, if_neg hfresh] using
            FullRun.old stack height site.val ending tail.val hheight hsite hold htail
    let prepend : (Σ choice : Fin height ⊕ Fin count,
        Histories (next stack height ending count choice) size) →
        Histories (stack, height, ending) (size + 1) := fun piece =>
      ⟨operation stack height count piece.1 :: piece.2.val,
        ⟨by simp [piece.2.property.1], prepend_run piece.1 piece.2⟩⟩
    have prepend_injective : Function.Injective prepend := by
      rintro ⟨first, firstTail⟩ ⟨second, secondTail⟩ heq
      have hval := congrArg Subtype.val heq
      have hcons := List.cons.inj hval
      have hchoice := op_injective hcons.1
      cases hchoice
      have htail : firstTail = secondTail := Subtype.ext hcons.2
      cases htail
      rfl
    have prepend_surjective : Function.Surjective prepend := by
      rintro ⟨steps, hlength, hrun⟩
      cases hrun with
      | nil stack height ending hpositive => simp at hlength
      | record stack height gap ending rest hgap htail =>
        let choice : Fin height ⊕ Fin count := .inl ⟨gap, hgap⟩
        have hrest : rest.length = size := by simpa using hlength
        let tail : Histories (next stack height ending count choice) size :=
          ⟨rest, hrest, htail⟩
        exact ⟨⟨choice, tail⟩, Subtype.ext rfl⟩
      | descend stack height site ending rest hsite hfresh htail =>
        let choice : Fin height ⊕ Fin count := .inr ⟨site, by rw [← hcount]; exact hsite⟩
        have hrest : rest.length = size := by simpa using hlength
        have hnext : FullRun (next stack height ending count choice).1
            (next stack height ending count choice).2.1
            (next stack height ending count choice).2.2 rest := by
          simpa only [next, choice, hfresh, if_true] using htail
        let tail : Histories (next stack height ending count choice) size :=
          ⟨rest, hrest, hnext⟩
        refine ⟨⟨choice, tail⟩, Subtype.ext ?_⟩
        simp only [prepend, operation, choice, hfresh, if_true]
        rfl
      | old stack height site ending rest hpositive hsite hold htail =>
        let choice : Fin height ⊕ Fin count := .inr ⟨site, by rw [← hcount]; exact hsite⟩
        have hfresh : ¬stack.getD site true = false := by rw [hold]; decide
        have hrest : rest.length = size := by simpa using hlength
        have hnext : FullRun (next stack height ending count choice).1
            (next stack height ending count choice).2.1
            (next stack height ending count choice).2.2 rest := by
          simpa only [next, choice, if_neg hfresh] using htail
        let tail : Histories (next stack height ending count choice) size :=
          ⟨rest, hrest, hnext⟩
        refine ⟨⟨choice, tail⟩, Subtype.ext ?_⟩
        simp only [prepend, operation, choice, if_neg hfresh]
        rfl
    exact ⟨(Equiv.ofBijective prepend ⟨prepend_injective, prepend_surjective⟩).symm⟩
  exact fun count size => history_split stack budget mode count size

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Renewal
