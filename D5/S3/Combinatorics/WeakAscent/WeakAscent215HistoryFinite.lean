/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215HistoryFinite
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215HistoryFinite
   mirror-E: none(waiver:finite-depth-full-history-languages)
   anchors: [mathlib/module/Mathlib.Data.Set.Finite.Lattice]
   utility: none
   digest: Induction over depth bounds full histories by finite unions of legal child languages. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Renewal
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215HistoryFinite

open WeakAscent215Pure WeakAscent215Renewal

theorem full_histories_finite (depth : ℕ) (stack : List Bool) (budget : ℕ) (mode : Bool) :
    {steps : List FullStep | steps.length = depth ∧ FullRun stack budget mode steps}.Finite := by
  induction depth generalizing stack budget mode with
  | zero =>
    apply (Set.finite_singleton ([] : List FullStep)).subset
    intro steps hsteps
    exact List.length_eq_zero_iff.mp hsteps.1
  | succ depth ih =>
    let records : Set (List FullStep) := ⋃ gap : Fin budget,
      (fun rest => FullStep.pure (.record gap.val) :: rest) ''
        {rest | rest.length = depth ∧
          FullRun (stack ++ List.replicate gap.val false ++ [true])
            (budget - gap.val) true rest}
    let descents : Set (List FullStep) := ⋃ site : Fin stack.length,
      (fun rest => FullStep.pure (.descend site.val) :: rest) ''
        {rest | rest.length = depth ∧ FullRun (stack.take site.val) budget false rest}
    let oldSteps : Set (List FullStep) := ⋃ site : Fin stack.length,
      (fun rest => FullStep.old site.val :: rest) ''
        {rest | rest.length = depth ∧ FullRun
          (bif mode && (site.val + 1 == stack.length) then [true] else [])
          (bif mode && (site.val + 1 == stack.length) then budget + 1 else budget)
          (mode && (site.val + 1 == stack.length)) rest}
    have records_finite : records.Finite := by
      apply Set.finite_iUnion
      intro gap
      exact (ih _ _ _).image _
    have descents_finite : descents.Finite := by
      apply Set.finite_iUnion
      intro site
      exact (ih _ _ _).image _
    have old_finite : oldSteps.Finite := by
      apply Set.finite_iUnion
      intro site
      exact (ih _ _ _).image _
    apply ((records_finite.union descents_finite).union old_finite).subset
    intro steps hsteps
    obtain ⟨hlength, hrun⟩ := hsteps
    cases hrun with
    | nil stack budget mode hbudget => simp at hlength
    | record stack budget gap mode rest hgap htail =>
      apply Or.inl
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨⟨gap, hgap⟩, rest, ⟨?_, htail⟩, rfl⟩
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
    | descend stack budget site mode rest hsite hfresh htail =>
      apply Or.inl
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨⟨site, hsite⟩, rest, ⟨?_, htail⟩, rfl⟩
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
    | old stack budget site mode rest hbudget hsite hold htail =>
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨⟨site, hsite⟩, rest, ⟨?_, htail⟩, rfl⟩
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength

end D5.S3.Combinatorics.WeakAscent.WeakAscent215HistoryFinite
