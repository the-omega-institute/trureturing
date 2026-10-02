/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Finite
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Finite
   mirror-E: none(waiver:fixed-bidegree-history-finiteness)
   anchors: [mathlib/module/Mathlib.Data.Set.Finite.List, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Bounds every pure-history site and encodes fixed bidegrees in a finite alphabet. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Pure
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Finite

open WeakAscent215Pure

theorem pure_histories_finite (length totalSpend : ℕ) :
    {steps : List PureStep | steps.length = length ∧ spend steps = totalSpend ∧
      ∃ ending, PureRun [] steps ending}.Finite := by
  classical
  have bound (stack ending : List Bool) (steps : List PureStep)
      (hrun : PureRun stack steps ending) :
      ∀ step ∈ steps, match step with
        | .record gap => gap ≤ spend steps
        | .descend site => site < stack.length + spend steps + steps.length := by
    induction hrun with
    | nil stack => simp
    | record stack ending rest gap htail ih =>
      intro step hstep
      simp only [List.mem_cons] at hstep
      rcases hstep with rfl | hrest
      · simp only [spend]
        omega
      · have hb := ih step hrest
        cases step with
        | record nextGap =>
          simp only [spend] at hb ⊢
          omega
        | descend site =>
          simp only [List.length_append, List.length_replicate, List.length_cons,
            List.length_nil, spend] at hb ⊢
          omega
    | descend stack ending rest site hsite hfresh htail ih =>
      intro step hstep
      simp only [List.mem_cons] at hstep
      rcases hstep with rfl | hrest
      · simp only [spend, List.length_cons]
        omega
      · have hb := ih step hrest
        cases step with
        | record gap => exact hb
        | descend nextSite =>
          simp only [spend, List.length_cons, List.length_take] at hb ⊢
          omega
  let limit := length + totalSpend + 1
  let decode : Bool × Fin limit → PureStep := fun tagged =>
    if tagged.1 then PureStep.record tagged.2.val else PureStep.descend tagged.2.val
  let decodeList : (Fin length → Bool × Fin limit) → List PureStep :=
    fun encoded => List.ofFn fun index => decode (encoded index)
  have finite_lists : (Set.range decodeList).Finite := Set.finite_range decodeList
  apply finite_lists.subset
  intro steps hsteps
  obtain ⟨hlength, hspend, ending, hrun⟩ := hsteps
  have letter_bound (step : PureStep) (hstep : step ∈ steps) :
      match step with
        | .record gap => gap < limit
        | .descend site => site < limit := by
    have hb := bound [] ending steps hrun step hstep
    cases step with
    | record gap =>
      simp only [hspend] at hb
      dsimp [limit]
      omega
    | descend site =>
      simp only [List.length_nil, Nat.zero_add, hspend, hlength] at hb
      dsimp [limit]
      omega
  let encode : Fin length → Bool × Fin limit := fun index =>
    match hstep : steps[index.val]'(by omega) with
    | .record gap => (true, ⟨gap, by
        have hb := letter_bound (.record gap) (hstep ▸ List.getElem_mem (by omega))
        exact hb⟩)
    | .descend site => (false, ⟨site, by
        have hb := letter_bound (.descend site) (hstep ▸ List.getElem_mem (by omega))
        exact hb⟩)
  refine ⟨encode, ?_⟩
  apply List.ext_getElem
  · simp [decodeList, hlength]
  · intro index hencoded hindex
    have hi : index < length := by simpa [decodeList] using hencoded
    change (List.ofFn fun index => decode (encode index))[index] = steps[index]
    rw [List.getElem_ofFn]
    dsimp [encode, decode]
    split <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rename_i hstep <;> exact hstep.symm

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Finite
