/- GID: D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackThreeDivergence
   mirror-E: none(waiver:first-disagreement-pattern-obstruction)
   anchors: []
   utility: none
   digest: A first disagreement pops a low prefix and leaves a permanent 231 in both stacks. -/

import D5.S3.Combinatorics.VincularStack.VincularStackThreeBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackThreeDivergence

open VincularStackThreeDefs
open VincularStackDefs (Contains231)

theorem divergence (entry : ℕ) (stack : List ℕ) (hnodup : (entry :: stack).Nodup)
    (havoid : ¬ Contains312 false false stack)
    (hillegal : Contains312 false false (entry :: stack))
    (hlegal : ¬ Contains312 false true (entry :: stack)) :
    ∃ popped : List ℕ, ∃ high : ℕ, ∃ tail : List ℕ, ∃ low : ℕ,
      stack = popped ++ high :: tail ∧ popped ≠ [] ∧
      (∀ value ∈ popped, value < low) ∧ low ∈ tail ∧ low < entry ∧ entry < high ∧
      Push false false entry stack = (popped, entry :: high :: tail) ∧
      Push false true entry stack = ([], entry :: stack) ∧
      Contains231 (entry :: high :: tail) ∧ Contains231 (entry :: stack) := by
  have hfresh : ∀ position, position < stack.length → stack.getD position 0 ≠ entry := by
    intro position hposition heq
    apply (List.nodup_cons.mp hnodup).1
    rw [← heq, List.getD_eq_getElem stack 0 hposition]
    exact List.getElem_mem hposition
  have hdistinct : ∀ first last, first < last → last < stack.length →
      stack.getD first 0 ≠ stack.getD last 0 := by
    intro first last hfirst hlast
    rw [List.getD_eq_getElem stack 0 (by omega), List.getD_eq_getElem stack 0 hlast]
    exact fun heq => (by omega : first ≠ last) (hnodup.of_cons.getElem_inj_iff.mp heq)
  have hascent : ∃ first last, first < last ∧ last < stack.length ∧
      stack.getD first 0 < stack.getD last 0 ∧ stack.getD last 0 < entry := by
    obtain ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper, _, _⟩ :=
      hillegal
    cases first with
    | zero =>
      cases middle with
      | zero => omega
      | succ middle =>
        cases last with
        | zero => omega
        | succ last =>
          exact ⟨middle, last, by omega, by simpa using hlast,
            by simpa using hlower, by simpa using hupper⟩
    | succ first =>
      cases middle with
      | zero => omega
      | succ middle =>
        cases last with
        | zero => omega
        | succ last =>
          exact False.elim (havoid ⟨first, by simpa using hfirst,
            middle, by simpa using hmiddle, last, by simpa using hlast,
            by omega, by omega, by simpa using hlower, by simpa using hupper,
            by simp, by simp⟩)
  obtain ⟨first, last, hfl, hlast, hasc, hlow⟩ := hascent
  have hnoascent : ∀ position, position + 1 < stack.length →
      stack.getD (position + 1) 0 < entry →
      stack.getD (position + 1) 0 ≤ stack.getD position 0 := by
    intro position hposition hbelow
    by_contra hnot
    apply hlegal
    refine ⟨0, by simp, position + 1, by simp; omega,
      position + 2, by simp; omega, by omega, by omega, ?_, ?_, by simp, by simp⟩
    · simpa using (by omega : stack.getD position 0 < stack.getD (position + 1) 0)
    · simpa [Nat.add_assoc] using hbelow
  have hdecrease : ∀ start finish, start ≤ finish → finish < stack.length →
      (∀ position, start ≤ position → position ≤ finish →
        stack.getD position 0 < entry) →
      stack.getD finish 0 ≤ stack.getD start 0 := by
    intro start finish horder
    induction finish, horder using Nat.le_induction with
    | base => intros; exact le_rfl
    | succ finish horder inductionHypothesis =>
      intro hfinish hbelow
      exact (hnoascent finish hfinish (hbelow (finish + 1) (by omega) le_rfl)).trans
        (inductionHypothesis (by omega)
          (fun position hp hq => hbelow position hp (by omega)))
  have hexists : ∃ position, position < last ∧ entry < stack.getD position 0 := by
    by_contra hnone
    have hbelow : ∀ position, first ≤ position → position ≤ last →
        stack.getD position 0 < entry := by
      intro position hp hq
      by_cases heq : position = last
      · simpa [heq] using hlow
      · have hnot : ¬ entry < stack.getD position 0 :=
          fun hlarge => hnone ⟨position, by omega, hlarge⟩
        have := hfresh position (by omega)
        omega
    have := hdecrease first last (by omega) hlast hbelow
    omega
  let boundary := Nat.find hexists
  have hboundary : boundary < last ∧ entry < stack.getD boundary 0 := Nat.find_spec hexists
  have hbefore : ∀ position, position < boundary → stack.getD position 0 < entry := by
    intro position hposition
    have hne := hfresh position (by omega)
    have hnotlarge : ¬ entry < stack.getD position 0 := by
      intro hlarge
      have := Nat.find_min' hexists ⟨by omega, hlarge⟩
      dsimp [boundary] at hposition
      omega
    omega
  have hfirstboundary : first < boundary := by
    by_contra hnot
    have hle : boundary ≤ first := by omega
    by_cases heq : boundary = first
    · rw [heq] at hboundary
      omega
    · apply havoid
      exact ⟨boundary, by omega, first, by omega, last, hlast, by omega, hfl,
        hasc, by omega, by simp, by simp⟩
  have hprefixbound : ∀ position, position < boundary →
      stack.getD position 0 < stack.getD last 0 := by
    intro position hposition
    by_cases hprior : position < first
    · rcases lt_or_gt_of_ne (hdistinct position last (by omega) hlast) with hbelow | habove
      · exact hbelow
      · exact False.elim (havoid ⟨position, by omega, first, by omega, last, hlast,
          hprior, hfl, hasc, habove, by simp, by simp⟩)
    · have hle := hdecrease first position (by omega) (by omega)
        (fun index _ hindex => hbefore index (by omega))
      omega
  let popped := stack.take boundary
  let high := stack.getD boundary 0
  let tail := stack.drop (boundary + 1)
  let low := stack.getD last 0
  have hhigh : entry < high := hboundary.2
  have hlower : low < entry := hlow
  have hread : ∀ offset position,
      (stack.drop offset).getD position 0 = stack.getD (offset + position) 0 := by
    intro offset position
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hsplit : stack = popped ++ high :: tail := by
    dsimp [popped, high, tail]
    rw [List.getD_eq_getElem stack 0 (by omega)]
    exact (List.take_append_drop boundary stack).symm.trans (by
      congr 1
      exact List.drop_eq_getElem_cons (by omega))
  have hpnonempty : popped ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [popped, List.length_take, List.length_nil] at hlength
    omega
  have hpbound : ∀ value ∈ popped, value < low := by
    intro value hvalue
    obtain ⟨position, hposition, hvalue⟩ := List.mem_iff_getElem.mp hvalue
    have hindex : position < boundary := by
      simp only [popped, List.length_take] at hposition
      omega
    have hget : stack.getD position 0 = value := by
      rw [List.getD_eq_getElem stack 0 (by omega)]
      simpa only [popped, List.getElem_take] using hvalue
    rw [← hget]
    exact hprefixbound position hindex
  have hlowtail : low ∈ tail := by
    have hindex : last - (boundary + 1) < tail.length := by
      simp only [tail, List.length_drop]
      omega
    have hget : tail.getD (last - (boundary + 1)) 0 = low := by
      rw [hread]
      have heq : boundary + 1 + (last - (boundary + 1)) = last := by omega
      rw [heq]
    rw [← hget, List.getD_eq_getElem tail 0 hindex]
    exact List.getElem_mem hindex
  have hterminal : ¬ Contains312 false false (entry :: high :: tail) := by
    rintro ⟨start, hstart, middle, hmiddle, finish, hfinish, hsm, hmf,
      hlower, hupper, _, _⟩
    have htailread : ∀ position, tail.getD position 0 =
        stack.getD (boundary + 1 + position) 0 := hread (boundary + 1)
    cases start with
    | zero =>
      cases middle with
      | zero => omega
      | succ middle =>
        cases middle with
        | zero =>
          change high < (entry :: high :: tail).getD finish 0 at hlower
          change (entry :: high :: tail).getD finish 0 < entry at hupper
          omega
        | succ middle =>
          cases finish with
          | zero => omega
          | succ finish =>
            cases finish with
            | zero => omega
            | succ finish =>
              simp only [List.getD_cons_zero, List.getD_cons_succ] at hlower hupper
              apply havoid
              refine ⟨boundary, by omega, boundary + 1 + middle, ?_,
                boundary + 1 + finish, ?_, by omega, by omega, ?_, ?_, by simp, by simp⟩
              · simp only [List.length_cons, tail, List.length_drop] at hmiddle; omega
              · simp only [List.length_cons, tail, List.length_drop] at hfinish; omega
              · simpa only [htailread] using hlower
              · rw [← htailread]
                change tail.getD finish 0 < high
                omega
    | succ start =>
      cases middle with
      | zero => omega
      | succ middle =>
        cases finish with
        | zero => omega
        | succ finish =>
          have hrest : high :: tail = stack.drop boundary := by
            dsimp [high, tail]
            rw [List.getD_eq_getElem stack 0 (by omega)]
            exact (List.drop_eq_getElem_cons (by omega)).symm
          simp only [List.getD_cons_succ] at hlower hupper
          rw [hrest, hread, hread] at hlower hupper
          apply havoid
          refine ⟨boundary + start, ?_, boundary + middle, ?_, boundary + finish, ?_,
            by omega, by omega, hlower, hupper, by simp, by simp⟩ <;>
            simp only [List.length_cons, hrest, List.length_drop] at hstart hmiddle hfinish <;>
            omega
  have hpop : ∀ front : List ℕ, (∀ value ∈ front, value < low) →
      Push false false entry (front ++ high :: tail) = (front, entry :: high :: tail) := by
    intro front
    induction front with
    | nil =>
      intro hbound
      simp only [List.nil_append, Push, if_neg hterminal]
    | cons top front inductionHypothesis =>
      intro hbound
      have htop := hbound top (by simp)
      have htest : Contains312 false false (entry :: top :: (front ++ high :: tail)) := by
        obtain ⟨position, hposition, hvalue⟩ := List.mem_iff_getElem.mp hlowtail
        refine ⟨0, by simp, 1, by simp, front.length + position + 3, by simp; omega,
          by omega, by omega, ?_, ?_, by simp, by simp⟩
        · simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [List.getD_append_right front (high :: tail) 0 _ (by omega)]
          have heq : front.length + position + 1 - front.length = position + 1 := by omega
          rw [heq]
          simp only [List.getD_cons_succ]
          rw [List.getD_eq_getElem tail 0 hposition, hvalue]
          exact htop
        · simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [List.getD_append_right front (high :: tail) 0 _ (by omega)]
          have heq : front.length + position + 1 - front.length = position + 1 := by omega
          rw [heq]
          simp only [List.getD_cons_succ]
          rw [List.getD_eq_getElem tail 0 hposition, hvalue]
          exact hlower
      simp only [List.cons_append, Push, if_pos htest]
      rw [inductionHypothesis (fun value hvalue => hbound value (by simp [hvalue]))]
  have hpushB : Push false true entry stack = ([], entry :: stack) := by
    cases stack with
    | nil => rfl
    | cons top rest => simp only [Push, if_neg hlegal]
  have hbadC : Contains231 (entry :: high :: tail) := by
    obtain ⟨position, hposition, hvalue⟩ := List.mem_iff_getElem.mp hlowtail
    refine ⟨0, 1, position + 2, by omega, by omega, by simp; omega, ?_, ?_⟩
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [List.getD_eq_getElem tail 0 hposition, hvalue]
      exact hlower
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hhigh
  have hbadB : Contains231 (entry :: stack) := by
    exact ⟨0, boundary + 1, last + 1, by omega, by omega, by simp; omega,
      by simpa using hlow, by simpa using hboundary.2⟩
  exact ⟨popped, high, tail, low, hsplit, hpnonempty, hpbound, hlowtail, hlow,
    hboundary.2, by rw [hsplit]; exact hpop popped hpbound, hpushB, hbadC, hbadB⟩

end D5.S3.Combinatorics.VincularStack.VincularStackThreeDivergence
