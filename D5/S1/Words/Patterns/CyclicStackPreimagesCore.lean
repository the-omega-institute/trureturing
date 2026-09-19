/- GID: D5/S1/Words/Patterns/CyclicStackPreimagesCore
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimages
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Parity, mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Literal cyclic-stack semantics and converse barrier infrastructure. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeWhile

/-!
# Consecutive cyclic-pattern-avoiding stack preimages

This is the consecutive cyclic `[123]` stack map of Zhan and Bie. With the
stack written top first, an incoming value `x` pops the top `a` over `b`
exactly for the patterns `x < a < b`, `b < x < a`, or `a < b < x`. The same
test is repeated after every pop, and the remaining stack is flushed top first.

For `m = n / 2`, the target is `(1,...,m,n,...,m+1)`. The fibre is taken
inside the complete list of permutations of `(1,...,n)`, independently of the
candidate family used in the proof.

The definitions and symbolic candidate proofs are not bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite instance
(`utility: none`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.CyclicStackPreimages

/-- Finite source data used by the information-registration sidecar. Each
coordinate packs one forbidden-pattern bit and three base-five digits. -/
abbrev CyclicStackSourceWord := Fin 6 → Fin 250

def sourceCode (forbiddenBit : Bool) (input output gap : Fin 5) : Fin 250 :=
  ⟨(if forbiddenBit then 125 else 0) + input * 25 + output * 5 + gap, by
    split <;> omega⟩

/-- The forbidden-pattern truth table, Figure 3 input/output, and the first
even gap candidate in one closed finite word. -/
def cyclicStackSourceWord : CyclicStackSourceWord :=
  ![sourceCode true 3 4 3, sourceCode false 1 2 1,
    sourceCode false 2 1 4, sourceCode true 4 3 2,
    sourceCode true 0 0 0, sourceCode false 0 0 0]

/-- Whether the incoming value and the top two stack entries form one of the
three forbidden consecutive cyclic patterns. -/
def forbidden (x a b : ℕ) : Bool :=
  decide (x < a ∧ a < b ∨ b < x ∧ x < a ∨ a < b ∧ b < x)

/-- Pop the shortest forced prefix of a top-first stack. The first component
is the output produced by these pops and the second is the surviving stack. -/
def drain (x : ℕ) : List ℕ → List ℕ × List ℕ
  | a :: b :: stack =>
      if forbidden x a b then
        let rest := drain x (b :: stack)
        (a :: rest.1, rest.2)
      else
        ([], a :: b :: stack)
  | stack => ([], stack)

/-- Process input against a top-first stack and finally flush that stack. -/
def process : List ℕ → List ℕ → List ℕ
  | [], stack => stack
  | x :: input, stack =>
      let step := drain x stack
      step.1 ++ process input (x :: step.2)

/-- The output and residual stack after a prefix, before the final flush. -/
def run : List ℕ → List ℕ → List ℕ × List ℕ
  | [], stack => ([], stack)
  | x :: input, stack =>
      let step := drain x stack
      let rest := run input (x :: step.2)
      (step.1 ++ rest.1, rest.2)

private lemma run_append (pre suffix stack : List ℕ) :
    run (pre ++ suffix) stack =
      let first := run pre stack
      let second := run suffix first.2
      (first.1 ++ second.1, second.2) := by
  induction pre generalizing stack with
  | nil => rfl
  | cons x pre ih =>
      simp only [List.cons_append, run]
      let step := drain x stack
      rw [ih]
      simp only [List.append_assoc]

lemma process_eq_run (input stack : List ℕ) :
    let _sourceObject := cyclicStackSourceWord
    process input stack = (run input stack).1 ++ (run input stack).2 := by
  induction input generalizing stack with
  | nil => rfl
  | cons x input ih =>
      simp only [process, run]
      let step := drain x stack
      rw [ih]
      simp only [List.append_assoc]

lemma process_append (pre suffix stack : List ℕ) :
    let _sourceObject := cyclicStackSourceWord
    process (pre ++ suffix) stack =
      (run pre stack).1 ++ process suffix (run pre stack).2 := by
  rw [process_eq_run, run_append, process_eq_run]
  simp only [List.append_assoc]

private lemma run_stack_ne_nil (input stack : List ℕ)
    (hne : input ≠ [] ∨ stack ≠ []) : (run input stack).2 ≠ [] := by
  induction input generalizing stack with
  | nil =>
      simp only [run]
      rcases hne with h | h
      · exact (h rfl).elim
      · exact h
  | cons x input ih =>
      simp only [run]
      apply ih
      exact Or.inr (List.cons_ne_nil x (drain x stack).2)

private lemma drain_stack_ne_nil (x : ℕ) {stack : List ℕ} (hne : stack ≠ []) :
    (drain x stack).2 ≠ [] := by
  induction stack with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
      cases tail with
      | nil => simp [drain]
      | cons b rest =>
          simp only [drain]
          split
          · exact ih (List.cons_ne_nil b rest)
          · simp

private lemma drain_append (x : ℕ) (stack : List ℕ) :
    (drain x stack).1 ++ (drain x stack).2 = stack := by
  induction stack with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b rest =>
          simp only [drain]
          split
          · simpa only [List.cons_append] using congrArg (a :: ·) ih
          · rfl

/-- Entries already on the stack retain their top-to-bottom order in all
future output. This is the LIFO fact used by the barrier argument. -/
private lemma stack_sublist_process (input stack : List ℕ) :
    stack.Sublist (process input stack) := by
  induction input generalizing stack with
  | nil => exact List.Sublist.refl stack
  | cons x input ih =>
      simp only [process]
      let step := drain x stack
      have htail : step.2.Sublist (process input (x :: step.2)) :=
        (List.sublist_cons_self x step.2).trans (ih (x :: step.2))
      have hwhole : (step.1 ++ step.2).Sublist
          (step.1 ++ process input (x :: step.2)) :=
        htail.append_left step.1
      simpa only [step, drain_append] using hwhole

lemma process_perm (input stack : List ℕ) :
    let _sourceObject := cyclicStackSourceWord
    (process input stack).Perm (input ++ stack) := by
  induction input generalizing stack with
  | nil => exact List.Perm.refl stack
  | cons x input ih =>
      simp only [process]
      let step := drain x stack
      have hprocess := (ih (x :: step.2)).append_left step.1
      have hcomm : (step.1 ++ input).Perm (input ++ step.1) :=
        List.perm_append_comm
      have hswap₁ := hcomm.append_right (x :: step.2)
      have hswap₂ := (List.perm_middle (a := x) (l₁ := step.1) (l₂ := step.2)).append_left input
      have hswap₃ := List.perm_middle (a := x) (l₁ := input)
        (l₂ := step.1 ++ step.2)
      have hmove : (step.1 ++ (input ++ x :: step.2)).Perm
          (x :: (input ++ (step.1 ++ step.2))) := by
        have ha : (step.1 ++ (input ++ x :: step.2)).Perm
            ((input ++ step.1) ++ x :: step.2) := by
          simpa only [List.append_assoc] using hswap₁
        have hb : ((input ++ step.1) ++ x :: step.2).Perm
            (input ++ x :: (step.1 ++ step.2)) := by
          simpa only [List.append_assoc] using hswap₂
        exact ha.trans (hb.trans hswap₃)
      have hstack : step.1 ++ step.2 = stack := by
        simpa only [step] using drain_append x stack
      change (step.1 ++ process input (x :: step.2)).Perm (x :: (input ++ stack))
      rw [← hstack]
      exact hprocess.trans hmove

private lemma run_perm (input stack : List ℕ) :
    ((run input stack).1 ++ (run input stack).2).Perm (input ++ stack) := by
  rw [← process_eq_run]
  exact process_perm input stack

/-- The consecutive cyclic `[123]` stack-sorting map. -/
def cyclicStackSort (input : List ℕ) : List ℕ :=
  process input []

/-- The target `(1,...,floor(n/2),n,...,floor(n/2)+1)`. -/
def target (n : ℕ) : List ℕ :=
  List.range' 1 (n / 2) ++ (List.range' (n / 2 + 1) (n - n / 2)).reverse

private lemma target_pairwise_barrier (n : ℕ) :
    (target n).Pairwise fun earlier later =>
      ¬(n / 2 < earlier ∧ later ≤ n / 2) := by
  let m := n / 2
  let lows := List.range' 1 m
  let highs := (List.range' (m + 1) (n - m)).reverse
  have hlows : lows.Pairwise fun earlier later => ¬(m < earlier ∧ later ≤ m) := by
    apply List.pairwise_of_forall_mem_list
    intro earlier hearlier later _
    simp only [lows, List.mem_range'] at hearlier
    omega
  have hhighs : highs.Pairwise fun earlier later => ¬(m < earlier ∧ later ≤ m) := by
    apply List.pairwise_of_forall_mem_list
    intro earlier _ later hlater
    simp only [highs, List.mem_reverse, List.mem_range'] at hlater
    omega
  rw [show target n = lows ++ highs by rfl, List.pairwise_append]
  refine ⟨hlows, hhighs, ?_⟩
  intro earlier hearlier later _
  simp only [lows, List.mem_range'] at hearlier
  omega

private lemma target_pairwise_lows (n : ℕ) :
    (target n).Pairwise fun earlier later =>
      earlier ≤ n / 2 → later ≤ n / 2 → earlier < later := by
  let m := n / 2
  let lows := List.range' 1 m
  let highs := (List.range' (m + 1) (n - m)).reverse
  have hlows : lows.Pairwise fun earlier later =>
      earlier ≤ m → later ≤ m → earlier < later := by
    apply (List.pairwise_lt_range' (s := 1) (n := m)).imp
    intro earlier later hlt _ _
    exact hlt
  have hhighs : highs.Pairwise fun earlier later =>
      earlier ≤ m → later ≤ m → earlier < later := by
    apply List.pairwise_of_forall_mem_list
    intro earlier hearlier
    simp only [highs, List.mem_reverse, List.mem_range'] at hearlier
    omega
  rw [show target n = lows ++ highs by rfl, List.pairwise_append]
  refine ⟨hlows, hhighs, ?_⟩
  intro earlier _ later hlater _ hlaterLow
  simp only [highs, List.mem_reverse, List.mem_range'] at hlater
  omega

lemma target_low_order {n earlier later : ℕ}
    (hearlier : earlier ≤ n / 2) (hlater : later ≤ n / 2)
    (hpair : [earlier, later].Sublist (target n)) :
    let _sourceObject := cyclicStackSourceWord
    earlier < later := by
  exact (target_pairwise_lows n).forall_sublist hpair hearlier hlater

private lemma barrier {n high low : ℕ} (hhigh : n / 2 < high)
    (hlow : low ≤ n / 2) {input stack : List ℕ}
    (hpair : [high, low].Sublist stack)
    (houtput : process input stack = target n) : False := by
  have hfuture := hpair.trans (stack_sublist_process input stack)
  rw [houtput] at hfuture
  exact (target_pairwise_barrier n).forall_sublist hfuture ⟨hhigh, hlow⟩

private lemma barrier_sublist {n high low : ℕ} (hhigh : n / 2 < high)
    (hlow : low ≤ n / 2) {input stack : List ℕ}
    (hpair : [high, low].Sublist stack)
    (houtput : (process input stack).Sublist (target n)) : False := by
  have hfuture := hpair.trans (stack_sublist_process input stack)
  exact (target_pairwise_barrier n).forall_sublist (hfuture.trans houtput) ⟨hhigh, hlow⟩

lemma drain_low_over_high {n low high : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low :: input) (high :: stack)).Sublist (target n)) :
    let _sourceObject := cyclicStackSourceWord
    drain low (high :: stack) = ([], high :: stack) := by
  cases stack with
  | nil => rfl
  | cons below rest =>
      simp only [drain]
      split
      next hforbidden =>
        exfalso
        let step := drain low (below :: rest)
        have hlowStack : [low].Sublist (low :: step.2) := by
          simpa only [List.singleton_append] using
            List.sublist_append_left [low] step.2
        have hlowFuture : [low].Sublist (process input (low :: step.2)) :=
          hlowStack.trans (stack_sublist_process input (low :: step.2))
        have hlowTail : [low].Sublist (step.1 ++ process input (low :: step.2)) :=
          hlowFuture.trans (List.sublist_append_right step.1 _)
        have hpair : [high, low].Sublist
            (high :: (step.1 ++ process input (low :: step.2))) :=
          hlowTail.cons_cons high
        have hshape : process (low :: input) (high :: below :: rest) =
            high :: (step.1 ++ process input (low :: step.2)) := by
          simp [process, drain, hforbidden, step]
        rw [hshape] at houtput
        exact (target_pairwise_barrier n).forall_sublist
          (hpair.trans houtput) ⟨hhigh, hlow⟩
      next _ => rfl

/-- Two lows cannot occupy the same chronological gap after a high. The
second low either pops the first in decreasing order, or remains above it in
increasing order; both possibilities reverse their required target order. -/
lemma no_two_lows_after_high {n low₁ low₂ high : ℕ}
    (hlow₁ : low₁ ≤ n / 2) (hlow₂ : low₂ ≤ n / 2)
    (hne : low₁ ≠ low₂) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low₁ :: low₂ :: input) (high :: stack)).Sublist
      (target n)) :
    let _sourceObject := cyclicStackSourceWord
    False := by
  have hfirst := drain_low_over_high hlow₁ hhigh houtput
  have htail : (process (low₂ :: input) (low₁ :: high :: stack)).Sublist
      (target n) := by
    simpa only [process, hfirst, List.nil_append] using houtput
  simp only [process, drain] at htail
  split at htail
  next hforbidden =>
    have hdescending : low₂ < low₁ := by
      have hf : low₂ < low₁ ∧ low₁ < high ∨
          high < low₂ ∧ low₂ < low₁ ∨
          low₁ < high ∧ high < low₂ := by
        simpa [forbidden] using hforbidden
      rcases hf with hf | hf | hf <;> omega
    let step := drain low₂ (high :: stack)
    have hlowStack : [low₂].Sublist (low₂ :: step.2) := by
      simpa only [List.singleton_append] using
        List.sublist_append_left [low₂] step.2
    have hlowFuture : [low₂].Sublist (process input (low₂ :: step.2)) :=
      hlowStack.trans (stack_sublist_process input (low₂ :: step.2))
    have hlowTail : [low₂].Sublist
        (step.1 ++ process input (low₂ :: step.2)) :=
      hlowFuture.trans (List.sublist_append_right step.1 _)
    have hpair : [low₁, low₂].Sublist
        (low₁ :: (step.1 ++ process input (low₂ :: step.2))) :=
      hlowTail.cons_cons low₁
    have htarget : [low₁, low₂].Sublist (target n) := by
      exact hpair.trans (by simpa only [step, List.cons_append] using htail)
    have := target_low_order hlow₁ hlow₂ htarget
    omega
  next hallowed =>
    have hincreasing : low₁ < low₂ := by
      have hf : ¬(low₂ < low₁ ∧ low₁ < high ∨
          high < low₂ ∧ low₂ < low₁ ∨
          low₁ < high ∧ high < low₂) := by
        simpa [forbidden] using hallowed
      by_contra hnot
      apply hf
      left
      constructor <;> omega
    have hstackPair : [low₂, low₁].Sublist (low₂ :: low₁ :: high :: stack) := by
      exact List.sublist_append_left [low₂, low₁] (high :: stack)
    have hfuture : [low₂, low₁].Sublist
        (process input (low₂ :: low₁ :: high :: stack)) :=
      hstackPair.trans (stack_sublist_process input _)
    have htarget : [low₂, low₁].Sublist (target n) := by
      exact hfuture.trans (by simpa only [List.nil_append] using htail)
    have := target_low_order hlow₂ hlow₁ htarget
    omega

/-- If a high arrives while a low is pending directly above the preceding
high, successful execution forces the preceding high to be smaller. This is
the local `312` pop which orders highs without assuming their order. -/
lemma pending_low_forces_high_increase {n low high next : ℕ}
    (hlow : low ≤ n / 2) (hnext : n / 2 < next)
    {input stack : List ℕ}
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)) :
    let _sourceObject := cyclicStackSourceWord
    high < next := by
  simp only [process, drain] at houtput
  split at houtput
  next hforbidden =>
    have hf : next < low ∧ low < high ∨ high < next ∧ next < low ∨
        low < high ∧ high < next := by
      simpa [forbidden] using hforbidden
    rcases hf with hf | hf | hf <;> omega
  next _ =>
    exfalso
    have hstackPair : [next, low].Sublist (next :: low :: high :: stack) := by
      exact List.sublist_append_left [next, low] (high :: stack)
    have hfuture : [next, low].Sublist
        (process input (next :: low :: high :: stack)) :=
      hstackPair.trans (stack_sublist_process input _)
    have htarget : [next, low].Sublist (target n) := by
      exact hfuture.trans (by simpa only [List.nil_append] using houtput)
    exact (target_pairwise_barrier n).forall_sublist htarget ⟨hnext, hlow⟩

lemma drain_high_while_low_remains {n x high futureLow : ℕ}
    (hhigh : n / 2 < high) (hlow : futureLow ≤ n / 2)
    {input stack : List ℕ} (hmem : futureLow ∈ input)
    (houtput : (process (x :: input) (high :: stack)).Sublist (target n)) :
    let _sourceObject := cyclicStackSourceWord
    drain x (high :: stack) = ([], high :: stack) := by
  cases stack with
  | nil => rfl
  | cons below rest =>
      simp only [drain]
      split
      next hforbidden =>
        exfalso
        let step := drain x (below :: rest)
        have hfutureMem : futureLow ∈ process input (x :: step.2) := by
          have hp := process_perm input (x :: step.2)
          apply hp.mem_iff.mpr
          exact List.mem_append_left _ hmem
        have hfutureSub : [futureLow].Sublist (process input (x :: step.2)) :=
          List.singleton_sublist.mpr hfutureMem
        have hfutureTail : [futureLow].Sublist
            (step.1 ++ process input (x :: step.2)) :=
          hfutureSub.trans (List.sublist_append_right step.1 _)
        have hpair : [high, futureLow].Sublist
            (high :: (step.1 ++ process input (x :: step.2))) :=
          hfutureTail.cons_cons high
        have hshape : process (x :: input) (high :: below :: rest) =
            high :: (step.1 ++ process input (x :: step.2)) := by
          simp [process, drain, hforbidden, step]
        rw [hshape] at houtput
        exact (target_pairwise_barrier n).forall_sublist
          (hpair.trans houtput) ⟨hhigh, hlow⟩
      next _ => rfl

private lemma pending_low_drain_shape {n low high next : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    {input stack : List ℕ}
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)) :
    drain next (low :: high :: stack) =
      (low :: (drain next (high :: stack)).1, (drain next (high :: stack)).2) := by
  have hinc := pending_low_forces_high_increase hlow hnext houtput
  have hforbidden : forbidden next low high = true := by
    simp [forbidden]
    omega
  simp [drain, hforbidden]

lemma pending_low_drains_only_low_while_low_remains
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)) :
    let _sourceObject := cyclicStackSourceWord
    drain next (low :: high :: stack) = ([low], high :: stack) := by
  have hshape := pending_low_drain_shape hlow hhigh hnext houtput
  have htail : (process (next :: input) (high :: stack)).Sublist (target n) := by
    rw [process, hshape] at houtput
    simp only [List.cons_append] at houtput
    have hsuffix : (process (next :: input) (high :: stack)).Sublist
        (low :: process (next :: input) (high :: stack)) :=
      List.sublist_cons_self low _
    apply hsuffix.trans
    simpa only [process] using houtput
  have hstop := drain_high_while_low_remains hhigh hfutureLow hmem htail
  rw [hshape, hstop]

lemma process_pending_low_while_low_remains
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)) :
    let _sourceObject := cyclicStackSourceWord
    process (next :: input) (low :: high :: stack) =
      low :: process input (next :: high :: stack) := by
  rw [process, pending_low_drains_only_low_while_low_remains hlow hhigh hnext
    hfutureLow hmem houtput]
  rfl

private lemma drain_greater_over_descending_top {next high below : ℕ}
    (hbelow : below < high) (hnext : high < next) (stack : List ℕ) :
    drain next (high :: below :: stack) = ([], high :: below :: stack) := by
  have hallowed : forbidden next high below = false := by
    simp [forbidden]
    omega
  simp [drain, hallowed]

private lemma pending_low_drains_only_low_over_descending_top
    {n low high next below : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hbelow : below < high) {input : List ℕ} (stack : List ℕ)
    (houtput : (process (next :: input) (low :: high :: below :: stack)).Sublist
      (target n)) :
    drain next (low :: high :: below :: stack) =
      ([low], high :: below :: stack) := by
  have hinc := pending_low_forces_high_increase hlow hnext houtput
  rw [pending_low_drain_shape hlow hhigh hnext houtput,
    drain_greater_over_descending_top hbelow hinc]

/-- A successful input starts with a high: a nonempty initial block of lows
would leave a low below that first high, contradicting the barrier. -/
lemma no_lows_before_first_high {n high : ℕ} {pre rest : List ℕ}
    (hpre : ∀ low ∈ pre, low ≤ n / 2) (hhigh : n / 2 < high)
    (houtput : cyclicStackSort (pre ++ high :: rest) = target n) :
    let _sourceObject := cyclicStackSourceWord
    pre = [] := by
  by_contra hne
  let first := run pre []
  have hfirst : first.2 ≠ [] := by
    exact run_stack_ne_nil pre [] (Or.inl hne)
  let step := drain high first.2
  have hstep : step.2 ≠ [] := by
    exact drain_stack_ne_nil high hfirst
  cases hs : step.2 with
  | nil => exact hstep hs
  | cons low tail =>
      have hlowFirst : low ∈ first.2 := by
        have hmem : low ∈ step.1 ++ step.2 := by simp [hs]
        rw [show step.1 ++ step.2 = first.2 by
          simpa only [step] using drain_append high first.2] at hmem
        exact hmem
      have hlowPre : low ∈ pre := by
        have hmem : low ∈ first.1 ++ first.2 := List.mem_append_right _ hlowFirst
        have hp := run_perm pre []
        change (first.1 ++ first.2).Perm (pre ++ []) at hp
        simpa using (hp.mem_iff.mp hmem : low ∈ pre ++ [])
      have hlow := hpre low (by simpa using hlowPre)
      unfold cyclicStackSort at houtput
      rw [process_append] at houtput
      simp only [process] at houtput
      change first.1 ++ (step.1 ++ process rest (high :: step.2)) = target n at houtput
      have hfuture : (process rest (high :: step.2)).Sublist (target n) := by
        have hsuffix := List.sublist_append_right step.1
          (process rest (high :: step.2))
        have hsuffix := List.sublist_append_of_sublist_right (l₁ := first.1) hsuffix
        rw [houtput] at hsuffix
        exact hsuffix
      have hpair : [high, low].Sublist (high :: step.2) := by
        rw [hs]
        exact List.sublist_append_left [high, low] tail
      exact barrier_sublist hhigh hlow hpair hfuture

end D5.S1.Words.Patterns.CyclicStackPreimages
