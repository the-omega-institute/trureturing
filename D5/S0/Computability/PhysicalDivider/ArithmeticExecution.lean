/- GID: D5/S0/Computability/PhysicalDivider/ArithmeticExecution
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Linear physical extent throughout the exact positive-divider arithmetic segment. -/

import D5.S0.Computability.PhysicalDivider.SourceRun
import D5.S0.Computability.PhysicalDivider.Positive
import D5.S0.Computability.PhysicalDivider.StackGrowth
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- Growth is charged within one clean round, whose source duration is linear in width. -/
def arithmeticStackBound (w : ℕ) : ℕ :=
  (w + 1) + (6 * (w + 1) + 10) *
    @programPushBound DivStack DivLabel DivControl (fun _ => Bool) _ divMachine.m

/-- The exact positive arithmetic segment reaches its internal done boundary.
The same linear interval contains the support and head at every physical prefix;
preparation and the subsequent return program are separate segments. -/
theorem positive_physical_arithmetic (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (frame : FrameTape → Tape Bool) (frameHeads : FrameTape → ℤ)
    (hframe : ∀ k, 0 ≤ frameHeads k ∧ frameHeads k ≤ 2 * arithmeticStackBound w)
    (hwithin : LocatedWithin (locatedSourceCfg
      (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
        frame frameHeads)
      (fun _ => -(sourceStepBudget : ℤ))
      (fun _ => 2 * arithmeticStackBound w + sourceStepBudget)) :
    ∃ m ≤ sourceStepBudget * divPositiveRunTime w,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[m])
        (some (locatedSourceCfg
          (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
          frame frameHeads)) =
        some (locatedSourceCfg
          (divDoneCfg true (fixedBits (w + 1) d) (fixedBits (w + 1) (a % d))
            (fixedBits w (a / d))) frame frameHeads) ∧
      ∀ j ≤ m, ∃ c,
        ((fun o : Option LocatedCfg => o.bind locatedStep)^[j])
          (some (locatedSourceCfg
            (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
              (fixedBits (w + 1) 0)) frame frameHeads)) = some c ∧
        LocatedWithin c (fun _ => -(sourceStepBudget : ℤ))
          (fun _ => 2 * arithmeticStackBound w + sourceStepBudget) := by
  let src := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let W := w + 1
  let R := 6 * W + 10
  let P := @programPushBound DivStack DivLabel DivControl (fun _ => Bool) _ divMachine.m
  have grow (c c' : divMachine.Cfg) (i : ℕ) (hi : i ≤ R)
      (hc : ∀ k, (c.stk k).length ≤ W) (hrun : (src^[i]) (some c) = some c') :
      ∀ k, (c'.stk k).length ≤ arithmeticStackBound w := by
    intro k
    have hg := @iterate_stack_length_le DivStack DivLabel DivControl (fun _ => Bool)
      _ _ _ divMachine.m i c c' hrun k
    have hmul := Nat.mul_le_mul_right P hi
    have hinit := hc k
    change (c'.stk k).length ≤ W + R * P
    change (c'.stk k).length ≤ (c.stk k).length + i * P at hg
    omega
  have rounds (bits : List Bool) (s : DivisionScan)
      (hr : s.remainder < d) (hlen : bits.length + s.quotient.length ≤ w) :
      ∀ i ≤ bits.length * R, ∀ c,
        (src^[i]) (some (divCleanCfg .outer true bits (fixedBits W d)
          (fixedBits W s.remainder) s.quotient [])) = some c →
        ∀ k, (c.stk k).length ≤ arithmeticStackBound w := by
    induction bits generalizing s with
    | nil =>
      intro i hi c hc k
      have : i = 0 := by simpa using hi
      subst i
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hc
      subst c
      have hW : W ≤ arithmeticStackBound w := by dsimp [arithmeticStackBound, W]; omega
      cases k <;> simp [divMachine, fixedBits_length, divCleanCfg, divCfg, divStacks] <;>
        simp only [List.length_nil, Nat.zero_add] at hlen <;> omega
    | cons b bits ih =>
      intro i hi c hc
      have hclean : ∀ k,
          ((divCleanCfg .outer true (b :: bits) (fixedBits W d)
            (fixedBits W s.remainder) s.quotient []).stk k).length ≤ W := by
        intro k
        cases k <;> simp [divMachine, fixedBits_length, divCleanCfg, divCfg, divStacks, W] <;>
          simp only [List.length_cons] at hlen <;> omega
      by_cases hiR : i ≤ R
      · exact grow _ c i hiR hclean hc
      · have hround := div_round_fixed w d s b bits hd hr
        change (src^[R]) _ = _ at hround
        have hrem : (divisionScanStep d s b).remainder < d := by
          have hh := (divisionScan_invariant hd0 [b] s hr).2
          simpa [divisionScan] using hh
        have hlen' : bits.length + (divisionScanStep d s b).quotient.length ≤ w := by
          dsimp [divisionScanStep]
          simp only [List.length_cons] at hlen
          omega
        apply ih (divisionScanStep d s b) hrem hlen' (i - R) (by
          simp only [List.length_cons, Nat.add_mul] at hi; omega) c
        rw [show i = (i - R) + R by omega, Function.iterate_add_apply, hround] at hc
        exact hc
  let dividend := (fixedBits w a).reverse
  let divisor := fixedBits W d
  let remainder := fixedBits W 0
  let first := divInitialCfg dividend divisor remainder
  let outer := divCleanCfg .outer true dividend divisor remainder [] []
  have hfirst : ∀ k, (first.stk k).length ≤ W := by
    intro k
    cases k <;> simp [divMachine, fixedBits_length, first, divInitialCfg, divCfg, divStacks, dividend, divisor, remainder, W]
  have hinspect : (src^[2 * W + 3]) (some first) = some outer := by
    have hdextra : d < 2 ^ W := by dsimp [W]; rw [pow_succ]; omega
    have htrue : containsTrue divisor = true := by
      cases hc : containsTrue divisor with
      | false =>
        have hz := containsTrue_false_bitsValue_zero hc
        have hv : bitsValue divisor = d := by
          simp [divisor, bitsValue_fixedBits, Nat.mod_eq_of_lt hdextra]
        rw [hv] at hz
        omega
      | true => rfl
    have hi := div_inspect_iterate false dividend divisor remainder []
    have hr := div_restore_inspected_iterate true dividend [] remainder [] divisor.reverse
    simp only [Bool.false_or, htrue, List.append_nil] at hi
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
    have hi0 : divMachine.step
        (divCleanCfg .inspectDivisor true dividend [] remainder [] divisor.reverse) =
        some (divCleanCfg .restoreInspectedDivisor true dividend [] remainder [] divisor.reverse) := by
      simp [default, FinTM2.inhabitedσ, instInhabitedDivControl,
        instInhabitedDivControl.default, instInhabitedBool.default,
        divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld]
      all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
    have hr0 : divMachine.step
        (divCleanCfg .restoreInspectedDivisor true dividend divisor remainder [] []) =
        some (divCleanCfg .dispatch true dividend divisor remainder [] []) := by
      simp [default, FinTM2.inhabitedσ, instInhabitedDivControl,
        instInhabitedDivControl.default, instInhabitedBool.default,
        divMachine, divMoveIteration, divCleanCfg, divCfg, divStacks, DivControl.clearHeld]
      all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
    have hdsp : divMachine.step (divCleanCfg .dispatch true dividend divisor remainder [] []) =
        some outer := by rfl
    change (src^[divisor.length]) _ = _ at hi hr
    have hstart : first = divCleanCfg .inspectDivisor false dividend divisor remainder [] [] := by
      rfl
    rw [hstart, show 2 * W + 3 = 1 + (1 + (divisor.length + (1 + divisor.length))) by
      simp [divisor]; omega]
    rw [Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_add_apply, hi]
    change src (some _) = _ at hi0 hr0 hdsp
    rw [Function.iterate_one, hi0, hr, hr0, hdsp]
  have hall : ∀ i ≤ divPositiveRunTime w, ∀ c, (src^[i]) (some first) = some c →
      ∀ k, (c.stk k).length ≤ arithmeticStackBound w := by
    intro i hi c hc
    by_cases hiscan : i ≤ 2 * W + 3
    · exact grow first c i (by dsimp [R]; omega) hfirst hc
    · rw [show i = (i - (2 * W + 3)) + (2 * W + 3) by omega,
        Function.iterate_add_apply, hinspect] at hc
      by_cases hirounds : i - (2 * W + 3) ≤ dividend.length * R
      · exact rounds dividend ⟨[], 0⟩ hd0 (by simp [dividend])
          (i - (2 * W + 3)) hirounds c hc
      · have hlast : i = divPositiveRunTime w := by
          dsimp [divPositiveRunTime, W, R] at hi ⊢
          simp only [dividend, List.length_reverse, fixedBits_length] at hirounds
          dsimp [W, R] at hiscan hirounds
          omega
        subst i
        have hfull := divMachine_positive_correct w a d ha hd0 hd
        change (src^[divPositiveRunTime w]) (some first) = _ at hfull
        rw [show divPositiveRunTime w =
            (divPositiveRunTime w - (2 * W + 3)) + (2 * W + 3) by
              dsimp [divPositiveRunTime, W]; omega,
          Function.iterate_add_apply, hinspect] at hfull
        rw [hfull] at hc
        cases hc
        intro k
        have hW : W ≤ arithmeticStackBound w := by dsimp [arithmeticStackBound, W]; omega
        cases k <;> simp [divMachine, fixedBits_length, divDoneCfg, divCfg, divStacks, W] <;> omega
  exact source_run_refinement (divPositiveRunTime w) _ _
    (divMachine_positive_correct w a d ha hd0 hd) (arithmeticStackBound w)
    hall frame frameHeads hframe hwithin

end D5.S0.Computability.PhysicalDivider
