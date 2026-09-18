/- GID: D5/S0/Computability/PhysicalDivider/Finalize
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both borrow branches restore a clean divider round boundary. -/

/-
Source: szymtor/RAM-TM, commit 6fe5a3d94f6c2da46cc2c5ab98cd36997b130737.
Authors: Szymon Toruńczyk and Codex 5.6 (upstream manifest).
Apache-2.0; full license, source mapping and retirement condition:
Library/Computability/ramtm2026divider.md.
Original declaration names and proof derivations are retained. Import routing,
definitional unfolding and local inlining adapt the source to the current pin.
These symbolic program and word laws contain no certified finite instance,
bounded enumeration, certificate checker or conditional numerical reduction.
-/

import D5.S0.Computability.PhysicalDivider.SubtractLoops

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:815-868.
theorem div_finalize_true (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool)
    (hlen : differenceReverse.length = remainderBackup.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false :: quotient) []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:636.
  have div_step_choose_true (selected : Bool)
      (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .choose selected true dividend divisor [] quotient []
          remainderBackup differenceReverse []) =
        some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
          remainderBackup differenceReverse []) := by
    rfl
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:664.
  have div_step_discardDifference_nil (selected : Bool)
      (dividend divisor quotient remainderBackup : List Bool) :
      divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
          quotient [] remainderBackup [] []) =
        some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
          remainderBackup [] []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:701.
  have div_step_restoreRemainder_nil (selected : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
          remainder quotient [] [] [] []) =
        some (divPhaseCfg .emit selected true dividend divisor remainder quotient
          [] [] [] []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:804.
  have div_step_emit (selected borrow : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divPhaseCfg .emit selected borrow dividend divisor remainder quotient
          [] [] [] []) =
        some (divCleanCfg .outer true dividend divisor remainder
          ((!borrow) :: quotient) []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divPhaseCfg, divCleanCfg, divCfg, divStacks, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hc : (stepO^[1])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
    simpa [stepO] using div_step_choose_true selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd := div_discardDifference_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0 : (stepO^[1])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
        remainderBackup [] []) := by
    simpa [stepO] using div_step_discardDifference_nil selected dividend divisor quotient
      remainderBackup
  have hr := div_restoreRemainder_iterate selected dividend divisor [] quotient
    remainderBackup
  simp only [List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainderBackup.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_restoreRemainder_nil selected dividend divisor
      remainderBackup.reverse quotient
  have he : (stepO^[1])
      (some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false :: quotient) []) := by
    simpa [stepO] using div_step_emit selected true dividend divisor
      remainderBackup.reverse quotient
  have h := chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime :
      1 + (1 + (remainderBackup.length +
        (1 + (differenceReverse.length + 1)))) =
        2 * remainderBackup.length + 4 := by omega
  rw [htime] at h
  simpa [stepO] using h

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:870-923.
theorem div_finalize_false (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool)
    (hlen : remainderBackup.length = differenceReverse.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true :: quotient) []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:644.
  have div_step_choose_false (selected : Bool)
      (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .choose selected false dividend divisor [] quotient []
          remainderBackup differenceReverse []) =
        some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
          remainderBackup differenceReverse []) := by
    rfl
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:740.
  have div_step_discardOldRemainder_nil (selected : Bool)
      (dividend divisor quotient differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
          quotient [] [] differenceReverse []) =
        some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
          [] differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:777.
  have div_step_restoreDifference_nil (selected : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
          remainder quotient [] [] [] []) =
        some (divPhaseCfg .emit selected false dividend divisor remainder quotient
          [] [] [] []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:804.
  have div_step_emit (selected borrow : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divPhaseCfg .emit selected borrow dividend divisor remainder quotient
          [] [] [] []) =
        some (divCleanCfg .outer true dividend divisor remainder
          ((!borrow) :: quotient) []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divPhaseCfg, divCleanCfg, divCfg, divStacks, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hc : (stepO^[1])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
    simpa [stepO] using div_step_choose_false selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd := div_discardOldRemainder_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0 : (stepO^[1])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
        [] differenceReverse []) := by
    simpa [stepO] using div_step_discardOldRemainder_nil selected dividend divisor quotient
      differenceReverse
  have hr := div_restoreDifference_iterate selected dividend divisor [] quotient
    differenceReverse
  simp only [List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor
        differenceReverse.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_restoreDifference_nil selected dividend divisor
      differenceReverse.reverse quotient
  have he : (stepO^[1])
      (some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true :: quotient) []) := by
    simpa [stepO] using div_step_emit selected false dividend divisor
      differenceReverse.reverse quotient
  have h := chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime :
      1 + (1 + (differenceReverse.length +
        (1 + (remainderBackup.length + 1)))) =
        2 * remainderBackup.length + 4 := by omega
  rw [htime] at h
  simpa [stepO] using h

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:925-990.
theorem div_subtract_pipeline (selected : Bool)
    (dividend divisor candidate quotient : List Bool)
    (hlen : candidate.length = divisor.length) :
    let borrow := subBorrowOut candidate divisor false
    let nextRemainder := if borrow then candidate else subBits candidate divisor false
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      4 * candidate.length + 6])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow) :: quotient) []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:556.
  have div_step_subtract_nil (selected borrow : Bool)
      (dividend quotient divisorBackup remainderBackup differenceReverse : List Bool) :
      divMachine.step (divSubCfg selected borrow none none dividend [] [] quotient
          divisorBackup remainderBackup differenceReverse) =
        some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
          divisorBackup remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divSubCfg, divPhaseCfg, divCfg, divStacks]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:607.
  have div_step_restoreDivisor_nil (selected borrow : Bool)
      (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
          quotient [] remainderBackup differenceReverse []) =
        some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
          remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let borrow := subBorrowOut candidate divisor false
  let difference := subBits candidate divisor false
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hs := div_subtract_iterate selected false dividend divisor candidate quotient
    [] [] [] hlen
  change (stepO^[candidate.length])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] [])) = _ at hs
  simp only [List.append_nil] at hs
  change _ = some (divSubCfg selected borrow none none dividend [] [] quotient
    divisor.reverse candidate.reverse difference.reverse) at hs
  have hs0 : (stepO^[1])
      (some (divSubCfg selected borrow none none dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse)) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse []) := by
    simpa [stepO] using div_step_subtract_nil selected borrow dividend quotient
      divisor.reverse candidate.reverse difference.reverse
  have hr := div_restoreDivisor_iterate selected borrow dividend [] quotient
    divisor.reverse candidate.reverse difference.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        [] candidate.reverse difference.reverse [])) =
      some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse []) := by
    simpa [stepO] using div_step_restoreDivisor_nil selected borrow dividend divisor
      quotient candidate.reverse difference.reverse
  have hp : (stepO^[2 * candidate.length + 4])
      (some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse [])) =
      some (divCleanCfg .outer true dividend divisor
        (if borrow then candidate else difference) ((!borrow) :: quotient) []) := by
    cases hb : borrow with
    | false =>
        have hdlen : candidate.reverse.length = difference.reverse.length := by
          simp [difference, subBits_length_of_eq false hlen]
        simpa only [hb, List.length_reverse, List.reverse_reverse, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using div_finalize_false selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
    | true =>
        have hdlen : difference.reverse.length = candidate.reverse.length := by
          simp [difference, subBits_length_of_eq false hlen]
        simpa only [hb, List.length_reverse, List.reverse_reverse, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using div_finalize_true selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
  have h := chain (chain (chain (chain hs hs0) hr) hr0) hp
  have htime :
      2 * candidate.length + 4 +
        (1 + (divisor.length + (1 + candidate.length))) =
        4 * candidate.length + 6 := by omega
  rw [htime] at h
  simpa [stepO, borrow, difference] using h

end Lax51Proofs.RamToTM
