/- GID: D5/S0/Computability/PhysicalDivider/Shift
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed fixed-width remainder shift for a restoring-division round. -/

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

import D5.S0.Computability.PhysicalDivider.Machine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:385-400.
theorem div_shiftFirst_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftFirst selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse
        (remainder.reverse ++ shiftTemp)) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:358.
  have div_step_shiftFirst_cons (selected borrow x : Bool)
      (dividend divisor remainder quotient divisorBackup remainderBackup
        differenceReverse shiftTemp : List Bool) :
      divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor
          (x :: remainder) quotient divisorBackup remainderBackup differenceReverse
          shiftTemp) =
        some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
          divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction remainder generalizing shiftTemp with
  | nil => rfl
  | cons x remainder ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_shiftFirst_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:441-456.
theorem div_shiftSecond_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[shiftTemp.length])
      (some (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor
        (shiftTemp.reverse ++ remainder) quotient divisorBackup remainderBackup
        differenceReverse []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:415.
  have div_step_shiftSecond_cons (selected borrow x : Bool)
      (dividend divisor remainder quotient divisorBackup remainderBackup
        differenceReverse shiftTemp : List Bool) :
      divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
          quotient divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) =
        some (divPhaseCfg .shiftSecond selected borrow dividend divisor (x :: remainder)
          quotient divisorBackup remainderBackup differenceReverse shiftTemp) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction shiftTemp generalizing remainder with
  | nil => rfl
  | cons x shiftTemp ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_shiftSecond_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:470-540.
theorem div_shift_pipeline (b x : Bool)
    (dividend divisor remainder quotient : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * (x :: remainder).length + 4])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (shiftInBit b (x :: remainder)) quotient [] [] [] []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:346.
  have div_step_outer_cons (b : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step
          (divCleanCfg .outer true (b :: dividend) divisor remainder quotient []) =
        some (divPhaseCfg .shiftFirst b false dividend divisor remainder quotient
          [] [] [] []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divCleanCfg, divPhaseCfg, divCfg, divStacks,
      Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:372.
  have div_step_shiftFirst_nil (selected borrow : Bool)
      (dividend divisor quotient divisorBackup remainderBackup differenceReverse
        shiftTemp : List Bool) :
      divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor []
          quotient divisorBackup remainderBackup differenceReverse shiftTemp) =
        some (divPhaseCfg .shiftDiscard selected borrow dividend divisor [] quotient
          divisorBackup remainderBackup differenceReverse shiftTemp) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:402.
  have div_step_shiftDiscard_cons (selected borrow x : Bool)
      (dividend divisor quotient divisorBackup remainderBackup differenceReverse
        shiftTemp : List Bool) :
      divMachine.step (divPhaseCfg .shiftDiscard selected borrow dividend divisor []
          quotient divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) =
        some (divPhaseCfg .shiftSecond selected borrow dividend divisor [] quotient
          divisorBackup remainderBackup differenceReverse shiftTemp) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divPhaseCfg, divCfg, divStacks, DivControl.clearHeld,
      Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:428.
  have div_step_shiftSecond_nil (selected borrow : Bool)
      (dividend divisor remainder quotient divisorBackup remainderBackup
        differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
          quotient divisorBackup remainderBackup differenceReverse []) =
        some (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder quotient
          divisorBackup remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:458.
  have div_step_shiftPrepend (selected borrow : Bool)
      (dividend divisor remainder quotient divisorBackup remainderBackup
        differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder
          quotient divisorBackup remainderBackup differenceReverse []) =
        some (divPhaseCfg .subtract selected false dividend divisor (selected :: remainder)
          quotient divisorBackup remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divPhaseCfg, divCfg, divStacks, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have houter : (stepO^[1])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divPhaseCfg .shiftFirst b false dividend divisor (x :: remainder)
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_outer_cons b dividend divisor (x :: remainder) quotient
  have hfirst := div_shiftFirst_iterate b false dividend divisor (x :: remainder)
    quotient [] [] [] []
  simp only [List.append_nil] at hfirst
  have hfirst0 : (stepO^[1])
      (some (divPhaseCfg .shiftFirst b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse)) =
      some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse) := by
    simpa [stepO] using div_step_shiftFirst_nil b false dividend divisor quotient
      [] [] [] (x :: remainder).reverse
  have hdiscard : (stepO^[1])
      (some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse)) =
      some (divPhaseCfg .shiftSecond b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse.tail) := by
    cases hrev : (x :: remainder).reverse with
    | nil => simp at hrev
    | cons y ys =>
        simpa [stepO, hrev] using
          div_step_shiftDiscard_cons b false y dividend divisor quotient [] [] [] ys
  have hsecond := div_shiftSecond_iterate b false dividend divisor [] quotient [] [] []
    (x :: remainder).reverse.tail
  simp only [List.append_nil] at hsecond
  have hsecond0 : (stepO^[1])
      (some (divPhaseCfg .shiftSecond b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] []) := by
    simpa [stepO] using div_step_shiftSecond_nil b false dividend divisor
      ((x :: remainder).reverse.tail.reverse) quotient [] [] []
  have hprepend : (stepO^[1])
      (some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (b :: (x :: remainder).reverse.tail.reverse) quotient [] [] [] []) := by
    simpa [stepO] using div_step_shiftPrepend b false dividend divisor
      ((x :: remainder).reverse.tail.reverse) quotient [] [] []
  have h := chain (chain (chain (chain (chain (chain houter hfirst) hfirst0)
    hdiscard) hsecond) hsecond0) hprepend
  have htime :
      1 + (1 + ((x :: remainder).reverse.tail.length +
        (1 + (1 + ((x :: remainder).length + 1))))) =
        2 * (x :: remainder).length + 4 := by
    simp
    omega
  rw [htime] at h
  have hout : (x :: remainder).reverse.tail.reverse =
      (x :: remainder).take remainder.length := by
    rw [List.tail_reverse, List.reverse_reverse, List.dropLast_eq_take]
    simp
  rw [hout] at h
  simpa [stepO, shiftInBit] using h

end Lax51Proofs.RamToTM
