/- GID: D5/S0/Computability/PhysicalDivider/SubtractLoops
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed subtraction and restoration loops of the Boolean divider. -/

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

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:567-592.
theorem div_subtract_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) (hlen : remainder.length = divisor.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divSubCfg selected borrow none none dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse)) =
      some (divSubCfg selected (subBorrowOut remainder divisor borrow) none none dividend
        [] [] quotient (divisor.reverse ++ divisorBackup)
        (remainder.reverse ++ remainderBackup)
        ((subBits remainder divisor borrow).reverse ++ differenceReverse)) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:542.
  have div_step_subtract_cons (selected borrow x y : Bool)
      (dividend divisor remainder quotient divisorBackup remainderBackup
        differenceReverse : List Bool) :
      divMachine.step (divSubCfg selected borrow none none dividend (y :: divisor)
          (x :: remainder) quotient divisorBackup remainderBackup differenceReverse) =
        some (divSubCfg selected (fullSubtractor x y borrow).2 none none dividend divisor
          remainder quotient (y :: divisorBackup) (x :: remainderBackup)
          ((fullSubtractor x y borrow).1 :: differenceReverse)) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divSubCfg, divCfg, divStacks, DivControl.diffBit,
      DivControl.subAdvance, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction remainder generalizing divisor borrow divisorBackup remainderBackup
      differenceReverse with
  | nil =>
      cases divisor with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x remainder ih =>
      cases divisor with
      | nil => simp at hlen
      | cons y divisor =>
          simp at hlen
          rw [List.length_cons, Function.iterate_succ_apply]
          simp only [Option.bind_some, div_step_subtract_cons]
          rw [ih (borrow := (fullSubtractor x y borrow).2)
            (divisor := divisor) (hlen := hlen)]
          simp [subBorrowOut, subBits, List.reverse_cons, List.append_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:619-634.
theorem div_restoreDivisor_iterate (selected borrow : Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse :
      List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[divisorBackup.length])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse [])) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend
        (divisorBackup.reverse ++ divisor) [] quotient [] remainderBackup
        differenceReverse []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:594.
  have div_step_restoreDivisor_cons (selected borrow y : Bool)
      (dividend divisor quotient divisorBackup remainderBackup differenceReverse :
        List Bool) :
      divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
          quotient (y :: divisorBackup) remainderBackup differenceReverse []) =
        some (divPhaseCfg .restoreDivisor selected borrow dividend (y :: divisor) []
          quotient divisorBackup remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction divisorBackup generalizing divisor with
  | nil => rfl
  | cons y divisorBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreDivisor_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:676-687.
theorem div_discardDifference_iterate (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:652.
  have div_step_discardDifference_cons (selected x : Bool)
      (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
          quotient [] remainderBackup (x :: differenceReverse) []) =
        some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
          remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction differenceReverse with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_discardDifference_cons, ih]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:713-726.
theorem div_restoreRemainder_iterate (selected : Bool)
    (dividend divisor remainder quotient remainderBackup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor remainder
        quotient [] remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor
        (remainderBackup.reverse ++ remainder) quotient [] [] [] []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:689.
  have div_step_restoreRemainder_cons (selected x : Bool)
      (dividend divisor remainder quotient remainderBackup : List Bool) :
      divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
          remainder quotient [] (x :: remainderBackup) [] []) =
        some (divPhaseCfg .restoreRemainder selected true dividend divisor
          (x :: remainder) quotient [] remainderBackup [] []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction remainderBackup generalizing remainder with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreRemainder_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:752-763.
theorem div_discardOldRemainder_iterate (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:728.
  have div_step_discardOldRemainder_cons (selected x : Bool)
      (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
          quotient [] (x :: remainderBackup) differenceReverse []) =
        some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
          remainderBackup differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction remainderBackup with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_discardOldRemainder_cons, ih]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:789-802.
theorem div_restoreDifference_iterate (selected : Bool)
    (dividend divisor remainder quotient differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor remainder
        quotient [] [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor
        (differenceReverse.reverse ++ remainder) quotient [] [] [] []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:765.
  have div_step_restoreDifference_cons (selected x : Bool)
      (dividend divisor remainder quotient differenceReverse : List Bool) :
      divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
          remainder quotient [] [] (x :: differenceReverse) []) =
        some (divPhaseCfg .restoreDifference selected false dividend divisor
          (x :: remainder) quotient [] [] differenceReverse []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction differenceReverse generalizing remainder with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreDifference_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

end Lax51Proofs.RamToTM
