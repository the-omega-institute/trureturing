/- GID: D5/S0/Computability/PhysicalDivider/Machine
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed eight-stack Boolean restoring-divider program. -/

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

import D5.S0.Computability.PhysicalDivider.WordArithmetic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:14-21.
structure DivControl where
  held : Option Bool
  selected : Bool
  left : Option Bool
  right : Option Bool
  borrow : Bool
  divisorNonzero : Bool
  deriving DecidableEq, Fintype, Inhabited

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:23-23.
def DivControl.clearHeld (s : DivControl) : DivControl := { s with held := none }

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:25-26.
def DivControl.diffBit (s : DivControl) : Bool :=
  (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).1

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:28-31.
def DivControl.subAdvance (s : DivControl) : DivControl :=
  { s with
    borrow := (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).2,
    left := none, right := none }

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:33-36.
inductive DivStack
  | dividend | divisor | remainder | quotient
  | divisorBackup | remainderBackup | differenceReverse | shiftTemp
  deriving DecidableEq, Fintype, Inhabited

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:38-46.
inductive DivLabel
  | inspectDivisor | restoreInspectedDivisor | dispatch
  | zeroLoop | outer
  | shiftFirst | shiftDiscard | shiftSecond | shiftPrepend
  | subtract | restoreDivisor | choose
  | discardDifference | restoreRemainder
  | discardOldRemainder | restoreDifference | emit
  | done
  deriving DecidableEq, Fintype, Inhabited

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:48-54.
def divMoveIteration (source target : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.push target (fun s => s.held.getD false) <|
        .load DivControl.clearHeld <| .goto fun _ => loop)

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:56-61.
def divDiscardIteration (source : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.load DivControl.clearHeld <| .goto fun _ => loop)

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:63-135.
def divMachine : Turing.FinTM2 where
  K := DivStack
  k₀ := .dividend
  k₁ := .quotient
  Γ _ := Bool
  Λ := DivLabel
  main := .inspectDivisor
  σ := DivControl
  initialState := default
  m
    | .inspectDivisor =>
        .pop .divisor (fun s a =>
          { s with
            held := a,
            divisorNonzero := s.divisorNonzero || a.getD false }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .restoreInspectedDivisor)
            (.push .divisorBackup (fun s => s.held.getD false) <|
              .load DivControl.clearHeld <| .goto fun _ => .inspectDivisor)
    | .restoreInspectedDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreInspectedDivisor .dispatch
    | .dispatch => .branch DivControl.divisorNonzero
        (.goto fun _ => .outer) (.goto fun _ => .zeroLoop)
    | .zeroLoop =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.push .quotient (fun _ => false) <|
              .load DivControl.clearHeld <| .goto fun _ => .zeroLoop)
    | .outer =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.load (fun s => { s with selected := s.held.getD false, held := none }) <|
              .goto fun _ => .shiftFirst)
    | .shiftFirst => divMoveIteration .remainder .shiftTemp .shiftFirst .shiftDiscard
    | .shiftDiscard =>
        .pop .shiftTemp (fun s _ => DivControl.clearHeld s) <|
          .goto fun _ => .shiftSecond
    | .shiftSecond => divMoveIteration .shiftTemp .remainder .shiftSecond .shiftPrepend
    | .shiftPrepend =>
        .push .remainder DivControl.selected <|
          .load (fun s => { s with borrow := false, left := none, right := none }) <|
            .goto fun _ => .subtract
    | .subtract =>
        .pop .remainder (fun s a => { s with left := a }) <|
          .branch (fun s => s.left.isNone)
            (.goto fun _ => .restoreDivisor)
            (.pop .divisor (fun s b => { s with right := b }) <|
              .push .remainderBackup (fun s => s.left.getD false) <|
                .push .divisorBackup (fun s => s.right.getD false) <|
                  .push .differenceReverse DivControl.diffBit <|
                    .load DivControl.subAdvance <| .goto fun _ => .subtract)
    | .restoreDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreDivisor .choose
    | .choose => .branch DivControl.borrow
        (.goto fun _ => .discardDifference) (.goto fun _ => .discardOldRemainder)
    | .discardDifference =>
        divDiscardIteration .differenceReverse .discardDifference .restoreRemainder
    | .restoreRemainder =>
        divMoveIteration .remainderBackup .remainder .restoreRemainder .emit
    | .discardOldRemainder =>
        divDiscardIteration .remainderBackup .discardOldRemainder .restoreDifference
    | .restoreDifference =>
        divMoveIteration .differenceReverse .remainder .restoreDifference .emit
    | .emit =>
        .push .quotient (fun s => !s.borrow) <|
          .load (fun s =>
            { s with
              held := none, selected := false, left := none, right := none,
              borrow := false }) <|
            .goto fun _ => .outer
    | .done => .halt

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:137-146.
def divStacks (dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp : List Bool) : DivStack → List Bool
  | .dividend => dividend
  | .divisor => divisor
  | .remainder => remainder
  | .quotient => quotient
  | .divisorBackup => divisorBackup
  | .remainderBackup => remainderBackup
  | .differenceReverse => differenceReverse
  | .shiftTemp => shiftTemp

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:148-154.
def divCfg (label : DivLabel) (state : DivControl)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) : divMachine.Cfg where
  l := some label
  var := state
  stk := divStacks dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:156-157.
def divInitialCfg (dividend divisor remainder : List Bool) : divMachine.Cfg :=
  divCfg .inspectDivisor default dividend divisor remainder [] [] [] [] []

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:159-163.
def divCleanCfg (label : DivLabel) (divisorNonzero : Bool)
    (dividend divisor remainder quotient divisorBackup : List Bool) :
    divMachine.Cfg :=
  divCfg label { (default : DivControl) with divisorNonzero := divisorNonzero }
    dividend divisor remainder quotient divisorBackup [] [] []

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:165-168.
def divDoneCfg (divisorNonzero : Bool) (divisor remainder quotient : List Bool) :
    divMachine.Cfg :=
  divCfg .done { (default : DivControl) with divisorNonzero := divisorNonzero }
    [] divisor remainder quotient [] [] [] []

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:170-178.
def divPhaseCfg (label : DivLabel) (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) : divMachine.Cfg :=
  divCfg label
    { (default : DivControl) with
      selected := selected, borrow := borrow,
      divisorNonzero := true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:180-188.
def divSubCfg (selected borrow : Bool) (left right : Option Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) : divMachine.Cfg :=
  divCfg .subtract
    { (default : DivControl) with
      selected := selected, borrow := borrow, left := left, right := right,
      divisorNonzero := true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse []

end Lax51Proofs.RamToTM
