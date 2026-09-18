/- GID: D5/S0/Computability/PhysicalDivider/CallProgram
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed preparation, divider statements, copy-out, erasure and return on fourteen bit tapes. -/

import D5.S0.Computability.PhysicalDivider.FiniteControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.PhysicalDivider

open Turing Lax51Proofs.RamToTM

/-- Every administrative edge, including return signalling, executes a counted read. -/
def frameInstruction (label : FrameLabel) (held : Option Bool) : Instruction :=
  match label with
  | .seekA => startBlock (.inr .operandA) (.seekFirst)
      (.frame .seekD held false)
  | .seekD => startBlock (.inr .operandD) (.seekFirst)
      (.frame .seekCapacity held false)
  | .seekCapacity => startBlock (.inr .capacity) (.seekFirst)
      (.frame .seekQ held false)
  | .seekQ => startBlock (.inr .quotientOut) (.seekFirst)
      (.frame .seekR held false)
  | .clearQ => startBlock (.inr .quotientOut) (.popMarker)
      (.frame .clearQRead held true)
  | .seekR => startBlock (.inr .remainderOut) (.seekFirst)
      (.frame .clearQ held false)
  | .clearR => startBlock (.inr .remainderOut) (.popMarker)
      (.frame .clearRRead held true)
  | .loadA => startBlock (.inr .operandA) (.popMarker)
      (.frame .loadARead held true)
  | .loadAPush => startBlock (.inl .dividend) (.pushFirst (held.getD false))
      (.frame .loadABackup held false)
  | .loadABackup => startBlock (.inr .capacityBackup) (.pushFirst (held.getD false))
      (.frame .loadA held false)
  | .restoreA => startBlock (.inr .capacityBackup) (.popMarker)
      (.frame .restoreARead held true)
  | .restoreAPush => startBlock (.inr .operandA) (.pushFirst (held.getD false))
      (.frame .restoreA held false)
  | .padD => startBlock (.inl .divisor) (.pushFirst false)
      (.frame .loadD held false)
  | .loadD => startBlock (.inr .operandD) (.popMarker)
      (.frame .loadDRead held true)
  | .loadDPush => startBlock (.inl .shiftTemp) (.pushFirst (held.getD false))
      (.frame .loadD held false)
  | .restoreD => startBlock (.inl .shiftTemp) (.popMarker)
      (.frame .restoreDRead held true)
  | .restoreDPush => startBlock (.inl .divisor) (.pushFirst (held.getD false))
      (.frame .restoreDCopy held false)
  | .restoreDCopy => startBlock (.inr .operandD) (.pushFirst (held.getD false))
      (.frame .restoreD held false)
  | .padR => startBlock (.inl .remainder) (.pushFirst false)
      (.frame .loadCapacity held false)
  | .loadCapacity => startBlock (.inr .capacity) (.popMarker)
      (.frame .loadCapacityRead held true)
  | .loadCapacityPush => startBlock (.inr .capacityBackup) (.pushFirst (held.getD false))
      (.frame .loadCapacityZero held false)
  | .loadCapacityZero => startBlock (.inl .remainder) (.pushFirst false)
      (.frame .loadCapacity held false)
  | .restoreCapacity => startBlock (.inr .capacityBackup) (.popMarker)
      (.frame .restoreCapacityRead held true)
  | .restoreCapacityPush => startBlock (.inr .capacity) (.pushFirst (held.getD false))
      (.frame .restoreCapacity held false)
  | .copyQ => startBlock (.inl .quotient) (.popMarker)
      (.frame .copyQRead held true)
  | .copyQReverse => startBlock (.inl .shiftTemp) (.pushFirst (held.getD false))
      (.frame .copyQ held false)
  | .emitQ => startBlock (.inl .shiftTemp) (.popMarker)
      (.frame .emitQRead held true)
  | .emitQPush => startBlock (.inr .quotientOut) (.pushFirst (held.getD false))
      (.frame .emitQ held false)
  | .copyR => startBlock (.inl .remainder) (.popMarker)
      (.frame .copyRRead held true)
  | .copyRReverse => startBlock (.inl .shiftTemp) (.pushFirst (held.getD false))
      (.frame .copyR held false)
  | .emitR => startBlock (.inl .shiftTemp) (.popMarker)
      (.frame .emitRRead held true)
  | .emitRPush => startBlock (.inr .remainderOut) (.pushFirst (held.getD false))
      (.frame .emitR held false)
  | .clearDivisor => startBlock (.inl .divisor) (.popMarker)
      (.frame .clearDivisorRead held true)
  | .parkDividend => startBlock (.inl .dividend) (.parkMarker)
      (.frame .parkDivisor held false)
  | .parkDivisor => startBlock (.inl .divisor) (.parkMarker)
      (.frame .parkRemainder held false)
  | .parkRemainder => startBlock (.inl .remainder) (.parkMarker)
      (.frame .parkQuotient held false)
  | .parkQuotient => startBlock (.inl .quotient) (.parkMarker)
      (.frame .parkDivisorBackup held false)
  | .parkDivisorBackup => startBlock (.inl .divisorBackup) (.parkMarker)
      (.frame .parkRemainderBackup held false)
  | .parkRemainderBackup => startBlock (.inl .remainderBackup) (.parkMarker)
      (.frame .parkDifference held false)
  | .parkDifference => startBlock (.inl .differenceReverse) (.parkMarker)
      (.frame .parkShift held false)
  | .parkShift => startBlock (.inl .shiftTemp) (.parkMarker)
      (.frame .parkA held false)
  | .parkA => startBlock (.inr .operandA) (.parkMarker)
      (.frame .parkD held false)
  | .parkD => startBlock (.inr .operandD) (.parkMarker)
      (.frame .parkCapacity held false)
  | .parkCapacity => startBlock (.inr .capacity) (.parkMarker)
      (.frame .parkCapacityBackup held false)
  | .parkCapacityBackup => startBlock (.inr .capacityBackup) (.parkMarker)
      (.frame .parkQ held false)
  | .parkQ => startBlock (.inr .quotientOut) (.parkMarker)
      (.frame .parkR held false)
  | .parkR => startBlock (.inr .remainderOut) (.parkMarker)
      (.frame .signalReturn held false)
  | .clearQRead => controlRead (.frame (if held.isNone then .clearR else .clearQ) held)
  | .clearRRead => controlRead (.frame (if held.isNone then .loadA else .clearR) held)
  | .loadARead => controlRead (.frame (if held.isNone then .restoreA else .loadAPush) held)
  | .restoreARead => controlRead (.frame (if held.isNone then .padD else .restoreAPush) held)
  | .loadDRead => controlRead (.frame (if held.isNone then .restoreD else .loadDPush) held)
  | .restoreDRead => controlRead (.frame (if held.isNone then .padR else .restoreDPush) held)
  | .loadCapacityRead => controlRead (.frame (if held.isNone then .restoreCapacity else .loadCapacityPush) held)
  | .restoreCapacityRead => controlRead (.frame (if held.isNone then .enterSource else .restoreCapacityPush) held)
  | .copyQRead => controlRead (.frame (if held.isNone then .emitQ else .copyQReverse) held)
  | .emitQRead => controlRead (.frame (if held.isNone then .copyR else .emitQPush) held)
  | .copyRRead => controlRead (.frame (if held.isNone then .emitR else .copyRReverse) held)
  | .emitRRead => controlRead (.frame (if held.isNone then .clearDivisor else .emitRPush) held)
  | .clearDivisorRead => controlRead (.frame (if held.isNone then .parkDividend else .clearDivisor) held)
  | .enterSource => controlRead (.sourceLabel .inspectDivisor default)
  | .signalReturn => controlRead .returned

/-- Interpret only substatements in the finite closure of the selected divider. -/
def sourceInstruction (parent : SourceNode) (state : DivControl) : Instruction :=
  match h : parent.val with
  | .push k f _ => startBlock (.inl k) (.pushFirst (f state)) (.sourcePush parent state)
  | .pop k _ _ => startBlock (.inl k) .popMarker (.sourceRead parent state)
  | .peek k _ _ => startBlock (.inl k) .peekMarker (.sourceRead parent state)
  | .load f child => controlRead (.sourceStmt (sourceChild parent child (by
      classical
      rw [h]
      exact Finset.mem_insert_of_mem TM2.stmts₁_self)) (f state))
  | .branch f left right =>
      if f state then
        controlRead (.sourceStmt (sourceChild parent left (by
          classical
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))) state)
      else
        controlRead (.sourceStmt (sourceChild parent right (by
          classical
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))) state)
  | .goto f => controlRead (.sourceLabel (f state) state)
  | .halt => controlRead (.frame .copyQ none)

/-- Source `.done` is an internal boundary, followed by actual output and cleanup work. -/
def instruction : Control → Option Instruction
  | .frame label held => some (frameInstruction label held)
  | .sourceLabel .done _ => some (controlRead (.frame .copyQ none))
  | .sourceLabel label state => some (controlRead (.sourceStmt (sourceEntry label) state))
  | .sourceStmt node state => some (sourceInstruction node state)
  | .block tape (.finished result) next => some (controlRead (continueBlock next result))
  | .block tape pc next => (blockAction pc).map (liftBlockAction tape next)
  | .returned => none

/-- No coordinate, width, operand integer or high-water mark is available to this function. -/
def executeInstruction (tapes : ActiveTape → Tape Bool) : Instruction → PhysicalCfg
  | .read k next => ⟨next (tapes k).head, tapes⟩
  | .write k b next => ⟨next, Function.update tapes k ((tapes k).write b)⟩
  | .move k d next => ⟨next, Function.update tapes k ((tapes k).move d)⟩

def physicalStep (c : PhysicalCfg) : Option PhysicalCfg :=
  (instruction c.control).map (executeInstruction c.tapes)

/-- All initial data, including the old output, is represented at fixed spatial origins. -/
def entryTapes (a d capacity oldQ oldR : List Bool) : ActiveTape → Tape Bool
  | .inl _ => stackAtOrigin []
  | .inr .operandA => stackAtOrigin a
  | .inr .operandD => stackAtOrigin d
  | .inr .capacity => stackAtOrigin capacity
  | .inr .capacityBackup => stackAtOrigin []
  | .inr .quotientOut => stackAtOrigin oldQ
  | .inr .remainderOut => stackAtOrigin oldR

/-- A call starts at a finite control boundary, with no implicit preparation operation. -/
def callEntry (a d capacity oldQ oldR : List Bool) : PhysicalCfg :=
  ⟨.frame .seekA none, entryTapes a d capacity oldQ oldR⟩

/-- Re-entering the control boundary costs a read and does not alter any tape or head. -/
def callAgain (c : PhysicalCfg) : Option PhysicalCfg :=
  match c.control with
  | .returned => some (executeInstruction c.tapes (controlRead (.frame .seekA none)))
  | _ => none

end D5.S0.Computability.PhysicalDivider
