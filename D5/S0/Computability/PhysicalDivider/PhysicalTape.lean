/- GID: D5/S0/Computability/PhysicalDivider/PhysicalTape
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Computability.TuringMachine.Tape]
   utility: none
   digest: Elementary bit actions for the concrete divider's two-bit stack blocks. -/

import D5.S0.Computability.PhysicalDivider.Machine
import Mathlib.Computability.TuringMachine.Tape

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.PhysicalDivider

open Turing

/-- The additional tapes used by the framed divider, besides its eight actual stacks. -/
inductive FrameTape
  | operandA | operandD | capacity | capacityBackup | quotientOut | remainderOut
  deriving DecidableEq, Fintype, Inhabited

/-- Each actual source stack has its own tape. -/
abbrev ActiveTape := Sum Lax51Proofs.RamToTM.DivStack FrameTape

/-- A block is blank `00`, bottom `01`, or data `1b`. -/
def cellsBelow : List Bool → List Bool
  | [] => [true, false]
  | b :: bs => b :: true :: cellsBelow bs

/-- Mathematical representation at the top; constructing this value is not a machine action. -/
def stackAtTop : List Bool → Tape Bool
  | [] => Tape.mk₂ [] [false, true]
  | b :: bs => Tape.mk₂ (cellsBelow bs) [true, b]

/-- Representation while parking: higher, already traversed blocks remain on the right. -/
def stackWithAbove : List Bool → List Bool → Tape Bool
  | [], above => Tape.mk₂ [] ([false, true] ++ above)
  | b :: bs, above => Tape.mk₂ (cellsBelow bs) ([true, b] ++ above)

/-- The same origin-anchored word with its head parked on the bottom block. -/
def stackAtOrigin (bs : List Bool) : Tape Bool :=
  Tape.mk₂ [] ([false, true] ++ bs.reverse.flatMap (fun b => [true, b]))

/-- All control states are fixed before the word, operand and capacity are chosen. -/
inductive BlockControl
  | pushFirst (b : Bool) | pushSecond (b : Bool) | pushMarker (b : Bool)
  | pushDataMove (b : Bool) | pushData (b : Bool) | pushBack
  | popMarker | popDataMove | popRead | popEraseData (b : Bool)
  | popMarkerMove (b : Bool) | popEraseMarker (b : Bool)
  | popBackFirst (b : Bool) | popBackSecond (b : Bool)
  | peekMarker | peekDataMove | peekRead | peekBack (b : Bool)
  | seekFirst | seekSecond | seekMarker | seekBackFirst | seekBackSecond
  | parkMarker | parkFirst | parkSecond
  | finished (value : Option Bool)
  deriving DecidableEq, Fintype, Inhabited

/-- Exactly one read, one write, or one unit move; the continuation is finite control. -/
inductive BlockAction
  | read (next : Bool → BlockControl)
  | write (bit : Bool) (next : BlockControl)
  | move (direction : Dir) (next : BlockControl)

/-- The concrete transition table. Pop erases both cells before leaving the old block. -/
def blockAction : BlockControl → Option BlockAction
  | .pushFirst b => some (.move .right (.pushSecond b))
  | .pushSecond b => some (.move .right (.pushMarker b))
  | .pushMarker b => some (.write true (.pushDataMove b))
  | .pushDataMove b => some (.move .right (.pushData b))
  | .pushData b => some (.write b .pushBack)
  | .pushBack => some (.move .left (.finished none))
  | .popMarker => some (.read fun occupied =>
      if occupied then .popDataMove else .finished none)
  | .popDataMove => some (.move .right .popRead)
  | .popRead => some (.read fun b => .popEraseData b)
  | .popEraseData b => some (.write false (.popMarkerMove b))
  | .popMarkerMove b => some (.move .left (.popEraseMarker b))
  | .popEraseMarker b => some (.write false (.popBackFirst b))
  | .popBackFirst b => some (.move .left (.popBackSecond b))
  | .popBackSecond b => some (.move .left (.finished (some b)))
  | .peekMarker => some (.read fun occupied =>
      if occupied then .peekDataMove else .finished none)
  | .peekDataMove => some (.move .right .peekRead)
  | .peekRead => some (.read fun b => .peekBack b)
  | .peekBack b => some (.move .left (.finished (some b)))
  | .seekFirst => some (.move .right .seekSecond)
  | .seekSecond => some (.move .right .seekMarker)
  | .seekMarker => some (.read fun occupied =>
      if occupied then .seekFirst else .seekBackFirst)
  | .seekBackFirst => some (.move .left .seekBackSecond)
  | .seekBackSecond => some (.move .left (.finished none))
  | .parkMarker => some (.read fun occupied =>
      if occupied then .parkFirst else .finished none)
  | .parkFirst => some (.move .left .parkSecond)
  | .parkSecond => some (.move .left .parkMarker)
  | .finished _ => none

/-- Only the actual tape and fixed finite control are available to the machine. -/
structure BlockCfg where
  control : BlockControl
  tape : Tape Bool

def blockStep (c : BlockCfg) : Option BlockCfg :=
  match blockAction c.control with
  | none => none
  | some (.read next) => some ⟨next c.tape.head, c.tape⟩
  | some (.write bit next) => some ⟨next, c.tape.write bit⟩
  | some (.move direction next) => some ⟨next, c.tape.move direction⟩

/-- Accounting coordinates are not stored in, or read by, `BlockCfg`. -/
structure Extent where
  head : ℤ
  low : ℤ
  high : ℤ

/-- Reads and writes count the current cell; moves count the cell they visit. -/
def accountAction (action : BlockAction) (e : Extent) : Extent :=
  let head := match action with
    | .move .left _ => e.head - 1
    | .move .right _ => e.head + 1
    | _ => e.head
  ⟨head, min e.low head, max e.high head⟩

/-- The erased support remains charged by the monotone low/high coordinates. -/
def accountedBlockStep (c : BlockCfg × Extent) : Option (BlockCfg × Extent) :=
  match blockAction c.1.control with
  | none => none
  | some action => (blockStep c.1).map (fun next => (next, accountAction action c.2))

/-- Initially present cells and the current head belong to the counted interval. -/
def Within (t : Tape Bool) (e : Extent) : Prop :=
  e.low ≤ e.head ∧ e.head ≤ e.high ∧
    ∀ i : ℤ, t.nth i = true → e.low ≤ e.head + i ∧ e.head + i ≤ e.high

/-- The block containing the bottom marker is included even for an empty stack. -/
def topExtent (bs : List Bool) : Extent :=
  ⟨2 * (bs.length : ℤ), 0, 2 * (bs.length : ℤ) + 1⟩

/-- This is a space observable, not a counter or transition argument. -/
def extentCost (e : Extent) : ℕ :=
  (e.high - e.low + 1).toNat + (e.head.natAbs + 1).size + 1

end D5.S0.Computability.PhysicalDivider
