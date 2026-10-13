import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused

namespace LeanInformationAudit.AuricFib

open Lean
open D5.S3.Arith.FibonacciAtomic
open LiteralWindowEnd (Window)
open ImmediateWindowStateCapacity (RawState rawMachine rawTransition rawOutput)
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

/-- The order is the SPEC mode order, independent of the native constructor order. -/
def modes : List Window := [.zero, .low, .high, .ends, .middle]

def modeIndex : Window → Nat
  | .zero => 0 | .low => 1 | .high => 2 | .ends => 3 | .middle => 4

def modeName : Window → String
  | .zero => "null" | .low => "2" | .high => "5" | .ends => "25" | .middle => "3"

def firstState (a : Window) : RawState 0 := rawTransition (rawMachine 0).start a

def suffixState (a : Window) : RawState 0 := rawTransition (firstState a) .high

def firstReply (a : Window) : Option Int := rawOutput (firstState a)

def suffixReply (a : Window) : Option Int := rawOutput (suffixState a)

def seam (a : Window) : Option Bool := (firstState a).map Prod.fst

def guardAccepts (a : Window) : Bool := (suffixState a).isSome

def parityEvent (a : Window) : Bool := (firstReply a).any (fun n => n % 2 == 1)

/-- The fixed target is the actual odd-record and rejected-suffix joint event. -/
def targetIndicator (a : Window) : Rat := if parityEvent a && !guardAccepts a then 1 else 0

abbrev nativeArena : Arena := Arena.ofFintype Window

def enumeration : Arena.StateEnumeration nativeArena where
  states := modes
  nodup := by change modes.Nodup; decide
  complete := by change modes.toFinset = (Finset.univ : Finset Window); decide

/-- Analysis units satisfy the counting API, and carry no proof-escape assertion. -/
def readoutUnit {O : Type} [DecidableEq O] (axis : PrimitiveAxis)
    (readout : Window → O) : TheoremUnit nativeArena where
  primitives := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    atom := fun _ => ⟨axis, cutKernel readout⟩ }
  Statement := True
  proof := True.intro

abbrev nativeCatalog : Catalog nativeArena := Catalog.ofVector ![
  readoutUnit .cut modeIndex, readoutUnit .flow seam,
  readoutUnit .admit guardAccepts, readoutUnit .cut suffixReply]

def readoutName (i : Fin 4) : String :=
  match i.val with
  | 0 => "atom" | 1 => "seam" | 2 => "guard" | _ => "reply"

def readoutIndex (s : String) : Except String (Fin 4) :=
  match s with
  | "atom" => .ok 0 | "seam" => .ok 1 | "guard" => .ok 2 | "reply" => .ok 3
  | _ => .error s!"unknown micro readout: {s}; law statistics are not sample readouts"

def nativeRows : Json := Json.arr (modes.toArray.map fun a =>
  let q := firstState a
  Json.mkObj [
    ("mode", toJson (modeName a)),
    ("bits_x2_y5_z3", toJson [if LiteralWindowEnd.first a then 1 else 0,
      if LiteralWindowEnd.last a then 1 else 0, if a = .middle then 1 else 0]),
    ("first_reply", toJson (firstReply a |>.map toString)),
    ("suffix_reply", toJson (suffixReply a |>.map toString)),
    ("seam", toJson (seam a)),
    ("composition", q.map (fun s =>
      toJson [toString (s.2.1 : Int), toString (s.2.2 : Int)]) |>.getD Json.null),
    ("guard_accepts", toJson (guardAccepts a)),
    ("parity_event", toJson (parityEvent a))])

end LeanInformationAudit.AuricFib
