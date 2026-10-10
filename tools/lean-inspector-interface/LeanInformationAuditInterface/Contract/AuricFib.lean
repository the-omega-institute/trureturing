import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

namespace LeanInformationAudit.AuricFib.Contract
open D5.S3.Arith.FibonacciAtomic
open LiteralWindowEnd (Window)
open ImmediateWindowStateCapacity (RawState rawTransition rawMachine rawOutput)

/-- The complete native state domain is Window, independent of law support.
The equalities bind an owner's reader and total continuation to the same source. -/
structure NativeBridge where
  reader : Window → RawState 0
  reply : Window → Option Int
  reader_eq : reader = fun a => rawTransition (rawMachine 0).start a
  reply_eq : reply = fun a => rawOutput (rawTransition (reader a) .high)

/-- Exact rational declared masses, with normalization checked by Lean.
Declaration does not certify acquisition or a physical probability law. -/
structure Masses where
  nullMass : Nat
  lowMass : Nat
  highMass : Nat
  endsMass : Nat
  middleMass : Nat
  denominator : Nat
  positive : 0 < denominator
  normalized : nullMass + lowMass + highMass + endsMass + middleMass = denominator

inductive Acquisition where
  | absent (source : String)
  | declared (source : String) (masses : Masses)
  | empirical (source : String) (archive : List Window)

inductive Readout where
  | atom | seam | guard | reply
  deriving DecidableEq

/-- Unsupported contracts remain data; they carry no native correspondence. -/
inductive Evidence where
  | native (bridge : NativeBridge) (acquisition : Acquisition)
      (initial : List Readout) (layers : List Readout)
  | unsupported (reason : String)

/-- Source-owned downstream analysis attached to an actual compiled theorem.
This is neither a proof-escape registration nor an admission certificate. -/
structure Application {Statement : Sort u} (occurrence : Statement) where
  evidence : Evidence

end LeanInformationAudit.AuricFib.Contract
