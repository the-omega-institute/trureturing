import LeanInformationAuditInterface.Contract.Analysis.Finite
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

/-- The reader is exactly the evaluator occurring in the original theorem,
at its explicit initialized single-window substitution. -/
theorem NativeBridge.reader_source (bridge : NativeBridge) (window : Window) :
    bridge.reader window = (rawMachine 0).toDFA.evalFrom
      (some (false, GraftAffineClosure.residue 0 (0, 0))) [window] := by
  rw [bridge.reader_eq]
  rfl

/-- The total task is the same evaluator at the appended high suffix. -/
theorem NativeBridge.reply_source (bridge : NativeBridge) (window : Window) :
    bridge.reply window = rawOutput ((rawMachine 0).toDFA.evalFrom
      (some (false, GraftAffineClosure.residue 0 (0, 0))) [window, .high]) := by
  rw [bridge.reply_eq, bridge.reader_eq]
  rfl

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

/-- Full native theorem correspondence is confined to this adapter. The
single-window substitution preserves the original theorem as its premise. -/
structure NativeSource {Statement : Prop} (occurrence : Statement) where
  reconstruction : Analysis.Reconstruction Statement
    (type_of% NativeContinuation.NullReplyFiber.native_execution)

/-- The original theorem specialized at seam=false, composition=(0,0), and one
window. This proof is obtained from the indexed occurrence, not another theorem. -/
def NativeSource.specialize {Statement : Prop} {occurrence : Statement}
    (source : NativeSource occurrence) (window : Window) :
    type_of% (NativeContinuation.NullReplyFiber.native_execution false (0, 0) [window]) := by
  cases source with
  | mk reconstruction =>
    cases reconstruction
    exact occurrence false (0, 0) [window]

/-- The same initialized state followed by high uses the original full theorem
at the explicit two-letter history; rejection stays in its Option output. -/
def NativeSource.continueHigh {Statement : Prop} {occurrence : Statement}
    (source : NativeSource occurrence) (window : Window) :
    type_of% (NativeContinuation.NullReplyFiber.native_execution false (0, 0) [window, .high]) := by
  cases source with
  | mk reconstruction =>
    cases reconstruction
    exact occurrence false (0, 0) [window, .high]

/-- Evidence is indexed by the full occurrence. Generic clients have no native
proposition restriction and require neither finite acquisition nor a source law.
Unsupported submissions carry no correspondence evidence. -/
inductive Evidence {Statement : Prop} (occurrence : Statement) where
  | typed (client : Analysis.Client.{0,t,s,r,o,a,v} occurrence)
  | native (source : NativeSource occurrence) (bridge : NativeBridge) (acquisition : Acquisition)
      (initial : List Readout) (layers : List Readout)
  | unsupported (reason : String)

/-- Source-owned downstream analysis attached to an actual compiled theorem.
This is neither a proof-escape registration nor an admission certificate. -/
structure Application {Statement : Prop} (occurrence : Statement) where
  evidence : Evidence.{t,s,r,o,a,v} occurrence

end LeanInformationAudit.AuricFib.Contract
