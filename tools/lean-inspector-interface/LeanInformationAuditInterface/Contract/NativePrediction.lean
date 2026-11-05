import LeanInformationAuditInterface.Contract.Analysis.Prediction
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

namespace LeanInformationAudit.AuricFib.NativePrediction
open D5.S3.Arith.FibonacciAtomic
open LiteralWindowEnd (Window)
open ImmediateWindowStateCapacity
open LeanInformationAudit.Analysis
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- These are actual reader observations, not geometric coordinates of a law. -/
inductive Summary where
  | reply | seamReply | memory
  deriving DecidableEq

abbrev Snapshot := Option (Option Bool × Int × Option Int)

def Summary.read (summary : Summary) : RawState 0 → Snapshot
  | none => none
  | some (seam, state) => some (
      if summary == .reply then none else some seam,
      GraftAffineClosure.quantity state,
      if summary == .memory then some (GraftAffineClosure.quantity (clock state)) else none)

def decode : Snapshot → Option Int
  | none => none
  | some (_, quantity, _) => some quantity

/-- Witness coordinates are natural source coordinates. They cannot silently
introduce negative integer states outside the source history theorem. -/
inductive Point where
  | rejected
  | live (seam : Bool) (left right : Nat)

def Point.state : Point → RawState 0
  | .rejected => none
  | .live seam left right => some (seam, GraftAffineClosure.residue 0 (left, right))

/-- An input is a declared native letter. Repeated operations remain allowed;
rejection is absorbing and every operation is total on the actual raw state. -/
def model (summary : Summary) (actions : List Window) :
    PredictionModel (RawState 0) {a // a ∈ actions} Snapshot (Option Int) where
  observe := summary.read
  step := fun action state => rawTransition state action.val
  reply := rawOutput
  decode := decode
  reply_eq := by intro state; cases state <;> rfl

/-- A separation certifies a finite permitted continuation, not an exhaustive
search or an absence of all other distinguishing continuations. -/
structure Separation (summary : Summary) (actions : List Window) where
  left : Point
  right : Point
  word : List Window
  permitted : ∀ action ∈ word, action ∈ actions
  same : summary.read left.state = summary.read right.state
  different : rawOutput ((rawMachine 0).toDFA.evalFrom left.state word) ≠
    rawOutput ((rawMachine 0).toDFA.evalFrom right.state word)

/-- No numeric gain or cardinality follows from missing evidence. -/
inductive Evidence (summary : Summary) (actions : List Window) where
  | unknown (reason : String)
  | closed (proof : (model summary actions).Closed)
  | separated (witness : Separation summary actions)

structure Contract where
  summary : Summary
  actions : List Window
  evidence : Evidence summary actions

/-- Complete letters of the real input type; this is not a state enumeration. -/
def allActions : List Window := [.zero, .low, .high, .ends, .middle]

end LeanInformationAudit.AuricFib.NativePrediction
