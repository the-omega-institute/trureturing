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

abbrev Snapshot := Option (Option Bool × ZMod 0 × Option (ZMod 0))

def Summary.read (summary : Summary) : RawState 0 → Snapshot
  | none => none
  | some (seam, state) => some (
      if summary == .reply then none else some seam,
      GraftAffineClosure.quantity state,
      if summary == .memory then some (GraftAffineClosure.quantity (clock state)) else none)

def decode : Snapshot → Option (ZMod 0)
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
    PredictionModel (RawState 0) {a // a ∈ actions} Snapshot (Option (ZMod 0)) where
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


/-- The memory summary is closed for any declared subset of native letters.
The proof covers the entire integer evaluator, including absorbing rejection. -/
theorem memory_closed (actions : List Window) : (model .memory actions).Closed := by
  intro action left right same
  change Summary.read .memory (rawTransition left action.val) =
    Summary.read .memory (rawTransition right action.val)
  change Summary.read .memory left = Summary.read .memory right at same
  cases left with
  | none => cases right <;> simp_all [Summary.read, rawTransition]
  | some left =>
    cases right with
    | none => simp [Summary.read] at same
    | some right =>
      rcases left with ⟨seam, x⟩
      rcases right with ⟨otherSeam, y⟩
      have parts := Option.some.inj same
      have seams : seam = otherSeam := by
        simpa [Summary.read] using congrArg (fun z => z.1) parts
      have hu : GraftAffineClosure.quantity x = GraftAffineClosure.quantity y := by
        simpa [Summary.read] using congrArg (fun z => z.2.1) parts
      have hv : GraftAffineClosure.quantity (clock x) =
          GraftAffineClosure.quantity (clock y) := by
        simpa [Summary.read] using congrArg (fun z => z.2.2) parts
      subst otherSeam
      have observed : windowObserve (clock x + displacement action.val) =
          windowObserve (clock y + displacement action.val) := by
        dsimp [windowObserve, clock, GraftAffineClosure.step, GraftAffineClosure.quantity]
          at hu hv ⊢
        apply Prod.ext
        · dsimp
          linear_combination hv
        · dsimp
          linear_combination hu + 4 * hv
      by_cases guard : (seam && LiteralWindowEnd.last action.val) = true
      · simp [rawTransition, guard]
      · have lifted := congrArg (fun pair : ZMod 0 × ZMod 0 =>
          some (some (LiteralWindowEnd.first action.val), pair.1, some pair.2)) observed
        simpa [Summary.read, rawTransition, guard, windowObserve] using lifted


/-- This is an unbounded finite-word consequence of the existing dynamic
closure theorem, rather than a search through a selected depth. -/
theorem memory_future (actions : List Window) {left right : RawState 0}
    (same : Summary.read .memory left = Summary.read .memory right)
    (word : List {a // a ∈ actions}) :
    rawOutput (runWord (model .memory actions).step word left) =
      rawOutput (runWord (model .memory actions).step word right) :=
  (model .memory actions).future_of_closed (memory_closed actions) same word

/-- A null continuation separates equal current quantities, even when their
seams agree. Both points belong to the original natural composition domain. -/
def quantitySeparation : Separation .seamReply allActions where
  left := .live false 3 0
  right := .live false 0 2
  word := [.zero]
  permitted := by simp [allActions]
  same := by decide
  different := by decide

/-- Omitting the seam identifies states whose high continuation succeeds and
rejects respectively. Rejection is part of the reply, not discarded data. -/
def rejectionSeparation : Separation .reply allActions where
  left := .live false 0 0
  right := .live true 0 0
  word := [.high]
  permitted := by simp [allActions]
  same := by decide
  different := by decide

end LeanInformationAudit.AuricFib.NativePrediction
