import LeanInformationAuditInterface.Contract.AuricFib

namespace LeanInformationAuditFibTests.AuricFib.CompiledFixture
open D5.S3.Arith.FibonacciAtomic
open ImmediateWindowStateCapacity
open LeanInformationAudit.AuricFib.Contract

private def acquiredNullMass : Nat := 1

def acquiredMasses : Masses where
  nullMass := acquiredNullMass
  lowMass := 1
  highMass := 1
  endsMass := 1
  middleMass := 1
  denominator := 5
  positive := by decide
  normalized := by decide

def reader : LiteralWindowEnd.Window → RawState 0 :=
  fun a => rawTransition (rawMachine 0).start a

def reply : LiteralWindowEnd.Window → Option Int :=
  fun a => rawOutput (rawTransition (reader a) .high)

def bridge : NativeBridge where
  reader := reader
  reply := reply
  reader_eq := rfl
  reply_eq := rfl

def declared : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "compiled source fixture" acquiredMasses)
    [] [.seam, .guard, .reply, .atom]

def absent : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "unacquired compiled source")
    [] [.seam, .guard, .reply, .atom]

def empirical : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.empirical "compiled archive" [.zero, .ends, .middle])
    [] [.seam, .guard, .reply, .atom]

def apex : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "apex fixture" {
    nullMass := 0, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 1,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def zeroCondition : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "zero event fixture" {
    nullMass := 1, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 0,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def unsupported : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .unsupported "unbounded history source has no supported finite arena"

def rejected : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "incomplete readout contract") [] [.seam]

theorem noise : True := trivial

theorem unrelated : True := trivial

/-- Propositional transport can inhabit a typed record; it does not supply the
original telescope. Compiled source reconstruction must reject this fixture. -/
def wrongSource : NativeSource unrelated where
  reconstruction := by
    have h : True = (type_of% NativeContinuation.NullReplyFiber.native_execution) :=
      propext ⟨fun _ => NativeContinuation.NullReplyFiber.native_execution, fun _ => trivial⟩
    rw [← h]
    exact .exact

def wrongTarget : Application.{0,0,0,0,0,0} unrelated where
  evidence := .native wrongSource bridge (.absent "unrelated statement") [] [.seam, .guard, .reply, .atom]

def parameterized (_n : Nat) : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "parameterized contract") [] [.seam, .guard, .reply, .atom]


open LeanInformationAudit.AuricFib

/-- The same original source supplies both a positive invariant and concrete
counterexamples for weaker observations. The one-window source law stays absent. -/
def predictionClosed : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .memory, actions := NativePrediction.allActions,
    evidence := .closed (NativePrediction.memory_closed _) } }

def predictionQuantity : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .seamReply, actions := NativePrediction.allActions,
    evidence := .separated NativePrediction.quantitySeparation } }

def predictionRejection : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .reply, actions := NativePrediction.allActions,
    evidence := .separated NativePrediction.rejectionSeparation } }

def predictionUnknown : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .seamReply, actions := NativePrediction.allActions,
    evidence := .unknown "no operation evidence supplied" } }

/-- Closure over an empty input type covers only the empty continuation. -/
def predictionEmpty : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .reply, actions := [],
    evidence := .closed (by intro action; exact False.elim (by simpa using action.property)) } }

/-- Prediction evidence cannot turn a non-native occurrence into this source. -/
def predictionWrongSource : Application.{0,0,0,0,0,0} unrelated where
  evidence := .typed {
    source := LeanInformationAudit.Analysis.Source.unobserved unrelated
      `LeanInformationAuditFibTests.AuricFib.CompiledFixture
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }
  prediction := some { source := wrongSource, contract := {
    summary := .memory, actions := NativePrediction.allActions,
    evidence := .closed (NativePrediction.memory_closed _) } }

end LeanInformationAuditFibTests.AuricFib.CompiledFixture
