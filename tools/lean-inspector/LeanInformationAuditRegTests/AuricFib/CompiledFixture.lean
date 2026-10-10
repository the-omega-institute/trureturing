import LeanInformationAuditInterface.Contract.AuricFib

namespace LeanInformationAuditRegTests.AuricFib.CompiledFixture
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

def declared : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.declared "compiled source fixture" acquiredMasses)
    [] [.seam, .guard, .reply, .atom]

def absent : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.absent "unacquired compiled source")
    [] [.seam, .guard, .reply, .atom]

def empirical : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.empirical "compiled archive" [.zero, .ends, .middle])
    [] [.seam, .guard, .reply, .atom]

def apex : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.declared "apex fixture" {
    nullMass := 0, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 1,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def zeroCondition : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.declared "zero event fixture" {
    nullMass := 1, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 0,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def unsupported : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .unsupported "unbounded history source has no supported finite arena"

def rejected : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.absent "incomplete readout contract") [] [.seam]

theorem noise : True := trivial

theorem unrelated : True := trivial

def wrongTarget : Application unrelated where
  evidence := .native bridge (.absent "unrelated statement") [] [.seam, .guard, .reply, .atom]

def parameterized (_n : Nat) : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native bridge (.absent "parameterized contract") [] [.seam, .guard, .reply, .atom]

end LeanInformationAuditRegTests.AuricFib.CompiledFixture
