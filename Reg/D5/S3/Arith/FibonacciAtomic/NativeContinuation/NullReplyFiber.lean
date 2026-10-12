import LeanInformationAuditInterface.Contract.AuricFib

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
open _root_.D5.S3.Arith.FibonacciAtomic
open ImmediateWindowStateCapacity
open LeanInformationAudit.AuricFib.Contract

def source : NativeSource NativeContinuation.NullReplyFiber.native_execution where
  reconstruction := .exact

def bridge : NativeBridge where
  reader := fun a => rawTransition (rawMachine 0).start a
  reply := fun a => rawOutput (rawTransition (rawTransition (rawMachine 0).start a) .high)
  reader_eq := rfl
  reply_eq := rfl

/-- The original native execution occurrence has an exact complete single-window
analysis. Its source law is unacquired, so only finite micro readings are available. -/
def initializedWindow : Application.{0,0,0,0,0,0}
    NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native source bridge
    (.absent "complete initialized native Window source") [] [.seam, .guard, .reply, .atom]

def qualificationNative : Application.{0,0,0,0,0,0}
    NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native source bridge (.declared "R3 qualification input" {
    nullMass := 1, lowMass := 1, highMass := 1, endsMass := 1, middleMass := 1,
    denominator := 5, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
