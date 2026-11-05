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
  prediction := some {
    source := source
    contract := {
      summary := .memory
      actions := LeanInformationAudit.AuricFib.NativePrediction.allActions
      evidence := .closed (LeanInformationAudit.AuricFib.NativePrediction.memory_closed _) } }

def initializedWindowQuantity : Application.{0,0,0,0,0,0}
    NativeContinuation.NullReplyFiber.native_execution where
  evidence := initializedWindow.evidence
  prediction := some {
    source := source
    contract := {
      summary := .seamReply
      actions := LeanInformationAudit.AuricFib.NativePrediction.allActions
      evidence := .separated LeanInformationAudit.AuricFib.NativePrediction.quantitySeparation } }

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
