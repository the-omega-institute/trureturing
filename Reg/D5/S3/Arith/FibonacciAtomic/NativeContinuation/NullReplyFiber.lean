import LeanInformationAuditInterface.Contract.AuricFib

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
open _root_.D5.S3.Arith.FibonacciAtomic
open ImmediateWindowStateCapacity
open LeanInformationAudit.AuricFib.Contract

/-- The original native execution occurrence has an exact complete single-window
analysis. Its source law is unacquired, so only finite micro readings are available. -/
def initializedWindow : Application NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native {
    reader := fun a => rawTransition (rawMachine 0).start a
    reply := fun a => rawOutput (rawTransition (rawTransition (rawMachine 0).start a) .high)
    reader_eq := rfl
    reply_eq := rfl
  } (.absent "complete initialized native Window source") [] [.seam, .guard, .reply, .atom]

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
