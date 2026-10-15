/- Transient kernel/memory check for an exact block of the full singleton
receipt module. This file is not a standalone delivery or global acceptance.
The actual 497 highest-index rows include the original singleton root.
-/
import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false
namespace D5.S3.Quantum.Entanglement.EJM.EJMSingletonReceiptBlockProbe
open D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData
set_option maxHeartbeats 100000000 in
-- Check this exact block of the unchanged complete mirror receipt.
set_option trace.profiler true in
theorem mirror_last : ∀ k : Fin 497,
    checkMirrorFields ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel
set_option maxHeartbeats 100000000 in
-- Check every unknown coordinate and all four values in this exact block.
set_option trace.profiler true in
theorem transitions_last : ∀ k : Fin 497,
    checkTransitions ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel
#print axioms mirror_last
#print axioms transitions_last
end D5.S3.Quantum.Entanglement.EJM.EJMSingletonReceiptBlockProbe
