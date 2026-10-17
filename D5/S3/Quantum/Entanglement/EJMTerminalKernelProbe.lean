import D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

set_option trace.profiler true in
example : ∀ j : Fin 4,
    triangleTerminalCheck ⟨j.val, lt_trans j.isLt (by decide : 4 < 4588)⟩ = true := by
  decide +kernel

set_option trace.profiler true in
example : ∀ j : Fin 8,
    singletonTerminalCheck ⟨j.val, lt_trans j.isLt (by decide : 8 < 1192)⟩ = true := by
  decide +kernel
