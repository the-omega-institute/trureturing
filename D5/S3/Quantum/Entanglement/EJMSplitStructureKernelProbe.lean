import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

set_option trace.profiler true in
example : ∀ j : Fin 32,
    checkStructure trianglePartialAct triangleRows
      ⟨4588 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option trace.profiler true in
example : ∀ j : Fin 32,
    checkStructure singletonPartialAct singletonRows
      ⟨1192 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

