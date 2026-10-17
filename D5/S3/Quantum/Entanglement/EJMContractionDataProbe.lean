import D5.S3.Quantum.Entanglement.EJM.EJMContractionData
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJM.EJMContractionSymmetry
open D5.S3.Quantum.Entanglement.EJM.EJMContractionData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

set_option trace.profiler true in
theorem triangle_contraction_probe : ∀ i : Fin 2,
    triangleContraction F1 (triangleTail ⟨i.val, lt_trans i.isLt (by decide : 2 < 95)⟩) =
      triangleValue ⟨i.val, lt_trans i.isLt (by decide : 2 < 95)⟩ := by
  decide +kernel

set_option trace.profiler true in
theorem singleton_contraction_probe : ∀ i : Fin 8,
    singletonContraction F2
      (singletonTail ⟨i.val, lt_trans i.isLt (by decide : 8 < 332)⟩) =
      singletonValue ⟨i.val, lt_trans i.isLt (by decide : 8 < 332)⟩ := by
  decide +kernel

#print axioms triangle_contraction_probe
#print axioms singleton_contraction_probe
