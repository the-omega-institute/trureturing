/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLiteralBatch0
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLiteralBatch0
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Kernel arithmetic compares the literal observation and its first partials with their tables at residue 0. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
theorem literal_value_at_0 (ab : Fin 4 × Fin 4) :
    slicedObservation imaginary (point (0 : F)) ab = valueAt 0 ab := by
  rcases ab with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
theorem literal_partial_at_0 (r : Fin 10) (j : Fin 5) :
    partialValue imaginary (point (0 : F)) (observedRow r) j = partialAt 0 r j := by
  fin_cases r <;> fin_cases j <;> decide +kernel

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
