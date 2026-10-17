import D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

set_option trace.profiler true in
theorem lookup_triangle : F1 ![0,0,0,0,0,0,0,0,0,0] = (-10502458495547) := by
  decide +kernel

set_option trace.profiler true in
theorem lookup_singleton : F2 ![0,0,0,0,0,0,0,0,0] = 892409425237 := by
  decide +kernel

#print axioms lookup_triangle
#print axioms lookup_singleton
