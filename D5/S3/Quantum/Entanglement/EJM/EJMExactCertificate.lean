/- GID: D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMExactCertificate
   mirror-E: none(waiver:exact-triangle-nonlocality-refutation)
   anchors: [D5/S3/Quantum/Entanglement/EJM/EJMGlobalBoundReplay, D5/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance]
   utility: kind=checker; basis=refutes=gid:D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.claim; result=D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.result; claim=D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.claim
   digest: The actual complete context-specific certificate refutes locality of the original EJM distribution. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay
import D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMExactCertificate
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score ejmDistribution)
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation (Node)

/-! This pending exact computation is the remaining global proof obligation.
No imported C++ validation or claimed external minimum is used as a premise.
This source is not a delivered certificate until its actual Lean check succeeds. -/

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
set_option trace.profiler true in
theorem global_accepted : globalAccepted := by
  decide +kernel

theorem score_lower_bound (e : Node → Fin 4) : scale ≤ score F1 F2 e :=
  accepted_score_lower_bound triangle_accepted singleton_accepted global_accepted e

def claim : Prop :=
  D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
    ejmDistribution

theorem result : ¬ claim :=
  accepted_excludes_triangle_local triangle_accepted singleton_accepted global_accepted

#print axioms global_accepted
#print axioms score_lower_bound
#print axioms result
end D5.S3.Quantum.Entanglement.EJM.EJMExactCertificate
