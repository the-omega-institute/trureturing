/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock24
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock24
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock24.accepted
   digest: Exact structural checks for actual triangle row interval [31744, 32768). -/

/- These are the same original checkStructure obligations, split at existing
1024-row boundaries so interruption preserves completed kernel modules.
All literal assignments, actions, child indices and lower bounds remain.
No independent finite-instance result or global acceptance is asserted.
The complete EJMStructureCertificates receipt consumes this entire interval.
Source-bound registration remains unfinished under issue #16309. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock24
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_31744 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨31744 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 1024) :
    checkStructure trianglePartialAct triangleRows
      ⟨31744 + j.val, by have h := j.isLt; omega⟩ = true := by
  exact triangle_chunk_31744 j

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock24
