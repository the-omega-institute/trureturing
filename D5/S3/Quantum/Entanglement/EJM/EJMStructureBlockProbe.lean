/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureBlockProbe
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureBlockProbe
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureBlockProbe.triangle_first_block
   digest: Measure a bounded piece of the same actual complete structural receipt. -/

/- WIP resource probe for the original structural obligation. This is not
complete local acceptance, global acceptance or a delivery. Every original
row must still be checked before the consumer can be frozen. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureBlockProbe
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
theorem triangle_first_block : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel
#print axioms triangle_first_block
end D5.S3.Quantum.Entanglement.EJM.EJMStructureBlockProbe
