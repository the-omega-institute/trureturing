/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock6
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock6
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock6.accepted
   digest: Exact structural checks for actual singleton row interval [6144, 7168). -/

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
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock6
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_6144 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨6144 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 1024) :
    checkStructure singletonPartialAct singletonRows
      ⟨6144 + j.val, by have h := j.isLt; omega⟩ = true := by
  exact singleton_chunk_6144 j

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock6
