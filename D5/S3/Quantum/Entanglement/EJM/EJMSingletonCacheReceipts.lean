/- GID: D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated; premises=D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts.mirror_accepted,D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts.transitions_accepted
   digest: Full finite-domain kernel receipts bind every local mirror and unknown-coordinate transition to the original rows. -/

/- Prepared source: not yet compiled. Part of the same complete actual EJM
certificate, not a standalone conditional or numerical delivery. All literal
mirrors, actions and transition receipts require kernel acceptance before use.
The original score, scale, all actual assignments and four value branches are
preserved. Producer checks below are not mathematical premises. -/

import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror00
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror01
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror02
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions00
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions01
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions02

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
-- Async elaboration retained a measured 32 GiB heap for these finite proofs.
-- Finish each unchanged kernel receipt before beginning the next one.
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

-- Exhaustive interval dispatch consumes every original kernel group.
set_option maxHeartbeats 10000000 in
private theorem mirror_fields_accepted (j : Fin 8689) : checkMirrorFields j = true := by
  by_cases h0 : j.val < 4096
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror00.accepted j (by omega) h0
  by_cases h1 : j.val < 8192
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror01.accepted j (by omega) h1
  exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror02.accepted j (by omega) j.isLt

theorem mirror_accepted (j : Fin 8689) : checkMirror j = true := by
  apply decide_eq_true
  exact EJMLocalCacheData.checked_raw_mirror_eq (by decide) (by decide)
    (mirror j) (singletonTree.read 9 j.val) (mirror_fields_accepted j)

-- Exhaustive interval dispatch consumes every original kernel group.
set_option maxHeartbeats 10000000 in
theorem transitions_accepted (j : Fin 8689) : checkTransitions j = true := by
  by_cases h0 : j.val < 4096
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions00.accepted j (by omega) h0
  by_cases h1 : j.val < 8192
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions01.accepted j (by omega) h1
  exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Transitions02.accepted j (by omega) j.isLt

theorem assignment_eq (j : Fin 8689) :
    assignment j = (singletonRows j).assignment :=
  (of_decide_eq_true (mirror_accepted j)).1

theorem lower_eq (j : Fin 8689) : lower j = (singletonRows j).lower :=
  (of_decide_eq_true (mirror_accepted j)).2

/-- This consequence uses the original row assignments on both sides. -/
theorem transition_accepted (j : Fin 8689) (i : Fin 9) (a : Fin 4)
    (unknown : (singletonRows j).assignment i = none) :
    D5.S0.Certificates.FiniteLocalRowCache.checkTransition singletonPartialAct
      singletonRows transition j i a = true := by
  have hu : assignment j i = none := by rw [assignment_eq, unknown]
  have h := of_decide_eq_true (transitions_accepted j) i hu a
  rw [assignment_eq, assignment_eq] at h
  exact decide_eq_true h

#print axioms assignment_eq
#print axioms lower_eq
#print axioms transition_accepted

end D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
