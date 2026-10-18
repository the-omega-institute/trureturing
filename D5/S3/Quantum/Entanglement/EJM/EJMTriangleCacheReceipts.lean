/- GID: D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated; premises=D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.mirror_accepted,D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.transitions_accepted
   digest: Full finite-domain kernel receipts bind every local mirror and unknown-coordinate transition to the original rows. -/

/- Part of the same complete actual EJM certificate,
not a standalone conditional or numerical delivery. All literal
mirrors, actions and transition receipts require kernel acceptance before use.
The original score, scale, all actual assignments and four value branches are
preserved. Producer checks below are not mathematical premises. -/

import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror00
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror01
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror02
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror03
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror04
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror05
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror06
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror07
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror08
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror09
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror10
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions00
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions01
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions02
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions03
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions04
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions05
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions06
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions07
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions08
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions09
import D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
-- Bounded kernel reductions preserve every original row and transition.
-- Complete each receipt before beginning the next finite block.
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheReceipts
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheData

-- Exhaustive interval dispatch consumes every original kernel group.
set_option maxHeartbeats 10000000 in
private theorem mirror_fields_accepted (j : Fin 41294) : checkMirrorFields j = true := by
  by_cases h0 : j.val < 4096
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror00.accepted j (by omega) h0
  by_cases h1 : j.val < 8192
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror01.accepted j (by omega) h1
  by_cases h2 : j.val < 12288
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror02.accepted j (by omega) h2
  by_cases h3 : j.val < 16384
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror03.accepted j (by omega) h3
  by_cases h4 : j.val < 20480
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror04.accepted j (by omega) h4
  by_cases h5 : j.val < 24576
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror05.accepted j (by omega) h5
  by_cases h6 : j.val < 28672
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror06.accepted j (by omega) h6
  by_cases h7 : j.val < 32768
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror07.accepted j (by omega) h7
  by_cases h8 : j.val < 36864
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror08.accepted j (by omega) h8
  by_cases h9 : j.val < 40960
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror09.accepted j (by omega) h9
  exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror10.accepted j (by omega) j.isLt

theorem mirror_accepted (j : Fin 41294) : checkMirror j = true := by
  apply decide_eq_true
  exact EJMLocalCacheData.checked_raw_mirror_eq (by decide) (by decide)
    (mirror j) (triangleTree.read 10 j.val) (mirror_fields_accepted j)

-- Exhaustive interval dispatch consumes every original kernel group.
set_option maxHeartbeats 10000000 in
theorem transitions_accepted (j : Fin 41294) : checkTransitions j = true := by
  by_cases h0 : j.val < 4096
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions00.accepted j (by omega) h0
  by_cases h1 : j.val < 8192
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions01.accepted j (by omega) h1
  by_cases h2 : j.val < 12288
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions02.accepted j (by omega) h2
  by_cases h3 : j.val < 16384
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions03.accepted j (by omega) h3
  by_cases h4 : j.val < 20480
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions04.accepted j (by omega) h4
  by_cases h5 : j.val < 24576
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions05.accepted j (by omega) h5
  by_cases h6 : j.val < 28672
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions06.accepted j (by omega) h6
  by_cases h7 : j.val < 32768
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions07.accepted j (by omega) h7
  by_cases h8 : j.val < 36864
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions08.accepted j (by omega) h8
  by_cases h9 : j.val < 40960
  · exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions09.accepted j (by omega) h9
  exact D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Transitions10.accepted j (by omega) j.isLt

theorem assignment_eq (j : Fin 41294) :
    assignment j = (triangleRows j).assignment :=
  (of_decide_eq_true (mirror_accepted j)).1

theorem lower_eq (j : Fin 41294) : lower j = (triangleRows j).lower :=
  (of_decide_eq_true (mirror_accepted j)).2

/-- This consequence uses the original row assignments on both sides. -/
theorem transition_accepted (j : Fin 41294) (i : Fin 10) (a : Fin 4)
    (unknown : (triangleRows j).assignment i = none) :
    D5.S0.Certificates.FiniteLocalRowCache.checkTransition trianglePartialAct
      triangleRows transition j i a = true := by
  have hu : assignment j i = none := by rw [assignment_eq, unknown]
  have h := of_decide_eq_true (transitions_accepted j) i hu a
  rw [assignment_eq, assignment_eq] at h
  exact decide_eq_true h

#print axioms assignment_eq
#print axioms lower_eq
#print axioms transition_accepted

end D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheReceipts
