/- GID: D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadoutsPilot
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadoutsPilot
   mirror-E: none(waiver:exact-shared-local-readout-suffix-acceptance)
   anchors: []
   utility: none
   digest: Every actual readout, projection and child edge of the original suffix is independently checked. -/

/- Prepared actual-suffix receipts, not yet kernel accepted or delivered.
All 647 triangle and 425 singleton readouts and all 2497 context checks are
required below. The concrete root carries the original depth-12 prefix;
this module does not claim a universal score bound or a locality refutation. -/
import D5.S3.Quantum.Entanglement.EJM.EJMSharedStaticPilotData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
open D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
open D5.S3.Quantum.Entanglement.EJM.EJMSharedStaticPilotData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

theorem triangle_accepted : ∀ j, checkTriangle (triangles j) = true := by
  decide +kernel

theorem singleton_accepted : ∀ j, checkSingleton (singletons j) = true := by
  decide +kernel

theorem rows_accepted : ∀ index,
    checkRow rows bound EJMGlobalScoreSymmetry.dominates index = true := by
  decide +kernel

/-- This is the actual original-prefix suffix, with every numerical leaf,
projection and child edge checked above. Its rank conclusion leaves the
prefix domain unrestricted for the smaller event, as global symmetry cuts
require. Complete global coverage remains a separate obligation. -/
theorem suffix_smaller_bad_event
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (contexts 0) e)
    (hbad : score F1 F2 e < scale) :
    ∃ e' : Event (Fin 20) (Fin 4),
      score F1 F2 e' < scale ∧ FiniteLex.rank e' < FiniteLex.rank e := by
  exact checked_forces_smaller_bad_event
    (score F1 F2) FiniteLex.rank EJMGlobalScoreSymmetry.act scale rows bound
    EJMGlobalScoreSymmetry.dominates
    (fun index p e accepted hp => checked_bound triangles singletons
      triangle_accepted singleton_accepted (triangleSelection (leafIndex index))
      (singletonSelection (leafIndex index)) p accepted e hp)
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    rows_accepted 0 e hp hbad

#print axioms triangle_accepted
#print axioms singleton_accepted
#print axioms rows_accepted
#print axioms suffix_smaller_bad_event
end D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsPilot
