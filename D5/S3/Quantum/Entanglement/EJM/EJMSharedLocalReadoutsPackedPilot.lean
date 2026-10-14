/- Prepared actual-suffix receipts, not yet kernel accepted or delivered.
All 647 triangle and 425 singleton readouts and all 2497 context checks are
required below. Selection uses each actual projected partial context; the
original readout assignment and arithmetic sum are checked in full.
The root retains the original depth-12 prefix, so this module does not claim
a universal score bound or a locality refutation. -/
import D5.S3.Quantum.Entanglement.EJM.EJMSharedStaticPackedPilotData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsPackedPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
open D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
open D5.S3.Quantum.Entanglement.EJM.EJMSharedStaticPackedPilotData
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

/-- Every numerical leaf, actual projection and child edge of the existing
suffix is checked above. The smaller event may leave the prefix domain, as
the original global symmetry rank descent requires. -/
theorem suffix_smaller_bad_event
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (contexts 0) e)
    (hbad : score F1 F2 e < scale) :
    ∃ e' : Event (Fin 20) (Fin 4),
      score F1 F2 e' < scale ∧ FiniteLex.rank e' < FiniteLex.rank e := by
  exact checked_forces_smaller_bad_event
    (score F1 F2) FiniteLex.rank EJMGlobalScoreSymmetry.act scale rows bound
    EJMGlobalScoreSymmetry.dominates
    (fun _index p e accepted hp => checked_bound triangles singletons
      triangle_accepted singleton_accepted (triangleSelection p)
      (singletonSelection p) p accepted e hp)
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    rows_accepted 0 e hp hbad

#print axioms triangle_accepted
#print axioms singleton_accepted
#print axioms rows_accepted
#print axioms suffix_smaller_bad_event
end D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsPackedPilot
