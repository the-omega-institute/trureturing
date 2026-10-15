/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover550
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierResponses
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMCacheState (step lower)
open EJMCacheSoundness (initial)
open EJMCertificateData (F1 F2)
open EJMPartialBoundData (scale)
open EJMOriginalCachedGlobalReplay (Valid valid_lower_le_score step_valid initial_valid)
open EJMInflationScore (score)

theorem accepted_original_root :
    FiniteAdaptiveSemanticFrontierReplay.check EJMOriginalGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale frontier 21
      EJMOriginalGlobalDAGData.root initial (fun _ => none) = true := by
  simpa only [TransientEJMOriginalAdaptiveFrontierBridge.Accepted, prefixCache,
    prefixPartial, EJMOriginalGlobalDAGData.root] using context_0_0_1558776

/-- This concrete conclusion requires every generated raw/semantic cut receipt
and every actual coverage proof to compile. It has no rootAccepted premise. -/
theorem original_score_lower_bound :
    ∀ e : FiniteSymmetryBoundReplay.Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact PreparedFiniteAdaptiveFrontierResponse.checked_global_lower_bound
    (score F1 F2) FiniteLexSymmetry.rank EJMGlobalScoreSymmetry.act
    EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
    Valid valid_lower_le_score step_valid EJMGlobalScoreSymmetry.actual_score_invariant
    EJMGlobalScoreSymmetry.dominates_rank_lt frontier (frontier_responses all_cut_responses)
    21 EJMOriginalGlobalDAGData.root initial initial_valid accepted_original_root

#print axioms original_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
