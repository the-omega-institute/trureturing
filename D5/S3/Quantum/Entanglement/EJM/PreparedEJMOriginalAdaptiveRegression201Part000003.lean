/- Generated actual-context certificate source; prepared/uncompiled.
No native count, minimum or producer assertion is a Lean premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201Part000001
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201Part000002
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem accepted_16_2_53 : Accepted 16 2 ⟨53, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    5 ⟨53, by decide⟩ (prefixCache 16 2)
    (prefixPartial 16 2) = true
  decide +kernel

theorem accepted_16_3_54 : Accepted 16 3 ⟨54, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    5 ⟨54, by decide⟩ (prefixCache 16 3)
    (prefixPartial 16 3) = true
  decide +kernel

theorem node_15_55 :
    EJMOriginalGlobalDAGData.nodes 6 ⟨55, by decide⟩ =
      .split (coordinate 15) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_0_55 : Accepted 15 0 ⟨55, by decide⟩ := by
  apply assemble 15 0 ⟨55, by decide⟩ (by decide) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) node_15_55
  intro a
  fin_cases a
  · exact accepted_16_0_30
  · exact accepted_16_1_52
  · exact accepted_16_2_53
  · exact accepted_16_3_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
