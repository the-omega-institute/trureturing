/- Generated actual-context certificate source; prepared/uncompiled.
No native count, minimum or producer assertion is a Lean premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201Part000001
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem accepted_17_6_51 : Accepted 17 6 ⟨51, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    4 ⟨51, by decide⟩ (prefixCache 17 6)
    (prefixPartial 17 6) = true
  decide +kernel

theorem accepted_17_7_29 : Accepted 17 7 ⟨29, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    4 ⟨29, by decide⟩ (prefixCache 17 7)
    (prefixPartial 17 7) = true
  decide +kernel

theorem node_16_52 :
    EJMOriginalGlobalDAGData.nodes 5 ⟨52, by decide⟩ =
      .split (coordinate 16) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_1_52 : Accepted 16 1 ⟨52, by decide⟩ := by
  apply assemble 16 1 ⟨52, by decide⟩ (by decide) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) node_16_52
  intro a
  fin_cases a
  · exact accepted_17_4_38
  · exact accepted_17_5_43
  · exact accepted_17_6_51
  · exact accepted_17_7_29

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
