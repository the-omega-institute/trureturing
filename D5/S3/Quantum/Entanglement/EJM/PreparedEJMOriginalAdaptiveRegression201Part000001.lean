/- Generated actual-context certificate source; prepared/uncompiled.
No native count, minimum or producer assertion is a Lean premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201Part000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_30 :
    EJMOriginalGlobalDAGData.nodes 5 ⟨30, by decide⟩ =
      .split (coordinate 16) (![⟨16, by decide⟩,⟨27, by decide⟩,⟨28, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_0_30 : Accepted 16 0 ⟨30, by decide⟩ := by
  apply assemble 16 0 ⟨30, by decide⟩ (by decide) (![⟨16, by decide⟩,⟨27, by decide⟩,⟨28, by decide⟩,⟨29, by decide⟩]) node_16_30
  intro a
  fin_cases a
  · exact accepted_17_0_16
  · exact accepted_17_1_27
  · exact accepted_17_2_28
  · exact accepted_17_3_29

theorem accepted_17_4_38 : Accepted 17 4 ⟨38, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    4 ⟨38, by decide⟩ (prefixCache 17 4)
    (prefixPartial 17 4) = true
  decide +kernel

theorem accepted_17_5_43 : Accepted 17 5 ⟨43, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    4 ⟨43, by decide⟩ (prefixCache 17 5)
    (prefixPartial 17 5) = true
  decide +kernel

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAdaptiveRegression201
