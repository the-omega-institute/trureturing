import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalAdaptivePilot
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checkSplit checked_split_node)
private theorem accepted_17_0 : Accepted 17 0 ⟨16, by decide⟩ := by
  decide +kernel

private theorem accepted_17_1 : Accepted 17 1 ⟨27, by decide⟩ := by
  decide +kernel

private theorem accepted_17_2 : Accepted 17 2 ⟨28, by decide⟩ := by
  decide +kernel

private theorem accepted_17_3 : Accepted 17 3 ⟨29, by decide⟩ := by
  decide +kernel

private theorem node_16_30 :
    EJMOriginalGlobalDAGData.nodes 5 ⟨30, by decide⟩ =
      .split (coordinate 16) (![⟨16, by decide⟩,⟨27, by decide⟩,⟨28, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

private theorem accepted_16_0 : Accepted 16 0 ⟨30, by decide⟩ := by
  apply assemble 16 0 ⟨30, by decide⟩ (by decide) (![⟨16, by decide⟩,⟨27, by decide⟩,⟨28, by decide⟩,⟨29, by decide⟩]) node_16_30
  intro a
  fin_cases a
  · exact accepted_17_0
  · exact accepted_17_1
  · exact accepted_17_2
  · exact accepted_17_3

private theorem accepted_17_4 : Accepted 17 4 ⟨38, by decide⟩ := by
  decide +kernel

private theorem accepted_17_5 : Accepted 17 5 ⟨43, by decide⟩ := by
  decide +kernel

private theorem accepted_17_6 : Accepted 17 6 ⟨51, by decide⟩ := by
  decide +kernel

private theorem accepted_17_7 : Accepted 17 7 ⟨29, by decide⟩ := by
  decide +kernel

private theorem node_16_52 :
    EJMOriginalGlobalDAGData.nodes 5 ⟨52, by decide⟩ =
      .split (coordinate 16) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

private theorem accepted_16_1 : Accepted 16 1 ⟨52, by decide⟩ := by
  apply assemble 16 1 ⟨52, by decide⟩ (by decide) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) node_16_52
  intro a
  fin_cases a
  · exact accepted_17_4
  · exact accepted_17_5
  · exact accepted_17_6
  · exact accepted_17_7

private theorem accepted_16_2 : Accepted 16 2 ⟨53, by decide⟩ := by
  decide +kernel

private theorem accepted_16_3 : Accepted 16 3 ⟨54, by decide⟩ := by
  decide +kernel

private theorem node_15_55 :
    EJMOriginalGlobalDAGData.nodes 6 ⟨55, by decide⟩ =
      .split (coordinate 15) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

private theorem accepted_15_0 : Accepted 15 0 ⟨55, by decide⟩ := by
  apply assemble 15 0 ⟨55, by decide⟩ (by decide) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) node_15_55
  intro a
  fin_cases a
  · exact accepted_16_0
  · exact accepted_16_1
  · exact accepted_16_2
  · exact accepted_16_3

#print axioms accepted_15_0
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalAdaptivePilot
