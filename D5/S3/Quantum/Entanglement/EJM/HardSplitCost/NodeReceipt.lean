/- GID: D5/S3/Quantum/Entanglement/EJM/HardSplitCost/NodeReceipt
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/HardSplitCost/NodeReceipt
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/HardSplitCost/NodeReceipt.root_split_receipt,D5/S3/Quantum/Entanglement/EJM/HardSplitCost/NodeReceipt.root_split
   digest: Exact original node-17413 split receipt and equation consumed by raw_cut_00337. -/

/- Uncompiled transient candidate. No acceptance claim. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
set_option trace.profiler true
namespace D5.S3.Quantum.Entanglement.EJM.TransientHardSplit
open EJMOriginalReplayAssembly (Accepted coordinate assemble)
theorem root_split_receipt :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 8 ⟨17413, by decide⟩)
      (coordinate 13) (fun a : Fin 4 => (![⟨17372, by decide⟩, ⟨17384, by decide⟩, ⟨17399, by decide⟩, ⟨17412, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) = true := by
  decide +kernel

theorem root_split : EJMOriginalGlobalDAGData.nodes 8 ⟨17413, by decide⟩ =
    .split (coordinate 13) (fun a : Fin 4 => (![⟨17372, by decide⟩, ⟨17384, by decide⟩, ⟨17399, by decide⟩, ⟨17412, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_split_node
    _ _ _ root_split_receipt

#print axioms root_split_receipt
#print axioms root_split
end D5.S3.Quantum.Entanglement.EJM.TransientHardSplit
