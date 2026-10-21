/- GID: D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_receipt_d14_i17412,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_node_d14_i17412,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_receipt_d15_i17411,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_node_d15_i17411,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_receipt_d16_i17410,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_node_d16_i17410,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_receipt_d17_i1305,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.split_node_d17_i1305
   digest: Original split receipts and equations at nodes 17412, 17411, 17410 and 1305 support the exact five-split Raw002 assembly. -/

/- Source-only integration candidate. No deployment or kernel acceptance.
Four remaining exact path-node equations; the accepted root equation is reused unchanged.
No prefix-free Accepted transfer.
-/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier.Raw002Tail442Checkpoint

theorem split_receipt_d14_i17412 :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 7 ⟨17412, by decide⟩)
      (EJMOriginalReplayAssembly.coordinate 14) (fun a : Fin 4 => (![⟨17402, by decide⟩, ⟨17407, by decide⟩, ⟨17409, by decide⟩, ⟨17411, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) = true := by
  decide +kernel

theorem split_node_d14_i17412 :
    EJMOriginalGlobalDAGData.nodes 7 ⟨17412, by decide⟩ =
      .split (EJMOriginalReplayAssembly.coordinate 14) (fun a : Fin 4 => (![⟨17402, by decide⟩, ⟨17407, by decide⟩, ⟨17409, by decide⟩, ⟨17411, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_split_node
    _ _ _ split_receipt_d14_i17412

#print axioms split_receipt_d14_i17412
#print axioms split_node_d14_i17412

theorem split_receipt_d15_i17411 :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 6 ⟨17411, by decide⟩)
      (EJMOriginalReplayAssembly.coordinate 15) (fun a : Fin 4 => (![⟨6279, by decide⟩, ⟨9516, by decide⟩, ⟨15585, by decide⟩, ⟨17410, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) = true := by
  decide +kernel

theorem split_node_d15_i17411 :
    EJMOriginalGlobalDAGData.nodes 6 ⟨17411, by decide⟩ =
      .split (EJMOriginalReplayAssembly.coordinate 15) (fun a : Fin 4 => (![⟨6279, by decide⟩, ⟨9516, by decide⟩, ⟨15585, by decide⟩, ⟨17410, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_split_node
    _ _ _ split_receipt_d15_i17411

#print axioms split_receipt_d15_i17411
#print axioms split_node_d15_i17411

theorem split_receipt_d16_i17410 :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 5 ⟨17410, by decide⟩)
      (EJMOriginalReplayAssembly.coordinate 16) (fun a : Fin 4 => (![⟨295, by decide⟩, ⟨1183, by decide⟩, ⟨4692, by decide⟩, ⟨1305, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) = true := by
  decide +kernel

theorem split_node_d16_i17410 :
    EJMOriginalGlobalDAGData.nodes 5 ⟨17410, by decide⟩ =
      .split (EJMOriginalReplayAssembly.coordinate 16) (fun a : Fin 4 => (![⟨295, by decide⟩, ⟨1183, by decide⟩, ⟨4692, by decide⟩, ⟨1305, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_split_node
    _ _ _ split_receipt_d16_i17410

#print axioms split_receipt_d16_i17410
#print axioms split_node_d16_i17410

theorem split_receipt_d17_i1305 :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 4 ⟨1305, by decide⟩)
      (EJMOriginalReplayAssembly.coordinate 17) (fun a : Fin 4 => (![⟨442, by decide⟩, ⟨442, by decide⟩, ⟨442, by decide⟩, ⟨986, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) = true := by
  decide +kernel

theorem split_node_d17_i1305 :
    EJMOriginalGlobalDAGData.nodes 4 ⟨1305, by decide⟩ =
      .split (EJMOriginalReplayAssembly.coordinate 17) (fun a : Fin 4 => (![⟨442, by decide⟩, ⟨442, by decide⟩, ⟨442, by decide⟩, ⟨986, by decide⟩] a : Fin EJMOriginalGlobalDAGData.Size)) :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_split_node
    _ _ _ split_receipt_d17_i1305

#print axioms split_receipt_d17_i1305
#print axioms split_node_d17_i1305

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier.Raw002Tail442Checkpoint
