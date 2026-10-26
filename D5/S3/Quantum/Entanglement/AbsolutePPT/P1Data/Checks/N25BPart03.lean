/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_768,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_784,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_800,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_816,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_832,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_848,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_864,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N25BPart03.checked_nodes_880
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
theorem checked_nodes_768 : ∀ k : Fin 16, NodeOK 25 true nodes (768+k.val) := by decide +kernel

theorem checked_nodes_784 : ∀ k : Fin 16, NodeOK 25 true nodes (784+k.val) := by decide +kernel

theorem checked_nodes_800 : ∀ k : Fin 16, NodeOK 25 true nodes (800+k.val) := by decide +kernel

theorem checked_nodes_816 : ∀ k : Fin 16, NodeOK 25 true nodes (816+k.val) := by decide +kernel

theorem checked_nodes_832 : ∀ k : Fin 16, NodeOK 25 true nodes (832+k.val) := by decide +kernel

theorem checked_nodes_848 : ∀ k : Fin 16, NodeOK 25 true nodes (848+k.val) := by decide +kernel

theorem checked_nodes_864 : ∀ k : Fin 16, NodeOK 25 true nodes (864+k.val) := by decide +kernel

theorem checked_nodes_880 : ∀ k : Fin 3, NodeOK 25 true nodes (880+k.val) := by decide +kernel
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
