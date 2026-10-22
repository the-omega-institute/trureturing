/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02.checked_nodes_512,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02.checked_nodes_528,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02.checked_nodes_544,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Checks/N30APart02.checked_nodes_560
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
theorem checked_nodes_512 : ∀ k : Fin 16, NodeOK 30 false nodes (512+k.val) := by decide +kernel

theorem checked_nodes_528 : ∀ k : Fin 16, NodeOK 30 false nodes (528+k.val) := by decide +kernel

theorem checked_nodes_544 : ∀ k : Fin 16, NodeOK 30 false nodes (544+k.val) := by decide +kernel

theorem checked_nodes_560 : ∀ k : Fin 7, NodeOK 30 false nodes (560+k.val) := by decide +kernel
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
