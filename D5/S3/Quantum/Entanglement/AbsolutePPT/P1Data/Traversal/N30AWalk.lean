/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30AWalk
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30AWalk
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30AWalk.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart08
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
theorem checked_walk : walk nodes nodes.size (nodes.size-1) = List.range nodes.size := by
  change walk nodes 567 566 = List.range 567
  rw [List.range_eq_range']
  exact traversal_566 567 (by decide +kernel)
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
