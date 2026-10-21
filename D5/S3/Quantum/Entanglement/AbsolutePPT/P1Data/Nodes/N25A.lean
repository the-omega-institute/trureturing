/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Nodes/N25A
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Nodes/N25A
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: none
   digest: Ordered concatenation of the complete literal forest; no check success is asserted. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25AChunk00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25AChunk01
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25AChunk02
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25AChunk03
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
def nodes : Array Node :=
  (nodes_chunk_0.toList ++
    nodes_chunk_700.toList ++
    nodes_chunk_1400.toList ++
    nodes_chunk_2100.toList).toArray
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
