# Context Depth Boundary

## Abstract

Every finite depth misses a distinction in a pair of stopped chains and fails to preserve their unary update.

For each natural k, the state carrier is Bool times Fin (k+2). Its two branches are the disjoint chains a_0 through a_(k+1) and b_0 through b_(k+1). The single total unary operation increases the position by one and stops at k+1. Only a_(k+1) has readout true; all other states read false. Every generator is this unary operation, so finite words give exactly the actual one-hole contexts, including the identity.

**Theorem 1.1 (Agreement, separation and failure of stability at every depth).**

Lean statement: `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.stopped_chain_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.stopped_chain_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, the starts a_0 and b_0 agree on every word of length at most k and on every actual context denoted by such a word. A word of length k+1 gives some true and some false respectively. Their successors already disagree at depth k. The calculation holds for every initial branch and position: a word of length n preserves the branch and changes position i to min(i+n,k+1). It also covers k=0.

**Theorem 1.2 (Neither completeness nor operation stability has a designated finite depth).**

Lean statement: `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.depth_adequacy_refutation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.depth_adequacy_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DepthAdequacyClaim says that some k has complete depth-k observations on Chain k, or some k has an operation-stable depth-k relation on Chain k. The theorem negates this whole disjunction. The starts refute completeness and their successors refute stability independently, for each k. Every distinguishing context remains finite; the family quantifies over finite depths.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.depth_adequacy_refutation`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.stopped_chain_boundary`
- Dependency: [D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts](StrictOneHoleContexts.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization](../../ObserverMemory/Algorithms/ControlledSignatureStabilization.md)
