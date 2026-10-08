# Complete endpoint graphs and joint actual paths

## Abstract

Complete endpoint graphs and joint actual paths.

**Theorem 1.1 (Composing exact bit deletions).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.bitShift_bitShift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.bitShift_bitShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual legal address and all natural m and n, deleting m bits and then n bits equals deleting m+n bits from that same address.

**Theorem 1.2 (Complete endpoint graphs and joint actual paths).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.closed_observation_graph_realization`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.closed_observation_graph_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every budget b_0 in Q(t) intersect [0,lambda], there exist an integer denominator q>=1 and a conjugate radius R>=0 satisfying the original endpoint parameters. The set B consists of embedding(z)/q in I_0 with conjugate absolute value at most R. All effective color endpoints, state endpoints and branch-domain endpoints are in B.

The pinned localization theorem clears the finitely many rational coefficients with one positive integer denominator. The integral unit g inverse preserves that lattice, while conjugate inverse updates contract by g. Bounds on both real embeddings bound both integer coordinates, proving B finite. For every admissible q,R, B is closed under every inverse branch whenever the image remains in I_0.

Every guard-typed endpoint singleton and every whole interval between adjacent endpoints is a vertex. The vertex set is finite. An endpoint selects its singleton; a nonendpoint selects the interval between its nearest endpoints. The selected piece is contained in every closed constraint containing the point whose endpoints belong to the same typed endpoint set.

The only edge rule requires a lawful guard transition, the whole current piece in the forward branch domain, and the whole successor piece in its inverse image. Every branch-contained piece has an inverse image equal to the union of all whole successor pieces contained there. All endpoint singletons remain in that union. Every vertex has an outgoing edge.

The guard-relative root images for three, null, five, two and twenty-five are [-1,t-1], [t-1,g], [g,t], [t,2t] and [2t,1+t], respectively. The outgoing guard is the highest window bit; guard one allows only three, null and five.

The address space consists of infinite Boolean streams without adjacent ones. Guard zero admits every legal stream; guard one requires the first bit to be zero. With t=(sqrt(5)-1)/2 and g=t^3, the literal three-bit window series kappa(x) equals -signedValue(x)/t^2. Its guard-relative ranges are exactly I_0=[-1,1+t] and I_1=[-1,t].

The first window l has translation Delta_l and kappa(x)=Delta_l-g kappa(Tx). The actual tail Tx satisfies the outgoing guard and deletes exactly three bits. Every lawful window and every legal outgoing tail have a unique lawful actual prepend. Same-coordinate endpoint addresses remain distinct.

For every finite closed observed path, every actual legal address z in its terminal guard whose scalar lies in its terminal piece lifts to one actual address x realizing all vertices and labels. Deleting exactly three times the source-word length from x yields that same z. A path with one observed color and no edges lifts z itself.

Every actual eventually-zero address has an integral golden scalar: kappa(x)=embedding(z) for some golden integer z. This implication does not assert that every integral scalar has an eventually-zero address.

## References

- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.bitShift_bitShift`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationGraphRealization.closed_observation_graph_realization`
- Dependency: [D5/S0/Carrier/Units](../../../S0/Carrier/Units.md)
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel](ClosedObservationCommonTailWidthModel.md)
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
- Dependency: [D5/S1/Scale/Embedding](../../Scale/Embedding.md)
