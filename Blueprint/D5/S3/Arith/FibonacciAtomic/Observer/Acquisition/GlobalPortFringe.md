# A terminal fringe identifies global ports

## Abstract

The maximal ray in one physical direction and a terminal side probe identify a single global correspondence.

The source is the existing free ordered magma on Boolean leaves, with true denoting alpha and false denoting beta. Its specified substitution sends alpha to beta, beta to the ordered pair of beta and alpha, and preserves every original pair. Semantic address false is left and true is right. Physical false names a and physical true names b. One equivalence pi from Boolean physical names to Boolean semantic directions is applied letterwise at every branch. It is fixed across the entire tree, including newly created branches.

**Definition 1.1 (The actual directional height).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.spineHeight`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.spineHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a leaf the height is zero. On a pair it is one plus the height of the child in direction d. This recursively defined mathematical quantity concerns the actual finite tree. It is not an acquired operand or a height promised to a controller.

**Definition 1.2 (Presence under one global correspondence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalPresence`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalPresence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pi, physical word w and actual tree v, physicalPresence(pi,w,v) is true exactly when the existing total readout at the letterwise translated word map(pi,w) is not absent. Alpha, beta and branch all count as present. False means absent. Words beyond a leaf remain legal observations with a false presence bit.

**Definition 1.3 (The mathematical physical a-height).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalHeight`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

physicalHeight(pi,v) is spineHeight(pi(false),v). The theorem identifies it as the actual maximum of all natural lengths s whose physical a-power is present, and also identifies that set with the complete initial interval through this height.

**Theorem 1.4 (Complete maximum and orientation relation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.global_port_fringe`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.global_port_fringe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original source u, every natural j at least two, and every Boolean equivalence pi, put v equal to the actual 2j-fold substitution of u and h equal to physicalHeight(pi,v). Then h is a greatest element of the set of s with physicalPresence(pi,a repeated s times,v)=true. For every natural s, that bit is true if and only if s is at most h. Both bounds hold: h is at least two and at most 2j plus the original leaf count minus one. At the single word consisting of h minus two copies of a followed by b and a, the physical presence bit is false if and only if pi(a) is left, and true if and only if pi(a) is right. All statements concern this same actual v and the same global pi.

The native source, substitution, total address readout and subtree geometry are the existing GenealogicalFiberTransport, ActualTreeReadoutAcquisition and ActualLeafHistoryRigidity structures. Atomic reachability is reused directly from NativeRankedNavigationCompiler.atomic_navigation, and the pure right-ray threshold is reused from NativeBirthVectorDecoder.pathThreshold_allTrue. The path-cost lower bound for the threshold follows by direct projection of the original FiniteSourceMass.threshold_last formula. The additional relation is the terminal probe at the actual maximal ray for every original tree, together with its maximum specification and original-leaf bound. The proof does not claim that the reused atomic suppliers are new mathematics.

The atomic navigation theorem assigns weight one to a left edge and weight two to a right edge, and enforces that every traversed parent is a branch. Applied to a pure ray, it gives height m minus one on the left and floor(m/2) on the right in the m-fold image of alpha, for positive m. Applied to the side suffix after two fewer ray edges, its branch threshold is s plus four for a left ray of length s and twice s plus three for a right ray. For the images at indices 2j and 2j plus one, these inequalities give respectively absence and presence. Beta is the one-step image of alpha, so both original labels use this same supplier.

Induction over the arbitrary original tree then preserves every original branch. Passing through its selected child adds one to the maximal ray height and prepends that same direction to the side probe. Because each terminal replacement already has height at least two, natural subtraction by two commutes with this extension. The nonempty sibling contributes at least one original leaf, giving the original-leaf-count upper bound. The separate directional presence induction proves membership at the maximum and excludes every longer power. The equivalence sends the other physical name to the opposite semantic direction, turning the semantic side word into the literal physical word ba.

The relation includes singleton alpha and beta originals, j equal to two, both global correspondences, all finite ordered shapes, repeated equal subtrees and all-alpha originals. Neither a supplied original leaf address nor an orientation or recovery law is a hypothesis. The height is defined from the actual register solely as a mathematical quantity. This structural result specifies no installed acquisition procedure, paid call bound, authority, storage, physical duration, root acquisition or controller continuation. Independent local swaps do not satisfy its one-global-correspondence premise.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.global_port_fringe`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalHeight`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.physicalPresence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe.spineHeight`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass](../../Geometry/FiniteSourceMass.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder](../NativeBirthVectorDecoder.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler](../NativeRankedNavigationCompiler.md)
