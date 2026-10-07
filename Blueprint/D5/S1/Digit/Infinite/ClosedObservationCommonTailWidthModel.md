# The Complete Closed Observation Model

## Abstract

Actual legal addresses, closed observations and the complete endpoint graph.

**Definition 1.1 (The reciprocal golden ratio).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.t`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.t` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

t is the reciprocal of the golden ratio, equivalently (sqrt(5) - 1)/2.

**Definition 1.2 (The three-bit contraction).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.g`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

g = t^3 is the contraction magnitude. A source step deletes exactly three individual bits.

**Definition 1.3 (The critical radius).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lambda`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lambda` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The critical closed observation radius is lambda = t^2/10.

**Definition 1.4 (Guard intervals).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateInterval`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The incoming guards zero and one have closed scalar intervals I_0 = [-1, 1+t] and I_1 = [-1, t], respectively.

**Definition 1.5 (Actual guard restrictions).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateAddress`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An address is an infinite Boolean stream without adjacent ones. Incoming guard one requires its first bit to be zero; incoming guard zero imposes no additional restriction.

**Definition 1.6 (Individual-bit shifts).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.bitShift`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.bitShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bitShift(x,n) deletes the lowest n bits of the actual address x and retains the no-adjacent-ones property.

**Definition 1.7 (The source clock).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.originalT`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.originalT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(x) = bitShift(x,3). Cylinder padding never changes this deletion clock.

**Definition 1.8 (The actual subsequent guard).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.actualGuard`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.actualGuard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time zero the guard is the specified incoming guard. At positive window time j it is bit 3j-1 of the original address.

**Definition 1.9 (Legal windows).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Label`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A label is a legal Boolean word of length three, read from low to high, without adjacent ones.

**Definition 1.10 (Actual window extraction).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.window`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Window j consists of bits 3j, 3j+1 and 3j+2 of the same actual address.

**Definition 1.11 (The null window).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.nullLabel`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.nullLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The null label is the three-bit word 000.

**Definition 1.12 (The label three).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.threeLabel`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.threeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label three is the three-bit word 010.

**Definition 1.13 (The label two).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoLabel`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label two is the three-bit word 100.

**Definition 1.14 (The label five).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.fiveLabel`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.fiveLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label five is the three-bit word 001.

**Definition 1.15 (The label twenty-five).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoFiveLabel`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoFiveLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label twenty-five is the single three-bit word 101.

**Definition 1.16 (Window translations).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offset`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For bits e_0,e_1,e_2, the translation is e_0 - t e_1 + t^2 e_2. The null, two, three, twenty-five and five labels have translations 0, 1, -t, 2-t and t^2.

**Definition 1.17 (Integral translation coordinates).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offsetInteger`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offsetInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the integral basis (1,phi), a window translation has coordinates (e_0+e_1+2e_2, -e_1-e_2), where phi=1+t.

**Definition 1.18 (The literal infinite window series).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.kappa`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar of an actual address x is the infinite sum over j of (-g)^j times the translation of its j-th three-bit window. Distinct addresses at scalar contacts remain distinct.

**Definition 1.19 (Outgoing guard).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.outgoing`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.outgoing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outgoing guard of a window is its highest bit.

**Definition 1.20 (The original guard graph).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lawful`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lawful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A window from guard s to s-prime is lawful when incoming guard one forces the lowest window bit to be zero, and s-prime is the highest window bit. Thus guard zero admits null, two and three to zero and twenty-five and five to one; guard one admits null and three to zero and five to one.

**Definition 1.21 (Closed forward branches).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.branch`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.branch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a legal window l, f_l(y)=Delta_l-g y, on the interval of its outgoing guard.

**Definition 1.22 (Inverse branches).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inverseBranch`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inverseBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse branch is F_l(x)=(Delta_l-x)/g.

**Definition 1.23 (Eventually null addresses).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.finiteTail`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.finiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite-tail address has all individual bits zero from some index onward, equivalently all sufficiently late windows are null.

**Definition 1.24 (The five instrument cuts).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cuts`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cuts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cuts are a=-t^2-lambda, b=g-3lambda, c=t-5lambda, d=2t-7lambda and e=2t+lambda.

**Definition 1.25 (Lower color endpoints).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellLower`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six lower endpoints, in color order zero through five, are -1,a,b,c,d,e.

**Definition 1.26 (Upper color endpoints).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellUpper`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six upper endpoints, in color order zero through five, are a,b,c,d,e,1+t.

**Definition 1.27 (Complete closed expansions).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.observation`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For budget b_0 and color i, E_i is the interval [max(-1,l_i-b_0), min(1+t,r_i+b_0)]. Whole closed endpoints are retained.

**Definition 1.28 (A fixed color instrument).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.instrument`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.instrument` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed function Q assigns every scalar in I_0 to one of six colors and assigns it within that color cell closure [l_i,r_i]. Each cut has one fixed assignment.

**Definition 1.29 (Actually attainable observations).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.exactObservation`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.exactObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact closed-budget relation for color i consists of x in I_0 for which a target y in I_0 has Q(y)=i and |x-y|<=b_0. It is distinct from the complete closed expansion.

**Definition 1.30 (The rational coefficient field).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inCoefficientField`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inCoefficientField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar belongs to Q(t) when it can be written a+b t with rational a and b.

**Definition 1.31 (The bounded-conjugate endpoint set).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpoints`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For integer q>=1 and radius R, B consists of scalars x in I_0 of the form embedding(z)/q, where z is a golden integer and the absolute value of embedding(conj(z))/q is at most R.

**Definition 1.32 (All construction seeds).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.seeds`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.seeds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seed set contains -1,1+t,t,-t^2,g,2t and every effective lower and upper endpoint of the six closed expansions.

**Definition 1.33 (Admissible construction parameters).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpointParameters`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpointParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters require q>=1, R>=0, every seed in B, and g times the absolute conjugate translation of every legal window at most (1-g)R. They assume neither graph finiteness nor address realization.

**Definition 1.34 (Singletons and adjacent closed intervals).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.basicPiece`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.basicPiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A guard-s basic piece [a,b] has endpoints in B intersect I_s, with a<=b, and either a=b or no point of B strictly between a and b. Entire adjacent closed intervals and all endpoint singletons are included.

**Definition 1.35 (Typed graph vertices).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Vertex`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is a guard together with the two endpoints of one basic closed piece. Its guard type is retained.

**Definition 1.36 (The set carried by a vertex).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.piece`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.piece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The piece carried by vertex (s,a,b) is the entire closed interval [a,b].

**Definition 1.37 (Exact all-containment edges).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.edge`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge from (s,P) with label l to (s-prime,Q) requires the lawful guard transition, P contained in f_l(I_s-prime), and Q contained in F_l(P). Both conditions concern the entire piece.

**Definition 1.38 (Whole-piece color permission).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.permits`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.permits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex permits color i exactly when its whole piece is contained in E_i.

**Definition 1.39 (Finite observed paths).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.ClosedPath`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.ClosedPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point path reads one color and has an empty source word. A step reads a color at its current vertex, follows one exact all-containment edge and continues an observed path. A path with n colors has n-1 edges, and its terminal color is already read.

**Definition 1.40 (Joint realization by one address).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.addressChain`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.addressChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite vertex and label chain is realized by one actual address when its first guard and scalar lie in the first piece, its first window is the first label, and its actual three-bit tail recursively realizes the remainder. A terminal point retains its actual guard and scalar.

**Definition 1.41 (All word and terminal-vertex pairs).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.histories`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.histories` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonempty color history, H contains every distinct terminal vertex and source word of a compatible path starting with guard zero. Path multiplicity is ignored. Before any color is read, every guard-zero vertex is paired with the empty word.

**Definition 1.42 (The global longest common prefix).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.globalLCP`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.globalLCP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonempty candidate family, select one word and take its longest prefix that is a prefix of every candidate word. The empty candidate family has the empty prefix.

**Definition 1.43 (The complete residual pair family).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.residuals`

*Formalization.* `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.residuals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R is the image of H under deletion of the same global longest common prefix from every candidate word, retaining the terminal vertex.

## References

- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.ClosedPath`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Label`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.Vertex`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.actualGuard`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.addressChain`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.basicPiece`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.bitShift`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.branch`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellLower`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cellUpper`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.cuts`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.edge`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpointParameters`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.endpoints`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.exactObservation`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.finiteTail`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.fiveLabel`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.g`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.globalLCP`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.histories`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inCoefficientField`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.instrument`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.inverseBranch`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.kappa`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lambda`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.lawful`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.nullLabel`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.observation`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offset`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.offsetInteger`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.originalT`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.outgoing`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.permits`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.piece`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.residuals`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.seeds`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateAddress`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.stateInterval`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.t`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.threeLabel`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoFiveLabel`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.twoLabel`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.window`
- Dependency: [D5/S0/Carrier/Units](../../../S0/Carrier/Units.md)
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
- Dependency: [D5/S1/Scale/Embedding](../../Scale/Embedding.md)
