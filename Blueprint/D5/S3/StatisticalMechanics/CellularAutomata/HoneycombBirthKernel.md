# Birth polynomials of adjacent honeycomb cuts

## Abstract

Adjacent-cut birth polynomials and their normalized honeycomb kernels.

Here Vertex is Bool × ℤ × ℤ, x(v) and y(v) are its integer coordinate projections, and e is Lean's typeclass argument for decidable adjacency. Subtraction in tick and exponent expressions is truncated in ℕ. The symbol X denotes the polynomial indeterminate.

**Definition 1.1 (Adjacent-cut birth difference).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall a \in \mathbb{N}, d \in \mathbb{N},\; (\operatorname{delta}\left(G, a, d\right): \mathbb{Z}[X]) = \sum_{v \in \operatorname{omegaDomain}\left(a, d\right)} (\operatorname{ite}\left((\exists t \in \mathbb{N},\; \operatorname{Born}\left(G, \operatorname{omegaDomain}\left(a, d\right), \operatorname{A}\left(0, 0\right), t, v\right)), X^{\operatorname{min}_{t \in \mathbb{N} \mid \operatorname{Born}\left(G, \operatorname{omegaDomain}\left(a, d\right), \operatorname{A}\left(0, 0\right), t, v\right)}}, 0\right)) - \sum_{v \in \operatorname{omegaDomain}\left(a, d + 1\right)} (\operatorname{ite}\left((\exists t \in \mathbb{N},\; \operatorname{Born}\left(G, \operatorname{omegaDomain}\left(a, d + 1\right), \operatorname{A}\left(0, 0\right), t, v\right)), X^{\operatorname{min}_{t \in \mathbb{N} \mid \operatorname{Born}\left(G, \operatorname{omegaDomain}\left(a, d + 1\right), \operatorname{A}\left(0, 0\right), t, v\right)}}, 0\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each birth polynomial counts every retained vertex that is born with a monomial at its birth tick.

**Definition 1.2 (Birth indicator).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(\operatorname{Vertex}\right), t \in \mathbb{N}, v \in \operatorname{Vertex},\; (\operatorname{birthWeight}\left(G, D, t, v\right): \mathbb{Z}) = \operatorname{ite}\left(\operatorname{state}\left(G, D, \operatorname{A}\left(0, 0\right), t, v\right) = \operatorname{some}\left((t, 1)\right), 1, 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.birthWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is an integer, so the difference of two such weights can be negative.

**Definition 1.3 (Difference of birth indicators).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall a \in \mathbb{N}, d \in \mathbb{N}, t \in \mathbb{N}, v \in \operatorname{Vertex},\; (\operatorname{signedWeight}\left(G, a, d, t, v\right): \mathbb{Z}) = \operatorname{birthWeight}\left(G, \operatorname{omegaDomain}\left(a, d\right), t, v\right) - \operatorname{birthWeight}\left(G, \operatorname{omegaDomain}\left(a, d + 1\right), t, v\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.signedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orientation is the weight at cut d minus the weight at cut d+1.

**Theorem 1.4 (Coefficient over a common finite set).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall U \in \operatorname{Finset}\left(\operatorname{Vertex}\right), a \in \mathbb{N}, d \in \mathbb{N},\; (\operatorname{omegaDomain}\left(a, d\right) \subseteq U) \Rightarrow (\forall t \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{delta}\left(G, a, d\right), t\right) = \sum_{v \in U} (\operatorname{signedWeight}\left(G, a, d, t, v\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.coeff_delta_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U contains the larger cut domain. Vertices outside each cut contribute zero to its birth count.

At a positive multiple a of a dyadic strip width P, horizontal translation identifies the right strip with the height-P run after a delay of 2(a−P). On the left, the birth indicators for the two cuts agree.

**Theorem 1.5 (Dyadic copy of the adjacent-cut difference).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (((\operatorname{EarliestBirthIff}\left(G\right)) \Rightarrow (\forall b \in \mathbb{N}, a \in \mathbb{N}, c \in \mathbb{N},\; (0 < a) \Rightarrow ((2^{b} \mid a) \Rightarrow ((c + 1 \le 2^{b}) \Rightarrow (\operatorname{delta}\left(G, a, c\right) = X^{2 \cdot (a - 2^{b})} \cdot \operatorname{delta}\left(G, 2^{b}, c\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.adjacent_copy_of_earliest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph satisfies both the adjacency laws and the earliest-birth parity law. The same column c is used at both heights.

At neighboring cuts of an integral height, write τ=2a−d−1 for the removed layer's time. The potential 2τ−g+y changes by at most one along an edge before conversion to a natural. On the removed layer it equals the earliest possible touch time.

**Theorem 1.6 (Support of the signed birth indicator).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\forall a \in \mathbb{N}, d \in \mathbb{N},\; (d < a) \Rightarrow (\forall j \in \mathbb{N}, v \in \operatorname{Vertex},\; (\operatorname{signedWeight}\left(G, a, d, 2 \cdot a - d - 1 + j, v\right) \ne 0) \Rightarrow ((v \in \operatorname{omegaDomain}\left(a, d\right)) \land (\exists i \in \mathbb{N},\; (\operatorname{g}\left(v\right) = (2 \cdot a - d - 1: \mathbb{Z}) - (i: \mathbb{Z})) \land (i + \operatorname{Int.toNat}\left(\operatorname{y}\left(v\right)\right) \le j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.signedSupport_of_neighborLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion expands the private predicate SignedSupport. The layer time and the natural index i are cast to integers before taking their difference.

**Definition 1.7 (Normalized kernel coefficient).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall j \in \mathbb{N}, d \in \mathbb{N},\; (\operatorname{kernelEntry}\left(G, j, d\right): \mathbb{Z}) = \operatorname{coeff}\left(\operatorname{delta}\left(G, 2^{\operatorname{min}_{b \in \mathbb{N} \mid d < 2^{b}}}, d\right), 2 \cdot 2^{\operatorname{min}_{b \in \mathbb{N} \mid d < 2^{b}}} - d - 1 + j\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.kernelEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the least natural exponent b with d < 2^b, then read the coefficient after the removed layer’s delay.

**Theorem 1.8 (Coefficient at any eligible dyadic height).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right), e \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (((\operatorname{EarliestBirthIff}\left(G\right)) \Rightarrow (\forall b \in \mathbb{N}, d \in \mathbb{N}, j \in \mathbb{N},\; (d < 2^{b}) \Rightarrow (\operatorname{kernelEntry}\left(G, j, d\right) = \operatorname{coeff}\left(\operatorname{delta}\left(G, 2^{b}, d\right), 2 \cdot 2^{b} - d - 1 + j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.kernelEntry_eq_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any eligible dyadic height may be used with the same graph and parity law.

**Definition 1.9 (Kernel coefficient on the repository graph).**

$$\forall j \in \mathbb{N}, d \in \mathbb{N},\; (\operatorname{birthKernelEntry}\left(j, d\right): \mathbb{Z}) = \operatorname{kernelEntry}\left(\operatorname{honeycombGraph}, \operatorname{repositoryAdjacency}, j, d\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.birthKernelEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The specialized readout uses the existing honeycomb graph and its concrete adjacency decision procedure.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.adjacent_copy_of_earliest`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.birthKernelEntry`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.birthWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.coeff_delta_on`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.delta`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.kernelEntry`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.kernelEntry_eq_coeff`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.signedSupport_of_neighborLaws`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel.signedWeight`
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch](HoneycombFirstTouch.md)
