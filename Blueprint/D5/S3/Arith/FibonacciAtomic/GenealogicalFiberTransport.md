# Composition Fibers and Fibonacci Genealogical Transport

## Abstract

Ordered tree shapes and their leaf labels determine exact composition fibers.

Sources are nonempty ordered full binary trees. True labels alpha and false labels beta. Their composition counts the two leaf labels. The Fibonacci step and quantity are M(a,b)=(b,a+b) and q(a,b)=2a+3b.

**Definition 1.1 (Actual sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source type is FreeMagma Bool, with the original ordered tree constructors.

**Definition 1.2 (Native substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.substitution`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.substitution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The magma homomorphism sends alpha to beta and beta to the ordered pair (beta,alpha).

**Definition 1.3 (Actual leaf composition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.composition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.composition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alpha has composition (1,0), beta has composition (0,1), and pairing adds compositions.

**Definition 1.4 (Composition fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Fiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fiber(v) consists of actual source trees whose composition equals v.

**Definition 1.5 (Catalan and binomial expression).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(a,b)=catalan(a+b-1) choose(a+b,a). Natural subtraction is truncated at zero.

**Definition 1.6 (Labels on a shape).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.TreeLabels`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.TreeLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf carries one Boolean label, and an internal node carries the labels of its left and right subshapes.

**Definition 1.7 (Assembling a source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.assemble`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.assemble` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assembling a shape with its leaf labels produces the actual ordered source tree.

**Definition 1.8 (Decomposing a source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.decompose`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.decompose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decomposition retains the ordered shape and every leaf label.

**Definition 1.9 (Shape and label equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.sourceEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.sourceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assembly and decomposition are inverse on all nonempty ordered sources.

**Definition 1.10 (Indexed leaf labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.labelsEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.labelsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Leaf labels are functions on the left-to-right leaf positions of a shape.

**Definition 1.11 (Complete indexed encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.indexedEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.indexedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual source corresponds to its ordered shape and its Boolean leaf-position function.

**Definition 1.12 (Shape and alpha positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.positionedEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.positionedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual source corresponds to its ordered shape and the subset of its alpha positions, using the existing supportEquiv.

**Definition 1.13 (Fixed-composition correspondence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a+b>=1, actual sources of composition (a,b) correspond to shapes with a+b-1 internal nodes and subsets of exactly a alpha positions.

**Definition 1.14 (Actual iterated substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberMap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map from Fiber(v) to Fiber(M^n v) sends a source to its n-th substituted tree.

**Definition 1.15 (Real uniform mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.uniformMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.uniformMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each tree in a nonempty fiber has mass 1/card(Fiber(v)).

**Definition 1.16 (Variation on one target fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.transportVariation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.transportVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compare the actual pushforward and the uniform target mass using one half of their finite absolute-difference sum.

**Theorem 1.17 (Exact hidden fibers and transport variation).**

$$\begin{gathered}(\forall a, b, ((1 \leq a + b) \implies ((\operatorname{Finite}\left(\operatorname{F}\left((a, b)\right)\right)) \land \\{}(\operatorname{card}\left(\operatorname{F}\left((a, b)\right)\right) = \operatorname{N}\left((a, b)\right)) \land \\{}(\operatorname{Nonempty}\left(\operatorname{F}\left((a, b)\right)\right)) \land \\{}(\forall t, ((t \in \operatorname{F}\left((a, b)\right)) \implies (\forall n, ((\operatorname{c}\left(\operatorname{rho}\left(n, t\right)\right) = \operatorname{M}\left(n, (a, b)\right)) \land \\{}(\operatorname{q}\left(\operatorname{c}\left(\operatorname{rho}\left(n, t\right)\right)\right) = \operatorname{q}\left(\operatorname{M}\left(n, (a, b)\right)\right)))))) \land \\{}(\forall n, ((\operatorname{Injective}\left(\operatorname{rhoFiber}\left((a, b), n\right)\right)) \land \\{}(\operatorname{card}\left(\operatorname{I}\left(n, (a, b)\right)\right) = \operatorname{N}\left((a, b)\right)) \land \\{}(\forall y, ((y \in \operatorname{F}\left(\operatorname{M}\left(n, (a, b)\right)\right)) \implies ((0 \leq \operatorname{P}\left(n, (a, b), y\right)) \land \\{}(0 \leq \operatorname{U}\left(\operatorname{M}\left(n, (a, b)\right), y\right))))) \land \\{}(\sum_{y \in \operatorname{F}\left(\operatorname{M}\left(n, (a, b)\right)\right)} \operatorname{P}\left(n, (a, b), y\right) = 1) \land \\{}(\sum_{y \in \operatorname{F}\left(\operatorname{M}\left(n, (a, b)\right)\right)} \operatorname{U}\left(\operatorname{M}\left(n, (a, b)\right), y\right) = 1) \land \\{}(\operatorname{TV}\left((a, b), n\right) = 1 - \frac{\operatorname{N}\left((a, b)\right)}{\operatorname{N}\left(\operatorname{M}\left(n, (a, b)\right)\right)}))) \land \\{}((2 \leq a + b) \implies (1 - \frac{1}{2}^{b} \leq \operatorname{TV}\left((a, b), 1\right))) \land \\{}(\operatorname{Tendsto}\left(n \mapsto \operatorname{TV}\left((a, b), n\right), atTop, \operatorname{nhds}\left(1\right)\right))))) \land \\{}(\operatorname{TV}\left((1, 1), 1\right) = \frac{2}{3})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All a,b,n are natural numbers, including zero. F(v) is the actual tree fiber, N(v) its Catalan and binomial expression, P_n(v,y) the existing preimage-sum pushforward applied to the actual fiber map and source uniform mass, and U(v,y) the uniform mass. M(n,v) denotes M^n v and rho(n,t) denotes rho^n t. TV(v,n) compares the pushed and uniform target masses. I_n(v) is the image of the actual fiber map rho_v^n. Every displayed sum ranges over the whole target fiber F(M^n v).

The substitution is injective because no image is the leaf alpha. The image of a beta leaf is the pair (beta,alpha), which cannot be the image of an internal node: its right child alpha is not an image. The remaining pairs decode recursively. Thus each positive pushforward mass has exactly one preimage, and the image has the cardinality of the source fiber.

The total variation splits into the image and its complement. The image contributes the difference between the reciprocal source and target cardinalities; the complement contributes the reciprocal target cardinality. The one-step bound follows from Catalan doubling after index one and monotonicity of the binomial coefficient. Under iteration, the total leaf count increases by at least one every two steps, and the target cardinality grows without bound. Its reciprocal tends to zero.

The shape count is the Catalan count in Stanley, Enumerative Combinatorics, Volume 2, section 6.2. The shape enumeration and the finite subset count use their corresponding mathlib results.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Fiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.Source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.TreeLabels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.assemble`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.composition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.decompose`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.fiberMap`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.indexedEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.labelsEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.positionedEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.sourceEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.substitution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.transportVariation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.uniformMass`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
- Dependency: [D5/S3/Entropy/Forgetting/CompletionEntropyMinimality](../../Entropy/Forgetting/CompletionEntropyMinimality.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/BinaryCharacterUniformInformationExactness](../../Fourier/CharacterSelection/BinaryCharacterUniformInformationExactness.md)
- Dependency: [D5/S3/Quantum/MultifactorCorrelationSectorDecomposition](../../Quantum/MultifactorCorrelationSectorDecomposition.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../TotalVariation/Pinsker.md)
