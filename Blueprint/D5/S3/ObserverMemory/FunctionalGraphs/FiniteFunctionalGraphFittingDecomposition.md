# Finite Functional-Graph Fitting Decomposition

## Abstract

A finite self-map transfer decomposes into a nilpotent transient part and its periodic core.

**Theorem 1.1 (The transfer splits into transient and periodic summands).**

$$\forall Y, \operatorname{Finite}(Y),\\\forall \tau: Y \to Y,\\\forall N \in \mathbb{N},\\\operatorname{range}(\tau^{N}) = \operatorname{periodicPts}(\tau) \Rightarrow (IsCompl(\ker transferOperator(\tau)^{N}, \operatorname{range}(transferOperator(\tau)^{N})) \land\\transientSubspace(\tau, N) = \ker transferOperator(\tau)^{N} \land\\IsNilpotent(transientTransfer(\tau, N)) \land\\\operatorname{range}(transferOperator(\tau)^{N}) = periodicCoreSubspace(\tau) \land\\Bijective(periodicCoreTransfer(\tau)) \land\\(\forall p: PeriodicCore(\tau), periodicCoreTransfer(\tau)(periodicBasisVector(\tau, p)) = periodicBasisVector(\tau, periodicCorePermutation(\tau, p))) \land\\(\forall v: Finsupp(Y, \mathbb{C}), linearEquivFunOnFinite(\mathbb{C}, \mathbb{C}, Y)(transferOperator(\tau)(v)) = linearMap(\mathbb{C}, \mathbb{C}, \tau)(linearEquivFunOnFinite(\mathbb{C}, \mathbb{C}, Y)(v)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.finite_functional_graph_fitting_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau be a self-map of a finite state carrier Y. The transfer operator sends the canonical basis vector at y to the basis vector at tau(y). Let N be any natural exponent whose iterate image is exactly the periodic-point set.

The transient subspace is constructed independently as the kernel of coefficient aggregation along the N-th iterate of tau. The theorem identifies it with the kernel of the corresponding transfer power before proving nilpotence of the restricted transfer.

The canonical linearEquivFunOnFinite map identifies finite-support vectors with the source carrier C^Y. A public intertwining clause shows that transferOperator agrees through this equivalence with Mathlib's function-space linearMap induced directly by tau.

The periodic-core subspace is the span of the canonical basis vectors at periodic points. The update induces the displayed canonical permutation of those points, and the restricted transfer acts on every periodic basis vector through exactly that permutation.

Repository search supplied the canonical transfer, periodic-core, and stable-image declarations but no theorem packaging all seven clauses. Pinned Mathlib supplies Finsupp range, finite-dimensional rank-nullity and complement criteria, iterated injectivity, the injective-surjective equivalence, and the periodic-point bijection applied directly by the proof.

## References

- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.finite_functional_graph_fitting_decomposition`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap](../InverseLimits/IdentityFuturePastGap.md)
- Dependency: [D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore](../InverseLimits/StableImagePeriodicCore.md)
- Dependency: [D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics](../InverseLimits/TraceRankCombinatorics.md)
