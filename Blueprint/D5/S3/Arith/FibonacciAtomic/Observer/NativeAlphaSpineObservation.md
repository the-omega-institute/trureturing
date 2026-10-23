# Native alpha-spine observation locality

## Abstract

NativeAlphaSpineObservation

**Lemma 1.1 (The original reached hole).**

$$\forall p: Address, (\forall x: Source, (\operatorname{subtree}\left(p, \operatorname{E}\left(p, x\right)\right) = \operatorname{some}\left(x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original address p and actual Source x, the alpha-sibling path context E(p,x) reaches precisely x at p. The identity includes the empty path. Originally-present transport therefore applies at this hole at every natural epoch, even when a selected strict extension is initially absent.

**Theorem 1.2 (Three-source native observation boundary).**

$$\forall p: Address, (\forall k: Nat, ((1 \leq k) \implies ((\operatorname{readout}\left(p, \operatorname{E}\left(p, \operatorname{of}\left(true\right)\right)\right) = alpha) \land (\operatorname{readout}\left(p, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right) = beta) \land (\operatorname{readout}\left(p, \operatorname{E}\left(p, \operatorname{mul}\left(\operatorname{of}\left(true\right), \operatorname{of}\left(true\right)\right)\right)\right) = branch) \land (\forall q: Address, ((\neg (\operatorname{IsPrefix}\left(p, q\right))) \implies ((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(true\right)\right)\right)\right) = \operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right)) \land (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right) = \operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{mul}\left(\operatorname{of}\left(true\right), \operatorname{of}\left(true\right)\right)\right)\right)\right))))) \land (\forall q: Address, ((\operatorname{length}\left(q\right) \leq \operatorname{length}\left(p\right) + k) \implies (((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(true\right)\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right) \neq absent)) \land ((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{mul}\left(\operatorname{of}\left(true\right), \operatorname{of}\left(true\right)\right)\right)\right)\right) \neq absent))))) \land (\forall q: Address, ((\neg ((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(true\right)\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right) \neq absent))) \implies (\operatorname{length}\left(p\right) + k + 1 \leq \operatorname{length}\left(q\right)))) \land (\forall q: Address, ((\neg ((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{of}\left(false\right)\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2 \times k, \operatorname{E}\left(p, \operatorname{mul}\left(\operatorname{of}\left(true\right), \operatorname{of}\left(true\right)\right)\right)\right)\right) \neq absent))) \implies (\operatorname{length}\left(p\right) + k + 1 \leq \operatorname{length}\left(q\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_observation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sources form FreeMagma Bool: finite nonempty ordered Boolean trees with source leaves alpha=of(true) and beta=of(false). Addresses are finite Boolean lists, with false=L and true=R. The readout values alpha, beta, branch, and absent are replies, distinct from source trees. Write rho for substitution, which sends alpha to beta, beta to mul(beta,alpha), and mul(x,y) to mul(rho(x),rho(y)). For every address p, the alpha-spine source is defined by E([],x)=x, E(L::p,x)=mul(E(p,x),alpha), and E(R::p,x)=mul(alpha,E(p,x)).

The original sources E(p,alpha), E(p,beta), and E(p,mul(alpha,alpha)) have replies alpha, beta, and branch at p. Their current sources are obtained by applying rho 2k times. At every arbitrary address q for which p is not a prefix of q, the current raw replies agree. This includes proper ancestors of p and every divergent continuation; equality of these replies does not assert equality of the corresponding subtrees.

For a query q=p++r inside the prefix cone, the current readout of E(p,x) equals the readout at r of rho iterated 2k on x. Writing T(j)=rho iterated j on alpha, the three transported fillings are T(2k), T(2k+1), and mul(T(2k),T(2k)). For k at least one, the Fibonacci support chain gives equal non-absence bits at every suffix of length at most k. Combining this with raw reply equality outside the cone gives both adjacent support equivalences at every arbitrary q of length at most |p|+k. Each adjacent support distinction therefore requires |q| at least |p|+k+1.

The bounds include p=[] and k=1 and quantify over all finite addresses. Inside the prefix cone, equal non-absence bits do not assert equal raw replies or equal subtrees. The conclusion concerns literal query length; it supplies no protocol optimum or extension to a fourth source.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_observation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery](ActualCutPartitionRecovery.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain](ActualFibonacciSupportChain.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
