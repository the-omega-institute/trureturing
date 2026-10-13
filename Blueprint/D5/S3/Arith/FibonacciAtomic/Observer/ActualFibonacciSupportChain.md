# Actual Fibonacci support chain

## Abstract

ActualFibonacciSupportChain

Sources are finite nonempty ordered Boolean trees. False addresses mean left and true addresses mean right. The initial source is the true-labelled leaf alpha, and substitution sends alpha to beta and beta to the ordered pair of beta and alpha. Pos denotes the set of all literal addresses whose native readout is not absent; it records only presence, without requiring agreement of leaf labels or branch replies.

**Theorem 1.1 (Strict inclusions and bounded support agreement).**

$$\forall k: Nat, ((1 \leq k) \implies (((\operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right) \subseteq \operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right)) \land (\operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right) \neq \operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right))) \land ((\operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right) \subseteq \operatorname{Pos}\left(\operatorname{mul}\left(\operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right), \operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right)\right)) \land (\operatorname{Pos}\left(\operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right) \neq \operatorname{Pos}\left(\operatorname{mul}\left(\operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right), \operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right)\right))) \land (\forall q: Address, ((\operatorname{length}\left(q\right) \leq k) \implies (((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right) \neq absent)) \land ((\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, 2k + 1, \operatorname{of}\left(true\right)\right)\right) \neq absent) \iff (\operatorname{readout}\left(q, \operatorname{mul}\left(\operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right), \operatorname{iterate}\left(substitution, 2k, \operatorname{of}\left(true\right)\right)\right)\right) \neq absent)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.actual_fibonacci_support_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k at least one, the support of the even orbit tree is strictly contained in the next odd support, which is strictly contained in the support of the ordered pair of two copies of the even tree. Both adjacent membership equivalences hold at every address of length at most k, including the empty address.

The orbit recurrence gives left and right children with ranks one and two below the parent rank. Induction on an arbitrary address proves that every address of length d is present at every orbit rank at least twice d. Applying this fact to rank twice k makes all three support bits equal to one throughout the stated radius. Original subtree transport gives the global inclusions. The words consisting of k minus one right edges followed by two left edges, and of k right edges followed by one left edge, respectively establish strictness.

The statement has no source-size bound, selected-word restriction or image-positivity premise. It concerns support bits on the actual trees; it gives neither complete reply equality nor a protocol cost bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.actual_fibonacci_support_chain`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](DelayedOriginalReadout.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](../SourceTransportCentralizer.md)
