# Exact Address Certificates for Actual Tree Images

## Abstract

Alpha leaf queries give exact positive certificates for actual Fibonacci tree images.

Sources are the existing nonempty ordered full binary trees with alpha and beta leaves. The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. Composition c counts alpha and beta leaves. Paths reuse the existing FiniteDescription type of finite Boolean lists, including the empty root address. Leaf labels use true for alpha and false for beta.

**Theorem 1.1 (Sharp cardinality and depth).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies (\forall h \in Nat, (((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(FiniteDescription\right), (\operatorname{S}\left(3 \cdot k, V, h, R\right)))) \land ((\operatorname{D}\left(V\right) \leq h) \implies (\exists R \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{S}\left(3 \cdot k, V, h, R\right)) \land (\operatorname{card}\left(R\right) = \operatorname{a}\left(V\right))))) \land (\forall Q \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \implies (\operatorname{a}\left(V\right) \leq \operatorname{card}\left(Q\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All k and h are natural numbers, V is a complete source tree, and Q is a finite set of addresses. I(d) denotes ActualImage(d), a(V) is the first component of c(V), D(V) is height(V), and S(d,V,h,Q) abbreviates Sound(d,V,h,Q), including the depth window. Thus below the maximum leaf depth there is no sound certificate; at or above it the minimum cardinality is exactly a(V).

Every twice-substituted leaf block has an alpha descendant below each of its internal nodes. Matching all alpha endpoints forces every branch of V to remain present in a competitor. Equal total leaf and alpha counts then force the whole ordered tree and all its labels to agree. The alpha address set therefore attains the upper bound.

Each alpha leaf is the right endpoint of a terminal pair (beta,alpha). Swapping either such pair to (alpha,beta) preserves composition and changes only its two endpoint observations. The new left alpha leaf excludes the competitor from the substitution image. Every sound query set must meet each endpoint pair, and these pairs are disjoint. A deepest pair supplies the obstruction when the path window is too shallow.

Certificate complexity and lower bounds from disjoint sensitive blocks are classical, as in Nisan's CREW PRAMs and Decision Trees (1991) and Buhrman and de Wolf's Complexity Measures and Decision Tree Complexity: A Survey (2002). The exact cardinality for these actual substitution images with fixed composition is the tree-specific conclusion.

**Theorem 1.2 (Unique optimal certificates and the complete leaf frontier).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies ((\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies (\forall Q \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{W}\left(h, Q\right)) \implies (((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \land (\operatorname{card}\left(Q\right) = \operatorname{a}\left(V\right))) \Leftrightarrow (Q = \operatorname{A}\left(V\right))))))) \land (\forall h \in Nat, (\forall Q \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \Leftrightarrow (\operatorname{L}\left(V\right) \subseteq Q))))) \land (\forall h \in Nat, ((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{W}\left(h, R\right)) \land (\operatorname{U}\left(3 \cdot k, V, R\right)))))) \land (\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies ((\operatorname{W}\left(h, \operatorname{L}\left(V\right)\right)) \land (\operatorname{U}\left(3 \cdot k, V, \operatorname{L}\left(V\right)\right)) \land (\operatorname{card}\left(\operatorname{L}\left(V\right)\right) = \operatorname{n}\left(V\right)) \land (\forall Q \in \operatorname{Finset}\left(FiniteDescription\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \implies ((\operatorname{n}\left(V\right) \leq \operatorname{card}\left(Q\right)) \land ((\operatorname{card}\left(Q\right) = \operatorname{n}\left(V\right)) \Leftrightarrow (Q = \operatorname{L}\left(V\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least one, V belongs to I(3 times k). Write A(V) for its alpha addresses, L(V) for all its leaf addresses, a(V) for its alpha count and n(V) for its total leaf count. W(h,Q) means Within(h,Q), and U(d,V,Q) means UnSound(d,V,Q). At or above D(V), the complete leaf frontier is the unique minimum certificate without a composition promise.

Three substitution steps give strictly more beta leaves than alpha leaves. If a sound set of a(V) queries omits an alpha leaf, it also omits a beta leaf. Exchanging those labels preserves composition and all queried results. If the chosen beta is the alpha leaf's left sibling, the exchange puts an alpha on the left. Otherwise the old terminal pair becomes (beta,beta). Both possibilities violate the structure of a twice-substituted tree.

Without a composition promise, omitting any leaf permits a single label flip. An alpha-to-beta flip creates a terminal (beta,beta) pair. A beta-to-alpha flip cannot obey the rule that every alpha is the right leaf of a terminal (beta,alpha) pair. Conversely, matching the labeled complete leaf frontier forces equality of the ordered source trees, by recursively matching the two child frontiers.

The shallow-window obstruction follows from the fixed-composition certificate theorem. At or above that depth, all n(V) leaves are available, and the complete-leaf condition gives both the lower bound and uniqueness. The exact uniqueness and complete-leaf equivalence are specific to these substitution images; general decision-tree certificate complexity supplies neighboring background.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddresses](ActualImageAddresses.md)
