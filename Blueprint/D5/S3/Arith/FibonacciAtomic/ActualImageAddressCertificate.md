# Exact Address Certificates for Actual Tree Images

## Abstract

Alpha leaf queries give exact positive certificates for actual Fibonacci tree images.

Sources are the existing nonempty ordered full binary trees with alpha and beta leaves. The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. Composition c counts alpha and beta leaves. Paths reuse the frozen ActualTreeReadoutAcquisition.Address type of finite Boolean lists, including the empty root address. Endpoint observations use its Reply and address-first readout; complete leaf sets use ActualImageSevenLeafSeparation.leafAddresses. Leaf labels use true for alpha and false for beta.

**Theorem 1.1 (Sharp cardinality and depth).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies (\forall h \in Nat, (((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(Address\right), (\operatorname{S}\left(3 \cdot k, V, h, R\right)))) \land ((\operatorname{D}\left(V\right) \leq h) \implies (\exists R \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, R\right)) \land (\operatorname{card}\left(R\right) = \operatorname{a}\left(V\right))))) \land (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \implies (\operatorname{a}\left(V\right) \leq \operatorname{card}\left(Q\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All k and h are natural numbers, V is a complete source tree, and Q is a finite set of addresses. I(d) denotes ActualImage(d), a(V) is the first component of c(V), D(V) is height(V), and S(d,V,h,Q) abbreviates Sound(d,V,h,Q), including the depth window. Thus below the maximum leaf depth there is no sound certificate; at or above it the minimum cardinality is exactly a(V).

Every twice-substituted leaf block has an alpha descendant below each of its internal nodes. Matching all alpha endpoints forces every branch of V to remain present in a competitor. Equal total leaf and alpha counts then force the whole ordered tree and all its labels to agree. The alpha address set therefore attains the upper bound.

Each alpha leaf is the right endpoint of a terminal pair (beta,alpha). Swapping either such pair to (alpha,beta) preserves composition and changes only its two endpoint observations. The new left alpha leaf excludes the competitor from the substitution image. Every sound query set must meet each endpoint pair, and these pairs are disjoint. A deepest pair supplies the obstruction when the path window is too shallow.

Certificate complexity and lower bounds from disjoint sensitive blocks are classical, as in Nisan's CREW PRAMs and Decision Trees (1991) and Buhrman and de Wolf's Complexity Measures and Decision Tree Complexity: A Survey (2002). The exact cardinality for these actual substitution images with fixed composition is the tree-specific conclusion.

**Theorem 1.2 (Unique optimal certificates and the complete leaf frontier).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies ((\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies (((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \land (\operatorname{card}\left(Q\right) = \operatorname{a}\left(V\right))) \Leftrightarrow (Q = \operatorname{A}\left(V\right))))))) \land (\forall h \in Nat, (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \Leftrightarrow (\operatorname{L}\left(V\right) \subseteq Q))))) \land (\forall h \in Nat, ((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, R\right)) \land (\operatorname{U}\left(3 \cdot k, V, R\right)))))) \land (\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies ((\operatorname{W}\left(h, \operatorname{L}\left(V\right)\right)) \land (\operatorname{U}\left(3 \cdot k, V, \operatorname{L}\left(V\right)\right)) \land (\operatorname{card}\left(\operatorname{L}\left(V\right)\right) = \operatorname{n}\left(V\right)) \land (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \implies ((\operatorname{n}\left(V\right) \leq \operatorname{card}\left(Q\right)) \land ((\operatorname{card}\left(Q\right) = \operatorname{n}\left(V\right)) \Leftrightarrow (Q = \operatorname{L}\left(V\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least one, V belongs to I(3 times k). Write A(V) for its alpha addresses, L(V) for all its leaf addresses, a(V) for its alpha count and n(V) for its total leaf count. W(h,Q) means Within(h,Q), and U(d,V,Q) means UnSound(d,V,Q). At or above D(V), the complete leaf frontier is the unique minimum certificate without a composition promise.

Three substitution steps give strictly more beta leaves than alpha leaves. If a sound set of a(V) queries omits an alpha leaf, it also omits a beta leaf. Exchanging those labels preserves composition and all queried results. If the chosen beta is the alpha leaf's left sibling, the exchange puts an alpha on the left. Otherwise the old terminal pair becomes (beta,beta). Both possibilities violate the structure of a twice-substituted tree.

Without a composition promise, omitting any leaf permits the frozen flip operation. The source_foundation theorem excludes that flipped tree from the third image and supplies unchanged readouts at every other address. Every image at depth 3k is a third image. Conversely, the same frozen theorem reconstructs a complete ordered tree from its labeled leaf frontier.

The shallow-window obstruction follows from the fixed-composition certificate theorem. At or above that depth, all n(V) leaves are available, and the complete-leaf condition gives both the lower bound and uniqueness. The exact uniqueness and complete-leaf equivalence are specific to these substitution images; general decision-tree certificate complexity supplies neighboring background.

**Theorem 1.3 (Sharp leaf budget above a height).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall h \in Nat, (((\operatorname{D}\left(\operatorname{A}\left(3 \cdot k\right)\right) = 3 \cdot k - 1) \land (\operatorname{D}\left(\operatorname{B}\left(3 \cdot k\right)\right) = 3 \cdot k) \land (\operatorname{c}\left(\operatorname{A}\left(3 \cdot k\right)\right) = (\operatorname{F}\left(3 \cdot k - 1\right), \operatorname{F}\left(3 \cdot k\right))) \land (\operatorname{c}\left(\operatorname{B}\left(3 \cdot k\right)\right) = (\operatorname{F}\left(3 \cdot k\right), \operatorname{F}\left(3 \cdot k + 1\right))) \land (\operatorname{n}\left(\operatorname{A}\left(3 \cdot k\right)\right) = \operatorname{F}\left(3 \cdot k + 1\right)) \land (\operatorname{n}\left(\operatorname{B}\left(3 \cdot k\right)\right) = \operatorname{F}\left(3 \cdot k + 2\right)) \land (\operatorname{F}\left(3 \cdot k + 2\right) = \operatorname{F}\left(3 \cdot k + 1\right) + \operatorname{F}\left(3 \cdot k\right)) \land (\operatorname{F}\left(3 \cdot k + 2\right) < 2 \cdot \operatorname{F}\left(3 \cdot k + 1\right))) \land (\forall X \in Source, ((X \in \operatorname{I}\left(3 \cdot k\right)) \implies ((h < \operatorname{D}\left(X\right)) \implies (\operatorname{C}\left(3 \cdot k, h\right) \leq \operatorname{n}\left(X\right))))) \land (\operatorname{V}\left(3 \cdot k, h\right) \in \operatorname{I}\left(3 \cdot k\right)) \land (h < \operatorname{D}\left(\operatorname{V}\left(3 \cdot k, h\right)\right)) \land (\operatorname{sub}\left(\operatorname{V}\left(3 \cdot k, h\right), \operatorname{r}\left(3 \cdot k, h\right)\right) = \operatorname{some}\left(J\right)) \land (\neg (\operatorname{W}\left(3 \cdot k, h\right) \in \operatorname{I}\left(3 \cdot k\right))) \land (\operatorname{c}\left(\operatorname{W}\left(3 \cdot k, h\right)\right) = \operatorname{c}\left(\operatorname{V}\left(3 \cdot k, h\right)\right)) \land (\forall u \in Address, ((\operatorname{length}\left(u\right) \leq h) \implies (\operatorname{readout}\left(u, \operatorname{W}\left(3 \cdot k, h\right)\right) = \operatorname{readout}\left(u, \operatorname{V}\left(3 \cdot k, h\right)\right)))) \land (\operatorname{n}\left(\operatorname{V}\left(3 \cdot k, h\right)\right) = \operatorname{C}\left(3 \cdot k, h\right)) \land ((3 \cdot k - 1 \leq h) \implies ((\operatorname{c}\left(\operatorname{V}\left(3 \cdot k, h\right)\right) = (\operatorname{F}\left(3 \cdot k - 1\right) \cdot \operatorname{m}\left(3 \cdot k, h\right) + \operatorname{F}\left(3 \cdot k\right), \operatorname{F}\left(3 \cdot k\right) \cdot \operatorname{m}\left(3 \cdot k, h\right) + \operatorname{F}\left(3 \cdot k + 1\right))) \land (\operatorname{sub}\left(\operatorname{V}\left(3 \cdot k, h\right), \operatorname{R}\left(\operatorname{m}\left(3 \cdot k, h\right)\right)\right) = \operatorname{some}\left(\operatorname{B}\left(3 \cdot k\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.heightFrontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural k at least one put d=3k, A=rho iterated d times on alpha and B=rho iterated d times on beta. F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. Write a=F(d+1), b=F(d+2), and n(X) for the total number of leaves. The height D counts edges. The budget C(d,h) is a when h is at most d-2, and b plus a times m otherwise, where m=h+1-d uses natural truncated subtraction. Thus at h=d-1 the value of m is zero.

Let U(0)=beta and U(m+1)=(alpha,U(m)). Define V(d,h)=A in the low range and rho iterated d times on U(m) in the high range. Define r(d,h) as d-2 left steps in the low range and m right steps followed by d-1 left steps in the high range. The subtree at r is J=(beta,alpha). Let W(d,h) replace that subtree by (alpha,beta). In the formula c is composition, I is the actual image, sub is the addressed subtree, some is the present-subtree constructor and R(m) is the address of m right steps.

Each source leaf becomes one A or B block. Every sibling subtree along a source path contains at least a output leaves. Induction on the source gives a lower bound a for every image and b plus a times (D-d) whenever its height D is at least d. The strict relation b<2a handles a deepest alpha block as well as a deepest beta block. The right comb attains the high bound, with its beta block at R(m).

Swapping the specified terminal pair preserves exact composition and changes only the two leaf labels at depths above h. Every endpoint observation within the window therefore agrees, including branches and absent endpoints. The left alpha leaf excludes W from the actual image. The universal lower bound together with the explicit attaining image characterizes the minimum leaf budget over images whose height exceeds h.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.heightFrontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddresses](ActualImageAddresses.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
