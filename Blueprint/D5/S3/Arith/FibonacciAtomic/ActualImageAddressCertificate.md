# Exact Address Certificates for Actual Tree Images

## Abstract

Alpha leaf queries give exact positive certificates for actual Fibonacci tree images.

Sources are the existing nonempty ordered full binary trees with alpha and beta leaves. The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. Composition c counts alpha and beta leaves. Paths reuse the frozen ActualTreeReadoutAcquisition.Address type of finite Boolean lists, including the empty root address. Endpoint observations use its Reply and address-first readout; complete leaf sets use ActualImageSevenLeafSeparation.leafAddresses. Leaf labels use true for alpha and false for beta. Alpha endpoints reuse ActualLeafHistoryRigidity.alphaLeaves, and addressed subtrees reuse its subtree with the address supplied first.

**Definition 1.1 (Maximum leaf depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.height`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.height` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Height is the height of the existing ordered shape decomposition. A leaf has height zero.

**Definition 1.2 (Actual substitution image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.ActualImage`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.ActualImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ActualImage(d) is the range of the d-fold native substitution on complete source trees.

**Definition 1.3 (Finite depth window).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Within`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Within` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Within(h,Q) means that each address in the finite set Q has length at most h.

**Definition 1.4 (Positive address certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Sound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Sound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sound(d,V,h,Q) means Within(h,Q) and: every complete tree U with c(U)=c(V) and readout(u,U)=readout(u,V) for every u in Q belongs to ActualImage(d). Exact composition is the only competitor promise, no prefix-closure condition on Q, and no adaptive or random query order.

**Definition 1.5 (Certificates without a composition promise).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.UnSound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.UnSound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every complete source U matching all queried endpoint results must belong to ActualImage(d). No composition or leaf-count constraint is placed on U; the depth window is imposed separately.

**Definition 1.6 (Subtree replacement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.replace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.replace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replacement changes the complete subtree at a valid address and retains the surrounding ordered tree. Invalid paths leave the tree unchanged.

**Definition 1.7 (Alpha coverage of branches).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.AlphaCovered`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.AlphaCovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every internal node has an alpha leaf descendant, recursively throughout the tree.

**Definition 1.8 (Right comb source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rightComb`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rightComb` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero comb is beta. The successor comb pairs alpha on the left with the preceding comb on the right, giving m alpha side leaves and one terminal beta at m right steps.

**Theorem 1.9 (Third-image inclusion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d at least three and every U in I(d), U is a third substitution image.

**Theorem 1.10 (Alpha cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.alpha_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.alpha_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete source t, the cardinality of alphaLeaves(t) equals the alpha component of composition(t).

**Theorem 1.11 (Leaf depth and beta cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_data`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source t, all its leaf addresses have length at most height(t), and its beta-filtered leaf set has cardinality equal to the beta composition component.

**Theorem 1.12 (Left alpha obstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.no_left_alpha`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.no_left_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every third image t and every address r, the left child of r cannot be an alpha leaf.

**Theorem 1.13 (Changing a leaf label).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_change`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing the leaf b at address s by c retains a leaf c there, adds composition(c) while removing composition(b), and preserves every readout away from s.

**Theorem 1.14 (Image alpha structure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one and every U in I(3k), U is AlphaCovered and each alpha address is the right child of a terminal pair(beta,alpha).

**Theorem 1.15 (Strict beta surplus).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.beta_surplus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.beta_surplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one and every V in I(3k), the beta composition count is strictly larger than its alpha count.

**Theorem 1.16 (Exchange composition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_composition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source V and two addresses s,t, the two leaf-change composition equations for alpha to beta at s and beta to alpha at t imply that the resulting composition equals composition(V).

**Theorem 1.17 (Exchange obstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_conflict`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_conflict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V,Wone,W be sources, s and t distinct addresses and s the right child of r. Suppose the subtree at r in V is pair(beta,alpha), t has beta reply in V, s is beta in Wone, t is alpha in W, Wone matches V away from s, and W matches Wone away from t. Then W cannot be a third image.

**Theorem 1.18 (Alpha addresses of a pair).**

$$\forall s \in Source, (\forall t \in Source, (\operatorname{alphaLeaves}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{union}\left(\operatorname{prefixLeft}\left(\operatorname{alphaLeaves}\left(s\right)\right), \operatorname{prefixRight}\left(\operatorname{alphaLeaves}\left(t\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.alpha_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alpha address set of pair(s,t) is the union of the left-prefixed alpha addresses of s and the right-prefixed alpha addresses of t. The two prefixes are disjoint.

**Theorem 1.19 (Sharp cardinality and depth).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies (\forall h \in Nat, (((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(Address\right), (\operatorname{S}\left(3 \cdot k, V, h, R\right)))) \land ((\operatorname{D}\left(V\right) \leq h) \implies (\exists R \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, R\right)) \land (\operatorname{card}\left(R\right) = \operatorname{a}\left(V\right))))) \land (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \implies (\operatorname{a}\left(V\right) \leq \operatorname{card}\left(Q\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All k and h are natural numbers, V is a complete source tree, and Q is a finite set of addresses. I(d) denotes ActualImage(d), a(V) is the first component of c(V), D(V) is height(V), and S(d,V,h,Q) abbreviates Sound(d,V,h,Q), including the depth window. Thus below the maximum leaf depth there is no sound certificate; at or above it the minimum cardinality is exactly a(V).

Every twice-substituted leaf block has an alpha descendant below each of its internal nodes. Matching all alpha endpoints forces every branch of V to remain present in a competitor. Equal total leaf and alpha counts then force the whole ordered tree and all its labels to agree. The alpha address set therefore attains the upper bound.

Each alpha leaf is the right endpoint of a terminal pair (beta,alpha). Swapping either such pair to (alpha,beta) preserves composition and changes only its two endpoint observations. The new left alpha leaf excludes the competitor from the substitution image. Every sound query set must meet each endpoint pair, and these pairs are disjoint. A deepest pair supplies the obstruction when the path window is too shallow.

Certificate complexity and lower bounds from disjoint sensitive blocks are classical, as in Nisan's CREW PRAMs and Decision Trees (1991) and Buhrman and de Wolf's Complexity Measures and Decision Tree Complexity: A Survey (2002). The exact cardinality for these actual substitution images with fixed composition is the tree-specific conclusion.

**Theorem 1.20 (Unique optimal certificates and the complete leaf frontier).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies ((\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies (((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \land (\operatorname{card}\left(Q\right) = \operatorname{a}\left(V\right))) \Leftrightarrow (Q = \operatorname{A}\left(V\right))))))) \land (\forall h \in Nat, (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \Leftrightarrow (\operatorname{L}\left(V\right) \subseteq Q))))) \land (\forall h \in Nat, ((h < \operatorname{D}\left(V\right)) \implies (\neg\exists R \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, R\right)) \land (\operatorname{U}\left(3 \cdot k, V, R\right)))))) \land (\forall h \in Nat, ((\operatorname{D}\left(V\right) \leq h) \implies ((\operatorname{W}\left(h, \operatorname{L}\left(V\right)\right)) \land (\operatorname{U}\left(3 \cdot k, V, \operatorname{L}\left(V\right)\right)) \land (\operatorname{card}\left(\operatorname{L}\left(V\right)\right) = \operatorname{n}\left(V\right)) \land (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{W}\left(h, Q\right)) \implies ((\operatorname{U}\left(3 \cdot k, V, Q\right)) \implies ((\operatorname{n}\left(V\right) \leq \operatorname{card}\left(Q\right)) \land ((\operatorname{card}\left(Q\right) = \operatorname{n}\left(V\right)) \Leftrightarrow (Q = \operatorname{L}\left(V\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least one, V belongs to I(3 times k). Write A(V) for its alpha addresses, L(V) for all its leaf addresses, a(V) for its alpha count and n(V) for its total leaf count. W(h,Q) means Within(h,Q), and U(d,V,Q) means UnSound(d,V,Q). At or above D(V), the complete leaf frontier is the unique minimum certificate without a composition promise.

Three substitution steps give strictly more beta leaves than alpha leaves. If a sound set of a(V) queries omits an alpha leaf, it also omits a beta leaf. Exchanging those labels preserves composition and all queried results. If the chosen beta is the alpha leaf's left sibling, the exchange puts an alpha on the left. Otherwise the old terminal pair becomes (beta,beta). Both possibilities violate the structure of a twice-substituted tree.

Without a composition promise, omitting any leaf permits the frozen flip operation. The source_foundation theorem excludes that flipped tree from the third image and supplies unchanged readouts at every other address. Every image at depth 3k is a third image. Conversely, the same frozen theorem reconstructs a complete ordered tree from its labeled leaf frontier.

The shallow-window obstruction follows from the fixed-composition certificate theorem. At or above that depth, all n(V) leaves are available, and the complete-leaf condition gives both the lower bound and uniqueness. The exact uniqueness and complete-leaf equivalence are specific to these substitution images; general decision-tree certificate complexity supplies neighboring background.

**Theorem 1.21 (Sharp leaf budget above a height).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall h \in Nat, (((\operatorname{D}\left(\operatorname{A}\left(3 \cdot k\right)\right) = 3 \cdot k - 1) \land (\operatorname{D}\left(\operatorname{B}\left(3 \cdot k\right)\right) = 3 \cdot k) \land (\operatorname{c}\left(\operatorname{A}\left(3 \cdot k\right)\right) = (\operatorname{F}\left(3 \cdot k - 1\right), \operatorname{F}\left(3 \cdot k\right))) \land (\operatorname{c}\left(\operatorname{B}\left(3 \cdot k\right)\right) = (\operatorname{F}\left(3 \cdot k\right), \operatorname{F}\left(3 \cdot k + 1\right))) \land (\operatorname{n}\left(\operatorname{A}\left(3 \cdot k\right)\right) = \operatorname{F}\left(3 \cdot k + 1\right)) \land (\operatorname{n}\left(\operatorname{B}\left(3 \cdot k\right)\right) = \operatorname{F}\left(3 \cdot k + 2\right)) \land (\operatorname{F}\left(3 \cdot k + 2\right) = \operatorname{F}\left(3 \cdot k + 1\right) + \operatorname{F}\left(3 \cdot k\right)) \land (\operatorname{F}\left(3 \cdot k + 2\right) < 2 \cdot \operatorname{F}\left(3 \cdot k + 1\right))) \land (\forall X \in Source, ((X \in \operatorname{I}\left(3 \cdot k\right)) \implies ((h < \operatorname{D}\left(X\right)) \implies (\operatorname{C}\left(3 \cdot k, h\right) \leq \operatorname{n}\left(X\right))))) \land (\operatorname{V}\left(3 \cdot k, h\right) \in \operatorname{I}\left(3 \cdot k\right)) \land (h < \operatorname{D}\left(\operatorname{V}\left(3 \cdot k, h\right)\right)) \land (\operatorname{sub}\left(\operatorname{V}\left(3 \cdot k, h\right), \operatorname{r}\left(3 \cdot k, h\right)\right) = \operatorname{some}\left(J\right)) \land (\neg (\operatorname{W}\left(3 \cdot k, h\right) \in \operatorname{I}\left(3 \cdot k\right))) \land (\operatorname{c}\left(\operatorname{W}\left(3 \cdot k, h\right)\right) = \operatorname{c}\left(\operatorname{V}\left(3 \cdot k, h\right)\right)) \land (\forall u \in Address, ((\operatorname{length}\left(u\right) \leq h) \implies (\operatorname{readout}\left(u, \operatorname{W}\left(3 \cdot k, h\right)\right) = \operatorname{readout}\left(u, \operatorname{V}\left(3 \cdot k, h\right)\right)))) \land (\operatorname{n}\left(\operatorname{V}\left(3 \cdot k, h\right)\right) = \operatorname{C}\left(3 \cdot k, h\right)) \land ((3 \cdot k - 1 \leq h) \implies ((\operatorname{c}\left(\operatorname{V}\left(3 \cdot k, h\right)\right) = (\operatorname{F}\left(3 \cdot k - 1\right) \cdot \operatorname{m}\left(3 \cdot k, h\right) + \operatorname{F}\left(3 \cdot k\right), \operatorname{F}\left(3 \cdot k\right) \cdot \operatorname{m}\left(3 \cdot k, h\right) + \operatorname{F}\left(3 \cdot k + 1\right))) \land (\operatorname{sub}\left(\operatorname{V}\left(3 \cdot k, h\right), \operatorname{R}\left(\operatorname{m}\left(3 \cdot k, h\right)\right)\right) = \operatorname{some}\left(\operatorname{B}\left(3 \cdot k\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.heightFrontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural k at least one put d=3k, A=rho iterated d times on alpha and B=rho iterated d times on beta. F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. Write a=F(d+1), b=F(d+2), and n(X) for the total number of leaves. The height D counts edges. The budget C(d,h) is a when h is at most d-2, and b plus a times m otherwise, where m=h+1-d uses natural truncated subtraction. Thus at h=d-1 the value of m is zero.

Let U(0)=beta and U(m+1)=(alpha,U(m)). Define V(d,h)=A in the low range and rho iterated d times on U(m) in the high range. Define r(d,h) as d-2 left steps in the low range and m right steps followed by d-1 left steps in the high range. The subtree at r is J=(beta,alpha). Let W(d,h) replace that subtree by (alpha,beta). In the formula c is composition, I is the actual image, sub is the addressed subtree, some is the present-subtree constructor and R(m) is the address of m right steps.

Each source leaf becomes one A or B block. Every sibling subtree along a source path contains at least a output leaves. Induction on the source gives a lower bound a for every image and b plus a times (D-d) whenever its height D is at least d. The strict relation b<2a handles a deepest alpha block as well as a deepest beta block. The right comb attains the high bound, with its beta block at R(m).

Swapping the specified terminal pair preserves exact composition and changes only the two leaf labels at depths above h. Every endpoint observation within the window therefore agrees, including branches and absent endpoints. The left alpha leaf excludes W from the actual image. The universal lower bound together with the explicit attaining image characterizes the minimum leaf budget over images whose height exceeds h.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.ActualImage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.AlphaCovered`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.UnSound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.Within`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.alpha_card`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.alpha_mul`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.beta_surplus`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_composition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.exchange_conflict`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.height`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.heightFrontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_positive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.image_structure`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_change`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.leaf_data`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.no_left_alpha`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.replace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rightComb`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.rigidity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](ActualLeafHistoryRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
