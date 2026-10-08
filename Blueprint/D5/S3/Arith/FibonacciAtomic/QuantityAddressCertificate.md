# Quantity Address Certificates

## Abstract

Exact quantity and raw addresses determine the sharp positive certificate frontier.

Sources are the existing nonempty finite ordered full binary trees. The native substitution rho sends alpha to beta and beta to pair(beta,alpha), preserving ordered pairing. A(V) and B(V) are the original alpha and beta leaf-address sets; a(V) and b(V) are their cardinalities. The scalar m(V)=2a(V)+3b(V) uses GraftAffineClosure.quantity on the existing composition. I(d) is the range of rho iterated d times. D(V) is maximum leaf depth, with root depth zero. Addresses and all four raw replies reuse ActualTreeReadoutAcquisition. LL, LR and R denote the Boolean lists [false,false], [false,true] and [true]. Pairset(x,y) denotes their unordered two-element set.

**Definition 1.1 (Scalar soundness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.ScalarSound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.ScalarSound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(f,g,d,V,h,Q), for arbitrary natural weights f and g, means that every address in the finite set Q has length at most h, and every complete source U with f*a(U)+g*b(U)=f*a(V)+g*b(V) and matching raw replies at all addresses in Q lies in I(d). Competitors have only this exact scalar promise; their composition, number of leaves, shape and height are unrestricted. In the theorem below S(d,V,h,Q) denotes S(2,3,d,V,h,Q). For positive weights f<g, every nonempty subtree has weight at least f, with equality only for alpha. When g<2f, weight g occurs only for beta. When every branch of V has a beta descendant, matching all beta endpoints gives a weighted lower bound; equality forces the complete tree U to equal V.

**Definition 1.2 (Quantity soundness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.QuantitySound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.QuantitySound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

QuantitySound(d,V,h,Q) is S(2,3,d,V,h,Q), the weight pair used for the quantity frontier.

**Theorem 1.3 (Sharp frontier and all minimum sets).**

$$\forall k \in Nat, ((1 \leq k) \implies (\forall V \in Source, ((V \in \operatorname{I}\left(3 \cdot k\right)) \implies (\forall h \in Nat, ((1 \leq \operatorname{a}\left(V\right)) \land ((h < \operatorname{D}\left(V\right)) \implies (\neg \exists Q \in \operatorname{Finset}\left(Address\right), (\operatorname{S}\left(3 \cdot k, V, h, Q\right)))) \land ((\operatorname{D}\left(V\right) \leq h) \implies ((2 \leq \operatorname{a}\left(V\right)) \implies ((\operatorname{S}\left(3 \cdot k, V, h, \operatorname{B}\left(V\right)\right)) \land (\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \implies ((\operatorname{b}\left(V\right) \leq \operatorname{card}\left(Q\right)) \land ((\operatorname{card}\left(Q\right) = \operatorname{b}\left(V\right)) \Leftrightarrow (Q = \operatorname{B}\left(V\right))))))))) \land ((\operatorname{a}\left(V\right) = 1) \implies ((3 \cdot k = 3) \land (V = \operatorname{rhoCubed}\left(alpha\right)) \land (\operatorname{b}\left(V\right) = 2) \land ((\operatorname{D}\left(V\right) \leq h) \implies ((\forall Q \in \operatorname{Finset}\left(Address\right), ((\operatorname{S}\left(3 \cdot k, V, h, Q\right)) \implies ((2 \leq \operatorname{card}\left(Q\right)) \land ((\operatorname{card}\left(Q\right) = 2) \Leftrightarrow ((Q = \operatorname{Pairset}\left(LL, LR\right)) \lor (Q = \operatorname{Pairset}\left(LL, R\right)) \lor (Q = \operatorname{Pairset}\left(LR, R\right))))))) \land (\forall Q \in \operatorname{Finset}\left(Address\right), (((Q = \operatorname{Pairset}\left(LL, LR\right)) \lor (Q = \operatorname{Pairset}\left(LL, R\right)) \lor (Q = \operatorname{Pairset}\left(LR, R\right))) \implies (\operatorname{S}\left(3 \cdot k, V, h, Q\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k at least one, every V in I(3k) and every natural depth h, a(V) is positive. Below D(V) no quantity-sound query set exists. At or above D(V), when a(V) is at least two, the set B(V) is sound, all sound sets have at least b(V) addresses, and equality holds exactly for B(V).

If a(V)=1 then 3k=3 and V=rho cubed(alpha)=pair(pair(beta,alpha),beta), with two beta leaves. At or above its height all sound sets have at least two addresses. Exactly Pairset(LL,LR), Pairset(LL,R) and Pairset(LR,R) attain this bound, and each is sound.

Matching every beta leaf preserves the full branch skeleton. Any remaining alpha slot contains a nonempty subtree of quantity at least two, with equality only for alpha. Additivity and equality of total quantity force equality in every slot, so the complete competitor tree equals V.

Exchanging an omitted alpha and an omitted beta preserves quantity and excludes the resulting tree from the image. Thus a sound set contains every alpha or every beta address. If two beta addresses are omitted, replace one beta by alpha and the other by pair(alpha,alpha). The joint modification preserves quantity and changes replies only at the two beta addresses and the two immediate children of the expanded slot. Soundness forces a queried immediate child for each omitted beta. Those children are distinct and outside the original leaf set, giving the sharp cardinality bound.

The single-alpha case reduces to the unique single-alpha third image. The two mixed pairs fix two leaf slots and leave quantity three for the remaining slot, whose only nonempty realization is beta. The shallow-depth obstruction is the existing composition-preserving terminal-pair swap.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.QuantitySound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.ScalarSound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](ActualImageAlphaSeparation.md)
