# Alpha Separation and Literal Two-Hole Equality

## Abstract

Sharp alpha separation and all literal two-hole equality cases of actual Fibonacci tree images.

Sources are nonempty finite ordered full binary trees with alpha and beta leaves. The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. I is the range of rho cubed on these complete sources. L(P) is the existing leaf-address set, with root-first Boolean paths: false means left and true means right. Composition counts alpha and beta leaves.

The leaf length n is FreeMagma.length. Shared leaves, unshared leaves, Nonconflict, E, A and C use ActualImageSevenLeafSeparation. Its seven_leaf_separation theorem supplies the exact address semantics and Theorem 30.4. A is pair(E,beta), C is pair(A,E), and E is pair(beta,alpha).

**Definition 1.1 (Directed alpha deficit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.delta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

delta(P,Q) is the cardinality of the set difference of the original alpha-leaf address sets. The prose notation μ(P) denotes the cardinality of the original alpha-leaf address set.

**Definition 1.2 (Two source holes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.TwoHole`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.TwoHole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Single-hole contexts reuse ActualLeafHistoryRigidity.OutputContext, its plug filling and its root-first holeAddress. The outer one-hole context leads to the lowest common ancestor. Its left and right one-hole contexts lead to the two distinct holes. A Boolean records their naming order. TwoHole.fill(J,X,Y) plugs the named trees into the left and right contexts and their pair into the outer context, so each tree is inserted exactly once and the entire outer context and each fixed sibling are retained. TwoHole.addresses gives two addresses with the same outer prefix and opposite next bits, and hence neither is a prefix of the other.

**Definition 1.3 (Canonical divergence frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.frontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.frontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Comparison is performed on complete preimages. Equal subtrees stop; two branches recurse into the ordered children; an atom-compound comparison records the current address.

**Definition 1.4 (Atomic-side hole count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.forwardCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.forwardCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

forwardCount(S,T) counts frontier holes whose S side is atomic and T side is compound.

**Definition 1.5 (Literal double-hole normal form).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.NormalForm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.NormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NormalForm(S,T) retains a complete source context J and y equal to beta or (alpha,alpha), with S=fill(J,beta,(alpha,y)) and T=fill(J,(alpha,y),beta). Its frontier is exactly the two named, mutually nonprefix addresses. Writing Y=rho cubed(y) and K=rho cubed(fill(J,beta,beta)), the actual trees are literally replace(replace(K,u,C),v,(A,Y)) and replace(replace(K,u,(A,Y)),v,C). Thus every fixed sibling has an actual preimage.

**Theorem 1.6 (Replacement through a context).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.path_replace`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.path_replace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every context H, trees M,X and address u, replacement of X in H.plug(M) at H.holeAddress followed by u equals H.plug(replace(M,u,X)).

**Theorem 1.7 (Composition through a context).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.context_composition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.context_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every single-hole context H and trees U,V, composition(H.plug(U)) plus composition(V) equals composition(H.plug(V)) plus composition(U).

**Theorem 1.8 (Positive alpha count and its unit case).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.alpha_count_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.alpha_count_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete source p, rho cubed(p) has at least one alpha leaf. If it has exactly one alpha leaf, p is the single leaf alpha.

**Theorem 1.9 (Sharp Alpha Separation).**

$$(\forall S \in Source, (\forall T \in Source, (((\neg(\operatorname{rho3}\left(S\right) = \operatorname{rho3}\left(T\right))) \land (\operatorname{n}\left(\operatorname{rho3}\left(S\right)\right) = \operatorname{n}\left(\operatorname{rho3}\left(T\right)\right)) \land (\operatorname{NC}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right))) \implies ((3 \leq \operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right)) \land (3 \leq \operatorname{delta}\left(\operatorname{rho3}\left(T\right), \operatorname{rho3}\left(S\right)\right)) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right) = 3) \Leftrightarrow (\operatorname{NormalForm}\left(S, T\right))) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(T\right), \operatorname{rho3}\left(S\right)\right) = 3) \Leftrightarrow (\operatorname{NormalForm}\left(S, T\right))) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right) = 3) \implies ((\operatorname{c}\left(\operatorname{rho3}\left(S\right)\right) = \operatorname{c}\left(\operatorname{rho3}\left(T\right)\right)) \land (\operatorname{c}\left(S\right) = \operatorname{c}\left(T\right)))))))) \land (\forall J \in TwoHole, (\forall y \in Source, (((y = beta) \lor (y = \operatorname{pair}\left(alpha, alpha\right))) \implies ((\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) \in I) \land (\operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right) \in I) \land (\operatorname{NormalForm}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right), \operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)) \land (\neg(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) = \operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right))) \land (\operatorname{n}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{n}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{NC}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{delta}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right) = 3) \land (\operatorname{delta}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = 3) \land (\operatorname{c}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{c}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{c}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) = \operatorname{c}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)) \land (\operatorname{nu}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right) = \operatorname{unsharedCount}\left(y\right)) \land (\operatorname{nu}\left(\operatorname{rho3}\left(\operatorname{fill}\left(J, \operatorname{pair}\left(alpha, y\right), beta\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{unsharedCount}\left(y\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all complete preimages S,T, put P=rho cubed(S) and Q=rho cubed(T). Distinct equal-leaf nonconflicting images have at least three alpha addresses missing in each direction. Either deficit equals three precisely when NormalForm(S,T) holds. The same Y is C or (A,A) at both holes. Equality implies identical compositions of both the actual trees and their preimages.

Every complete two-hole source context and each permitted y produce distinct equal-leaf nonconflicting actual images with both directed alpha deficits equal to three. The canonical preimage frontier consists of exactly their two independent holes, and the actual tree equalities retain both address replacements. The total unshared leaf counts, denoted unsharedCount(y), are seven when y is beta, and eight when y is (alpha,alpha).

At every atom-compound hole, the atomic side contributes at least one alpha deficit and the compound side at least two. Equal total leaf counts force both orientations to occur. A deficit of three forces exactly one hole in each orientation. A compound-side deficit of two forces the comparison C versus (A,Y), with Y=C or (A,A); its leaf increase is three or four. The other hole must balance this increase, excluding the alpha-atom comparison, whose increase is at least five. The unique five- and six-leaf images force the same Y at both holes. Deficits and compatibility add over distinct child addresses and are preserved by each common fixed sibling.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.NormalForm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.TwoHole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.alpha_count_facts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.context_composition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.delta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.forwardCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.path_replace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery](ActualHistorySingleHoleRecovery.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
