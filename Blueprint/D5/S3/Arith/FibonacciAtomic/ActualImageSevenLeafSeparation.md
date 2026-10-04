# Seven-Leaf Separation of Actual Tree Images

## Abstract

Distinct equal-size three-step Fibonacci tree images have at least seven unshared leaves.

Sources are nonempty finite ordered full binary trees with alpha and beta leaves. The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. I is the range of rho cubed on these complete sources. L(P) is the existing leaf-address set, with root-first Boolean paths: false means left and true means right. Composition counts alpha and beta leaves.

**Definition 1.1 (Leaf count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.n`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.n` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

n(P) is the cardinality of L(P).

**Definition 1.2 (Shared leaf count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.s`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.s` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

s(P,Q) is the cardinality of the intersection of L(P) and L(Q).

**Definition 1.3 (Unshared leaf count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.nu`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.nu` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nu(P,Q)=n(P)-s(P,Q), the number of leaves of P whose addresses are not leaves of Q.

**Definition 1.4 (Nonconflicting leaf labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NC`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NC(P,Q) means that the existing endpoint observations agree at every shared leaf address. A leaf of one tree may be a branch or absent in the other; such addresses impose no agreement condition.

**Definition 1.5 (Terminal pair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E=(beta,alpha).

**Definition 1.6 (Alpha image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A=(E,beta)=rho cubed(alpha), with three leaves.

**Definition 1.7 (Beta image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C=(A,E)=rho cubed(beta), with five leaves.

**Definition 1.8 (Smallest compatible compound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.B`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B=(C,A), with eight leaves.

**Definition 1.9 (Directed alpha deficit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.delta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

delta(P,Q) is the cardinality of the set difference of the original alpha-leaf address sets.

**Definition 1.10 (Alpha weight).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.mu`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.mu` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mu(P) is the cardinality of the original alpha-leaf address set.

**Definition 1.11 (One source hole).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.OneHole`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.OneHole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A context has one hole, and is built by attaching complete fixed source trees on its left or right. OneHole.fill(g,H,X) inserts X and applies g to each fixed source sibling. Using g=rho cubed makes all fixed siblings actual images; using the identity retains the preimage. OneHole.address records every ordered left or right choice from the root.

**Definition 1.12 (Two source holes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.TwoHole`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.TwoHole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer one-hole context leads to the lowest common ancestor. Its left and right one-hole contexts lead to the two distinct holes. A Boolean records their naming order. TwoHole.fill(J,g,X,Y) inserts the named trees exactly once, retaining the entire outer context and each fixed sibling. TwoHole.addresses gives two addresses with the same outer prefix and opposite next bits, and hence neither is a prefix of the other.

**Definition 1.13 (Canonical divergence frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.frontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.frontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Comparison is performed on complete preimages. Equal subtrees stop; two branches recurse into the ordered children; an atom-compound comparison records the current address.

**Definition 1.14 (Atomic-side hole count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.forwardCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.forwardCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

forwardCount(S,T) counts frontier holes whose S side is atomic and T side is compound.

**Definition 1.15 (Literal double-hole normal form).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NormalForm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NormalForm(S,T) retains a complete source context J and y equal to beta or (alpha,alpha), with S=fill(id,J,beta,(alpha,y)) and T=fill(id,J,(alpha,y),beta). Its frontier is exactly the two named, mutually nonprefix addresses. Writing Y=rho cubed(y) and K=rho cubed(fill(id,J,beta,beta)), the actual trees are literally replace(replace(K,u,C),v,(A,Y)) and replace(replace(K,u,(A,Y)),v,C). Thus every fixed sibling has an actual preimage.

**Theorem 1.16 (Sharp separation and the smallest pair).**

$$((\forall P \in I, (\forall Q \in I, (((\neg(P = Q)) \land (\operatorname{n}\left(P\right) = \operatorname{n}\left(Q\right)) \land (\operatorname{NC}\left(P, Q\right))) \implies ((11 \leq \operatorname{n}\left(P\right)) \land (\operatorname{nu}\left(P, Q\right) = \operatorname{nu}\left(Q, P\right)) \land (7 \leq \operatorname{nu}\left(P, Q\right)) \land (\operatorname{s}\left(P, Q\right) \leq \operatorname{n}\left(P\right) - 7))))) \land (\exists P13, Q13, ((P13 = \operatorname{pair}\left(C, \operatorname{pair}\left(A, C\right)\right)) \land (Q13 = \operatorname{pair}\left(\operatorname{pair}\left(A, C\right), C\right)) \land (P13 = \operatorname{rho3}\left(\operatorname{pair}\left(beta, \operatorname{pair}\left(alpha, beta\right)\right)\right)) \land (Q13 = \operatorname{rho3}\left(\operatorname{pair}\left(\operatorname{pair}\left(alpha, beta\right), beta\right)\right)) \land (P13 \in I) \land (Q13 \in I) \land (\neg(P13 = Q13)) \land (\operatorname{NC}\left(P13, Q13\right)) \land (\operatorname{c}\left(P13\right) = \operatorname{pair}\left(5, 8\right)) \land (\operatorname{c}\left(Q13\right) = \operatorname{pair}\left(5, 8\right)) \land (\operatorname{n}\left(P13\right) = 13) \land (\operatorname{n}\left(Q13\right) = 13) \land (\operatorname{s}\left(P13, Q13\right) = 6) \land (\operatorname{nu}\left(P13, Q13\right) = 7) \land (\operatorname{nu}\left(Q13, P13\right) = 7))) \land (\forall P \in I, (\forall Q \in I, (((\neg(P = Q)) \land (\operatorname{n}\left(P\right) = 11) \land (\operatorname{n}\left(Q\right) = 11) \land (\operatorname{NC}\left(P, Q\right))) \implies (\operatorname{set}\left(P, Q\right) = \operatorname{set}\left(\operatorname{pair}\left(A, B\right), \operatorname{pair}\left(B, A\right)\right))))) \land ((\operatorname{pair}\left(A, B\right) \in I) \land (\operatorname{pair}\left(B, A\right) \in I) \land (\neg(\operatorname{pair}\left(A, B\right) = \operatorname{pair}\left(B, A\right))) \land (\operatorname{n}\left(\operatorname{pair}\left(A, B\right)\right) = 11) \land (\operatorname{n}\left(\operatorname{pair}\left(B, A\right)\right) = 11) \land (\operatorname{NC}\left(\operatorname{pair}\left(A, B\right), \operatorname{pair}\left(B, A\right)\right))) \land (\forall F \in \operatorname{Finset}\left(Source\right), (((\forall P \in F, ((P \in I) \land (\operatorname{n}\left(P\right) = 11))) \land (\forall P \in F, (\forall Q \in F, ((\neg(P = Q)) \implies (\operatorname{NC}\left(P, Q\right)))))) \implies (\operatorname{card}\left(F\right) \leq 2)))) \land (\forall S \in Source, (\forall T \in Source, (((\neg(\operatorname{rho3}\left(S\right) = \operatorname{rho3}\left(T\right))) \land (\operatorname{n}\left(\operatorname{rho3}\left(S\right)\right) = \operatorname{n}\left(\operatorname{rho3}\left(T\right)\right)) \land (\operatorname{NC}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right))) \implies ((3 \leq \operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right)) \land (3 \leq \operatorname{delta}\left(\operatorname{rho3}\left(T\right), \operatorname{rho3}\left(S\right)\right)) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right) = 3) \Leftrightarrow (\operatorname{NormalForm}\left(S, T\right))) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(T\right), \operatorname{rho3}\left(S\right)\right) = 3) \Leftrightarrow (\operatorname{NormalForm}\left(S, T\right))) \land ((\operatorname{delta}\left(\operatorname{rho3}\left(S\right), \operatorname{rho3}\left(T\right)\right) = 3) \implies ((\operatorname{c}\left(\operatorname{rho3}\left(S\right)\right) = \operatorname{c}\left(\operatorname{rho3}\left(T\right)\right)) \land (\operatorname{c}\left(S\right) = \operatorname{c}\left(T\right)))))))) \land (\forall J \in TwoHole, (\forall y \in Source, (((y = beta) \lor (y = \operatorname{pair}\left(alpha, alpha\right))) \implies ((\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) \in I) \land (\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right) \in I) \land (\operatorname{NormalForm}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right), \operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)) \land (\neg(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) = \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right))) \land (\operatorname{n}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{n}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{NC}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{delta}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right) = 3) \land (\operatorname{delta}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = 3) \land (\operatorname{c}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{c}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right)) \land (\operatorname{c}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right) = \operatorname{c}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)) \land (\operatorname{nu}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right)\right) = \operatorname{unsharedCount}\left(y\right)) \land (\operatorname{nu}\left(\operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, \operatorname{pair}\left(alpha, y\right), beta\right)\right), \operatorname{rho3}\left(\operatorname{fill}\left(\operatorname{id}\left(\right), J, beta, \operatorname{pair}\left(alpha, y\right)\right)\right)\right) = \operatorname{unsharedCount}\left(y\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P13=(C,(A,C)) and Q13=((A,C),C). Their respective literal preimages are (beta,(alpha,beta)) and ((alpha,beta),beta). They are distinct nonconflicting actual images, both have composition (5,8) and thirteen leaves, and they share six leaf addresses. Thus each has exactly seven unshared leaves. These equalities and preimages are included in the theorem.

Every actual image is A, C, or a pair of actual images. In a nonconflicting atom-compound comparison, the atom has fewer leaves, the two leaf counts are at least three and eight, and the unshared counts are at least two and five. Shared and unshared counts add across the two child addresses. Recursive comparison therefore either retains one strict orientation or encounters opposite orientations, which contribute at least eleven leaves and seven unshared leaves on each side. Equal total sizes require the latter case.

The actual images of at most eight leaves are A, C, (A,A), (A,C), and (C,A). An eleven-leaf image has two children in that list. The resulting six ordered possibilities have exactly one distinct nonconflicting unordered pair: (A,B) and (B,A). This pair has no shared leaves. Every finite pairwise nonconflicting family of eleven-leaf actual images consequently has at most two members.

For all complete preimages S,T, put P=rho cubed(S) and Q=rho cubed(T). Distinct equal-leaf nonconflicting images have at least three alpha addresses missing in each direction. Either deficit equals three precisely when NormalForm(S,T) holds. The same Y is C or (A,A) at both holes. Equality implies identical compositions of both the actual trees and their preimages.

Every complete two-hole source context and each permitted y produce distinct equal-leaf nonconflicting actual images with both directed alpha deficits equal to three. The canonical preimage frontier consists of exactly their two independent holes, and the actual tree equalities retain both address replacements. The total unshared leaf counts, denoted unsharedCount(y), are seven when y is beta, and eight when y is (alpha,alpha).

At every atom-compound hole, the atomic side contributes at least one alpha deficit and the compound side at least two. Equal total leaf counts force both orientations to occur. A deficit of three forces exactly one hole in each orientation. A compound-side deficit of two forces the comparison C versus (A,Y), with Y=C or (A,A); its leaf increase is three or four. The other hole must balance this increase, excluding the alpha-atom comparison, whose increase is at least five. The unique five- and six-leaf images force the same Y at both holes. Deficits and compatibility add over distinct child addresses and are preserved by each common fixed sibling.

Substitution trees, Fibonacci trees and their leaf-induced subtrees are established neighboring subjects. Patera's Generating the Fibonacci Chain in O(log n) Space and O(n) Time studies generation of substitution words; Legendre's Labeled Fibonacci Trees studies integer labels; Dossou-Olory's Leaf-Induced Subtrees of Leaf-Fibonacci Trees counts induced subtree shapes. The statement here concerns fixed address intersections and label compatibility of complete ordered substitution images.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NC`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NormalForm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.OneHole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.TwoHole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.delta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.forwardCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.mu`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.n`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.nu`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.s`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
