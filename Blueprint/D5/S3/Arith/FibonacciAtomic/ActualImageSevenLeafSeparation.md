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

**Theorem 1.9 (Sharp separation and the smallest pair).**

$$(\forall P \in I, (\forall Q \in I, (((\neg(P = Q)) \land (\operatorname{n}\left(P\right) = \operatorname{n}\left(Q\right)) \land (\operatorname{NC}\left(P, Q\right))) \implies ((11 \leq \operatorname{n}\left(P\right)) \land (\operatorname{nu}\left(P, Q\right) = \operatorname{nu}\left(Q, P\right)) \land (7 \leq \operatorname{nu}\left(P, Q\right)) \land (\operatorname{s}\left(P, Q\right) \leq \operatorname{n}\left(P\right) - 7))))) \land (\exists P13, Q13, ((P13 = \operatorname{pair}\left(C, \operatorname{pair}\left(A, C\right)\right)) \land (Q13 = \operatorname{pair}\left(\operatorname{pair}\left(A, C\right), C\right)) \land (P13 = \operatorname{rho3}\left(\operatorname{pair}\left(beta, \operatorname{pair}\left(alpha, beta\right)\right)\right)) \land (Q13 = \operatorname{rho3}\left(\operatorname{pair}\left(\operatorname{pair}\left(alpha, beta\right), beta\right)\right)) \land (P13 \in I) \land (Q13 \in I) \land (\neg(P13 = Q13)) \land (\operatorname{NC}\left(P13, Q13\right)) \land (\operatorname{c}\left(P13\right) = \operatorname{pair}\left(5, 8\right)) \land (\operatorname{c}\left(Q13\right) = \operatorname{pair}\left(5, 8\right)) \land (\operatorname{n}\left(P13\right) = 13) \land (\operatorname{n}\left(Q13\right) = 13) \land (\operatorname{s}\left(P13, Q13\right) = 6) \land (\operatorname{nu}\left(P13, Q13\right) = 7) \land (\operatorname{nu}\left(Q13, P13\right) = 7))) \land (\forall P \in I, (\forall Q \in I, (((\neg(P = Q)) \land (\operatorname{n}\left(P\right) = 11) \land (\operatorname{n}\left(Q\right) = 11) \land (\operatorname{NC}\left(P, Q\right))) \implies (\operatorname{set}\left(P, Q\right) = \operatorname{set}\left(\operatorname{pair}\left(A, B\right), \operatorname{pair}\left(B, A\right)\right))))) \land ((\operatorname{pair}\left(A, B\right) \in I) \land (\operatorname{pair}\left(B, A\right) \in I) \land (\neg(\operatorname{pair}\left(A, B\right) = \operatorname{pair}\left(B, A\right))) \land (\operatorname{n}\left(\operatorname{pair}\left(A, B\right)\right) = 11) \land (\operatorname{n}\left(\operatorname{pair}\left(B, A\right)\right) = 11) \land (\operatorname{NC}\left(\operatorname{pair}\left(A, B\right), \operatorname{pair}\left(B, A\right)\right))) \land (\forall F \in \operatorname{Finset}\left(Source\right), (((\forall P \in F, ((P \in I) \land (\operatorname{n}\left(P\right) = 11))) \land (\forall P \in F, (\forall Q \in F, ((\neg(P = Q)) \implies (\operatorname{NC}\left(P, Q\right)))))) \implies (\operatorname{card}\left(F\right) \leq 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P13=(C,(A,C)) and Q13=((A,C),C). Their respective literal preimages are (beta,(alpha,beta)) and ((alpha,beta),beta). They are distinct nonconflicting actual images, both have composition (5,8) and thirteen leaves, and they share six leaf addresses. Thus each has exactly seven unshared leaves. These equalities and preimages are included in the theorem.

Every actual image is A, C, or a pair of actual images. In a nonconflicting atom-compound comparison, the atom has fewer leaves, the two leaf counts are at least three and eight, and the unshared counts are at least two and five. Shared and unshared counts add across the two child addresses. Recursive comparison therefore either retains one strict orientation or encounters opposite orientations, which contribute at least eleven leaves and seven unshared leaves on each side. Equal total sizes require the latter case.

The actual images of at most eight leaves are A, C, (A,A), (A,C), and (C,A). An eleven-leaf image has two children in that list. The resulting six ordered possibilities have exactly one distinct nonconflicting unordered pair: (A,B) and (B,A). This pair has no shared leaves. Every finite pairwise nonconflicting family of eleven-leaf actual images consequently has at most two members.

Substitution trees, Fibonacci trees and their leaf-induced subtrees are established neighboring subjects. Patera's Generating the Fibonacci Chain in O(log n) Space and O(n) Time studies generation of substitution words; Legendre's Labeled Fibonacci Trees studies integer labels; Dossou-Olory's Leaf-Induced Subtrees of Leaf-Fibonacci Trees counts induced subtree shapes. The statement here concerns fixed address intersections and label compatibility of complete ordered substitution images.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.NC`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.n`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.nu`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.s`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](ActualImageAddressCertificate.md)
