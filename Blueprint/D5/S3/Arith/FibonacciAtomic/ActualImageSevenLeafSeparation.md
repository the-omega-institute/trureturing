# Seven-Leaf Separation of Actual Fibonacci Images

## Abstract

Distinct equal-size nonconflicting actual third Fibonacci images differ at at least seven leaf addresses on each side.

T is FreeMagma Bool: nonempty finite free ordered full binary trees. True labels alpha and false labels beta. No associativity, commutativity or quotient identifications are imposed. The original substitution rho sends alpha to beta, beta to pair(beta,alpha), and preserves the ordered pair constructor.

**Definition 1.1 (Actual third image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.thirdImage`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.thirdImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(t)=rho^3(t), and I is exactly the range of R on T.

**Definition 1.2 (Literal leaf addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafAddresses`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafAddresses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(t) is a finite set of finite Boolean words. It is the toFinset view of ActualTreeReadoutAcquisition.leaves(t). False in a word means left and true means right. A leaf contributes the empty word; pair(p,q) contributes the left-prefixed words of L(p) and the right-prefixed words of L(q).

**Definition 1.3 (Labels at exact addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

label(t,u) is some(b) exactly when the public ActualTreeReadoutAcquisition.readout(u,t) reports that leaf label. Alpha projects to some(true), beta to some(false), and branch or absent to none.

**Definition 1.4 (Shared leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharedLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharedLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

s(p,q) counts literal addresses which are leaves in both trees, irrespective of labels. Simultaneous recursion gives one for two leaves, the sum of corresponding child counts for two branches, and zero for mixed root types.

**Definition 1.5 (Shared-label compatibility).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.Nonconflict`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.Nonconflict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NC(p,q) compares labels only at shared leaf addresses. Mixed leaf/branch and leaf/absent reports impose no restriction.

**Definition 1.6 (Unshared leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.unsharedLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.unsharedLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

n(p) is FreeMagma.length(p), and nu(p,q)=n(p)-s(p,q). The theorem identifies these numbers with the exact finite address cardinalities.

**Definition 1.7 (Second alpha image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E=pair(beta,alpha).

**Definition 1.8 (Third alpha image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A=pair(E,beta)=R(alpha).

**Definition 1.9 (Third beta image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C=pair(A,E)=R(beta).

**Definition 1.10 (First original preimage).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.pThirteen`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.pThirteen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

p=pair(beta,pair(alpha,beta)).

**Definition 1.11 (Second original preimage).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.qThirteen`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.qThirteen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q=pair(pair(alpha,beta),beta).

**Definition 1.12 (First sharp image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.PThirteen`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.PThirteen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P=pair(C,pair(A,C)).

**Definition 1.13 (Second sharp image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.QThirteen`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.QThirteen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q=pair(pair(A,C),C).

**Definition 1.14 (Exact shared labelled words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharpShared`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharpShared` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H consists of (LLLL,beta), (LLLR,alpha), (LLR,beta), (RLLL,beta), (RLLR,alpha), and (RLR,beta). joint(p,q) maps each word in L(p) intersect L(q) to its pair with label(p,u).getD(false). The leaf-address equivalence ensures that the default is never used there.

card is finite-set cardinality, inter and diff are intersection and difference. Word is the type of finite left/right words, Bool is the label type, and c counts alpha first and beta second. The sharp pair proves attainment of the separation constant; it makes no assertion of capacity equality.

**Theorem 1.15 (Universal Separation and Same-Composition Sharpness).**

$$\begin{gathered}(\forall p: T, ((\operatorname{card}\left(\operatorname{L}\left(p\right)\right) = \operatorname{n}\left(p\right)) \land (\forall u: \operatorname{Word}\left(\right), ((u \in \operatorname{L}\left(p\right)) \iff (\exists b: \operatorname{Bool}\left(\right), (\operatorname{label}\left(p, u\right) = \operatorname{some}\left(b\right))))))) \land (\forall p: T, (\forall q: T, ((\operatorname{s}\left(p, q\right) = \operatorname{card}\left(\operatorname{inter}\left(\operatorname{L}\left(p\right), \operatorname{L}\left(q\right)\right)\right)) \land (\operatorname{nu}\left(p, q\right) = \operatorname{card}\left(\operatorname{diff}\left(\operatorname{L}\left(p\right), \operatorname{L}\left(q\right)\right)\right)) \land ((\operatorname{NC}\left(p, q\right)) \iff (\forall u: \operatorname{Word}\left(\right), (\forall a: \operatorname{Bool}\left(\right), (\forall b: \operatorname{Bool}\left(\right), ((\operatorname{label}\left(p, u\right) = \operatorname{some}\left(a\right)) \implies ((\operatorname{label}\left(q, u\right) = \operatorname{some}\left(b\right)) \implies (a = b)))))))))) \land (\forall P: T, (\forall Q: T, (\forall n: \operatorname{Nat}\left(\right), (((P \in I) \land (Q \in I) \land (P \neq Q) \land (\operatorname{n}\left(P\right) = n) \land (\operatorname{n}\left(Q\right) = n) \land (\operatorname{NC}\left(P, Q\right))) \implies ((11 \leq n) \land (\operatorname{nu}\left(P, Q\right) = \operatorname{nu}\left(Q, P\right)) \land (7 \leq \operatorname{nu}\left(P, Q\right)) \land (\operatorname{s}\left(P, Q\right) \leq n - 7)))))) \land ((P = \operatorname{R}\left(p\right)) \land (Q = \operatorname{R}\left(q\right)) \land (P \neq Q) \land (\operatorname{NC}\left(P, Q\right)) \land (\operatorname{c}\left(P\right) = (5, 8)) \land (\operatorname{c}\left(Q\right) = (5, 8)) \land (\operatorname{n}\left(P\right) = 13) \land (\operatorname{n}\left(Q\right) = 13) \land (\operatorname{s}\left(P, Q\right) = 6) \land (\operatorname{nu}\left(P, Q\right) = 7) \land (\operatorname{nu}\left(Q, P\right) = 7) \land (\operatorname{joint}\left(P, Q\right) = H))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.seven_leaf_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual third image has at least three leaves, and every image of a preimage other than alpha has at least five. A and C conflict at LR. Comparing A with pair(R(x),R(y)) is compatible exactly when x is not alpha; then the shared count is zero and the composite has at least eight leaves.

For C against pair(R(x),R(y)), compatibility excludes y=alpha. If x=alpha, the shared count is three, leaving two leaves on the atomic side and at least five on the composite side. The case x=beta conflicts. A branching x reduces to the A comparison and has no shared leaves. Thus every legal atomic/composite pair has strictly increasing sizes, sizes at least three and eight, and unshared counts at least two and five.

Induction on the actual preimages propagates four alternatives: equal images, either strict size orientation with those local bounds, or sizes at least eleven and both unshared counts at least seven. Exact address counts add across corresponding children. Opposite strict orientations give three plus eight leaves and two plus five unshared leaves on each side. A previously separated child remains separated. Distinct equal-size images therefore satisfy the fourth alternative. Equal sizes equate the two differences and give the shared-leaf upper bound.

The two literal preimages produce P and Q. Each image contains one A and two C, giving composition (5,8) and thirteen leaves. Their six shared labelled addresses are exactly H, so each side has seven unshared leaves.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.A`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.C`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.E`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.Nonconflict`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.PThirteen`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.QThirteen`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafAddresses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.leafLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.pThirteen`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.qThirteen`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.seven_leaf_separation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharedLeaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.sharpShared`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.thirdImage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.unsharedLeaves`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](ActualTreeReadoutAcquisition.md)
