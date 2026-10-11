# Exact Clifford Leaf Observation Fibers

## Abstract

The Clifford leaf product has exactly six distinct canonical phases.

Let Q(a,b)=a*a+a*b-b*b on the real coordinate plane, and let C be its Clifford algebra with v*v=Q(v)1. Write A and B for the canonical images of (1,0) and (0,1). Sources are the existing ordered Boolean leaf trees; alpha is true and beta is false. The existing substitution sends alpha to beta and beta to (beta,alpha).

The quadratic form Q and ordered leaf product E are those of FixedHistoryComposition. The free-magma homomorphism E sends alpha to A and beta to B, and multiplies the leaves in source order.

**Definition 1.1 (Canonical observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.X`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X(j)=E(rho^j(alpha)) for every natural index j.

**Definition 1.2 (Six chronological phases).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.phases`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.phases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six values are A, B, BA, A+B, -B, AB, in that order.

**Definition 1.3 (Reader on the canonical image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.Factors`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.Factors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A target g factors when a function on the range of X takes X(j) to g(j) for every natural j. The reader receives only the algebra element.

**Theorem 1.4 (Exact fibers and canonical successor).**

$$(\forall j, (\operatorname{c}\left(\operatorname{T}\left(j\right)\right) = \operatorname{atomicBlock}\left(j\right))) \land ((\forall j, (\operatorname{X}\left(j\right) = \operatorname{P}\left(\operatorname{mod}\left(j, 6\right)\right))) \land ((\forall j, k, ((\operatorname{X}\left(j\right) = \operatorname{X}\left(k\right)) \Leftrightarrow (\operatorname{mod}\left(j, 6\right) = \operatorname{mod}\left(k, 6\right)))) \land ((\forall Y, g, ((\operatorname{Factors}\left(g\right)) \Leftrightarrow (\forall j, (\operatorname{g}\left(j+6\right) = \operatorname{g}\left(j\right))))) \land ((\operatorname{Factors}\left(j \mapsto \operatorname{X}\left(j+1\right)\right)) \land ((\neg\exists R, (\forall t, (\operatorname{R}\left(\operatorname{E}\left(t\right)\right) = \operatorname{E}\left(\operatorname{rho}\left(t\right)\right)))) \land (((\operatorname{E}\left(t2\right) = 1) \land ((\operatorname{E}\left(t4\right) = 1) \land ((\operatorname{E}\left(\operatorname{rho}\left(t2\right)\right) = -1) \land (\operatorname{E}\left(\operatorname{rho}\left(t4\right)\right) = 1)))) \land ((\exists p, q, ((\operatorname{c}\left(p\right) = (3,0)) \land ((\operatorname{c}\left(q\right) = (3,0)) \land ((\operatorname{leafLabels}\left(p\right) = \operatorname{leafLabels}\left(q\right)) \land ((p \neq q) \land (\operatorname{E}\left(p\right) = \operatorname{E}\left(q\right))))))) \land (\forall Y, g, (\exists f, (\forall j, ((j < 6)\implies(\operatorname{f}\left(\operatorname{X}\left(j\right)\right) = \operatorname{g}\left(j\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here c is the existing composition, M(a,b)=(b,a+b), T(j)=rho^j(alpha), and P denotes the displayed six-element phase list. For every type Y and every g from the natural numbers to Y, a reader exists exactly when g is six-periodic. This includes the successor target g(j)=X(j+1).

The Clifford square and polar relations give A*A=1, B*B=-1 and AB+BA=1. The ordered source recursion gives X(j+2)=X(j+1)X(j). These relations produce the six phases. A two-by-two real matrix representation separates all six, so equality of observations is precisely equality of indices modulo six.

Let t2=(alpha,alpha) and t4=(t2,t2). Both leaf products are 1, while their substituted products are -1 and 1. No reader on the full source image can therefore perform substitution. The unequal trees p=((alpha,alpha),alpha) and q=(alpha,(alpha,alpha)) have equal composition (3,0), equal ordered leaf labels, and equal Clifford observations. Here leafLabels(t) is the list of the indexedEquiv leaf-position function. For each Y and target g, a reader can fit g on all indices j<6, because these observations are distinct.

The Clifford construction and its universal property are standard; see Lundholm and Svensson, Clifford algebra, geometric algebra, and applications, arXiv:0907.5356v1, sections 2.1-2.3.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.Factors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.X`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.phases`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FixedHistoryComposition](FixedHistoryComposition.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
