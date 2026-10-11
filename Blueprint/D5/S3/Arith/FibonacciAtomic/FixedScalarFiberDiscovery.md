# Discovery on a Fixed Scalar Fiber

## Abstract

A fixed Fibonacci scalar fiber has two actual positive trees and sharp discovery costs.

Sources are nonempty finite free ordered full binary trees with alpha and beta leaves. The original substitution rho sends alpha to beta and beta to pair(beta,alpha). Every observation uses the original complete source through the four-valued address readout. False denotes left and true denotes right. No associativity or commutativity quotient is used.

**Definition 1.1 (Complete scalar fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.scalarFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.scalarFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural L put f=F(3L+3), g=F(3L+4), and m=3f+5g. X(L) contains every source U with f times a(U) plus g times b(U) equal to m. No image, composition, shape, leaf-count or height promise is supplied.

**Definition 1.2 (First positive source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.P`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A=pair(pair(beta,alpha),beta), B=pair(A,pair(beta,alpha)), and P=pair(A,B)=rho^3(pair(alpha,beta)). The blocks are the existing literal A and C.

**Definition 1.3 (Second positive source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.Q`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q=pair(B,A)=rho^3(pair(beta,alpha)).

**Definition 1.4 (Positive certificate cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificateSize`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificateSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

k(L)=5 at L=0 and k(L)=3 at positive L.

**Definition 1.5 (Pointwise fiber contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.CorrectOn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.CorrectOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A history-only Policy pi is correct on X(L) when every U in X(L) has a finite fuel-bounded execute run returning its actual third-image membership bit.

**Definition 1.6 (Observation window).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.WindowOn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.WindowOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every address in a terminating run on a source in X(L) has length at most h. Together with CorrectOn this covers every actual query on each fiber input.

**Definition 1.7 (Distinct queries).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.NoRepeatOn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.NoRepeatOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The address list of every terminating run on X(L) is duplicate-free.

**Definition 1.8 (Optimal worst-input cost).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.discoveryCost`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.discoveryCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(pi,U) is extendedCost: the number of distinct addresses in a finite run, and positive infinity for nontermination. D(L,h) is the infimum, over policies correct on X(L) and obeying h, of the supremum of C over X(L).

**Definition 1.9 (The two minimum certificates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(L,V) is the set of beta leaf addresses of V at L=0, and its alpha address set at positive L.

**Definition 1.10 (Whole-fiber soundness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.FiberSound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.FiberSound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite address set J is sound at V if every U in X(L) matching V at all addresses in J is an actual third image.

**Definition 1.11 (Ordered endpoint test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.testNext`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.testNext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(label,S) queries the listed addresses in left-right lexicographic order. A matching leaf reply continues the test; all three other replies reject. Exhausting the list accepts.

**Definition 1.12 (The two complete response tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.strategy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.strategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

piP=strategy(L,true) and piQ=strategy(L,false). At L=0 piP first queries LR: beta tests BP without LR, branch tests BQ, alpha and absent reject. piQ first queries RR: beta tests BQ without RR, branch tests BP, alpha and absent reject. At positive L piP first queries LLR: alpha tests AP without LLR, beta tests AQ, branch and absent reject. piQ first queries RLR: alpha tests AQ without RLR, beta tests AP, branch and absent reject. AP={LLR,RLLR,RRR}, AQ={LLLR,LRR,RLR}, BP={LLL,LR,RLLL,RLR,RRL}, and BQ={LLLL,LLR,LRL,RLL,RR}. Every remaining test uses its corresponding leaf label.

**Theorem 1.13 (Classification and Sharp Discovery Cost).**

$$\forall L \in Nat, (\forall h \in Nat, ((\operatorname{Finite}\left(\operatorname{X}\left(L\right)\right)) \land (\operatorname{c}\left(\operatorname{X}\left(L\right)\right) = \operatorname{if}\left(L = 0, \left\{\operatorname{pair}\left(0, 7\right), \operatorname{pair}\left(3, 5\right), \operatorname{pair}\left(6, 3\right), \operatorname{pair}\left(9, 1\right)\right\}, \left\{\operatorname{pair}\left(3, 5\right)\right\}\right)) \land (\operatorname{inter}\left(\operatorname{X}\left(L\right), I3\right) = \left\{P, Q\right\}) \land (P \neq Q) \land (P = \operatorname{rho3}\left(\operatorname{pair}\left(alpha, beta\right)\right)) \land (Q = \operatorname{rho3}\left(\operatorname{pair}\left(beta, alpha\right)\right)) \land ((h < 4) \implies (\operatorname{Pi}\left(L, h\right) = \emptyset)) \land ((4 \leq h) \implies ((\forall pi \in \operatorname{Pi}\left(L, h\right), ((\operatorname{k}\left(L\right) \leq \operatorname{C}\left(pi, P\right)) \land (\operatorname{k}\left(L\right) \leq \operatorname{C}\left(pi, Q\right)) \land (2 \operatorname{k}\left(L\right) + 1 \leq \operatorname{C}\left(pi, P\right) + \operatorname{C}\left(pi, Q\right)))) \land ((\operatorname{CorrectOn}\left(L, piP\right)) \land (\operatorname{CorrectOn}\left(L, piQ\right)) \land (\operatorname{WindowOn}\left(L, 4, piP\right)) \land (\operatorname{WindowOn}\left(L, 4, piQ\right)) \land (\operatorname{NoRepeatOn}\left(L, piP\right)) \land (\operatorname{NoRepeatOn}\left(L, piQ\right)) \land (\forall U \in \operatorname{X}\left(L\right), ((\operatorname{C}\left(piP, U\right) \leq \operatorname{k}\left(L\right) + 1) \land (\operatorname{C}\left(piQ, U\right) \leq \operatorname{k}\left(L\right) + 1))) \land (\operatorname{pair}\left(\operatorname{C}\left(piP, P\right), \operatorname{C}\left(piP, Q\right)\right) = \operatorname{pair}\left(\operatorname{k}\left(L\right), \operatorname{k}\left(L\right) + 1\right)) \land (\operatorname{pair}\left(\operatorname{C}\left(piQ, P\right), \operatorname{C}\left(piQ, Q\right)\right) = \operatorname{pair}\left(\operatorname{k}\left(L\right) + 1, \operatorname{k}\left(L\right)\right))))) \land (\operatorname{D}\left(L, h\right) = \operatorname{if}\left(h < 4, \infty, \operatorname{if}\left(L = 0, 6, 4\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L and h are natural numbers. Pi(L,h) denotes the policies satisfying CorrectOn(L) and WindowOn(L,h); I3 denotes the actual third substitution image. The scalar and all replies come from the same original source. Controller computation, scalar acquisition and address text length are free.

Adjacent Fibonacci coefficients are coprime. Nonnegativity leaves four compositions at stage zero and only (3,5) later. Actual composition transport forces a positive source's preimage to have one leaf of each label. The composition fiber (1,1) has cardinality two and is exhausted by the two opposite ordered pairs, giving precisely P and Q. Each composition fiber is finite.

At stage zero the five beta responses force the branching skeleton and beta slots. The three remaining subtrees have scalar sum six and each contributes at least two, so all three are single alpha leaves. Label exchanges and beta grafts establish the unique minimum beta certificate. At positive stages the alpha certificate theorem applies on the whole scalar fiber.

Every accepting run is a sound certificate: any source matching its paid addresses follows the same deterministic history. The unique minimum certificates of P and Q are disjoint, but both runs share their first query. Their costs therefore cannot both be k(L). The two response tables attain the resulting bound and use only distinct addresses of depth at most four.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.CorrectOn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.FiberSound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.NoRepeatOn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.P`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.Q`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.WindowOn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.certificateSize`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.discoveryCost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.scalarFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.strategy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.testNext`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon](PrimeGcdHorizon.md)
