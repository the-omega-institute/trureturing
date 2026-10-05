# Sharp Clifford Canonical Recovery

## Abstract

The complete infinite canonical Clifford orbit permits exactly the stated modular readers.

Use the Clifford algebra and leaf observation E from CliffordLeafOrbit. The canonical source is T(j)=rho^j(alpha), its observation is X(j), and its composition is z(j)=M^j(1,0), with M(a,b)=(b,a+b). A factorizing reader is a function on the range of X; it receives the algebra element alone. The residueTarget(D) maps j to z(j) modulo D.

**Definition 1.1 (Standard low representatives).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.low`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.low` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive d, low(d,j) is the pair of standard representatives of z(j) modulo d.

The integer carry kappa(d,j) is floor((low(d,j)[0]+low(d,j)[1])/d), using the standard residue-pair carry. It is zero or one for positive d.

**Definition 1.2 (Next-step carry output).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.K`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(d,e,j)=(0,kappa(d,j)) modulo e.

**Definition 1.3 (Current high output).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.H`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(d,e,j) is the pair of quotients of the coordinates of z(j) by d, reduced modulo e.

**Definition 1.4 (Complete current target).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.L`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(d,e,j) pairs low(d,j) with H(d,e,j). Both components come from the same source.

**Theorem 1.5 (Sharp recovery and source obstructions).**

$$\begin{gathered}(\forall D, ((1 \leq D) \implies ((\operatorname{Factors}\left(\operatorname{residueTarget}\left(D\right)\right)) \Leftrightarrow (D \mid 4))))\\{}\land (\forall d, e, (((1 \leq d) \land (2 \leq e)) \implies ((\operatorname{Factors}\left(\operatorname{K}\left(d, e\right)\right)) \Leftrightarrow (d \mid 4))))\\{}\land (\forall d, ((1 \leq d) \implies ((\operatorname{Factors}\left(\operatorname{K}\left(d, 1\right)\right)) \land (\forall j, (\operatorname{K}\left(d, 1, j\right) = 0)))))\\{}\land (\forall e, ((1 \leq e) \implies ((\operatorname{Factors}\left(\operatorname{K}\left(1, e\right)\right)) \land (\forall j, ((\operatorname{low}\left(1, j\right) = 0) \land (\operatorname{kappa}\left(1, j\right) = 0) \land (\operatorname{K}\left(1, e, j\right) = 0))))))\\{}\land (\forall d, e, (((1 \leq d) \land (1 \leq e)) \implies ((\operatorname{Factors}\left(\operatorname{L}\left(d, e\right)\right)) \Leftrightarrow (de \mid 4))))\\{}\land (\forall d, e, (((1 \leq d) \land (1 \leq e) \land (d \mid 4)) \implies ((\operatorname{Factors}\left(\operatorname{H}\left(d, e\right)\right)) \Leftrightarrow (de \mid 4))))\\{}\land (\forall e, ((1 \leq e) \implies ((\operatorname{Factors}\left(\operatorname{L}\left(1, e\right)\right)) \Leftrightarrow (e \mid 4))))\\{}\land ((\operatorname{X}\left(0\right) = A) \land (\operatorname{X}\left(6\right) = A) \land (\operatorname{z}\left(0\right) = (1, 0)) \land (\operatorname{z}\left(6\right) = (5, 8)) \land (\operatorname{quantity}\left(\operatorname{z}\left(0\right)\right) = 2) \land (\operatorname{quantity}\left(\operatorname{z}\left(6\right)\right) = 34) \land (\operatorname{low}\left(3, 0\right) = (1, 0)) \land (\operatorname{low}\left(3, 6\right) = (2, 2)) \land (\forall e, ((2 \leq e) \implies ((\operatorname{K}\left(3, e, 0\right) = (0, 0)) \land (\operatorname{K}\left(3, e, 6\right) = (0, 1)) \land (\operatorname{K}\left(3, e, 0\right) \neq \operatorname{K}\left(3, e, 6\right))))) \land (\operatorname{low}\left(4, 0\right) = (1, 0)) \land (\operatorname{low}\left(4, 6\right) = (1, 0)) \land (\operatorname{K}\left(4, 2, 0\right) = 0) \land (\operatorname{K}\left(4, 2, 6\right) = 0) \land (\operatorname{H}\left(4, 2, 0\right) = 0) \land (\operatorname{H}\left(4, 2, 6\right) = (1, 0)))\\{}\land ((\operatorname{Factors}\left(j \mapsto \operatorname{X}\left(j+1\right)\right)) \land (\neg\exists R, (\forall t, (\operatorname{R}\left(\operatorname{E}\left(t\right)\right) = \operatorname{E}\left(\operatorname{rho}\left(t\right)\right)))) \land ((\operatorname{E}\left(t2\right) = 1) \land (\operatorname{E}\left(t4\right) = 1) \land (\operatorname{E}\left(\operatorname{rho}\left(t2\right)\right) = -1) \land (\operatorname{E}\left(\operatorname{rho}\left(t4\right)\right) = 1)) \land (\exists p, q, ((\operatorname{c}\left(p\right) = (3, 0)) \land (\operatorname{c}\left(q\right) = (3, 0)) \land (\operatorname{leafLabels}\left(p\right) = \operatorname{leafLabels}\left(q\right)) \land (p \neq q) \land (\operatorname{E}\left(p\right) = \operatorname{E}\left(q\right)))) \land (\forall Y, g, (\exists f, (\forall j, ((j < 6) \implies (\operatorname{f}\left(\operatorname{X}\left(j\right)\right) = \operatorname{g}\left(j\right)))))))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All moduli D,d,e are natural numbers. The first classification assumes D>=1. The carry classification assumes d>=1 and e>=2. The complete-target classification assumes d,e>=1. The high-only classification additionally assumes d divides 4. For e=1 the carry output is identically zero for every positive d; for d=1 both low and the integer carry vanish, so the carry output vanishes for every positive e.

Observation equality is index equality modulo six. Modular composition is six-periodic precisely when the modulus divides 4. A periodic carry forces the difference of low representatives at indices j+6 and j to satisfy a bounded integer Fibonacci recursion. For such a difference a(j), the product a(j)a(j+1) increases by a(j+1)^2. Its bounded integer range has a greatest element; the sequence is then zero on a tail, and the reversible recursion forces every difference to vanish. This yields the carry necessity for all moduli. The standard quotient-remainder identities identify the complete target with composition modulo d*e.

The same actual sources at indices zero and six have equal Clifford observation A and compositions (1,0) and (5,8). Their quantities are 2 and 34. At d=3 their low pairs are (1,0) and (2,2), with carry outputs (0,0) and (0,1) for every e>=2. At d=4,e=2 the low pairs agree at (1,0), both next-step carry outputs vanish, and current highs are (0,0) and (1,0).

The canonical successor has a reader. On all source trees, no function R on the image of E satisfies R(E(t))=E(rho(t)) for every t. Let t2=(alpha,alpha) and t4=(t2,t2). Both have observation 1, but their substituted observations are -1 and 1. The trees p=((alpha,alpha),alpha) and q=(alpha,(alpha,alpha)) have equal composition (3,0) and the same ordered leaf-label list, yet p and q are unequal and their observations agree. Thus the observation also fails to recover parentheses on a fixed composition and leaf order. For every type Y and target g from the natural numbers to Y, a reader can fit g on the initial indices j<6.

The statements concern the complete infinite orbit. They do not impose the same necessary conditions on arbitrary finite source subsets. The standard Clifford construction is described in Lundholm and Svensson, arXiv:0907.5356v1, sections 2.1-2.3. Flaut, DOI:10.1186/1687-1847-2014-279, concerns a different Clifford construction associated with generalized Fibonacci quaternions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.H`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.K`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.L`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.low`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit](CliffordLeafOrbit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](GlobalGcdSampling.md)
- Dependency: [D5/S3/Quantum/Algebra/CarryTransport/FibonacciOutputAlgebra](../../Quantum/Algebra/CarryTransport/FibonacciOutputAlgebra.md)
