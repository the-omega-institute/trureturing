# Sharp Factorial Divisor Weight Resolution

## Abstract

For each fixed real C>1, on a factorial congruence domain with height (m!)^C, the largest relative divisor-weight response has a sharp logarithmic rate. The same congruent pair has a diverging additive gap.

**Definition 1.1 (Prime interval).**

$$\forall m\in \mathbb{N}, \forall x\in \mathbb{R}, \operatorname{S}\left(m, x\right) = \{p\in \mathbb{N}\mid \operatorname{Prime}\left(p\right)\land m<p\le \left\lfloor x\right\rfloor\}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.blockSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(m,x) is the finite set of primes p with m < p <= floor(x), where the floor takes values in the naturals and is zero for negative x.

**Definition 1.2 (Prime block).**

$$\forall m\in \mathbb{N}, \forall x\in \mathbb{R}, \operatorname{Q}\left(m, x\right) = \prod_{p\in \operatorname{S}\left(m, x\right)}p$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.primeBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q(m,x) multiplies every prime in S(m,x) once; an empty product is one.

**Definition 1.3 (Lower cutoff).**

$$\forall C\in \mathbb{R}, \forall m\in \mathbb{N}, \operatorname{Y}\left(C, m\right) = \frac{C-1}{8}m\operatorname{log}\left(m\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.lowerCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Y(C,m)=((C-1)/8)*m*log(m). The logarithm is the real logarithm.

**Definition 1.4 (Factorial prime-block number).**

$$\forall C\in \mathbb{R}, \forall m\in \mathbb{N}, \operatorname{A}\left(C, m\right) = m!\operatorname{Q}\left(m, \operatorname{Y}\left(C, m\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.lowerNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(C,m)=m!*Q(m,Y(C,m)). Thus A(C,m) and m! have the same zero residue modulo m!.

**Definition 1.5 (Actual ratio domain).**

$$\forall C\in \mathbb{R}, \forall m\in \mathbb{N}, \operatorname{V}\left(C, m\right) = \{\frac{\operatorname{Z}\left(a\right)}{\operatorname{Z}\left(b\right)}\mid a,b\in \mathbb{N},1\le a,b\le (m!)^{C},a\equiv b\pmod{m!}\}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.pairValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(C,m) consists of Z(a)/Z(b) for positive natural integers a,b at most (m!)^C and congruent modulo m!. Here Z(n)=sigma(n)/n and sigma sums the positive divisors. This is one common height and congruence domain.

**Definition 1.6 (Extreme ratio).**

$$\forall C\in \mathbb{R}, \forall m\in \mathbb{N}, \operatorname{E}\left(C, m\right) = \operatorname{sup}\left(\operatorname{V}\left(C, m\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.extremeRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(C,m) is the real supremum of V(C,m); the supremum of an empty admissible set is zero. For C>1 the theorem shows that V is finite, contains one, and contains E, so this supremum is an actual maximum.

**Theorem 1.7 (Sharp relative rate and additive divergence).**

$$\forall C\in \mathbb{R}, 1<C\Rightarrow (\forall m\in \mathbb{N}, \operatorname{Finite}\left(\operatorname{V}\left(C, m\right)\right)\land 1\in \operatorname{V}\left(C, m\right)\land \operatorname{E}\left(C, m\right)\in \operatorname{V}\left(C, m\right)\land 1\le \operatorname{E}\left(C, m\right))\land (\exists M\in \mathbb{N}, \forall m\in \mathbb{N}, M\le m\Rightarrow 0<\operatorname{A}\left(C, m\right)\land \operatorname{A}\left(C, m\right)\le (m!)^{C}\land m!\le (m!)^{C}\land \operatorname{A}\left(C, m\right)\equiv m!\pmod{m!}\land \operatorname{gcd}\left(m!, \operatorname{Q}\left(m, \operatorname{Y}\left(C, m\right)\right)\right) = 1\land \frac{\operatorname{Z}\left(\operatorname{A}\left(C, m\right)\right)}{\operatorname{Z}\left(m!\right)} = \prod_{p\in \operatorname{S}\left(m, \operatorname{Y}\left(C, m\right)\right)}(1+\frac{1}{p}))\land \lim_{m\to\infty}(\operatorname{E}\left(C, m\right)-1)\frac{\operatorname{log}\left(m\right)}{\operatorname{log}\left(\operatorname{log}\left(m\right)\right)} = 1\land \lim_{m\to\infty}(\frac{\operatorname{Z}\left(\operatorname{A}\left(C, m\right)\right)}{\operatorname{Z}\left(m!\right)}-1)\frac{\operatorname{log}\left(m\right)}{\operatorname{log}\left(\operatorname{log}\left(m\right)\right)} = 1\land \lim_{m\to\infty}\frac{\operatorname{Z}\left(\operatorname{A}\left(C, m\right)\right)-\operatorname{Z}\left(m!\right)}{\operatorname{exp}\left(\gamma\right)\operatorname{log}\left(\operatorname{log}\left(m\right)\right)} = 1\land \lim_{m\to\infty}\operatorname{Z}\left(\operatorname{A}\left(C, m\right)\right)-\operatorname{Z}\left(m!\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any real C>1. For every natural m, the set V(C,m) is finite, contains one, and contains its maximum E(C,m), which is at least one. For all sufficiently large m, A(C,m) is positive, both A(C,m) and m! are at most (m!)^C, they are congruent modulo m!, and Q(m,Y(C,m)) is coprime to m!. The normalized divisor-weight quotient Z(A(C,m))/Z(m!) is the product of 1+1/p on S(m,Y(C,m)). Both the maximum relative excess and this pair's relative excess, multiplied by log(m)/log(log(m)), tend to one. For this same pair the additive gap divided by exp(gamma)*log(log(m)) tends to one, and the additive gap tends to positive infinity. Here gamma is the Euler--Mascheroni constant.

For the upper estimate, split the prime factors at X=m*log(m)*log(log(m)). The factorial-congruence squeeze bounds the small factors. The complete Euler product on m<p<=X and the logarithmic tail bound give the matching upper rate. Mertens' logarithmic error estimate controls the interval product at this scale.

For the lower estimate, take the actual pair A(C,m),m! with cutoff Y(C,m). The primorial bound and the logarithmic factorial lower bound place both integers in the prescribed height domain. Coprimality gives the product of 1+1/p exactly. Factoring it as the interval Euler product times the product of 1-1/p^2 leaves a correction between 1-1/m and one. This gives the matching lower rate. The logarithms of this pair's ratio and the maximum tend to zero, so exponentiation preserves the first-order excess.

Finally Z(m!)/(exp(gamma)*log(m)) tends to one. Multiplication with the pair's relative excess gives the additive asymptotic. Uniform convergence of relative responses therefore does not imply that additive gaps vanish. This conclusion supplies no Robin inequality violation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.blockSet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.extremeRatio`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.lowerCutoff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.lowerNumber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.pairValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.primeBlock`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer](UniformDivisorWeightTransfer.md)
