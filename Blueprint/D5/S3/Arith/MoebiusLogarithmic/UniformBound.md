# Uniform coprime logarithmic sums

## Abstract

Finite logarithmic Moebius sums have an unconditional bound uniform in the modulus and cutoff.

**Definition 1.1 (The exact logarithmic coefficients).**

$$\forall q\in\mathbb{N},x\in\mathbb{R},\operatorname{S}\left(q, x\right) = \sum_{1\le n\le \operatorname{floor}\left(x\right),\operatorname{gcd}\left(n, q\right) = 1}\frac{\operatorname{mu}\left(n\right)}{n}\cdot \operatorname{log}\left(\frac{x}{n}\right)$$

*Formalization.* `D5/S3/Arith/MoebiusLogarithmic/UniformBound.coprimeLogSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural q and real x, S(q,x) is the finite sum over positive integers n at most the natural floor of x and coprime to q. It uses the actual integer Moebius function cast to the reals and the real natural logarithm. For x<1 the sum is empty. A term n=x, when present, has zero logarithm.

**Theorem 1.2 (The elementary base estimate).**

$$\forall x\in\mathbb{R},1\le x\Rightarrow0\le \operatorname{S}\left(1, x\right)\land \operatorname{S}\left(1, x\right)\le2\cdot(1-\frac{1}{x})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/MoebiusLogarithmic/UniformBound.logarithmic_base_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x at least one, the unrestricted logarithmic sum lies between zero and 2(1-1/x). Let F(t) be the integral of (u-floor(u))/u^2 from one to t. This primitive is increasing and lies between zero and 1-1/t. Abel summation gives F(t)=log(t)-H(floor(t))+floor(t)/t, where H is the harmonic sum. Finite Moebius cancellation with harmonic weights then expresses S(1,x) as 1-1/x plus the sum of mu(n)F(x/n)/n. The bound on every reciprocal Moebius prefix and finite summation by parts control the absolute value of this last sum by F(x).

**Theorem 1.3 (All moduli and positive real cutoffs).**

$$\forall q\in\mathbb{N},x\in\mathbb{R},1\le q\land0<x\Rightarrow0\le \operatorname{S}\left(q, x\right)\land \operatorname{S}\left(q, x\right)\le\frac{2\cdot q}{\operatorname{phi}\left(q\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/MoebiusLogarithmic/UniformBound.coprime_log_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural q and positive real x, the coprime logarithmic sum is nonnegative and at most 2q/phi(q), where phi is Euler's actual totient. The finite coefficient convolution gives S(q,x)=sum S(1,x/d)/d over positive d at most x whose prime divisors divide q. All prime powers in this support remain present. The reciprocal mass of that finite set is at most the finite-prime Euler product product (1-1/p)^(-1)=q/phi(q). Applying the base estimate term by term proves both inequalities.

No relation between q and x is required. The cases q=1, x<1, and x=1 are included. Repeated prime factors of q do not change the supported primes. These finite coefficient estimates do not establish the Riemann hypothesis or the strict Robin inequality for all integers above 5040.

## References

- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/UniformBound.coprimeLogSum`
- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/UniformBound.coprime_log_uniform_bound`
- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/UniformBound.logarithmic_base_bound`
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution](CoprimeConvolution.md)
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound](ReciprocalBound.md)
