# Affine Lcm Robin Margins

## Abstract

Two actual affine lcm families have positive Robin margins and an unbounded weight gap under explicit analytic premises.

**Definition 1.1 (Actual affine seed lcm).**

$$\operatorname{Q}\left(L\right) = \operatorname{lcm}\left(\right)_{0\le a<L}(3a+5)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.affineLcm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q(L) is the finite lcm of the natural seeds 3a+5 for 0<=a<L. The empty lcm is one.

**Definition 1.2 (Saturated core).**

$$\operatorname{A}\left(L\right) = 3^{\operatorname{NatLog}\left(3, L\right)}\operatorname{Q}\left(L\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.saturatedCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(L)=3^(Nat.log 3 L)*Q(L). For positive L the natural logarithmic exponent agrees with the natural floor of log(L)/log(3).

**Definition 1.3 (Full short signature).**

$$\operatorname{O}\left(L, N\right) = (\operatorname{v}\left(3, N\right),\operatorname{gcdVector}\left(L, N\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.shortSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

O(L,N) retains v_3(N) and the function a:Fin L -> gcd(N,3a+5), so every sampled gcd coordinate remains visible.

**Definition 1.4 (Visible divisor core).**

$$\operatorname{B}\left(L, N\right) = 3^{\operatorname{v}\left(3, N\right)}\operatorname{gcd}\left(N, \operatorname{Q}\left(L\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.visibleCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(L,N)=3^v_3(N)*gcd(N,Q(L)). Prime valuations use natural factorization; the exact fiber assertion is restricted to positive N.

**Definition 1.5 (Residue prime logarithmic sum).**

$$\operatorname{theta}\left(r, y\right) = \sum_{\operatorname{Prime}\left(p\right),p\le y,\operatorname{mod}\left(p, 3\right) = r}\operatorname{log}\left(p\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.residueTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

theta(r,y) sums log(p) over primes p<=floor(y) with p mod 3=r. The natural floor convention makes the sum empty at negative cutoffs.

**Definition 1.6 (Robin margin).**

$$\operatorname{Delta}\left(N\right) = E\operatorname{log}\left(\operatorname{log}\left(N\right)\right)-\operatorname{U}\left(N\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.robinMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta(N)=exp(gamma)*log(log(N))-sigma(N)/N. The intended Robin domain is N>1; the theorem eventually gives N>5040.

**Theorem 1.7 (Two positive margins in one actual signature fiber).**

$$\forall C\in \mathbb{R}, 0<C\land \operatorname{Hypothesis3021}\left(\right)\Rightarrow ((\forall L\in \mathbb{N}, 2\le L\Rightarrow \operatorname{ArithmeticContext}\left(L\right))\land \lim_{L\to\infty}(\frac{\operatorname{log}\left(\operatorname{A}\left(L\right)\right)}{\frac{3}{4}m}) = 1\land \lim_{L\to\infty}(\frac{\operatorname{log}\left(\operatorname{A}\left(L\right)\right)}{\frac{9}{4}L}) = 1\land \lim_{L\to\infty}(\operatorname{U}\left(\operatorname{A}\left(L\right)\right)-E(\operatorname{log}\left(m\right)-\frac{\operatorname{log}\left(2\right)}{2})) = 0\land \lim_{L\to\infty}(\operatorname{Delta}\left(\operatorname{A}\left(L\right)\right)) = E\operatorname{log}\left(\frac{3}{2\operatorname{sqrt}\left(2\right)}\right)\land 0<E\operatorname{log}\left(\frac{3}{2\operatorname{sqrt}\left(2\right)}\right)\land \lim_{L\to\infty}(\frac{\operatorname{log}\left(\operatorname{H}\left(L\right)\right)}{x}) = 1\land \lim_{L\to\infty}(\operatorname{U}\left(\operatorname{H}\left(L\right)\right)-E(\operatorname{log}\left(x\right)-\frac{\operatorname{log}\left(2\right)}{2})) = 0\land \lim_{L\to\infty}(\operatorname{Delta}\left(\operatorname{H}\left(L\right)\right)) = \frac{E}{2}\operatorname{log}\left(2\right)\land 0<\frac{E}{2}\operatorname{log}\left(2\right)\land \lim_{L\to\infty}((\frac{\operatorname{U}\left(\operatorname{H}\left(L\right)\right)}{\operatorname{U}\left(\operatorname{A}\left(L\right)\right)}-1)\frac{\operatorname{log}\left(L\right)}{\operatorname{log}\left(\operatorname{log}\left(L\right)\right)}) = 1\land \lim_{L\to\infty}(\frac{\operatorname{U}\left(\operatorname{H}\left(L\right)\right)-\operatorname{U}\left(\operatorname{A}\left(L\right)\right)}{E\operatorname{log}\left(\operatorname{log}\left(L\right)\right)}) = 1\land \lim_{L\to\infty}(\operatorname{U}\left(\operatorname{H}\left(L\right)\right)-\operatorname{U}\left(\operatorname{A}\left(L\right)\right)) = \infty\land (\exists L_{0}\in \mathbb{N}, \forall L\in \mathbb{N}, L_{0}\le L\Rightarrow \operatorname{EventualContext}\left(C, L, \operatorname{A}\left(L\right), \operatorname{H}\left(L\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/AffineLcmRobinMargins.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any real C>0, without requiring C>1. Assume theta(r,y)=y/2+O(y/log(y)^3) for each r=1,2 and the additive premise P(y)-exp(gamma)*log(y)->0. Here P is the complete inverse Euler product over primes at most y. Along all natural L tending to infinity, put m=3L+2, x=(C/256)*m*log(m), T=product(m<p<=x) p and H=A(L)*T. The displayed size and weight limits hold with E=exp(gamma). Both explicit margin constants are positive. Both normalized contrast rates tend to one, and U(H)-U(A) tends to positive infinity.

For every L>=2, Q and A are positive, 3 does not divide Q, v_3(A)=Nat.log 3 L, D_L divides A which divides D_m, and B(L,A)=A. The prime support and positive-N fiber identities below hold for every such L, and 5040 divides A whenever L>=16. The eventual context holds simultaneously: A and H are positive, exceed 5040, are divisible by 5040, satisfy U(N)<E*log(log(N)), and are at most exp(C*L*log(L)). Their full short signatures agree, B(L,A)=B(L,H)=A, and A is coprime to T. Also 3 does not divide Q, v_3(A)=Nat.log 3 L, and D_L divides A, which divides D_m, where D_j=lcm(1,...,j). For every prime p, p divides Q exactly when (p mod 3=1 and 2p<=m) or (p mod 3=2 and p<=m). For every positive N, O(L,N)=O(L,A) exactly when N=A*t for a natural t>=1 coprime to 3; every such N has visible core A.

The proof uses the actual affine prime-power occurrence witnesses, including the seed 8 for the prime power 2. Abel summation controls the missing residue-one band m/2<p<=m. The same band and valuation defect enter both exact Euler identities. The additive product premise supplies the constant terms. The intermediate affine lcm size asymptotic is classical; see Qian and Hong, arXiv:1204.5415v2, Corollary 1.2 with a=3,b=2,l=1,m=0. The conclusions concern these two specified families under the stated premises and do not classify Robin truth on the whole fiber.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.affineLcm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.residueTheta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.robinMargin`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.saturatedCore`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.shortSignature`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.visibleCore`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineLcmRobinMargins.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic](AffineLcmCoreArithmetic.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution](ModularDivisorWeightResolution.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer](UniformDivisorWeightTransfer.md)
