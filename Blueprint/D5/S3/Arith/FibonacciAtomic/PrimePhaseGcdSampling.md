# Prime Phase Gcd Sampling

## Abstract

Sharp prime Fibonacci phase identification and simultaneous bounded natural counterexamples.

F(0)=0 and F(1)=1. All queried times are positive natural numbers. The signed reading takes the absolute value of the entire linear combination. The source reading uses actual nonnegative coordinates, not merely residue labels.

**Definition 1.1 (Signed local reading).**

$$\operatorname{G}\left(p, n, z, k\right) = \operatorname{gcd}\left(\operatorname{abs}\left(\operatorname{F}\left(k-1\right)\cdot n+\operatorname{F}\left(k\right)\cdot z\right), p\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.localGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state coordinates n,z are integers and the modulus p is natural.

**Definition 1.2 (Natural source reading).**

$$\operatorname{g}\left(H, a, b, k\right) = \operatorname{gcd}\left(\operatorname{F}\left(k+3\right)\cdot a+\operatorname{F}\left(k+4\right)\cdot b, H\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.sourceGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source coordinates a,b and the modulus H are natural numbers.

**Definition 1.3 (Prime-primitive signed state).**

$$\operatorname{Primitive}\left(p, n, z\right) \Leftrightarrow (\neg\operatorname{dvd}\left(p, \operatorname{abs}\left(n\right)\right) \lor \neg\operatorname{dvd}\left(p, \operatorname{abs}\left(z\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.primitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state is p-primitive when at least one coordinate is not divisible by p.

For each prime p, write r=zeroRank(p), the least positive d with p dividing F(d). For a finite positive-time table S, let A be its phase image modulo r. Set T=r-1 when r=p+1 and T=r otherwise.

$$
(r = \operatorname{zeroRank}\left(p\right)) \land (A = \{\operatorname{mod}\left(k, r\right) \mid k \in S\}) \land (T = \operatorname{if}\left(r = p+1, r-1, r\right))
$$

**Theorem 1.4 (Sharp identification and fixed-source late separation).**

$$\forall p \in \mathbb{N}, (\operatorname{Prime}\left(p\right)) \implies (\forall S \in \operatorname{Finset}\left(\mathbb{N}\right), (\forall k \in S, 0<k) \implies (((\forall n, z, nPrime, zPrime \in \mathbb{Z}, (\forall k \in S, \operatorname{G}\left(p, n, z, k\right) = \operatorname{G}\left(p, nPrime, zPrime, k\right)) \implies (\forall k \in \mathbb{N}, (0<k) \implies (\operatorname{G}\left(p, n, z, k\right) = \operatorname{G}\left(p, nPrime, zPrime, k\right)))) \Leftrightarrow (T\le\operatorname{card}\left(A\right))) \land ((\forall a, b, aPrime, bPrime \in \mathbb{N}, (\forall k \in S, \operatorname{g}\left(p, a, b, k\right) = \operatorname{g}\left(p, aPrime, bPrime, k\right)) \implies (\forall k \in \mathbb{N}, (0<k) \implies (\operatorname{g}\left(p, a, b, k\right) = \operatorname{g}\left(p, aPrime, bPrime, k\right)))) \Leftrightarrow (T\le\operatorname{card}\left(A\right))) \land ((\operatorname{card}\left(A\right)<T) \implies (\forall Q \in \mathbb{N}, (0<Q) \implies (\exists n, z, nPrime, zPrime \in \mathbb{Z}, \exists a, b, aPrime, bPrime \in \mathbb{N}, (\operatorname{Primitive}\left(p, n, z\right)) \land (\operatorname{Primitive}\left(p, nPrime, zPrime\right)) \land (a<Q\cdot p) \land (b<Q\cdot p) \land (aPrime<Q\cdot p) \land (bPrime<Q\cdot p) \land (\forall k \in \mathbb{N}, (0<k) \implies ((\operatorname{g}\left(Q\cdot p, a, b, k\right) = Q\cdot \operatorname{G}\left(p, n, z, k\right)) \land (\operatorname{g}\left(Q\cdot p, aPrime, bPrime, k\right) = Q\cdot \operatorname{G}\left(p, nPrime, zPrime, k\right)))) \land (\forall k \in S, (\operatorname{G}\left(p, n, z, k\right) = \operatorname{G}\left(p, nPrime, zPrime, k\right)) \land (\operatorname{g}\left(Q\cdot p, a, b, k\right) = \operatorname{g}\left(Q\cdot p, aPrime, bPrime, k\right))) \land (\forall B \in \mathbb{N}, \exists t \in \mathbb{N}, (B<t) \land (0<t) \land (\neg(t \in S)) \land (\operatorname{G}\left(p, n, z, t\right) = p) \land (\operatorname{G}\left(p, nPrime, zPrime, t\right) = 1) \land (\operatorname{g}\left(Q\cdot p, a, b, t\right) = Q\cdot p) \land (\operatorname{g}\left(Q\cdot p, aPrime, bPrime, t\right) = Q) \land (\operatorname{g}\left(Q\cdot p, aPrime, bPrime, t\right) = \operatorname{div}\left(Q\cdot p, p\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.prime_phase_gcd_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two identification statements include zero and nonprimitive states, hence constant saturated readings. Only the number of distinct queried phases matters; no answer at time zero or common content is supplied. The rank satisfies 3<=r<=p+1, and pairwise recovery gives distinct kernel directions. A unit scalar return preserves zero support, without requiring the Fibonacci step to return to the identity. Nonzero states have at most one zero phase. When r=p+1 every direction has one; otherwise an affine direction avoids all zero phases. Missing one phase in the proper case, or two in the full case, therefore gives indistinguishable primitive states. Their inverse-source residues (5n-3z,-3n+2z), scaled by Q, lie strictly below Qp and realize every positive-time reading simultaneously. Both states and both sources are fixed before the cutoff B. The later separating time alone varies. The local p,1 separation uses unscaled signed states even when p divides Q. Natural-source identification is modulo p, not a claimed general-modulus Qp identification criterion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.localGcd`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.prime_phase_gcd_sampling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.primitive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.sourceGcd`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](TimeSampling.md)
