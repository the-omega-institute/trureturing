# Exact Root Arithmetic in the Dyadic Solenoid

## Abstract

The odd part q of a positive degree determines its cyclic multiplication kernel and the exact cardinality q of every root fiber in the dyadic solenoid.

Use the existing DyadicSolenoid from DyadicTimeSeparation: sequences in AddCircle(1) satisfying 2 x(n+1)=x(n), with the topology inherited from the product of circles. Circle period one is fixed throughout. No new carrier or replacement topology is introduced.

**Theorem 1.1 (Cyclic kernels and exact root fibers).**

$$\forall k \in N,\; \forall q \in N,\; \operatorname{Odd}\left(q\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{AddEquiv}\left(\operatorname{Kernel}\left(\operatorname{nsmul}\left(2^{k} \cdot q, S2\right)\right), \operatorname{ZMod}\left(q\right)\right)\right) \land \left(\forall a \in S2,\; \operatorname{Finite}\left(\operatorname{RootFiber}\left(2^{k} \cdot q, a\right)\right) \land \operatorname{card}\left(\operatorname{RootFiber}\left(2^{k} \cdot q, a\right)\right) = q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/DyadicRootFiberArithmetic.dyadic_root_fiber_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and odd natural q, put m=2^k q. The kernel of the additive multiplication homomorphism by m is additively equivalent to ZMod q. For every a in S2 the subtype of x satisfying m x=a is finite and its Nat.card is q. Oddness implies q is positive; q=1, k=0 and m=1 are included. Every positive natural degree has this factorization by Nat.exists_eq_two_pow_mul_odd. Thus multiplication by powers of two is bijective, and all other positive degrees have exactly their odd part many roots at each target.

Write q=2d+1 and s=d+1. On q-torsion in the circle, 2s acts as q+1, hence as the identity. Compatibility therefore forces x(n+1)=s x(n), so x(n)=s^n x(0). Conversely each ZMod q element z gives the compatible sequence s^n ZMod.toAddCircle(z). Coordinate zero proves injectivity using ZMod.toAddCircle_injective. AddCircle.nsmul_eq_zero_iff supplies every possible initial coordinate as r/q modulo one, proving surjectivity. The zero kernel of doubling in dyadic_time_separation removes the factor 2^k. Its positive-degree surjectivity, together with AddMonoidHom.fiberEquivKerOfSurjective, identifies each root fiber with that cyclic kernel.

For the doubling dynamics T(x)=2x, induction gives T iterated n times equal to multiplication by 2^n. For n>0, T^n(x)=x is equivalent to (2^n-1)x=0; the latter degree is odd. Consequently the number of points fixed by the n-th iterate is exactly 2^n-1. This counts points whose period divides n, not points of least period exactly n. It is a consequence of the root arithmetic, without an entropy assertion.

There is also an alternative algebraic rational-time construction. Apply FiniteRootFiberCoherence.finite_root_fibers_rational_coherence with H=Multiplicative S2 and h=Multiplicative.ofAdd thirdPoint. The exact arithmetic above gives finite root fibers in every positive degree, and dyadic_time_separation supplies their nonemptiness. The finite inverse-system theorem then gives a homomorphism from Multiplicative Q to Multiplicative S2 carrying 1 to h, equivalently an additive rational homomorphism with value thirdPoint at 1. This is an alternative inference to the parent's Baer argument, not a new existence assertion. The parent also proves every such rational homomorphism is discontinuous in the usual rational topology and that no continuous real homomorphism reaches thirdPoint at time 1. Algebraic coherence therefore supplies no continuous time flow there.

These are classical solenoid arithmetic and dynamics phenomena. R. N. Gumerov, On finite-sheeted covering mappings onto solenoids, arXiv:math/0312288v1, gives context for power maps on solenoids. The proof here uses the specified additive inverse-limit carrier directly. No literature novelty or formal identification with another solenoid model is claimed.

## References

- Truth anchor: `D5/S1/Solenoid/DyadicRootFiberArithmetic.dyadic_root_fiber_arithmetic`
- Dependency: [D5/S1/Solenoid/DyadicTimeSeparation](DyadicTimeSeparation.md)
