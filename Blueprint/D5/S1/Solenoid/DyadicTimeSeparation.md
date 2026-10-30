# Algebraic and Continuous Time in the Dyadic Solenoid

## Abstract

The compact connected dyadic solenoid admits algebraic rational time at a nonzero order-three point, but no continuous rational or real time there.

Let S2 be the additive subgroup of the product of unit additive circles consisting of sequences x with 2 times x(n+1) equal to x(n). Its topology is the subspace topology of that product. This is the dyadic carrier, distinct from the all-positive-degree UniversalSolenoid: only doubling compatibility is imposed here, and S2 has a nonzero point h with coordinates (-1)^n/3 modulo one.

**Theorem 1.1 (A divisible compact connected group separates algebraic and continuous time).**

$$\operatorname{Compact}\left(S2\right) \land \left(\operatorname{Connected}\left(S2\right) \land \left(\operatorname{Continuous}\left(j\right) \land \left(\operatorname{DenseRange}\left(j\right) \land \left(\left(\forall m \in N,\; 0 < m \Rightarrow \operatorname{Surjective}\left(\operatorname{multiplication}\left(m, S2\right)\right)\right) \land \left(\left(\forall x \in S2,\; 2 \cdot x = 0 \Rightarrow x = 0\right) \land \left(\neg(h = 0) \land \left(3 \cdot h = 0 \land \left(\left(\exists phi \in \operatorname{AddHom}\left(Q, S2\right),\; \operatorname{phi}\left(1\right) = h\right) \land \left(\left(\forall theta \in \operatorname{AddHom}\left(Q, S2\right),\; \operatorname{theta}\left(1\right) = h \Rightarrow \left(\left(\forall n \in N,\; \operatorname{theta}\left(\frac{1}{4}^{n}\right) = h\right) \land \neg(\operatorname{Continuous}\left(theta\right))\right)\right) \land \neg(\exists psi \in \operatorname{AddHom}\left(R, S2\right),\; \operatorname{Continuous}\left(psi\right) \land \operatorname{psi}\left(1\right) = h)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/DyadicTimeSeparation.dyadic_time_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S2 is a compact connected abelian topological group. For every positive integer m, multiplication by m is surjective. Multiplication by two has zero kernel. The point h is nonzero and 3 times h is zero. There exists an additive homomorphism phi from the rational numbers to S2 with phi(1)=h. Every such homomorphism satisfies phi((1/4)^n)=h for every natural n and is discontinuous for the usual rational topology. There is no continuous additive homomorphism psi from the real numbers to S2 with psi(1)=h.

The map j from the real line has coordinate j(t)(n)=t/2^n modulo one. It is a continuous additive homomorphism with dense image. For a finite set of coordinates choose its largest index N, lift x(N) to a real representative r, and take t=2^N r. Compatibility matches every earlier coordinate exactly. The compatibility equations are closed equalizers in a compact product, proving compactness; the dense continuous image of the connected real line proves connectedness. The image of multiplication by a positive m is compact and closed. It contains j of the real line because t/m is a real preimage, so density makes multiplication surjective.

Compatibility also shows that a point killed by doubling has every coordinate zero. At the alternating third-period point, doubling negates each coordinate and tripling kills it. Divisibility makes the underlying abelian group injective as an integer module. Baer's extension property extends the homomorphism from the integers sending 1 to h along the inclusion of the integers into the rationals. This constructs a genuine additive rational homomorphism without imposing continuity.

Doubling is injective, hence so is multiplication by four, and 4h=h. For any rational homomorphism anchored at h, the recurrence 4 phi((1/4)^(n+1))=phi((1/4)^n) therefore forces every value to equal h. The arguments tend to zero in the usual rational topology, while the image remains the nonzero constant h, contradicting continuity and Hausdorff uniqueness of limits. Restricting a continuous real homomorphism along the continuous rational inclusion gives the real-time obstruction. For the discrete topology on the rational domain every map is continuous; the obstruction concerns its usual topology. The dense real flow j exists, but cannot take the value h at time 1.

These are classical solenoid phenomena. R. N. Gumerov, On finite-sheeted covering mappings onto solenoids, arXiv:math/0312288v1, defines the dyadic case by constant bonding degree two. Propositions 1 and 2 discuss surjective power maps and the homeomorphism property for primes repeated infinitely in the bonding sequence. That multiplicative-circle account provides classical context; the assertions here are proved directly on the displayed additive-circle carrier, without asserting a formally verified identification of the two models or a new result in the literature.

## References

- Truth anchor: `D5/S1/Solenoid/DyadicTimeSeparation.dyadic_time_separation`
