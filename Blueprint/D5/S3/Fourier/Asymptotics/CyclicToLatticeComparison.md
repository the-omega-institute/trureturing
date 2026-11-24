# Quantitative comparison of cyclic and lattice minima

## Abstract

Two cosine moments give a uniform comparison with the integer-lattice minimum.

**Theorem 1.1 (Energy and distance bounds on the finite cycle).**

$$\begin{aligned}&0 \le \operatorname{L}\left(m\right) - \operatorname{E}\left(q, a\right) \le \frac{2 \cdot t}{Z} \cdot \frac{\lambda}{q^{2}} \le 2 \cdot \frac{\lambda}{q^{2}},\\&\operatorname{D}\left(q, v, w\right) \le \operatorname{E}\left(v\right) - \operatorname{L}\left(m\right) + \frac{2 \cdot t}{Z} \cdot \frac{\lambda}{q^{2}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison.cyclic_to_lattice_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be a positive integer, q>2n a modulus and λ real. Put m=λ/(8π²) and a=1−λ/q², and require (n²−1)/5≤m≤n(n+2)/5. The interval in particular gives λ≥0. Let w be the integer-lattice minimizer furnished by the activation theorem for this interval, with radius parameter t and normalizer Z. Write L(m) for its squared mass.

The finite probability weights have full first and second cosine moments at least a. The minimum E_q(a) is attained. For each feasible weight v, E(v) denotes its squared mass and D_q(v,w) is the sum of squared differences against w at the centered residue representatives. The displayed comparison bounds D_q(v,w) for every competitor and bounds the minimum using the same lattice law.

For a centered residue j, write θ=2πj/q. On the full centered range, θ² cos θ≤sin² θ. The sign suffices when cos θ≤0. Otherwise the half-angle estimate sin(|θ|/2)≥(|θ|/2)cos(θ/2), together with cos⁴(θ/2)≥cos θ, gives the inequality. Consequently (t cos θ−(q sin θ/(2π))²)/Z lies below the lattice weight. Summing against feasible v controls the cross term of the squared-distance identity. The zero site contributes t to Z, giving t/Z≤1.

For the upper bound the lattice support embeds injectively on the cycle since q>2n. The cosine deficits of the embedded law are bounded by its second moment times 2π²/q² and 8π²/q² for the two modes. The inequality 1−cos x≤x²/2 supplies both estimates. The finite feasible set is closed in the unit box, so continuity gives a minimizer.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison.cyclic_to_lattice_comparison`
- Dependency: [D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation](LatticeSquareMomentActivation.md)
