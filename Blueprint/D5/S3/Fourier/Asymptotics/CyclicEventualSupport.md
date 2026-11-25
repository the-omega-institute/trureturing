# Exact eventual support of the cyclic minimizer

## Abstract

For every positive budget, the two-cosine squared-mass minimizer eventually has a closed front window and all nearest antipodal sites as its positive support.

**Theorem 1.1 (Eventual support for both parities and all activation levels).**

$$\forall \lambda, 0 < \lambda, m = \frac{\lambda}{8 \cdot \pi^{2}}, \exists n \in Nat,\; \exists t \in Real,\; \exists Z \in Real,\; \exists w \in \operatorname{LatticeWeights}\left(\right),\; \left(0 < n \land \left(\left(\frac{n^{2} - 1}{5} \le m \land m < \frac{n \cdot \left(n + 2\right)}{5}\right) \land \operatorname{Activation}\left(m, n, t, Z, w\right)\right)\right) \land \left(\exists Q \in Nat,\; \forall q \in Nat,\; \left(0 < q \land Q \le q\right) \Rightarrow \left(\left(\exists v \in \operatorname{Feasible}\left(q, 1 - \frac{\lambda}{q^{2}}\right),\; \operatorname{IsMinOn}\left(E, \operatorname{Feasible}\left(q, 1 - \frac{\lambda}{q^{2}}\right), v\right) \land \left(\operatorname{M}\left(1, v\right) = 1 - \frac{\lambda}{q^{2}} \land \left(\operatorname{M}\left(2, v\right) = 1 - \frac{\lambda}{q^{2}} \land \left(\forall u \in \operatorname{Feasible}\left(q, 1 - \frac{\lambda}{q^{2}}\right),\; u \ne v \Rightarrow \operatorname{E}\left(v\right) < \operatorname{E}\left(u\right)\right)\right)\right)\right) \land \left(\forall v \in \operatorname{Feasible}\left(q, 1 - \frac{\lambda}{q^{2}}\right),\; \operatorname{IsMinOn}\left(E, \operatorname{Feasible}\left(q, 1 - \frac{\lambda}{q^{2}}\right), v\right) \Rightarrow \left(\forall i \in \operatorname{ZMod}\left(q\right),\; 0 < \operatorname{v}\left(i\right) \Leftrightarrow \left(\operatorname{Centered}\left(i\right)^{2} \le t \lor \left(\forall j \in \operatorname{ZMod}\left(q\right),\; \operatorname{c}\left(i\right) \le \operatorname{c}\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicEventualSupport.cyclic_eventual_exact_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive budget λ, set m = λ/(8π²), and take the integer-lattice activation data at m. The lattice weight at j is (t−j²)₊/Z. For all sufficiently large positive moduli q, the unique cyclic minimizer has both cosine moments equal to 1−λ/q². The positive sites of every minimizer are exactly those with centered j² ≤ t and those attaining the smallest sampled first cosine. The cutoff applies to even and odd moduli.

Take h = 2π/q and d = 0 or 1/2 on even or odd moduli respectively. Use rows (1, 1−c, (1−c²)/h²) on the front window and the one or two closest antipodal sites. The Gram matrix has an invertible limit because its rows at the center, a front neighbor, and a closest antipode span three dimensions. Its solve matches (1, 2mh², m), with limiting coefficients (t/Z, −(t−d²)/(2Z), −1/Z).

The total antipodal weight divided by h² tends to μ = 3m/4. Positive limiting front weights stay positive. At t = N², the front variation has mass −μ and squared-index moment m₄/3 − d²μ, where m₄ is the fourth moment of the lattice law. Adding μ times the lattice law gives zero mass, positive squared-index moment, and quadratic leading coefficient 1/(3Z) in the squared index. The weighted pair identity gives a strictly positive value at N². The lattice law vanishes there, so this is also the sign of the original variation.

The two first excluded cosine levels are −cos((d+1)h) and cos((N+1)h), with N the front radius. Their polynomial readings have strictly negative limits. Every excluded cosine lies between them, so convexity gives the strict sign throughout the complement. Exact moments and the squared-distance identity certify the positive part as the unique minimizer.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicEventualSupport.cyclic_eventual_exact_support`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicParityLimit](CyclicParityLimit.md)
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicSupportCertificate](CyclicSupportCertificate.md)
