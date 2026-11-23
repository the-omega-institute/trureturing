# Lattice Enclosures and Cyclic Collision Mass

## Abstract

Certified lattice coordinates give upper and lower collision bounds through a finite character sum.

Use a finite coordinate set, real frequencies g(j), integer approximations a(j), and weights w(j). Let E(t) be the sum of products of weighted multinomial coefficients of ordered degree-p pairs with real frequency gap at most t. Their lattice coordinates are the integer sums of a(j) with the same counts. Let C(R) count the same weighted ordered pairs whose lattice difference modulo q belongs to a finite residue set R. Write R(H) for the image of the integer interval from −H to H in ZMod q. Each residue occurs only once.

For both transfers below the weights are nonnegative, the lattice step s and the coordinate error e satisfy s≥0 and e≥0, and |g(j)−s a(j)|≤e for every j. For the first transfer take s>0 and let H be the floor of (t+2pe)/s.

**Theorem 1.1 (The modular band contains the real near-collisions).**

$$\operatorname{E}\left(t\right) \le \operatorname{C}\left(\operatorname{R}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.tailCollisionMass_le_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed difference of the errors is bounded by e times the sum of the absolute count differences. For two degree-p vectors that sum is at most 2p.

For the reverse transfer assume each a(j) lies in an integer interval [l,u] and p(u−l)+H<q.

**Theorem 1.2 (A bounded lattice spread excludes wraparound).**

$$\operatorname{C}\left(\operatorname{R}\left(H\right)\right) \le \operatorname{E}\left(s \cdot H + 2 \cdot p \cdot e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_le_tail_of_no_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Congruent integers differ by a multiple of q. The spread of the degree-p lattice sums makes this multiple zero for a residue in R(H). The strict inequality excludes aliasing at an endpoint.

For the Fourier identity assume q>0. Write S(k)=Σ w(j)χ(k,a(j)), where χ(k,x) is the positive standard character at x in ZMod q.

**Theorem 1.3 (Character orthogonality evaluates the cyclic mass).**

$$q \cdot \operatorname{C}\left(R\right) = \sum_{k \in \operatorname{ZMod}\left(q\right)} \left|\operatorname{S}\left(k\right)\right|^{2 \cdot p} \cdot (\sum_{y \in R} \operatorname{chi}\left(k, -y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multinomial expansion of the power gives the weighted character sum over the degree vectors. Conjugation introduces the second vector with opposite sign, and the sum over characters retains exactly the differences in R.

With certified enclosures for fixed ζ ordinates, the first transfer and the exact Fourier identity give a finite upper certificate. A bound with the required degree, resolution and computational cost is still open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_fourier`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_le_tail_of_no_wrap`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.tailCollisionMass_le_cyclic`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
- Dependency: [D5/S3/Fourier/FinitePoisson](../FinitePoisson.md)
