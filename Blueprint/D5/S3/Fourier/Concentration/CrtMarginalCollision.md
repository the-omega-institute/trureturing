# Joint collision mass from two cyclic marginals

## Abstract

Separate collision statistics leave the mixed character contribution undetermined.

On the residues modulo six let P give masses 1/2, 1/4, 1/4 at 0, 3, 4. Let Q give masses 3/4 and 1/4 at 0 and 1. All other masses vanish in each law. For each positive integer p, write E(P) and E(Q) for the collision masses of two independent p-fold sums modulo six. Write A and B for the collision masses for P modulo two and three, and C and F for those for Q.

**Theorem 1.1 (Identical marginal collision profiles with opposite factorization errors).**

$$\begin{aligned}A=C \land B=F\\\operatorname{E}\left(P\right)<A \cdot B<\operatorname{E}\left(Q\right)\\\operatorname{E}\left(P\right)-A \cdot B=\frac{\frac{1}{16}^{p}-\frac{7}{64}^{p}}{3}\\\operatorname{E}\left(Q\right)-A \cdot B=\frac{\frac{13}{16}^{p}-\frac{7}{64}^{p}}{3}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CrtMarginalCollision.crt_marginal_collision_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two weights induce the same law modulo two and the same law modulo three. Use the exact cyclic character average `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_fourier` to evaluate the collision mass of the degree-p sums. The squared mixed Fourier magnitudes of P and Q are 1/16 and 13/16. The product of the two pure squared magnitudes is 7/64. Each mixed contribution occurs twice among the six characters. The difference from A B is therefore controlled by these distinct pth powers. This comparison treats a fixed finite modular law. The weighted near-collision estimate for actual zeta ordinates remains open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CrtMarginalCollision.crt_marginal_collision_gap`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_fourier`
- Dependency: [D5/S3/Fourier/Concentration/CyclicCollisionCertificate](CyclicCollisionCertificate.md)
