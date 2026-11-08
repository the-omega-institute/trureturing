# HsfThreeLevelCoefficients

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Definition 1.1 (H).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-level denominator p^2+pq+q^2.

**Definition 1.2 (Q).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product H(p,q)H(q,r)H(r,p).

**Definition 1.3 (edgeNumerator).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeNumerator`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual pair numerator pq(p-q)^2(p^2-pq+q^2)(p^2+7pq+q^2).

**Definition 1.4 (rho).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical HsfBalancedSpectralCertificate.kappa evaluated at q/p; its explicit closed formula is proved for positive p,q.

**Definition 1.5 (symmetricF).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.symmetricF`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.symmetricF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicitly specified triangle numerator of spectral degree fifteen, written in the elementary symmetric variables of weights one, two and three.

**Definition 1.6 (F).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The triangle numerator at e=p+q+r, f=pq+qr+rp, g=pqr.

**Definition 1.7 (Xi).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual triangle coefficient 9pqrF/(4Q^3), used for the real part of the oriented source cycle.

**Definition 1.8 (closedCubic).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.closedCubic`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.closedCubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual closed cubic with edge weights rho(p,q),rho(q,r),rho(r,p) and cycle coefficient Xi(p,q,r).

**Theorem 1.9 (H pos).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H(p,q) is strictly positive at positive levels.

**Theorem 1.10 (Q pos).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every factor of Q is positive at positive levels, including collisions.

**Theorem 1.11 (rho closed).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical kappa(q/p) equals the literal two-variable rho rational formula, without a spectral gap denominator.

**Theorem 1.12 (rho nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pair coefficient is nonnegative at all positive levels.

**Theorem 1.13 (rho pos).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pair coefficient is strictly positive when its two positive levels differ.

**Theorem 1.14 (rho symm).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pair coefficient is symmetric in its two positive levels.

**Theorem 1.15 (rho self).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pair coefficient vanishes on a level collision.

**Theorem 1.16 (F symmetry).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_swap_last`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_swap_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar triangle numerator is unchanged when its last two levels are exchanged.

**Theorem 1.17 (F nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual triangle numerator is nonnegative for every positive triple. Its 118 positive ordered-chamber monomials and permutation symmetry establish the sign; this gives no sign to a complex source cycle.

**Theorem 1.18 (Xi nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual scalar coefficient Xi is nonnegative at every positive triple, with all collisions retained.

**Theorem 1.19 (Xi double).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_double`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a double collision Xi(p,p,q)=2rho(p,q). The factor two is preserved.

**Theorem 1.20 (Xi self).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At three equal levels Xi vanishes.

**Definition 1.21 (commonDen).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.commonDen`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.commonDen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common denominator 12Q^4 of the three pair weights and the cycle weight, positive at positive levels.

**Definition 1.22 (edgeScaled).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeScaled`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeScaled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair numerator multiplied by the fourth powers of the other two H factors.

**Definition 1.23 (cycleScaled).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycleScaled`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycleScaled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal scaled cycle numerator 27pqrQF.

**Definition 1.24 (p396).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cleared polynomial 4U1U2+396U3-U1H0^2, with Ui formed from the actual scaled pair numerators.

**Theorem 1.25 (edge scaled).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edge_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edge_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact binding of each scaled pair numerator to commonDen times the actual rho.

**Theorem 1.26 (cycle scaled).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycle_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycle_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact binding of the scaled cycle numerator to commonDen times the actual Xi.

**Theorem 1.27 (p396 scaled).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree-seventy-two polynomial is exactly commonDen^3 times the actual coefficient comparison margin. This normalization alone does not assert its sign.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_swap_last`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.H_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Q_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_double`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.Xi_self`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.closedCubic`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.commonDen`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycleScaled`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.cycle_scaled`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeNumerator`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edgeScaled`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.edge_scaled`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.p396_scaled`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_closed`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_self`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.rho_symm`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.symmetricF`
- Dependency: [D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate](HsfBalancedSpectralCertificate.md)
- Dependency: [D5/S3/Quantum/Matrix/PsdThreeCubicComplex](PsdThreeCubicComplex.md)
