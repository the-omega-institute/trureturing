# The actual ghost BRST Virasoro anomaly

## Abstract

Mixed Virasoro anomaly of the cubic ghost charge

The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.

**Theorem 1.1 (R covariance).**

$$\forall m \in Int,\; \forall r \in Int,\; \operatorname{L}\left(m\right) \cdot \operatorname{R}\left(r\right) - \operatorname{R}\left(r\right) \cdot \operatorname{L}\left(m\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(-2 \cdot m - r\right), \operatorname{R}\left(m + r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostAnomaly.R_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual c Ward identity acts on each pure-c pair. A bijective integer shift aligns both finite sums and their coefficients combine to minus two m minus r.

**Theorem 1.2 (Qg odd).**

$$\operatorname{parity} \cdot \operatorname{Qg} + \operatorname{Qg} \cdot \operatorname{parity} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostAnomaly.Qg_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual occupation parity anticommutes with each b and c mode. A product of three odd modes remains odd, and statewise finite supports justify passing parity through the cubic sum.

**Definition 1.3 (anomalyCoefficient).**

$$\forall r \in Int,\; \operatorname{anomalyCoefficient}\left(r\right) = \operatorname{div}\left(26, 12\right) \cdot \left(\operatorname{Int}.\operatorname{cast}\left(r\right)^{3} - \operatorname{Int}.\operatorname{cast}\left(r\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostAnomaly.anomalyCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This coefficient uses the ghost central charge minus twenty-six and the commutator direction.

**Theorem 1.4 (mixed anomaly).**

$$\forall r \in Int,\; \operatorname{Qg} \cdot \operatorname{L}\left(r\right) - \operatorname{L}\left(r\right) \cdot \operatorname{Qg} = \operatorname{smul}\left(\operatorname{div}\left(26, 12\right) \cdot \left(\operatorname{Int}.\operatorname{cast}\left(r\right)^{3} - \operatorname{Int}.\operatorname{cast}\left(r\right)\right), \operatorname{c}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostAnomaly.mixed_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Graded Jacobi, both cubic Ward identities, finite R covariance and the actual Virasoro theorem make the residual anticommute with all b and c. Multiplication by actual parity puts it in the scalar commutant; oddness forces it to vanish.

This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostAnomaly.Qg_odd`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostAnomaly.R_covariance`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostAnomaly.anomalyCoefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostAnomaly.mixed_anomaly`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRST](BcGhostBRST.md)
