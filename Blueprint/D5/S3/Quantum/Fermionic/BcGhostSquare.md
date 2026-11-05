# The all-integer ghost BRST square

## Abstract

Full ghost BRST square anomaly

The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.

**Definition 1.1 (squareTerm).**

$$\forall n \in Int,\; \operatorname{squareTerm}\left(n\right) = \operatorname{smul}\left(\operatorname{div}\left(-26, 24\right) \cdot \left(\operatorname{Int}.\operatorname{cast}\left(n\right)^{3} - \operatorname{Int}.\operatorname{cast}\left(n\right)\right), \operatorname{c}\left(-n\right) \cdot \operatorname{c}\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostSquare.squareTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is minus twenty-six over twenty-four; summation includes both signed indices.

**Theorem 1.2 (squareTerm finite).**

$$\forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((n\mapsto\operatorname{squareTerm}\left(n, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostSquare.squareTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure-c support theorem at total index zero, reindexed by negation, proves statewise local finiteness.

**Definition 1.3 (squareAnomaly).**

$$\forall v \in Fock,\; \operatorname{squareAnomaly}\left(v\right) = \sum_{n\in Int}^{fin}\operatorname{squareTerm}\left(n, v\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostSquare.squareAnomaly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the full statewise finite anomaly endomorphism.

**Theorem 1.4 (square anomaly).**

$$\operatorname{Qg} \cdot \operatorname{Qg} = \operatorname{squareAnomaly}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostSquare.square_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd charge, the commutator of its square with b is the commutator of Q with its b anticommutator, without an extra factor one half. Mixed anomaly and finite triple-c cancellation identify both b and c commutators with those of the full pure-c anomaly. The difference is scalar by the original Fock commutant theorem. Both operators kill the ghost vacuum, so that scalar is zero. This argument is confined to the ghost sector.

This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostSquare.squareAnomaly`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostSquare.squareTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostSquare.squareTerm_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostSquare.square_anomaly`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostAnomaly](BcGhostAnomaly.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostJacobi](BcGhostJacobi.md)
