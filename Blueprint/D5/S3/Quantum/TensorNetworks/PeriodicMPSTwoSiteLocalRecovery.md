# Local two-site recovery on the periodic chart

## Abstract

Local recovery from the normalized periodic two-site marginal

**Definition 1.1 (Squared amplitude mass).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.twoMass`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.twoMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace of the actual two-site Gram matrix sums the squared moduli of the periodic amplitudes. Its real part is the total mass.

**Definition 1.2 (Normalized two-site marginal).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.normalizedTwo`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.normalizedTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At positive mass, divide the Gram matrix of the two-site amplitude flattening by its trace. This gives the marginal of the unit-norm periodic state.

**Theorem 1.3 (A local decoder at each periodic length).**

$$\forall r \in Nat,\; \exists a \in Complex,\; \exists x \in Fin\left(4\right) \to Complex,\; \exists U \in Set\left(Fin\left(4\right) \to Complex\right),\; \exists decode \in Matrix\left(Prod\left(Fin\left(2\right), Fin\left(2\right)\right), Prod\left(Fin\left(2\right), Fin\left(2\right)\right), Complex\right) \to \left(Fin\left(4\right) \to Complex\right),\; \exists L \in Real,\; ((((((IsOpen\left(U\right)) \land (x \in U)) \land (\forall y \in Fin\left(4\right) \to Complex,\; (y \in U) \Rightarrow (0 < twoMass\left(chart\left(a, y\right), r\right)))) \land (InjOn\left((\lambda (y: Fin\left(4\right) \to Complex) \mapsto normalizedTwo\left(chart\left(a, y\right), r\right)), U\right))) \land (\forall y \in Fin\left(4\right) \to Complex,\; (y \in U) \Rightarrow (decode\left(normalizedTwo\left(chart\left(a, y\right), r\right)\right) = y))) \land (0 \leq L)) \land (\forall y \in Fin\left(4\right) \to Complex,\; (y \in U) \Rightarrow (\forall z \in Fin\left(4\right) \to Complex,\; (z \in U) \Rightarrow (norm\left(y - z\right) \leq L \cdot norm\left(normalizedTwo\left(chart\left(a, y\right), r\right) - normalizedTwo\left(chart\left(a, z\right), r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.normalized_local_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every ring length r+4 there is a fixed entry a and a nonempty open set of the four remaining complex chart coordinates. The periodic states have positive mass throughout this set, and the actual normalized two-site marginal is injective there. One decoder returns all four chart coordinates with a Lipschitz bound in the entrywise sup norm.

Differentiating the identity that recovers the raw marginal from the mass and the normalized marginal makes every normalized kernel direction radial in the raw marginal. The nonsingular minor includes the raw value column and therefore forces that direction to vanish. A real linear left inverse of the normalized differential gives a fixed projection. The inverse function theorem on the projected observation gives the decoder. On a smaller neighborhood, the projected observation differs from the identity to first order with a uniform two-point error at most half the source distance. This gives the stated bound.

The neighborhood is relative to the fixed chart. Phase classes represented elsewhere in the periodic state space are outside the uniqueness claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.normalizedTwo`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.normalized_local_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery.twoMass`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential](PeriodicMPSTwoSiteDifferential.md)
