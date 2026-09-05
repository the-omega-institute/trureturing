# Finite Resolvent--Clark Identity

## Abstract

A finite paired real spectrum becomes its exact resolvent-weighted atomic circle measure under Cayley compactification.

**Definition 1.1 (Paired ordinate measure).**

$$\forall J \in Type, m \in J \to ENNReal, gamma \in J \to \operatorname{Real}\left(\right),\; \operatorname{Fintype}\left(J\right) \Rightarrow \operatorname{pairedOrdinateMeasure}\left(m, gamma\right) = \operatorname{sum}\left(j, J, m\left(j\right) \cdot \left(\operatorname{dirac}\left(gamma\left(j\right)\right) + \operatorname{dirac}\left(-gamma\left(j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/FiniteResolventClarkIdentity.pairedOrdinateMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each finite index contributes equally weighted Dirac atoms at its positive and negative real ordinates. The measure sum retains multiplicity when ordinates coincide.

**Definition 1.2 (Finite atomic circle measure).**

$$\forall J \in Type, a \in \operatorname{Real}\left(\right), m \in J \to ENNReal, gamma \in J \to \operatorname{Real}\left(\right),\; \left(\operatorname{Fintype}\left(J\right) \land 0 < a\right) \Rightarrow \operatorname{finiteAtomicClarkMeasure}\left(a, m, gamma\right) = \operatorname{sum}\left(j, J, m\left(j\right) \cdot \operatorname{resolventDensity}\left(a, gamma\left(j\right)\right) \cdot \left(\operatorname{dirac}\left(\operatorname{cayleyCircle}\left(a, gamma\left(j\right)\right)\right) + \operatorname{dirac}\left(\operatorname{cayleyCircle}\left(a, -gamma\left(j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/FiniteResolventClarkIdentity.finiteAtomicClarkMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every paired atom is moved by the canonical Cayley map and its mass is multiplied by the exact reciprocal-quadratic resolvent density. Evenness of that density gives both signs the same coefficient.

**Theorem 1.3 (Finite atomic Cayley pushforward).**

$$\forall J \in Type, a \in \operatorname{Real}\left(\right), m \in J \to ENNReal, gamma \in J \to \operatorname{Real}\left(\right),\; \left(\operatorname{Fintype}\left(J\right) \land 0 < a\right) \Rightarrow \operatorname{cayleyCompactification}\left(a, \operatorname{pairedOrdinateMeasure}\left(m, gamma\right)\right) = \operatorname{finiteAtomicClarkMeasure}\left(a, m, gamma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/FiniteResolventClarkIdentity.finite_atomic_cayley_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib distributes withDensity and Measure.map across the finite measure sum, scalar multiplication, and each paired sum.

The Dirac with-density and map laws then evaluate every summand. This is the nontrivial finite atomic calculation on which the final identity rests.

**Theorem 1.4 (Half-scale resolvent--Clark identity).**

$$\forall J \in Type, m \in J \to ENNReal, gamma \in J \to \operatorname{Real}\left(\right), sigma \in \operatorname{Measure}\left(Circle\right),\; \operatorname{Fintype}\left(J\right) \Rightarrow \left(sigma = \operatorname{finiteAtomicClarkMeasure}\left(\frac{1}{2}, m, gamma\right) \Rightarrow \left(\operatorname{cayleyCompactification}\left(\frac{1}{2}, \operatorname{pairedOrdinateMeasure}\left(m, gamma\right)\right) = \operatorname{finiteAtomicClarkMeasure}\left(\frac{1}{2}, m, gamma\right) \land \operatorname{finiteAtomicClarkMeasure}\left(\frac{1}{2}, m, gamma\right) = sigma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/FiniteResolventClarkIdentity.finite_resolvent_clark_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At scale one half, the compactification is the explicit finite atomic Li measure by the preceding pushforward theorem.

The supplied Clark measure is required to have that same atomic expansion. This premise records the analytic Clark/Herglotz identification that is not available in the repository, so the theorem does not overclaim an unconditional equality.

## References

- Truth anchor: `D5/S3/Weil/FiniteResolventClarkIdentity.finiteAtomicClarkMeasure`
- Truth anchor: `D5/S3/Weil/FiniteResolventClarkIdentity.finite_atomic_cayley_pushforward`
- Truth anchor: `D5/S3/Weil/FiniteResolventClarkIdentity.finite_resolvent_clark_identity`
- Truth anchor: `D5/S3/Weil/FiniteResolventClarkIdentity.pairedOrdinateMeasure`
- Dependency: [D5/S3/Weil/TestFunctions/CayleyMomentTransport](TestFunctions/CayleyMomentTransport.md)
