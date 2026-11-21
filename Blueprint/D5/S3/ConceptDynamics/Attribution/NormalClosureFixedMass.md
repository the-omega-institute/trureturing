# The normal closure determines full fixed mass

## Abstract

A criterion for full subgroup-fixed mass in finite equivariant calibrations.

**Theorem 1.1 (Full subgroup-fixed seed mass is equivalent to row support for the normal closure).**

$$\forall G, X, Y, H:\operatorname{Subgroup}\left(G\right), P:X \times Y \to \mathbb{R}, \operatorname{CovariantProbabilityKernel}\left(P\right) \Rightarrow ((\exists S:\operatorname{FiniteSeedType}\left(\operatorname{MaxUniverse}\left(v, w\right)\right), a:S \to \mathbb{R}, f:X \times S \to Y, \operatorname{PositiveCalibration}\left(G, P, S, a, f\right) \land \operatorname{FixedMass}\left(H, a\right)=1) \iff (\forall x:X, y:Y, 0<\operatorname{P}\left(x, y\right) \Rightarrow \forall n:\operatorname{NormalClosure}\left(H\right), n \cdot x=x \Rightarrow n \cdot y=y))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/NormalClosureFixedMass.full_subgroup_fixed_seed_mass_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a nonempty finite input type X in universe v and on a finite output type Y in universe w with decidable equality. A probability kernel P has nonnegative entries, normalized rows and is covariant under G. Let H be a subgroup of G and let N be the normal closure of H in G.

The seed type belongs to the maximum of the input and output universes. PositiveCalibration requires a G-action on that type, strictly positive normalized G-invariant weights, and a pointwise G-covariant deterministic readout realizing each entry of P as the total weight of seeds with the indicated output. FixedMass is the total weight of seeds fixed by every element of the subgroup.

When the H-fixed event has full weight, positivity forces each seed to be fixed by H. The kernel of the seed action is normal and contains H, so it contains N as well. Covariance then forces the stated row support. Conversely, the row support gives mass one in every row for the N stabilizer criterion. The normal-subgroup maximum supplies a calibration with full N-fixed mass, which also has full H-fixed mass.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/NormalClosureFixedMass.full_subgroup_fixed_seed_mass_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass](NormalSubgroupFixedMass.md)
