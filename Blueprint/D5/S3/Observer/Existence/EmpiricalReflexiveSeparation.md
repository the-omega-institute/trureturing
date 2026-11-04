# Empirical and Reflexive Completeness Separate

## Abstract

A complete quantum-state readout does not make internal self-evaluation exhaustive.

**Theorem 1.1 (The embedded square root of two).**

$$(Real.sqrt\left(2\right): Complex)^{2} = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.complex_sqrt_two_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real square root of two, embedded in Complex, has square two. This identity normalizes the rank-one qubit projectors.

**Theorem 1.2 (Normalized rank-one densities are projections).**

$$\forall v \in \operatorname{Fin}\left(2\right) \to Complex,\; \operatorname{dotProduct}\left(\operatorname{star}\left(v\right), v\right) = 1 \Rightarrow \operatorname{IsNormalizedRankOneProjection}\left(\operatorname{rankOneDensity}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.rankOneDensity_isNormalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density matrix of a unit vector is a normalized rank-one projection.

**Theorem 1.3 (Empirical completeness coexists with reflexive incompleteness).**

$$\exists context \in \operatorname{Fin}\left(3\right) \to \operatorname{RankOneContext}\left(2\right),\; \operatorname{Injective}\left((rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right) \mapsto \operatorname{contextReadout}\left(context, \operatorname{matrix}\left(rho\right)\right))\right) \land \left(\forall evaluation \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right) \to \left(\operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right) \to Bool\right),\; \neg (state \mapsto \operatorname{not}\left(\operatorname{evaluation}\left(state, state\right)\right)) \in \operatorname{range}\left(evaluation\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.empirical_complete_reflexive_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a three-context rank-one qubit observer whose projector-trace readout is injective on the canonical carrier of positive, trace-one qubit density states. This is the public current-state reconstruction clause.

For every Boolean evaluation table indexed twice by that same density-state carrier, the function obtained by negating the table on its diagonal is outside the table's range. This is exactly the public internal self-evaluation non-capture clause.

The concrete witness uses the three standard mutually unbiased qubit bases. The proof then applies the repository's complete-context tomography and fixed-point-free Lawvere escape theorems.

## References

- Truth anchor: `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.complex_sqrt_two_sq`
- Truth anchor: `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.empirical_complete_reflexive_incomplete`
- Truth anchor: `D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.rankOneDensity_isNormalized`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../../Quantum/Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../Quantum/PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/Tomography/ObserverDiagonalSeparation](../../Quantum/Tomography/ObserverDiagonalSeparation.md)
