# Diagonal Global Balance

## Abstract

A single shared orientation bit centers every orbit while preserving maximal pairwise direction correlation.

**Definition 1.1 (The global diagonal reflection law).**

$$\forall T \in \operatorname{Type},\; \operatorname{Fintype}\left(T\right) \Rightarrow \operatorname{diagonalLaw}\left(T\right) = \operatorname{toMeasure}\left(\operatorname{map}\left(\operatorname{uniformOfFintype}\left(\operatorname{Fin}\left(2\right)\right), (bit: \operatorname{Fin}\left(2\right) \mapsto (index: T \mapsto bit))\right)\right).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonalLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform binary orientation bit is sent to the corresponding constant configuration. Its pushforward is exactly the half-half law on the all-negative and all-positive configurations of the finite window.

**Lemma 1.2 (The diagonal law is a probability measure).**

$$\forall T \in \operatorname{Type},\; \operatorname{Fintype}\left(T\right) \Rightarrow \operatorname{IsProbabilityMeasure}\left(\operatorname{diagonalLaw}\left(T\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonalLaw_isProbabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the uniform probability mass function on the two orientation bits preserves total mass one.

**Definition 1.3 (Signed displacement at one orbit).**

$$\forall T \in \operatorname{Type}, delta \in T \to \mathbb{R}, orbit \in T, configuration \in T \to \operatorname{Fin}\left(2\right),\; \operatorname{orbitReadout}\left(delta, orbit, configuration\right) = \operatorname{real}\left(\operatorname{paritySign}\left(configuration\left(orbit\right)\right)\right) \cdot delta\left(orbit\right).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.orbitReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout multiplies the binary coordinate sign by the real displacement attached to the selected orbit.

**Lemma 1.4 (Joint second moment under the shared bit).**

$$\forall T \in \operatorname{Type}, delta \in T \to \mathbb{R}, orbit \in T, orbitPrime \in T,\; \operatorname{Fintype}\left(T\right) \Rightarrow \operatorname{integral}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbit, configuration\right) \cdot \operatorname{orbitReadout}\left(delta, orbitPrime, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right) = delta\left(orbit\right) \cdot delta\left(orbitPrime\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonal_joint_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both readouts see the same orientation bit, whose square is one. The exact joint second moment is therefore the product of the two displacements.

**Theorem 1.5 (Local balance and global maximal correlation).**

$$\forall T \in \operatorname{Type}, delta \in T \to \mathbb{R},\; \operatorname{Fintype}\left(T\right) \Rightarrow \left(\left(\forall orbit \in T,\; \operatorname{integral}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbit, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right) = 0\right) \land \left(\forall orbit \in T, orbitPrime \in T,\; orbit \ne orbitPrime \Rightarrow \left(\operatorname{covariance}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbit, configuration\right)), (configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbitPrime, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right) = delta\left(orbit\right) \cdot delta\left(orbitPrime\right) \land \left(\operatorname{covariance}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbit, configuration\right)), (configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbitPrime, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right)^{2} = \operatorname{variance}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbit, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right) \cdot \operatorname{variance}\left((configuration: T \to \operatorname{Fin}\left(2\right) \mapsto \operatorname{orbitReadout}\left(delta, orbitPrime, configuration\right)), \operatorname{diagonalLaw}\left(T\right)\right) \land \left(delta\left(orbit\right) \cdot delta\left(orbitPrime\right) \ne 0 \Rightarrow \left(\neg \operatorname{iIndepFun}\left((index: T \mapsto (configuration: T \to \operatorname{Fin}\left(2\right) \mapsto configuration\left(index\right))), \operatorname{diagonalLaw}\left(T\right)\right)\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonal_global_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite orbit type and every real displacement family, each orbit readout has expectation zero under the diagonal law. Distinct orbit readouts have covariance equal to the product of their displacements.

The squared covariance equals the product of the two variances, which records saturation of the covariance-variance bound and hence maximal absolute direction correlation.

If the displacement product of a distinct pair is nonzero, the coordinate projections cannot be jointly independent. Hypothetical coordinate independence would pass through the signed-displacement maps and force their nonzero covariance to vanish.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonalLaw`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonalLaw_isProbabilityMeasure`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonal_global_balance`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.diagonal_joint_second_moment`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.orbitReadout`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments](ParityConditionedMoments.md)
