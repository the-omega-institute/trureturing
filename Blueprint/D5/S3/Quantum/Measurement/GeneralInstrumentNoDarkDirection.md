# No Definite Dark Direction for General Instruments

## Abstract

A general no-click instrument has no definite dark direction exactly when its limit effect vanishes, exactly when the survival defect after d steps is positive definite, and exactly when Tr(rho F) = 0 for every density matrix rho.

**Theorem 1.1 (Four equivalent forms of the absence of dark directions).**

$${\sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \land S_{N} \to F} \Rightarrow\\{}D_{d} = 0 \iff F = 0 \iff I-S_{d} > 0 \iff\\{}\forall \rho \geq 0 \text{ with }\operatorname{Tr} \rho = 1, \operatorname{Tr}(\rho F) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection.no_dark_direction_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the d-dimensional space with the completeness relation, let S_N be the survival effects, D_d the stable dark layer and F the limit of S_N. The four conditions are: D_d is zero; F is zero; I - S_d is positive definite; Tr(rho F) = 0 for every density matrix rho.

Every vector of D_d satisfies S_N v = v from step d on, so F v = v; hence F = 0 forces D_d = 0. Conversely, if F is not zero, the Rayleigh quotient of F attains a largest value lambda > 0 on the unit sphere, so lambda I - F is positive semidefinite. On its kernel M, which contains the maximizer, the fixed-point equation gives <v, F v> = sum over a of <Q_a v, F Q_a v>, which is at most lambda times the sum of |Q_a v|^2, that is lambda (|v|^2 - sum of |L_i v|^2). Equality forces every L_i v to vanish and every Q_a v to lie in M, so M is a nonzero subspace annihilated by the click operators and invariant under the no-click operators, and it lies in D_d.

Since D_d is the kernel of the positive semidefinite operator I - S_d, it is zero exactly when I - S_d is positive definite. Testing F against the rank-one densities v v^* / |v|^2 shows that Tr(rho F) = 0 for all densities exactly when F = 0.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection.no_dark_direction_tfae`
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit](GeneralInstrumentSurvivalLimit.md)
