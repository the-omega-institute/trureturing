# A Permanent Dark Effect Need Not Be a Projection

## Abstract

A permanent no-click effect can retain fractional weight outside its certain dark directions.

**Theorem 1.1 (A two-dimensional non-projective dark effect).**

$$\forall a \in \mathbb{R},\; (0 < a) \Rightarrow ((a < 1) \Rightarrow (\exists Q \in (\operatorname{Fin}(2)) \to \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\; \exists L \in (\operatorname{Fin}(1)) \to \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\; \exists F \in \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\; (Q(0) = \operatorname{basisProjector}(0)) \land \left((Q(1) = \operatorname{single}(0, 1, \operatorname{sqrt}(a))) \land \left((L(0) = \operatorname{sqrt}((1 - a)) \cdot \operatorname{basisProjector}(1)) \land \left((\sum_{i \in \operatorname{Fin}(2)} {Q(i)}^{*} \cdot Q(i) + \sum_{i \in \operatorname{Fin}(1)} {L(i)}^{*} \cdot L(i) = 1) \land \left((\forall X \in \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\; \operatorname{noClickDual}(Q, X) = X_{00} \cdot F) \land \left((\forall N \in \operatorname{Nat},\; (1 \le N) \Rightarrow (\operatorname{survival}(Q, N) = F)) \land \left((\operatorname{Tendsto}(\operatorname{survival}(Q), atTop, \operatorname{nhds}(F))) \land \left((F = \operatorname{basisProjector}(0) + a \cdot \operatorname{basisProjector}(1)) \land \left((F \cdot F \ne F) \land \left((\forall v \in (\operatorname{Fin}(2)) \to \mathbb{C},\; (\operatorname{dotProduct}(\operatorname{star}(v), v) = 1) \Rightarrow ((\operatorname{dotProduct}(\operatorname{star}(v), \operatorname{mulVec}(F, v)) = 1) \Leftrightarrow (v(1) = 0))) \land \left((\operatorname{trace}(\operatorname{basisProjector}(1) \cdot F) = a) \land \left((\operatorname{trace}(\operatorname{basisProjector}(1) \cdot {L(0)}^{*} \cdot L(0)) = (1 - a)) \land (\operatorname{trace}(\operatorname{basisProjector}(1) \cdot \operatorname{basisProjector}(0)) = 0)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/NonProjectiveDarkEffect.non_projective_dark_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real a strictly between zero and one, two no-click Kraus operators and one click Kraus operator satisfy the completeness equation. The dual no-click map depends only on the upper-left entry and the survival effect is constant after the first step.

The limiting effect has diagonal entries one and a, so it is not idempotent. A unit vector has expectation one exactly when its second coordinate vanishes.

The second basis state has permanent no-click probability a even though its weight on the certain dark direction is zero.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/NonProjectiveDarkEffect.non_projective_dark_effect`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit](GeneralInstrumentSurvivalLimit.md)
