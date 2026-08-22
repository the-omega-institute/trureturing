# Universal Sufficiency Factorization

## Abstract

Universal sufficiency is equivalently target factorization or constancy on fibers.

**Lemma 1.1 (The target factor agrees on represented coordinates).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}Nonempty(X), q_{C}: X \to B, T: X \to Y,\\{}h: \forall x, y: X, q_{C}(x) = q_{C}(y) \Rightarrow T(x) = T(y),\\{}\forall x: X, targetFactor(q_{C}, T, h)(q_{C}(x)) = canonicalTargetReadout(T)(x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.targetFactor_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the target is constant whenever two states have the same concept coordinate. The resulting map from concept coordinates to the target image sends every represented coordinate q_C(x) to the canonical target point determined by x.

Coordinates outside the range of q_C are filled using an arbitrary state, which exists because the state space is nonempty. This choice cannot affect the represented coordinates covered by the lemma.

**Theorem 1.2 (Universal sufficiency has three equivalent forms).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}Nonempty(X), q_{C}: X \to B, T: X \to Y,\\{}(Refines(canonicalTargetReadout(T), q_{C}) \Leftrightarrow \exists f: B \to TargetImage(T), canonicalTargetReadout(T) = f \circ q_{C}) \land\\{}(\exists f: B \to TargetImage(T), canonicalTargetReadout(T) = f \circ q_{C} \Leftrightarrow \forall x, y: X, q_{C}(x) = q_{C}(y) \Rightarrow T(x) = T(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.universal_sufficiency_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept readout is sufficient for a target exactly when the canonical target-image readout factors through it. The same factorization exists exactly when the target is constant on each fiber of the concept readout.

Fiber constancy makes the factor map well-defined on represented coordinates. Nonemptiness of the state space supplies a target image value for any concept coordinates that no state represents; the auxiliary lemma proves agreement on all represented ones.

The repository proof reuses the pinned library's factor-through criterion and extension operation. Repository searches found adjacent factorization results but no existing declaration that combines this canonical target-image refinement with the fiber criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.targetFactor_apply`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.universal_sufficiency_factorization`
