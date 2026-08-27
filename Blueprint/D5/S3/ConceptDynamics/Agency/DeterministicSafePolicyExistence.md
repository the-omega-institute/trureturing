# Deterministic Safe Policy Existence

## Abstract

Fiberwise common legal actions characterize deterministic observation-based safe policies.

**Theorem 1.1 (A safe deterministic policy exists exactly when every effective fiber is safe).**

$$\forall X \in \operatorname{Type}, Q \in \operatorname{Type}, A \in \operatorname{Type}, q \in X \to Q, Legal \in X \to \left(A \to Prop\right),\; \left(\exists s \in \operatorname{range}\left(q\right) \to A,\; \forall z \in \operatorname{range}\left(q\right), x \in X,\; q\left(x\right) = \operatorname{val}\left(z\right) \Rightarrow Legal\left(x, s\left(z\right)\right)\right) \Leftrightarrow \left(\forall z \in \operatorname{range}\left(q\right),\; \exists a \in A,\; \forall x \in X,\; q\left(x\right) = \operatorname{val}\left(z\right) \Rightarrow Legal\left(x, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence.deterministic_safe_policy_exists_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The policy is defined on the realized observation range. Safety requires its chosen action to be legal at every full state compatible with that observation.

Such a policy supplies a common legal action in each effective fiber. Conversely, set-theoretic choice assembles one common action from every effective fiber; no measurable-selector claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence.deterministic_safe_policy_exists_iff`
