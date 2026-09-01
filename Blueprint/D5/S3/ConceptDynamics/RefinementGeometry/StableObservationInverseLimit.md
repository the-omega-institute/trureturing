# Stable Observation Inverse Limit

## Abstract

Expanding operation languages canonically form an inverse system of observational quotients.

**Theorem 1.1 (Stable observations form a functorial inverse-limit system).**

$$\forall A \in Type, X \in Type, Y \in Type, mathcalA \in \mathbb{N} \to \operatorname{Set}\left(A\right), O \in A \to \left(X \to Y\right),\; \operatorname{Increasing}\left(mathcalA\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \operatorname{operationSetoid}\left(mathcalA, O, n+1\right) \subseteq \operatorname{operationSetoid}\left(mathcalA, O, n\right)\right) \land \left(\left(\forall n \in \mathbb{N}, x \in X,\; \operatorname{r}\left(n+1, n\right)(\operatorname{class}\left(x, n+1\right)) = \operatorname{class}\left(x, n\right)\right) \land \left(\left(\forall n \in \mathbb{N}, x \in X, y \in X,\; \operatorname{EquivalentAt}\left(mathcalA, O, n+1, x, y\right) \Rightarrow \operatorname{r}\left(n+1, n\right)(\operatorname{class}\left(x, n+1\right)) = \operatorname{r}\left(n+1, n\right)(\operatorname{class}\left(y, n+1\right))\right) \land \left(\left(\left(\forall n \in \mathbb{N},\; \operatorname{r}\left(n, n\right) = id\right) \land \left(\forall i \in \mathbb{N}, j \in \mathbb{N}, k \in \mathbb{N},\; \left(i \le j \land j \le k\right) \Rightarrow \operatorname{r}\left(k, i\right) = \operatorname{r}\left(j, i\right) \circ \operatorname{r}\left(k, j\right)\right)\right) \land \left(\forall s \in \operatorname{StableObservationSpace}\left(mathcalA, O\right), n \in \mathbb{N},\; \operatorname{r}\left(n+1, n\right)(s_{n+1}) = s_{n}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.stable_observation_inverse_limit_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level n, two states are equivalent when every operation admitted at that level has the same readout on them. Inclusion of each operation family in its successor therefore makes the equivalence relations decrease.

The relation inclusion induces the canonical map from the finer quotient to the coarser quotient. It preserves representatives, is independent of their choice, and its maps obey identity and composition along the level order.

The stable observation space is the type of compatible threads in this quotient tower, reusing the repository's abstract inverse-thread construction.

**Theorem 1.2 (The observational equivalence tower can decrease strictly).**

$$\operatorname{StrictSubset}\left(\operatorname{operationSetoid}\left(strictOperationFamily, strictObservation, 1\right), \operatorname{operationSetoid}\left(strictOperationFamily, strictObservation, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.strict_observation_refinement_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Boolean states and one operation, level zero admits no operation and level one admits the identity observation. Thus false and true are equivalent at level zero but separated at level one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.stable_observation_inverse_limit_laws`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.strict_observation_refinement_witness`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity](../RefinementFactorization/InterventionFamilyKernelMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion](InverseLimitCompletion.md)
