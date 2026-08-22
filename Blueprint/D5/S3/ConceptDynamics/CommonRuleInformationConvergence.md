# Common-Rule Information Convergence

## Abstract

Correct common facts align a shared rule, while distinct rules can still disagree.

**Theorem 1.1 (Common facts align shared rules but not distinct rules).**

$$\forall X, Z, U: \operatorname{Type}, T: X \to Z, d, d_{i}, d_{j}: Z \to U,\ (\forall x: X, z_{i}, z_{j}: Z, (z_{i} = T(x) \land z_{j} = T(x)) \Rightarrow d(z_{i}) = d(z_{j})) \land\ (\forall x: X, z: Z, (T(x) = z \land d_{i}(z) \neq d_{j}(z)) \Rightarrow d_{i}(T(x)) \neq d_{j}(T(x))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CommonRuleInformationConvergence.common_rule_information_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is the canonical concept readout from source states to fully disclosed fact values. Two fact values are sufficient here when each is equal to that target value.

The first public conjunct applies one deterministic rule to two correct fact values. The second public conjunct applies distinct rules at a disclosed target value and preserves their disagreement.

Repository searches found no theorem containing both clauses. The existing disclosure-defect result instead concerns collisions and consequence recovery. The proof directly applies equality transport.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CommonRuleInformationConvergence.common_rule_information_convergence`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](ConceptFiberDecomposition.md)
