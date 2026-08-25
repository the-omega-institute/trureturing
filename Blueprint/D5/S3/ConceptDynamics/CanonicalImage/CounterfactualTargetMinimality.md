# Counterfactual Target Minimality

## Abstract

Fiber-constant target families factor uniquely through the canonical query-profile image.

**Theorem 1.1 (Target families factor through the canonical profile image).**

$$\forall M, J, K: \operatorname{Type}, Value: J \to \operatorname{Type}, Target: K \to \operatorname{Type}, queries: \forall j, M \to \operatorname{Set}(\operatorname{Value}(j)), targets: \forall k, M \to \operatorname{Target}(k), {\forall k, m, n, \operatorname{queryProfile}(Value, queries, m) = \operatorname{queryProfile}(Value, queries, n) \Rightarrow \operatorname{targets}(k, m) = \operatorname{targets}(k, n)} \Rightarrow \forall k, \exists! factor: \operatorname{CounterfactualImage}(Value, queries) \to \operatorname{Target}(k), \operatorname{targets}(k) = factor \circ \operatorname{counterfactualProjection}(Value, queries).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CanonicalImage/CounterfactualTargetMinimality.target_family_factors_through_cf_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The query family sends each model to the set of possible values of each query, and queryProfile collects those answers into one canonical profile. CounterfactualImage is the realized image of this profile, with counterfactualProjection as its canonical map.

For every target index, constancy on profile fibers gives a target-valued factor on the image. Surjectivity of the canonical image map makes that factor unique, so all targets in the family descend through the same named image object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CanonicalImage/CounterfactualTargetMinimality.target_family_factors_through_cf_image`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
