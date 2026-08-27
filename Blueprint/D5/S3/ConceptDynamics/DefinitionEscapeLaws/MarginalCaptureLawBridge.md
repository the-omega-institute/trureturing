# Finite-Additive Marginal Capture Bridge

## Abstract

Finite additive escape mass discharges the canonical marginal capture law.

**Theorem 1.1 (Marginal capture decreases as the finite definition set grows).**

$$\forall I, X, C, Target: Type,\ V: I \to Type,\ definitions: \forall i: I, \operatorname{Concept}\left(X, \operatorname{apply}\left(V, i\right)\right),\ q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Target\right),\ c: I \to Real, nu: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\ Gamma, Delta: \operatorname{Set}\left(I\right), d: I,\ \left(\operatorname{nonnegativeCost}\left(c\right) \land \left(\operatorname{disjointAdditive}\left(nu\right) \land \left(\operatorname{finite}\left(Delta\right) \land \left(\operatorname{subset}\left(Gamma, Delta\right) \land \operatorname{notMember}\left(d, Delta\right)\right)\right)\right)\right) \Rightarrow \operatorname{present}\left(diminishingMarginalCapture\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/MarginalCaptureLawBridge.marginal_capture_law_of_finite_additive_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula retains every Lean premise. nonnegativeCost states that zero is below every candidate cost. disjointAdditive states that nu.mass(left union right) equals nu.mass(left) plus nu.mass(right) when left and right are disjoint. Delta is finite, Gamma is a subset of Delta, and the added definition is not in Delta. There is no Finite X, Nonempty, DecidableEq, measurability, monotonicity, or shared-codomain premise.

The Lean conclusion is the imported marginalCaptureLaw without any change to its statement. It expands to F(Gamma union singleton d) minus F(Gamma) greater than or equal to F(Delta union singleton d) minus F(Delta), where F is the imported capturedEscapeMass and therefore still means M(empty) minus M(S). The candidate family keeps the dependent codomain V(i), and defectRelation remains the only target residual.

The proof is exactly the sixth projection of submodular_capture. The finite-Delta and nonnegative-cost assumptions are retained source-domain conditions, not advertised as local proof guards. Finite additivity is the proof guard that connects the weak EscapeWeight interface to the source weighted-cover reading.

Boundary: this bridge proves the law only under the displayed finite-additivity premise. Downstream users must not cite it as proving diminishing marginal capture from the weak EscapeWeight interface alone. FiniteCoverCounting.lean:380 contains the canonical weak-interface countermodel.

The named Boolean positive witness supplies a nonempty finite model with strictly decreasing marginal capture. The imported clause-six false neighbor changes only the inequality to a strict inequality in the opposite direction under unchanged premises. The nonvacuity theorem consumes the local positive witness and that existing complete false-neighbor statement directly.

Named scope limit MARGINAL_CAPTURE_BRIDGE_DOES_NOT_REPACKAGE_MONOTONICITY_OR_FOUR_TERM_SUBMODULARITY: DECT source line 550 also states monotonicity and four-term submodularity. This bridge covers only the diminishing-return clause at source lines 550-558 because that is the missing FiniteCoverCounting clause. The omitted source claims are already closed by submodular_capture conjuncts four and five; this is a named scope boundary, not an open mathematical gap.

scribe_lean_correspondence: the single displayed item present(diminishingMarginalCapture) maps to the sole Lean conclusion, marginalCaptureLaw. Every Lean premise appears in the displayed antecedent. The mapping is weaker because present omits the expanded inequality and the definitions of M and F. Equal mappings: zero. Stronger mappings: zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/MarginalCaptureLawBridge.marginal_capture_law_of_finite_additive_mass`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses](SubmodularCaptureWitnesses.md)
