# Submodular Definition-Escape Capture

## Abstract

Finite selections with nonnegative costs and additive escape mass satisfy the DECT capture laws.

**Theorem 1.1 (Capture is monotone, submodular, and has diminishing marginal returns).**

$$\forall I, X, C, Target: Type,\ V: I \to Type,\ definitions: \forall i: I, \operatorname{Concept}\left(X, \operatorname{apply}\left(V, i\right)\right),\ q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Target\right),\ c: I \to Real, nu: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\ \left(\operatorname{finiteSelectionArguments}\left(I\right) \land \operatorname{nonnegativeCost}\left(c\right)\right) \land \operatorname{disjointAdditive}\left(nu\right) \Rightarrow \operatorname{present}\left(C1\right) \land \operatorname{present}\left(C2\right) \land \operatorname{present}\left(C3\right) \land \operatorname{present}\left(C4\right) \land \operatorname{present}\left(C5\right) \land \operatorname{present}\left(C6\right) \land \operatorname{present}\left(C7\right) \land \operatorname{present}\left(C8\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed implication preserves all source ambient conditions. Each selection variable is accompanied by Set.Finite, nonnegativeCost means zero is below every c(gamma), and disjointAdditive means exactly that mass(left union right) equals mass(left) plus mass(right) whenever left and right are disjoint. It does not assume that the whole candidate language is finite, strictly positive cost, positive baseline mass, countable additivity, measurability, inhabitedness, or decidable equality.

The candidate family has the dependent Lean type definitions : forall i : I, Concept X (V i). Thus the formula does not replace the source family by a shared codomain. M is the imported residualEscapeMass and F is the imported capturedEscapeMass, whose definition is M(empty) minus M(S). The canonical defectRelation is the only target residual.

C1 through C8 map in order to the eight Lean conjuncts: the exact M formula on finite selections; the exact two-step F definition; the captured-union expansion; monotonicity; four-term submodularity; diminishing returns under A subset B and d not in B; equivalence of the two greedy score formulations; and persistence of a pair lying in the baseline defect while every candidate readout identifies it. The present labels are weaker summaries, not extra predicates.

The proof reuses capture_weight_submodular for the coverage step and uses finite additivity to identify M(empty) minus M(S) with the mass of the captured union. Nondegeneracy is supplied separately by a named positive model, so the theorem itself still admits the constant-zero weight required by the source's full domain.

GREEDY_ARGMAX_RULE_UNRESOLVED: C7 proves equality of the residual and capture score predicates. The source gives no candidate-domain, argmax-existence, tie, zero-cost, or freshness convention, so this module does not strengthen that algebraic identity into an existence claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture`
- Dependency: [D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture](../DefinitionCapture/MeasureCapture.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](../DefinitionEscape/FiniteCoverCounting.md)
