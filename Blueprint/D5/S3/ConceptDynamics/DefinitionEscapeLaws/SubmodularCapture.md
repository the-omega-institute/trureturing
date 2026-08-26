# Submodular Definition-Escape Capture

## Abstract

A positive finitely additive escape mass makes DECT capture a submodular coverage law.

**Theorem 1.1 (Capture is monotone, submodular, and has diminishing marginal returns).**

$$\forall I, X, C, Target: Type,\ V: I \to Type,\ definitions: \forall i: I, \operatorname{Concept}\left(X, \operatorname{apply}\left(V, i\right)\right),\ q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Target\right),\ c: I \to Real, nu: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\ 0 < \operatorname{mass}\left(nu, \operatorname{defectRelation}\left(q, T\right)\right) \land \operatorname{disjointAdditive}\left(nu\right) \Rightarrow \operatorname{present}\left(C1\right) \land \operatorname{present}\left(C2\right) \land \operatorname{present}\left(C3\right) \land \operatorname{present}\left(C4\right) \land \operatorname{present}\left(C5\right) \land \operatorname{present}\left(C6\right) \land \operatorname{present}\left(C7\right) \land \operatorname{present}\left(C8\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed implication preserves both Lean premises. Positive means zero is strictly below nu.mass(defectRelation(q,T)); disjointAdditive means exactly that mass(left union right) equals mass(left) plus mass(right) whenever left and right are disjoint. It does not abbreviate countable additivity, measurability, finiteness, inhabitedness, decidable equality, or monotonicity.

The candidate family has the dependent Lean type definitions : forall i : I, Concept X (V i). Thus the formula does not replace the source family by a shared codomain. M is the imported residualEscapeMass and F is the imported capturedEscapeMass, whose definition is M(empty) minus M(S). The canonical defectRelation is the only target residual.

C1 through C8 map in order to the eight Lean conjuncts: the exact M formula together with positive M(empty); the exact two-step F definition; the captured-union expansion; monotonicity; four-term submodularity; diminishing returns under A subset B and d not in B; equivalence of the two greedy score formulations; and persistence of a pair lying in the baseline defect while every candidate readout identifies it. The present labels are weaker summaries, not extra predicates.

The proof reuses capture_weight_submodular for the coverage step and uses finite additivity to identify M(empty) minus M(S) with the mass of the captured union. The positive premise excludes the constant-zero interpretation; it is not used as a hidden premise for only one selected conclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture`
- Dependency: [D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture](../DefinitionCapture/MeasureCapture.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](../DefinitionEscape/FiniteCoverCounting.md)
