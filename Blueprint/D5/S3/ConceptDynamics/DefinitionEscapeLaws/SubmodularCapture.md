# Submodular Definition-Escape Capture

## Abstract

Clause-local finite selections and additive escape mass satisfy the proved DECT capture laws.

**Theorem 1.1 (Capture is monotone, submodular, and has diminishing marginal returns).**

$$\forall I, X, C, Target: Type,\ V: I \to Type,\ definitions: \forall i: I, \operatorname{Concept}\left(X, \operatorname{apply}\left(V, i\right)\right),\ q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Target\right),\ c: I \to Real, nu: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\ \left(\operatorname{nonnegativeCost}\left(c\right) \land \operatorname{disjointAdditive}\left(nu\right)\right) \Rightarrow \left(\left(\operatorname{finite}\left(S1\right) \Rightarrow \operatorname{present}\left(C1\right)\right) \land \left(\left(\operatorname{finite}\left(S2\right) \Rightarrow \operatorname{present}\left(C2\right)\right) \land \left(\left(\operatorname{finite}\left(S3\right) \Rightarrow \operatorname{present}\left(C3\right)\right) \land \left(\left(\left(\operatorname{finite}\left(A4\right) \land \operatorname{finite}\left(B4\right)\right) \Rightarrow \operatorname{present}\left(C4\right)\right) \land \left(\left(\left(\operatorname{finite}\left(A5\right) \land \operatorname{finite}\left(B5\right)\right) \Rightarrow \operatorname{present}\left(C5\right)\right) \land \left(\left(\operatorname{finite}\left(B6\right) \Rightarrow \operatorname{present}\left(C6\right)\right) \land \left(\left(\operatorname{finite}\left(S7\right) \Rightarrow \operatorname{supportingLemma}\left(greedyScoreRewrite\right)\right) \land \left(\operatorname{present}\left(C8\right) \land \operatorname{open}\left(greedyArgmaxRuleUnresolved\right)\right)\right)\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed implication preserves all source ambient conditions. Finiteness is clause-local: C1 uses finite(S1), C2 finite(S2), C3 finite(S3), C4 finite(A4) and finite(B4), C5 finite(A5) and finite(B5), C6 finite(B6), and the score rewrite finite(S7). C8 has no finiteness premise, and I itself is not required to be finite. nonnegativeCost means zero is below every c(gamma), and disjointAdditive means exactly that mass(left union right) equals mass(left) plus mass(right) whenever left and right are disjoint. It does not assume strictly positive cost, positive baseline mass, countable additivity, measurability, inhabitedness, or decidable equality.

The candidate family has the dependent Lean type definitions : forall i : I, Concept X (V i). Thus the formula does not replace the source family by a shared codomain. M is the imported residualEscapeMass and F is the imported capturedEscapeMass, whose definition is M(empty) minus M(S). The canonical defectRelation is the only target residual.

C1 through C6 map in order to the first six Lean conjuncts: the exact M formula; the exact two-step F definition; the captured-union expansion; monotonicity; four-term submodularity; and diminishing returns under A subset B and d not in B. supportingLemma(greedyScoreRewrite) maps to Lean conjunct seven, which proves only equivalence of the residual-score and capture-score comparison predicates. C8 maps to Lean conjunct eight, persistence of a baseline-defect pair that every candidate readout identifies. The present and supportingLemma labels are weaker summaries, not extra predicates.

The proof reuses capture_weight_submodular for the coverage step and uses finite additivity to identify M(empty) minus M(S) with the mass of the captured union. Nondegeneracy is supplied separately by a named positive model, so the theorem itself still admits the constant-zero weight required by the source's full domain.

The clause-local finite premises and nonnegativeCost are retained as source-domain conditions, not advertised as proof guards: deleting them currently produces no named failure. disjointAdditive is a proof guard, with its absence consumed by the named weak-weight countermodel.

GREEDY_ARGMAX_RULE_UNRESOLVED: C7 proves equality of the residual and capture score predicates. The source gives no candidate-domain, argmax-existence, tie, zero-cost, or freshness convention, so this module does not strengthen that algebraic identity into an existence claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture`
- Dependency: [D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture](../DefinitionCapture/MeasureCapture.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](../DefinitionEscape/FiniteCoverCounting.md)
