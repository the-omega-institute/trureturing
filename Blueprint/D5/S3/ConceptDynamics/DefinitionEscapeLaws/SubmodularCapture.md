# Submodular Definition-Escape Capture

## Abstract

Finite source selections and additive escape mass satisfy the proved DECT capture laws.

**Theorem 1.1 (Capture is monotone, submodular, and has diminishing marginal returns).**

$$\forall I, X, C, Target: Type,\ V: I \to Type,\ definitions: \forall i: I, \operatorname{Concept}\left(X, \operatorname{apply}\left(V, i\right)\right),\ q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Target\right),\ c: I \to Real, nu: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\ \left(\operatorname{nonnegativeCost}\left(c\right) \land \operatorname{disjointAdditive}\left(nu\right)\right) \Rightarrow \left(\left(\operatorname{finite}\left(S1\right) \Rightarrow \operatorname{present}\left(C1\right)\right) \land \left(\left(\operatorname{finite}\left(S2\right) \Rightarrow \operatorname{present}\left(C2\right)\right) \land \left(\left(\operatorname{finite}\left(S3\right) \Rightarrow \operatorname{present}\left(C3\right)\right) \land \left(\left(\left(\operatorname{finite}\left(A4\right) \land \left(\operatorname{finite}\left(B4\right) \land \operatorname{subset}\left(A4, B4\right)\right)\right) \Rightarrow \operatorname{present}\left(C4\right)\right) \land \left(\left(\left(\operatorname{finite}\left(A5\right) \land \operatorname{finite}\left(B5\right)\right) \Rightarrow \operatorname{present}\left(C5\right)\right) \land \left(\left(\left(\operatorname{finite}\left(B6\right) \land \left(\operatorname{subset}\left(A6, B6\right) \land \operatorname{notMember}\left(definition6, B6\right)\right)\right) \Rightarrow \operatorname{present}\left(C6\right)\right) \land \left(\left(\operatorname{finite}\left(S7\right) \Rightarrow \operatorname{supportingLemma}\left(greedyScoreRewrite\right)\right) \land \operatorname{present}\left(C8\right)\right)\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed implication retains finiteness as a source-domain annotation on C1 through C7. The Lean theorem proves those clauses without finite-selection premises, so each displayed finite antecedent is weaker than its Lean counterpart rather than an additional Lean guard. C4 also retains A4 subset B4; C6 retains A6 subset B6 and definition6 not in B6. C8 has no finiteness premise, and I itself is not required to be finite. nonnegativeCost means zero is below every c(gamma), and disjointAdditive means exactly that mass(left union right) equals mass(left) plus mass(right) whenever left and right are disjoint. It does not assume strictly positive cost, positive baseline mass, countable additivity, measurability, inhabitedness, or decidable equality.

The candidate family has the dependent Lean type definitions : forall i : I, Concept X (V i). Thus the formula does not replace the source family by a shared codomain. M is the imported residualEscapeMass and F is the imported capturedEscapeMass, whose definition is M(empty) minus M(S). The canonical defectRelation is the only target residual.

C1 through C6 map in order to the first six Lean conjuncts: the exact M formula; the exact two-step F definition; the captured-union expansion; monotonicity; four-term submodularity; and diminishing returns under A subset B and d not in B. supportingLemma(greedyScoreRewrite) maps to Lean conjunct seven, which proves only equivalence of the residual-score and capture-score comparison predicates. C8 maps to Lean conjunct eight, persistence of a baseline-defect pair that every candidate readout identifies. The present and supportingLemma labels are weaker summaries, not extra predicates.

The proof reuses capture_weight_submodular for the coverage step and uses finite additivity to identify M(empty) minus M(S) with the mass of the captured union. Nondegeneracy is supplied separately by a named positive model, so the theorem itself still admits the constant-zero weight required by the source's full domain.

The finite-selection annotations are retained only in this weaker source summary and do not occur in the Lean theorem type. nonnegativeCost is likewise not advertised as a proof guard. disjointAdditive is a proof guard, with its absence consumed by the named weak-weight countermodel.

C7 proves equality of the residual and capture score predicates. The remaining greedy-rule obligations are recorded as six locatable residual-ledger subitems, not inserted as a ninth authoritative formula conjunct.

scribe_lean_correspondence: C1, C2, C3, C4, C5, C6, C7, and C8 map respectively to Lean conjuncts one through eight. Every displayed item is weaker: present(C1-C6,C8) and supportingLemma(C7) summarize the full Lean predicates, while C1-C7 additionally retain finite source-domain annotations. C4 binds A4 subset B4, and C6 binds A6 subset B6 plus definition6 not in B6. Equal mappings: zero. Stronger mappings: zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.submodular_capture`
- Dependency: [D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture](../DefinitionCapture/MeasureCapture.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](../DefinitionEscape/FiniteCoverCounting.md)
