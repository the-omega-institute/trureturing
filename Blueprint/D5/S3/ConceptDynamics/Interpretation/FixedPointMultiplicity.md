# Fixed-Point Multiplicity and Actuality

## Abstract

Powerset endomorphisms realize every fixed-point multiplicity, while a unique fixed point need not belong to a nonempty actuality predicate.

**Theorem 1.1 (Self-consistency neither forces uniqueness nor selects actuality).**

$$\begin{gathered}(\neg\exists S: \operatorname{Set}(Unit), \operatorname{compl}(S) = S) \land\\{}(\exists! S: \operatorname{Set}(Unit), \emptyset = S) \land\\{}(\exists S: \operatorname{Set}(Bool), T: \operatorname{Set}(Bool), S \neq T \land \operatorname{inter}(S, \{false\}) = S \land \operatorname{inter}(T, \{false\}) = T) \land\\{}(\forall S: \operatorname{Set}(Unit), \operatorname{union}(S, \emptyset) = S) \land\\{}((\exists S: \operatorname{Set}(Bool), \operatorname{inter}(S, \{false\}) = S) \land (\neg\exists! S: \operatorname{Set}(Bool), \operatorname{inter}(S, \{false\}) = S)) \land\\{}(\exists \mathcal{A}: \operatorname{Set}(\operatorname{Set}(Unit)), \operatorname{Nonempty}(\mathcal{A}) \land (\exists! S: \operatorname{Set}(Unit), \emptyset = S) \land \forall S: \operatorname{Set}(Unit), \emptyset = S \Rightarrow \neg S \in \mathcal{A}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/FixedPointMultiplicity.fixed_point_multiplicity_and_actuality_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complement on subsets of a singleton has no fixed point; a constant-empty map has exactly one; intersection with the Boolean singleton has distinct fixed points; and union with the empty set fixes every subset of the singleton.

The same multiple-fixed-point construction directly refutes uniqueness. For actuality, the theorem supplies a nonempty predicate on singleton subsets that excludes every fixed point of the uniquely fixing constant-empty map. The source's selector list is qualitative guidance without in-scope predicates, so no selector semantics are invented.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/FixedPointMultiplicity.fixed_point_multiplicity_and_actuality_gap`
