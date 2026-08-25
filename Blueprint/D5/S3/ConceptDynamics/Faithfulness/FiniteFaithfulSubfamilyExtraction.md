# Finite Extraction of a Faithful Observer Family

## Abstract

A faithful observer family on a finite state carrier contains a faithful finite subfamily.

**Theorem 1.1 (Full joint faithfulness is witnessed by finitely many coordinates).**

$$\begin{aligned}\forall X, I: \operatorname{Type}, O: I \to \operatorname{Type},\\{}[\operatorname{Finite}(X)], q: \forall i: I, X \to O(i),\\\operatorname{Injective}(\operatorname{jointReadout}(q)) \implies\\\exists J: \operatorname{Finset}(I), \operatorname{Injective}(\operatorname{jointReadout}({i: \{i: I \mid i \in J\} \mapsto q(i)})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction.finite_faithful_subfamily_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full observer is the canonical dependent joint readout of the coordinate family. Its injectivity means every distinct pair of states is separated by at least one coordinate.

There are only finitely many distinct state pairs. A finite-subcover argument selects finitely many separating coordinates, and their restricted dependent joint readout remains injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction.finite_faithful_subfamily_extraction`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](JointFaithfulnessLeibnizCriterion.md)
