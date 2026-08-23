# Target-Relative Biinterpretation

## Abstract

Mutual recovery of selected targets transports answerability without identifying all internal states.

**Theorem 1.1 (Target-relative recovery transports answerability without state isomorphism).**

$$(\forall X \in Type, Y \in Type, I \in Type, J \in Type, A \in Type, B \in Type, h \in X \to Y, k \in Y \to X, T \in I \to \operatorname{Concept}\left(X, A\right), S \in J \to \operatorname{Concept}\left(Y, B\right),\; \left(\left(\forall i \in I,\; T_{i} \circ k \circ h = T_{i}\right) \Rightarrow \left(\forall i \in I,\; \operatorname{Refines}\left(T_{i}, h\right)\right)\right) \land \left(\left(\forall j \in J,\; S_{j} \circ h \circ k = S_{j}\right) \Rightarrow \left(\forall j \in J,\; \operatorname{Refines}\left(S_{j}, k\right)\right)\right)) \land (firstCoordinateTarget \circ setSecondTrueCoordinate \circ eraseSecondCoordinate = firstCoordinateTarget \land \left(firstCoordinateTarget \circ eraseSecondCoordinate \circ setSecondTrueCoordinate = firstCoordinateTarget \land \left(\left(\neg \operatorname{Bijective}\left(eraseSecondCoordinate\right)\right) \land \left(\left(\neg \operatorname{Bijective}\left(setSecondTrueCoordinate\right)\right) \land \left(setSecondTrueCoordinate \circ eraseSecondCoordinate \ne id \land eraseSecondCoordinate \circ setSecondTrueCoordinate \ne id\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/TargetRelativeBiinterpretation.target_relative_biinterpretation_transports_answerability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward translation h, reverse translation k, and both indexed target families are public source primitives. If every source target is recovered after h then k, that target factors through h using its composition with k as the answer map.

The reverse argument has a disjoint recovery premise: if every target-model target is recovered after k then h, it factors through k using its composition with h. These are the two public Refines conclusions from the family's canonical answerability relation.

The public countermodel uses internal states Bool times Bool. The forward map replaces the second coordinate by false, the reverse map replaces it by true, and both target families observe only the first coordinate. Both target-recovery equations therefore hold.

Each translation identifies states that differ only in the second coordinate, so neither is bijective. Their composites set that coordinate to true or false and hence neither composite is the identity. Thus agreement on all selected targets does not imply isomorphism of internal states.

The module imports Concept and Refines as the family single source of truth. The concrete maps are coordinate constructions, not definitions of the factorization or non-isomorphism conclusions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/TargetRelativeBiinterpretation.target_relative_biinterpretation_transports_answerability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
