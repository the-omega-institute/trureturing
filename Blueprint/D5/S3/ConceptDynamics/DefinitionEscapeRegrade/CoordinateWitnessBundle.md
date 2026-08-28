# Closed Coordinate Witness Bundle Characterization

## Abstract

Closed nonempty coordinate witnesses exactly record changed protected coordinates.

**Theorem 1.1 (Closed nonempty coordinate witnesses characterize record change).**

$$\begin{gathered}\forall TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(TargetChain\right)], [\operatorname{DecidableEq}\left(Domain\right)], [\operatorname{DecidableEq}\left(Epsilon\right)],\\{}[\operatorname{DecidableEq}\left(Condition\right)], [\operatorname{DecidableEq}\left(Comparator\right)], [\operatorname{DecidableEq}\left(Baseline\right)], [\operatorname{DecidableEq}\left(WeightSpec\right)],\\{}oldCoordinates, newCoordinates: \operatorname{ProtectedCoordinates}\left(TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec\right),\\{}\operatorname{HasClosedCoordinateWitnessBundle}\left(oldCoordinates, newCoordinates\right) \iff\\{}oldCoordinates \neq newCoordinates.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle.has_closed_coordinate_witness_bundle_iff_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CoordinateWitnessBundle records a finite set of changed labels and proves every registered dependent projection differs. Closed supplies the converse inclusion, while the existence predicate requires nonemptiness.

The reverse implication scans exactly the seven protected-coordinate labels using the supplied decidable equalities. If that scan were empty, frozen dependent extensionality would force the records equal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle.has_closed_coordinate_witness_bundle_iff_ne`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeRegrade/ProtectedCoordinateExtensionality](ProtectedCoordinateExtensionality.md)
