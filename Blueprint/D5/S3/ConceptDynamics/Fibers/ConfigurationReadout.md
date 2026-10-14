# Legal configuration readouts

## Abstract

Actual original-fibre composition and the unique static assignment from an empty reference.

**Theorem 1.1 (Two-edge diamonds characterize all legal path composites).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall C: \operatorname{Predicate}\left(\operatorname{Finset}\left(E\right)\right), (\forall R: \operatorname{LocalReadout}\left(C\right), ((\forall A: \operatorname{FiniteConfigurations}\left(C\right), (\forall B: \operatorname{FiniteConfigurations}\left(C\right), (\forall l: \operatorname{List}\left(E\right), (\forall m: \operatorname{List}\left(E\right), (\forall x: \operatorname{Fibre}\left(R, A\right), ((\operatorname{Exec}\left(A, l, B\right) \land \operatorname{Exec}\left(A, m, B\right)) \implies (\operatorname{legalPathMap}\left(C, R, A, B, l, x\right) = \operatorname{legalPathMap}\left(C, R, A, B, m, x\right)))))))) \iff \operatorname{LegalDiamonds}\left(C, R\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.actual_path_composition_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original readout has a fibre only at each finite legal configuration, and a map only at each actual basic edge. No state or edge map is postulated at an illegal configuration. Complete a legal fibre by Option of its proof-indexed original states; illegal vertices have only None. Each actual state embeds as Some. Along an execution with legal endpoints every intermediate lower set lies inside the legal final configuration and is legal. Thus a legal path remains Some, and its value determines a genuine endpoint-fibre map. Optional diamonds with illegal final endpoint end at None on both sides; those with legal final endpoint are exactly the supplied two-edge diamonds. The generic finite-endpoint connectivity theorem applies to this faithful completion. Injectivity of Some then gives equality of the original endpoint maps.

**Theorem 1.2 (The empty reference uniquely determines the compatible assignment).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall C: \operatorname{Predicate}\left(\operatorname{Finset}\left(E\right)\right), (\forall R: \operatorname{LocalReadout}\left(C\right), ((\operatorname{Apply}\left(C, \emptyset\right) \land \operatorname{LegalDiamonds}\left(C, R\right)) \implies (\forall x: \operatorname{EmptyFibre}\left(C, R\right), (\exists ! f: \operatorname{SectionSpace}\left(R\right), ((\operatorname{Apply}\left(f, \operatorname{EmptyConfiguration}\left(C\right)\right) = x) \land \operatorname{StaticCompatible}\left(C, R, f\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.static_assignment_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a legal path from the empty configuration to every finite configuration and transport the reference value along it. Diamond path independence makes the resulting value independent of that choice. Concatenating a chosen path with one actual basic edge proves compatibility with every supplied edge map. Conversely any compatible assignment propagates along every legal execution by induction, so its value at each configuration is the transported empty reference. This proves existence and uniqueness of the actual edge-compatible static assignment. Failure of a legal diamond prevents an unconditional removal of execution order.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.actual_path_composition_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.static_assignment_unique`
- Dependency: [D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport](ConfigurationPathTransport.md)
