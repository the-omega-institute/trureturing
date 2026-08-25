# Named Nonvacuity Witnesses For The Direct DECT Laws

## Abstract

Ten named witnesses make every packaged direct DECT law mechanically nonvacuous.

**Theorem 1.1 (All named direct-law witnesses are present together).**

$$\operatorname{present}\left(W1\right) \land \operatorname{present}\left(W2\right) \land \operatorname{present}\left(W3a\right) \land \operatorname{present}\left(W3b\right) \land \operatorname{present}\left(W4\right) \land \operatorname{present}\left(W5\right) \land \operatorname{present}\left(W7\right) \land \operatorname{present}\left(W8\right) \land \operatorname{present}\left(W9\right) \land \operatorname{present}\left(Wcapture\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLawWitnesses.directly_provable_laws_witnesses_nonvacuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed present labels are a deliberately weaker summary of the Lean conjunction. In source order, the Lean theorem extracts a concrete residual pair for clause one, identity factorization for clause two, both a redundant-readout pair and the Empty-state FactorsThrough-not-Refines separation for clause three, a blind pair for clause four, finite closure from a nonempty baseline defect for clause five, nonzero prepared and semigroup defects for clauses seven and eight, and a tight cascade bound for clause nine.

The Lean package consumes the complete statement of every named witness, including all premises, equalities, memberships, nonemptiness claims, factorizations, obstructions, and strict or tight inequalities. The displayed present labels only record the weaker fact that all ten complete witnesses occur together. The final label is an adjacent strict captured-mass submodularity example; it is not source clause six and does not close TASK D5-T0049.

W1, W2, W3a, W3b, W4, W5, W7, W8, W9, and Wcapture map respectively to clause1_nonvacuity_witness, clause2_nonvacuity_witness, clause3_nonvacuity_witness, clause3_fiber_constancy_not_refines_witness, clause4_nonvacuity_witness, clause5_nonvacuity_witness, clause7_nonvacuity_witness, clause8_nonvacuity_witness, clause9_nonvacuity_witness, and adjacent_capture_submodularity_strict_witness.

There are ten names because clause three has two independent checks and the adjacent capture boundary is retained separately. The package requires each full witness type, so deleting any witness or weakening any conjunct in one makes the package fail to elaborate instead of silently accepting a decorative example.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLawWitnesses.directly_provable_laws_witnesses_nonvacuous`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLaws](DirectlyProvableLaws.md)
