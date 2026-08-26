# Named Witnesses For Submodular Capture

## Abstract

Named finite models and attacks mechanically guard every submodular-capture clause.

**Theorem 1.1 (All capture witnesses and premise attacks occur together).**

$$\operatorname{present}\left(Wquant\right) \land \operatorname{present}\left(Wblind\right) \land \operatorname{present}\left(Wsubset\right) \land \operatorname{present}\left(Wzero\right) \land \operatorname{present}\left(Wadditive\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses.submodular_capture_witnesses_nonvacuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Wquant is finite_capture_laws_nonvacuous. Its three-edge Boolean model consumes the first seven theorem conjuncts and records exact M and F values, a nonempty captured union, strict monotonicity, strict submodularity, strict marginal decrease, and the greedy rewrite.

Wblind is fixed_language_blind_pair_persists_witness and consumes the eighth theorem conjunct on a concrete unequal Boolean pair. Wsubset is subset_premise_is_necessary_witness: the candidate is absent from B, but reversing A subset B makes the marginal inequality false. Wzero is constant_zero_weight_is_rejected_witness: its baseline defect is nonempty and its zero mass is finitely additive, but it fails the strict-positive premise.

Wadditive is finite_additivity_is_necessary_witness, whose proof directly reuses the canonical theorem marginal_capture_law_not_implied_by_escape_weight. Its object is the CAS marginalCaptureLaw over the canonical defectRelation, so it shows the weaker EscapeWeight fields alone do not imply diminishing capture. No second countermodel or residual is defined.

The five displayed present labels are deliberately weaker than the Lean conjunction. The Lean consumer repeats and consumes the complete statement of every witness, including all strict inequalities, memberships, equalities, premise failures, and the existential weak-weight countermodel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses.submodular_capture_witnesses_nonvacuous`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture](SubmodularCapture.md)
