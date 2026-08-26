# Named Witnesses For Submodular Capture

## Abstract

Named models, premise attacks, and universal refutations guard every capture clause.

**Theorem 1.1 (All capture witnesses and premise attacks occur together).**

$$\operatorname{present}\left(Wquant\right) \land \operatorname{present}\left(Wblind\right) \land \operatorname{present}\left(Wsubset\right) \land \operatorname{present}\left(Wzero\right) \land \operatorname{present}\left(Wadditive\right) \land \operatorname{present}\left(WfalseC1\right) \land \operatorname{present}\left(WfalseC2\right) \land \operatorname{present}\left(WfalseC3\right) \land \operatorname{present}\left(WfalseC4\right) \land \operatorname{present}\left(WfalseC5\right) \land \operatorname{present}\left(WfalseC6\right) \land \operatorname{present}\left(WfalseC7\right) \land \operatorname{present}\left(WfalseC8\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses.submodular_capture_witnesses_nonvacuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Wquant is finite_capture_laws_nonvacuous. Its three-edge Boolean model consumes the first seven theorem conjuncts and records exact M and F values, a nonempty captured union, strict monotonicity, strict submodularity, strict marginal decrease, and the greedy rewrite.

Wblind is fixed_language_blind_pair_persists_witness and consumes the eighth theorem conjunct on a concrete unequal Boolean pair. Wsubset is subset_premise_is_necessary_witness: the candidate is absent from B, but reversing A subset B makes the marginal inequality false. Wzero is constant_zero_weight_is_admissible_witness: its baseline defect is nonempty, costs are nonnegative, and its zero mass is finitely additive but not positive. This guards the removal of the unsupported global positivity premise.

Wadditive is finite_additivity_is_necessary_witness, whose proof directly reuses the canonical theorem marginal_capture_law_not_implied_by_escape_weight. Its object is the CAS marginalCaptureLaw over the canonical defectRelation, so it shows the weaker EscapeWeight fields alone do not imply diminishing capture. No second countermodel or residual is defined.

WfalseC1 through WfalseC8 are the named theorems clause_one_false_neighbor_witness through clause_eight_false_neighbor_witness. C1 through C7 are universally quantified refutations under exactly the theorem premises, including their finite-selection source-domain conditions. They respectively refute denial of the exact residual-mass formula; denial of F(S)=M(empty)-M(S); denial of the captured-union expansion; strict reverse monotonicity; strict reverse submodularity; strictly increasing marginal capture while retaining subset and freshness; and denial of the residual-score/capture-score equivalence. Thus their negations are theorems for every admissible model, not facts that happen only in one finite model. C8 is likewise universal but has no finite-selection premise: it flips only the conclusion from membership to nonmembership and refutes that neighbor under the unchanged blind-pair hypotheses.

The displayed present labels are deliberately weaker than the Lean conjunction. The Lean consumer repeats and consumes the complete statement of every witness, including all strict inequalities, memberships, equalities, premise failures, and the existential weak-weight countermodel.

scribe_lean_correspondence: Wquant maps to finite_capture_laws_nonvacuous; Wblind to fixed_language_blind_pair_persists_witness; Wsubset to subset_premise_is_necessary_witness; Wzero to constant_zero_weight_is_admissible_witness; and Wadditive to finite_additivity_is_necessary_witness. WfalseC1 through WfalseC8 map in order to clause_one_false_neighbor_witness through clause_eight_false_neighbor_witness. Each of these thirteen Formula items is weaker because present(name) omits the full Lean statement. Equal mappings: zero. Stronger mappings: zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses.submodular_capture_witnesses_nonvacuous`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture](SubmodularCapture.md)
