# Context Extension and Complement Transport

## Abstract

A finite context embedding transports complements with an explicit new-region charge defect.

**Proposition 1.1 (The complete extension and complement proposition).**

$$R = OmegaD \setminus \operatorname{j}\left(OmegaC\right), \operatorname{q}\left(D, \operatorname{j}\left(A\right)\right) = \operatorname{q}\left(C, A\right) \land \left(OmegaD \setminus \operatorname{j}\left(A\right) = \operatorname{j}\left(OmegaC \setminus A\right) \operatorname{union} R \land \left(\operatorname{Disjoint}\left(\operatorname{j}\left(OmegaC \setminus A\right), R\right) \land \left(\operatorname{q}\left(D, \operatorname{complement}\left(D, \operatorname{j}\left(A\right)\right)\right) - \operatorname{q}\left(C, \operatorname{complement}\left(C, A\right)\right) = \operatorname{charge}\left(D, R\right) \land \left(\left(OmegaD \setminus \operatorname{j}\left(A\right) = \operatorname{j}\left(OmegaC \setminus A\right) \Leftrightarrow R = \emptyset\right) \land \left(\left(\operatorname{q}\left(D, \operatorname{complement}\left(D, \operatorname{j}\left(A\right)\right)\right) = \operatorname{q}\left(C, \operatorname{complement}\left(C, A\right)\right) \Leftrightarrow \operatorname{charge}\left(D, R\right) = 0\right) \land \left(\left(\operatorname{Balanced}\left(C\right) \land \operatorname{Balanced}\left(D\right)\right) \Rightarrow \operatorname{charge}\left(D, R\right) = 0\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.context_extension_complement_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite context embedding and an old selection, let R be the new current region. The kernel-checked conjunction records all three displayed transport identities together with disjointness, the exactness criterion, the zero-charge readout criterion, and the balanced-context consequence.

The individual declarations below expose each component for downstream use; the conjunction records the proposition's complete algebraic content.

**Theorem 1.2 (Transport preserves the selected readout).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.map_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.map_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An attribute-preserving archive embedding maps every old current selection into the new current region. The signed finite sum is unchanged by this transport, so q of the mapped history equals q of the original history.

**Theorem 1.3 (Transport preserves q).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_map`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The q-valued form is the same transported readout identity after packaging the context and selection pair.

**Theorem 1.4 (The transported complement splits exactly).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complement of a mapped selection in the larger current region is the disjoint union of the mapped old complement and the genuinely new current events. This finite set identity accounts for every event and uses the embedding's current region containment.

**Theorem 1.5 (The two complement pieces are disjoint).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_map_disjoint_newRegion`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_map_disjoint_newRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mapped old complement and the new current region cannot share an event: membership in the latter excludes membership in the mapped old current region.

**Theorem 1.6 (The complement readout defect is exactly new-region charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_charge_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_charge_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the old complement readout from the transported complement readout cancels the mapped old events. The only remaining contribution is the signed charge of the new current region.

**Theorem 1.7 (The q complement defect is exactly new-region charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_charge_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_charge_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The q-valued form packages the same complement difference and therefore has the same new-region charge defect.

**Theorem 1.8 (Exact complement transport is equivalent to no new region).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition_exact_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition_exact_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set decomposition reduces to literal equality with the mapped old complement precisely when the new current region is empty. This is an exact finite iff, separate from the weaker possibility of charge cancellation.

**Theorem 1.9 (Complement readouts agree exactly when the defect balances).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_readout_exchange_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_readout_exchange_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerical complement readouts are equal exactly when the new current region has zero signed charge. Thus a nonempty extension can still be invisible to q when its positive and negative contributions balance.

**Theorem 1.10 (Underlying complement readouts agree exactly when the defect balances).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_readout_exchange_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_readout_exchange_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same defect criterion holds for the underlying signed readout: equality of the two complement readouts is equivalent to zero charge in the new region.

**Theorem 1.11 (Balanced contexts make the extension charge vanish).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.balanced_newRegion_charge_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.balanced_newRegion_charge_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both source and target contexts are balanced, the target background charge splits between the transported source current region and the new region. Since transport preserves the source charge and both backgrounds are zero, the new region has zero signed charge. Exact set equality can still fail when that region is nonempty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.balanced_newRegion_charge_zero`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_charge_difference`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_decomposition_exact_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_map_disjoint_newRegion`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.complement_readout_exchange_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.context_extension_complement_spec`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.map_readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_charge_difference`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_complement_readout_exchange_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.q_map`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](ComplementCharge.md)
