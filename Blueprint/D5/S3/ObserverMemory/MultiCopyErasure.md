# Finite Multi-Copy Record Erasure

## Abstract

A finite independent record family keeps a nonzero coherence entry nonzero exactly when every record overlap is nonzero.

**Theorem 1.1 (A zero-overlap copy erases a nonzero entry).**

$$\rho_{ij}\neq0 \Rightarrow\\\operatorname{channel}(R,\rho)_{ij}=0 \iff \exists k, g_{k}(i,j)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_quantifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of independent environment records act on one nonzero system matrix entry. Composing the frozen single-record channel once per copy multiplies that entry by the product of all record overlaps. The output is zero exactly when at least one copy has zero overlap at the selected pair of addresses.

**Theorem 1.2 (Coherence survives exactly when every copy has nonzero overlap).**

$$\rho_{ij}\neq0 \Rightarrow\\\operatorname{channel}(R,\rho)_{ij}\neq0 \iff \forall k, g_{k}(i,j)\neq0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_nonzero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero input entry, the output remains nonzero if and only if every record factor has nonzero overlap. Thus a family containing a zero-overlap copy erases the selected entry. This statement evaluates the composed record channel on its stated input; it does not apply another channel to the resulting output.

**Theorem 1.3 (Two copies give a nontrivial erasure certificate).**

$$\rho_{01}=\frac{1}{2} \land g_{0}(i,j)=0 \land g_{1}(i,j)=1 \land\\\operatorname{channel}(distinguishing,\rho)_{01}=0 \land \operatorname{channel}(independent,\rho)_{01}=\frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/MultiCopyErasure.two_copy_erasure_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original equal-superposition density matrix, the family containing one copied-address factor has zero off-diagonal overlap in that factor, and its channel erases the selected entry. The counterfactual family with two address-independent factors is evaluated separately on the same original matrix and leaves its one-half entry unchanged.

## References

- Truth anchor: `D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_nonzero_iff`
- Truth anchor: `D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_quantifier`
- Truth anchor: `D5/S3/ObserverMemory/MultiCopyErasure.two_copy_erasure_certificate`
- Dependency: [D5/S3/Observer/MeasurementMarginal](../Observer/MeasurementMarginal.md)
