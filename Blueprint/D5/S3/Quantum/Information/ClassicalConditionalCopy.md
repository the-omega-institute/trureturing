# Classical Pointer Conditional Copy

## Abstract

A physical conditional copy over a finite classical pointer, with unrestricted BC blocks.

Let X, B, C be finite carriers, p a nonnegative distribution of total mass one on X, and tau_x an arbitrary density state on B tensor C. The original state is recordState p tau. The copied state is the same orthogonal pointer record with fragment tau_x tensor Tr_B(tau_x). No orthogonality, commutativity or separability of the tau_x is assumed. The pointer supplies orthogonality of the whole record components. Weights may vanish, and singular and entangled BC blocks remain allowed.

**Theorem 1.1 (Discarding E recovers the original state).**

$$\operatorname{TrE}\left(omega\right) = \rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalConditionalCopy.conditionalCopy_discard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual finite-coordinate partial trace over the appended C carrier returns each tau_x, hence the original XBC density matrix.

**Theorem 1.2 (The pointer-copy density agrees).**

$$\operatorname{omegaXE}\left(omega\right) = \operatorname{rhoXC}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalConditionalCopy.conditionalCopy_pointer_copy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing BC after an explicit index permutation gives recordState p (Tr_B tau). This is exactly the original XC density with E replacing C.

**Theorem 1.3 (The exact copy entropy).**

$$\operatorname{S}\left(XBCE\right) = \operatorname{S}\left(XBC\right) + \operatorname{S}\left(XE\right) - \operatorname{H}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalConditionalCopy.entropy_conditionalCopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing orthogonal-mixture entropy theorem applies to whole pointer components. Existing product-state entropy adds inside each block. Their finite weighted sums give the displayed equality in nats.

## References

- Truth anchor: `D5/S3/Quantum/Information/ClassicalConditionalCopy.conditionalCopy_discard`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalConditionalCopy.conditionalCopy_pointer_copy`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalConditionalCopy.entropy_conditionalCopy`
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](StrongSubadditivity.md)
