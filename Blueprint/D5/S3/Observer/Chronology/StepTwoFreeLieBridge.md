# Step-Two Free Lie and Representation Bridge

## Abstract

Tensor Magnus brackets map to represented commutators and free Lie brackets.

**Definition 1.1 (Tensor multiplication representation).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensorMultiplication`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensorMultiplication` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's multiplication map sends a tensor pair to its product in the chosen associative algebra.

**Definition 1.2 (Represented tensor signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.representTensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.representTensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Degree one is retained and the genuine degree-two tensor is multiplied inside the target algebra.

**Definition 1.3 (Free Lie evaluation).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieEvaluation`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's universal property extends event values uniquely to a Lie homomorphism into the associative algebra with commutator bracket.

**Theorem 1.4 (Tensor and free-Lie agreement).**

$$\operatorname{mul}(\operatorname{tensorCommutator}(\operatorname{f}(a), \operatorname{f}(b))) = \operatorname{freeLieEval}(f, \operatorname{bracket}(\operatorname{of}(a), \operatorname{of}(b))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensor_and_free_lie_brackets_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The representation of a single-event signature is its truncated exponential, the representation is multiplicative for Chen composition, and it is compatible with every chronological word signature; the universal tensor bracket maps to the ring commutator, so the primitive Magnus coordinate represents to the step-two Magnus logarithm, with two events giving exactly the represented commutator.

The bracket of two free generators evaluates to the commutator of their observed values, so the tensor and free-Lie realizations agree under every associative-algebra representation.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieEvaluation`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.representTensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensorMultiplication`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensor_and_free_lie_brackets_agree`
- Dependency: [D5/S3/Observer/Chronology/PrimitiveMagnusLog](PrimitiveMagnusLog.md)
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalSignature](StepTwoChronologicalSignature.md)
