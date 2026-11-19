# Finite Half-Current Lowering

## Abstract

Finite evaluation of the original lowering action on marked oscillator words

**Theorem 1.1 (Termination at the original cutoff).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_lowering_word`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_lowering_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normally ordered polynomial evaluates to the factorial-normalized original lowering flow at every cutoff for which the remaining powers vanish.

**Theorem 1.2 (Finite creation and pair contraction).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_word_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_word_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unpaired oscillator contributes the finite binomial creator. A paired oscillator contributes the original Gram entry times the ordinary coefficient of the regular Cauchy correction.

**Theorem 1.3 (Ordinary Möbius pullback coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.half_pullback_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.half_pullback_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal local coordinate and its half-current Jacobian produce the same finite binomial creator coefficients, with the scale at the surviving mode.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_lowering_word`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.evaluate_word_step`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.half_pullback_coefficient`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy](OriginalHalfCurrentCauchy.md)
