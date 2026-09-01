# Step-Two Free-Lie Bridge

## Abstract

Degree-two chronological orientation is the universal free-Lie bracket and maps to every interpreted Lie commutator.

**Definition 1.1 (Universal degree-two free-Lie word).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieDegreeTwo`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ordered event pair is sent to the bracket of its two free-Lie generators.

**Theorem 1.2 (Free-Lie orientation reversal).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_swap`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two events negates their universal degree-two bracket.

**Theorem 1.3 (Repeated events have zero bracket).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_self`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The free-Lie degree-two word of one event with itself vanishes.

**Theorem 1.4 (Universal lift preserves the bracket).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Lie-algebra interpretation sends the universal event bracket to the corresponding interpreted bracket.

**Theorem 1.5 (Tensor and free-Lie orientations agree).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensor_and_free_lie_swap_orientation`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensor_and_free_lie_swap_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor alternant and free-Lie bracket both reverse sign under the same event exchange.

**Theorem 1.6 (Commuting interpretations annihilate degree two).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the interpreted bracket vanishes, the universal degree-two free-Lie word maps to zero.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.freeLieDegreeTwo`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_swap`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_self`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.tensor_and_free_lie_swap_orientation`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoFreeLieBridge.free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero`
- Dependency: [D5/S3/Observer/Chronology/PrimitiveMagnusLog](PrimitiveMagnusLog.md)
