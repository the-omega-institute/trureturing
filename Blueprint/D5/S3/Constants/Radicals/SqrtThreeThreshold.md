# Square Root of Three Threshold

## Abstract

Twice root three lies strictly above three.

**Theorem 1.1 (Twice root three exceeds three).**

$$3 < 2\cdot\sqrt{3}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Radicals/SqrtThreeThreshold.three_lt_two_mul_sqrt_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The secondary threshold in the source is strict: two times the square root of three is greater than three. The proof applies the pinned library's square-root comparison theorem to the rational inequality (3/2)^2 < 3, then rescales by two.

## References

- Truth anchor: `D5/S3/Constants/Radicals/SqrtThreeThreshold.three_lt_two_mul_sqrt_three`
