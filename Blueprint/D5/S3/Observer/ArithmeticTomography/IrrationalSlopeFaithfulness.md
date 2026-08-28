# Irrational Slope Faithfulness

## Abstract

An irrational linear slope faithfully encodes every integer pair as one real value.

**Theorem 1.1 (The irrational-slope observer is injective).**

$$\forall alpha: \mathbb{R}, \operatorname{Irrational}\left(alpha\right) \Rightarrow \operatorname{Injective}\left(((m, n): \mathbb{Z} \times \mathbb{Z} \mapsto alpha m + n)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness.irrational_slope_observer_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of two readings makes the slope times the difference of the first coordinates an integer. If that difference were nonzero, irrationality would be preserved under integer scaling, contradicting the integer value. Both coordinates therefore agree.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness.irrational_slope_observer_injective`
