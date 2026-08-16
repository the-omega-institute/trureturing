# Periodic Three Complement

## Abstract

The period-three continued-fraction tail and its [0;1,2] prefix are complementary.

**Theorem 1.1 (The period-three tail has an exact complementary prefix).**

$$x=\frac{\sqrt{13}-3}{2},\quad \operatorname{CF}(x)=[0;\overline{3}],\quad \frac{1}{1+\frac{1}{2+x}}+x=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicThreeComplement.periodic_three_continued_fraction_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x=(sqrt(13)-3)/2. Its floor is zero, and the inverse of its fractional part is 3+x. Mathlib's of_h_eq_floor, of_s_head, and of_s_succ recurrences therefore compute every continued-fraction coefficient after the head as 3. The same quadratic fixed-point identity reduces the [0;1,2] prefix to 1-x.

This declaration closes only the continued-fraction identity in residual remark/27.447-27.450. The subsequent lambda=4 accumulation claim, the 647-word survey, and the stated derived-set candidates remain outside this formalization.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicThreeComplement.periodic_three_continued_fraction_complement`
