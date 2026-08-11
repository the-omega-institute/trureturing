# Fixed-Form Discriminant

## Abstract

The fixed-point form discriminant of a 2x2 integer matrix equals tr^2 - 4 det; at determinant -1 it is tr^2 + 4.

**Theorem 1.1 (At determinant minus one the fixed-form discriminant is trace squared plus four).**

$$ad-bc=-1 \Rightarrow (d-a)^{2}+4bc=(a+d)^{2}+4$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/FixedFormDiscriminant.det_neg_one_fixed_form_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-point equation x = (a x + b)/(c x + d) of a 2x2 integer matrix [[a,b],[c,d]] gives the quadratic c x^2 + (d - a) x - b, whose discriminant is (d - a)^2 + 4 b c. By the ring identity this equals (a + d)^2 - 4(a d - b c) = tr^2 - 4 det. When the determinant a d - b c is -1, the discriminant is exactly tr^2 + 4.

For the pinned odd core of trace 12 j (determinant -1), the discriminant specialises to (12 j)^2 + 4 = 4(36 j^2 + 1), exactly four times the negative-Pell discriminant d_j = 36 j^2 + 1. No claim is made about class-equivalence or the minimum of the core form beyond this discriminant identity.

## References

- Truth anchor: `D5/S3/PrimeForms/FixedFormDiscriminant.det_neg_one_fixed_form_disc`
