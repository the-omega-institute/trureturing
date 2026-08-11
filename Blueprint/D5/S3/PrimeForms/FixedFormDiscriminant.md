# Fixed-Form Discriminant

## Abstract

The fixed-point form discriminant of a 2×2 integer matrix equals tr²−4·det; at determinant −1 it is tr²+4.

**Theorem 1.1 (At determinant −1 the fixed-form discriminant is tr²+4).**

$$ad - bc = -1 \Rightarrow (d-a)^2 + 4bc = (a+d)^2 + 4$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/FixedFormDiscriminant.det_neg_one_fixed_form_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-point equation x = (ax+b)/(cx+d) of a 2×2 integer matrix [[a,b],[c,d]] gives the quadratic c·x² + (d−a)·x − b, whose discriminant is (d−a)² + 4bc. By the ring identity this equals (a+d)² − 4(ad−bc) = tr² − 4·det. When the determinant ad−bc is −1, the discriminant is exactly tr² + 4.

For the pinned odd core of trace 12j (determinant −1), the discriminant specialises to (12j)² + 4 = 4(36j² + 1), exactly four times the negative-Pell discriminant d_j = 36j² + 1. No claim is made about class-equivalence or the minimum of the core form beyond this discriminant identity.

## References
