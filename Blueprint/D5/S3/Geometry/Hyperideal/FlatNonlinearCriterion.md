# Exact nonlinear flat criterion

## Abstract

The exact nonlinear correction separates the flat boundary from the symmetric transverse case.

Use the six independent positive coordinates in the order (r,a,b,o,c,d). Set A=rad(r,a,d), B=rad(r,b,c), C=r^2-1+(a-d)(c-b)+2(r+1)sqrt(abcd), S=sqrt(ac)+sqrt(bd), and J=(sqrt(AB)-C)/(r+1). The auxiliary C is the inner product of the two explicit three-dimensional vectors used in the Cauchy bound.

The correction J is nonnegative. The original cosine is at most -1 exactly when the opposite product (r-1)(o-1) reaches S^2+J. Equality J=0 occurs exactly on the opposite-pair symmetry a=c and b=d; there the criterion reduces to (r-1)(o-1)>=(a+b)^2.

**Theorem 1.1 (Nonnegative nonlinear correction).**

$$\forall r \in Real, a \in Real, b \in Real, c \in Real, d \in Real,\; \left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow 0 \le J\left(r, a, b, c, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.J_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite Cauchy-Schwarz applied to the explicit three-coordinate vectors proves C<=sqrt(AB), and the positive factor r+1 preserves the inequality.

**Theorem 1.2 (Exact flat iff).**

$$\forall r \in Real, a \in Real, b \in Real, o \in Real, c \in Real, d \in Real,\; \left(\left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow \left(cosine\left(r, a, b, o, c, d\right) \le -1 \Leftrightarrow \left(r - 1\right) \cdot \left(o - 1\right) \ge S\left(a, b, c, d\right)^{2} + J\left(r, a, b, c, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.cosine_le_neg_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding numerator+C gives (r+1)(S^2-(r-1)(o-1)); replacing sqrt(AB) by C+(r+1)J and using the positive denominator yields the iff.

**Theorem 1.3 (Equality characterization).**

$$\forall r \in Real, a \in Real, b \in Real, c \in Real, d \in Real,\; \left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow \left(J\left(r, a, b, c, d\right) = 0 \Leftrightarrow \left(a = c \land b = d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.J_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram determinant is a sum of three squares. Its vanishing forces equality of the two vector coordinates and then a=c and b=d; the converse follows by direct substitution.

**Theorem 1.4 (Symmetric transverse reduction).**

$$\forall r \in Real, a \in Real, b \in Real, o \in Real,\; \left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \Rightarrow \left(cosine\left(r, a, b, o, a, b\right) \le -1 \Leftrightarrow \left(r - 1\right) \cdot \left(o - 1\right) \ge \left(a + b\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.symmetric_cosine_le_neg_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When c=a and d=b, the square-root terms reduce to a and b and the equality characterization gives J=0, yielding the sharp reduced product test.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.J_eq_zero_iff`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.J_nonneg`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.cosine_le_neg_one_iff`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.symmetric_cosine_le_neg_one_iff`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
