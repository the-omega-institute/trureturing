# Uniform Resolvent Remainder

## Abstract

A spectral floor of two gives a quadratic resolvent remainder constant of one quarter.

Let A and E be real square matrices on any finite decidable index type, including the empty type. Write I for the identity. Matrix order is the positive semidefinite order: X is at most Y when Y-X is positive semidefinite. Herm denotes symmetry and Unit denotes invertibility. Every matrix norm below is the spectral norm induced by the Euclidean vector norm. The inverse is the nonsingular matrix inverse. The real number c in the first statement is arbitrary.

**Theorem 1.1 (An inverse controlled by a positive floor).**

$${{Herm\left(A\right)}\land {{0 < c}\land {c\cdot I \le A}}}\implies {{Unit\left(A\right)}\land {\Vert (A)^{-1}\Vert  \le (c)^{-1}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_control_of_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real spectral value of A is at least c. When c is positive, zero is absent from the spectrum, so A is invertible. Continuous functional calculus represents the inverse by the scalar function x mapped to its reciprocal. The norm estimate for this calculus bounds the inverse norm by the reciprocal of c.

**Theorem 1.2 (The perturbed spectral floor).**

$${{2\cdot I \le A}\land {{Herm\left(E\right)}\land {\Vert E\Vert  \le 1}}}\implies {I \le A+E}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/UniformResolventRemainder.perturbed_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute value of each real spectral value of E is at most its spectral norm, hence at most one. Symmetry therefore gives E at least minus I in matrix order. Add this to A at least twice I to obtain the stated lower bound.

**Theorem 1.3 (The two inverse norms).**

$${{Herm\left(A\right)}\land {{Herm\left(E\right)}\land {{2\cdot I \le A}\land {\Vert E\Vert  \le 1}}}}\implies {{\Vert (A)^{-1}\Vert  \le \frac{1}{2}}\land {\Vert (A+E)^{-1}\Vert  \le 1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the general inverse estimate to A with c=2 and to A+E with c=1. The sum is symmetric, and the preceding spectral floor supplies its positive lower bound. Neither constant contains the size of the index type.

Define R=A inverse E A inverse E (A+E) inverse, with the factors in that order. This is the five-factor term in the first-order inverse expansion. The following estimate concerns that matrix product.

**Theorem 1.4 (The quadratic remainder bound).**

$${{Herm\left(A\right)}\land {{Herm\left(E\right)}\land {{2\cdot I \le A}\land {\Vert E\Vert  \le 1}}}}\implies {\Vert R\Vert  \le \frac{\Vert E\Vert ^{2}}{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/UniformResolventRemainder.remainder_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Submultiplicativity bounds the product norm by the product of its five norms. The two factors A inverse each contribute at most one half, the last inverse contributes at most one, and the two perturbation factors contribute the square of the norm of E. The resulting constant one quarter is the same in every finite dimension.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_bounds`
- Truth anchor: `D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_control_of_lower_bound`
- Truth anchor: `D5/S3/Observer/BlockStructure/UniformResolventRemainder.perturbed_lower_bound`
- Truth anchor: `D5/S3/Observer/BlockStructure/UniformResolventRemainder.remainder_bound`
