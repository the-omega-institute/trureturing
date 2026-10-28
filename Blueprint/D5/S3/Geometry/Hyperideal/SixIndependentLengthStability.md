# A quantitative stability envelope for broken pairing symmetry

## Abstract

Quantitative Cauchy stability for the six-independent-length determinant remainder.

Application in the original six coordinates. Take (r,a,b,o,c,d) with all six entries greater than one and use A=(a+c)/2, B=(b+d)/2, xi=(a-c)/2 and zeta=(b-d)/2. The original-to-character Gram correspondence identifies the original determinant with -L*M+Xi. Here t=xi^2+zeta^2 is nonnegative and C=ro-1+sqrt((A^2-B^2)^2+(r-o)^2) is positive. If L>0, M>0 and t<sqrt(C^2+L*M)-C, the envelope theorem gives a negative original determinant and hence strict bounds for all six original source cosines.

The same input gives a quantitative bound at every original edge. Write E=t^2+2*C*t. For any eps>0 with eps<L*M-E, let D_e1,D_e2 be the positive radicands belonging to that original edge. Its unchanged cosine satisfies 1-phi_e^2 >= (x_e^2-1)*eps/(D_e1*D_e2)>0. The parameter eps and the determinant estimate belong to this one shared six-coordinate input, and all six edge reindexings preserve its determinant.

On the one-deviation slice r=o>1, A=B=h>1 and zeta=0, C=r^2-1, Xi=2*(r^2-1)*xi^2+xi^4 and the radius is exactly (r+1)*(1+2*h-r). For r=49/10 and h=2 it is 59/100. More explicitly, the determinant of the original vector (49/10,2+xi,2,49/10,2-xi,2) is (xi^2-59/100)*(xi^2+4661/100), so it is negative exactly when xi^2<59/100 and zero exactly when xi^2=59/100. At xi=sqrt(59)/10 all six original coordinates remain greater than one and the determinant is zero. The radius controls the squared deviation t; its coordinate threshold is sqrt(59)/10. These conclusions concern the same original algebraic cosine data and retain the separate geometric-realization and global-gluing obligations.

For the six-independent-length character coordinates, let t be the squared Euclidean size of the two asymmetry coordinates. Let C be the center coefficient obtained by adding ro-1 to the Euclidean norm of (A squared minus B squared, r minus o).

**Theorem 1.1 (The asymmetry remainder has a quadratic-plus-quartic envelope).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; Xi\left(r, o, A, B, xi, zeta\right) \le asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.asymmetry_remainder_le_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic part of Xi is bounded by 2 C t through the two-dimensional Cauchy inequality, while the quartic part is at most t squared. This is the new estimate that controls both independent symmetry-breaking directions.

**Theorem 1.2 (The stability envelope forces a negative determinant).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right) < L\left(r, o, A, B\right) \cdot M\left(r, o, A, B\right) \Rightarrow det\left(gram\left(r, o, A, B, xi, zeta\right)\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.determinant_negative_of_stability_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever the envelope t squared plus 2 C t is strictly below the product L M, the exact determinant remainder identity gives a negative Gram determinant. The implication only uses that strict bound; positive-length and geometric realization conditions remain separate hypotheses of the surrounding model.

**Theorem 1.3 (The strict envelope is equivalent to a square-root radius).**

$$\forall r \in Real, o \in Real, A \in Real, B \in Real, xi \in Real, zeta \in Real,\; 0 < L\left(r, o, A, B\right) \Rightarrow \left(0 < M\left(r, o, A, B\right) \Rightarrow \left(0 < stabilityCoefficient\left(r, o, A, B\right) \Rightarrow \left(asymmetrySize\left(xi, zeta\right) < stabilityRadius\left(r, o, A, B\right) \Leftrightarrow asymmetrySize\left(xi, zeta\right)^{2} + 2 \cdot stabilityCoefficient\left(r, o, A, B\right) \cdot asymmetrySize\left(xi, zeta\right) < L\left(r, o, A, B\right) \cdot M\left(r, o, A, B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.stability_bound_iff_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When L and M are positive and C is positive, the strict quadratic-plus-quartic bound is equivalent to t being below sqrt(C squared plus L M) minus C. This is a sufficient radius for the six-length determinant criterion, not a claim that the radius is a maximal geometric ball.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.asymmetry_remainder_le_envelope`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.determinant_negative_of_stability_bound`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.stability_bound_iff_radius`
- Dependency: [D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder](SixIndependentLengthRemainder.md)
