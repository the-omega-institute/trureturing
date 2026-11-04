# Measurable Joint Calibration

## Abstract

Integrable square remainders and absolute-continuity transport give quantitative comparison and rigidity for measurable reciprocal densities.

**Definition 1.1 (Smooth reference equations).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.Calibration`

*Formalization.* `D5/S3/Analytic/Variational/MeasurableJointCalibration.Calibration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real parameter b and real functions Z,Q,M,N, Calibration requires Z and M to be infinitely differentiable at every point of [0,1], Q continuous on that interval, Z'=Q, M'=N, Z>0, Q>0, M(r)=8bQ(r)/9+8rQ(r)^2/(9Z(r)), and N(r)=-8rQ(r)^3/(27Z(r)^2). These conditions apply to the reference, independently of the competitor. The remainder theorem uses these differential and algebraic equations rather than assuming a comparison or an equality characterization.

**Definition 1.2 (The reciprocal square defect).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.defect`

*Formalization.* `D5/S3/Analytic/Variational/MeasurableJointCalibration.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real functions u,U,Q, defect(u,U,Q,x)=u(x)[sqrt(x)/u(x)-(2/3)Q(U(x))]^2. The factor 2/3 converts the derivative of x sqrt(x) to the original reciprocal square-root coordinate.

**Definition 1.3 (The calibrated potential).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.potential`

*Formalization.* `D5/S3/Analytic/Variational/MeasurableJointCalibration.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real functions U,Z,M, potential(U,Z,M,x)=M(U(x))[x sqrt(x)-Z(U(x))/2]. Its endpoint difference is the comparison constant.

**Theorem 1.4 (Individual bounds imply reciprocal integrability).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.bounded_positive_integrability`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/MeasurableJointCalibration.bounded_positive_integrability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be a.e. measurable for volume restricted to [1,2]. Suppose there are real c,B with c>0 and c<=u(x)<=B a.e. Then u, x/u(x), and [integral from 1 to x of u]/u(x)^2 are interval integrable on [1,2]. The cumulative integral is continuous and bounded on this compact interval. The positive lower bound controls both reciprocal terms. The constants may depend on u; no common bounds or regularity of u are required.

**Theorem 1.5 (Global remainder and zero-energy transport).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/MeasurableJointCalibration.remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b be any real number and let Z,Q,M,N satisfy Calibration. Let u be a.e. measurable on [1,2] with its own positive lower and finite upper bounds. Let U be absolutely continuous on [1,2], map this interval into [0,1], have derivative u a.e., and satisfy U(1)=0. Suppose Z(0)=1 and the density L(x)=b x/u(x)+U(x)/u(x)^2 is interval integrable. Then the defect is interval integrable, its integral E is nonnegative, and potential(2)-potential(1)+bE<=integral L. If E=0, then sqrt(x)/u(x)=(2/3)Q(U(x)) a.e. and Z(U(x))=x sqrt(x) at every x in the entire closed interval [1,2]. There is no smoothness or inverse assumption on u or U. Nonnegative b is unnecessary for this calibrated estimate; positivity is used when an application infers E=0 from equality of cost.

The scalar cubic tangent gap is nonnegative by a two-case polynomial identity. Retaining the exact quadratic gap 4b(q-Q)^2/9 and substituting q=3 sqrt(x)/(2u(x)) gives precisely b times the original square defect after multiplication by u. Before comparing integrals, compact continuity of Q composed with U and the individual density bounds prove integrability. Smoothness makes Z and M Lipschitz on the compact range, so their compositions with U and the potential are absolutely continuous. The a.e. chain rule and the fundamental theorem of calculus integrate the calibrated inequality. Zero nonnegative integrable energy gives the reciprocal slope equation a.e.; the absolutely continuous function Z(U(x))-x sqrt(x) then has derivative zero a.e. and is constant. Its value at 1 is zero, including the endpoints in the resulting identity.

**Theorem 1.6 (Cumulative integrals respect null sets).**

Lean statement: `D5/S3/Analytic/Variational/MeasurableJointCalibration.primitive_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/MeasurableJointCalibration.primitive_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If real functions u and v agree a.e. for volume restricted to [1,2], their integrals from 1 to x agree for every x in [1,2]. Restrict the same a.e. identity to each initial interval. This preserves all null-set representatives when the calibration is applied to an optimizer.

## References

- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.Calibration`
- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.bounded_positive_integrability`
- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.defect`
- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.potential`
- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.primitive_congr`
- Truth anchor: `D5/S3/Analytic/Variational/MeasurableJointCalibration.remainder`
