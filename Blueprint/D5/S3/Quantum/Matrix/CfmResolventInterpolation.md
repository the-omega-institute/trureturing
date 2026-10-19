# A three-node resolvent estimate

## Abstract

Three spectral nodes control the two mixed resolvent products with constant 54.

**Theorem 1.1 (Uniform control of mixed resolvents).**

Lean statement: `D5/S3/Quantum/Matrix/CfmResolventInterpolation.mixed_resolvent_control`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CfmResolventInterpolation.mixed_resolvent_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a complex Hermitian 3 by 3 matrix with every eigenvalue below one, and put R_s=(sI−C)⁻¹. For any real linear observation L into a real seminormed space, the sum of the squared norms of L(R_2 R_4) and L(R_3 R_4) is at most 54 times the sum of the squared norms of L(R_2²), L(R_2 R_3), and L(R_3²).

Write y_i=3−λ_i>2 and d=∏(y_i+1). At each of the three spectral nodes, interpolation gives R_2 R_4=c_1 R_2²+c_2 R_2 R_3+c_3 R_3², where c_1=∏(y_i−1)/d, c_2=2(e_2−e_3)/d, and c_3=2e_3/d. The second mixed product has coefficients 2c_1, 2c_2−1, 2c_3. Their squared coefficient sums are bounded by 9 and 45. The continuous functional calculus lifts the spectral identities; a three-term Cauchy–Schwarz estimate gives 9+45=54. Distinct eigenvalues are not required.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CfmResolventInterpolation.mixed_resolvent_control`
