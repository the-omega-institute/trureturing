# Closed rectangle estimate for the coupled cubic residual

## Abstract

An exact endpoint certificate controls the cubic residual on a closed rectangle.

**Definition 1.1 (Mean excess).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.e`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t, e(t)=(1-t)^2(2t^2+t+2)/(3(1+t^2)). In the normalization X=diag(1,t^2), this is the cubic divided-difference mean minus t.

**Definition 1.2 (Off-diagonal penalty).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.beta`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set beta(t)=2(1-t^2)^2(1+3t^2+t^4)/(9(1+t^2)). The real denominator is positive for every t.

**Definition 1.3 (The completed-square term).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.T`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t,y, put T(t,y)=4e(t)ty+e(t)^2y^2.

**Definition 1.4 (The remaining cubic residual).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.J`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set J(t,y)=2(1-2t^2)T(t,y)+beta(t)y^2-(9/4)T(t,y)^2. This is the residual obtained after completing the square in the trace variable of the two-dimensional coupling estimate.

**Theorem 1.5 (Nonnegativity on the full closed rectangle).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.rectangular_J_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.rectangular_J_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real t,y with t>=0, 2t^2<=1, y>=0 and y^2<=2, one has J(t,y)>=0. At y=sqrt(2), clearing the positive denominator yields a degree-14 Bernstein expansion in q=sqrt(2)t. Its coefficients are A+B sqrt(2), with B>=0 and A+(24/17)B>=0. The exact identity and all coefficient signs are checked in Lean; no sampled numerical premise is used. For the interior of the y interval, J(t,y)=y g(y), where g is a cubic with nonpositive quadratic and cubic coefficients. An explicit positive factorization of its difference from the endpoint chord proves g(y)>=0. Both boundary values t=0 and 2t^2=1, and y=0, are included without dividing by y.

This is a scalar supplier for the complex Hermitian two-by-two cubic coupling estimate studied in connection with the He-Saunderson-Fawzi sandwiched Renyi compatibility question, arXiv:2502.05627v1, Conjecture 6.2, and DOI 10.1007/s10107-025-02314-0, Conjecture 1. It does not settle arbitrary dimension, general base Y, other exponents, or the complete HSF conjecture. No literature novelty or official acceptance is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.J`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.T`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.beta`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.e`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.rectangular_J_nonneg`
