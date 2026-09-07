# Linear Factors for the Pochhammer Operator

## Abstract

For every positive parameter, a normalized linear factor preserves the closed real-root interval of the Pochhammer image.

**Theorem 1.1 (The operator identity on each falling basis element).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor_on_falling`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor_on_falling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write D_k=X(X-1)...(X-k+1) and A_k=(a)_k. The frozen operator definition gives L_a(D_k)=A_k X^k. The recurrences X D_k=D_(k+1)+k D_k and A_(k+1)=A_k(a+k) show that both sides of V7.0 equal A_k[(1+k/a)X^(k+1)+(t+k/a)X^k]. The constant basis element is included.

**Theorem 1.2 (V7.0 for every real polynomial).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Q=L_a(P), the image L_a((X/a+t)P) is (X+t)Q+X(1+X)Q'/a. Mathlib's polynomial-sequence span theorem and linearity extend the basis identity to all polynomials. This identity requires a>0 but imposes no restriction on t.

**Theorem 1.3 (The differential expression preserves the closed interval).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.differential_preserves_unit_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/LinearFactor.differential_preserves_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and 0<=t<=1, the expression (X+t)Q+X(1+X)Q'/a has all complex roots in the real interval [-1,0] whenever Q does. At a root away from Q and the endpoints, Mathlib's logarithmic derivative identity gives a*t/z+a*(1-t)/(z+1)+sum_r 1/(z-r)=0. Real linear functionals separate every point outside [-1,0] from this nonnegative weighted sum. Multiplicities are retained; zero polynomials and endpoint roots are handled separately.

**Theorem 1.4 (Open Problem 1.9 with a normalized linear factor).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.linear_factor_preserves_unit_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/LinearFactor.linear_factor_preserves_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>0, 0<=t<=1 and real polynomial P whose Pochhammer image has all roots in [-1,0], the same holds after multiplying P by X/a+t. This resolves the registered linear-factor case of Vishnyakova's Open Problem 1.9 in arXiv:2608.03723. The unrestricted two-factor question is outside this theorem.

## References

- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.differential_preserves_unit_interval`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.lOp_linear_factor_on_falling`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/LinearFactor.linear_factor_preserves_unit_interval`
- Dependency: [D5/S3/Zeros/PochhammerDeformation/QuadraticInterval](QuadraticInterval.md)
