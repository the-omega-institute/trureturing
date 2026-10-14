# The full moving primal theta tail

## Abstract

The full moving primal theta tail.

**Theorem 1.1 (A uniform budget relative to the actual origin flux).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalPrimalTailProjection.original_primal_tail_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/OriginalPrimalTailProjection.original_primal_tail_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put A_m=pi*m^2 and q_m(x)=exp(x/2)*exp(-A_m*exp(2*x))*(4*A_m^2*exp(4*x)-6*A_m*exp(2*x)). The full omitted tail is Q_N(x)=sum over j>=0 of q_(N+j+1)(x). Its origin flux is the full sum of exp(-A_m)*(8*A_m^3-30*A_m^2+15*A_m) over m>N. For every a > 0, one positive constant C works for every integer N >= 1 and every adjoint parameter 0 <= alpha <= a. The tail contains all primal modes m > N, with their original scale pi*m^2. Its actual origin flux is positive and equals minus its derivative at zero. The tail is four times continuously differentiable. The sum of the absolute origin derivative of its density adjoint and the weighted integral of the absolute value of its second density adjoint is at most C*(N+1)^4 times that flux. The weighted absolute value is integrable; its weight is exp(a*x^2/2) on the positive half-line.

The density adjoint is A_alpha(f)=f''+alpha*(f+x*f'). The derivative polynomials obey P_0(y)=4*y^2-6*y and P_(r+1)(y)=(1/2-2*y)*P_r(y)+2*y*P_r'(y). Compact Gaussian majorants justify differentiation of the full series. For L=2*r+9/2+p, the endpoint constant is exp(L+(a/2+L)^2/16). A quartic lower bound for exp(2*x) pays this constant while preserving exp(-pi*m^2). The complete shifted polynomial-geometric series bounds every omitted mode; comparison with the positive first flux term gives the fourth-power cutoff budget. No tail-norm or polynomial-energy assumption enters the result.

This is the analytic norm component of the moving primal projection. It does not assert the original B projection estimate or the nodal head debit. Those require the original finite B differential equation and energy, two one-sided adjoint integrations including their infinity brackets, and the exact full-source moment and head bridges. The original RH, source coupling, cofactor and multiplicity obligations remain outside this statement.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/OriginalPrimalTailProjection.original_primal_tail_budget`
- Dependency: [D5/S3/Analytic/Fourier/ThetaDifferentialKernel](../../Analytic/Fourier/ThetaDifferentialKernel.md)
