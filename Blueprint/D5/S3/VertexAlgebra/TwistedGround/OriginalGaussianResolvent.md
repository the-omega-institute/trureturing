# Original Gaussian Operator and Signed Resolvent

## Abstract

Original Gaussian Operator and Signed Resolvent

The carrier is the complex square-summable sequence space, with coordinate n representing physical frequency n+1. The operator is the norm-summable series of rank-one maps with the literal OriginalGaussianMatrix.matrixEntry z (n+1) (m+1). Square cutoffs use Fin N, including the empty cutoff. Exact zero extension and restriction identify each cutoff with the existing finite Gaussian matrix; convergence in operator norm transfers its norm(z)^2 bound to the infinite operator on norm(z)<1.

Write b_s=centralBinom(s)/4^s and q=sqrt(r), where 0<r<1. The function F is the real restriction of OriginalHalfBinomialPeriod.period, and its series is sum b_k^2*r^k. Define L_s=sum b_k*b_(k+s)*r^k. The source e_s=halfBinomial(s)*q^s/sqrt(s), weighted source w_s=s*e_s, and candidate U_s=(-1)^s*q^s*L_s/(sqrt(s)*F) are all proved square summable. Frequency multiplication is used on these explicitly proved vectors, without asserting a bounded diagonal operator.

The existing positive half-binomial convolution, inverted by finite power-series multiplication, supplies the shifted finite convolution. Absolute convergence permits regrouping the actual double series. Keeping the t=0 boundary gives s*b_s*sum_(t>=1) b_t*r^t*L_t/(s+t)=L_s-b_s*F. The proved coordinate action then gives (1-M)U=e. The ordinary Neumann-series left inverse is applied only after the operator bound proves norm(M)<1.

The signed resolvent column is immediately consumed in a bilinear scalar contraction. Absolute convergence follows from the proved square-summable weighted source and the resolvent vector; a second absolute double-series regrouping reduces the scalar to (B-F)/F. The coefficient convolution gives B=sum b_k*r^k=1/sqrt(1-r). No complex conjugation occurs in this bilinear contraction.

These statements concern the original infinite coefficient operator and its signed resolvent column. They establish no determinant, trace/differentiation passage, endpoint asymptotic, vertex-operator-algebra construction, fusion or anomaly statement, string theory, or AdS/CFT realization.

**Theorem 1.1 (resolvent_column).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<r<1 and every n, the resolvent at sqrt(r) applied to the original source has coordinate (-1)^(n+1)*sqrt(r)^(n+1)*L_(n+1)/(sqrt(n+1)*F). The source-specific infinite residual is derived rather than assumed.

**Theorem 1.2 (bilinear_resolvent_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<r<1 the bilinear series sum_(s>=1) s*e_s*(R e)_s converges absolutely and one plus its sum equals 1/(sqrt(1-r)*F(r)).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialPeriod](../../Analytic/OriginalHalfBinomialPeriod.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix](OriginalGaussianMatrix.md)
