# Original Gaussian Operator, Resolvent Moments and Determinant Limit

## Abstract

Original Gaussian Operator, Resolvent Moments and Determinant Limit

The carrier is the complex square-summable sequence space, with coordinate n representing physical frequency n+1. The operator is the norm-summable series of rank-one maps with the literal OriginalGaussianMatrix.matrixEntry z (n+1) (m+1). Square cutoffs use Fin N, including the empty cutoff. Exact zero extension and restriction identify each cutoff with the existing finite Gaussian matrix; convergence in operator norm transfers its norm(z)^2 bound to the infinite operator on norm(z)<1.

Write b_s=centralBinom(s)/4^s and q=sqrt(r), where 0<r<1. The function F is the real restriction of OriginalHalfBinomialPeriod.period, and its series is sum b_k^2*r^k. Define L_s=sum b_k*b_(k+s)*r^k. The source e_s=halfBinomial(s)*q^s/sqrt(s), weighted source w_s=s*e_s, and candidate U_s=(-1)^s*q^s*L_s/(sqrt(s)*F) are all proved square summable. Frequency multiplication is used on these explicitly proved vectors, without asserting a bounded diagonal operator.

The existing positive half-binomial convolution, inverted by finite power-series multiplication, supplies the shifted finite convolution. Absolute convergence permits regrouping the actual double series. Keeping the t=0 boundary gives s*b_s*sum_(t>=1) b_t*r^t*L_t/(s+t)=L_s-b_s*F. The proved coordinate action then gives (1-M)U=e. The ordinary Neumann-series left inverse is applied only after the operator bound proves norm(M)<1.

The signed resolvent column is immediately consumed in a bilinear scalar contraction. Absolute convergence follows from the proved square-summable weighted source and the resolvent vector; a second absolute double-series regrouping reduces the scalar to (B-F)/F. The coefficient convolution gives B=sum b_k*r^k=1/sqrt(1-r). No complex conjugation occurs in this bilinear contraction.

The frequency-weighted column d_s=s*U_s is proved square summable using the polynomial-geometric majorant sum s^2*r^s. The literal entries obey (s+t)*M_st=w_s*w_t, with the original halfBinomial signs. Every row sum is absolutely convergent before this identity is summed. Combining it with (1-M)U=e gives (1+M)d=(B/F)w=w/(sqrt(1-r)*F). This argument never applies a bounded frequency-diagonal operator.

Define Rplus as the operator-norm Neumann series sum (-M)^k on the same complex square-summable carrier. The actual estimate norm(M)<=norm(z)^2<1 supplies convergence and both inverse laws. Applying the inverse to the weighted equation gives Rplus*w=sqrt(1-r)*F*d. The finite symmetry t<->n-t gives sum_(t=0)^n t*b_t*b_(n-t)=n/2. The binomial recurrence yields sum n*b_n*r^n=r*B/(2*(1-r)). A nonnegative summable double-series majorant permits the Cauchy regrouping, giving w^T*d=r*B/(4*(1-r)*F), and hence w^T*Rplus*w=r/(4*(1-r)). Absolute convergence of the complex bilinear contraction is also proved directly by the square-summable pairing. The transpose notation is bilinear and introduces no conjugates.

This result concerns the original coefficient model and its actual infinite operator. The determinant constructed below uses this same coefficient model. The trace differentiation passage, endpoint asymptotic, nome, occupation attribution, vertex-operator-algebra construction, fusion or anomaly statement, string theory, and AdS/CFT realization remain outside these results.

The closed-cycle logarithm uses the actual signed entries at positive frequencies, with even walk length 2*(k+1) and divisor k+1. Absolute values are taken on each edge before summing internal vertices. At the negative real radius, the original signs cancel and realize these absolute walks by the same original operator. Its norm bound and a summable geometric coordinate majorant control all cycle lengths. The determinant gaussianDet is the exponential of this absolutely convergent cycle logarithm.

The finite logarithm uses traces of powers of the literal finiteSection N z. Exact zero extension identifies these powers with sectionOp powers, and dominated convergence first passes the spatial cutoff through the coordinate trace, then through the cycle-length series. For real z, one Hermitian spectral eigenbasis works simultaneously for all powers. The actual spectral norm bound and the scalar logarithm series give det(1-(finiteSection N z)^2)=exp(finiteLog N z), including N=0. Polynomial finite entries and a local summable series majorant prove finite-log holomorphy; the identity theorem extends this equality to every complex z with norm(z)<1. Consequently the literal finite determinants converge pointwise to gaussianDet. The square is taken after cutoff.

Uniform spatial cutoff convergence and holomorphy of the infinite logarithm and determinant, identification with a period expression, and physical or string-theoretic realization are not asserted. The spectral and analytic ingredients are classical; these results are the source-specific composition for the original signed kernel.

**Definition 1.1 (gaussianLogDet).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianLogDet`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianLogDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minus the sum of the actual even closed-cycle traces divided by k+1. On norm(z)<1 the series converges absolutely.

**Definition 1.2 (gaussianDet).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianDet`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex exponential of gaussianLogDet. The cutoff theorem identifies it with the limit of the actual finite Gaussian determinants.

**Definition 1.3 (finiteLog).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finiteLog`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finiteLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minus the sum of tr((finiteSection N z)^(2*(k+1)))/(k+1). The powers use the matrix cut off before multiplication; the length-series majorant is independent of N.

**Theorem 1.4 (finite_determinant_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cutoff N and complex norm(z)<1, the determinant of 1-(finiteSection N z)^2 equals exp(finiteLog N z). This includes the empty determinant and arbitrary complex phases; Hermitian diagonalization is used only on the real slice.

**Theorem 1.5 (finite_determinants_tendsto).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinants_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinants_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex point of the open unit disk, det(1-(finiteSection N z)^2) tends to gaussianDet z as N tends to infinity. This is pointwise spatial cutoff convergence, with no period identity or physical realization premise.

**Theorem 1.6 (resolvent_column).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<r<1 and every n, the resolvent at sqrt(r) applied to the original source has coordinate (-1)^(n+1)*sqrt(r)^(n+1)*L_(n+1)/(sqrt(n+1)*F). The source-specific infinite residual is derived rather than assumed.

**Theorem 1.7 (bilinear_resolvent_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<r<1 the bilinear series sum_(s>=1) s*e_s*(R e)_s converges absolutely and one plus its sum equals 1/(sqrt(1-r)*F(r)).

**Definition 1.8 (weightedColumn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<=r<1, this actual element of complex l2 has coordinate (n+1)*columnValue(r,n). Its membership proof uses the polynomial-geometric majorant, retaining the physical frequency n+1.

**Definition 1.9 (oppositeResolvent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.oppositeResolvent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.oppositeResolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total definition is sum_(k>=0) (-operator(z))^k. Its inverse interpretation uses norm(z)<1, established for z=sqrt(r) in the source-specific results.

**Theorem 1.10 (weightedColumn_equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn_equation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, (1+operator(sqrt(r))) applied to weightedColumn equals weightedSource multiplied by the complex scalar 1/(sqrt(1-r)*F(r)). This is the actual coordinate anticommutator consequence, with all row sums convergent.

**Theorem 1.11 (opposite_resolvent_weighted_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.opposite_resolvent_weighted_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.opposite_resolvent_weighted_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, the constructed opposite resolvent at sqrt(r) applied to weightedSource equals sqrt(1-r)*F(r) times weightedColumn. No inverse or source-action identity is supplied as a hypothesis.

**Theorem 1.12 (bilinear_opposite_resolvent_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_opposite_resolvent_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_opposite_resolvent_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, the series sum_(n>=0) weightedSource(n)*(oppositeResolvent(sqrt(r))*weightedSource)(n) converges absolutely and equals the complex embedding of r/(4*(1-r)). This scalar consumes the signed weighted column, the finite weighted convolution and the absolute double-series regrouping. It is a coefficient-model result, not a determinant or physical realization theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_opposite_resolvent_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finiteLog`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinant_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.finite_determinants_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianDet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.gaussianLogDet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.oppositeResolvent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.opposite_resolvent_weighted_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn_equation`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialPeriod](../../Analytic/OriginalHalfBinomialPeriod.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix](OriginalGaussianMatrix.md)
