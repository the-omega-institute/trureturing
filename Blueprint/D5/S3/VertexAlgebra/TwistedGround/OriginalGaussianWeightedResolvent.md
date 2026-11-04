# Original Gaussian Weighted and Opposite Resolvent

## Abstract

Original Gaussian Weighted and Opposite Resolvent

Use the complex square-summable carrier and literal signed operator M from OriginalGaussianResolvent. For 0<r<1, put q=sqrt(r), b_s=centralBinom(s)/4^s, F=sum b_k^2*r^k, B=sum b_k*r^k=1/sqrt(1-r), and L_s=sum b_k*b_(k+s)*r^k. The original source is e_s=halfBinomial(s)*q^s/sqrt(s), its frequency weighting is w_s=s*e_s, and the signed column is U_s=(-1)^s*q^s*L_s/(sqrt(s)*F), with (1-M)U=e.

The frequency-weighted column d_s=s*U_s is proved square summable using the polynomial-geometric majorant sum s^2*r^s. The literal entries obey (s+t)*M_st=w_s*w_t, with the original halfBinomial signs. Every row sum is absolutely convergent before this identity is summed. Combining it with (1-M)U=e gives (1+M)d=(B/F)w=w/(sqrt(1-r)*F). This argument never applies a bounded frequency-diagonal operator.

Define Rplus as the operator-norm Neumann series sum (-M)^k on the same complex square-summable carrier. The actual estimate norm(M)<=norm(z)^2<1 supplies convergence and both inverse laws. Applying the inverse to the weighted equation gives Rplus*w=sqrt(1-r)*F*d. The finite symmetry t<->n-t gives sum_(t=0)^n t*b_t*b_(n-t)=n/2. The binomial recurrence yields sum n*b_n*r^n=r*B/(2*(1-r)). A nonnegative summable double-series majorant permits the Cauchy regrouping, giving w^T*d=r*B/(4*(1-r)*F), and hence w^T*Rplus*w=r/(4*(1-r)). Absolute convergence of the complex bilinear contraction is also proved directly by the square-summable pairing. The transpose notation is bilinear and introduces no conjugates.

This result concerns the original coefficient model and its actual infinite operator. It establishes no determinant or trace/differentiation passage, endpoint asymptotic, nome, occupation attribution, vertex-operator-algebra construction, fusion or anomaly statement, string theory, or AdS/CFT realization.

**Definition 1.1 (weightedColumn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<=r<1, this actual element of complex l2 has coordinate (n+1)*columnValue(r,n). Its membership proof uses the polynomial-geometric majorant, retaining the physical frequency n+1.

**Definition 1.2 (oppositeResolvent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.oppositeResolvent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.oppositeResolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total definition is sum_(k>=0) (-operator(z))^k. Its inverse interpretation uses norm(z)<1, established for z=sqrt(r) in the source-specific results.

**Theorem 1.3 (weightedColumn_equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn_equation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, (1+operator(sqrt(r))) applied to weightedColumn equals weightedSource multiplied by the complex scalar 1/(sqrt(1-r)*F(r)). This is the actual coordinate anticommutator consequence, with all row sums convergent.

**Theorem 1.4 (opposite_resolvent_weighted_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.opposite_resolvent_weighted_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.opposite_resolvent_weighted_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, the constructed opposite resolvent at sqrt(r) applied to weightedSource equals sqrt(1-r)*F(r) times weightedColumn. No inverse or source-action identity is supplied as a hypothesis.

**Theorem 1.5 (bilinear_opposite_resolvent_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.bilinear_opposite_resolvent_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.bilinear_opposite_resolvent_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, the series sum_(n>=0) weightedSource(n)*(oppositeResolvent(sqrt(r))*weightedSource)(n) converges absolutely and equals the complex embedding of r/(4*(1-r)). This scalar consumes the signed weighted column, the finite weighted convolution and the absolute double-series regrouping. It is a coefficient-model result, not a determinant or physical realization theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.bilinear_opposite_resolvent_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.oppositeResolvent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.opposite_resolvent_weighted_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent.weightedColumn_equation`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent](OriginalGaussianResolvent.md)
