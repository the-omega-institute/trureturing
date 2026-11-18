# Normalized Positive Gaussian Kernel Candidates

## Abstract

Normalized Positive Gaussian Kernel Candidates

The explicit positive-sector formulas and finite rational identities come from the supplied Pro candidate construction, with independent exact algebra verification. Lean proofs differentiate the existing normalized source functions, use their actual squares to cancel the diagonal pole, and reuse the existing half-binomial Picard-Fuchs theorem. The algebra verification is advisory input; the declarations below carry the formal conclusions.

The source functions retain the original Gaussian normalization. The positive identification leaf proves equality of the actual positive J generating kernel with candidateJ on the full original source bidisk and identifies every positive T mode with its finite candidate throughout the complex unit disk. The companion PositiveT.GeneratorIdentification.positiveT_hasSum and positiveT_eq_candidateT prove rational positive T generator reconstruction with derived absolute convergence for real 0<r<1 and complex u,v satisfying norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, including both axes and the diagonal. Finite J mode extraction and other signed sectors remain later steps. The conditional parity uniqueness theorem is not used as an unconditional identification. These Gaussian results do not complete VOA, CFT, string theory or AdS/CFT.

**Theorem 1.1 (W_sum_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W_sum_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W_sum_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the original complex source bidisk, W(u,r)+W(v,r) is nonzero, including r=0 and the spatial diagonal. The unchanged proof uses the actual source square and zero-parameter normalization. This helper is consumed by positiveJ_eq_candidateJ in the positive identification leaf.

**Theorem 1.2 (candidateJ_joint_analytic).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing candidateJ is jointly complex analytic in its spatial coordinates under the original bidisk inequalities and nonzero W sum. Its unchanged proof composes the actual normalized source and rational factors. The positive J identification uses this helper to establish candidate regularity.

**Definition 1.3 (a).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.a`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor a(u,r)=1-(1-r)u.

**Definition 1.4 (b).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.b`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor b(u)=1-u.

**Definition 1.5 (E).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.E`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reflected-chart denominator E(u,v,r)=1-u-v+(1-r)uv.

**Definition 1.6 (W).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(u,r)=a(u,r) times the existing positive sourceMode. No square root is chosen independently of the normalized literal source series.

**Definition 1.7 (ell).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.ell`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic derivative of the existing complex half-binomial period. Its use in the differential equations is restricted to the open unit disk, where period_ne_zero applies.

**Definition 1.8 (correction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.correction`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.correction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common period correction r(1-r)ell(r). Its derivative is obtained from the existing picard_fuchs theorem and actual period nonvanishing.

**Definition 1.9 (rationalT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalT`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The regular rational T factor r(1+(1-r)uv)/(2E)+r squared uv/E squared.

**Definition 1.10 (rationalJ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The off-diagonal rational J factor [u b(v) a(u,r)+v b(u) a(v,r)]/[2(u-v) squared].

**Definition 1.11 (cauchy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.cauchy`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.cauchy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Cauchy subtraction (u+v)/[2(u-v) squared], used only off the diagonal when identifying the regular J expression.

**Definition 1.12 (candidateT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the two actual positive sourceMode functions times rationalT minus correction. The full T identity contribution is retained in the proposed formula; equality with the original full externalT is not assumed.

**Definition 1.13 (candidateJ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The regular expression M(u)M(v)[r/4-correction+r squared (u+v)/(4 b(u)b(v)(W(u)+W(v)) squared)]. It has no inverse external coordinate and no explicit diagonal denominator.

**Definition 1.14 (L).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.L`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive frequency operator L f(u)=u(1-u)f prime(u)+(1-3u)f(u)/2, with the normalization used in the original displacement equations.

**Theorem 1.15 (candidateT_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex u,v,r with norm(u)+norm(r)<1, norm(v)+norm(r)<1 and E nonzero, the actual T candidate satisfies both the frequency-difference and radial PDEs. Their source is the existing sourceMode product with modeA and modeH and the actual shiftedCentralDerivative/period ratio. Zero coordinates, u=v and r=0 remain in scope. The radial derivative is complex; real restriction supplies the radial parameter derivative. The proof differentiates the rational factor and source factors, uses both exact rational certificates, and consumes Picard-Fuchs through the derivative of correction.

**Theorem 1.16 (candidateJ_regular).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_regular`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two source-disk inequalities alone, the regular J expression is complex differentiable in either external coordinate, including u=v and zero coordinates. Off the diagonal it equals M(u)M(v)(rationalJ-correction)-cauchy. The cancellation follows from the actual sourceMode squares. Those squares also imply that a vanishing W sum at nonzero r would force u=v and then W=0, which contradicts its nonzero square. At r=0 the literal normalization gives W=1. Thus no W-sum hypothesis or independent root choice is needed.

**Theorem 1.17 (candidateJ_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two source-disk inequalities alone, the regular J candidate satisfies the positive frequency-sum PDE with the original modeA/modeH source and constant 1/4, including u=v and zero coordinates. Off the diagonal the proof consumes the rational J certificate and the Cauchy derivative identity. Joint analyticity makes both partial derivatives continuous, so their equation extends to the removable diagonal. The logarithmic derivative is the actual shiftedCentralDerivative/period ratio.

**Theorem 1.18 (candidateT_original_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_original_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_original_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<=r<1 and the original convergence inequalities norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, both T differential equations hold with the exact actual source factors and period ratio. No denominator condition, nonzero coordinate or diagonal exclusion is assumed. The proof establishes norm(r*u*v)<norm((1-u)(1-v)) from the two convergence inequalities, excluding E=0, and then consumes the general complex T verification. The radial term uses the real derivative of the candidate restricted to real r, matching the derivative type in the original radial_differential equation; HasDerivAt.comp_ofReal supplies this bridge. Equality with the original literal T is a separate open obligation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.E`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.L`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.W_sum_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.a`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.b`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateJ_regular`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.candidateT_original_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.cauchy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.correction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.ell`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate.rationalT`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore](OriginalGaussianExternalCandidateCore.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity](OriginalGaussianPeriodIdentity.md)
