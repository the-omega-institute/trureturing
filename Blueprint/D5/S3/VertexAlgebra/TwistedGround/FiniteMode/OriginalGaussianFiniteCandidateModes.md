# Finite Original Gaussian Candidate Modes

## Abstract

Finite Original Gaussian Candidate Modes

The actual positive source amplitude has finite support for every complex parameter: a(p,r)=sum n<=p centralWeight(n)*(-1)^n*choose(p,n)*r^n. Derivatives of a, the two denominator tables, and their finite convolutions use only finite sums. No parameter derivative is exchanged with an infinite sum over external modes.

The ++ candidate is t(p,q,r)=P(p,q,r)-k(r)*a(p,r)*a(q,r), composed with r=z squared. P contains both the r/2 convolution term and the direct r squared inverse-square contribution. The logarithmic period factor k=r*(1-r)*Fprime/F uses the literal original period and its existing Picard-Fuchs equation.

These are concrete finite mode functions with derivatives and analyticity on the unit disk. The inverse-table coefficient interpretation, candidate differential equations, signed source extension, all J modes, and full identification with original externalT remain separate obligations. The actual negative-zero row against any positive mode is identified with an explicit finite source formula; this does not yet verify its equality to the independently defined all-sign rational candidate. The guarded shift11 is only a Taylor monomial shift; it never replaces the signed predecessor true,0 by zero.

**Theorem 1.1 (a_euler_mode_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal finite source polynomials satisfy r*aPrime(p+1,r)=(p+1)*(a(p+1,r)-a(p,r)), for every natural p and complex r. Pascal and weighted binomial identities are combined after extending the lower polynomial by its zero top coefficient. This polynomial label factor differs from the signed half-frequency.

**Theorem 1.2 (externalT_negative_zero_positive_finite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<r<1 and every positive mode p, the actual full externalT(false,0,true,p,sqrt r) equals negativeZeroT(p,r). At p=0 this is -sqrt(1-r)*r*ell(r), and at successor p+1 it is sqrt(1-r)*((p+1)*(a(p+1,r)-a(p,r))-r*ell(r)*a(p+1,r)). The proof uses the actual original moment/jet boundary, finite source differentiation, the mode recurrence and the original period. It never sets this signed predecessor to zero.

**Theorem 1.3 (sourceAmplitude_true_finite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact support reduction of the actual positive source to a finite polynomial.

**Theorem 1.4 (hasDerivAt_L).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite double convolution satisfies the full product rule for any scalar differentiable denominator table.

**Theorem 1.5 (ell_picard_fuchs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing period equation yields the exact logarithmic equation without dividing by r or 1-r.

**Theorem 1.6 (hasDerivAt_k).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The period factor has derivative 1/4-r*(1-r)*ell squared throughout the unit disk, including zero.

**Theorem 1.7 (hasDerivAt_t).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete finite candidate has the stated derivative, retaining its full polynomial contribution.

**Theorem 1.8 (candidateT_analyticOnNhd).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each fixed positive mode candidate is analytic on the open unit disk in z.

**Theorem 1.9 (hasDerivAt_candidateT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The z derivative is the finite r derivative times 2z.

**Theorem 1.10 (candidateT_even).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit z-squared composition is even.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet](../OriginalGaussianExternalSourceJet.md)
