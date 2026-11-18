# Finite Original Gaussian Candidate Modes

## Abstract

Finite Original Gaussian Candidate Modes

The actual positive source amplitude has finite support for every complex parameter: a(p,r)=sum n<=p centralWeight(n)*(-1)^n*choose(p,n)*r^n. Derivatives of a, the two denominator tables, and their finite convolutions use only finite sums. No parameter derivative is exchanged with an infinite sum over external modes.

The ++ candidate is t(p,q,r)=P(p,q,r)-k(r)*a(p,r)*a(q,r), composed with r=z squared. P contains both the r/2 convolution term and the direct r squared inverse-square contribution. The logarithmic period factor k=r*(1-r)*Fprime/F uses the literal original period and its existing Picard-Fuchs equation.

These are concrete finite mode functions with derivatives and analyticity on the unit disk. The literal finite tables now satisfy E*h=delta00, E*h2=h and their finite derivative and Euler recurrences. Their actual finite convolutions satisfy E*G=A and E*J=G. The complete P denominator equation is proved; the asymmetric polynomial Euler stencil, candidate signed-frequency differential equations, signed source extension, all J modes, and full identification with original externalT remain separate obligations. The actual negative-zero row against any positive mode is identified with an explicit finite source formula; this does not yet verify its equality to the independently defined all-sign rational candidate. The guarded shift11 is only a Taylor monomial shift; it never replaces the signed predecessor true,0 by zero.

**Theorem 1.1 (sourceDerivativeConvolution_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceDerivativeConvolution_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceDerivativeConvolution_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite convolution Q_H=sum a(i)*r*aPrime(j)*H(p-i,q-j) satisfies 2*(Q_H-(1-r)*Y*Q_H)=-r*Y*L_H for every coefficient table H and all indices, including q=0. A finite reindexing applies the source derivative recurrence term by term. This supplies the source cancellation required by the still-open asymmetric polynomial Euler stencil; it asserts no original/candidate equality.

**Theorem 1.2 (a_derivative_mode_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_derivative_mode_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_derivative_mode_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite source derivative satisfies 2*(aPrime(p+1)-(1-r)*aPrime(p))=-a(p) for every complex r. The proof combines Pascal differences with the existing centralWeight_step ratio; there is no division by r.

**Theorem 1.3 (h_pascal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_pascal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_pascal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two Pascal differences of the literal finite binomial table give r*h(p,q). The proof pads finite ranges only with vanishing binomial terms and shifts the summation index.

**Theorem 1.4 (h_euler_mode_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_euler_mode_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_euler_mode_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite table satisfies r*hPrime(p+1,q)=(p+1)*(h(p+1,q)-h(p,q)), including q=0.

**Theorem 1.5 (hPrime_succ_succ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_succ_succ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_succ_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the literal h finite sum at successor indices equals the actual h2 table, by a finite index shift.

**Theorem 1.6 (h_inverse_stencil).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_inverse_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_inverse_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The guarded polynomial operator E=1-X-Y+(1-r)*XY sends h to the single coefficient at (0,0). Both axes are proved explicitly, and X,Y are only Taylor coefficient shifts.

**Theorem 1.7 (hPrime_eq_shift11).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_eq_shift11`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_eq_shift11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite derivative hPrime is the guarded XY shift of h2, including zero derivative along each axis. This helper is consumed in the h2 Euler recurrence.

**Theorem 1.8 (h2_inverse_stencil).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_inverse_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_inverse_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same operator E sends the actual finite h2 table to h. The interior follows by differentiating a finite Pascal identity, and each axis is proved separately.

**Theorem 1.9 (L_h_inverse_stencil).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h_inverse_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h_inverse_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal finite rectangular convolution G=L_h satisfies E*G=a(p)*a(q). Guarded shifts pass through the actual finite convolution; the impulse selects precisely the original source coefficients.

**Theorem 1.10 (L_h2_inverse_stencil).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h2_inverse_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h2_inverse_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal finite rectangular convolution J=L_h2 satisfies E*J=G. This is consumed by the complete polynomial denominator equation.

**Theorem 1.11 (h2_euler_mode_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_euler_mode_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_euler_mode_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-denominator coefficients satisfy r*h2Prime(p+1,q)=(p+1)*h2(p+1,q)-(p+2)*h2(p,q), obtained by differentiating the finite h Euler recurrence.

**Theorem 1.12 (P_inverse_stencil).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.P_inverse_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.P_inverse_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete polynomial part satisfies E*P=r/2*(A+(1-r)*XY*A)+r squared*XY*G. The r squared term is retained. This is a denominator equation only: the asymmetric Euler stencil and literal original/candidate germ equality remain unproved.

**Theorem 1.13 (a_euler_mode_step).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal finite source polynomials satisfy r*aPrime(p+1,r)=(p+1)*(a(p+1,r)-a(p,r)), for every natural p and complex r. Pascal and weighted binomial identities are combined after extending the lower polynomial by its zero top coefficient. This polynomial label factor differs from the signed half-frequency.

**Theorem 1.14 (externalT_negative_zero_positive_finite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<r<1 and every positive mode p, the actual full externalT(false,0,true,p,sqrt r) equals negativeZeroT(p,r). At p=0 this is -sqrt(1-r)*r*ell(r), and at successor p+1 it is sqrt(1-r)*((p+1)*(a(p+1,r)-a(p,r))-r*ell(r)*a(p+1,r)). The proof uses the actual original moment/jet boundary, finite source differentiation, the mode recurrence and the original period. It never sets this signed predecessor to zero.

**Theorem 1.15 (sourceAmplitude_true_finite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact support reduction of the actual positive source to a finite polynomial.

**Theorem 1.16 (hasDerivAt_L).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite double convolution satisfies the full product rule for any scalar differentiable denominator table.

**Theorem 1.17 (ell_picard_fuchs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing period equation yields the exact logarithmic equation without dividing by r or 1-r.

**Theorem 1.18 (hasDerivAt_k).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The period factor has derivative 1/4-r*(1-r)*ell squared throughout the unit disk, including zero.

**Theorem 1.19 (hasDerivAt_t).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete finite candidate has the stated derivative, retaining its full polynomial contribution.

**Theorem 1.20 (candidateT_analyticOnNhd).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each fixed positive mode candidate is analytic on the open unit disk in z.

**Theorem 1.21 (hasDerivAt_candidateT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The z derivative is the finite r derivative times 2z.

**Theorem 1.22 (candidateT_even).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit z-squared composition is even.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h2_inverse_stencil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.L_h_inverse_stencil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.P_inverse_stencil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_derivative_mode_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.a_euler_mode_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.candidateT_even`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.ell_picard_fuchs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_euler_mode_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h2_inverse_stencil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_eq_shift11`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hPrime_succ_succ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_euler_mode_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_inverse_stencil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.h_pascal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_L`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_k`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.hasDerivAt_t`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceAmplitude_true_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes.sourceDerivativeConvolution_step`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet](../OriginalGaussianExternalSourceJet.md)
