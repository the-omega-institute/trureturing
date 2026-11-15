# The critical arithmetic envelope from the complete zero strip

## Abstract

A uniform actual zero strip gives the critical arithmetic Mertens envelope.

**Theorem 1.1 (The full-strip power and logarithm estimate).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.actual_B_critical_strip_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.actual_B_critical_strip_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha with 0<alpha<=1/2, assume that every complex rho satisfying ZeroSum.IsNontrivialZero has Re(rho)<=1-alpha. There exist real C,T with 0<=C and exp(1)<=T such that, for every real x>=T, abs(RHSharpArithmeticEnvelope.B(x))<=C/(x^alpha*log(x)). Here B(x)=Mertens.E₃(x)+log(log(Chebyshev.theta(x)))-log(log(x)) is the canonical actual arithmetic function. The endpoint alpha=1/2 is included. The strip is a hypothesis; its existence and RH are not conclusions.

Write actualH(y) as the complete series of actualCoeff(k)*exp(y*actualZero(k)), with each analytic multiplicity represented by its occurrences. Absolute coefficient mass and the strip give norm(actualH(y))<=coeffMass*exp((1-alpha)*y) for y>=0. The actual integrated explicit formula, its bounded trivial-zero correction, and ZeroAbscissaPower.primitive_eq_negative_tail give abs(Q(exp(y)))<=C0*exp(-alpha*y) for y>=log(2). No zero truncation or attained extremal zero is used.

Use WeightedTailTransport.transport_exp and r_exp with R(y)=(y+1)/y² and W(y)=(y+2)/y³. The exact identity is Jpsi(exp(y))=R(y)*Q(exp(y))-integral_(v>y) W(v)*Q(exp(v)). Positivity of W, monotonicity of exp(-alpha*v), and CountableResolvent.W_tail bound the integral by C0*exp(-alpha*y)*R(y). Since R(y)<=2/y for y>=1, abs(Jpsi(x))<=4*C0/(x^alpha*log(x)). This retains the logarithmic denominator at the exact exponent alpha. The unconditional psi-theta square-root estimate, MellinWeightedVariation.weight_nonneg and RHSharpArithmeticEnvelope.A_data give abs(S(x))<=4*abs(H)/(x^alpha*log(x)); A_data already supplies both integrability and the upper bound 2/(sqrt(x)*log(x)) for the square-root weight tail.

The strip bounds zeroAbscissa by 1-alpha. Apply actual_zero_abscissa_power_bound with beta=1-alpha/2 and positive epsilon=beta-zeroAbscissa, then transfer the psi rate to theta using the unconditional square-root gap. The prime number limits give theta(x)>=x/2 eventually. The scaled log-log tangent-gap stability theorem therefore gives abs(N(x))<=8*((theta(x)-x)/x)²/log(x). Squaring the beta rate uses exactly 2*beta-2=-alpha and yields 8*K²/(x^alpha*log(x)). Finally finite_cancellation bounds abs(E₃(x)+E₂p(x)) by 4/x, which is eventually at most 4/(x^alpha*log(x)). The original tails identity B=Jpsi-S+(E₃+E₂p)+N combines these bounds with C=4*C0+4*abs(H)+4+8*K² and one common real threshold.

The argument uses the classical integrated explicit formula and Abel summation. The Mertens suppliers retain the PrimeNumberTheoremAnd contributors' Apache-2.0 notice, the IEANTN/Mertens.lean source at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01, and the attribution to Leo Goldmakher, A quick proof of Mertens' theorem; the supplying notice and license are preserved at Library/notes/pntplus2026mertens.md. No literature-priority claim is made.

**Theorem 1.2 (The actual quadratic log-log remainder).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.nonlinear_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.nonlinear_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x with exp(2)<=x and x/2<=Chebyshev.theta(x), the original nonlinear estimate is abs(RHSharpArithmeticEnvelope.N(x)) <=8*((Chebyshev.theta(x)-x)/x)²/log(x). It applies the existing scaled log-log tangent-gap stability theorem. Its statement and proof are reused directly by the same-point theta-tail maximum argument; no zero-strip hypothesis is needed for this quadratic estimate.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.actual_B_critical_strip_envelope`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope.nonlinear_quadratic`
- Dependency: [D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvatureStability](LogLogGlobalCurvatureStability.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](../../../Weil/Mertens/IntegratedExplicit/WholeFormula.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../Weil/Mertens/ZeroAbscissaPower.md)
