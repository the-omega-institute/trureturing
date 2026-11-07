# Unconditional integrated explicit formula

## Abstract

Unconditional integrated explicit formula

Positive-U composite application, with no new theorem identity. Let rho0 be an ACTUAL nontrivial zero: classicalZeta(rho0)=0 and 0<Re(rho0)<1. Assume beta=Re(rho0)>1/2 and gamma=Im(rho0)>0, and put delta=beta-1/2, D=gamma+10, m0=100*D^2/delta^2, m1=500*D^4/delta^2. The composite conclusion is existence of a real A in the CLOSED interval [exp(4*m0),exp(28*m1)] such that U(A)>sqrt(A)*(4*log(A)+9). These are its only mathematical premises. The complete formula alone asserts no positive peak: the finite power-sum selection, complete omitted-tail estimate and signed localization below are essential parts of this application of existing results.

Here U is literally CompleteMertensPeak.U: U(t)=t*sum(Lambda(n)/n,0<n<=floorNat(t))-Chebyshev.psi(t)-t*log(t)+(1+gammaE)*t, with Lambda=ArithmeticFunction.vonMangoldt and gammaE=Real.eulerMascheroniConstant. The upper endpoint is inclusive and every prime power remains. Write H(y)=sum_k exp(rho_k*y)/(rho_k*(1-rho_k)) over the exhaustive actual analytic occurrence family, retaining each multiplicity and both imaginary signs. actual_integrated_explicit_formula for y>0 gives exactly H(y)=U(exp(y))-log(2*pi)+trivialT(y), where trivialT(y)=sum_{j>=1} exp(-2*j*y)/(2*j*(2*j+1)). Its full correction satisfies trivialT(y)<=1-log(2)<log(2*pi), so Re(H(y))<=U(exp(y)). This uses the complete series correction, not a truncated identity.

The actual mass/height owner supplies gamma>10, 0<delta<1/2, D>20, the exact closed occurrence set S and its bound card(S)<=2*D^2. The ZeroPowerSum owner's application selects m in [m0,m1], m>=1, at which the real part of the full E=sum_k exp(m*((rho_k-i*gamma)^2+16*(rho_k-i*gamma))) is at least exp(a*m)/2, a=beta^2+16*beta. Its entire strict-complement tail has norm <=2*D^2*exp(-19*m), as derived there; this lower bound is not assumed. The ActualZeroLaplace owner supplies integral Re(H)*K=Re(E), |K|<=V, product integrability and the full envelope integral bound. The CountableGaussianQuadraticFourthMoment owner supplies the explicit central and BOTH exterior budgets from its second/fourth moments and pinned Gaussian identities.

Assume for contradiction that every A in [exp(4*m0),exp(28*m1)] fails the strict peak inequality. For each y in J=[4*m,28*m], monotonicity of exp gives exp(y) in that asserted closed interval and y>0. Therefore f(y)=Re(H(y))<=U(exp(y))<=sqrt(exp(y))*(4*log(exp(y))+9)=(4*y+9)*exp(y/2)<=b(y), with b(y)=(4*y+11)*exp(y/2)>=0. The constants nine in the conclusion and eleven in this majorant have distinct roles.

Retain the signed debit before absolute relaxation. On J, f*(K+V)<=b*(K+V)<=2*b*V; on J-complement, f*(K+V)<=|f|*(K+V)<=2*|f|*V. Integrability permits indicator decomposition and subtraction of the WHOLE integral f*V, giving Re(E)<=2*integral_J b*V+2*integral_{J-complement}|f|*V-integral_R f*V. Decompose J-complement exactly into its nonnegative exterior and the entire negative axis. With the budgets derived in the existing owners, the right side is <=600*m*D^2*exp(33*m/4)+24*D^2*exp(9*m/2)+16*D^2*exp(-32*m)+1000*D^2*exp(-83*m). Since m>=1, every smaller exponent is absorbed in m*D^2*exp(33*m/4); 600+24+16+1000=1640<2000 gives Re(E)<=2000*m*D^2*exp(33*m/4). No sign or complement term has been discarded.

Finally a=33/4+17*delta+delta^2. The lower time bound says 100*D^2<=m*delta^2. The second Taylor term of exp, (17*delta*m)^2/2<=exp(17*delta*m), then gives 4000*m*D^2<(17*delta*m)^2/2<=exp(17*delta*m). Multiplying by exp(33*m/4) and using delta^2*m>=0 yields 4000*m*D^2*exp(33*m/4)<exp(a*m). This contradicts exp(a*m)/2<=Re(E)<=2000*m*D^2*exp(33*m/4), completing the existential with the original 100/500/4/28 constants and both closed endpoints. This is an exposition of the composite reuse derivation, with no named binding wrapper, new Describe or first freeze. It supplies neither an actual off-critical zero nor an unconditional integer witness; the separate quantitative arithmetic application and its additional all-real hypothesis are stated in CompleteMertensPeak.

For every real y>0, the complete actual zero occurrence series equals U(exp(y))-log(2*pi) plus the full trivial zero correction. The residual is literally zero on y<=0 and damped by exp(-2*y) on y>0. Its L1 Fourier transform vanishes at nonzero frequencies by the actual Laplace suppliers. Continuity of that transform gives frequency zero without applying the digamma series at integer one. Pointwise inversion uses continuity only at the requested positive y. This formula makes no RH, Robin positivity or positive U peak claim. Integer 5040, all integer endpoints N>=2, every prime-power endpoint and the literal exponential-over-denominator form are checked only by transient anonymous applications.

**Theorem 1.1 (explicitDiscrepancy line integrable).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{IntegrableOn}\left((\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{explicitDiscrepancy}\left(\mathit{x1}\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitDiscrepancy_line_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.2 (explicitDiscrepancy line zero).**

$$\forall x0 \in \mathrm{Real},\; \mathit{x0} \ne 0 \Rightarrow \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x2}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{explicitDiscrepancy}\left(\mathit{x2}\right))\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitDiscrepancy_line_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.3 (explicitFourierResidual integrable).**

$$\mathrm{Integrable}\left(\mathrm{explicitFourierResidual}, \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.4 (explicitFourierResidual continuousAt).**

$$\forall x0 \in \mathrm{Real},\; 0 < \mathit{x0} \Rightarrow \mathrm{ContinuousAt}\left(\mathrm{explicitFourierResidual}, \mathit{x0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_continuousAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.5 (explicitFourierResidual fourier).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{fourier}\left(\mathrm{explicitFourierResidual}, \mathit{x0}\right) = \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{explicitDiscrepancy}\left(\mathit{x1}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.6 (explicitFourierResidual fourier zero).**

$$\mathrm{fourier}\left(\mathrm{explicitFourierResidual}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_fourier_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.7 (actual integrated explicit formula).**

$$\forall x0 \in \mathrm{Real},\; 0 < \mathit{x0} \Rightarrow \mathrm{actualH}\left(\mathit{x0}\right) = \mathrm{ofReal}\left(\mathrm{U}\left(\mathrm{exp}\left(\mathit{x0}\right)\right) - \mathrm{log}\left(2 \cdot \mathrm{pi}\right) + \mathrm{trivialT}\left(\mathit{x0}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.actual_integrated_explicit_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.actual_integrated_explicit_formula`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitDiscrepancy_line_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitDiscrepancy_line_zero`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_continuousAt`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_fourier`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_fourier_zero`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula.explicitFourierResidual_integrable`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace](CompleteMangoldtLaplace.md)
