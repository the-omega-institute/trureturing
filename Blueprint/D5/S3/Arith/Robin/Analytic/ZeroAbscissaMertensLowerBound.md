# Transport from the actual zero abscissa to the Mertens error

## Abstract

The unconditional lower power envelope of the actual arithmetic B

**Theorem 1.1 (Every positive exponent margin on all sufficiently large real endpoints).**

$$\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists C \in \mathbb{R},\; \exists T \in \mathbb{R},\; 0 \le C \land \left(2 \le T \land \left(\forall x \in \mathbb{R},\; T \le x \Rightarrow -C \cdot x^{Theta - 1 + epsilon} \le \operatorname{B}\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroAbscissaMertensLowerBound.actual_B_zero_abscissa_lower_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Theta=KappaGap.zeroAbscissa, the supremum of the real parts of the actual nontrivial zeta zeros, and B=RHSharpArithmeticEnvelope.B. Thus B(x)=Mertens.E₃(x)+log(log(Chebyshev.theta(x)))-log(log(x)). For every real epsilon>0 there are real constants C>=0 and T>=2 such that -C*x^(Theta-1+epsilon)<=B(x) for every real x>=T. The constants may depend on epsilon. There is no Riemann Hypothesis assumption, and the supremum need not be attained.

The prime number theorem gives theta(x)/x->1, hence eventually x/2<=theta(x)<=3*x/2. The identity log(log(theta(x)))-log(log(x))=log(1+log(theta(x)/x)/log(x)) then proves that this difference tends to zero. Mertens.E₃.bound' also gives E₃(x)->0, so B(x)->0. If Theta-1+epsilon>=0, the eventual bound B(x)>=-1 and x^(Theta-1+epsilon)>=1 prove the conclusion with C=1.

Otherwise set beta=Theta+epsilon/2. The RH/right-strip dichotomy and the existence of a nontrivial zero give Theta>=1/2, so 1/2<beta<1. ZeroAbscissaPower.actual_zero_abscissa_power_bound supplies the unconditional actual psi estimate at exponent beta. ZeroFreeStripMertensEnvelope.theta_power_bound uses the public Chebyshev bound psi(x)-theta(x)<=H*sqrt(x) to transfer it to abs(theta(x)-x)<=K*x^beta on a sufficiently large real tail, with K>=0.

Put w(t)=(log(t)+1)/(t^2*log(t)^2), Jtheta(x)=integral_(t>x)(theta(t)-t)*w(t), and N(x)=log(log(theta(x)))-log(log(x))-(theta(x)-x)/(x*log(x)). ThetaTailRobinWitness.theta_tail_mertens_robin gives integrability and the exact decomposition B=Jtheta+(E₃+E₂p)+N for every x>=2. For t>=exp(1), 0<=w(t)<=2/t^2. Integration of the power majorant gives abs(Jtheta(x))<=(2*K/(1-beta))*x^(beta-1). This uses the actual infinite Lebesgue tail, without differentiating theta or assuming cancellation of zero phases.

Strict log-log tangency in both directions, with y>=x/2 and x>=4, yields abs(log(log(y))-log(log(x)))<=4*abs(y-x)/(x*log(x)). Consequently N(x)>=-5*K*x^(beta-1) on the same eventual domain. RHSharpArithmeticEnvelope.finite_cancellation supplies abs(E₃(x)+E₂p(x))<=4/x. Since beta>1/2 and x>=1, 1/x<=x^(beta-1). Adding these bounds gives B(x)>=-(2*K/(1-beta)+5*K+4)*x^(beta-1). Finally beta-1<=Theta-1+epsilon and the coefficient is nonnegative, so increasing the exponent preserves the asserted lower bound.

The result controls B at the actual zero abscissa. It neither identifies that abscissa with one half nor proves RH or Robin's inequality.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroAbscissaMertensLowerBound.actual_B_zero_abscissa_lower_power`
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../Weil/Mertens/ZeroAbscissaPower.md)
