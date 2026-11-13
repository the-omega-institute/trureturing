# Affine Tails of the Actual Arithmetic Kernel

## Abstract

An affine upper bound on any positive tail of the complete actual arithmetic kernel forces RH.

**Theorem 1.1 (An affine upper bound on an arbitrary positive tail forces RH).**

$$\forall tau \in \mathbb{R},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < tau \Rightarrow \left(\left(\forall t \in \mathbb{R},\; tau \le t \Rightarrow \operatorname{K}\left(t\right) \le a \cdot t + b\right) \Rightarrow \operatorname{RiemannHypothesis}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_affine_tail_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau>0 and let a,b be arbitrary real numbers. Suppose K(t)<=a*t+b for every real t>=tau, where K is the full literal ActualKernelLocalPositivity.K, with every Mangoldt ramp and trivial-zero correction retained. Then Mathlib RiemannHypothesis holds. This conditional criterion does not establish its arithmetic hypothesis or the original Robin converse.

The existing private engine is parameterized in place. For t>0 the actual integrated explicit formula identifies K(t) with k(t)=exp(-t/2)*Re(actualH(t)). On [tau,infinity), the denial makes a*t+b-k(t) nonnegative. Its ENNReal density against restricted volume defines mu; the closed and open cutoff restrictions agree because a singleton is Lebesgue-null. For r<0, |(a*t+b)*exp(r*t)| is bounded by (|a|*|t|+|b|)*exp(r*t). The zeroth and first exponential moments pay this bound for signed a,b. The actual exponential bound for k then proves mu's moments for r<-1/2, without finite total mass.

For P(z)=complexMGF(id,mu)(-z), the actual Laplace identity gives P=A-N/(z^2-1/4) initially in Re(z)>1/2. Keep the original normalization N=M*z-X'/X, X(z)=xiReading(z+1/2), M=firstLiMass. Here A=B+C, B=exp(-z*tau)*((a*tau+b)/z+a/z^2), and C=integral_(0,tau] exp(-z*t)*k(t) dt. Differentiating the restricted-volume transform pays B. Dominated parameter differentiation proves C entire, retaining the full finite prefix at the new cutoff without differentiating k.

First continue (z^2-1/4)*X*P=((z^2-1/4)*A-M*z)*X+X' on the actual open convex convergence domain of P inside Re(z)>0. Only local nonvanishing near positive real points is needed: the actual height theorem excludes real zeros of X. Endpoint normalization gives N(1/2)=0. The extension Q(z)=dslope(N,1/2,z)/(z+1/2) is holomorphic on this local nonzero domain. Analytic punctured uniqueness yields P=A-Q as a neighborhood germ at every interior convergence point there, including z=1/2; totalized division is not used as an extension.

Reflect z to -z and apply NonnegativeBoundary.integrable_exp_on_real_ray at target 0. The paid germs supply every real interior convergence point, so all negative exponential moments converge. The crossed identity now yields X'=G*X on the whole half-plane Re(z)>0, with G=(z^2-1/4)*(P-A)+M*z analytic even at the half-point and putative zeros of X. Using X(1/2)=1/2, the existing analytic linear ODE theorem excludes all such zeros; the existing right-half-strip reduction proves RH.

**Theorem 1.2 (The literal arithmetic kernel exceeds its linear envelope).**

$$\neg \operatorname{RiemannHypothesis} \Rightarrow \left(\exists y \in \mathbb{R},\; \operatorname{log}\left(10000\right) \le y \land 4 \cdot y + 9 < \operatorname{exp}\left(\frac{-y}{2}\right) \cdot \left(\operatorname{U}\left(\operatorname{exp}\left(y\right)\right) - \operatorname{log}\left(2 \cdot \pi\right) + \operatorname{trivialT}\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_linear_peak_of_not_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U, containing all prime-power endpoints, and trivialT is the complete trivial-zero correction. The conclusion has no zero-simplicity, prime-number-theorem or additional transform hypothesis. It provides no quantitative upper bound for the first excursion.

Deny the excursion and apply actual_kernel_affine_tail_implies_rh with tau=log(10000), a=4, b=9. This positive cutoff permits the exact arithmetic identity for K at every point of that closed tail. The parameterized engine above includes the entire finite prefix at tau; no upper bound is extended to an earlier tail.

**Theorem 1.3 (The signed-kernel Laplace transform gives an analytic linear ODE).**

$$\left(\forall beta \in \mathbb{R},\; 0 < beta \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall t \in \mathbb{R},\; \left|\operatorname{K}\left(t\right)\right| \le C \cdot \operatorname{exp}\left(beta \cdot \left|t\right|\right)\right)\right)\right) \Rightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_subexponential_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be precisely ActualKernelLocalPositivity.K: K(t)=exp(-|t|/2)*(CompleteMertensPeak.U(exp(|t|)) - log(2*pi) + trivialT(|t|)). Every Mangoldt ramp and every trivial-zero correction is retained. Suppose that for every real beta>0 there exists a real C>0 such that for every real t, |K(t)|<=C*exp(beta*|t|). Then Mathlib RiemannHypothesis holds. C may depend on beta. The statement adds no positivity, RH, zero-free or logarithmic-derivative hypothesis.

For Re(z)>0 set L(z)=integral_(t>0) exp(-z*t)*K(t) dt, using the signed K itself. Continuity is reused from K_continuous. At a point z0 with a=Re(z0)>0, choose beta=a/4. Throughout the open neighborhood Re(z)>a/2, the derivative integrand is bounded in norm by C*t*exp(-a*t/4). The pinned Mathlib exponential-moment owner proves this majorant integrable; hasDerivAt_integral_of_dominated_loc_of_deriv_le then proves complex differentiability and hence analyticity on Re(z)>0. No derivative of K is taken.

On t>0 the actual integrated explicit formula identifies K(t) with linearKernel(t), whose complex form and Laplace formula follow from the complete integrated explicit formula. With X(z)=xiReading(z+1/2), M=firstLiMass and D(z)=z^2-1/4, the initial formula on Re(z)>1/2 is L=(M*z-X'/X)/D. Xi nonvanishing is used only on this initial half-plane, where the existing owner already supplies it.

Clear both denominators there to get D*X*L=M*z*X-X'. Both sides are analytic throughout the connected half-plane Re(z)>0, so analytic_continuation_unique extends this cross-multiplied identity. It yields X'=G*X with G=M*z-D*L analytic, including at z=1/2 and at any putative zero of X. There is no division by X in this continuation.

Use the existing shiftedXi_half fact X(1/2)=1/2 as the nonzero anchor. AnalyticLogarithmicContinuation's analytic_linear_ode_zero_free excludes every zero of X in Re(z)>0 without any simplicity premise. The existing RightHalfStripRiemannReduction converts this to Mathlib RH. This conditional criterion does not prove that the arithmetic K satisfies its subexponential hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_affine_tail_implies_rh`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_subexponential_implies_rh`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_linear_peak_of_not_rh`
- Dependency: [D5/S3/Analytic/Laplace/NonnegativeBoundary](../../../Analytic/Laplace/NonnegativeBoundary.md)
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity](ActualKernelLocalPositivity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](WholeFormula.md)
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](../../Probability/AnalyticLogarithmicContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
