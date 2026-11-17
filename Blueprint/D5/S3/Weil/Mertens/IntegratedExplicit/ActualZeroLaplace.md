# Laplace transform of every actual zero occurrence

## Abstract

Laplace transform of every actual zero occurrence

Signed Gaussian application of actual_complete_H_package. Use the actual occurrence H and coefficients c_k from ActualReciprocalSquareBounds. For real m>0 and gamma define d_m(y)=exp(-(y-16*m)^2/(4*m))/sqrt(4*pi*m), u=(y-16*m)/(2*m), P=(u+i*gamma)*(u+i*gamma-1)-1/(2*m), W(y)=-exp(-i*gamma*y)*P*d_m(y), K=Re(W), and V(y)=2*(u^2+gamma^2+1)*d_m(y). These are scalar definitions in this application, not additional library declarations. The complete H package supplies reality and the all-occurrence weighted integral exchange whenever exp(max(y,0))*|W(y)| or exp(max(y,0))*V(y) is integrable.

For every complex tilt z, Mathlib complexMGF_id_gaussianReal and iteratedDeriv_complexMGF at mean 16*m and variance 2*m give M(z)=exp(m*z^2+16*m*z), integral exp(z*y)*d_m=M(z), integral u*exp(z*y)*d_m=z*M(z), and integral u^2*exp(z*y)*d_m=(z^2+1/(2*m))*M(z). Exponential monomial integrability follows from integrableExpSet_id_gaussianReal and integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet; gaussianReal_of_var_ne_zero and integral_gaussianReal_eq_integral_smul give the literal Lebesgue density and normalization. Expanding P at z=rho-i*gamma retains the variance term and cancels it exactly against -1/(2*m), giving integral exp(rho*y)*W(y)=-rho*(rho-1)*exp(m*((rho-i*gamma)^2+16*(rho-i*gamma))). The transform of V is 2*(rho^2+gamma^2+1+1/(2*m))*exp(m*rho^2+16*m*rho). These statements allow every complex rho and all m>0.

Polynomial Gaussian integrability at the real tilts zero and one, together with exp(max(y,0))<=1+exp(y), pays both weighted integrability premises. Apply actual_complete_H_package separately to W and V before passing real parts through their Bochner integrals. Multiplication of the W transform by the literal c_k cancels -rho_k*(rho_k-1), because rho_k and 1-rho_k are nonzero in the open strip. The resulting identity is integral Re(H(y))*K(y)=Re(E), with E the complete shifted Gaussian sum described in the mass and power-sum owners. The V exchange retains sum_k c_k*2*(rho_k^2+gamma^2+1+1/(2*m))*exp(m*rho_k^2+16*m*rho_k). Neither exchange replaces the whole series by its local part.

For m>=1, the norm-product inequality |A*B|<=(|A|^2+|B|^2)/2, with A=u+i*gamma and B=u+i*gamma-1, followed by |u|<=u^2+1/4, gives |P|<=2*(u^2+gamma^2+1). Hence |K|<=V and 0<=K+V. The actual coefficient bound |c_k|<=eta_k^(-2) and |H|<=2*exp(max(y,0)) also give integrability of H*K, H*V and |Re(H)|*V. The central b(y)=(4*y+11)*exp(y/2) times V is integrable by the same polynomial Gaussian bounds.

For the entire V response suppose gamma>10, D=gamma+10, m>=1 and t=|eta_k|>10. The strip gives |rho_k^2+gamma^2+1+1/(2*m)|<=t^2+gamma^2+5/2 and the exponential norm <=exp(17*m)*exp(-m*t^2). Put v=t^2-100>=0 and A=gamma^2+205/2. Then 1<=A<=D^2 and A+v<=A*(1+v)<=A*exp(m*v). Thus (t^2+gamma^2+5/2)*exp(-m*t^2)<=D^2*exp(-100*m). Each complete V-response term is bounded by 2*D^2*exp(-83*m)*eta_k^(-2). Summable comparison against the actual mass R<2 first proves absolute convergence, then gives |integral Re(H)*V|<=4*D^2*exp(-83*m)<=1000*D^2*exp(-83*m). This pays the whole signed envelope debit; the coefficient 1000 is a faithful weakening of four.

The coefficient is 1/(rho*(1-rho)) at each actual analytic multiplicity occurrence, with both imaginary signs. The existing normalized xi resolvent supplies the exact mass, conjugation supplies reality, and absolute coefficient bounds pay the integral exchange. No symmetry, mass, transform or RH assumption is added. These analytic suppliers are consumed by the complete integrated explicit formula.

**Theorem 1.1 (actual complete H package).**

$$\mathrm{HasSum}\left((\lambda \mathit{x0}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x0}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x0}\right)\right)}), \mathrm{ofReal}\left(\mathrm{firstLiMass}\right), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right) \land \left(\exists x0 \in \mathrm{Perm}\left(\mathrm{Nat}\right),\; \left(\forall x1 \in \mathrm{Nat},\; \mathrm{actualZero}\left(\mathit{x0}\left(\mathit{x1}\right)\right) = \mathrm{starRingEnd}\left(\mathrm{Complex}\right)\left(\mathrm{actualZero}\left(\mathit{x1}\right)\right)\right) \land \left(\left(\forall x1 \in \mathrm{Real},\; \mathrm{Summable}\left((\lambda \mathit{x2}:\mathrm{Nat}. (\lambda \mathit{x3}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x3}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x3}\right)\right)})\left(\mathit{x2}\right) \cdot \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x1}\right) \cdot \mathrm{actualZero}\left(\mathit{x2}\right)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right) \land \left(\mathrm{im}\left(\mathrm{tsum}\left((\lambda \mathit{x2}:\mathrm{Nat}. (\lambda \mathit{x3}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x3}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x3}\right)\right)})\left(\mathit{x2}\right) \cdot \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x1}\right) \cdot \mathrm{actualZero}\left(\mathit{x2}\right)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)\right) = 0 \land \left\lVert \mathrm{tsum}\left((\lambda \mathit{x2}:\mathrm{Nat}. (\lambda \mathit{x3}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x3}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x3}\right)\right)})\left(\mathit{x2}\right) \cdot \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x1}\right) \cdot \mathrm{actualZero}\left(\mathit{x2}\right)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right) \right\rVert \le \frac{101}{100} \cdot \mathrm{firstLiMass} \cdot \mathrm{exp}\left(\mathrm{max}\left(\mathit{x1}, 0\right)\right)\right)\right) \land \left(\forall x1 \in \mathrm{Real} \to \mathrm{Complex},\; \mathrm{AEStronglyMeasurable}\left(\mathit{x1}, \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right) \Rightarrow \left(\mathrm{Integrable}\left((\lambda \mathit{x3}:\mathrm{Real}. \mathrm{exp}\left(\mathrm{max}\left(\mathit{x3}, 0\right)\right) \cdot \left\lVert \mathit{x1}\left(\mathit{x3}\right) \right\rVert), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right) \Rightarrow \mathrm{HasSum}\left((\lambda \mathit{x4}:\mathrm{Nat}. (\lambda \mathit{x5}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x5}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x5}\right)\right)})\left(\mathit{x4}\right) \cdot \mathrm{integral}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), (\lambda \mathit{x5}:\mathrm{Real}. \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x5}\right) \cdot \mathrm{actualZero}\left(\mathit{x4}\right)\right) \cdot \mathit{x1}\left(\mathit{x5}\right))\right)), \mathrm{integral}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), (\lambda \mathit{x4}:\mathrm{Real}. \mathrm{tsum}\left((\lambda \mathit{x5}:\mathrm{Nat}. (\lambda \mathit{x6}:\mathrm{Nat}. \frac{1}{\mathrm{actualZero}\left(\mathit{x6}\right) \cdot \left(1 - \mathrm{actualZero}\left(\mathit{x6}\right)\right)})\left(\mathit{x5}\right) \cdot \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x4}\right) \cdot \mathrm{actualZero}\left(\mathit{x5}\right)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right) \cdot \mathit{x1}\left(\mathit{x4}\right))\right), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_complete_H_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.2 (actualCoeff hasSum).**

$$\mathrm{HasSum}\left(\mathrm{actualCoeff}, \mathrm{ofReal}\left(\mathrm{firstLiMass}\right), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualCoeff_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.3 (actualH summable).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{Summable}\left((\lambda \mathit{x1}:\mathrm{Nat}. \mathrm{actualCoeff}\left(\mathit{x1}\right) \cdot \mathrm{exp}\left(\mathrm{ofReal}\left(\mathit{x0}\right) \cdot \mathrm{actualZero}\left(\mathit{x1}\right)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.4 (actualH bound).**

$$\forall x0 \in \mathrm{Real},\; \left\lVert \mathrm{actualH}\left(\mathit{x0}\right) \right\rVert \le \frac{101}{100} \cdot \mathrm{firstLiMass} \cdot \mathrm{exp}\left(\mathrm{max}\left(\mathit{x0}, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.5 (actualH continuous).**

$$\mathrm{Continuous}\left(\mathrm{actualH}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.6 (xiReading ne zero right).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{xiReading}\left(\mathit{x0}\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.xiReading_ne_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.7 (actual normalized resolvent).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{HasSum}\left((\lambda \mathit{x2}:\mathrm{Nat}. \frac{1}{\mathit{x0} - \mathrm{actualZero}\left(\mathit{x2}\right)} + \frac{1}{\mathrm{actualZero}\left(\mathit{x2}\right)}), \mathrm{logDeriv}\left(\mathrm{xiReading}, \mathit{x0}\right) + \frac{\mathrm{ofReal}\left(\mathrm{firstLiMass}\right)}{2}, \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_normalized_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.8 (actual resolvent hasSum).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{HasSum}\left((\lambda \mathit{x2}:\mathrm{Nat}. \frac{\mathrm{actualCoeff}\left(\mathit{x2}\right)}{\mathit{x0} - \mathrm{actualZero}\left(\mathit{x2}\right)}), \frac{\mathrm{ofReal}\left(\mathrm{firstLiMass}\right) \cdot \left(\mathit{x0} - \frac{1}{2}\right) - \mathrm{logDeriv}\left(\mathrm{xiReading}, \mathit{x0}\right)}{\mathit{x0} \cdot \left(\mathit{x0} - 1\right)}, \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_resolvent_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.9 (actualH laplace integrable).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{IntegrableOn}\left((\lambda \mathit{x2}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x0} \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{actualH}\left(\mathit{x2}\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_laplace_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.10 (actualH laplace).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x2}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x0} \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{actualH}\left(\mathit{x2}\right))\right) = \frac{\mathrm{ofReal}\left(\mathrm{firstLiMass}\right) \cdot \left(\mathit{x0} - \frac{1}{2}\right) - \mathrm{logDeriv}\left(\mathrm{xiReading}, \mathit{x0}\right)}{\mathit{x0} \cdot \left(\mathit{x0} - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.11 (xi logDeriv right).**

$$\forall x0 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{logDeriv}\left(\mathrm{xiReading}, \mathit{x0}\right) = \frac{1}{\mathit{x0}} + \frac{1}{\mathit{x0} - 1} - \frac{\mathrm{ofReal}\left(\mathrm{log}\left(\mathrm{pi}\right)\right)}{2} + \frac{\mathrm{digamma}\left(\frac{\mathit{x0}}{2}\right)}{2} + \frac{\mathrm{deriv}\left(\mathrm{riemannZeta}, \mathit{x0}\right)}{\mathrm{riemannZeta}\left(\mathit{x0}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.xi_logDeriv_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualCoeff_hasSum`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_continuous`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_laplace`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_laplace_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actualH_summable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_complete_H_package`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_normalized_resolvent`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.actual_resolvent_hasSum`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.xiReading_ne_zero_right`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.xi_logDeriv_right`
- Dependency: [D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds](../../ZeroData/ActualReciprocalSquareBounds.md)
