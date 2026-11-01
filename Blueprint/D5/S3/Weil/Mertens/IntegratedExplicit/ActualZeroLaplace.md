# Laplace transform of every actual zero occurrence

## Abstract

Laplace transform of every actual zero occurrence

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
