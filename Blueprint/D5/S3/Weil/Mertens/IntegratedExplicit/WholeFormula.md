# Unconditional integrated explicit formula

## Abstract

Unconditional integrated explicit formula

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
