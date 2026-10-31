# Inclusive Mangoldt ramps and complete Mertens transform

## Abstract

Inclusive Mangoldt ramps and complete Mertens transform

The function U is the existing CompleteMertensPeak.U, with inclusive Chebyshev psi and the actual Euler constant. The locally finite positive-part ramp is zero when an integer term enters, so continuity includes every prime-power endpoint. Positive Tonelli and the complete Mangoldt LSeries at two pay the infinite arithmetic exchange before the complex integral is evaluated. The Fourier line is s=2+2*pi*i*t.

**Theorem 1.1 (mangoldtRamp nonneg).**

$$\forall x0 \in \mathrm{Nat},\; \forall x1 \in \mathrm{Real},\; 0 \le \mathrm{mangoldtRamp}\left(\mathit{x0}, \mathit{x1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.2 (mangoldtRamp continuous).**

$$\forall x0 \in \mathrm{Nat},\; \mathrm{Continuous}\left(\mathrm{mangoldtRamp}\left(\mathit{x0}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.3 (mangoldtRamp at entry).**

$$\forall x0 \in \mathrm{Nat},\; \mathrm{mangoldtRamp}\left(\mathit{x0}, \mathrm{cast}\left(\mathit{x0}\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_at_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.4 (mangoldtPart summable).**

$$\forall x0 \in \mathrm{Real},\; 0 \le \mathit{x0} \Rightarrow \mathrm{Summable}\left((\lambda \mathit{x2}:\mathrm{Nat}. \mathrm{mangoldtRamp}\left(\mathit{x2}, \mathit{x0}\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.5 (U eq complete ramps).**

$$\forall x0 \in \mathrm{Real},\; 0 \le \mathit{x0} \Rightarrow \mathrm{U}\left(\mathit{x0}\right) = \mathrm{mangoldtPart}\left(\mathit{x0}\right) - \mathit{x0} \cdot \mathrm{log}\left(\mathit{x0}\right) + \left(1 + \mathrm{eulerMascheroniConstant}\right) \cdot \mathit{x0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_eq_complete_ramps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.6 (U continuousAt pos).**

$$\forall x0 \in \mathrm{Real},\; 0 < \mathit{x0} \Rightarrow \mathrm{ContinuousAt}\left(\mathrm{U}, \mathit{x0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_continuousAt_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.7 (U exp continuous).**

$$\mathrm{Continuous}\left((\lambda \mathit{x0}:\mathrm{Real}. \mathrm{U}\left(\mathrm{exp}\left(\mathit{x0}\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_exp_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.8 (complete mangoldt endpoint).**

$$\forall x0 \in \mathrm{Nat},\; 0 < \mathit{x0} \Rightarrow \left(\mathrm{mangoldtRamp}\left(\mathit{x0}, \mathrm{cast}\left(\mathit{x0}\right)\right) = 0 \land \left(\mathrm{ContinuousAt}\left(\mathrm{U}, \mathrm{cast}\left(\mathit{x0}\right)\right) \land \mathrm{U}\left(\mathrm{cast}\left(\mathit{x0}\right)\right) = \mathrm{sum}\left(\mathrm{Ioc}\left(0, \mathit{x0}\right), (\lambda \mathit{x2}:\mathrm{Nat}. \mathrm{vonMangoldt}\left(\mathit{x2}\right) \cdot \left(\frac{\mathrm{cast}\left(\mathit{x0}\right)}{\mathrm{cast}\left(\mathit{x2}\right)} - 1\right))\right) - \mathrm{cast}\left(\mathit{x0}\right) \cdot \mathrm{log}\left(\mathrm{cast}\left(\mathit{x0}\right)\right) + \left(1 + \mathrm{eulerMascheroniConstant}\right) \cdot \mathrm{cast}\left(\mathit{x0}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.complete_mangoldt_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.9 (transformLine re).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{re}\left(\mathrm{transformLine}\left(\mathit{x0}\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.transformLine_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.10 (mangoldtRamp laplace).**

$$\forall x0 \in \mathrm{Nat},\; \forall x1 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x1}\right) \Rightarrow \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x3}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x1} \cdot \mathrm{ofReal}\left(\mathit{x3}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtRamp}\left(\mathit{x0}, \mathrm{exp}\left(\mathit{x3}\right)\right)\right))\right) = \frac{\mathrm{LSeriesTerm}\left((\lambda \mathit{x3}:\mathrm{Nat}. \mathrm{ofReal}\left(\mathrm{vonMangoldt}\left(\mathit{x3}\right)\right)), \mathit{x1}, \mathit{x0}\right)}{\mathit{x1} \cdot \left(\mathit{x1} - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.11 (mangoldtRamp laplace integrable).**

$$\forall x0 \in \mathrm{Nat},\; \forall x1 \in \mathrm{Complex},\; 1 < \mathrm{re}\left(\mathit{x1}\right) \Rightarrow \mathrm{IntegrableOn}\left((\lambda \mathit{x3}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x1} \cdot \mathrm{ofReal}\left(\mathit{x3}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtRamp}\left(\mathit{x0}, \mathrm{exp}\left(\mathit{x3}\right)\right)\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.12 (mangoldtRamp laplace norm).**

$$\forall x0 \in \mathrm{Real},\; \forall x1 \in \mathrm{Nat},\; \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x2}:\mathrm{Real}. \left\lVert \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtRamp}\left(\mathit{x1}, \mathrm{exp}\left(\mathit{x2}\right)\right)\right) \right\rVert)\right) = \frac{\frac{\mathrm{vonMangoldt}\left(\mathit{x1}\right)}{\mathrm{cast}\left(\mathit{x1}\right)^{2}}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.13 (mangoldtRamp norm integrals summable).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{Summable}\left((\lambda \mathit{x1}:\mathrm{Nat}. \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x2}:\mathrm{Real}. \left\lVert \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtRamp}\left(\mathit{x1}, \mathrm{exp}\left(\mathit{x2}\right)\right)\right) \right\rVert)\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_norm_integrals_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.14 (mangoldtPart line integrable).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{IntegrableOn}\left((\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtPart}\left(\mathrm{exp}\left(\mathit{x1}\right)\right)\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_line_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.15 (mangoldtPart line laplace).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{mangoldtPart}\left(\mathrm{exp}\left(\mathit{x1}\right)\right)\right))\right) = \frac{\frac{-\mathrm{deriv}\left(\mathrm{riemannZeta}, \mathrm{transformLine}\left(\mathit{x0}\right)\right)}{\mathrm{riemannZeta}\left(\mathrm{transformLine}\left(\mathit{x0}\right)\right)}}{\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \left(\mathrm{transformLine}\left(\mathit{x0}\right) - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_line_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.16 (first exp moment).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x1}:\mathrm{Real}. \mathrm{ofReal}\left(\mathit{x1}\right) \cdot \mathrm{exp}\left(\left(1 - \mathrm{transformLine}\left(\mathit{x0}\right)\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right))\right) = \frac{1}{\left(\mathrm{transformLine}\left(\mathit{x0}\right) - 1\right)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.first_exp_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.17 (U line integrable).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{IntegrableOn}\left((\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{U}\left(\mathrm{exp}\left(\mathit{x1}\right)\right)\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_line_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.18 (U line laplace).**

$$\forall x0 \in \mathrm{Real},\; \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x1}:\mathrm{Real}. \mathrm{exp}\left(-\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \mathrm{ofReal}\left(\mathit{x1}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{U}\left(\mathrm{exp}\left(\mathit{x1}\right)\right)\right))\right) = \frac{\frac{-\mathrm{deriv}\left(\mathrm{riemannZeta}, \mathrm{transformLine}\left(\mathit{x0}\right)\right)}{\mathrm{riemannZeta}\left(\mathrm{transformLine}\left(\mathit{x0}\right)\right)}}{\mathrm{transformLine}\left(\mathit{x0}\right) \cdot \left(\mathrm{transformLine}\left(\mathit{x0}\right) - 1\right)} - \frac{1}{\left(\mathrm{transformLine}\left(\mathit{x0}\right) - 1\right)^{2}} + \frac{\mathrm{ofReal}\left(1 + \mathrm{eulerMascheroniConstant}\right)}{\mathrm{transformLine}\left(\mathit{x0}\right) - 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_line_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_continuousAt_pos`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_eq_complete_ramps`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_exp_continuous`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_line_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.U_line_laplace`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.complete_mangoldt_endpoint`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.first_exp_moment`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_line_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_line_laplace`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtPart_summable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_at_entry`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_continuous`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_laplace_norm`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.mangoldtRamp_norm_integrals_summable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.transformLine_re`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../../../Arith/Robin/CompleteMertensPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace](TrivialZeroLaplace.md)
