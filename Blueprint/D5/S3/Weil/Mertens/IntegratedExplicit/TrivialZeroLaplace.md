# Complete trivial zero correction

## Abstract

Complete trivial zero correction

The natural index n represents j=n+1. The full coefficient series has mass 1-log(2), and uniform absolute bounds give continuity on the nonnegative half-axis. Damping pays the complete Laplace exchange for Re(s)>0. No finite truncation replaces the correction. The digamma series at one half is within its integer-complement domain.

**Theorem 1.1 (trivialCoeff nonneg).**

$$\forall x0 \in \mathrm{Nat},\; 0 \le \mathrm{trivialCoeff}\left(\mathit{x0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialCoeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.2 (trivialCoeff hasSum).**

$$\mathrm{HasSum}\left(\mathrm{trivialCoeff}, 1 - \mathrm{log}\left(2\right), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialCoeff_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.3 (trivialT summable).**

$$\forall x0 \in \mathrm{Real},\; 0 \le \mathit{x0} \Rightarrow \mathrm{Summable}\left((\lambda \mathit{x2}:\mathrm{Nat}. \mathrm{trivialCoeff}\left(\mathit{x2}\right) \cdot \mathrm{exp}\left(-\left(2 \cdot \left(\mathrm{cast}\left(\mathit{x2}\right) + 1\right)\right) \cdot \mathit{x0}\right)), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.4 (trivialT nonneg).**

$$\forall x0 \in \mathrm{Real},\; 0 \le \mathit{x0} \Rightarrow 0 \le \mathrm{trivialT}\left(\mathit{x0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.5 (trivialT le mass).**

$$\forall x0 \in \mathrm{Real},\; 0 \le \mathit{x0} \Rightarrow \mathrm{trivialT}\left(\mathit{x0}\right) \le 1 - \mathrm{log}\left(2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_le_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.6 (trivialT continuousOn).**

$$\mathrm{ContinuousOn}\left(\mathrm{trivialT}, \mathrm{Ici}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.7 (trivialT continuousAt).**

$$\forall x0 \in \mathrm{Real},\; 0 < \mathit{x0} \Rightarrow \mathrm{ContinuousAt}\left(\mathrm{trivialT}, \mathit{x0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_continuousAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.8 (trivialT laplace integrable).**

$$\forall x0 \in \mathrm{Complex},\; 0 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{IntegrableOn}\left((\lambda \mathit{x2}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x0} \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{trivialT}\left(\mathit{x2}\right)\right)), \mathrm{Ioi}\left(0\right), \mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_laplace_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.9 (trivialT laplace hasSum).**

$$\forall x0 \in \mathrm{Complex},\; 0 < \mathrm{re}\left(\mathit{x0}\right) \Rightarrow \mathrm{HasSum}\left((\lambda \mathit{x2}:\mathrm{Nat}. \frac{\mathrm{ofReal}\left(\mathrm{trivialCoeff}\left(\mathit{x2}\right)\right)}{\mathit{x0} + 2 \cdot \left(\mathrm{cast}\left(\mathit{x2}\right) + 1\right)}), \mathrm{integral}\left(\mathrm{restrict}\left(\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right), \mathrm{Ioi}\left(0\right)\right), (\lambda \mathit{x2}:\mathrm{Real}. \mathrm{exp}\left(-\mathit{x0} \cdot \mathrm{ofReal}\left(\mathit{x2}\right)\right) \cdot \mathrm{ofReal}\left(\mathrm{trivialT}\left(\mathit{x2}\right)\right))\right), \mathrm{unconditional}\left(\mathrm{Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_laplace_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

**Theorem 1.10 (trivial partial fraction).**

$$\forall x0 \in \mathrm{Complex},\; \forall x1 \in \mathrm{Complex},\; \mathit{x0} \ne 0 \Rightarrow \left(2 \cdot \mathit{x0} + 1 \ne 0 \Rightarrow \left(\mathit{x1} + 2 \cdot \mathit{x0} \ne 0 \Rightarrow \frac{1}{2 \cdot \mathit{x0} \cdot \left(\mathit{x1} + 2 \cdot \mathit{x0}\right)} + \frac{\mathit{x1} - 1}{2 \cdot \mathit{x0} \cdot \left(2 \cdot \mathit{x0} + 1\right) \cdot \left(\mathit{x1} + 2 \cdot \mathit{x0}\right)} = \frac{1}{2 \cdot \mathit{x0} \cdot \left(2 \cdot \mathit{x0} + 1\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivial_partial_fraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact hypotheses, occurrence indices and endpoint quantifiers are given by the Lean declaration.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialCoeff_hasSum`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialCoeff_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_continuousAt`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_continuousOn`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_laplace_hasSum`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_laplace_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_le_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivialT_summable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.trivial_partial_fraction`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace](ActualZeroLaplace.md)
