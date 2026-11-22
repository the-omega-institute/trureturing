# Forward increments of the full root spectrum

## Abstract

Sharp forward increments of the full root spectrum under quarter-phase recurrence

**Theorem 1.1 (Uniform upper estimate and a signed late return).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists A \in \mathbb{R},\; \exists C \in \mathbb{R},\; 2 \le A \land \left(0 \le C \land \left(\forall t \in \mathbb{R},\; \left(0 < t \land A \cdot t \le 1\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \left|\operatorname{S}\left(r, u + r \cdot t\right) - \operatorname{S}\left(r, u\right)\right| \le \frac{r \cdot t}{2 \cdot \pi \cdot \operatorname{s}\left(r\right)} \cdot \operatorname{log}\left(\frac{1}{t}\right)^{2} + C \cdot t \cdot \left(1 + \operatorname{log}\left(\frac{1}{t}\right)\right)\right) \land \left(q \in H \Rightarrow \left(\forall U \in \mathbb{R},\; \forall b \in \mathbb{R},\; b < \frac{r \cdot t}{2 \cdot \pi \cdot \operatorname{s}\left(r\right)} \cdot \operatorname{log}\left(\frac{1}{t}\right)^{2} - C \cdot t \cdot \left(1 + \operatorname{log}\left(\frac{1}{t}\right)\right) \Rightarrow \left(\exists u \in \mathbb{R},\; U \le u \land b < \operatorname{S}\left(r, u + r \cdot t\right) - \operatorname{S}\left(r, u\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement.root_signal_quarter_phase_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here S is the centered, normalized root signal summed over actual zero occurrences with analytic multiplicity. Put s(r) = 1/2 − 1/(2r). The displacement is rt for positive t.

The quarter phase q has value i on every distinct positive zeta zero. Its hull H is the closure of the phase orbit in the product topology. Positive occurrences use the same coordinate for each copy of a zero. Negative occurrences use the conjugate coordinate of the corresponding positive zero. Continuity carries the phase readout to arbitrarily late returns.

Under RH the leading coefficient of each occurrence is −r/(1/4 + γ²). The difference from the root coefficient is summable after multiplication by |γ|, so its contribution to the increment is bounded by a constant times t, uniformly in phase. At q the real parts sum to r times the positive-ordinate sine slope before dividing by s(r). This pairing uses the analytic multiplicity of each distinct zero. `D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness`

The uniform upper estimate bounds the exponential increment by the absolute sine plus the cosine deficit. The absolute sine equals the sine of the absolute argument through |γ|t ≤ 1. The correction above that cutoff is controlled by the inverse-square tail. The origin cosine deficit contributes at the smaller scale t(1 + log(1/t)). `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp` `D5/S3/Weil/Mertens/ZeroAbscissaPower`

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement.root_signal_quarter_phase_increment`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement](RHRootLateIncrement.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../ZeroAbscissaPower.md)
- Dependency: [D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer](../../../../ZeroData/ZetaOrdinateCompleteOptimizer.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp](../../ActualKernelCusp.md)
- Narrative reference: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../ZeroAbscissaPower.md)
- Narrative reference: [D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness](../../../../ZeroData/ZetaOrdinatePhaseStiffness.md)
