# External-Support Invisibility

## Abstract

A compactly supported Weil correlation is unchanged by adding a tempered distribution whose distributional support lies outside its doubled window.

**Theorem 1.1 (External support is invisible to local Weil correlations).**

$$\begin{aligned}\forall L: \operatorname{Real}\left(\right), weilSource, kappa: \operatorname{TemperedDistribution}\left(\operatorname{Real}\left(\right), \operatorname{Complex}\left(\right)\right),\\hkappa: \operatorname{dsupport}\left(kappa\right) \subseteq \operatorname{compl}\left(\operatorname{Ioo}\left(-2L, 2 \cdot L\right)\right), f, h: \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right),\\hfSmooth: \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), f\right), hhSmooth: \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), h\right),\\hfCompact: \operatorname{HasCompactSupport}\left(f\right), hhCompact: \operatorname{HasCompactSupport}\left(h\right),\\hfSupport: \operatorname{tsupport}\left(f\right) \subseteq \operatorname{Ioo}\left(-L, L\right), hhSupport: \operatorname{tsupport}\left(h\right) \subseteq \operatorname{Ioo}\left(-L, L\right) \Rightarrow\\\operatorname{let} correlation := \operatorname{weilTest}\left(f, h\right),\\\operatorname{let} hcorrelationCompact: \operatorname{HasCompactSupport}\left(correlation\right) := \operatorname{weilTestHasCompactSupport}\left(hfCompact, hhCompact\right),\\\operatorname{let} hcorrelationSmooth: \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), correlation\right) := \operatorname{contDiffConvolutionRight}\left(\operatorname{hasCompactSupportTilde}\left(hhCompact\right), hfSmooth, \operatorname{contDiffTilde}\left(hhSmooth\right)\right),\\\operatorname{let} correlationTest := \operatorname{toSchwartzMap}\left(correlation, hcorrelationCompact, hcorrelationSmooth\right),\\\operatorname{add}\left(weilSource, kappa\right)\left(correlationTest\right) = weilSource\left(correlationTest\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ExternalSupportInvisibility.external_support_invisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical Weil correlation is constructed from the two supplied smooth compact tests. Its strict doubled-window support permits a finite smooth partition-of-unity decomposition into neighborhoods where the added tempered distribution vanishes.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ExternalSupportInvisibility.external_support_invisibility`
