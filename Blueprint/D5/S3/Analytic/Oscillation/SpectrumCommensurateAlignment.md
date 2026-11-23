# Frequent Full Alignment with a Logarithmic Square Tail

## Abstract

A logarithmic square tail can coexist with frequent full sine alignment.

**Theorem 1.1 (Full alignment in every interval of logarithmic length).**

$$\exists S \in Spectrum,\; \exists w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{Infinite}\left(\operatorname{index}\left(S\right)\right) \land \left(\left(\forall j \in \operatorname{index}\left(S\right),\; 0 < \operatorname{w}\left(j\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \left(\operatorname{HasLogarithmicSquareTail}\left(S, w\right) \land \left(\forall T \in \mathbb{R},\; 5 \le T \Rightarrow \left(0 < \operatorname{mass}\left(S, w, T\right) \land \left(\exists q \in \mathbb{N},\; 0 < q \land \left(q + 1 \le \frac{\operatorname{log}\left(T\right)}{\operatorname{log}\left(2\right)} \land \left(\left(\forall m \in \mathbb{Z},\; \forall X \in \mathbb{R},\; X \le T \Rightarrow \operatorname{sine}\left(S, w, X, \frac{\pi \cdot q}{2} + m \cdot 2 \cdot \pi \cdot q\right) = \operatorname{mass}\left(S, w, X\right)\right) \land \left(\forall A \in \mathbb{R},\; \exists m \in \mathbb{Z},\; A < \frac{\pi \cdot q}{2} + m \cdot 2 \cdot \pi \cdot q \land \frac{\pi \cdot q}{2} + m \cdot 2 \cdot \pi \cdot q < A + \frac{2 \cdot \pi}{\operatorname{log}\left(2\right)} \cdot \operatorname{log}\left(T\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment.exists_logarithmic_full_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use blocks between 4·2ⁿ and 8·2ⁿ. In block n let q be the largest power of five at most n+1. Put q·2ⁿ distinct frequencies at offsets (4k+1)/q from the lower boundary, and divide total weight 2n+1 equally among them. The frequencies strictly inside each block give local finiteness and distinctness.

A cutoff in block n contains the first n complete blocks and some of block n. Their weights bound the inclusive mass between n² and (n+1)². The squared weight of a complete block is at most 20(n+1)/2ⁿ, the consecutive difference of 40(n+2)/2ⁿ. Summing from the block containing X bounds the tail by a constant times log X/X for every finite upper cutoff T ≥ X.

At a cutoff in block N, each earlier denominator divides q in block N with quotient congruent to one modulo four. Multiplying each retained frequency by q therefore gives an integer congruent to one modulo four. All retained sines equal one at πq/2 and at every translate of that time by an integer multiple of 2πq, simultaneously at every smaller inclusive cutoff. The estimate q+1 ≤ log T/log 2 puts at least 2π between that period and the stated interval length.

Thus the logarithmic mass and square-tail laws permit a spectrum that reaches full mass in every sufficiently long window. The construction concerns a comparison spectrum. The window theorem with rational linear independence is available in `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window`

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment.exists_logarithmic_full_alignment`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow](SpectrumLogarithmicMissingWindow.md)
