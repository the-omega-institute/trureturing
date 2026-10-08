# BonaMagaRicheyHalfFrequency

## Abstract

Half letter frequency characterizes balanced borders of nonempty binary words.

**Definition 1.1 (claim).**

$$(claim) \Leftrightarrow (\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow ((\operatorname{Tendsto}\left(\operatorname{rho}\left(w\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)) \Leftrightarrow (\operatorname{BalancedBorders}\left(w\right))))$$

*Formalization.* `D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.claim` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“A word $w$ has $\rho^{w} = 1/2$ if and only if $w$ has balanced borders. The same holds with $\rho^{w}$ replaced by $q^{w}$.” (Conjecture 6.1, p. 20.)

The first sentence is encoded for every nonempty List Bool as convergence of the source averages to 1/2. No separate convergence hypothesis is added. The q sentence is outside this claim.

**Theorem 1.2 (result).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow ((\operatorname{Tendsto}\left(\operatorname{rho}\left(w\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)) \Leftrightarrow (\operatorname{BalancedBorders}\left(w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

The half-frequency characterization holds for every nonempty binary word. For lengths at least three, the scalar moment identities and escaping Abel weights force the boundary signed moment to vanish. The longest-border estimate then forces every border to be balanced. Singleton and constant length-two words are excluded directly; mixed length-two words have balanced borders. The reverse implication gives exact half frequency at every positive length.

## References

- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.claim`
- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.result`
- Dependency: [D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary](ForbiddenWordRationalBoundary.md)
