# Leading Spectral Moment Recovery

## Abstract

The leading positive spectral scale and its positive inverse-square ordinate are recovered from power moments.

**Theorem 1.1 (Power moments recover the leading spectral scale).**

$$\begin{gathered}\forall alpha: \mathbb{N} \to \mathbb{R}, multiplicity: \mathbb{N} \to \mathbb{N}, gamma \in \mathbb{R},\\{}(\forall j \in \mathbb{N}, 0 < \operatorname{alpha}\left(j\right)) \land \operatorname{StrictAnti}\left(alpha\right) \land 0 < \operatorname{multiplicity}\left(0\right) \land\\{}\operatorname{Summable}\left((j \mapsto \operatorname{real}\left(\operatorname{multiplicity}\left(j\right)\right) \times \operatorname{alpha}\left(j\right))\right) \land 0 < gamma \land \operatorname{alpha}\left(0\right) = (gamma^{-1})^{2} \Rightarrow\\{}\text{let } moment: \mathbb{N} \to \mathbb{R} := (n: \mathbb{N} \mapsto \operatorname{tsum}\left(j, \operatorname{real}\left(\operatorname{multiplicity}\left(j\right)\right) \times \operatorname{alpha}\left(j\right)^{n + 1}\right));\\{}\operatorname{Tendsto}\left((n \mapsto \frac{\operatorname{moment}\left(n + 1\right)}{\operatorname{moment}\left(n\right)}), atTop, \operatorname{nhds}\left(\operatorname{alpha}\left(0\right)\right)\right) \land\\{}\operatorname{Tendsto}\left((n \mapsto \operatorname{moment}\left(n\right)^{\frac{1}{\operatorname{real}\left(n + 1\right)}}), atTop, \operatorname{nhds}\left(\operatorname{alpha}\left(0\right)\right)\right) \land\\{}\operatorname{Tendsto}\left((n \mapsto \sqrt{\frac{\operatorname{moment}\left(n\right)}{\operatorname{moment}\left(n + 1\right)}}), atTop, \operatorname{nhds}\left(gamma\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/LeadingSpectralMomentRecovery.leading_spectral_moment_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be a strictly decreasing positive real spectrum, let multiplicity assign natural multiplicities, and assume the multiplicity-weighted first spectral powers are summable. The leading multiplicity and the inverse-square ordinate gamma are positive, with alpha at zero equal to the square of gamma inverse.

Define each moment as the infinite sum of multiplicity times the corresponding spectral power. Dominated convergence makes the normalized tail tend to the leading multiplicity. Consecutive moment ratios and real roots therefore recover alpha at zero, while the square root of the inverse ratio recovers gamma.

Repository, pinned library, and external Lean searches found no equal or stronger leading-atom moment theorem. The proof directly uses the pinned dominated-convergence theorem for infinite sums, the power limit below one, real-power continuity, division, and square-root continuity.

## References

- Truth anchor: `D5/S3/Constants/Moments/LeadingSpectralMomentRecovery.leading_spectral_moment_recovery`
