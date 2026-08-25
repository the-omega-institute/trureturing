# Full CRT Blind Count and Distance

## Abstract

The full product range has maximal blind-coordinate count one below its length and exact distance one.

**Theorem 1.1 (Full CRT range has no coordinate-error margin).**

$$\begin{gathered}\forall m: \mathbb{N} \to \mathbb{N}, n \in \mathbb{N},\\{}(0 < n \land\\{}(\forall i, j, i < j \land j < n \Rightarrow \operatorname{m}\left(i\right) < \operatorname{m}\left(j\right)) \land\\{}(\forall i, i < n \Rightarrow 2 \leq \operatorname{m}\left(i\right)) \land\\{}(\forall i, j, i < n \land j < n \land i \neq j \Rightarrow \gcd(\operatorname{m}\left(i\right), \operatorname{m}\left(j\right)) = 1)) \Rightarrow\\{}\operatorname{maximumBlindCoordinateCount}\left(m, n, \operatorname{prefixProduct}\left(m, n\right)\right) = n - 1 \land\\{}\operatorname{residueMinimumDistance}\left(m, n, \operatorname{prefixProduct}\left(m, n\right)\right) = 1 \land\\{}(\forall x, y \in \mathbb{N}, x < \operatorname{prefixProduct}\left(m, n\right) \land y < \operatorname{prefixProduct}\left(m, n\right) \land \operatorname{residueWord}\left(m, n, x\right) = \operatorname{residueWord}\left(m, n, y\right) \Rightarrow x = y) \land\\{}(\exists x, y \in \mathbb{N}, x < y \land y < \operatorname{prefixProduct}\left(m, n\right) \land \operatorname{hammingDist}\left(\operatorname{residueWord}\left(m, n, x\right), \operatorname{residueWord}\left(m, n, y\right)\right) = 1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTBlindCountAndDistance.full_crt_blind_count_distance_and_detection_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blind-coordinate count is the canonical maximum over coordinate subsets whose modulus product lies below the message range. At the full product, every prefix omitting the last coordinate is admissible, while the complete coordinate set is not.

The resulting residue words are still injective on the complete range, so encoding remains unique. The attained minimum supplies two valid words separated in exactly one coordinate, showing that a single changed coordinate can be accepted as another valid word.

## References

- Truth anchor: `D5/S3/Arith/Coding/FullCRTBlindCountAndDistance.full_crt_blind_count_distance_and_detection_limit`
- Dependency: [D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin](FullCRTDynamicRangeNoCorrectionMargin.md)
