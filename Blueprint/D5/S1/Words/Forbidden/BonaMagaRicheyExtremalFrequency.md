# BonaMagaRicheyExtremalFrequency

## Abstract

The unrestricted proposed maximizers of the limiting avoidance frequency fail at length one.

Bóna, Maga and Richey, arXiv:2606.06655v2, Section 5.3, page 19: “Among all words of a fixed length k, forbidding the word 10^{k-1} or its reversal should maximize the frequency rho, although we do not have a proof of this.” Section 2 specifies k at least one throughout. Both proposed words and all binary competitors of that length are included; constant words are allowed.

A word is a List Bool, with true representing one. The imported ForbiddenWordCounting.omega w n consists of every length-n word containing no contiguous occurrence of w. Its native rho w n is the total number of ones in those words divided by n times their cardinality, with real coercions and real division. At n=0 this quotient is totalized; the value at zero does not affect convergence atTop. These are Definitions 2.1 and 2.4 of the source. The stopped first-hit statistic q is outside this assertion.

**Definition 1.1 (The proposed word).**

$$\forall k \in \mathbb{N},\; \operatorname{proposedWord}\left(k\right) = \operatorname{List}.\operatorname{cons}(true, \operatorname{List}.\operatorname{replicate}(k - 1, false))$$

*Formalization.* `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.proposedWord` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

For every natural k, proposedWord k is true followed by k-1 copies of false. Subtraction is truncated natural subtraction. The claim uses only k at least one, where this is exactly the length-k word 10^{k-1}. The second proposed optimizer is its List.reverse.

**Definition 1.2 (Maximization of actual limits).**

$$\forall k \in \mathbb{N},\; \forall u \in \operatorname{List}\left(Bool\right),\; (\operatorname{MaximizesFrequency}\left(k, u\right)) \Leftrightarrow ((\operatorname{List}.\operatorname{length}(u) = k) \land (\exists r \in \mathbb{R},\; (\operatorname{Tendsto}\left(\operatorname{rho}\left(u\right), atTop, \operatorname{nhds}\left(r\right)\right)) \land (\forall v \in \operatorname{List}\left(Bool\right),\; (\operatorname{List}.\operatorname{length}(v) = k) \Rightarrow (\exists s \in \mathbb{R},\; (\operatorname{Tendsto}\left(\operatorname{rho}\left(v\right), atTop, \operatorname{nhds}\left(s\right)\right)) \land (s \le r)))))$$

*Formalization.* `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.MaximizesFrequency` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

For every natural k and every binary list u, MaximizesFrequency k u says that u has length k and there exists a real r to which its native rho converges. For every binary list v of length k there must exist a real s to which its native rho converges, with s at most r. The quantified values are actual limits. Uniqueness of real limits makes their choice immaterial. Convergence is part of the assertion, rather than an implication whose convergence premises can be empty.

**Definition 1.3 (The full universal assertion).**

$$(claim) \Leftrightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((\operatorname{MaximizesFrequency}\left(k, \operatorname{proposedWord}\left(k\right)\right)) \land (\operatorname{MaximizesFrequency}\left(k, \operatorname{List}.\operatorname{reverse}(\operatorname{proposedWord}\left(k\right))\right))))$$

*Formalization.* `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

claim has type Prop. For every natural k at least one, both the proposed word and its reversal must maximize the limiting frequency among all length-k binary words. There is no restriction on composition, nonconstancy or irreducibility. The separate fixed-composition question later in Section 5.3 is not included.

**Theorem 1.4 (The universal assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

At k=1, proposedWord 1 and its reversal are both [true]. The native theorem BalancedBordersHalfFrequency.rho_singleton gives rho [true] n=0 and rho [false] n=1 for every natural n greater than zero. An eventually constant sequence converges to that constant, so the two actual limits are zero and one, with 0<1. In particular each proposed optimizer has a strictly smaller limiting frequency than the competitor [false] of the same length. The private singleton_tendsto lemma transfers the positive-length native identities to these limits. If claim held, its first maximization at k=1 would give a candidate limit r and a competitor limit s with s≤r. Uniqueness of limits forces r=0 and s=1, contradicting 0<1. The theorem has literal type Not claim. This decides the unrestricted universal assertion. Variants with k at least two, k at least three or only nonconstant words remain unproved here; no general classification of maximizers follows.

## References

- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.MaximizesFrequency`
- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim`
- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.proposedWord`
- Truth anchor: `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.result`
- Dependency: [D5/S1/Words/Forbidden/BalancedBordersHalfFrequency](BalancedBordersHalfFrequency.md)
