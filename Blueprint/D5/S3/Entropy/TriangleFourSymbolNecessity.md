# Triangle Four-Symbol Necessity

## Abstract

The source-faithful four-symbol necessity core for the finite triangle equality fiber.

**Theorem 1.1 (Three weighted likelihood directions require four outputs).**

$$\forall O, \operatorname{Fintype}\left(O\right) \Rightarrow \forall F:\operatorname{TriangleLikelihoodFrame}\left(O\right), 4 \le \operatorname{card}\left(O\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolNecessity.weighted_likelihood_frame_card_ge_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frame is the actual equality-fiber likelihood data: a strictly positive output law, three centered likelihood directions, pairwise weighted orthogonality, and one nonzero direction for each source. The proof makes 1 and the three directions linearly independent in the finite output function space, so the output support has cardinality at least four.

This is the dimension part of the source theorem. The stochastic-kernel derivation of the frame is deliberately a separate bridge obligation.

**Theorem 1.2 (Binary pair-readout tables are parity up to relabelling).**

$$\forall g:Bool\to Bool\to Bool, \operatorname{RowsInjective}\left(g\right) \land \operatorname{ColumnsInjective}\left(g\right) \Rightarrow \exists c:Bool, \forall u, v, \operatorname{g}\left(u, v\right) = \operatorname{xor}\left(c, \operatorname{xor}\left(u, v\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolNecessity.binary_latin_square_is_xor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity of every binary row and column is the exact four-cell recoverability condition. Exhaustive kernel reduction proves that the third block bit is the XOR of the first two, up to one global bit relabeling.

The hypotheses describe the actual block table obtained from the original source law; they do not assert conditional pairwise independence as a substitute for the full law.

**Definition 1.3 (Original-source binary block cell law).**

$$\forall S1, S2, S3, O, \forall h:\operatorname{Bijection}\left(\operatorname{prod}\left(Bool, Bool\right), O\right), \forall q1:\operatorname{prod}\left(Bool, S1\right)\to \mathbb{R}, \forall q2:\operatorname{prod}\left(Bool, S2\right)\to \mathbb{R}, \forall q3:\operatorname{prod}\left(Bool, S3\right)\to \mathbb{R}, \forall x:O, \forall s:\operatorname{prod}\left(S1, \operatorname{prod}\left(S2, S3\right)\right), \operatorname{binaryBlockCell}\left(h, q1, q2, q3, x, s\right) = \sum_{u\in Bool} \sum_{v\in Bool} \operatorname{if}\left(x = h(\operatorname{pair}\left(u, v\right)), \frac{1}{4} q1(\operatorname{pair}\left(u, \operatorname{fst}\left(s\right)\right)) q2(\operatorname{pair}\left(v, \operatorname{fst}\left(\operatorname{snd}\left(s\right)\right)\right)) q3(\operatorname{pair}\left(\operatorname{xor}\left(u, v\right), \operatorname{snd}\left(\operatorname{snd}\left(s\right)\right)\right))0\right).$$

*Formalization.* `D5/S3/Entropy/TriangleFourSymbolNecessity.binaryBlockCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cell law is indexed by the original source alphabets. It retains arbitrary within-block source noise and all structural zeros; q_i are not collapsed to source alphabets of size two.

**Theorem 1.4 (The reconstructed original source has independent pair marginals).**

$$\forall S1, S2, S3, \operatorname{Fintype}\left(S3\right) \Rightarrow \forall q1:\operatorname{prod}\left(Bool, S1\right)\to \mathbb{R}, \forall q2:\operatorname{prod}\left(Bool, S2\right)\to \mathbb{R}, \forall q3:\operatorname{prod}\left(Bool, S3\right)\to \mathbb{R}, \forall s1:S1, \forall s2:S2, \operatorname{normalized}\left(q3\right) \Rightarrow \sum_{u\in Bool} \sum_{v\in Bool} \sum_{s3\in S3} \frac{1}{4} q1(\operatorname{pair}\left(u, s1\right)) q2(\operatorname{pair}\left(v, s2\right)) q3(\operatorname{pair}\left(\operatorname{xor}\left(u, v\right), s3\right)) = (\frac{1}{2}) (q1(\operatorname{pair}\left(false, s1\right)) + q1(\operatorname{pair}\left(true, s1\right))) (\frac{1}{2}) (q2(\operatorname{pair}\left(false, s2\right)) + q2(\operatorname{pair}\left(true, s2\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolNecessity.binary_block_source_pair_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the full original three-source cell law over the third source gives the product of the two averaged block laws. This is the exact source-pair consequence used by the necessity reconstruction and keeps the original source alphabets and zeros visible.

## References

- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolNecessity.binaryBlockCell`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolNecessity.binary_block_source_pair_marginal`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolNecessity.binary_latin_square_is_xor`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolNecessity.weighted_likelihood_frame_card_ge_four`
- Dependency: [D5/S3/Entropy/EntropyEquality](EntropyEquality.md)
