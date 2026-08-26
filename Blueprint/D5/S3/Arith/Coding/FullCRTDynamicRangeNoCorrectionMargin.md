# Full CRT Dynamic Range Has No Correction Margin

## Abstract

Using the full CRT product gives exact distance one, with the degenerate boundaries and the role of full capacity made explicit.

**Theorem 1.1 (Maximum distance is controlled by the first modulus).**

$$\forall m: \mathbb{N} \to \mathbb{N}, n, K \in \mathbb{N}, 0 < n \land (\forall i, j, i \leq j \land j < n \Rightarrow \operatorname{m}\left(i\right) \leq \operatorname{m}\left(j\right)) \land (\forall i, i < n \Rightarrow 0 < \operatorname{m}\left(i\right)) \land (\forall i, j, i < n \land j < n \land i \neq j \Rightarrow \operatorname{Coprime}\left(\operatorname{m}\left(i\right), \operatorname{m}\left(j\right)\right)) \Rightarrow \operatorname{MinDistanceAtLeast}\left(m, n, K, n\right) \iff K \leq \operatorname{prefixProduct}\left(m, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.maximum_possible_distance_iff_first_modulus_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the existing dynamic-range equivalence to d=n leaves a prefix of length one. This audits the largest possible Hamming distance without introducing a new distance argument.

**Theorem 1.2 (Full CRT range has minimum distance one).**

$$\forall m: \mathbb{N} \to \mathbb{N}, n \in \mathbb{N}, 0 < n \land (\forall i, j, i \leq j \land j < n \Rightarrow \operatorname{m}\left(i\right) \leq \operatorname{m}\left(j\right)) \land (\forall i, i < n \Rightarrow 1 < \operatorname{m}\left(i\right)) \land (\forall i, j, i < n \land j < n \land i \neq j \Rightarrow \operatorname{Coprime}\left(\operatorname{m}\left(i\right), \operatorname{m}\left(j\right)\right)) \Rightarrow \operatorname{residueMinimumDistance}\left(m, n, \operatorname{prefixProduct}\left(m, n\right)\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.full_crt_dynamic_range_minimum_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At distance one the dynamic-range theorem returns the full prefix product itself, so the minimum distance is at least one.

For at least two coordinates, the last modulus being above one makes the full product strictly exceed the preceding prefix, and the same theorem rules out distance two. A single coordinate is handled by the ambient one-coordinate Hamming bound.

The source's t(K) clause is not represented because the volume does not define t with that meaning; no replacement definition is invented here.

**Theorem 1.3 (Positive length is necessary).**

$$\operatorname{residueMinimumDistance}\left((i \mapsto 2), 0, \operatorname{prefixProduct}\left((i \mapsto 2), 0\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.positive_length_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At length zero all indexed modulus assumptions are vacuous. The full prefix product is one, so there are no two messages and the defined minimum-distance infimum is zero rather than one.

**Theorem 1.4 (Moduli above one are necessary).**

$$\operatorname{residueMinimumDistance}\left((i \mapsto 1), 1, \operatorname{prefixProduct}\left((i \mapsto 1), 1\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.modulus_greater_than_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-coordinate code with modulus one has full product one. Its full message range contains no distinct pair, so its minimum-distance object is zero.

**Theorem 1.5 (Pairwise coprimality is necessary).**

$$\exists m: \mathbb{N} \to \mathbb{N}, (\forall i, i < 2 \Rightarrow 1 < \operatorname{m}\left(i\right)) \land (\forall i, j, i \leq j \land j < 2 \Rightarrow \operatorname{m}\left(i\right) \leq \operatorname{m}\left(j\right)) \land \neg\operatorname{Coprime}\left(\operatorname{m}\left(0\right), \operatorname{m}\left(1\right)\right) \land \operatorname{residueMinimumDistance}\left(m, 2, \operatorname{prefixProduct}\left(m, 2\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.pairwise_coprime_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered moduli two and four are both above one, but messages zero and four have the same two residues. The full-product code therefore has minimum distance zero.

**Theorem 1.6 (Full dynamic range is necessary).**

$$\exists m: \mathbb{N} \to \mathbb{N}, (\forall i, i < 2 \Rightarrow 1 < \operatorname{m}\left(i\right)) \land (\forall i, j, i \leq j \land j < 2 \Rightarrow \operatorname{m}\left(i\right) \leq \operatorname{m}\left(j\right)) \land \operatorname{Coprime}\left(\operatorname{m}\left(0\right), \operatorname{m}\left(1\right)\right) \land 2 < \operatorname{prefixProduct}\left(m, 2\right) \land \operatorname{residueMinimumDistance}\left(m, 2, 2\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.full_dynamic_range_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For coprime moduli two and three, restricting messages to zero and one uses a range of two below the full product six. Those two words differ in both coordinates, so the exact minimum distance is two.

## References

- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.full_crt_dynamic_range_minimum_distance`
- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.full_dynamic_range_is_necessary`
- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.maximum_possible_distance_iff_first_modulus_bound`
- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.modulus_greater_than_one_is_necessary`
- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.pairwise_coprime_is_necessary`
- Truth anchor: `D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.positive_length_is_necessary`
- Dependency: [D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance](ExactResidueCodeMinimumDistance.md)
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](ResidueCodeDynamicRange.md)
