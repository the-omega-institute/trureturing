# Dynamic Range and Minimum Distance of Residue Codes

## Abstract

For an ordered coprime residue system, the protected message range is determined exactly by the product of its smallest moduli.

**Lemma 1.1 (A strictly increasing finite index selection dominates its ranks).**

$$\forall k, n \in \mathbb{N}, \forall f: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \operatorname{StrictMono}\left(f\right) \Rightarrow \forall i \in \operatorname{Fin}\left(k\right), i \leq \operatorname{f}\left(i\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeDynamicRange.fin_index_le_strict_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strictly increasing map from the first k indices into the first n indices cannot send any rank i below i. In other words, the i-th selected coordinate is always at least the i-th coordinate of the initial segment.

The argument proceeds by rank. Rank zero has the required lower bound automatically. At the next rank, strict increase places its image strictly above the preceding image; the induction bound on that preceding image then forces the new image to be at least the new rank.

**Lemma 1.2 (Selected residue agreement is equivalent to product divisibility).**

$$\forall k, n, x, y \in \mathbb{N}, \forall m: \mathbb{N} \to \mathbb{N}, \forall f: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), x \leq y, (\forall i, j \in \operatorname{Fin}\left(k\right), i \neq j \Rightarrow \gcd(\operatorname{m}\left(\operatorname{f}\left(i\right)\right), \operatorname{m}\left(\operatorname{f}\left(j\right)\right)) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right), \operatorname{residueWord}\left(m, n, x, \operatorname{f}\left(i\right)\right) = \operatorname{residueWord}\left(m, n, y, \operatorname{f}\left(i\right)\right)) \iff \prod_{i \in \operatorname{Fin}\left(k\right)} \operatorname{m}\left(\operatorname{f}\left(i\right)\right) \mid y - x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeDynamicRange.agree_on_iff_prod_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose k coordinates of an n-coordinate residue word and suppose the moduli at those coordinates are pairwise coprime. For messages x and y with x at most y, their residues agree at every selected coordinate exactly when the product of all selected moduli divides y minus x.

Agreement modulo each selected modulus makes every factor divide the message difference. Pairwise coprimality combines these divisibilities into divisibility by the full product. Conversely, each selected modulus divides that product, so product divisibility recovers every individual congruence and hence every selected residue equality.

**Theorem 1.3 (Maximum dynamic range is equivalent to the minimum-distance bound).**

$$\forall m: \mathbb{N} \to \mathbb{N}, \forall n, d, K \in \mathbb{N}, 1 \leq d \leq n, (\forall i, j \in \mathbb{N}, i \leq j \land j < n \Rightarrow \operatorname{m}\left(i\right) \leq \operatorname{m}\left(j\right)), (\forall i \in \mathbb{N}, i < n \Rightarrow 0 < \operatorname{m}\left(i\right)), (\forall i, j \in \mathbb{N}, i < n \land j < n \land i \neq j \Rightarrow \gcd(\operatorname{m}\left(i\right), \operatorname{m}\left(j\right)) = 1), \operatorname{MinDistanceAtLeast}\left(m, n, K, d\right) \iff K \leq \operatorname{prefixProduct}\left(m, n - d + 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeDynamicRange.maximum_dynamic_range_iff_min_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the first n moduli be positive, nondecreasing, and pairwise coprime, and let d lie between one and n. The residue code on messages below K has Hamming distance at least d precisely when K is no larger than the product of the first n - d + 1 moduli.

If K exceeds that prefix product, the messages zero and the prefix product both lie in the range and agree on those first coordinates, leaving fewer than d disagreements. This supplies the concrete obstruction to any larger dynamic range.

For the converse, a pair at distance below d agrees on at least n - d + 1 coordinates. Coprimality makes the product of their selected moduli divide the positive message difference, while monotonicity makes that selected product at least the initial prefix product. The assumed range bound then puts K below the difference, contradicting that both messages lie below K.

## References

- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeDynamicRange.agree_on_iff_prod_dvd`
- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeDynamicRange.fin_index_le_strict_mono`
- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeDynamicRange.maximum_dynamic_range_iff_min_distance`
