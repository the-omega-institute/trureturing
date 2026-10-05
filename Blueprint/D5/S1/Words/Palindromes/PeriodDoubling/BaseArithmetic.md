# Arithmetic Meaning of the Base Transducer

## Abstract

The f charges on accepted paths equal the signed-weight difference of the encoded rounded halves.

**Theorem 1.1 (Path charge is the exact signed-weight difference).**

$$\forall charge \in \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \left(s \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(charge\right)\right) \land t \in \operatorname{accept}\left(\operatorname{baseAutomaton}\left(charge\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(charge\right), s, t, xs\right),\; \operatorname{pathCharge}\left(\lambda [\operatorname{Fin}\left(1492\right)] a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} [\operatorname{Fin}\left(1492\right)] \mapsto \operatorname{fst}\left(a\right), p\right) = \operatorname{cast}\left(\operatorname{signedWeight}\left(\operatorname{foldr}\left(a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto x:\mathbb{Z} \mapsto \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(a\right)\right)\right) + 2 \cdot x, 0, xs\right) + \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s\right)\right)\right), 2\right), 0\right)\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{signedWeight}\left(\operatorname{foldr}\left(a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto x:\mathbb{Z} \mapsto \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(a\right)\right)\right) + 2 \cdot x, 0, xs\right) + \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s\right)\right)\right), 3\right), 0\right)\right), \mathbb{Z}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic.base_path_signed_weight_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third and fourth edge coordinates encode successive binary digits, least significant first, above the endpoint's bit zero. Folding a + 2 x reconstructs the shifted integer. Source components 2 and 3 supply the fixed bit-zero parities, so adding them reconstructs the two rounded halves. The carry identities and the forced even remainder after a nonzero signed digit give the signed-weight change at each edge; path induction telescopes it. cast denotes the natural-to-integer embedding. This theorem identifies f weights and does not assert that all legal palindrome cuts have already been represented by accepted paths.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic.base_path_signed_weight_difference`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates](BaseCertificates.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight](SignedWeight.md)
