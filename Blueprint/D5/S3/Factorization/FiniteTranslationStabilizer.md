# Finite Translation Stabilizers

## Abstract

Finite translation stabilizers act freely on their stabilized sets.

Let S be a finite subset of an additive commutative group G. Its translation stabilizer H consists of the elements t for which t+S=S. The cardinality statements require G to be finite.

**Theorem 1.1 (The cardinal annihilates a stabilizer).**

$$\operatorname{translate}\left(t, S\right) = S \implies \operatorname{card}\left(S\right)t = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FiniteTranslationStabilizer.card_nsmul_eq_zero_of_vadd_finset_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing all translated points gives |S|t+sum(S)=sum(S), so |S|t=0. This conclusion also applies when the ambient group is infinite.

**Theorem 1.2 (Stabilizer order divides set size).**

$$\operatorname{card}\left(H\right) \mid \operatorname{card}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FiniteTranslationStabilizer.stabilizer_card_dvd_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H acts freely on S: a translation fixing one point is zero. Partitioning S into H-orbits proves the divisibility.

**Theorem 1.3 (Maximal stabilizers give cosets).**

$$\operatorname{card}\left(H\right) = \operatorname{card}\left(S\right), p \in S \implies S = p + H$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FiniteTranslationStabilizer.eq_stabilizer_coset_of_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orbit of p lies in S, and translation makes its points distinct. Equal finite cardinalities make the orbit all of S.

**Theorem 1.4 (Three-point stabilizer cosets).**

$$\operatorname{card}\left(S\right) = 3, t \in H, t \neq 0, p \in S \implies S = p + H$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FiniteTranslationStabilizer.three_point_eq_stabilizer_coset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero member rules out stabilizer order one. Since the order divides three, it equals three, and S is the coset through any p in S.

**Theorem 1.5 (The full translation cycle).**

$$\operatorname{card}\left(S\right) = 3, \operatorname{translate}\left(t, S\right) = S, t \neq 0, p \in S \implies S = \{p, p + t, p + 2t\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FiniteTranslationStabilizer.three_point_eq_translation_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by t moves p around three distinct points and then returns to p. These points exhaust S.

## References

- Truth anchor: `D5/S3/Factorization/FiniteTranslationStabilizer.card_nsmul_eq_zero_of_vadd_finset_eq`
- Truth anchor: `D5/S3/Factorization/FiniteTranslationStabilizer.eq_stabilizer_coset_of_card_eq`
- Truth anchor: `D5/S3/Factorization/FiniteTranslationStabilizer.stabilizer_card_dvd_card`
- Truth anchor: `D5/S3/Factorization/FiniteTranslationStabilizer.three_point_eq_stabilizer_coset`
- Truth anchor: `D5/S3/Factorization/FiniteTranslationStabilizer.three_point_eq_translation_cycle`
