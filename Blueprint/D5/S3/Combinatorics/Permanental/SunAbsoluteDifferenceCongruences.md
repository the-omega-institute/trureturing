# Sun's absolute-difference permanent congruences

## Abstract

Both absolute-difference permanent congruences in Sun Conjecture 4.2(i).

**Definition 1.1 (A).**

$$\forall p \in \mathbb{N},\; \forall s \in \mathbb{Z},\; \forall j \in \operatorname{Fin}\left(p\right),\; \forall k \in \operatorname{Fin}\left(p\right),\; \operatorname{A}\left(p, s, j, k\right) = \lvert (\operatorname{val}\left(j\right):\mathbb{Z}) + 1 - \left((\operatorname{val}\left(k\right):\mathbb{Z}) + 1\right) + s\rvert $$

*Formalization.* `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.A` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2022). *Arithmetic properties of some permanents*. DOI: [10.48550/arXiv.2108.07723](https://doi.org/10.48550/arXiv.2108.07723). URL: <https://arxiv.org/abs/2108.07723v7>.

*Commentary.*

The matrices in (4.3) and (4.4), p. 25, are “per[|j − k|]” and “per[|j − k + 1|]”, with 1 ⩽ j,k ⩽ p. The integer shift s unifies their entries. Source indices are val(j)+1 and val(k)+1; each value is cast to ℤ before subtraction and absolute value.

**Definition 1.2 (claim).**

$$claim = (\forall p \in \mathbb{N},\; \operatorname{Nat.Prime}\left(p\right) \Rightarrow \left(\operatorname{Odd}\left(p\right) \Rightarrow \left(((p:\mathbb{Z}) \mid (2 \cdot \operatorname{Matrix.permanent}\left(\operatorname{A}\left(p, 0\right)\right) + 1)) \land ((p:\mathbb{Z}) \mid (2 \cdot \operatorname{Matrix.permanent}\left(\operatorname{A}\left(p, 1\right)\right) - 1))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.claim` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2022). *Arithmetic properties of some permanents*. DOI: [10.48550/arXiv.2108.07723](https://doi.org/10.48550/arXiv.2108.07723). URL: <https://arxiv.org/abs/2108.07723v7>.

*Commentary.*

Conjecture 4.2(i), p. 25: “(i) For any odd prime p, we have per[|j − k|]₁⩽ⱼ,ₖ⩽ₚ ≡ −½ (mod p) and per[|j − k + 1|]₁⩽ⱼ,ₖ⩽ₚ ≡ ½ (mod p).” The displays are (4.3) and (4.4), respectively.

Nat.Prime and Odd express exactly an odd prime. Matrix.permanent uses the sum of column-indexed permutation products, equal to the source's row-indexed sum by inversion of the permutation. Since 2 is invertible modulo an odd prime, the two integer divisibilities are precisely (4.3) and (4.4). The same p serves both conjuncts.

**Theorem 1.3 (result).**

$$\forall p \in \mathbb{N},\; \operatorname{Nat.Prime}\left(p\right) \Rightarrow \left(\operatorname{Odd}\left(p\right) \Rightarrow \left(((p:\mathbb{Z}) \mid (2 \cdot \operatorname{Matrix.permanent}\left(\operatorname{A}\left(p, 0\right)\right) + 1)) \land ((p:\mathbb{Z}) \mid (2 \cdot \operatorname{Matrix.permanent}\left(\operatorname{A}\left(p, 1\right)\right) - 1))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2022). *Arithmetic properties of some permanents*. DOI: [10.48550/arXiv.2108.07723](https://doi.org/10.48550/arXiv.2108.07723). URL: <https://arxiv.org/abs/2108.07723v7>.

*Commentary.*

Alternating row and column signs give circulants without changing their permanents. A prime-order fixed-point count on the permutation-weight fibers leaves only translations in characteristic p. Fermat's identity and a telescoping alternating sum then evaluate both permanents. The prime circulant ingredient is the Brualdi–Newman congruence; the two absolute-difference reductions yield the stated divisibilities.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.A`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.result`
