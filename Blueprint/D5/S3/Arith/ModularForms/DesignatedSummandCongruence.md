# Exact dyadic divisibility for designated summands

## Abstract

The exact common power of two on degrees congruent to three modulo four is determined for every positive tuple count.

The ordered marked count is the degree coefficient of the corresponding power of F. For odd k the reciprocal dissection kills the missing residue after dilating the power k+1. When four divides k, dyadic dilation kills every odd degree at the required modulus. For k congruent to two modulo four, the square dissection and divisibility of the odd coefficients of W give the remaining bounds.

**Theorem 1.1 (Degree seven in the exceptional class).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandCongruence.exceptional_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandCongruence.exceptional_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For every natural k congruent to 2 modulo 16, the degree-seven coefficient of F to the power k is 8 modulo 16. Modulo 16, F to the power 64 has constant coefficient one and zero coefficients in degrees one through seven. For every natural k, the degree-seven coefficient of F to the power k modulo 16 therefore depends only on k modulo 64. Convolution modulo 16 through degree seven gives residue 8 for each of the four classes 2, 18, 34 and 50 modulo 64.

**Theorem 1.2 (Common dyadic exponent).**

$$\forall k \in \mathbb{N}, e \in \mathbb{N},\; 0 < k \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 2^{e} \mid \operatorname{markedCount}\left(k, 4 \cdot n + 3\right)\right) \Leftrightarrow e \le (\operatorname{if} k \bmod 16 = 2 \operatorname{then} 3 \operatorname{else} \operatorname{padicValNat}\left(2, \operatorname{markedCount}\left(k, 3\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandCongruence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For every positive k, the largest power of 2 dividing all Aₖ(4n+3) is 2 to the valuation of Aₖ(3) when k is not congruent to 2 modulo 16, and exactly 2³ when k is congruent to 2 modulo 16. Degree three attains the first bound and degree seven attains the second.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandCongruence.exceptional_sharp`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandCongruence.result`
- Dependency: [D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection](DesignatedSummandEtaDissection.md)
