# PanSkanderaWangAllSplitsBijection

## Abstract

The target family consists of one-based permutation words whose entry parity equals their one-based position parity.

**Definition 1.1 (B).**

$$\forall n \in \mathbb {N},\; \forall x \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{B}\left(n, x\right)) \Leftrightarrow ((\operatorname{IsPerm}\left(n, x\right)) \land (\forall k \in \mathbb {N},\; \forall hk \in k < \operatorname{length}\left(x\right),\; \operatorname{getElem}\left(x, k, hk\right) \bmod 2 = \left(k + 1\right) \bmod 2))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.B` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Source, Section 7 (p. 145): “We call the set that consists of u = u₁⋯uₙ satisfying the above conditions 𝔅ₙ, i,e,” followed by “𝔅ₙ = {u ∈ 𝔖ₙ | u₁u₂⋯uₙ takes odd and even integers alternately and u₁ is odd}”. The target family consists of one-based permutation words whose entry parity equals their one-based position parity. The proof hk supplies the list index bound.

**Theorem 1.2 (f injective).**

$$\forall n \in \mathbb {N},\; (4 \le n) \Rightarrow (\forall w \in \operatorname{List}\left(\mathbb {N}\right),\; \forall z \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{A}\left(n, w\right)) \Rightarrow ((\operatorname{A}\left(n, z\right)) \Rightarrow ((\operatorname{f}\left(n, w\right) = \operatorname{f}\left(n, z\right)) \Rightarrow (w = z))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.f_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

For every order at least four, the recursive map is injective on the literal source family. Recovering the maximum insertion position and the pair-swapped suffix reduces equality of outputs to equality at the preceding order.

**Theorem 1.3 (f image B).**

$$\forall n \in \mathbb {N},\; (4 \le n) \Rightarrow (\forall w \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{A}\left(n, w\right)) \Rightarrow (\operatorname{B}\left(n, \operatorname{f}\left(n, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.f_image_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

For every order at least four, the algorithm maps each source word to a word in the literal parity family. Pair swapping changes the parity offset on an even suffix, and reverse-complementation preserves the target family.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.B`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.f_image_B`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.f_injective`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord](PanSkanderaWangAllSplitsWord.md)
