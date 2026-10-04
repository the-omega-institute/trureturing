# PanSkanderaWangAllSplitsBlock

## Abstract

A permutation preserves a block exactly when membership before and after its action agrees at every index.

**Definition 1.1 (Preserves).**

$$\forall alpha \in Type*,\; [\operatorname{DecidableEq}\left(alpha\right)] \forall s \in \operatorname{Finset}\left(alpha\right),\; \forall w \in \operatorname{Perm}\left(alpha\right),\; (\operatorname{Preserves}\left(s, w\right)) \Leftrightarrow (\forall i \in alpha,\; (w\left(i\right) \in s) \Leftrightarrow (i \in s))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.Preserves` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

A permutation preserves a block exactly when membership before and after its action agrees at every index. The anonymous bracket is the Lean DecidableEq instance; alpha is an arbitrary type.

**Definition 1.2 (blockEquiv).**

$$\forall alpha \in Type*,\; [\operatorname{DecidableEq}\left(alpha\right)] \forall s \in \operatorname{Finset}\left(alpha\right),\; (\forall sigma \in \operatorname{Perm}\left(s\right),\; \forall tau \in \operatorname{Perm}\left(\operatorname{Subtype}\left(alpha, fun (i : alpha) \mapsto \neg (i \in s)\right)\right),\; \operatorname{val}\left(\operatorname{blockEquiv}\left(s\right)\left(\operatorname{pair}\left(sigma, tau\right)\right)\right) = \operatorname{ofSubtype}\left(sigma\right) \cdot \operatorname{ofSubtype}\left(tau\right)) \land (\forall w \in \operatorname{Subtype}\left(\operatorname{Perm}\left(alpha\right), fun (w : \operatorname{Perm}\left(alpha\right)) \mapsto \operatorname{Preserves}\left(s, w\right)\right),\; \operatorname{symm}\left(\operatorname{blockEquiv}\left(s\right)\right)\left(w\right) = \operatorname{pair}\left(\operatorname{subtypePerm}\left(\operatorname{val}\left(w\right), \operatorname{property}\left(w\right)\right), \operatorname{subtypePerm}\left(\operatorname{val}\left(w\right), fun (i : alpha) \mapsto \operatorname{notCongr}\left(\operatorname{property}\left(w\right)\left(i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.blockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The forward defining expression extends the two subtype permutations by identity and multiplies them. The inverse defining expression restricts the block-preserving permutation to the block and its complement. val and property are the two subtype projections; the inverse laws are verified in Lean.

**Theorem 1.3 (permanent block expansion).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{principalPermanent}\left(A, s\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus s\right) = \operatorname{sum}\left(fun (w : \operatorname{Subtype}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), fun (v : \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{Preserves}\left(s, v\right)\right)) \mapsto \operatorname{monomial}\left(A, \operatorname{val}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.permanent_block_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The product of the complementary principal permanents equals the sum over all block-preserving permutation monomials. The constructed block equivalence identifies the two independently chosen permutations with a single permutation of the whole index set.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.Preserves`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.blockEquiv`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.permanent_block_expansion`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord](PanSkanderaWangAllSplitsWord.md)
