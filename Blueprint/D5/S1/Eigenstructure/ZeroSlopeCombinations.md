# Zero-Slope Combinations

## Abstract

Nonzero drift slopes have a codimension-one zero-slope combination space.

**Theorem 1.1 (Zero-slope combinations have codimension one).**

$$\forall ell: \mathbb{N},\ \forall s: \operatorname{Dual}(\mathbb{R}^{ell}),\ s \neq 0 \Rightarrow \operatorname{dim}_{\mathbb{R}}(\operatorname{ker}(s)) + 1 = ell.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/ZeroSlopeCombinations.zero_slope_combinations_finrank_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be a nonzero real linear functional on the coefficient space of a finite cycle of length ell. Its kernel is the space of linear combinations whose total drift slope is zero. The dimension of this kernel plus one is ell.

Pinned Mathlib was searched before proving. The exact codimension-one result Module.Dual.finrank_ker_add_one_of_ne_zero was found and is applied directly; Module.finrank_fin_fun identifies the ambient dimension with the cycle length.

This closes only the source atom's claim that zero-slope combinations on the cycle form an ell-minus-one-dimensional space. The neighboring closed forms, compatibility identity, and erratum are not claimed here.

## References

- Truth anchor: `D5/S1/Eigenstructure/ZeroSlopeCombinations.zero_slope_combinations_finrank_add_one`
