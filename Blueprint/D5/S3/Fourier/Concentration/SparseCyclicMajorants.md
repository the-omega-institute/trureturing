# Sparse Fourier Support of a Nonnegative Cyclic Majorant

## Abstract

A finite Fourier support bounds the mean of a nonnegative cyclic majorant.

Let q be a positive integer and K a nonnegative real function on the cyclic group of order q. Let S be a set of frequencies containing every nonzero coefficient of the unnormalized discrete Fourier transform of K. Write M for the sum of K over the group and A(k,x) for the real part of the standard character evaluated at −xk modulo q.

Let R be any subset on which K is at least one.

**Theorem 1.1 (A lower bound with a correction from the set being majorized).**

$$\sum_{k \in S} \sum_{x \in R} (1-\operatorname{A}\left(k, x\right)) \leq \left|S\right| \cdot M-q \cdot \operatorname{K}\left(0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SparseCyclicMajorants.sparse_dft_majorant_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fourier inversion at zero expresses the right side as the double sum over S and the entire cyclic group with terms K(x) times (1−A(k,x)). Each term is nonnegative. Restrict to R and use K(x) at least one.

For the equality criterion assume K(0) is positive. Write SubgroupForm(K,S) for the existence of an additive subgroup H such that K equals K(0) on H and zero outside H, with S equal to the annihilator of H. The annihilator consists of the frequencies whose characters are one on H.

**Theorem 1.2 (Equality in the mean bound).**

$$\left|S\right| \cdot M = q \cdot \operatorname{K}\left(0\right) \iff \operatorname{SubgroupForm}\left(K, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SparseCyclicMajorants.sparse_dft_floor_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under equality, all phase terms with positive K(x) vanish. The support of K is therefore contained in the subgroup where every selected character is one. Inversion makes K constant on that subgroup. Every frequency in its annihilator has the same positive coefficient M and thus belongs to S. Conversely the phase terms vanish for a scaled subgroup indicator with its annihilator as the frequency set.

Positive height is needed for the equality criterion. For q=2 and K=0, equality holds with S={1}. Every annihilator contains the zero frequency.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/SparseCyclicMajorants.sparse_dft_floor_eq_iff`
- Truth anchor: `D5/S3/Fourier/Concentration/SparseCyclicMajorants.sparse_dft_majorant_gap`
- Dependency: [D5/S3/Fourier/FinitePoisson](../FinitePoisson.md)
