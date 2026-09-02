# Cayley Equivalence of de Branges and Nevanlinna Kernels

## Abstract

A positive shifted Cayley transform identifies the de Branges and Nevanlinna kernels through an invertible diagonal gauge.

**Theorem 1.1 (Exact pointwise gauge identity).**

$$omega>0, \forall x, 1+\operatorname{theta}\left(x\right)\neq0 \Rightarrow \operatorname{nevanlinnaKernel}\left(z, w\right)=\frac{\frac{4\pi}{omega}\operatorname{deBrangesKernel}\left(z, w\right)}{(1+\operatorname{theta}\left(z\right))(1+\overline{\operatorname{theta}\left(w\right)})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.cayley_nevanlinna_kernel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For omega > 0 and 1 + theta(x) nonzero, direct Cayley algebra gives the exact factor 4 pi / omega and the two nonvanishing gauge denominators.

No cross-denominator premise is needed. If z - conjugate(w) vanishes, both totalized kernel quotients are zero; otherwise the ordinary field calculation applies.

**Theorem 1.2 (Finite Gram positivity is equivalent).**

$$omega>0, \forall x, 1+\operatorname{theta}\left(x\right)\neq0 \Rightarrow \forall n, z_1, \cdot, z_n, \operatorname{PosSemidef}\left([\operatorname{deBrangesKernel}\left(z_i, z_j\right)]\right) \Leftrightarrow \operatorname{PosSemidef}\left([\operatorname{nevanlinnaKernel}\left(z_i, z_j\right)]\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.cayley_nevanlinna_kernel_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every finite sample, the Nevanlinna Gram matrix is U K U* where U is the diagonal gauge containing sqrt(4 pi / omega). Positivity of omega and nonvanishing of 1 + theta make U invertible, so positive semidefiniteness holds in both directions.

**Theorem 1.3 (A vanishing gauge denominator breaks the identity).**

$$\operatorname{theta}\left(0\right)=-1, \forall x\neq0, \operatorname{theta}\left(x\right)=0 \Rightarrow \operatorname{nevanlinnaKernel}\left(0, 1\right)\neq\frac{4\pi\operatorname{deBrangesKernel}\left(0, 1\right)}{(1+\operatorname{theta}\left(0\right))(1+\overline{\operatorname{theta}\left(1\right)})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.gauge_nonvanishing_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit function theta(0) = -1 and theta(x) = 0 away from zero makes the Cayley quotient totalize to zero at one endpoint while the uncancelled Nevanlinna difference remains nonzero. Thus the gauge premise cannot be omitted.

## References

- Truth anchor: `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.cayley_nevanlinna_kernel_identity`
- Truth anchor: `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.cayley_nevanlinna_kernel_posSemidef_iff`
- Truth anchor: `D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.gauge_nonvanishing_is_necessary`
- Dependency: [D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion](../../Analytic/Characterizations/ShiftedHerglotzCriterion.md)
