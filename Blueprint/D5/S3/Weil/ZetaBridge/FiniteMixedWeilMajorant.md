# Finite Mixed Weil Majorant

Status: Candidate source and author projection.

For a finite basis k_i define the actual mixed terms

`M_ij(n) = zeroSummand Z (convolve (k_i) (involution (k_j))) n`.

Every M_ij is absolutely summable by the existing zeta summability theorem. The complete coefficient expansion is

`s_n(a) = sum_ij a_i conjugate(a_j) M_ij(n)`.

With `E(a)=sum_i |a_i|^2` and `B(n)=sum_ij |M_ij(n)|`, the module proves

`|s_n(a)| <= E(a) B(n)` and `sum_n |s_n(a)| <= E(a) C`, where `C=sum_n B(n)`.

B is proved summable. C depends on the fixed basis and includes every mixed term. It is not postulated as an operator-norm hypothesis.

Main declarations: `mixedWeilSummand_summable`, `zeroSummand_finite_synthesis_expansion`, `finiteMixedMajorant_summable`, `finite_synthesis_absolute_sum_le`.
