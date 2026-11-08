# Original charged commutators in a fixed Sobolev operator space

## Abstract

Original charged commutators in a fixed Sobolev operator space

Mathlib supplies completion, normed operators, Fourier analysis, integer binomial identities and unconditional sum machinery under Apache 2.0. The additional arguments here concern the stated original objects and relations. No literature novelty or physical realization is asserted.

**Theorem 1.1 (modeProduct embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, charges a,b, natural k, integers m,n and original finite carrier vector v, the bounded product A_a^k(m) A_b^(r+k)(n) evaluated at embed_(r+s+k)(v) equals embed_k(A_a(m)(A_b(n)v)). Source transport is equality of Sobolev orders.

**Theorem 1.2 (reverseModeProduct embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse ordered bounded product evaluates on the same embed_(r+s+k)(v) to embed_k(A_b(n)(A_a(m)v)), for every original input and integer modes.

**Theorem 1.3 (modeCommutator embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-space bounded commutator evaluates on each original finite carrier input to the embedding of the actual algebraic charged-mode commutator.

**Theorem 1.4 (modeCommutator iterate embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_iterate_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_iterate_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j and integers m,n, evaluation of delta^j of the bounded commutator agrees with embed_k of delta^j of the actualField commutator at the exact shifted indices m+chargeEnergy(a)-1 and n+chargeEnergy(b)-1. This heterogeneous evaluation identity is proved by induction on j.

**Theorem 1.5 (modeCommutator delta).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_delta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, charges a,b and k, delta^N of the bounded commutator in B(H_(r+s+k),H_k) is zero, N=(-bilinear(a,b)).toNat. The actual algebraic charged locality theorem transfers through the proved iterate identity and density of the original carrier embedding, including N=0.

**Theorem 1.6 (modeProduct norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer-mode first product has norm at most C_a*C_b*(1+abs(m))^(r+k)*(1+abs(n))^(r+s+k). The constants are the actual original mode constants fixed before the modes and input.

**Theorem 1.7 (reverseModeProduct norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse product has norm at most C_a*C_b*(1+abs(m))^(r+s+k)*(1+abs(n))^(s+k), with the same original constants and source order.

**Theorem 1.8 (modeCommutator norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original bounded commutator has norm at most 2*C_a*C_b*(1+abs(m))^(r+s+k)*(1+abs(n))^(r+s+k). This uses the two complementary ordered-product estimates without increasing the source order by N.

**Theorem 1.9 (modeProductTerm le).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProductTerm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProductTerm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm of fhat(m)*ghat(n) acting on the first ordered mode product is at most C_a*C_b*weight_(r+k)(f,m)*weight_(r+s+k)(g,n).

**Theorem 1.10 (reverseModeProductTerm le).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProductTerm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProductTerm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse ordered term has norm at most C_a*C_b*weight_(r+s+k)(f,m)*weight_(s+k)(g,n).

**Theorem 1.11 (modeProduct absolute).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_absolute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, charges, Tests and k, the norm series of the first ordered product terms is summable on the full Z x Z, before any interchange.

**Theorem 1.12 (reverseModeProduct absolute).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_absolute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm series of the reverse ordered product terms is summable on the same Z x Z, with the complementary weights.

**Theorem 1.13 (modeCommutator absolute).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_absolute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original commutator-term norm series is summable on all Z x Z, by the two ordered absolute series and the triangle inequality.

**Theorem 1.14 (smearComposition eq tsum).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smearComposition_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smearComposition_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal first bounded composition of original infinite smears equals the sum over all integer pairs of its ordered mode-product terms. Continuous bilinear composition maps each summable operator series through the other, and joint absolute summability justifies the product-index sum.

**Theorem 1.15 (reverseSmearComposition eq tsum).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseSmearComposition_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseSmearComposition_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal reverse bounded composition on the same H_(r+s+k) equals the corresponding reverse-product series indexed by the same ordered pair (m,n), after its own absolute-convergence proof.

**Theorem 1.16 (smear comp eq double tsum).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smear_comp_eq_double_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smear_comp_eq_double_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of the two literal compositions H_(r+s+k)->H_k equals the double series of fhat(m)*ghat(n) acting on the original fixed-space mode commutator. Both ordered double series and their difference are absolutely norm summable; the sign is AB-BA.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_delta`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_iterate_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeCommutator_norm`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProductTerm_le`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.modeProduct_norm`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProductTerm_le`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseModeProduct_norm`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.reverseSmearComposition_eq_tsum`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smearComposition_eq_tsum`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator.smear_comp_eq_double_tsum`
- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalSmoothFields](OriginalSmoothFields.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualChargedLocality](../LatticeActualChargedLocality.md)
