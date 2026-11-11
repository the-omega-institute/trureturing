# Centred product expansion

## Abstract

Alternating subset expansion of centred finite products in a commutative ring.

**Theorem 1.1 (Alternating subset expansion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion.prod_sub_one_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion.prod_sub_one_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite set D in an index type with decidable equality and any function F into a commutative ring, the product of F(d)-1 over D equals the sum over subsets J of D of (-1)^(|D|-|J|) times the product of F(d) over J. Mathlib's Finset.prod_add expands the factors; the complementary subset has cardinality |D|-|J|. This identity applies to prime correlations, Boolean-cube coordinate functions and finite-sieve variables.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion.prod_sub_one_expansion`
