# Regular Traces of Weighted Products

## Abstract

The regular trace extracts the identity coefficient of an ordered product in a finite group algebra.

**Theorem 1.1 (The general regular trace identity).**

Lean statement: `D5/S3/FiniteGroups/RegularRepresentation/RegularTrace.trace_lmul_list_prod`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RegularRepresentation/RegularTrace.trace_lmul_list_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be any commutative ring with identity and H any finite group. For an arbitrary ordered list a of elements of the group algebra R[H], let L_b be the R-linear endomorphism given by left multiplication by b. Then the trace of the ordered product of the L_b is the cardinality of H, viewed in R, times the coefficient of the group identity in the ordered product of a.

Each factor can have arbitrary weights in R. No characteristic or nontriviality condition is needed. Lists of length k express every k >= 0. For the empty list, both products are their respective identities, the identity coefficient is one, and the trace is the cardinality of H in R.

In the standard basis indexed by H, the matrix entry in row x and column y of L_b is the coefficient of x times the inverse of y in b. Every diagonal entry is therefore the identity coefficient of b. Summing over H proves the trace formula. Multiplicativity of left multiplication identifies the operator product with left multiplication by the algebra product.

The proof uses the standard group-algebra basis, the coefficient formula for multiplication by a basis vector, and the equality between linear-map trace and matrix trace. These are the pinned Mathlib declarations MonoidAlgebra.basis, MonoidAlgebra.coeff_mul_single_apply, Algebra.toMatrix_lmul', and LinearMap.trace_eq_matrix_trace. The diagonal trace argument is the finite-group case of TauCeti's trace_leftMulMatrix_monoidAlgebra, whose immutable source and Apache 2.0 license are listed in Library/FiniteGroups/tauceti2026finitecharacters.md.

## References

- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/RegularTrace.trace_lmul_list_prod`
