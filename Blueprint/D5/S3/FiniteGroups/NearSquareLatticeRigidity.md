# Rigidity from adjacent columns and quotient index

## Abstract

Near maximal square coverings determine the actual integer relation lattice.

**Theorem 1.1 (The deficit is a product of two displacements).**

Lean statement: `D5/S3/FiniteGroups/NearSquareLatticeRigidity.near_square_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NearSquareLatticeRigidity.near_square_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok and W. Kyle Beatty (2025). *On the diameter of undirected Cayley graphs of finite abelian groups*. DOI: [10.2140/cnt.2025.14.1](https://doi.org/10.2140/cnt.2025.14.1). URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let L be an integer submodule of Z², n and δ integers with n ≥ 2 and 0 ≤ δ < n. Assume the actual quotient Z²/L has order n²−δ, and every coset has a representative (x,y) with 0 ≤ x,y < n. Then there are integers 0 ≤ a,b < n and ε equal to 1 or −1 such that ab=δ and L is exactly the integer span of (n,−εb) and (−a,εn). The strict deficit bound is part of the hypothesis.

If L contains a horizontal vector (p,0) with 0<p≤n, square coverage and the index bound force p=n and δ=0 and give the displayed basis directly, with b=0 and ε=1. If L contains no such horizontal vector, the least positive and negative vertical displacements between adjacent columns give vectors (p,−b) and (q,c). Square coverage forces b+c ≤ n. Their positive determinant is divisible by the actual quotient index and is at most n². Since δ<n, the determinant must equal n²−δ; the same bounds then force b+c=n and p=n or q=n. Taking a difference of vectors produces the displayed basis, up to a vertical reflection, and the missing area factors as ab. Equality of indices upgrades containment to equality of lattices.

This controls every lattice satisfying the covering and index hypotheses. It supplies the rigidity needed to exclude arbitrary Cayley generating pairs.

For integer vectors u,v with nonzero determinant, the index of their integer span is the natural absolute value of u₀v₁−u₁v₀. The helper span_pair_index applies pinned Mathlib's Submodule.natAbs_det_basis_change, with linear independence from Matrix.linearIndependent_rows_of_det_ne_zero. It is reused in the rigidity proof and in the index calculation for the sum-and-difference map; the determinant-index identity is credited to Mathlib.

## References

- Truth anchor: `D5/S3/FiniteGroups/NearSquareLatticeRigidity.near_square_rigidity`
