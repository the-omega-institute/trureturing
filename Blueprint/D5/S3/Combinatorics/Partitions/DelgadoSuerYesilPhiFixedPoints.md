# Fixed points of pseudo-Frobenius row deletion

## Abstract

The pseudo-Frobenius row deletion fixes exactly the symmetric numerical semigroups, which are the semigroups of type one and are almost symmetric.

**Theorem 1.1 (The fixed-point characterization).**

Lean statement: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A negative answer to Delgado, Süer and Yeşil's symmetrization question*. DOI: [10.5281/zenodo.24391331](https://doi.org/10.5281/zenodo.24391331). URL: <https://doi.org/10.5281/zenodo.24391331>.

*Commentary.*

Let U be a proper numerical set with Frobenius number F, genus g and pseudo-Frobenius set PF(U), and let Φ delete the rows labelled by PF(U) other than F, relabelling each retained gap by subtracting the number of deleted gaps below it. If U is symmetric, then Φ(U) = U as subsets of the naturals, F is its only pseudo-Frobenius number and 2g = F + 1. If U is a numerical semigroup, conversely Φ(U) = U holds if and only if U is symmetric, which holds if and only if PF(U) = {F}, and a symmetric U is almost symmetric. This is Corollary 3 of H. Ma and W. Zhang (version 2); the case F = 1 is included, and the forward direction is stated for every symmetric numerical set.

For a gap a, the largest gap b with b − a in S is pseudo-Frobenius, since adding a positive member s to b would give a larger such gap. If PF(S) = {F}, this gives F − a in S for every gap a, while a and F − a cannot both lie in S because their sum F is a gap; so S is symmetric. Conversely, if S is symmetric and f < F is a gap, F − f lies in S and f + (F − f) = F is a gap, so f is not pseudo-Frobenius. When PF(S) = {F} no row is deleted and Φ(S) = S. If Φ(S) = S, the deleted gap set equals the original one, so the retained rows are all the gaps and every pseudo-Frobenius number equals F. Reflection a ↦ F − a exchanges the members and the gaps in {0, …, F}, which gives 2g = F + 1 and, with |PF(S)| = 1, almost symmetry.

The semigroup hypothesis is needed for the converse: the numerical set with the single gap 2 has F = 2 as its only pseudo-Frobenius number, so Φ fixes it, but it is not symmetric since 1 and 2 − 1 are both members. This example is not compiled.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints.result`
- Dependency: [D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation](DelgadoSuerYesilPhiRefutation.md)
