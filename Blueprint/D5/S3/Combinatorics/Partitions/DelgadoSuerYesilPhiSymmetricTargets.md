# Symmetric targets of pseudo-Frobenius row deletion

## Abstract

Symmetric numerical sets with Frobenius number 2h - 1 number 2^(h-1), and the half of them containing 1 lie outside the pseudo-Frobenius row-deletion image.

**Theorem 1.1 (Counting the symmetric targets).**

Lean statement: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A negative answer to Delgado, Süer and Yeşil's symmetrization question*. DOI: [10.5281/zenodo.24391331](https://doi.org/10.5281/zenodo.24391331). URL: <https://doi.org/10.5281/zenodo.24391331>.

*Commentary.*

No symmetric numerical set has even Frobenius number. For every h ≥ 1 there are exactly 2^(h-1) symmetric numerical sets with Frobenius number 2h - 1. For every h ≥ 2 exactly 2^(h-2) of them contain 1, exactly 2^(h-2) omit 1, and at least 2^(h-2) of them are not the row deletion Φ(S) of any proper numerical semigroup S. The only numerical set with Frobenius number 1 is ℕ₀ ∖ {1}, which is Φ of an almost symmetric semigroup. This is Corollary 2 of H. Ma and W. Zhang (version 2); the total count is due to J. Marzuola and A. Miller. The exclusion is stated there for almost symmetric sources and holds for every proper numerical semigroup.

Symmetry pairs a with 2h - 1 - a for 0 ≤ a ≤ 2h - 1, so the middle point of an even Frobenius number would have to be both a member and a gap. With Frobenius number 2h - 1 the set is determined by its gaps below h, and every subset of {1, …, h - 1} occurs: put each chosen a among the gaps and each unchosen a's partner 2h - 1 - a among the gaps, together with 2h - 1. The sets containing 1 correspond to the subsets of {2, …, h - 1}, and those omitting 1 to the remaining 2^(h-2) subsets. Since Φ(S) never contains 1 for a proper numerical semigroup S, none of these is a row deletion.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets.result`
- Dependency: [D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber](DelgadoSuerYesilPhiOrdinaryFiber.md)
