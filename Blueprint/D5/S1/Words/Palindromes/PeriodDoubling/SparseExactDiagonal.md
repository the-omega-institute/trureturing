# Exact Sparse Diagonal

## Abstract

Exact Sparse Diagonal

**Theorem 1.1 (Exact Sparse Diagonal).**

$$\forall a \in \mathbb{N},\; \left(0 < a \land \operatorname{mod}\left(a, 2\right) = 1\right) \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda k:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot \operatorname{Nat.sub}\left(2 \cdot a, 1\right) + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(\operatorname{Nat.sub}\left(2 \cdot a, 1\right)\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(k\right)\right)\right)\right) = 3 \cdot a$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal.diagonal_exact_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive odd a, the sparse integer whose binary expansion is (100)^a followed by (10)^(2a minus one) has prefix palindromic length 3a. The signed-weight lower bound is 3a minus one. The marked charge obstruction excludes attainment of that lower bound; the explicit sparse cut path supplies the matching upper bound. Nat.sub denotes truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal.diagonal_exact_family`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction](MarkedPathObstruction.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper](SparseFamilyUpper.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic](SparseInitialArithmetic.md)
