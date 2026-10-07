# Exact Sparse Off-Diagonal

## Abstract

Exact Sparse Off-Diagonal

**Theorem 1.1 (Exact Sparse Off-Diagonal).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \left(\left(\left(0 < a \land \operatorname{mod}\left(a, 2\right) = 1\right) \land \operatorname{mod}\left(b, 2\right) = 1\right) \land 2 \cdot a + 1 \le b\right) \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda k:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(k\right)\right)\right)\right) = a + b$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal.offdiagonal_exact_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive odd a and odd b at least 2a+1, the prefix palindromic length of the sparse integer with binary expansion (100)^a(10)^b equals a+b. The constructed cut path attains the signed-weight lower bound.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal.offdiagonal_exact_family`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound](SignedCutLowerBound.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper](SparseFamilyUpper.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic](SparseInitialArithmetic.md)
