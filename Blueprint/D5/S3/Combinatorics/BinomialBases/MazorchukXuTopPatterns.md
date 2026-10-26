# The top coefficient and the complete Mazorchuk–Xu conjecture

## Abstract

The top weak-coordinate patterns are exactly a choice of position values and a permutation of the complementary cutoff values. Their factorial count proves the complete original all-deficit, all-valid-rank numerical polynomial conjecture for the literal triangular family.

**Theorem 1.1 (Exact factorial count of the top patterns).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \operatorname{factorial}\left(i\right) \cdot \operatorname{patternCoefficient}\left(i, \operatorname{two}\left(\right) \cdot i\right) = \operatorname{factorial}\left(\operatorname{two}\left(\right) \cdot i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.patternCoefficient_top_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

A full positive support of size 2i forces all 2i position and cutoff entries to be positive and pairwise distinct: removing zero and taking the union can otherwise not attain cardinality 2i. Thus the position entries increase strictly. The generic coordinate criterion gives exactly one exceptional-bit set. Choose its i position values as an i-subset of 1 through 2i, enumerate them in increasing order, and biject the i labelled cutoffs with the complementary values. The implemented finite bijection proves a(i,2i)=choose(2i,i)*i!. Mathlib card_finset_len, card_equiv and add_choose_mul_factorial_mul_factorial then give the displayed identity. Empty positions, empty complementary sets and i=0 are covered by the same construction.

**Theorem 1.2 (The original all-deficit polynomial statement).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \exists p \in \operatorname{Polynomial}\left(\operatorname{Rat}\left(\right)\right),\; ((\operatorname{natDegree}\left(p\right) = \operatorname{two}\left(\right) \cdot i) \land (\operatorname{leadingCoeff}\left(p\right) = \operatorname{inv}\left(\operatorname{ratCast}\left(\operatorname{factorial}\left(i\right)\right)\right))) \land (\forall n \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\operatorname{eval}\left(p, \operatorname{ratCast}\left(n\right)\right) = \operatorname{ratCast}\left(\operatorname{count}\left(n, n + \operatorname{one}\left(\right) - i\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/mazorchuk-xu-2026-first-column-deficit-polynomial` (proved) by `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mazorchuk-xu-2026-first-column-deficit-polynomial","declaration_gid":"D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Take the actual countingPolynomial from the full weak-coordinate binomial sum. Its evaluation theorem applies to every natural n with i<=n+1, with no eventual threshold. The top factorial identity makes its coefficient at degree 2i equal to the nonzero rational inverse of i!, so its degree bound is attained and its leading coefficient is 1/i!. The conclusion is the original Conjecture defined in MazorchukXuClosure, whose count is the cardinality of the literal triangular subsets satisfying both conclusions of Condition (star), including repeated points. The proof retains empty subsets and rows, zero and tied coordinates, n=0, i=0, and i=n+1; it never evaluates a source family at n=-1. Mazorchuk and Xu supply the question and the already known first four deficit formulas. The coordinate-pattern argument supplies the general proof; no originality, priority or completed later-literature census is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.patternCoefficient_top_factorial`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial](MazorchukXuPolynomial.md)
