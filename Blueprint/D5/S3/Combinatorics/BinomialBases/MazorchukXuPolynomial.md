# The rational counting polynomial on every original rank

## Abstract

The literal weak-coordinate binomial identity constructs one rational polynomial valid on all original ranks. Its exact conjectured degree and leading coefficient require the top-pattern factorial identity proved in MazorchukXuTopPatterns.

**Definition 1.1 (The actual rational counting polynomial).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \operatorname{countingPolynomial}\left(i\right) = \operatorname{sum}\left(\operatorname{range}\left(\operatorname{two}\left(\right) \cdot i + \operatorname{one}\left(\right)\right), \operatorname{lambda}\left(k, \operatorname{C}\left(\operatorname{div}\left(\operatorname{ratCast}\left(\operatorname{patternCoefficient}\left(i, k\right)\right), \operatorname{ratCast}\left(\operatorname{factorial}\left(k\right)\right)\right)\right) \cdot \operatorname{comp}\left(\operatorname{descPochhammer}\left(\operatorname{Rat}\left(\right), k\right), \operatorname{add}\left(X, \operatorname{C}\left(\operatorname{one}\left(\right) - \operatorname{ratCast}\left(i\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Use the pinned Mathlib falling-factorial polynomial divided by k!, shift its variable by 1-i in the rationals, and weight by the actual admissible pattern count. The sum is finite through 2i. No count identity or top coefficient is an assumption in this definition.

**Theorem 1.2 (One polynomial agrees at every valid n).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\operatorname{eval}\left(\operatorname{countingPolynomial}\left(i\right), \operatorname{ratCast}\left(n\right)\right) = \operatorname{ratCast}\left(\operatorname{count}\left(n, n + \operatorname{one}\left(\right) - i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Apply count_eq_binomial_sum and Mathlib Nat.cast_choose_eq_descPochhammer_div termwise. The inequality i<=n+1 justifies the natural-subtraction cast; the rational shift then evaluates exactly at M=n+1-i. The same polynomial works for every valid n, including n=0, M=0 and i=0.

**Theorem 1.3 (The polynomial degree is at most 2i).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \operatorname{natDegree}\left(\operatorname{countingPolynomial}\left(i\right)\right) \le \operatorname{two}\left(\right) \cdot i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_natDegree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The shifted k-th falling-factorial polynomial has degree k. Multiplication by its possibly zero scalar cannot increase degree. The finite sum therefore has degree at most 2i. This is an upper bound, not the conjectured exact degree.

**Theorem 1.4 (The coefficient at degree 2i).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \operatorname{coeff}\left(\operatorname{countingPolynomial}\left(i\right), \operatorname{two}\left(\right) \cdot i\right) = \operatorname{div}\left(\operatorname{ratCast}\left(\operatorname{patternCoefficient}\left(i, \operatorname{two}\left(\right) \cdot i\right)\right), \operatorname{ratCast}\left(\operatorname{factorial}\left(\operatorname{two}\left(\right) \cdot i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_top_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

All terms below 2i have zero coefficient at 2i. The shifted top falling-factorial polynomial is monic of degree 2i, by the pinned Mathlib APIs. Hence the displayed coefficient is its actual pattern count divided by (2i)!. The identity i!*a(i,2i)=(2i)! is proved in MazorchukXuTopPatterns and supplies the exact degree and leading coefficient in the full theorem there.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_eval`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_natDegree_le`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial.countingPolynomial_top_coeff`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization](MazorchukXuNormalization.md)
