# The excluded endpoint in Lewis–Won Conjecture 3.17

## Abstract

The only admissible balanced block size at n = 3 equals the strict lower endpoint.

**Definition 1.1 (The existential maximizer assertion).**

$$\begin{aligned}\forall n\in\mathbb{N},3\le n\implies \forall x\in\mathbb{R},(1\le x\land n=\frac{\log(x+1)}{\log(1+\frac{1}{x})}+2x)\implies\\\exists m\in\mathbb{N},(1\le m\land 2m\le n)\land\\(\forall j\in\mathbb{N},(1\le j\land 2j\le n)\implies E(n,j)\le E(n,m))\land x<m\land m<x+2\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.claim` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Lewis and Won, §3.4, printed pp. 20–22. At p. 20, Eq. (3.1) defines E(n,m) below, with S(m,k) the Stirling number of the second kind. The complete summand is squared. Both m and the comparison size j are natural numbers with 1 ≤ m and 2m ≤ n, or the same bounds for j. The size bounds make the natural subtraction exact.

$E(n,m)=\sum_{k=1}^{m}(S(m,k)\cdot k^{n-2m}\cdot k!)^{2}$

At p. 21 the lower cutoff x = m∗ is real, with x ≥ 1 and n ≥ 3. The equality uses the real cast of n. At p. 22 the conjecture asks for at least one global maximizer in the open interval (x, x + 2). Both endpoint comparisons use the real cast of m.

$n=\frac{\log(x+1)}{\log(1+\frac{1}{x})}+2x$

**Theorem 1.2 (Refutation at size three).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lewis-won-conjecture-3-17` (refuted) by `D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lewis-won-conjecture-3-17","declaration_gid":"D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

At n = 3 and x = 1 the logarithms both equal log 2, which is positive. Their quotient is one and the cutoff equation reads 3 = 1 + 2. Every admissible positive size satisfies 1 ≤ m and 2m ≤ 3, hence m = 1. Its strict lower comparison would read 1 < 1. The restriction to n ≥ 4 remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.claim`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result`
