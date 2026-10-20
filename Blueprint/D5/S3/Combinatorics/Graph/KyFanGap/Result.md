# The asymptotic graph Ky Fan conjecture

## Abstract

Infinitely many graph Ky Fan prefixes have strict asymptotic gaps.

**Theorem 1.1 (Infinitely many strict gaps).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/nikiforov-2015-ky-fan-asymptotic-gap` (proved) by `D5/S3/Combinatorics/Graph/KyFanGap/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nikiforov-2015-ky-fan-asymptotic-gap","declaration_gid":"D5/S3/Combinatorics/Graph/KyFanGap/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Nikiforov (2015). *Extrema of graph eigenvalues*. URL: <https://arxiv.org/abs/1502.00359v1>.

*Commentary.*

For infinitely many natural numbers k, the maximum Ky Fan k-sum over simple graphs on n vertices, divided by n, converges as n tends to infinity to a value strictly below (1+sqrt(k))/2. The Ky Fan sum uses decreasing singular values, including the absolute values of negative eigenvalues. The finite graph maximum ranges over every graph on Fin n, and the pinned definition extends the sum by zero singular values beyond the dimension.

Every positive nonsquare k has a uniform positive gap for all symmetric zero-one matrices of order at least k. Hence its graph maxima eventually obey the same bound. Blow-ups and padding give convergence to the explicit supremum of xi(k,m+k)/(m+k) over natural m. The limit is at most the universal bound minus the positive gap. Infinitely many primes supply infinitely many positive nonsquare k. The uniform gap holds for every positive nonsquare prefix; the final infinitude proof uses the prime subset. No effective value or optimal size of the gap is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Result.result`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/BlowUp](BlowUp.md)
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal](NearExtremal.md)
