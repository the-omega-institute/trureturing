# Regular graph CHS extrema

## Abstract

Extrema of complete homogeneous symmetric norms over connected regular graphs.

**Theorem 1.1 (The cycle minimizes and the complete graph maximizes).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/chavez-2023-regular-chs-norm-extrema` (proved) by `D5/S3/Combinatorics/Graph/RegularCHS/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chavez-2023-regular-chs-norm-extrema","declaration_gid":"D5/S3/Combinatorics/Graph/RegularCHS/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every natural n at least three and m at least one, the cycle and the complete graph on Fin n are connected and regular. Every connected regular simple graph G on these vertices has its degree 2m CHS norm at least that of the cycle and at most that of the complete graph. Thus both bounds are attained. The norm is the real power of the complete homogeneous symmetric polynomial in the real adjacency eigenvalues, with exponent one divided by 2m.

The coefficient lower bound holds more generally for every r-regular graph of order n at least three with r at least two, without connectedness. At regular degree two, cycle-component factorization gives the comparison. At regular degree three, closed-walk domination and the positive Newton recurrence give it. At regular degree at least four, the even closed-walk lower bound gives bseq n r m, monotonicity in r gives bseq n 4 m, and the spectral bound on the cycle places its coefficient below that sequence. Entrywise adjacency comparison with the complete graph gives the upper bound.

Connectedness and the degree-sum formula force the regular degree to be at least two when n is at least three. All adjacency CHS coefficients are nonnegative; monotonicity of the real power with nonnegative exponent transfers the coefficient inequalities to the stated norms. This conclusion concerns the regular family; it makes no assertion about the unicyclic family or uniqueness within a fixed degree class.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Result.result`
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Cubic](Cubic.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/CycleBound](CycleBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Newton](Newton.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular](TwoRegular.md)
