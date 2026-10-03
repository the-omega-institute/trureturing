# A Vandermonde refutation of the universal hyperbolic bound

## Abstract

A nonsystematic twenty-column code over F11 refutes the universal hyperbolic tradeoff for actual whole-file iid retrieval.

**Definition 1.1 (The quadratic moment curve).**

$$\operatorname{quadraticCurve}\left(\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.quadraticCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a parameter x in a field, the three coordinates are 1, x and x squared. The definition is valid over any field.

**Definition 1.2 (Types seen in an actual prefix).**

$$\operatorname{observedTypes}\left(\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.observedTypes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a map from physical indices to vector parameters, observedTypes is the finite set of parameters seen in the first t samples. Multiplicity remains in the physical-index sampling measure; the set records only which parameters have occurred.

**Definition 1.3 (Twenty physical sampling indices).**

$$\operatorname{physicalParameter}\left(\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.physicalParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alphabet is Fin 20. Indices zero through nine have parameter zero. Indices ten through nineteen have parameters one through ten in ZMod 11. Every physical index has probability one twentieth, independently with replacement.

**Definition 1.4 (Repeated singleton and quadratic-curve columns).**

$$\operatorname{columns}\left(\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column at parameter x is (1,x,x squared). There are ten copies of the first coordinate basis vector and ten other, distinct columns. Every column is nonzero because its first coordinate is one. Columns with parameters zero, one and two are independent, so the generator has rank three. The file sizes are one and two, in the original coordinate partition.

**Definition 1.5 (The complete all-generators assertion).**

$$\operatorname{hyperbolicBound}\left(\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.hyperbolicBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field K, positive file sizes s1,s2 with maximum at least two, k=s1+s2, any n at least k, and any rank-k indexed generator, the sum s1/E1+s2/E2 is at most one. Ei is the Bochner expectation of the actual minimum time for the uniform iid sampled-column span to contain the entire coordinate file. Systematicity, distinct columns, and the absence of zero columns are not added hypotheses.

**Definition 1.6 (Bar-Lev Conjecture 1).**

$$\forall K \in \operatorname{FiniteFields},\; \forall s1 \in \operatorname{PositiveNaturals},\; \forall s2 \in \operatorname{PositiveNaturals},\; 2 \le \operatorname{max}\left(s1, s2\right) \Rightarrow \left(\forall n \in \operatorname{Naturals},\; s1 + s2 \le n \Rightarrow \left(\forall G \in \operatorname{FullRankCodes}\left(K, s1 + s2, n\right),\; \frac{s1}{\operatorname{E1}\left(G\right)} + \frac{s2}{\operatorname{E2}\left(G\right)} \le 1\right)\right)$$

*Formalization.* `D5/S3/Resource/VandermondeHyperbolicRefutation.claim` (`✓ std3`).

*Citation.* Daniella Bar-Lev (2026). *Coded Information Retrieval for Block-Structured DNA-Based Data Storage*. DOI: [10.48550/arXiv.2603.17154](https://doi.org/10.48550/arXiv.2603.17154). URL: <https://arxiv.org/html/2603.17154v2>.

*Commentary.*

The assertion hyperbolicBound is quantified over every FiniteFieldModel, retaining its field structure and finite carrier. This is the universal hyperbolic bound in Section V-B, Conjecture 1, of arXiv:2603.17154v2.

**Theorem 1.7 (The universal hyperbolic assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/VandermondeHyperbolicRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bar-lev-2026-universal-hyperbolic-bound-refutation` (refuted) by `D5/S3/Resource/VandermondeHyperbolicRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bar-lev-2026-universal-hyperbolic-bound-refutation","declaration_gid":"D5/S3/Resource/VandermondeHyperbolicRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniella Bar-Lev (2026). *Coded Information Retrieval for Block-Structured DNA-Based Data Storage*. DOI: [10.48550/arXiv.2603.17154](https://doi.org/10.48550/arXiv.2603.17154). URL: <https://arxiv.org/html/2603.17154v2>.

*Commentary.*

For the stated twenty-column code, the singleton file is recovered exactly when a zero-parameter column has been drawn or three distinct nonzero parameters have been drawn. The second file is recovered exactly when three distinct parameters have been drawn. The exact failure tails are 45(1/10)^t-80(1/20)^t+36*0^t and 10(11/20)^t+45(1/10)^t-9(1/2)^t-90(1/20)^t+45*0^t. Finite-cylinder probabilities keep all ten duplicate physical indices. Summing these tails through retrieval_time_probability_bridge gives actual expectations E1=34/19 and E2=767/171. Consequently 1/E1+2/E2=26201/26078, exceeding one by 123/26078. This admissible nonzero witness refutes the complete all-generators statement, not a systematic subcase or a projected-rank substitute.

## References

- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.claim`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.columns`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.hyperbolicBound`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.observedTypes`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.physicalParameter`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.quadraticCurve`
- Truth anchor: `D5/S3/Resource/VandermondeHyperbolicRefutation.result`
- Dependency: [D5/S3/Resource/MinimumRetrievalTime](MinimumRetrievalTime.md)
