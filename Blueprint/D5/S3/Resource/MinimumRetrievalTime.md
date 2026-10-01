# Minimum iid span retrieval and the finite-length Pareto obstruction

## Abstract

An actual iid stopping-time bridge and a universal five-column obstruction refute the finite-length Pareto conjecture at file dimensions (1,2).

**Definition 1.1 (Minimum recovery time).**

$$\operatorname{minimumTime}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.minimumTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is the least natural time satisfying the recovery predicate, or infinity if no such time exists.

**Definition 1.2 (Uniform iid physical-index sampling).**

$$\operatorname{uniformSamples}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.uniformSamples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is the infinite product of uniform probability measures on the finite nonempty physical column-index alphabet. Equal or zero columns do not change the alphabet.

**Definition 1.3 (Span after a finite prefix).**

$$\operatorname{prefixSpan}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.prefixSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefix span is the linear span of columns at all sampled indices in positions strictly less than the given natural time.

**Definition 1.4 (Whole-file recovery).**

$$\operatorname{recovered}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.recovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recovery means inclusion of the entire target file submodule in the sampled prefix span.

**Definition 1.5 (Actual minimum file-retrieval stopping time).**

$$\operatorname{retrievalTime}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.retrievalTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The retrieval time is minimumTime applied to the prefix-span recovery predicate; it is not defined by an expectation formula.

**Theorem 1.6 (Probability and expectation bridge).**

$$\operatorname{E}\left(G, U\right) = \operatorname{tailSum}\left(G, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.retrieval_time_probability_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field and module, finite nonempty measurable physical-index alphabet with measurable singletons, and file U included in the column span of G: retrievalTime is measurable; t<retrievalTime iff recovery has not occurred after t draws; the nonnegative integral equals the sum of these tail probabilities. Each tail is at most N(1-1/N)^t, every finite tail sum is bounded by the integral, the integral is finite, its real-valued stopping time is integrable, and its Bochner integral equals the toReal nonnegative integral. Here E denotes this actual integral, not a new definition of the stopping time.

**Definition 1.7 (Old physical-index map).**

$$\operatorname{oldAddress}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.oldAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four physical indices map to basis indices 0,0,1,2.

**Definition 1.8 (Old full-rank generator).**

$$\operatorname{oldColumns}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.oldColumns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any three-element basis, the columns are b0,b0,b1,b2, with both b0 copies retained as distinct indices.

**Definition 1.9 (One-dimensional first file).**

$$\operatorname{oldFirstFile}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.oldFirstFile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first file is span{b0}.

**Definition 1.10 (Two-dimensional second file).**

$$\operatorname{oldSecondFile}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.oldSecondFile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second file is span{b1,b2}.

**Theorem 1.11 (The old code has actual expectation pair (2,6)).**

$$\operatorname{E}\left(G0, U1\right) = 2 \land \operatorname{E}\left(G0, U2\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.old_code_actual_expectations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every three-element basis over any field, the old four columns span the whole module, the actual expected retrieval time of span{b0} is 2, and that of span{b1,b2} is 6.

**Theorem 1.12 (Arbitrary-index two-coupon obstruction).**

$$6 < \operatorname{E}\left(G, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.five_column_three_kernel_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any five physical columns, linear projection, and file containing two vectors with independent projections: if all projected columns outside two distinct arbitrary indices vanish and the file lies in the full column span, its actual expected retrieval time is greater than 6. The conclusion uses a nine-term lower tail sum; no column ordering or permutation premise is required.

**Theorem 1.13 (Two intersecting failing pairs force expectation greater than two).**

$$2 < \operatorname{E}\left(G, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.five_column_bad_pairs_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any five physical columns and three distinct indices common,left,right, if neither the common,left pair nor the common,right pair spans the file, while all columns together do, the actual expected retrieval time is greater than 2.

**Theorem 1.14 (Independent projections and a third failing singleton).**

$$2 < \operatorname{E}\left(G, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.five_column_projected_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any five physical columns and recoverable file containing a nonzero target killed by a linear projection: if two columns have independent projections and a third distinct column cannot alone span the target, the actual expected file-retrieval time is greater than 2.

**Theorem 1.15 (Every full-rank successor fails weak Pareto domination).**

$$2 < \operatorname{E}\left(G, U1\right) \lor 6 < \operatorname{E}\left(G, U2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.five_column_universal_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every field, module, three-element basis, and unrestricted five-column full-span generator G, either E(G,span{b0})>2 or E(G,span{b1,b2})>6. Project along b0, select two independent projected columns from full span, and split according to the existence of another nonzero projected column. This exhausts all generators, including zeros and duplicates.

**Definition 1.16 (First coordinate file).**

$$\operatorname{firstCoordinateFile}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.firstCoordinateFile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For field K and file dimensions s1,s2, this is the span of standard basis vectors whose Fin(s1+s2) indices have value less than s1.

**Definition 1.17 (Second coordinate file).**

$$\operatorname{secondCoordinateFile}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.secondCoordinateFile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For field K and file dimensions s1,s2, this is the span of standard basis vectors whose Fin(s1+s2) indices have value at least s1.

**Definition 1.18 (Same-field weak Pareto length monotonicity).**

$$\operatorname{paretoCodeLengthMonotonicity}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.paretoCodeLengthMonotonicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed field K, quantify positive s1,s2 with max(s1,s2)>=2, every n>=s1+s2, and every indexed n-column matrix of rank s1+s2. Require an arbitrary (n+1)-column matrix over the same K of the same full rank whose actual expected retrieval times for both coordinate files are each at most those of the original matrix.

**Definition 1.19 (The complete finite-field data).**

$$\operatorname{FiniteFieldModel}\left(\right)$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.FiniteFieldModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite-field model contains an arbitrary carrier type, its field structure, and a Fintype structure. Quantification over this record preserves quantification over all finite fields and fixes the same field structure for both codes.

**Definition 1.20 (Bar-Lev Conjecture 2).**

$$claim \Leftrightarrow (\forall K \in \operatorname{FiniteFields},\; \forall s1 \in \operatorname{PositiveNaturals},\; \forall s2 \in \operatorname{PositiveNaturals},\; 2 \le \operatorname{max}\left(s1, s2\right) \Rightarrow \left(\forall n \in \operatorname{Naturals},\; s1 + s2 \le n \Rightarrow \left(\forall G \in \operatorname{FullRankCodes}\left(K, s1 + s2, n\right),\; \exists Gprime \in \operatorname{FullRankCodes}\left(K, s1 + s2, n + 1\right),\; \operatorname{E}\left(Gprime, \operatorname{firstCoordinateFile}\left(K, s1, s2\right)\right) \le \operatorname{E}\left(G, \operatorname{firstCoordinateFile}\left(K, s1, s2\right)\right) \land \operatorname{E}\left(Gprime, \operatorname{secondCoordinateFile}\left(K, s1, s2\right)\right) \le \operatorname{E}\left(G, \operatorname{secondCoordinateFile}\left(K, s1, s2\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Resource/MinimumRetrievalTime.claim` (`✓ std3`).

*Citation.* Daniella Bar-Lev (2026). *Coded Information Retrieval for Block-Structured DNA-Based Data Storage*. DOI: [10.48550/arXiv.2603.17154](https://doi.org/10.48550/arXiv.2603.17154). URL: <https://arxiv.org/html/2603.17154v2>.

*Commentary.*

The previous monotonicity property is asserted for every finite field structure. Both file sizes are positive; k=s1+s2, n>=k, and max(s1,s2)>=2. Expectations use actual minimum iid uniform-with-replacement span recovery. The successor is unrestricted and retains all physical zero and duplicate indices.

**Theorem 1.21 (The complete literal conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/MinimumRetrievalTime.result` (`✓ std3`). ∎

*Resolves.* `Problems/bar-lev-2026-pareto-code-length-monotonicity-refutation` (refuted) by `D5/S3/Resource/MinimumRetrievalTime.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bar-lev-2026-pareto-code-length-monotonicity-refutation","declaration_gid":"D5/S3/Resource/MinimumRetrievalTime.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniella Bar-Lev (2026). *Coded Information Retrieval for Block-Structured DNA-Based Data Storage*. DOI: [10.48550/arXiv.2603.17154](https://doi.org/10.48550/arXiv.2603.17154). URL: <https://arxiv.org/html/2603.17154v2>.

*Commentary.*

Over F2, take s1=1,s2=2,n=4 and columns e0,e0,e1,e2. Matrix rank equals three, and actual expectations are (2,6). The universal five-column obstruction excludes every full-rank successor under weak Pareto domination. Matrix rank is connected to full column span by the pinned finite-dimensional rank lemmas. This refutes Conjecture 2, not the already excluded (1,1) case or an append-only substitute.

## References

- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.FiniteFieldModel`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.claim`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.firstCoordinateFile`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.five_column_bad_pairs_obstruction`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.five_column_projected_obstruction`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.five_column_three_kernel_obstruction`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.five_column_universal_obstruction`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.minimumTime`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.oldAddress`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.oldColumns`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.oldFirstFile`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.oldSecondFile`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.old_code_actual_expectations`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.paretoCodeLengthMonotonicity`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.prefixSpan`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.recovered`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.result`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.retrievalTime`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.retrieval_time_probability_bridge`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.secondCoordinateFile`
- Truth anchor: `D5/S3/Resource/MinimumRetrievalTime.uniformSamples`
