# Growth transfer

## Abstract

Uniform exponential probability bounds for Mertens d=1, r=2.

**Theorem 1.1 (One base for both parities).**

$$\begin{gathered}(\forall m,k:\mathbb{N},0< m\Rightarrow 0< k\Rightarrow b(m)b(k)\le b(m+k+6))\land \\(\forall m:\mathbb{N},0< m\Rightarrow b(m)\le a(m+1))\land b(3)<24^{3}\Rightarrow \\\exists q,c,C:\mathbb{R},0< q<1\land 0< c\land 0< C\land \\\forall n:\mathbb{N},2\le n\Rightarrow cq^{n+5}\le p(n)\le Cq^{n+5}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.same_q_probability_of_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here b(m) is OpenCertificates.count m, the number of ranking words admitting a certificate, counted once per word. The quantity a(t) counts the successful labelled SourceModel.Profile t profiles, and p(t) is SourceModel.solutionProbability t = a(t)/24^(t+5). The source parameter is N=t+5. Singles are allowed, and each of the N agents independently chooses one of 24 strict neighbor rankings.

The conditional transfer isolates three concrete premises: padded concatenation with six added sites for positive lengths, injective six-site cyclic closure, and count 3 < 24^3. The final result supplies all three from PaddedCompletion.count_padded_supermultiplicative, CyclicClosure.count_le_successful_profile_count, and TriangleCount.count_three_bound, respectively. The upper cyclic comparison is the existing CyclicBridge.source_count_le_open_count, with the unchanged source probability normalization.

For f(m)=log b(m), the existing count lower bound makes every logarithm positive-domain and f nonnegative; the empty word has count one. Existing submultiplicativity gives subadditivity of f. Apply FixedGapGrowth.fixed_gap_log_bounds with gap six to obtain h*m <= f(m) <= h*m+f(6). Exponentiation yields exp(h)^m <= b(m) <= exp(h)^m*b(6). The strict count-at-three premise gives h < log 24. Thus q=exp(h)/24 lies strictly between zero and one, c=exp(h)^(-6) is positive, and C=b(6) is positive. Closure at m=n-1 supplies the lower bound, and cutting at N=n+5 supplies the upper bound, for every n>=2 without a parity split.

The estimate synthesizes the proved count components; global novelty and priority remain unproved. The original statement is Mertens, cond-mat/0509221v2, Conjecture 3, DOI 10.1088/1742-5468/2005/10/P10008, restricted to d=1,r=2. The Apache-2.0 supplier attribution and license remain in SourceModel and docs/reports/licenses/formal-conjectures-mertens/LICENSE.txt. The unfinished escape audit is tracked by issue 29645.

**Theorem 1.2 (Unconditional exact source probability).**

$$\begin{gathered}\exists q,c,C:\mathbb{R},0< q<1\land 0< c\land 0< C\land \\\forall n:\mathbb{N},2\le n\Rightarrow cq^{n+5}\le p(n)\le Cq^{n+5}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result` (`✓ std3`). ∎

*Resolves.* `Problems/mertens-2005-range-two-stable-matching` (proved) by `D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mertens-2005-range-two-stable-matching","declaration_gid":"D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stephan Mertens (2005). *Random Stable Matchings*. DOI: [10.1088/1742-5468/2005/10/P10008](https://doi.org/10.1088/1742-5468/2005/10/P10008). URL: <https://arxiv.org/abs/cond-mat/0509221v2>.

*Commentary.*

Here p(n) is exactly SourceModel.solutionProbability n, the number of labelled profiles admitting an acceptable stable partial matching divided by 24^(n+5). The N=n+5 ranking permutations are independent and uniform. Fixed points of the involution are singles; every acceptable neighbor is preferred to being single. The event is existential in matchings, so each successful profile is counted once.

There are no count, completion, rate, parity or analytic hypotheses. All n>=2, equivalently all N>=7, share the same positive q<1 and positive constants c,C. The concrete strict input is count 3<=13808<13824=24^3; the sixteen excluded words feed the analytic estimate on its live proof path. The proof applies the transfer above to the actual padded and cyclic injections. Its admissibility candidate is open-problem-resolution for the source's d=1,r=2 specialization, with no separate problem credit for the transfer or finite count helpers. General d,r, complete-graph asymptotics and worldwide priority remain outside this conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.same_q_probability_of_counts`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/CyclicBridge](CyclicBridge.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/CyclicClosure](CyclicClosure.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth](FixedGapGrowth.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/TriangleCount](TriangleCount.md)
