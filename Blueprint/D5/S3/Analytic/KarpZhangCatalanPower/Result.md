# Catalan powers preserve the two sequence classes

## Abstract

Both coefficient signs of Karp and Zhang's Conjecture 4.2.

**Definition 1.1 (Log-convex sequences).**

$$\forall h \in Nat \to Real,\; IsLogConvex\left(h\right) \Leftrightarrow \left(\left(\forall k \in Nat,\; 0 \le h\left(k\right)\right) \land \left(\left(\exists k \in Nat,\; h\left(k\right) \ne 0\right) \land \left(\forall k \in Nat,\; 1 \le k \Rightarrow h\left(k\right)^{2} \le h\left(k - 1\right) \cdot h\left(k + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Definition 1.1, page 2: “Let {fₖ}ₖ₌₀∞ be a non-negative nontrivial real sequence.” The log-convex clause reads: “If fₖ² ≤ fₖ₋₁fₖ₊₁ for all k ∈ ℕ, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).”

Here the natural indices in the inequality start at one. The predicate keeps nonnegativity and nontriviality and imposes no interval-support condition. The literal inequalities also admit a sequence supported on {0}; that endpoint case is included. The log-concave class is the existing KarpZhangReciprocal.Result.IsLogConcave, including its interval-support condition.

**Definition 1.2 (The finite Turanian coefficient).**

$$\forall h \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; delta\left(h, mu, alpha, beta, m\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} h\left(k\right) \cdot h\left(m - k\right) \cdot \left(\operatorname{Coeff}.\operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{Coeff}.\operatorname{a}\left(m - k, mu + beta\right) - \operatorname{Coeff}.\operatorname{a}\left(k, mu\right) \cdot \operatorname{Coeff}.\operatorname{a}\left(m - k, mu + alpha + beta\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.delta` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The coefficient a is Coeff.a, the literal quotient (t) rising factorial 2k divided by (t+1) rising factorial k times k factorial. The finite sum is the degree-m Cauchy coefficient; neither convergence nor growth assumptions on h are needed.

**Definition 1.3 (Conjecture 4.2).**

$$claim \Leftrightarrow \left(\forall h \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; 0 \le mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{IsLogConcave}\left(h\right) \Rightarrow 0 \le delta\left(h, mu, alpha, beta, m\right)\right) \land \left(IsLogConvex\left(h\right) \Rightarrow delta\left(h, mu, alpha, beta, m\right) \le 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.claim` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 4.2, page 8: Assume that {hₖ}ₖ₌₀∞ is log-concave (log-convex ) and independent of µ. Then the function µ → h(µ; x) defined in (15) is coefficient-wise log-concave (log-convex ).

For every sequence h, nonnegative real mu, alpha and beta, and every natural coefficient degree, delta is nonnegative for the source's log-concave class and nonpositive for its log-convex class. The sequence is independent of the parameters because a single h is fixed before they are quantified.

**Theorem 1.4 (Both signs hold in every degree).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-zhang-2023-conjecture-4-2` (proved) by `D5/S3/Analytic/KarpZhangCatalanPower/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-zhang-2023-conjecture-4-2","declaration_gid":"D5/S3/Analytic/KarpZhangCatalanPower/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The index law makes the full kernel sum zero. The positive derivative generator and reflected-interval cancellation give nonnegative central tails, including mu=0. The generic Abel identity KarpZhangReciprocal.Result.abel_layers writes delta as the increments of h(k)h(m-k) times these tails.

For log-concavity, KarpZhangReciprocal.Result.balanced_step makes the increments nonnegative. For log-convexity, a zero at index one propagates to every positive index. Otherwise all entries are positive, the adjacent inequalities make successive ratios increase, and the balanced products decrease. Thus their increments are nonpositive. This includes finite and singleton log-concave supports and the log-convex sequence supported only at zero. The central term is counted once and the degrees zero and one require no special assumption.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.delta`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.result`
- Dependency: [D5/S3/Analytic/KarpZhangCatalanPower/Interval](Interval.md)
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/Result](../KarpZhangReciprocal/Result.md)
