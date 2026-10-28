# Coefficientwise log-concavity of both series

## Abstract

Both coefficient assertions of Karp and Zhang's Conjecture 5.2.

**Definition 1.1 (Conjecture 5.2).**

$$claim \Leftrightarrow \left(\forall y \in Nat \to Real,\; \operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall m \in Nat,\; 0 \le \operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{delta}\left(y, mu, alpha, beta, m\right) \land 0 \le \operatorname{KarpZhangGamma}.\operatorname{Series}.\operatorname{gammaDelta}\left(y, mu, alpha, beta, m\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangConjecture/Result.claim` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Karp and Zhang, Conjecture 5.2, page 12: Suppose that {yₖ}ₖ₌₀∞ is a log-concave sequence. Then the functions μ→ỹ(μ;x) and μ→ŷ(μ;x) are coefficient-wise log-concave on μ>0.

The real sequence y satisfies KarpZhangReciprocal.Result.IsLogConcave: its terms are nonnegative, it is nontrivial, its adjacent log-concavity inequalities hold, and its support is an interval of integers with the precise zero condition of Definition 1.1. For every positive real mu, nonnegative real alpha and beta, and natural m, claim asserts both 0 at most KarpZhangReciprocal.Result.delta(y,mu,alpha,beta,m) and 0 at most KarpZhangGamma.Series.gammaDelta(y,mu,alpha,beta,m).

The reciprocal series has coefficient y(k)(2mu) rising factorial k divided by (mu) rising factorial k times k factorial. The gamma series has coefficient y(k)Real.Gamma(mu+k) divided by Real.Gamma(2mu+k) times k factorial. In both cases the Turanian is the product at mu+alpha and mu+beta minus the product at mu and mu+alpha+beta. Finite Cauchy coefficients express the assertion without convergence or growth hypotheses.

**Theorem 1.2 (Both halves hold for every coefficient).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangConjecture/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-zhang-2023-conjecture-5-2` (proved) by `D5/S3/Analytic/KarpZhangConjecture/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-zhang-2023-conjecture-5-2","declaration_gid":"D5/S3/Analytic/KarpZhangConjecture/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The theorem proves claim by combining KarpZhangReciprocal.Result.reciprocal_half and KarpZhangGamma.Series.gamma_half with the same sequence, base parameter, shifts and coefficient degree.

For the reciprocal series, reversible birth-and-death rates bound the score variance of an interval convolution by its expected curvature. Concavity along lines of constant parameter sum and symmetry give the symmetric-tail inequalities. Abel summation combines these tails with the increasing balanced products of a log-concave sequence.

For the gamma series, exponential smoothing preserves balanced coefficient minors. The paired reciprocal-gamma kernel has nonnegative total and at most one change from negative to positive, so increasing nonnegative smoothed weights give nonnegative coefficients of the two-variable transform. A positive diagonal substitution and the gamma duplication identity transfer these inequalities to the literal gamma-series coefficients. Both shifts may be any nonnegative real numbers, including zero.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangConjecture/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpZhangConjecture/Result.result`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Series](../KarpZhangGamma/Series.md)
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/Result](../KarpZhangReciprocal/Result.md)
