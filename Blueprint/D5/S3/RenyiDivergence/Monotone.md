# Order Monotonicity of Finite Renyi Divergence

## Abstract

Finite Renyi divergence is nondecreasing in its order separately below and above order one under minimal reference-mass hypotheses.

**Theorem 1.1 (Finite Renyi divergence is monotone below order one).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha , \beta \in \mathbb{R}, 0< \alpha \le \beta < 1,\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0\le q(i)) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)\le D_{\beta }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem supplies monotonicity in the order on the interval strictly below one: if 0 < alpha <= beta < 1, then D_alpha(p||q) <= D_beta(p||q). Together with the super-unit theorem below, this is the property that makes the Renyi family a coherent scale rather than a collection of unrelated quantities. The bucket's domain registration promised order monotonicity, and these two theorems supply it on the ranges where it genuinely holds under the repository's conventions.

The hypotheses are weaker than a conventional probability-law statement may suggest. Only p is required to be pointwise nonnegative and normalized. The reference mass q need only be pointwise nonnegative; it is not required to be normalized, and no discrete absolute-continuity hypothesis is imposed. Eleven waves in this bucket have now shown that deriving hypotheses statement by statement, rather than copying a sibling's assumptions, yields strictly stronger results.

Write S_gamma = sum_i p(i)^gamma q(i)^(1-gamma). Below one, both shifted orders alpha-1 and beta-1 are negative, and the ratio r = (alpha-1)/(beta-1) is at least one. Weighted Jensen gives S_beta^r <= S_alpha. After taking logarithms, division by the negative quantity alpha-1 reverses the inequality and yields D_alpha(p||q) <= D_beta(p||q). If the supports do not overlap, both power sums and both totalized divergences are zero; otherwise positivity licenses the logarithmic step.

**Theorem 1.2 (Finite Renyi divergence is monotone above order one).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha , \beta \in \mathbb{R}, 1< \alpha \le \beta ,\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0\le q(i)) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)\le D_{\beta }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one, the shifted orders are positive and the same Jensen mechanism uses the ratio in the opposite direction: r = (beta-1)/(alpha-1) >= 1 gives S_alpha^r <= S_beta. Division by the positive quantity beta-1 preserves the direction and again yields D_alpha(p||q) <= D_beta(p||q). Thus the sign change at one is handled symmetrically by reversing the ratio, rather than by adjoining an unrelated inequality argument. At alpha = 1 the prefactor 1/(alpha-1) is totalized to zero altogether, which is exactly why that endpoint cannot be included.

The scope divides into three categories and must not be compressed into a proved-versus-unproved dichotomy.

PROVED. Monotonicity holds for 0 < alpha <= beta < 1 and for 1 < alpha <= beta, with p normalized and nonnegative and q only pointwise nonnegative.

DISPROVED under the repository's literal conventions. Including beta = 1 fails: a point mass p against a uniform q has D_(1/2)(p||q) = log 2 but D_1(p||q) = 0, because totalization sends the prefactor 1/(alpha-1) to zero at alpha = 1 and thereby destroys the limiting divergence value. The unrestricted straddling claim also fails: a uniform p against a point-mass q has D_(1/2)(p||q) = log 2 but D_2(p||q) = -2 log 2.

The straddling counterexample is produced entirely by the totalizing conventions. At a coordinate where q vanishes and p does not, the term p^2/q is mathematically infinite, whereas Lean's x/0 = 0 renders it as zero; that erased contribution is what drags D_2 below D_(1/2). This failure is an artifact of the formalization's totality, not a fact about Renyi divergence.

NOT PROVED AND NOT DISPROVED. The straddling case with the discrete absolute-continuity hypothesis q(i) = 0 implies p(i) = 0 remains open in this module. That hypothesis removes the counterexample above, but the module establishes no theorem or counterexample for the resulting claim.

No order-one limit to the classical divergence, straddling monotonicity under absolute continuity, strictness, data-processing inequality for the Renyi family, or measure-theoretic analogue is claimed. All logarithms are natural, so the units are nats.

## References

- Truth anchor: `D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_lt_one`
- Truth anchor: `D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_one_lt`
- Dependency: [D5/S3/RenyiDivergence/Basic](Basic.md)
