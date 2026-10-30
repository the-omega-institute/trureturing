# Uniform prime-square local moments

## Abstract

The exact infinite local moment has a uniform prime-square approximation for every sufficiently large real moment parameter.

All local Lean names belong to D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation. The exponent a is natural, including zero; p and s in the definitions are real. Powers with real exponent s are positive-base real powers on the stated domain. The infinite sum is Lean's unconditional real tsum; its summability is proved for every p>1 and s≥0.

**Definition 1.1 (The original rational local factor).**

$$\forall (p: \mathbb{R}), (\forall (a: \mathbb{N}), (((a = 0) \Rightarrow (\operatorname{PrimeSquareMomentApproximation.factor}\left(p, a\right) = 1)) \land ((1 \le a) \Rightarrow (\operatorname{PrimeSquareMomentApproximation.factor}\left(p, a\right) = \frac{p + 3 \cdot (a: \mathbb{R}) \cdot \left(p - 1\right)}{2 \cdot \left(p + (a: \mathbb{R}) \cdot \left(p - 1\right)\right)}))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.factor` (`✓ std3`).

*Citation.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

For a=0 the factor is one. For every integer a≥1 it is exactly (p+3a(p−1))/(2(p+a(p−1))). For p>1 all these factors are positive, and for p≥1 they are at most 3/2.

**Definition 1.2 (The full infinite real-power moment).**

$$\forall (p: \mathbb{R}), (\forall (s: \mathbb{R}), (\operatorname{PrimeSquareMomentApproximation.localMoment}\left(p, s\right) = \left(1 - \frac{1}{p}\right) \cdot \sum_{a\in\mathbb{N}} \frac{\operatorname{PrimeSquareMomentApproximation.factor}\left(p, a\right)^{s}}{p^{a}}))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.localMoment` (`✓ std3`).

*Citation.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

This is the source series with every natural exponent present. Its prefactor is 1−1/p. Comparison with (3/2)^s times the geometric series with ratio 1/p proves summability for p>1 and s≥0. The a=0 summand is one, so the local moment is strictly positive for p>1 and s>0.

**Definition 1.3 (The prime-square scale).**

$$\operatorname{PrimeSquareMomentApproximation.c} = \frac{\operatorname{Real.log}\left(\frac{7}{6}\right)}{2}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c` (`✓ std3`).

*Citation.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

The source writes P=exp(cs). Thus P²=exp(2cs), and P^(1−δ)=exp((1−δ)cs).

**Definition 1.4 (A sufficient slope for every higher exponent).**

$$\operatorname{PrimeSquareMomentApproximation.c3} = \frac{\operatorname{Real.log}\left(\frac{5}{4}\right)}{3}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

For g(a)=(3a+1)/(2(a+1)), induction gives g(a)^3≤(5/4)^a for every a≥3. Taking logarithms yields log g(a)≤c3 a. This explicit c3 supplies the source's proposed smaller slope.

**Theorem 1.5 (A strict gap between the two scales).**

$$\operatorname{PrimeSquareMomentApproximation.c3} < \operatorname{PrimeSquareMomentApproximation.c}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c3_lt_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

The rational inequality (5/4)^2<(7/6)^3 gives 2 log(5/4)<3 log(7/6). Together with log(5/4)>0, this gives 0<c3<c.

**Theorem 1.6 (A positive exponential scale).**

$$0 < \operatorname{PrimeSquareMomentApproximation.c}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

Positivity follows from 0<c3<c. In particular 1−c3/c is positive, so the admissible interval 0<δ<1−c3/c is nonempty; its midpoint is one explicit choice.

**Definition 1.7 (The complete uniform statement).**

$$(\operatorname{PrimeSquareMomentApproximation.originalClaim}) \Leftrightarrow (\forall (delta: \mathbb{R}), ((0 < delta) \Rightarrow ((delta < 1 - \frac{\operatorname{PrimeSquareMomentApproximation.c3}}{\operatorname{PrimeSquareMomentApproximation.c}}) \Rightarrow (\forall (B: \mathbb{R}), ((2 < B) \Rightarrow (\forall (epsilon: \mathbb{R}), ((0 < epsilon) \Rightarrow (\exists (S: \mathbb{R}), (\forall (s: \mathbb{R}), ((S \le s) \Rightarrow (\forall (p: \mathbb{N}), ((\operatorname{Nat.Prime}\left(p\right)) \Rightarrow ((\operatorname{Nat.mod}\left(p, 4\right) = 1) \Rightarrow ((\operatorname{Real.exp}\left(\left(1 - delta\right) \cdot \operatorname{PrimeSquareMomentApproximation.c} \cdot s\right) < (p: \mathbb{R})) \Rightarrow (((p: \mathbb{R}) \le B \cdot \operatorname{Real.exp}\left(\operatorname{PrimeSquareMomentApproximation.c} \cdot s\right)) \Rightarrow (\operatorname{abs}\left(\operatorname{Real.log}\left(\operatorname{PrimeSquareMomentApproximation.localMoment}\left((p: \mathbb{R}), s\right)\right) - \operatorname{Real.log}\left(1 + \frac{\operatorname{Real.exp}\left(2 \cdot \operatorname{PrimeSquareMomentApproximation.c} \cdot s\right)}{(p: \mathbb{R})^{2}}\right)\right) < epsilon))))))))))))))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.originalClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

For each fixed admissible δ and fixed B>2, one real threshold works for every real s beyond it and every prime in the original congruence class and window. The lower endpoint is strict and the upper endpoint is closed. The explicit interval for δ is a sufficient interpretation of the source's sufficiently-small condition.

**Theorem 1.8 (Uniform logarithmic approximation).**

$$\operatorname{PrimeSquareMomentApproximation.originalClaim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathoverflow-516091-prime-square-local-moment` (proved) by `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathoverflow-516091-prime-square-local-moment","declaration_gid":"D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* unkown (2026). *Uniform dominance of a prime-square term in an Euler-product moment*. URL: <https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment>.

*Commentary.*

Put X=exp(2cs)/p² and q=exp(c3 s)/p. The sum of all a≥3 terms is at most q³/(1−q) when q<1. The a=1 term is at most 1/p. The exact a=2 factor is (7/6)(1−4/(21p−14)), so for p≥2 its logarithm lies between 2c−2/p and 2c. Consequently, if A=1+X and A0=1+e_p(2)^s/p², then A exp(−2s/p)≤A0≤A. This controls the relative perturbation even when X grows.

Writing T for the full tail and U=e_p(1)^s/p+T, the exact identity is m_p(s)=(1−1/p)(A0+U). The inequalities −2x≤log(1−x) for 0≤x≤1/2 and log(1+y)≤y give |log m_p(s)−log A|≤2/p+2s/p+q³/(1−q). Every logarithm used in this comparison has a positive argument.

Let α=(1−δ)c and κ=α−c3>0. Whenever p>exp(αs), one has 1/p≤exp(−αs) and q≤exp(−κs). Eventually q≤1/2, so q³/(1−q)≤2q. The common error bound is 2exp(−αs)+2s exp(−αs)+2exp(−κs), which tends to zero as the real variable s tends to infinity. Choose one threshold for this bound to be below ε, for q≤1/2 and for s≥1. It is independent of p.

The estimate holds for all real p≥2 above the lower exponential cutoff. Specializing it to natural primes preserves p≡1 mod 4 and p≤B exp(cs), although these additional restrictions are unnecessary for the bound. The conclusion concerns a single local factor. It asserts no global Euler-product approximation, sum over primes, or optimal endpoint for δ.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c3`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c3_lt_c`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.c_pos`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.factor`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.localMoment`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.originalClaim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.result`
