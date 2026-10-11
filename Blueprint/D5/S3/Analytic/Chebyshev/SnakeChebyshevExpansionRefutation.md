# Nikolov Snake Polynomial Chebyshev Expansion Refutation

## Abstract

An even convex majorant has a degree-six snake with a negative Chebyshev coefficient.

Kryvonos (ed.), arXiv:2312.07754v1, section “Snake polynomials with positive Chebyshev expansions”, definition verbatim: “Consider a majorant µ ∈ C[−1, 1], µ(x) ≥ 0, x ∈ [−1, 1]. If there exists P ∈ Pn, P ≠ 0, such that −µ(x) ≤ P(x) ≤ µ(x), x ∈ [−1, 1], then there exists a unique (up to orientation) polynomial ωµ ∈ Pn called snake polynomial associated with µ, which oscillates most between ±µ.” “The n-th snake polynomial ωµ is uniquely determined by the following properties: a) |ωµ(x)| ≤ µ(x) x ∈ [−1, 1]; b) There exists a set δ* = (τi*)_{i=0}^n, 1 ≥ τ0* > · · · > τn* ≥ −1, such that ωµ(τi*) = (−1)^i µ(τi*), i = 0, . . . , n” Conjecture verbatim: “Conjecture (G.N.) If µ ≥ 0 is a continuous even convex function in [−1, 1], then the associated with µ snake polynomials have non-negative expansion in the Chebyshev polynomials of the first kind.”

**Definition 1.1 (Bound and alternating contacts).**

$$\forall mu: \mathbb{R}\to \mathbb{R}, \forall n: \mathbb{N}, \forall omega: \operatorname{Polynomial}\left(\mathbb{R}\right), \operatorname{IsSnake}\left(mu, n, omega\right) \Leftrightarrow ((\operatorname{natDegree}\left(omega\right) \le n) \land ((\forall x: \mathbb{R}, (x\in \operatorname{Icc}\left(-1, 1\right)) \Rightarrow (\left|\operatorname{eval}\left(omega, x\right)\right| \le \operatorname{mu}\left(x\right))) \land (\exists tau: \operatorname{Fin}\left(n+1\right)\to \mathbb{R}, (\operatorname{StrictAnti}\left(tau\right)) \land ((\operatorname{tau}\left(0\right) \le 1) \land ((-1 \le \operatorname{tau}\left(\operatorname{last}\left(n\right)\right)) \land (\forall i: \operatorname{Fin}\left(n+1\right), \operatorname{eval}\left(omega, \operatorname{tau}\left(i\right)\right) = (-1)^{i} \cdot \operatorname{mu}\left(\operatorname{tau}\left(i\right)\right)))))))$$

*Formalization.* `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.IsSnake` (`✓ std3`).

*Citation.* L. Kryvonos (ed.) (2023). *Open problems on polynomials, their zero distribution and related questions: 2023*. URL: <https://arxiv.org/abs/2312.07754v1>.

*Commentary.*

The formal encoding of the quoted characterization uses a real polynomial of degree at most n, a pointwise bound on I=[−1,1], and a strictly decreasing map τ from Fin(n+1) to ℝ. Its first contact is at most one, its last at least minus one, and its values alternate as ω(τᵢ)=(−1)ⁱμ(τᵢ). These conditions express (a) and (b) in the positive initial orientation. Uniqueness up to orientation is asserted by the source and is not formalized here.

**Definition 1.2 (Nonnegative Chebyshev expansion).**

$$claim \Leftrightarrow (\forall mu: \mathbb{R}\to \mathbb{R}, (\operatorname{ContinuousOn}\left(mu, \operatorname{Icc}\left(-1, 1\right)\right)) \Rightarrow ((\forall x: \mathbb{R}, (x\in \operatorname{Icc}\left(-1, 1\right)) \Rightarrow (0 \le \operatorname{mu}\left(x\right))) \Rightarrow ((\forall x: \mathbb{R}, (x\in \operatorname{Icc}\left(-1, 1\right)) \Rightarrow (\operatorname{mu}\left(-x\right) = \operatorname{mu}\left(x\right))) \Rightarrow ((\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Icc}\left(-1, 1\right), mu\right)) \Rightarrow (\forall n: \mathbb{N}, \forall omega: \operatorname{Polynomial}\left(\mathbb{R}\right), (\operatorname{IsSnake}\left(mu, n, omega\right)) \Rightarrow (\exists a: \mathbb{N}\to \mathbb{R}, (\forall k: \mathbb{N}, 0 \le \operatorname{a}\left(k\right)) \land (omega = \sum_{k\in \operatorname{range}\left(n+1\right)} \operatorname{C}\left(\operatorname{a}\left(k\right)\right) \cdot \operatorname{T}\left(\mathbb{R}, \operatorname{Int}\left(k\right)\right))))))))$$

*Formalization.* `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.claim` (`✓ std3`).

*Citation.* L. Kryvonos (ed.) (2023). *Open problems on polynomials, their zero distribution and related questions: 2023*. URL: <https://arxiv.org/abs/2312.07754v1>.

*Commentary.*

The formal claim quantifies over every real function continuous, nonnegative, even and convex on I, every natural n and every polynomial satisfying IsSnake. It requires a coefficient function a:ℕ→ℝ nonnegative at every index, with ω=∑ₖ₌₀ⁿ C(aₖ)Tₖ. Tₖ is Chebyshev.T ℝ (k:ℤ), the first-kind polynomial, and C embeds a real constant. UP24, arXiv:2504.04845, §7, repeats the assertion as Conjecture 7.1 (Geno Nikolov).

**Theorem 1.3 (A negative constant Chebyshev coefficient).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nikolov-2023-snake-polynomial-chebyshev-expansion` (refuted) by `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nikolov-2023-snake-polynomial-chebyshev-expansion","declaration_gid":"D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* L. Kryvonos (ed.) (2023). *Open problems on polynomials, their zero distribution and related questions: 2023*. URL: <https://arxiv.org/abs/2312.07754v1>.

*Commentary.*

Take n=6, μ(x)=max{1,(4860|x|−1078)/137}, and P(x)=(38656x⁶−41568x⁴+6831x²−137)/137. The majorant is positive, continuous, even and convex. On [0,1/4], factorizations of 137(1−P) and 137(1+P) prove |P|≤1. On [1/4,1], with L(x)=(4860x−1078)/137, the factors of 137(L−P) are (1−x)(4x−1)(9664x⁴+12080x³+2292x²−155x+941), and 137(L+P)=(4x−3)²(2416x⁴+3624x³+1479x²+180x−135). The last quartic equals 137/2+(x−1/4)(2416x³+4228x²+2536x+814). The interval factors are nonnegative; evenness extends the bound to [−1,1]. The contacts 1,3/4,1/4,0,−1/4,−3/4,−1 have values 3782/137,−2567/137,1,−1,1,−2567/137,3782/137, respectively. The private lemmas P_bound_small, P_bound_large and P_snake establish these snake conditions. Comparing the coefficients of x⁰,x²,x⁴,x⁶ in a representation by T₀,…,T₆ forces a₀=−459/274, as proved by constant_coefficient_negative. The exact polynomial expansion is P=(−459/274)T₀+(1503/274)T₂+(2052/137)T₄+(1208/137)T₆. Thus nonnegative coefficients are impossible. Nikolov–Shadrin, arXiv:1210.7795, uses positive expansion as a sufficient hypothesis for extremality in majorant inequalities. This refutation leaves the folklore Markov-extremality conjecture and UP24 Problem 7.1 open; it also leaves strictly convex or smoother majorants and degrees at most five unsettled. Literature coverage is limited to the cited arXiv versions.

## References

- Truth anchor: `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.IsSnake`
- Truth anchor: `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result`
