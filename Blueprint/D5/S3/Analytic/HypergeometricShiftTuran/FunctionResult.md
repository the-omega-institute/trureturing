# The function Turanian can be negative

## Abstract

A convergent-series counterexample to the function clause of Conjecture 1.

**Definition 1.1 (The function in equation (10)).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(p\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(q\right) \to \mathbb{R},\; \forall mu \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{fval}\left(a, b, mu, x\right) = \sum'_{n: \mathbb{N}} \operatorname{Defs.coeff}\left(a, b, mu + n\right) \cdot \frac{x^{n}}{\operatorname{Nat.factorial}\left(n\right)}$$

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.fval` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Equation (10), page 5 of arXiv:1611.06724v1: “f (µ; x) = Γ(a + µ)/Γ(b + µ) pFq(a + µ; b + µ; x) = ∑ₙ₌₀∞ Γ(a + µ + n)/Γ(b + µ + n) xⁿ/n!.” Vector Gamma values denote products over entries. The Lean definition is the real tsum of Defs.coeff a b (mu+n) times x to the power n divided by n factorial. At the counterexample all three series converge, as follows from the Gamma recurrence and a geometric bound after index eight.

**Definition 1.2 (The function Turanian).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(p\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(q\right) \to \mathbb{R},\; \forall mu \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{turanian}\left(a, b, mu, alpha, beta, x\right) = \operatorname{fval}\left(a, b, mu + alpha, x\right) \cdot \operatorname{fval}\left(a, b, mu + beta, x\right) - \operatorname{fval}\left(a, b, mu, x\right) \cdot \operatorname{fval}\left(a, b, mu + alpha + beta, x\right)$$

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.turanian` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Equation (9), page 5: “∆f (α, β; x) := f (µ + α; x)f (µ + β; x) − f (µ; x)f (µ + α + β; x) = ∑ₘ₌₀∞ δm xᵐ”. The definition retains the two shifted products with exactly this subtraction order.

**Definition 1.3 (The universal function assertion).**

$$claim = \left(\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(p\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(q\right) \to \mathbb{R},\; (1 \le p) \Rightarrow ((p \le q) \Rightarrow ((\forall i \in \operatorname{Fin}\left(p\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(q\right),\; 0 < b\left(j\right)) \Rightarrow ((\operatorname{Defs.cond13}\left(a, b\right)) \Rightarrow (\forall mu \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall x \in \mathbb{R},\; (1 \le mu) \Rightarrow ((0 \le alpha) \Rightarrow ((0 \le beta) \Rightarrow ((0 \le x) \Rightarrow (0 \le \operatorname{turanian}\left(a, b, mu, alpha, beta, x\right))))))))))\right)$$

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Theorem 3, page 5: “Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.”

Conjecture 1, page 6: “Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.” The claim is its function clause in the branch 1 ≤ p ≤ q: all positive numerator and denominator parameter vectors satisfying Defs.cond13, all mu at least one, all nonnegative alpha, beta and x. It imposes no alpha at most beta+1 condition, since that restriction belongs to the coefficient clause. Section 2, page 3, states: “We will always assume that a₂ is not empty (i.e. p₂ ≥ 1), while all other subvectors are allowed to be empty.” It continues: “In this section we will consider log-convexity of the function f (µ; x) defined in (3) under these assumptions.” Section 3 sets a₁ and b₁ empty, so a=a₂. Whether nonemptiness carries into that section or is local to Section 2, the witness with p=1 belongs to the domain. Refuting the claim with 1 ≤ p refutes both readings.

**Theorem 1.4 (Refutation by an exact series estimate).**

$$\neg (\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(p\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(q\right) \to \mathbb{R},\; (1 \le p) \Rightarrow ((p \le q) \Rightarrow ((\forall i \in \operatorname{Fin}\left(p\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(q\right),\; 0 < b\left(j\right)) \Rightarrow ((\operatorname{Defs.cond13}\left(a, b\right)) \Rightarrow (\forall mu \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall x \in \mathbb{R},\; (1 \le mu) \Rightarrow ((0 \le alpha) \Rightarrow ((0 \le beta) \Rightarrow ((0 \le x) \Rightarrow (0 \le \operatorname{turanian}\left(a, b, mu, alpha, beta, x\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-pfq-conjecture-one-function` (refuted) by `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-pfq-conjecture-one-function","declaration_gid":"D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Take p=1, a=(1), q=12, every denominator parameter equal to one half, mu=1, alpha=beta=1/2 and x=2000. Write fval at mu=3/2 as sqrt(pi) times A′, fval at mu=1 as pi to the power -6 times R, and fval at mu=2 as pi to the power -6 times S. The integer and half-integer Gamma formulas give positive rational series for A′, R and S.

Use the first ten terms for each series. The tail of A′ is at most its term of index ten divided by 1-rho, where rho=74/100000000000 bounds every successive ratio after index nine. The resulting upper bound for A′ is at most 1672/1000. The first ten rational terms of R sum to at least 136700 and those of S to at least 69; these lower bounds already follow from their first three terms. Mathlib's pi<3.1416 and exact rational arithmetic give (1672/1000) squared times pi to the power 13 less than 136700 times 69. Hence pi times A′ squared is strictly smaller than pi to the power -12 times R times S. The Turanian is strictly negative.

The numerator is nonempty and all parameters are positive. Condition (13) reduces to (1/2)^12 ≤ 12(1/2)^11; the dimensions and nonnegative shifts satisfy every hypothesis of claim. Thus universal function nonnegativity is false. Theorem 3's integer-shift statement is unaffected by these two half shifts.

## References

- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.fval`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.turanian`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/Defs](Defs.md)
