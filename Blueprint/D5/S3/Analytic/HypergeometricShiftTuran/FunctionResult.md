# The function Turanian can be negative

## Abstract

A convergent-series counterexample to the function clause of Conjecture 1.

**Definition 1.1 (The function in equation (10)).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.fval`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.fval` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Equation (10), page 5 of arXiv:1611.06724v1: “f (µ; x) = Γ(a + µ)/Γ(b + µ) pFq(a + µ; b + µ; x) = ∑ₙ₌₀∞ Γ(a + µ + n)/Γ(b + µ + n) xⁿ/n!.” Vector Gamma values denote products over entries. The Lean definition is the real tsum of Defs.coeff a b (mu+n) times x to the power n divided by n factorial. At the counterexample all three series converge, as follows from the Gamma recurrence and a geometric bound after index eight.

**Definition 1.2 (The function Turanian).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.turanian`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.turanian` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Equation (9), page 5: “∆f (α, β; x) := f (µ + α; x)f (µ + β; x) − f (µ; x)f (µ + α + β; x) = ∑ₘ₌₀∞ δm xᵐ”. The definition retains the two shifted products with exactly this subtraction order.

**Definition 1.3 (The universal function assertion).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Theorem 3, page 5: “Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.”

Conjecture 1, page 6: “Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.” The claim is precisely its function clause in the p at most q branch: all positive numerator and denominator parameter vectors satisfying Defs.cond13, all mu at least one, all nonnegative alpha, beta and x. It imposes no alpha at most beta+1 condition, since that restriction belongs to the coefficient clause. A zero-length numerator is permitted, and condition (13) is then vacuous.

**Theorem 1.4 (Refutation by an exact series estimate).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-pfq-conjecture-one-function` (refuted) by `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-pfq-conjecture-one-function","declaration_gid":"D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Take p=0, q=12, every denominator parameter equal to one half, mu=1, alpha=beta=1/2 and x=5000. Write A=fval at mu=3/2, fval at mu=1 as pi to the power -6 times R, and fval at mu=2 as pi to the power -6 times S. The integer and half-integer Gamma formulas give positive rational series for A, R and S.

Use the first eight terms for each series. The tail of A is at most its term of index eight divided by 1-rho, where rho=5000/(9 times 10 to the power 12). The upper bound for A is at most 9/4. The first eight rational terms of R sum to at least 161000 and those of S to at least 34; these lower bounds already follow from their first two terms. Mathlib's pi<3.1416 and exact rational arithmetic give (9/4) squared times pi to the power 12 less than 161000 times 34. Therefore A squared is strictly smaller than pi to the power -12 times R times S. The Turanian is strictly negative.

The dimensions, positive denominator parameters and nonnegative shifts satisfy every hypothesis of claim. Thus universal function nonnegativity is false. Theorem 3's integer-shift statement is unaffected by these two half shifts.

## References

- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.fval`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.turanian`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/Defs](Defs.md)
