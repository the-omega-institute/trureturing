# Exact logistic Petz evaluation

## Abstract

The exact upper Petz weight gives a sharp uniform frequency-count bound for evaluation at zero.

Write w(t) = π/(cosh(2πt) + 1). Integrals in time use Lebesgue measure on the whole real line.

**Definition 1.1 (The log-exponential correlation).**

Lean statement: `D5/S3/Analytic/PetzLogisticEvaluation.correlation`

*Formalization.* `D5/S3/Analytic/PetzLogisticEvaluation.correlation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real frequencies ω indexed by a type ι, the complex matrix C = correlation(ω) has entry Cᵢⱼ equal to the integral over x > 0 of exp(−x) exp(i(ωⱼ − ωᵢ) log(x)/(2π)). The integral averages phase differences under the mean-one exponential law.

**Theorem 1.2 (Exact factorization of the logistic Fourier Gram).**

Lean statement: `D5/S3/Analytic/PetzLogisticEvaluation.exact_gram_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticEvaluation.exact_gram_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type ι and real frequency map ω, C is positive semidefinite, every Cᵢᵢ is one, and the integral of w(t) exp(i(ωⱼ − ωᵢ)t) is |Cᵢⱼ|² for every pair of indices. The identity includes coincident frequencies.

The Gamma integral evaluates the log-exponential correlation. Euler's reflection formula gives its squared modulus as (δ/2)/sinh(δ/2) for frequency difference δ ≠ 0, with value one at δ = 0. The cosine transform of w gives the same expression, and evenness cancels the sine transform.

**Theorem 1.3 (Evaluation at zero with the exact weight).**

Lean statement: `D5/S3/Analytic/PetzLogisticEvaluation.weighted_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticEvaluation.weighted_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type ι, real frequencies ω and complex coefficients a, let f(t) = Σᵢ aᵢ exp(iωᵢt). The density w(t)|f(t)|² is integrable and |f(0)|² is at most the integral of that density times the number of distinct frequencies. Equal frequencies are merged by summing their coefficients. The empty index type gives zero on both sides.

A Gram factorization of C gives unit vectors. The squared Frobenius norm of the sum of their rank-one outer products weighted by aᵢ is the logistic energy. Its trace is Σᵢ aᵢ, so the trace Cauchy–Schwarz inequality gives the count bound. This is the correlation-matrix case of Vybíral’s Schur product inequality (DOI 10.1016/j.aim.2020.107140).

**Theorem 1.4 (The least coefficient uniform in the frequencies).**

Lean statement: `D5/S3/Analytic/PetzLogisticEvaluation.card_le_of_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticEvaluation.card_le_of_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be a positive natural number. If a real K satisfies |f(0)|² ≤ K times the integral of w(t)|f(t)|² for every injective real frequency list on Fin m and every complex coefficient list on Fin m, then m ≤ K. The evaluation bound holds with K = m for every such list.

Take all coefficients equal to one and frequencies ωᵢ = iR for R > 0. The off-diagonal Fourier Gram entries tend to zero as R tends to infinity by the Riemann–Lebesgue lemma, while the diagonal stays one. The energy therefore tends to m and the squared evaluation is m².

## References

- Truth anchor: `D5/S3/Analytic/PetzLogisticEvaluation.card_le_of_uniform_bound`
- Truth anchor: `D5/S3/Analytic/PetzLogisticEvaluation.correlation`
- Truth anchor: `D5/S3/Analytic/PetzLogisticEvaluation.exact_gram_factorization`
- Truth anchor: `D5/S3/Analytic/PetzLogisticEvaluation.weighted_evaluation`
- Dependency: [D5/S3/Analytic/PetzStripFiniteSeries](PetzStripFiniteSeries.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../Quantum/GNSMatrix.md)
