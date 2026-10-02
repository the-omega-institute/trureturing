# The coefficients f_{N,k}(q) are polynomials

## Abstract

For all natural numbers N and k <= N, the coefficient f_{N,k}(q) = (q^{N-k} + q^k)/(1 + q^N) [N, k]_{q^2} in the partition function of the D_N-type Polychronakos-Frahm spin chain with polarized spin reversal operators is a polynomial in q. This proves the conjecture of B. Basu-Mallick, C. Datta, F. Finkel and A. Gonzalez-Lopez (arXiv:1503.08231).

**Definition 1.1 (The q-Pochhammer products).**

$$\forall j : \mathbb{N}, \operatorname{qPoch}\left(j\right) = \prod_{i=1}^{j} (1 - q^{2i})$$

*Formalization.* `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.qPoch` (`✓ std3`).

*Citation.* B. Basu-Mallick; C. Datta; F. Finkel; A. González-López (2015). *Rational quantum integrable systems of D_N type with polarized spin reversal operators*. DOI: [10.1016/j.nuclphysb.2015.06.016](https://doi.org/10.1016/j.nuclphysb.2015.06.016). URL: <https://arxiv.org/abs/1503.08231v1>.

*Commentary.*

Here q is the indeterminate of the field Q(q) of rational functions (RatFunc.X in Lean), and (q^2)_j is the product of 1 - q^{2i} over i = 1, ..., j, as in Eq. (m40) of the paper.

**Definition 1.2 (The q-binomial coefficients).**

$$\forall N : \mathbb{N}, \forall k : \mathbb{N}, \operatorname{qBinom}\left(N, k\right) = \frac{\operatorname{qPoch}\left(N\right)}{\operatorname{qPoch}\left(k\right) \cdot \operatorname{qPoch}\left(N-k\right)}$$

*Formalization.* `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.qBinom` (`✓ std3`).

*Citation.* B. Basu-Mallick; C. Datta; F. Finkel; A. González-López (2015). *Rational quantum integrable systems of D_N type with polarized spin reversal operators*. DOI: [10.1016/j.nuclphysb.2015.06.016](https://doi.org/10.1016/j.nuclphysb.2015.06.016). URL: <https://arxiv.org/abs/1503.08231v1>.

*Commentary.*

The q-binomial coefficient [N, k]_{q^2} is (q^2)_N / ((q^2)_k (q^2)_{N-k}) in Q(q); in Lean the subtraction N - k is natural-number subtraction, and the claim uses only k <= N.

**Definition 1.3 (The coefficients).**

$$\forall N : \mathbb{N}, \forall k : \mathbb{N}, \operatorname{coeffF}\left(N, k\right) = \frac{q^{N-k} + q^{k}}{1 + q^{N}} \cdot \operatorname{qBinom}\left(N, k\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.coeffF` (`✓ std3`).

*Citation.* B. Basu-Mallick; C. Datta; F. Finkel; A. González-López (2015). *Rational quantum integrable systems of D_N type with polarized spin reversal operators*. DOI: [10.1016/j.nuclphysb.2015.06.016](https://doi.org/10.1016/j.nuclphysb.2015.06.016). URL: <https://arxiv.org/abs/1503.08231v1>.

*Commentary.*

The coefficient f_{N,k}(q) of Eq. (m39) of the paper multiplies [N, k]_{q^2} by (q^{N-k} + q^k)/(1 + q^N).

**Definition 1.4 (The conjecture).**

$$claim \Leftrightarrow (\forall N : \mathbb{N}, \forall k : \mathbb{N}, k \le N \Rightarrow \exists p : \mathbb{Q}[q], \operatorname{coeffF}\left(N, k\right) = p)$$

*Formalization.* `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.claim` (`✓ std3`).

*Citation.* B. Basu-Mallick; C. Datta; F. Finkel; A. González-López (2015). *Rational quantum integrable systems of D_N type with polarized spin reversal operators*. DOI: [10.1016/j.nuclphysb.2015.06.016](https://doi.org/10.1016/j.nuclphysb.2015.06.016). URL: <https://arxiv.org/abs/1503.08231v1>.

*Commentary.*

For every N and every k <= N there is a polynomial p with rational coefficients whose image in Q(q) is f_{N,k}(q). The paper conjectures that f_{N,k}(q) is a polynomial in q.

**Theorem 1.5 (Polynomiality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/basu-mallick-2015-dn-psro-coefficient-polynomiality` (proved) by `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"basu-mallick-2015-dn-psro-coefficient-polynomiality","declaration_gid":"D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Basu-Mallick; C. Datta; F. Finkel; A. González-López (2015). *Rational quantum integrable systems of D_N type with polarized spin reversal operators*. DOI: [10.1016/j.nuclphysb.2015.06.016](https://doi.org/10.1016/j.nuclphysb.2015.06.016). URL: <https://arxiv.org/abs/1503.08231v1>.

*Commentary.*

Write B(a, b) = [a + b, a]_{q^2}. Since (q^2)_{j+1} = (q^2)_j (1 - q^{2(j+1)}) and (1 - q^{2a}) + q^{2a}(1 - q^{2b}) = 1 - q^{2(a+b)}, the q-Pascal rules B(a, b) = B(a - 1, b) + q^{2a} B(a, b - 1) and B(a, b) = q^{2b} B(a - 1, b) + B(a, b - 1) hold for a, b >= 1, so B(a, b) is a polynomial by induction on a + b, starting from B(a, 0) = B(0, b) = 1. Multiplying the first rule by q^b and the second by q^a and adding gives (q^b + q^a) B(a, b) = (1 + q^{a+b})(q^b B(a - 1, b) + q^a B(a, b - 1)). Hence f_{N,k} = q^{N-k} [N - 1, k - 1]_{q^2} + q^k [N - 1, k]_{q^2} for 1 <= k <= N - 1, and f_{N,0} = f_{N,N} = 1.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.coeffF`
- Truth anchor: `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.qBinom`
- Truth anchor: `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.qPoch`
- Truth anchor: `D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result`
