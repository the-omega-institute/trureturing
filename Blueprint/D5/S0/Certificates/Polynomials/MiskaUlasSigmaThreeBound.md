# The first bound of Miska–Ulas Conjecture 4.8 is false

## Abstract

A positive integer family refutes the degree-six symmetric-product bound.

**Definition 1.1 (Conjecture 4.8).**

$$\operatorname{claim} \Leftrightarrow (\forall n: \mathbb{N}, (4 \le n) \Rightarrow (\forall X: \operatorname{Fin}\left(n\right) \to \mathbb{N}, (\forall i: \operatorname{Fin}\left(n\right), 0 < X\left(i\right)) \Rightarrow ((\operatorname{Monotone}\left(X\right)) \Rightarrow (\forall m: \mathbb{N}, (m = \operatorname{MvPolynomial.eval}\left(X, \operatorname{MvPolynomial.esymm}\left(\operatorname{Fin}\left(n\right), \mathbb{N}, 3\right)\right)) \Rightarrow ((m = \operatorname{MvPolynomial.eval}\left(X, \operatorname{MvPolynomial.esymm}\left(\operatorname{Fin}\left(n\right), \mathbb{N}, n\right)\right)) \Rightarrow (((m: \mathbb{Q}) \le \frac{1}{12} \cdot (3021 \cdot (n: \mathbb{Q})^{6} - 77575 \cdot (n: \mathbb{Q})^{5} + 920361 \cdot (n: \mathbb{Q})^{4} - 6235705 \cdot (n: \mathbb{Q})^{3} + 24764202 \cdot (n: \mathbb{Q})^{2} - 53664304 \cdot (n: \mathbb{Q}) + 48986640)) \land ((X\left(\langle n - 1\rangle\right): \mathbb{Q}) \le \frac{1}{12} \cdot (27 \cdot (n: \mathbb{Q})^{4} - 190 \cdot (n: \mathbb{Q})^{3} + 471 \cdot (n: \mathbb{Q})^{2} - 500 \cdot (n: \mathbb{Q}) + 216))))))))$$

*Formalization.* `D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound.claim` (`✓ std3`).

*Citation.* Piotr Miska; Maciej Ulas (2022). *On the Diophantine equation σ₂(X̄ₙ) = σₙ(X̄ₙ)*. DOI: [10.1142/S1793042124500635](https://doi.org/10.1142/S1793042124500635). URL: <https://arxiv.org/abs/2203.03942v1>.

*Commentary.*

Page 16: “Let n ∈ N≥4 and suppose that m ∈ N satisfies m = σ_3(X_n) = σ_n(X_n). Then m ≤ (1/12)(3021n⁶ − 77575n⁵ + 920361n⁴ − 6235705n³ + 24764202n² − 53664304n + 48986640) and x_n ≤ (1/12)(27n⁴ − 190n³ + 471n² − 500n + 216).”

Page 1: “Let n ∈ N≥3 and for given k ≤ n consider the k-th symmetric polynomial σ_k(x_1, . . . , x_n) = Σ_{i_1<i_2<...<i_k} x_{i_1} · · · x_{i_k}.” Page 2: “By a solution of (1) we mean a sequence X_n = (x_1, . . . , x_n) satisfying the condition x_i ≤ x_{i+1} for i = 1, . . . , n − 1”, in positive integers.

The tuple is indexed by Fin n, starting at zero. MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ k) is the sum of products over k-element subsets. Monotone X expresses the source's nondecreasing order. The last index is the element of Fin n with value n − 1; its proof of being less than n is omitted in the display and follows from 4 ≤ n. The polynomial arithmetic and all displayed casts use ℚ.

**Theorem 1.2 (Refutation).**

$$\neg (\forall n: \mathbb{N}, (4 \le n) \Rightarrow (\forall X: \operatorname{Fin}\left(n\right) \to \mathbb{N}, (\forall i: \operatorname{Fin}\left(n\right), 0 < X\left(i\right)) \Rightarrow ((\operatorname{Monotone}\left(X\right)) \Rightarrow (\forall m: \mathbb{N}, (m = \operatorname{MvPolynomial.eval}\left(X, \operatorname{MvPolynomial.esymm}\left(\operatorname{Fin}\left(n\right), \mathbb{N}, 3\right)\right)) \Rightarrow ((m = \operatorname{MvPolynomial.eval}\left(X, \operatorname{MvPolynomial.esymm}\left(\operatorname{Fin}\left(n\right), \mathbb{N}, n\right)\right)) \Rightarrow (((m: \mathbb{Q}) \le \frac{1}{12} \cdot (3021 \cdot (n: \mathbb{Q})^{6} - 77575 \cdot (n: \mathbb{Q})^{5} + 920361 \cdot (n: \mathbb{Q})^{4} - 6235705 \cdot (n: \mathbb{Q})^{3} + 24764202 \cdot (n: \mathbb{Q})^{2} - 53664304 \cdot (n: \mathbb{Q}) + 48986640)) \land ((X\left(\langle n - 1\rangle\right): \mathbb{Q}) \le \frac{1}{12} \cdot (27 \cdot (n: \mathbb{Q})^{4} - 190 \cdot (n: \mathbb{Q})^{3} + 471 \cdot (n: \mathbb{Q})^{2} - 500 \cdot (n: \mathbb{Q}) + 216))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Piotr Miska; Maciej Ulas (2022). *On the Diophantine equation σ₂(X̄ₙ) = σₙ(X̄ₙ)*. DOI: [10.1142/S1793042124500635](https://doi.org/10.1142/S1793042124500635). URL: <https://arxiv.org/abs/2203.03942v1>.

*Commentary.*

For k ≥ 7 put n = k + 4, c = 3 σ₂(1ᵏ) + 8k + 7, and let Y consist of k ones followed by 2, k + 3, c. Put d = σ₃(Y) and append d to Y. The identity σ₂(Y) + 1 = 2(k + 3)c makes the resulting tuple solve σ₃ = σₙ. Its entries are positive and nondecreasing. The difference between its product and the proposed degree-six bound is (27/4) k(k − 1)(k − 2)(k − 3)(k − 4)(k − 5)(k − 6), positive for k ≥ 7. The proof specializes this family to n = 11.

The last coordinate on this family equals the proposed quartic bound. Thus this family contradicts the first bound while attaining equality in the second. The universal second bound remains open. The source's results about σ₂ = σₙ concern a different equation and are unaffected by this refutation of its final conjecture about σ₃.

## References

- Truth anchor: `D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound.claim`
- Truth anchor: `D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound.result`
