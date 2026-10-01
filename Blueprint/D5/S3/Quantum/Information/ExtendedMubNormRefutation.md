# A counterexample to the extended MUB norm conjecture

## Abstract

The doubly stochastic matrix I/2 + J/6 in dimension three satisfies the spectral condition of the extended MUB conjecture at mu = lambda = 2/3, but a nonzero real vector gives a mixed norm ratio strictly above the predicted norm.

**Definition 1.1 (Doubly stochastic matrices).**

$$\forall d : \mathbb{N}, \forall C : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right), \operatorname{DoublyStochastic}\left(C\right) \Leftrightarrow (C \in \operatorname{doublyStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.DoublyStochastic` (`✓ std3`).

*Citation.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

Membership in Mathlib's doublyStochastic over the reals means nonnegative entries and every row sum and column sum equal to one. Fin(d) indexes rows and columns by 0, ..., d - 1.

**Definition 1.2 (The second largest singular value).**

$$\forall d : \mathbb{N}, \forall C : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right), \operatorname{sigma2}\left(C\right) = \operatorname{ite}\left(1 < d, \sqrt{\operatorname{eigenvaluesZero}\left(C^{*} \cdot C, 1\right)}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.sigma2` (`✓ std3`).

*Citation.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

For d >= 2, sigma2 is the nonnegative square root of the eigenvalue at index 1 in the descending, multiplicity-preserving eigenvaluesZero list of the Hermitian Gram matrix C* C. Here C* is conjugate transpose, which equals transpose over the reals. The index is the Fin(card(Fin(d))) element with value 1; the definition extends by zero when d <= 1, outside the conjecture's domain. The operator ite selects its second argument when its first argument holds and its third argument otherwise.

**Definition 1.3 (Ordinary finite real lp norms).**

$$\forall d : \mathbb{N}, \forall p : \mathbb{R}, \forall x : \operatorname{Fin}\left(d\right) \to \mathbb{R}, \operatorname{lpNorm}\left(p, x\right) = (\sum_{i \in \operatorname{Fin}\left(d\right)} \left|x\left(i\right)\right|^{p})^{\frac{1}{p}}$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.lpNorm` (`✓ std3`).

*Citation.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

For positive finite p this expression is the ordinary lp norm, without normalizing counting measure. Powers use Real.rpow. In the theorem, the expression is identified with the norm on Mathlib's PiLp(ENNReal.ofReal(p)) by PiLp.norm_eq_sum.

**Definition 1.4 (All nonzero-vector norm ratios).**

$$\forall d : \mathbb{N}, \forall C : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right), \forall p : \mathbb{R}, \forall q : \mathbb{R}, \operatorname{ratios}\left(C, p, q\right) = \{r : \mathbb{R} \mid \exists x : \operatorname{Fin}\left(d\right) \to \mathbb{R}, (x \ne 0) \land (r = \frac{\operatorname{lpNorm}\left(q, \operatorname{mulVec}\left(C, x\right)\right)}{\operatorname{lpNorm}\left(p, x\right)})\}$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.ratios` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set contains the output q-norm divided by the input p-norm for every nonzero real vector; signs of coordinates are unrestricted. Matrix multiplication acts on column vectors.

**Definition 1.5 (The mixed operator norm).**

$$\forall d : \mathbb{N}, \forall C : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right), \forall p : \mathbb{R}, \forall q : \mathbb{R}, \operatorname{opNorm}\left(C, p, q\right) = \operatorname{sSup}\left(\operatorname{ratios}\left(C, p, q\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.opNorm` (`✓ std3`).

*Citation.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

The supremum of the ratio set is the ordinary real mixed operator norm for p, q >= 1. The proof bounds the ratio set using the continuous linear map between finite PiLp spaces and its operator norm. The conjecture only uses exponents greater than one.

**Definition 1.6 (Conjecture 1: extended MUB regime).**

$$claim \Leftrightarrow (\forall d : \mathbb{N}, \forall C : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right), \forall \mu : \mathbb{R}, \forall \lambda : \mathbb{R}, (2 \le d) \Rightarrow \left((\operatorname{DoublyStochastic}\left(C\right)) \Rightarrow \left((0 < \mu) \Rightarrow \left((\mu < 1) \Rightarrow \left((0 < \lambda) \Rightarrow \left((\lambda < 1) \Rightarrow \left((\operatorname{sigma2}\left(C\right)^{2} \le \frac{1 - \mu}{\mu} \cdot \frac{1 - \lambda}{\lambda}) \Rightarrow \operatorname{opNorm}\left(C, \frac{1}{\mu}, \frac{1}{1 - \lambda}\right) = \operatorname{val}\left(d\right)^{1 - \lambda - \mu}\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/ExtendedMubNormRefutation.claim` (`✓ std3`).

*Citation.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

Conjecture 1 (arXiv:2303.11382v1, p. 2): "(Extended MUB regime). Let C⁽²⁾ be a doubly stochastic matrix. Its norm is equal to that of C⁽²⁾_MUB, i.e. it is given by eq. (7), as long as (1−μ)/μ (1−λ)/λ ≥ σ₂², where σ₂ is the second largest singular value of C⁽²⁾." Equation (7) reads that the logarithm of the MUB norm from 1/μ to 1/(1−λ) equals (1−λ−μ) log d. The encoding uses C for C⁽²⁾, d >= 2, and 0 < mu, lambda < 1, with ordinary real-vector norms; val(d) is the coercion of the natural dimension to the reals. Equation (5) in the source allows complex vectors; the real vector used below belongs to that larger domain as well, so its strict lower bound also rules out the source's proposed complex norm value. No equality between real and complex operator norms is needed for this counterexample.

**Theorem 1.7 (The predicted norm equality fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ExtendedMubNormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rotundo-schwonnek-2023-extended-mub-norm-refutation` (refuted) by `D5/S3/Quantum/Information/ExtendedMubNormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rotundo-schwonnek-2023-extended-mub-norm-refutation","declaration_gid":"D5/S3/Quantum/Information/ExtendedMubNormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antonio F. Rotundo; René Schwonnek (2023). *An entropic uncertainty principle for mixed states*. DOI: [10.1103/PhysRevResearch.6.033043](https://doi.org/10.1103/PhysRevResearch.6.033043). URL: <https://arxiv.org/abs/2303.11382v1>.

*Commentary.*

Set d = 3, C = I/2 + J/6, x = (4,1,1), and mu = lambda = 2/3. The matrix is doubly stochastic. Its Gram matrix is I/4 + J/4, with descending eigenvalues (1,1/4,1/4), so sigma2(C) = 1/2 and the spectral condition holds with equality. The input exponent is 3/2 and the output exponent is 3. Since Cx = (3,3/2,3/2), the input norm cubed is 100 and the output norm cubed is 135/4. The norm ratio cubed is therefore 27/80 > 1/3, whereas the conjectured value 3^(-1/3) has cube 1/3. Boundedness of the ratio set makes this ratio a lower bound for its supremum, contradicting the predicted equality. This argument supplies a lower bound, without asserting that x maximizes the ratio; it concerns the arXiv norm statement rather than the journal's entropic reformulation.

## References

- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.DoublyStochastic`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.lpNorm`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.opNorm`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.ratios`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/ExtendedMubNormRefutation.sigma2`
