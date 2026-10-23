# Pick functions do not preserve embeddable matrices

## Abstract

A positive Pick function sends an embeddable stochastic matrix to a matrix with a negative entry.

Johnson, Mondal, and Tsatsomeros, Powers, Roots, and Positivity, arXiv:2609.06298v1, Table 2, Behavior of Matrix Classes under Pick Functions and Fractional Powers, p. 22, row 13, verbatim: “Embeddable Matrix | Open | Yes”. The note below the table states verbatim: “The entries marked Open indicate cases for which preservation under Pick functions remains an open question.” Remark 3.28, p. 17, states verbatim: “The embedding problem, introduced in [11], asks whether a given stochastic matrix A can be realized as the transition matrix of a continuous-time Markov process. It was shown in [24] that a nonsingular stochastic matrix A is embeddable if and only if A = e^B for some essentially nonnegative matrix B satisfying Be = 0.”

**Definition 1.1 (Stochastic matrices).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \operatorname{IsStochastic}\left(A\right) \Leftrightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), 0 \le \operatorname{entry}\left(A, i, j\right)) \land (\forall i: \operatorname{Fin}\left(n\right), \operatorname{sum}\left(j, \operatorname{Fin}\left(n\right), \operatorname{entry}\left(A, i, j\right)\right) = 1))$$

*Formalization.* `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.IsStochastic` (`✓ std3`).

*Citation.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

A real n×n matrix is stochastic when every entry is nonnegative and every row sums to one.

**Definition 1.2 (Embeddable stochastic matrices).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \operatorname{IsEmbeddable}\left(A\right) \Leftrightarrow ((\operatorname{IsStochastic}\left(A\right)) \land ((\operatorname{IsUnit}\left(\operatorname{det}\left(A\right)\right)) \land (\exists B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), (\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (\neg (i = j)) \Rightarrow (0 \le \operatorname{entry}\left(B, i, j\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), \operatorname{sum}\left(j, \operatorname{Fin}\left(n\right), \operatorname{entry}\left(B, i, j\right)\right) = 0) \land (\operatorname{exp}\left(B\right) = A)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.IsEmbeddable` (`✓ std3`).

*Citation.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

Remark 3.28 characterizes embeddability by a real generator B with nonnegative off-diagonal entries and zero row sums, whose exponential is A. The definition also requires stochasticity and a unit determinant. Mathlib's NormedSpace.exp on matrices uses the product topology.

**Definition 1.3 (Preservation of embeddable matrices).**

$$claim \Leftrightarrow (\forall k: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, \forall t: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall w: \operatorname{Fin}\left(k\right) \to \mathbb{R}, (0 \le b) \Rightarrow ((\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{t}\left(i\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(k\right), 0 \le \operatorname{w}\left(i\right)) \Rightarrow ((\forall x: \mathbb{R}, (0 < x) \Rightarrow (0 < \operatorname{pickFun}\left(a, b, t, w, x\right))) \Rightarrow (\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), (\operatorname{IsEmbeddable}\left(A\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (j < i) \Rightarrow (\operatorname{entry}\left(A, i, j\right) = 0)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), 0 < \operatorname{entry}\left(A, i, i\right)) \Rightarrow (\operatorname{IsEmbeddable}\left(\operatorname{pickCalc}\left(a, b, t, w, A\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

The assertion uses the public pickFun and pickCalc definitions from the frozen companion InfinitelyDivisiblePickRefutation. It quantifies over finite supports with b≥0, positive tᵢ, nonnegative wᵢ, and strict positivity on every positive real argument. For every dimension n, an embeddable upper-triangular matrix with positive diagonal must have an embeddable image. Its spectrum is its diagonal and lies in (0,∞)⊂D; the positive shifts are invertible. General preservation in Table 2, row 13, implies this restriction.

**Theorem 1.4 (A negative entry in dimension four).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnson-mondal-tsatsomeros-2026-embeddable-pick-refutation` (refuted) by `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnson-mondal-tsatsomeros-2026-embeddable-pick-refutation","declaration_gid":"D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

Let P have ones at (0,1), (1,2), (2,3), and (3,3), with every other entry zero. Let Q have ones in its last column and zeros elsewhere. Exact multiplication gives P³=Q and QP=Q; induction gives P^(k+3)=Q for every natural k. Splitting the exponential series after degree two yields exp P=I+P+P²/2+(e−5/2)Q, where e=exp(1). Commutation with −I gives A=exp(P−I)=e⁻¹(I+P+P²/2+(e−5/2)Q). The generator P−I has nonnegative off-diagonal entries and zero row sums. The matrix A has nonnegative entries, unit row sums, and diagonal (e⁻¹,e⁻¹,e⁻¹,1), so its determinant is e⁻³ and it is embeddable. It is upper triangular with positive diagonal. Take a=1, b=0, t=(1), w=(1), giving f(z)=2z/(1+z)>0 for real z>0. This is the finite-measure instance of Lemma 2.8. Its pole is outside D and its imaginary part is 2 Im z/|1+z|², explaining the analytic Pick property without a separate formalization. Writing d=1+e, an explicit right inverse C of A+I has rows (e/d,−e/d²,e(1−e)/(2d³),(−e³+2e²+2e+1)/(2d³)), (0,e/d,−e/d²,(1+2e−e²)/(2d²)), (0,0,e/d,(1−e)/(2d)), and (0,0,0,1/2). The proof checks (A+I)C=I and identifies C as the inverse. Remark 2.9 gives f[A]=2I−2C, whose (0,3) entry is (e³−2e²−2e−1)/(1+e)³<0, using certified bounds 2.718<e<2.72. Thus the (1,4) entry in one-based indices is negative, the image is not stochastic, and Table 2, row 13, has answer No. Rows 12 and 13 share the failure of entrywise positivity under positive Pick functions on non-normal matrices. Row 7, semipositive matrices, remains open.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.IsEmbeddable`
- Truth anchor: `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.IsStochastic`
- Truth anchor: `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation](InfinitelyDivisiblePickRefutation.md)
