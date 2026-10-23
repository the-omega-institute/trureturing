# Pick functions do not preserve strong infinite divisibility

## Abstract

A positive Pick function sends a 4×4 strongly infinitely divisible matrix to a matrix with a negative entry.

Johnson, Mondal, and Tsatsomeros, Powers, Roots, and Positivity, arXiv:2609.06298v1, Table 2, Behavior of Matrix Classes under Pick Functions and Fractional Powers, p. 22, row 12, verbatim: “Strongly Infinitely Divisible Matrix (SIDM) | Open | Yes”. The note below the table states verbatim: “The entries marked Open indicate cases for which preservation under Pick functions remains an open question.” The framing question in §1 is verbatim: “Given A ∈ C and a Pick function f, is f[A] ∈ C?” Definition 2.7 is verbatim: “Let D := C\(−∞, 0]. A complex function f analytic on D is called a Pick function if ℑf(z) ℑz ≥ 0, ∀z ∈ D”. Definition 3.25 is verbatim: “A nonnegative matrix A ∈ Mn(R) is said to be an infinitely divisible matrix (IDM) if, for every positive integer m, there exists a nonnegative matrix Km such that (Km)^m = A. If, in addition, A is invertible, then A is called a strongly infinitely divisible matrix (SIDM).”

**Definition 1.1 (Strong infinite divisibility).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \operatorname{IsSIDM}\left(A\right) \Leftrightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), 0 \le \operatorname{entry}\left(A, i, j\right)) \land ((\operatorname{IsUnit}\left(\operatorname{det}\left(A\right)\right)) \land (\forall m: \mathbb{N}, (0 < m) \Rightarrow (\exists K: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), (\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), 0 \le \operatorname{entry}\left(K, i, j\right)) \land (K^{m} = A)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.IsSIDM` (`✓ std3`).

*Citation.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

For a real n×n matrix A, IsSIDM A requires every entry to be nonnegative, the determinant to be a unit, and a nonnegative mth root for every positive integer m. Over the reals the unit-determinant condition is equivalent to invertibility, as in Definition 3.25.

**Definition 1.2 (Finite-measure Pick function).**

$$\forall k: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, \forall t: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall w: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall x: \mathbb{R}, \operatorname{pickFun}\left(a, b, t, w, x\right) = a + b \cdot x + \operatorname{sum}\left(i, \operatorname{Fin}\left(k\right), \operatorname{w}\left(i\right) \cdot \frac{\operatorname{t}\left(i\right) \cdot x - 1}{\operatorname{t}\left(i\right) + x}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.pickFun` (`✓ std3`).

*Citation.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

The finite-sum instance of Lemma 2.8 is a+bx+Σᵢwᵢ(tᵢx−1)/(tᵢ+x). Positive support points tᵢ and nonnegative weights wᵢ represent a positive finitely supported measure. The definition records the real-axis values; the source supplies the analytic Pick representation.

**Definition 1.3 (Finite-measure matrix calculus).**

$$\forall k: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, \forall t: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall w: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \operatorname{pickCalc}\left(a, b, t, w, A\right) = (a) \cdot (I) + (b) \cdot (A) + \operatorname{sum}\left(i, \operatorname{Fin}\left(k\right), (\operatorname{w}\left(i\right)) \cdot ((\operatorname{t}\left(i\right)) \cdot (I) - (1 + \operatorname{t}\left(i\right)^{2}) \cdot (\operatorname{inverse}\left(A + (\operatorname{t}\left(i\right)) \cdot (I)\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.pickCalc` (`✓ std3`).

*Citation.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

Remark 2.9 gives aI+bA+Σᵢwᵢ(tᵢI−(1+tᵢ²)(A+tᵢI)⁻¹) for matrices with spectrum in D. The preservation assertion restricts to upper-triangular matrices with positive diagonal, whose spectrum is their diagonal and lies in (0, ∞) ⊂ D. Since tᵢ>0, the shifted matrices also have positive diagonal and are invertible, so the inverses are genuine matrix inverses.

**Definition 1.4 (Preservation of SIDM).**

$$claim \Leftrightarrow (\forall k: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, \forall t: \operatorname{Fin}\left(k\right) \to \mathbb{R}, \forall w: \operatorname{Fin}\left(k\right) \to \mathbb{R}, (0 \le b) \Rightarrow ((\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{t}\left(i\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(k\right), 0 \le \operatorname{w}\left(i\right)) \Rightarrow ((\forall x: \mathbb{R}, (0 < x) \Rightarrow (0 < \operatorname{pickFun}\left(a, b, t, w, x\right))) \Rightarrow (\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), (\operatorname{IsSIDM}\left(A\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (j < i) \Rightarrow (\operatorname{entry}\left(A, i, j\right) = 0)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), 0 < \operatorname{entry}\left(A, i, i\right)) \Rightarrow (\operatorname{IsSIDM}\left(\operatorname{pickCalc}\left(a, b, t, w, A\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

The assertion quantifies over every finite support, real a and b, positive tᵢ, nonnegative wᵢ, and b≥0. It assumes that pickFun is strictly positive for every positive real argument. For every dimension n and real SIDM A that is upper triangular with positive diagonal, it requires pickCalc to be SIDM. Such matrices have spectrum equal to their diagonal, inside (0, ∞) ⊂ D, so Remark 2.9 applies. The general preservation statement in Table 2, row 12, would imply this restriction; failure within it therefore refutes the general statement.

**Theorem 1.5 (A negative entry in dimension four).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnson-mondal-tsatsomeros-2026-sidm-pick-refutation` (refuted) by `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnson-mondal-tsatsomeros-2026-sidm-pick-refutation","declaration_gid":"D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. R. Johnson; S. Mondal; M. J. Tsatsomeros (2026). *Powers, Roots, and Positivity*. DOI: [10.48550/arXiv.2609.06298](https://doi.org/10.48550/arXiv.2609.06298). URL: <https://arxiv.org/abs/2609.06298v1>.

*Commentary.*

Take a=1, b=0, t=(1), and w=(1), giving f(z)=2z/(1+z). For x>0 its real value 2x/(1+x) is positive. Its pole is outside D and Im f(z)=2 Im z/|1+z|², so it is a Pick function in Definition 2.7; this complex analytic explanation is not separately formalized here. Let N be the 4×4 shift and E(s)=I+sN+(s²/2)N²+(s³/6)N³. Exact multiplication gives E(s)E(u)=E(s+u), and induction gives E(s)^m=E(ms). The matrix A=E(1) has determinant 1 and nonnegative roots E(1/m) for every positive integer m. It is upper triangular with diagonal 1, so its spectrum is {1} ⊂ (0, ∞) ⊂ D and it satisfies the matrix restriction. The proof verifies (A+I)C=I for C=(1/2)I−(1/4)N+(1/48)N³ and identifies C with the inverse. Then pickCalc=2I−2C=I+N/2−N³/24 has entry −1/24 at (1,4), using one-based indices, or (0,3) in Fin 4. This contradicts its required nonnegativity. Table 2, row 12, has answer No. The nilpotent power series f[eᴺ]=I+tanh(N/2) explains the zero quadratic coefficient and negative cubic coefficient; for the 3×3 shift it gives I+N/2, which is nonnegative. This is the first negative entry in this shift family, not a classification of all smaller SIDM matrices. A double-precision computation for the Markov generator B=N−diag(1,1,1,0) gives f[eᴮ] with row sums 1 and (1,4) entry approximately −0.0219644568959024. It therefore fails to be stochastic. This numerical observation is not formalized and has no certified error bound; it suggests a negative answer for row 13. Rows 7 and 13 are not settled by this theorem. The source quotations bind to arXiv:2609.06298v1; their independent retrieval and any exhaustive literature or priority claim are ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.IsSIDM`
- Truth anchor: `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.pickCalc`
- Truth anchor: `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.pickFun`
- Truth anchor: `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result`
