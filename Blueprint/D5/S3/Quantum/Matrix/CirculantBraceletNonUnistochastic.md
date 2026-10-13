# Circulant bracelet sufficiency fails at order twelve

## Abstract

A circulant bracelet matrix of order twelve is not unistochastic.

Matrices have zero-based indices in Fin d. Subtraction in Fin d is modulo d. A sum indexed by Fin d includes every index exactly once. The real indexed supremum iSup is the maximum for the nonempty finite index sets in the question.

**Definition 1.1 (Circulant matrices).**

$$\forall (d: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), \operatorname{IsCirculant}\left(B\right) = \exists (v: \operatorname{Fin}\left(d\right) \to \mathbb{R}), B = \operatorname{Matrix.circulant}\left(v\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsCirculant` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Definition 5, page 4: "The set of d × d circulant matrices C_d consists of all matrices B whose entries satisfy [30] B_{j+l,k} = B_{j,k−l}, (7) where the addition and subtraction is modulo d." Matrix.circulant uses v(i−j); replacing the first row by its reversal gives the same set of matrices.

**Definition 1.2 (Unistochastic matrices).**

$$\forall (d: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), \operatorname{IsUnistochastic}\left(B\right) = \exists (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (B = \operatorname{RHLinalg.normSqMatrix}\left(U\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsUnistochastic` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Definition 4, page 3: "The set of d × d unistochastic matrices U_d consists of all bistochastic matrices B whose entries satisfy B_jk = |U_jk|² for some unitary matrix U." RHLinalg.normSqMatrix U has entry ‖U i j‖². Membership of U in Matrix.unitaryGroup implies bistochasticity of this squared-norm matrix.

**Definition 1.3 (Column and row bracelet conditions).**

$$\forall (d: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), \operatorname{IsBracelet}\left(B\right) = \left((B \in doublyStochastic\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)) \land ((\forall (k: \operatorname{Fin}\left(d\right)), \forall (l: \operatorname{Fin}\left(d\right)), (k \ne l) \Rightarrow (2 \cdot iSup\left(fun (j: \operatorname{Fin}\left(d\right)) \mapsto \operatorname{Real.sqrt}\left(B\left(j, k\right) \cdot B\left(j, l\right)\right)\right) \le \sum_{j: \operatorname{Fin}\left(d\right)} \operatorname{Real.sqrt}\left(B\left(j, k\right) \cdot B\left(j, l\right)\right))) \land (\forall (j: \operatorname{Fin}\left(d\right)), \forall (k: \operatorname{Fin}\left(d\right)), (j \ne k) \Rightarrow (2 \cdot iSup\left(fun (l: \operatorname{Fin}\left(d\right)) \mapsto \operatorname{Real.sqrt}\left(B\left(j, l\right) \cdot B\left(k, l\right)\right)\right) \le \sum_{l: \operatorname{Fin}\left(d\right)} \operatorname{Real.sqrt}\left(B\left(j, l\right) \cdot B\left(k, l\right)\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsBracelet` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Definition 7, page 4: "The set of d × d bracelet matrices L_d consists of these bistochastic matrices B whose entries satisfy:" equations (9a) and (9b), "which are called column and row bracelet conditions." The displayed inequalities are those two equations. The source counts d(d−1) conditions: distinct column pairs and distinct row pairs. Both orders of each pair give the same inequality.

**Definition 1.4 (The higher-dimensional sufficiency question).**

$$claim = \forall (d: \mathbb{N}), (4 < d) \Rightarrow (\forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), (\operatorname{IsCirculant}\left(B\right)) \Rightarrow ((\operatorname{IsBracelet}\left(B\right)) \Rightarrow (\operatorname{IsUnistochastic}\left(B\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.claim` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Section V, page 13: "Another observation that holds for d ≤ 4, and should be further investigated for d > 4, is whether the bracelet condition is sufficient for unistochasticity if we restrict the analysis to the set of circulant matrices." The formula quantifies over every natural d > 4 and every real d × d matrix. IsBracelet includes bistochasticity; IsUnistochastic allows an arbitrary complex unitary matrix, without requiring it to be circulant.

**Theorem 1.5 (A twelve-dimensional refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result` (`✓ std3`). ∎

*Resolves.* `Problems/rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency` (refuted) by `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency","declaration_gid":"D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Let S={0,1,3,4,6,9} modulo twelve, and put B(i,j)=1/6 when j−i belongs to S and zero otherwise. Every row and column contains six nonzero entries. Every distinct row or column pair overlaps in at least two positions, so all bracelet inequalities hold. If B were the squared-norm matrix of a unitary U, its zero entries would be exactly those of U. Put T={0,3,6,9}. Row 11 overlaps every row in T exactly in columns 0 and 3; row 2 overlaps them exactly in columns 3 and 6. Row orthogonality therefore gives common nonzero complex ratios λ and μ, with U(r,3)=λ U(r,0) and U(r,6)=μ U(r,3) for every r in T. Columns 0 and 6 overlap exactly on T, so their inner product is μλ·4/6, which is nonzero. This contradicts column orthogonality. Theorem 17, page 9, establishes the equality of circulant bracelet and circulant unistochastic matrices at dimension four. The counterexample concerns higher dimensions and does not decide the sufficiency question at dimensions five through eleven.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsBracelet`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsCirculant`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsUnistochastic`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result`
