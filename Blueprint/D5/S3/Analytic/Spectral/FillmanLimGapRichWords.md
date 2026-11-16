# FillmanLimGapRichWords

## Abstract

Periodic word metrics and positive products admit compatible realizations.

**Definition 1.1 (Word).**

$$\forall Y: Type, Word\left(Y\right) = (\{length: PNat; letter: Fin\left(val\left(length, Nat\right)\right) \to Y\})$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.Word` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 5, Definition 2.2: “Given a metric space (Y,d) and k ∈ ℕ, we denote a typical element in the product space Yᵏ by y = y₁⋯yₖ. We refer to y as a word.” “The set of words over Y is denoted by” Y⋆ := ⋃ₖ₌₁∞ Yᵏ. The record stores its positive length and its zero-based finite coordinate function.

**Definition 1.2 (concat).**

$$\forall Y: Type, \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), concat\left(x, y\right) = (\langle (\operatorname{Word}.\operatorname{length}\left(x\right))+(\operatorname{Word}.\operatorname{length}\left(y\right)), \operatorname{Fin}.\operatorname{append}\left(\operatorname{Word}.\operatorname{letter}\left(x\right), \operatorname{Word}.\operatorname{letter}\left(y\right)\right) \rangle)$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.concat` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 5, Definition 2.2: “The concatenation of words y ∈ Yᵏ and z ∈ Yˡ is denoted by” y♯z = y₁⋯yₖz₁⋯zₗ ∈ Yᵏ⁺ˡ. Fin.append preserves this coordinate order.

**Definition 1.3 (periodicLetter).**

$$\forall Y: Type, \forall x: Word\left(Y\right), \forall j: Nat, periodicLetter\left(x, j\right) = (\operatorname{Word}.\operatorname{letter}\left(x\right)\left(\langle j \bmod val\left(\operatorname{Word}.\operatorname{length}\left(x\right), Nat\right) \rangle\right))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.periodicLetter` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 5, Definition 2.2: “We denote by y♯ᵐ the result of concatenating m copies of y.” The zero-based periodic index is j modulo the positive length; the angle brackets form a Fin index.

**Definition 1.4 (wordDistance).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), wordDistance\left(x, y\right) = (\operatorname{Finset}.\operatorname{sup}'\left(\operatorname{Finset}.\operatorname{range}\left((val\left(\operatorname{Word}.\operatorname{length}\left(x\right), Nat\right)) * (val\left(\operatorname{Word}.\operatorname{length}\left(y\right), Nat\right))\right), (fun j: Nat \mapsto dist\left(periodicLetter\left(x, j\right), periodicLetter\left(y, j\right)\right))\right))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordDistance` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 5, Definition 2.2: “For y ∈ Yᵏ, z ∈ Yˡ, we define” d(y,z) := sup over 1 ≤ j ≤ kl of d((y♯ˡ)ⱼ,(z♯ᵏ)ⱼ). The finite supremum uses the same positions numbered from zero; its proof of nonemptiness follows from the positive lengths and is implicit. The val operations show coercions to Nat.

**Definition 1.5 (extend).**

$$\forall Y: Type, \forall A: Y \to \left(Real \to Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right)\right), \forall x: Word\left(Y\right), \forall E: Real, extend\left(A, x, E\right) = (\operatorname{List}.\operatorname{foldl}\left((fun M: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right) \mapsto (fun y: Y \mapsto (A\left(y, E\right)) * (M))), 1, \operatorname{List}.\operatorname{ofFn}\left(\operatorname{Word}.\operatorname{letter}\left(x\right)\right)\right))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.extend` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 5, Definition 2.3: “Given a function A : Y × ℝ → SL(2,ℝ), there is a unique extension A : Y⋆ × ℝ → SL(2,ℝ) such that” A(y♯z,E) = A(z,E)A(y,E). The left fold multiplies each successive letter on the left. The matrix-valued extension also permits arbitrary real matrices.

**Definition 1.6 (transfer).**

$$\forall x: Real, \forall E: Real, transfer\left(x, E\right) = (!![E-x, -1; 1, 0])$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.transfer` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 7, Definition 2.9: “The transfer matrix T : ℝ × ℝ → SL(2,ℝ) for the Schrödinger operator on ℓ²(ℤ), is given by” T(x,E) = [[E−x,−1],[1,0]]. The matrix has determinant one.

**Definition 1.7 (blockTransfer).**

$$\forall k: Nat, \forall x: EuclideanSpace\left(Real, Fin\left(k\right)\right), \forall E: Real, blockTransfer\left(x, E\right) = (\operatorname{List}.\operatorname{foldl}\left((fun M: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right) \mapsto (fun a: Real \mapsto (transfer\left(a, E\right)) * (M))), 1, \operatorname{List}.\operatorname{ofFn}\left((fun i: Fin\left(k\right) \mapsto x\left(i\right))\right)\right))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.blockTransfer` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 7, Definition 2.9: “In accordance with Definition 2.3, we also denote by T the unique extension of T to ℝ⋆ × ℝ satisfying (2.2).” EuclideanSpace coordinates are read in increasing finite-index order.

**Definition 1.8 (WordOver).**

$$\forall Y: Type, \forall X: Set\left(Y\right), \forall x: Word\left(Y\right), WordOver\left(X, x\right) = (\forall i: Fin\left(val\left(\operatorname{Word}.\operatorname{length}\left(x\right), Nat\right)\right), \operatorname{Word}.\operatorname{letter}\left(x\right)\left(i\right) \in X)$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.WordOver` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Every letter of the positive-length word belongs to the alphabet X.

**Definition 1.9 (GapRichWithExceptionalSet).**

$$\forall k: Nat, \forall X: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall S: Set\left(Real\right), GapRichWithExceptionalSet\left(X, S\right) = ((IsDiscrete\left(S\right)) \land (\forall E: Real, (\neg (E \in S)) \Rightarrow (\forall x: Word\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (WordOver\left(X, x\right)) \Rightarrow (\forall epsilon: Real, (0 < epsilon) \Rightarrow (\exists y: Word\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (WordOver\left(X, y\right)) \land ((wordDistance\left(x, y\right) < epsilon) \land (2 < \lvert \operatorname{Matrix}.\operatorname{trace}\left(extend\left(blockTransfer, y, E\right)\right) \rvert)))))))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.GapRichWithExceptionalSet` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 6, Definition 2.7: “We say that A is gap-rich with exceptional set S ⊆ ℝ if S is discrete, and, for all E ∈ ℝ∖S, x ∈ Y⋆, and ε > 0, there exist y = y(E,x,ε) ∈ Y⋆ such that” (i) d(x,y) < ε, and (ii) A(y,E) is hyperbolic. The fixed map is the polynomial block transfer; it is continuous and has determinant one. All positive perturbing word lengths are permitted.

**Definition 1.10 (GapRich).**

$$\forall k: Nat, \forall X: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), GapRich\left(X\right) = (\exists S: Set\left(Real\right), GapRichWithExceptionalSet\left(X, S\right))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.GapRich` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 6, Definition 2.7: “When the exact form of S is unimportant, we shall omit any mention of S and simply say that A is gap-rich. We say that X ⊆ Y is gap-rich for A if the restriction A|X×ℝ is gap-rich.” Page 7, Definition 2.9: “As above, we then simply say that a set X ⊆ ℝᵏ is gap-rich if T|X×ℝ is gap-rich in the sense of Definition 2.7.”

**Definition 1.11 (cartesianProduct).**

$$\forall k: Nat, \forall ell: Nat, \forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xthree: Set\left(EuclideanSpace\left(Real, Fin\left(ell\right)\right)\right), cartesianProduct\left(Xone, Xthree\right) = (\{z| \exists x: EuclideanSpace\left(Real, Fin\left(k\right)\right), (x \in Xone) \land (\exists y: EuclideanSpace\left(Real, Fin\left(ell\right)\right), (y \in Xthree) \land (z = (\operatorname{WithLp}.\operatorname{toLp}\left(2, \operatorname{Fin}.\operatorname{append}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(x\right), \operatorname{WithLp}.\operatorname{ofLp}\left(y\right)\right)\right))))\})$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.cartesianProduct` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 20, Question 2 uses “X₁ × X₃”. The product is represented in EuclideanSpace Real (Fin (k+ell)) by ordered concatenation of the first and second coordinate blocks.

**Theorem 1.12 (wordDistanceLtIff).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), \forall epsilon: Real, (wordDistance\left(x, y\right) < epsilon) \Leftrightarrow (\forall j: Nat, dist\left(periodicLetter\left(x, j\right), periodicLetter\left(y, j\right)\right) < epsilon)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordDistanceLtIff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

The finite product-period supremum is below epsilon exactly when every index of the two infinite periodic repetitions has distance below epsilon.

**Definition 1.13 (Good).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall epsilon: Real, \forall y: Word\left(Y\right), Good\left(x, epsilon, y\right) = ((val\left(\operatorname{Word}.\operatorname{length}\left(x\right), Nat\right) \mid val\left(\operatorname{Word}.\operatorname{length}\left(y\right), Nat\right)) \land (\forall i: Fin\left(val\left(\operatorname{Word}.\operatorname{length}\left(y\right), Nat\right)\right), dist\left(periodicLetter\left(x, val\left(i, Nat\right)\right), \operatorname{Word}.\operatorname{letter}\left(y\right)\left(i\right)\right) < epsilon))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.Good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

The output length is a multiple of the input length, and each output letter is within epsilon of its corresponding periodic input letter.

**Theorem 1.14 (goodSelf).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall epsilon: Real, (0 < epsilon) \Rightarrow (Good\left(x, epsilon, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodSelf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Every word has the multiple-length closeness property to itself for positive epsilon.

**Theorem 1.15 (goodDistance).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), \forall epsilon: Real, (Good\left(x, epsilon, y\right)) \Rightarrow (wordDistance\left(x, y\right) < epsilon)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Multiple-length coordinate closeness implies closeness in the periodic word distance.

**Theorem 1.16 (foldLeftStart).**

$$\forall Y: Type, \forall f: Y \to Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), \forall l: List\left(Y\right), \forall M: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), \operatorname{List}.\operatorname{foldl}\left((fun B: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right) \mapsto (fun a: Y \mapsto (f\left(a\right)) * (B))), M, l\right) = ((\operatorname{List}.\operatorname{foldl}\left((fun B: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right) \mapsto (fun a: Y \mapsto (f\left(a\right)) * (B))), 1, l\right)) * (M))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.foldLeftStart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

The left fold of left-multiplication acts on any starting matrix by right multiplication of the fold starting at the identity.

**Definition 1.17 (wordOfList).**

$$\forall Y: Type, \forall l: List\left(Y\right), \forall hl: 0 < \operatorname{List}.\operatorname{length}\left(l\right), wordOfList\left(l, hl\right) = (\langle \langle \operatorname{List}.\operatorname{length}\left(l\right), hl \rangle, (fun i: Fin\left(\operatorname{List}.\operatorname{length}\left(l\right)\right) \mapsto \operatorname{List}.\operatorname{get}\left(l, i\right)) \rangle)$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordOfList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

A list with positive length determines a Word whose positive length and indexed letters are the list length and List.get.

**Theorem 1.18 (wordOfListLetters).**

$$\forall Y: Type, \forall l: List\left(Y\right), \forall hl: 0 < \operatorname{List}.\operatorname{length}\left(l\right), \operatorname{List}.\operatorname{ofFn}\left(\operatorname{Word}.\operatorname{letter}\left(wordOfList\left(l, hl\right)\right)\right) = (l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordOfListLetters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Enumerating the letters of wordOfList recovers the original list.

**Theorem 1.19 (goodOfForallTwo).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), \forall epsilon: Real, (\operatorname{List}.\operatorname{Forall}_{2}\left((fun a: Y \mapsto (fun b: Y \mapsto dist\left(a, b\right) < epsilon)), \operatorname{List}.\operatorname{ofFn}\left(\operatorname{Word}.\operatorname{letter}\left(x\right)\right), \operatorname{List}.\operatorname{ofFn}\left(\operatorname{Word}.\operatorname{letter}\left(y\right)\right)\right)) \Rightarrow (Good\left(x, epsilon, y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodOfForallTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Pointwise List.Forall₂ closeness of the two complete coordinate lists gives equal lengths and the multiple-length closeness property.

**Theorem 1.20 (closureWordRealization).**

$$\forall Y: Type, [MetricSpace\left(Y\right)] \forall X: Set\left(Y\right), \forall A: Y \to \left(Real \to Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right)\right), \forall x: Word\left(Y\right), \forall y: Word\left(Y\right), \forall E: Real, \forall epsilon: Real, \forall C: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), (Good\left(x, epsilon, x\right)) \Rightarrow ((Good\left(x, epsilon, y\right)) \Rightarrow ((WordOver\left(X, x\right)) \Rightarrow ((WordOver\left(X, y\right)) \Rightarrow ((C \in \operatorname{Submonoid}.\operatorname{closure}\left(\left\{extend\left(A, x, E\right), extend\left(A, y, E\right)\right\}\right)) \Rightarrow ((C = (1)) \lor (\exists z: Word\left(Y\right), (WordOver\left(X, z\right)) \land ((Good\left(x, epsilon, z\right)) \land (extend\left(A, z, E\right) = (C)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.closureWordRealization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Every matrix in the submonoid generated by the two word transfers is the identity or the transfer of a word over X satisfying the same multiple-length closeness property to x. Concatenation realizes multiplication in the reversed order.

## References

- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.GapRich`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.GapRichWithExceptionalSet`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.Good`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.Word`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.WordOver`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.blockTransfer`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.cartesianProduct`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.closureWordRealization`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.concat`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.extend`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.foldLeftStart`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodDistance`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodOfForallTwo`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.goodSelf`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.periodicLetter`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.transfer`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordDistance`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordDistanceLtIff`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordOfList`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichWords.wordOfListLetters`
