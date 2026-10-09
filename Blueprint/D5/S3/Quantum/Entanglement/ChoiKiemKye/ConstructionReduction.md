# ConstructionReduction

## Abstract

Public declarations of ConstructionReduction, with complete parameters and the Lean operations.

**Definition 1.1 (phaseAt).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (j : \mathbb{N}) , \operatorname{phaseAt} a j = (if h : j - 1 < n \operatorname{then} a \langle j - 1 , h \rangle \operatorname{else} 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.phaseAt` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.2 (pEntry).**

$$\forall (d : \mathbb{N}) , \forall (z : \mathbb{N} \to \mathbb{C}) , \forall (i : \mathbb{N}) , \forall (j : \mathbb{N}) , \operatorname{pEntry} d z i j = (if i = j \operatorname{then} if d = 2 \operatorname{then} 1 \operatorname{else} 2 \operatorname{else} if j = i + 1 \operatorname{then} z j \operatorname{HDiv}.\operatorname{hDiv} z i \operatorname{else} if i = j + 1 \operatorname{then} z j \operatorname{HDiv}.\operatorname{hDiv} z i \operatorname{else} if i = 0 \land j + 1 = d \operatorname{then} z j \operatorname{else} if j = 0 \land i + 1 = d \operatorname{then} ((z i))^{- 1} \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pEntry` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.3 (P).**

$$\forall (d : \mathbb{N}) , \forall (z : \mathbb{N} \to \mathbb{C}) , P d z = (\lambda (i j : Fin d) \mapsto \operatorname{ConstructionReduction}. \operatorname{pEntry} d z \operatorname{val}\left(i\right) \operatorname{val}\left(j\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.P` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.4 (alphaUpper).**

$$\forall (k : \mathbb{N}) , \operatorname{alphaUpper} k = (\operatorname{List}. map (\lambda (j : \mathbb{N}) \mapsto (j + 1 , k - j)) (\operatorname{List}. \operatorname{range} (k \operatorname{HDiv}.\operatorname{hDiv} 2)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.alphaUpper` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.5 (betaUpper).**

$$\forall (n : \mathbb{N}) , \forall (l : \mathbb{N}) , \operatorname{betaUpper} n l = (\operatorname{List}. map (\lambda (j : \mathbb{N}) \mapsto (l + j , n - j)) (\operatorname{List}. \operatorname{range} ((n - l + 1) \operatorname{HDiv}.\operatorname{hDiv} 2)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.betaUpper` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.6 (indexList).**

$$\forall (\operatorname{upper} : \operatorname{List} (\mathbb{N} \times \mathbb{N})) , \operatorname{indexList} \operatorname{upper} = (\operatorname{upper} ++ \operatorname{List}. map \operatorname{Prod}. \operatorname{swap} \operatorname{upper}. \operatorname{reverse})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.indexList` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.7 (blockZ).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (\operatorname{upper} : \operatorname{List} (\mathbb{N} \times \mathbb{N})) , \forall (j : \mathbb{N}) , \operatorname{blockZ} a \operatorname{upper} j = (if j < \operatorname{upper}. \operatorname{length} \operatorname{then} 1 \operatorname{else} if j < (\operatorname{ConstructionReduction}. \operatorname{indexList} \operatorname{upper}) . \operatorname{length} \operatorname{then} ((\operatorname{ConstructionReduction}. \operatorname{phaseAt} a ((\operatorname{ConstructionReduction}. \operatorname{indexList} \operatorname{upper}) [j]) . 2))^{- 1} \cdot \operatorname{ConstructionReduction}. \operatorname{phaseAt} a ((\operatorname{ConstructionReduction}. \operatorname{indexList} \operatorname{upper}) [j]) . 1 \operatorname{else} 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.blockZ` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion. Optional list indexing is expanded into its defining in-bounds and out-of-bounds branches.

**Definition 1.8 (blockEntry).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (\operatorname{upper} : \operatorname{List} (\mathbb{N} \times \mathbb{N})) , \forall (\operatorname{scale} : \mathbb{C}) , \forall (row : Fin n \times Fin n) , \forall (col : Fin n \times Fin n) , \operatorname{blockEntry} a \operatorname{upper} \operatorname{scale} row col = (\operatorname{have} \operatorname{indices} := \operatorname{ConstructionReduction}. \operatorname{indexList} \operatorname{upper} ; \operatorname{have} rr := (\operatorname{val}\left(row. 1\right) + 1 , \operatorname{val}\left(row. 2\right) + 1) ; \operatorname{have} cc := (\operatorname{val}\left(col. 1\right) + 1 , \operatorname{val}\left(col. 2\right) + 1) ; if rr \in \operatorname{indices} \land cc \in \operatorname{indices} \operatorname{then} \operatorname{scale} \cdot \operatorname{ConstructionReduction}. \operatorname{pEntry} \operatorname{indices}. \operatorname{length} (\operatorname{ConstructionReduction}. \operatorname{blockZ} a \operatorname{upper}) (\operatorname{List}. \operatorname{idxOf} rr \operatorname{indices}) (\operatorname{List}. \operatorname{idxOf} cc \operatorname{indices}) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.blockEntry` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.9 (rhoGamma).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , \operatorname{rhoGamma} a b r = (\lambda (row col : Fin n \times Fin n) \mapsto (if row . 1 = row . 2 \land row = col \operatorname{then} (r : \mathbb{C}) \operatorname{else} 0) + \operatorname{blockEntry} a [(1 , 2)] 1 row col + \operatorname{blockEntry} a [(1 , 3)] 2 row col + (\sum (k : \mathbb{N}) \in \operatorname{Finset}. \operatorname{range} (n + 1) , if 4 \leq k \operatorname{then} \operatorname{blockEntry} a (\operatorname{alphaUpper} k) 1 row col \operatorname{else} 0) + (\sum (l : \mathbb{N}) \in \operatorname{Finset}. \operatorname{range} (n + 1) , if 2 \leq l \land l + 3 \leq n \operatorname{then} \operatorname{blockEntry} b (\operatorname{betaUpper} n l) 1 row col \operatorname{else} 0) + (if 3 < n \operatorname{then} \operatorname{blockEntry} b [(n - 2 , n)] 2 row col \operatorname{else} 0) + \operatorname{blockEntry} b [(n - 1 , n)] 1 row col)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.rhoGamma` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.10 (partialTranspose).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n \times Fin n) (Fin n \times Fin n) \mathbb{C}) , \operatorname{partialTranspose} A = (D5. S3. \operatorname{Quantum}. \operatorname{Entanglement}. \operatorname{StructuredNegativityCoincidenceRefutation}. \operatorname{partialTransposeB} A. \operatorname{transpose})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.partialTranspose` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion. Source, p. 1, verbatim: “The partial transpose (x ⊗ y)Γ of x ⊗ y ∈ Mₘ ⊗ Mₙ is given by xᵗ ⊗ y with the usual transpose xᵗ.” In the bound matrix carrier the entry at ((i,j),(k,l)) is A ((k,j),(i,l)); the frozen second-factor operation is applied to the ordinary transpose to obtain precisely this first-factor operation.

**Definition 1.11 (rho).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , rho a b r = (\operatorname{ConstructionReduction}. \operatorname{partialTranspose} (\operatorname{ConstructionReduction}. \operatorname{rhoGamma} a b r))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.rho` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.12 (D).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , D a b r = (\lambda (i j : Fin n) \mapsto if i = j \operatorname{then} \operatorname{val}\left(r\right) \operatorname{else} if \operatorname{val}\left(i\right) = 0 \operatorname{then} (if \operatorname{val}\left(j\right) = 2 \operatorname{then} 2 \operatorname{else} 1) \cdot (\operatorname{starRingEnd} \mathbb{C}) (a j) \operatorname{else} if \operatorname{val}\left(j\right) = 0 \operatorname{then} (if \operatorname{val}\left(i\right) = 2 \operatorname{then} 2 \operatorname{else} 1) \cdot a i \operatorname{else} if \operatorname{val}\left(j\right) + 1 = n \operatorname{then} (if \operatorname{val}\left(i\right) + 3 = n \operatorname{then} 2 \operatorname{else} 1) \cdot b i \operatorname{else} if \operatorname{val}\left(i\right) + 1 = n \operatorname{then} (if \operatorname{val}\left(j\right) + 3 = n \operatorname{then} 2 \operatorname{else} 1) \cdot (\operatorname{starRingEnd} \mathbb{C}) (b j) \operatorname{else} if \operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right) \lor \operatorname{val}\left(i\right) + 2 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 2 = \operatorname{val}\left(i\right) \operatorname{then} if \operatorname{val}\left(i\right) + \operatorname{val}\left(j\right) + 1 \leq n \operatorname{then} a i \cdot (\operatorname{starRingEnd} \mathbb{C}) (a j) \operatorname{else} b i \cdot (\operatorname{starRingEnd} \mathbb{C}) (b j) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.13 (tensor).**

$$\forall (n : \mathbb{N}) , \forall (x : Fin n \to \mathbb{C}) , \forall (y : Fin n \to \mathbb{C}) , \forall (a : Fin n \times Fin n) , \operatorname{tensor} x y a = (\operatorname{Matrix}. \operatorname{vecMulVec} x y a . 1 a . 2)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.tensor` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.14 (InRange).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n \times Fin n) (Fin n \times Fin n) \mathbb{C}) , \forall (v : Fin n \times Fin n \to \mathbb{C}) , \operatorname{InRange} A v = (v \in A. \operatorname{mulVecLin}. \operatorname{range})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.InRange` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.15 (PPT).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n \times Fin n) (Fin n \times Fin n) \mathbb{C}) , PPT A = (A. \operatorname{PosSemidef} \land (\operatorname{ConstructionReduction}. \operatorname{partialTranspose} A) . \operatorname{PosSemidef})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.PPT` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.16 (Edge).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n \times Fin n) (Fin n \times Fin n) \mathbb{C}) , \operatorname{Edge} A = (\forall (x y : Fin n \to \mathbb{C}) , x \neq 0 \to y \neq 0 \to \neg (\operatorname{ConstructionReduction}. \operatorname{InRange} A (\operatorname{ConstructionReduction}. \operatorname{tensor} x y) \land \operatorname{ConstructionReduction}. \operatorname{InRange} (\operatorname{ConstructionReduction}. \operatorname{partialTranspose} A) (\operatorname{ConstructionReduction}. \operatorname{tensor} (\lambda (i : Fin n) \mapsto (\operatorname{starRingEnd} \mathbb{C}) (x i)) y)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Edge` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion. Source, p. 1, verbatim: “There exists no nonzero product vector |ξᵢ⟩ ⊗ |ηᵢ⟩ ∈ Im ϱ such that |ξ̄ᵢ⟩ ⊗ |ηᵢ⟩ ∈ Im ϱΓ. Such states are called PPT entangled edge states [19], in short, edge states in this paper.” The predicate encodes the range exclusion; PPT and nonzeroness are separate conjuncts of Full.claim.

**Definition 1.17 (GenericPhases).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \operatorname{GenericPhases} a b = ((\forall (i : Fin n) , a i \neq 0 \land b i \neq 0) \land (\forall (i j : Fin n) , i < j \to ((a i))^{- 1} \cdot a j \neq ((b i))^{- 1} \cdot b j))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.GenericPhases` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.18 (Admissible).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \operatorname{Admissible} a b = ((\forall (i : Fin n) , \left\lVert a i \right\rVert = 1 \land \left\lVert b i \right\rVert = 1) \land \operatorname{ConstructionReduction}. \operatorname{phaseAt} a 1 = 1 \land \operatorname{ConstructionReduction}. \operatorname{phaseAt} b n = 1 \land (\forall (i j : Fin n) , i < j \to ((a i))^{- 1} \cdot a j \neq ((b i))^{- 1} \cdot b j))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Admissible` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.19 (LargestRoot).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , \operatorname{LargestRoot} a b r = ((\operatorname{ConstructionReduction}. D a b r) . det = 0 \land (\forall (s : \mathbb{R}) , (\operatorname{ConstructionReduction}. D a b s) . det = 0 \to s \leq r))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.LargestRoot` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.20 (SimpleRoot).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , \operatorname{SimpleRoot} a b r = (\exists (d : \mathbb{R}) , d \neq 0 \land \operatorname{HasDerivAt} (\lambda (s : \mathbb{R}) \mapsto (\operatorname{ConstructionReduction}. D a b s) . det. re) d r)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.SimpleRoot` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.21 (bracket).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (x : Fin n \to \mathbb{C}) , \forall (y : Fin n \to \mathbb{C}) , \forall (i : \mathbb{N}) , \forall (j : \mathbb{N}) , \operatorname{bracket} a x y i j = (\operatorname{ConstructionReduction}. \operatorname{phaseAt} x i \cdot \operatorname{ConstructionReduction}. \operatorname{phaseAt} y j - ((\operatorname{ConstructionReduction}. \operatorname{phaseAt} a i))^{- 1} \cdot \operatorname{ConstructionReduction}. \operatorname{phaseAt} a j \cdot \operatorname{ConstructionReduction}. \operatorname{phaseAt} x j \cdot \operatorname{ConstructionReduction}. \operatorname{phaseAt} y i)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.bracket` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.22 (BilinearSystem).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (x : Fin n \to \mathbb{C}) , \forall (y : Fin n \to \mathbb{C}) , \operatorname{BilinearSystem} a b x y = ((\forall k \in \operatorname{Finset}. Icc 2 n , (\sum j \in \operatorname{Finset}. \operatorname{range} (k \operatorname{HDiv}.\operatorname{hDiv} 2) , ((- 1))^{j} \cdot \operatorname{ConstructionReduction}. \operatorname{bracket} a x y (j + 1) (k - j)) = 0) \land (\forall l \in \operatorname{Finset}. Icc 1 (n - 2) , (\sum j \in \operatorname{Finset}. \operatorname{range} ((l + 1) \operatorname{HDiv}.\operatorname{hDiv} 2) , ((- 1))^{j} \cdot \operatorname{ConstructionReduction}. \operatorname{bracket} b x y (n - l + j) (n - j)) = 0))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.BilinearSystem` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.23 (AllowedSupport).**

$$\forall (n : \mathbb{N}) , \forall (\operatorname{isAlpha} : \operatorname{Bool}) , \forall (s : \operatorname{Finset} (Fin n)) , \operatorname{AllowedSupport} n \operatorname{isAlpha} s = (if \operatorname{isAlpha} = \operatorname{true} \operatorname{then} ((\forall i \in s , 2 \cdot (\operatorname{val}\left(i\right) + 1) \leq n + 1) \lor \exists (p : Fin n) (q : Fin n) , p \in s \land q \in s \land \operatorname{val}\left(p\right) + \operatorname{val}\left(q\right) + 2 \leq n + 1 \land 2 \cdot (\operatorname{val}\left(p\right) + 1) < n + 1 \land n + 1 < 2 \cdot (\operatorname{val}\left(q\right) + 1) \land (\forall i \in s , i = q \lor p \leq i \land \operatorname{val}\left(i\right) + \operatorname{val}\left(q\right) + 2 \leq n + 1)) \operatorname{else} ((\forall i \in s , n + 1 \leq 2 \cdot (\operatorname{val}\left(i\right) + 1)) \lor \exists (p : Fin n) (q : Fin n) , p \in s \land q \in s \land n + 1 < \operatorname{val}\left(p\right) + \operatorname{val}\left(q\right) + 2 \land 2 \cdot (\operatorname{val}\left(p\right) + 1) < n + 1 \land n + 1 < 2 \cdot (\operatorname{val}\left(q\right) + 1) \land (\forall i \in s , i = p \lor n + 1 < \operatorname{val}\left(i\right) + \operatorname{val}\left(p\right) + 2 \land i \leq q)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.AllowedSupport` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.24 (Classified).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (x : Fin n \to \mathbb{C}) , \forall (y : Fin n \to \mathbb{C}) , \operatorname{Classified} a b x y = (x = 0 \lor y = 0 \lor \exists (\operatorname{isAlpha} : \operatorname{Bool}) (s : \operatorname{Finset} (Fin n)) (c : Fin n \to \mathbb{C}) (t : \mathbb{C}) , t \neq 0 \land s. \operatorname{Nonempty} \land \operatorname{ConstructionReduction}. \operatorname{AllowedSupport} n \operatorname{isAlpha} s \land (\forall (i : Fin n) , c i \neq 0 \Leftrightarrow i \in s) \land (\forall (i : Fin n) , x i = c i \cdot t \land y i = c i \cdot if \operatorname{isAlpha} = \operatorname{true} \operatorname{then} a i \operatorname{else} b i))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Classified` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.25 (StarCondition).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (w : Fin n \to \mathbb{C}) , \operatorname{StarCondition} a b w = (\forall (\operatorname{isAlpha} : \operatorname{Bool}) (s : \operatorname{Finset} (Fin n)) , s. \operatorname{Nonempty} \to \operatorname{ConstructionReduction}. \operatorname{AllowedSupport} n \operatorname{isAlpha} s \to \forall (u : Fin n \to \mathbb{R}) , (\forall (i : Fin n) , 0 \leq u i) \to (\forall (i : Fin n) , u i \neq 0 \Leftrightarrow i \in s) \to (\sum i : Fin n , (\operatorname{val}\left(u i\right) \cdot if \operatorname{isAlpha} = \operatorname{true} \operatorname{then} a i \operatorname{else} b i) \cdot (\operatorname{starRingEnd} \mathbb{C}) (w i)) \neq 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.StarCondition` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.26 (proposition61_statement).**

$$\operatorname{proposition61}_{\operatorname{statement}} = (\forall (n : \mathbb{N}) , 3 \leq n \to \forall (a b : Fin n \to \mathbb{C}) (r : \mathbb{R}) (w : Fin n \to \mathbb{C}) , \operatorname{ConstructionReduction}. \operatorname{Admissible} a b \to 1 < r \to \operatorname{ConstructionReduction}. \operatorname{LargestRoot} a b r \to \operatorname{ConstructionReduction}. \operatorname{SimpleRoot} a b r \to w \neq 0 \to (\operatorname{ConstructionReduction}. D a b r) . \operatorname{mulVec} w = 0 \to \operatorname{ConstructionReduction}. \operatorname{StarCondition} a b w \to \operatorname{ConstructionReduction}. PPT (\operatorname{ConstructionReduction}. rho a b r) \land \operatorname{ConstructionReduction}. \operatorname{Edge} (\operatorname{ConstructionReduction}. rho a b r) \land (\operatorname{ConstructionReduction}. rho a b r) . \operatorname{rank} = n \cdot n - 1 \land (\operatorname{ConstructionReduction}. \operatorname{rhoGamma} a b r) . \operatorname{rank} = n \cdot n - 2 \cdot n + 3)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.proposition61_statement` (`✓ std3`).

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.27 (Partition.lo).**

$$\forall (n : \mathbb{N}) , \forall (t : \mathbb{N}) , \operatorname{Partition}. lo n t = (if t + 2 \leq n \operatorname{then} 1 \operatorname{else} t + 3 - n)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.lo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Definition 1.28 (Partition.hi).**

$$\forall (n : \mathbb{N}) , \forall (t : \mathbb{N}) , \operatorname{Partition}. hi n t = (if t + 2 \leq n \operatorname{then} t + 2 \operatorname{else} n)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.hi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.29 (Draft.triangular_pivot).**

$$\forall (u : \mathbb{N} \to \mathbb{C}) , \forall (v : \mathbb{N} \to \mathbb{C}) , \forall (\operatorname{weight} : \mathbb{N} \to \mathbb{N} \to \mathbb{C}) , \forall (N : \mathbb{N}) , \forall (p : \mathbb{N}) , (1 \leq p) \to ((u p \neq 0 \lor v p \neq 0) \to ((\forall (i : \mathbb{N}) , 1 \leq i \to i < p \to u i = 0 \land v i = 0) \to ((\forall (k i : \mathbb{N}) , 2 \leq k \to k \leq N \to i < k \operatorname{HDiv}.\operatorname{hDiv} 2 \to \operatorname{weight} k i \neq 0) \to ((\forall (k : \mathbb{N}) , 2 \leq k \to k \leq N \to (\sum j \in \operatorname{Finset}. \operatorname{range} (k \operatorname{HDiv}.\operatorname{hDiv} 2) , \operatorname{weight} k j \cdot (u (j + 1) \cdot v (k - j) - u (k - j) \cdot v (j + 1))) = 0) \to (\forall (q : \mathbb{N}) , (p < q) \to ((p + q \leq N + 1) \to ((u p \cdot v q - u q \cdot v p) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.triangular_pivot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion. The private scalar wedge is displayed by its literal defining expression.

**Definition 1.30 (Spectral.pencil).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , \forall (s : \mathbb{R}) , \operatorname{Spectral}. \operatorname{pencil} A s = (\operatorname{val}\left(s\right) \cdot 1 - A)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.31 (Spectral.det_pencil).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \forall (s : \mathbb{R}) , (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det = \prod i : \iota , \operatorname{val}\left(s - hA. \operatorname{eigenvalues} i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.det_pencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.32 (Spectral.pencil_conjugate).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \forall (s : \mathbb{R}) , \operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s = ((\operatorname{Unitary}. \operatorname{conjStarAlgAut} \mathbb{C} (\operatorname{Matrix} \iota \iota \mathbb{C})) hA. \operatorname{eigenvectorUnitary}) (\operatorname{Matrix}. \operatorname{diagonal} \lambda (i : \iota) \mapsto \operatorname{val}\left(s - hA. \operatorname{eigenvalues} i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pencil_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.33 (Spectral.largest_root_psd).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , (A. \operatorname{IsHermitian}) \to (\forall (r : \mathbb{R}) , (\forall (s : \mathbb{R}) , (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det = 0 \to s \leq r) \to ((\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A r) . \operatorname{PosSemidef}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.largest_root_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.34 (Spectral.det_pencil_re).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \forall (s : \mathbb{R}) , (\operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} A s) . det. re = \prod i : \iota , (s - hA. \operatorname{eigenvalues} i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.det_pencil_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.35 (D_hermitian).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , (\operatorname{ConstructionReduction}. D a b r) . \operatorname{IsHermitian})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.36 (D_pencil).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , \operatorname{ConstructionReduction}. D a b r = \operatorname{ConstructionReduction}. \operatorname{Spectral}. \operatorname{pencil} (- \operatorname{ConstructionReduction}. D a b 0) r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D_pencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.37 (partialTranspose_involutive).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n \times Fin n) (Fin n \times Fin n) \mathbb{C}) , \operatorname{ConstructionReduction}. \operatorname{partialTranspose} (\operatorname{ConstructionReduction}. \operatorname{partialTranspose} A) = A$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.partialTranspose_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.38 (Path.scaled_dominance_posDef).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall [\operatorname{DecidableEq} \iota] , \forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}) , (A. \operatorname{IsHermitian}) \to (\forall (g : \iota \to \mathbb{C}) , (\forall (i : \iota) , g i \neq 0) \to ((\forall (i : \iota) , (\sum j \in \operatorname{Finset}. \operatorname{univ}. \operatorname{erase} i , \left\lVert ((g i))^{- 1} \cdot A i j \cdot g j \right\rVert) < (A i i) . re) \to (A. \operatorname{PosDef})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.scaled_dominance_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.39 (Path.sum_indicator_le).**

$$\forall (\iota : \operatorname{Type}*) , \forall [\operatorname{Fintype} \iota] , \forall (P : \iota \to \operatorname{Prop}) , \forall [\operatorname{DecidablePred} P] , (\forall (i j : \iota) , P i \to P j \to i = j) \to (\forall (c : \mathbb{R}) , (0 \leq c) \to (((\sum i : \iota , if P i \operatorname{then} c \operatorname{else} 0)) \leq c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.sum_indicator_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.40 (proposition61).**

$$\forall (n : \mathbb{N}) , 3 \leq n \to \forall (a b : Fin n \to \mathbb{C}) (r : \mathbb{R}) (w : Fin n \to \mathbb{C}) , \operatorname{ConstructionReduction}. \operatorname{Admissible} a b \to 1 < r \to \operatorname{ConstructionReduction}. \operatorname{LargestRoot} a b r \to \operatorname{ConstructionReduction}. \operatorname{SimpleRoot} a b r \to w \neq 0 \to (\operatorname{ConstructionReduction}. D a b r) . \operatorname{mulVec} w = 0 \to \operatorname{ConstructionReduction}. \operatorname{StarCondition} a b w \to \operatorname{ConstructionReduction}. PPT (\operatorname{ConstructionReduction}. rho a b r) \land \operatorname{ConstructionReduction}. \operatorname{Edge} (\operatorname{ConstructionReduction}. rho a b r) \land (\operatorname{ConstructionReduction}. rho a b r) . \operatorname{rank} = n \cdot n - 1 \land (\operatorname{ConstructionReduction}. \operatorname{rhoGamma} a b r) . \operatorname{rank} = n \cdot n - 2 \cdot n + 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.proposition61` (`✓ std3`). ∎

*Citation.* J. Choi, Y.-H. Kiem, and S.-H. Kye (2020). *Entangled edge states of corank one with positive partial transposes*. DOI: [10.1063/1.5122836](https://doi.org/10.1063/1.5122836). URL: <https://arxiv.org/abs/1903.10745v2>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Admissible`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.AllowedSupport`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.BilinearSystem`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Classified`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.D_pencil`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.Edge`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.GenericPhases`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.InRange`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.LargestRoot`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.P`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.PPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.SimpleRoot`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.StarCondition`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.alphaUpper`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.betaUpper`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.blockEntry`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.blockZ`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.bracket`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.det_pencil`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.det_pencil_re`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.hi`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.indexList`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.largest_root_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.lo`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pEntry`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.partialTranspose_involutive`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pencil`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.pencil_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.phaseAt`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.proposition61`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.proposition61_statement`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.rho`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.rhoGamma`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.scaled_dominance_posDef`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.sum_indicator_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.tensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.triangular_pivot`
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../StructuredNegativityCoincidenceRefutation.md)
