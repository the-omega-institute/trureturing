# The gcd-three equator formula fails at dimension six

## Abstract

An exact positive-input certificate refutes the gcd-three equator formula.

**Definition 1.1 (The positive-map family).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)] \operatorname{tau}\left(n, k\right) = (let S : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) = \operatorname{Matrix}.\operatorname{of}\left((fun a b : \operatorname{Fin}\left(n\right) \mapsto if a = b + 1 then 1 else 0)\right); ((n : \mathbb{C}) - (k : \mathbb{C})) \cdot (\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{Matrix}.\operatorname{diagonalLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right), \operatorname{Matrix}.\operatorname{diagLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right)\right)) + \sum_{i \in \operatorname{Finset}.\operatorname{Icc}\left(1, k\right)} (\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{Matrix}.\operatorname{diagonalLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right), \operatorname{Matrix}.\operatorname{diagLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right)\right), \operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{LinearMap}.\operatorname{mulLeft}\left(\mathbb{C}, S^{i}\right), \operatorname{LinearMap}.\operatorname{mulRight}\left(\mathbb{C}, \operatorname{conjTranspose}\left(S^{i}\right)\right)\right)\right)) - \operatorname{LinearMap}.\operatorname{id})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.tau` (`✓ std3`).

*Citation.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Page 1, Eq. (3): “τ_{n,k}(X) = (n − k)ε(X) + Σ_{i=1}^{k} ε(Sⁱ X S^{†i}) − X”. Page 2, Eq. (4): “ε(X) = Σ_{i=0}^{n−1} Tr[X eᵢᵢ] eᵢᵢ.” In standard coordinates ε is the composition of diagonalLinearMap and diagLinearMap. Page 2, Eq. (5): “S eᵢ = eᵢ₊₁ (mod n)”. Indices are Fin n, and addition of matrix indices is modular addition. The matrix S is displayed by its entries. The composition of mulLeft and mulRight sends X to Sⁱ X (Sⁱ)ᴴ. The sum is indexed by Finset.Icc 1 k.

**Definition 1.2 (The rank-one Hadamard map).**

$$\forall n \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{hadamardMap}\left(n, v\right)\left(X\right) = \operatorname{Matrix}.\operatorname{hadamard}\left(\operatorname{Matrix}.\operatorname{vecMulVec}\left(v, \operatorname{star}\left(v\right)\right), X\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.hadamardMap` (`✓ std3`).

*Citation.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Page 2, Eq. (6): “H_{|v⟩}(X) = P_{|v⟩} ∘ X”, where “P_{|v⟩} = |v⟩⟨v|” and ∘ denotes the Hadamard product. vecMulVec v (star v) is the rank-one matrix with entries vᵢ conjugate(vⱼ). The displayed equality specifies the complex linear map on every matrix X.

**Definition 1.3 (The two Fourier vectors).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{vr}\left(n, r, j\right) = \frac{\operatorname{Complex}.\operatorname{exp}\left(\frac{2 \cdot (\operatorname{Real}.\operatorname{pi} : \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I} \cdot (r : \mathbb{C}) \cdot ((j : \mathbb{N}) : \mathbb{C})}{3}\right)}{(\operatorname{Real}.\operatorname{sqrt}\left((n : \mathbb{R})\right) : \mathbb{C})}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.vr` (`✓ std3`).

*Citation.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Page 3, Eqs. (10)–(11): “|v₁⟩ = (1/√n)(1, ω^{n/3}, (ω^{n/3})² …, (ω^{n/3})^{n−1})ᵀ” and “|v₂⟩ = (1/√n)(1, ω^{2n/3}, (ω^{2n/3})² …, (ω^{2n/3})^{n−1})ᵀ”. Here ω = e^{2πi/n}. The coordinate expression exp(2πi r j/3)/√n is used for r = 1, 2. All divisions in this expression take place in ℂ; j is first read as a natural-number coordinate.

**Definition 1.4 (The greatest positivity parameter).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)] \forall v \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \forall lam \in \mathbb{R},\; \operatorname{IsLambdaMax}\left(n, k, v, lam\right) \iff (\operatorname{IsGreatest}\left(\{l : \mathbb{R} \mid (0 \le l) \land (\operatorname{IsPositive}\left((\operatorname{tau}\left(n, k\right) - (l : \mathbb{C}) \cdot (\operatorname{hadamardMap}\left(n, v\right)))\right))\}, lam\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.IsLambdaMax` (`✓ std3`).

*Citation.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Page 2: “Let λ^max_{|v⟩} be the largest value of λ_{|v⟩}, such that the map τ_{n,k} − λ_{|v⟩} H_{|v⟩} is positive.” IsGreatest expresses attainment and maximality among nonnegative real parameters. IsPositive is FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive: every positive semidefinite input has a positive semidefinite output.

**Definition 1.5 (Conjecture 2, Eq. (13)).**

$$claim \iff (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)] (1 \le k) \Rightarrow ((k < n) \Rightarrow ((\operatorname{Nat}.\operatorname{gcd}\left(n, k\right) = 3) \Rightarrow (\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; (\left\lVert a \right\rVert^{2} + \left\lVert b \right\rVert^{2} = 1) \Rightarrow ((\left\lVert a \right\rVert = \left\lVert b \right\rVert) \Rightarrow (\operatorname{IsLambdaMax}\left(n, k, (fun j : \operatorname{Fin}\left(n\right) \mapsto a \cdot \operatorname{vr}\left(n, 1, j\right) + b \cdot \operatorname{vr}\left(n, 2, j\right)), (n : \mathbb{R}) - (k : \mathbb{R}) + \frac{(n : \mathbb{R}) - 3}{(n : \mathbb{R}) - \frac{2}{3} \cdot (k : \mathbb{R})}\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.claim` (`✓ std3`).

*Citation.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Page 3: “Conjecture 2. If GCD(n, k) = 3, then for the optimized map τ^{λ,α,β}_{n,k} = τ_{n,k} − λ_{|v⟩} H_{|v⟩} where |v⟩ = α|v₁⟩ + β|v₂⟩ one has λ^max_{|v⟩} ∈ [n − k, n − k + (n−3)/(n − ⅔k)]. Moreover, λ^max_{|v⟩} = n − k if α = 0 or β = 0, (12) λ^max_{|v⟩} = n − k + (n−3)/(n − ⅔k) if |α| = |β|. (13)” The proposition selects Eq. (13) alone. The source range k = 1, …, n − 1 is expressed by 1 ≤ k and k < n. The coefficients α and β are complex numbers a and b, with squared norms summing to one and equal norms. The vectors are j ↦ a·vr(n,1,j) + b·vr(n,2,j). The predicted parameter is a real expression; subtraction and division are in ℝ.

**Theorem 1.6 (Refutation of the equator assertion).**

$$\neg (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)] (1 \le k) \Rightarrow ((k < n) \Rightarrow ((\operatorname{Nat}.\operatorname{gcd}\left(n, k\right) = 3) \Rightarrow (\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; (\left\lVert a \right\rVert^{2} + \left\lVert b \right\rVert^{2} = 1) \Rightarrow ((\left\lVert a \right\rVert = \left\lVert b \right\rVert) \Rightarrow (\operatorname{IsLambdaMax}\left(n, k, (fun j : \operatorname{Fin}\left(n\right) \mapsto a \cdot \operatorname{vr}\left(n, 1, j\right) + b \cdot \operatorname{vr}\left(n, 2, j\right)), (n : \mathbb{R}) - (k : \mathbb{R}) + \frac{(n : \mathbb{R}) - 3}{(n : \mathbb{R}) - \frac{2}{3} \cdot (k : \mathbb{R})}\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Bera; G. Sarbicki; D. Chruściński (2023). *Optimizing positive maps in the matrix algebra M_n*. DOI: [10.48550/arXiv.2309.09621](https://doi.org/10.48550/arXiv.2309.09621). URL: <https://arxiv.org/abs/2309.09621v1>.

*Commentary.*

Take n = 6, k = 3 and a = b = 1/√2. The asserted parameter is 15/4. For q = (1,0,0,1,0,0), the matrix R = I/60 + (27/60) vecMulVec(q,star(q)) is positive semidefinite. Its quadratic forms are q* tau(6,3)(R) q = 59/30 and q* hadamardMap(6,v)(R) q = 11/18. Their difference at 15/4 is −13/40. A positive semidefinite output has a nonnegative quadratic form at q, giving a contradiction. Only coordinates 0 and 3 of v enter this calculation. The argument does not determine the exact greatest positivity parameter or settle the other parts of Conjecture 2.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.IsLambdaMax`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.hadamardMap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.tau`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.vr`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
