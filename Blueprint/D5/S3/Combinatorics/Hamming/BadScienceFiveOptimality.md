# The exact five-dimensional bad science optimum

## Abstract

The displayed five-dimensional bad science matrix maximizes the unit-row functional.

**Definition 1.1 (The bad science functional).**

$$\forall n \in \mathrm{Nat},\; \forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathrm{Real}\right),\; beta\left(A\right) = (2^{n})^{-1} \cdot \sum_{x:Fin\left(n\right) \to Bool} (\left\lVert Matrix.mulVec\left(A, fun (j: Fin\left(n\right)) \mapsto if x\left(j\right) then 1 else -1\right) \right\rVert)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.beta` (`✓ std3`).

*Citation.* Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng (2026). *On the Structure of Bad Science Matrices*. DOI: [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443). URL: <https://arxiv.org/abs/2408.00933>.

*Commentary.*

Section 1 (arXiv v2, p. 1) says: “The bad science matrix problem [4] is concerned with understanding, for matrices A ∈ ℝⁿˣⁿ whose rows are normalized to have ℓ²-length 1, the size of the quantity” and displays β(A) = 2⁻ⁿ ∑ ‖Ax‖∞ over x ∈ {−1,1}ⁿ. Here Fin n indexes coordinates, Bool indexes each sign, true gives +1, and false gives −1. The norm on Fin n → ℝ is the sup norm.

**Definition 1.2 (Unit Euclidean rows).**

$$\forall n \in \mathrm{Nat},\; \forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathrm{Real}\right),\; (UnitRows\left(A\right)) \Leftrightarrow (\forall i \in Fin\left(n\right),\; \sum_{j:Fin\left(n\right)} ((A\left(i, j\right))^{2}) = 1)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.UnitRows` (`✓ std3`).

*Citation.* Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng (2026). *On the Structure of Bad Science Matrices*. DOI: [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443). URL: <https://arxiv.org/abs/2408.00933>.

*Commentary.*

Section 1 (arXiv v2, p. 1) requires rows “normalized to have ℓ²-length 1”. For each row the sum of the squares of its real entries is one.

**Definition 1.3 (The five-dimensional matrix).**

$$Astar = HSMul.hSMul\left(\frac{1}{2 \cdot Real.sqrt\left(3\right)}, !![2,2,0,0,2; -2,2,0,2,0; -2,0,0,-2,2; 0,-Real.sqrt\left(3\right),Real.sqrt\left(3\right),Real.sqrt\left(3\right),Real.sqrt\left(3\right); 0,Real.sqrt\left(3\right),Real.sqrt\left(3\right),-Real.sqrt\left(3\right),-Real.sqrt\left(3\right)]\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.Astar` (`✓ std3`).

*Citation.* Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng (2026). *On the Structure of Bad Science Matrices*. DOI: [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443). URL: <https://arxiv.org/abs/2408.00933>.

*Commentary.*

Section 1.4 (arXiv v2, p. 3) displays this matrix, including its scalar factor 1/(2√3). The indices 0 through 4 list its rows and columns in order.

**Definition 1.4 (The optimality question).**

$$(claim) \Leftrightarrow (\forall A \in Matrix\left(Fin\left(5\right), Fin\left(5\right), \mathrm{Real}\right),\; UnitRows\left(A\right) \Rightarrow beta\left(A\right) \le beta\left(Astar\right))$$

*Formalization.* `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.claim` (`✓ std3`).

*Citation.* Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng (2026). *On the Structure of Bad Science Matrices*. DOI: [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443). URL: <https://arxiv.org/abs/2408.00933>.

*Commentary.*

Section 1.4 (arXiv v2, p. 3) asks verbatim: “We do not know whether this matrix is indeed optimal.” Optimality means that every real five-by-five matrix with unit Euclidean rows has beta at most beta Astar. All 32 Boolean functions are counted once, with uniform weight 1/32.

**Theorem 1.5 (Optimality in dimension five).**

$$\forall A \in Matrix\left(Fin\left(5\right), Fin\left(5\right), \mathrm{Real}\right),\; UnitRows\left(A\right) \Rightarrow beta\left(A\right) \le beta\left(Astar\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/albors-et-al-2024-bad-science-matrix-five` (proved) by `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"albors-et-al-2024-bad-science-matrix-five","declaration_gid":"D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng (2026). *On the Structure of Bad Science Matrices*. DOI: [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443). URL: <https://arxiv.org/abs/2408.00933>.

*Commentary.*

The maximum is (2 + 3√3)/4. For every antipodal-free subset S of the five-cube, with m vertices and vector sum u, the proof bounds the Euclidean length of u by (2√3 − 2)m + 8 − 4√3. The parity bound handles m at most five, while cube orthogonality and Cauchy–Schwarz handle m at least six. Choose one maximizing row for each vertex with coordinate zero positive, and orient its sign so its row product is nonnegative. The resulting five cells are antipodal-free and their sizes sum to 16. Summing the affine bound gives 8 + 12√3. For Astar, eight vertices have image sup norm 2 and the other 24 have image sup norm √3, attaining the bound. Uniqueness and dimensions at least six remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.Astar`
- Truth anchor: `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.UnitRows`
- Truth anchor: `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.beta`
- Truth anchor: `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.claim`
- Truth anchor: `D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.result`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../IsingUniquenessSets.md)
