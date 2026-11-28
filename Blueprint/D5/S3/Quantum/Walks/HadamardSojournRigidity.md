# Hadamard rigidity of positive sojourn time

## Abstract

Time-eight and time-4m rigidity for every two-state unitary coin and every unit initial state in the fixed direction basis.

**Definition 1.1 (Coherent return amplitude).**

$$\forall U \in \mathit{Matrix}\left(\mathit{Fin}\left(2\right), \mathit{Fin}\left(2\right), \mathbb{C}\right),\; \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \mathit{amplitude}\left(U, n, k\right) = \sum_{w \in \mathit{returningWords}\left(n, k\right)} \mathit{wordOperator}\left(U, w\right)$$

*Formalization.* `D5/S3/Quantum/Walks/HadamardSojournRigidity.amplitude` (`✓ std3`).

*Citation.* Shunya Tamura; Tomoki Yamagami (2026). *Hadamard Rigidity of Positive Sojourn Time Distributions for Rotation Coins*. DOI: [10.48550/arXiv.2609.05033](https://doi.org/10.48550/arXiv.2609.05033). URL: <https://arxiv.org/abs/2609.05033v1>.

*Commentary.*

The direction labels zero and one select the left and right rows of the coin. Generate each word of length n once. Keep the words whose displacement is zero and whose positive interval count is k. An interval contributes if its start is positive or its start is zero and the next step is right. Multiply the projected coins with later steps on the left and add the matrices over the retained words. The empty word has the identity matrix. These are the conventions in Section 2, printed pages 3 and 4.

**Definition 1.2 (Unnormalized weight).**

$$\forall U \in \mathit{Matrix}\left(\mathit{Fin}\left(2\right), \mathit{Fin}\left(2\right), \mathbb{C}\right),\; \forall phi \in \mathit{Fin}\left(2\right) \to \mathbb{C},\; \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \mathit{weight}\left(U, \mathit{phi}, n, k\right) = \Vert \mathit{amplitude}\left(U, n, k\right) \mathit{phi} \Vert^{2}$$

*Formalization.* `D5/S3/Quantum/Walks/HadamardSojournRigidity.weight` (`✓ std3`).

*Citation.* Shunya Tamura; Tomoki Yamagami (2026). *Hadamard Rigidity of Positive Sojourn Time Distributions for Rotation Coins*. DOI: [10.48550/arXiv.2609.05033](https://doi.org/10.48550/arXiv.2609.05033). URL: <https://arxiv.org/abs/2609.05033v1>.

*Commentary.*

Apply the coherent return amplitude to the initial coin vector and sum the squared moduli of its two output coordinates. This is the weight defined in Section 2, printed page 4.

**Definition 1.3 (Exact conditional uniformity).**

$$\forall U \in \mathit{Matrix}\left(\mathit{Fin}\left(2\right), \mathit{Fin}\left(2\right), \mathbb{C}\right),\; \forall phi \in \mathit{Fin}\left(2\right) \to \mathbb{C},\; \forall m \in \mathbb{N},\; \mathit{exactUniform}\left(U, \mathit{phi}, m\right) \Leftrightarrow \operatorname{\mathit{let}} T = \sum_{0 \leq j \leq 4 \cdot m} \mathit{weight}\left(U, \mathit{phi}, 4 \cdot m, j\right) \operatorname{\mathit{in}} 0 < T \land \left(\forall k \in \mathbb{N},\; \frac{\mathit{weight}\left(U, \mathit{phi}, 4 \cdot m, k\right)}{T} = \operatorname{\mathit{if}} 0 < k \land \left(k < 4 \cdot m \land \mathit{Even}\left(k\right)\right) \operatorname{\mathit{then}} \frac{1}{2 \cdot m - 1} \operatorname{\mathit{else}} 0\right)$$

*Formalization.* `D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform` (`✓ std3`).

*Citation.* Shunya Tamura; Tomoki Yamagami (2026). *Hadamard Rigidity of Positive Sojourn Time Distributions for Rotation Coins*. DOI: [10.48550/arXiv.2609.05033](https://doi.org/10.48550/arXiv.2609.05033). URL: <https://arxiv.org/abs/2609.05033v1>.

*Commentary.*

The denominator T sums the weights at time 4m over the counts zero through 4m. Exact uniformity requires T to be positive. For positive m it assigns mass 1/(2m−1) to each even count strictly between zero and 4m and zero to every other natural count. The subtraction in the denominator is in the real numbers. Definition 3.1 gives the support and the common mass for positive m.

**Theorem 1.4 (The time-eight test and uniformity at every positive multiple of four).**

$$\forall U \in \mathit{Matrix}\left(\mathit{Fin}\left(2\right), \mathit{Fin}\left(2\right), \mathbb{C}\right),\; \forall phi \in \mathit{Fin}\left(2\right) \to \mathbb{C},\; \left(U^{H} \cdot U = 1 \land \sum_{i \in \mathit{Fin}\left(2\right)} \lvert \mathit{phi}\left(i\right) \rvert^{2} = 1\right) \Rightarrow \left(\left(\mathit{exactUniform}\left(U, \mathit{phi}, 2\right) \Leftrightarrow \left(\forall i \in \mathit{Fin}\left(2\right),\; \forall j \in \mathit{Fin}\left(2\right),\; \lvert U\left(i, j\right) \rvert = \frac{1}{\sqrt{2}}\right)\right) \land \left(\left(\forall i \in \mathit{Fin}\left(2\right),\; \forall j \in \mathit{Fin}\left(2\right),\; \lvert U\left(i, j\right) \rvert = \frac{1}{\sqrt{2}}\right) \Leftrightarrow \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \mathit{exactUniform}\left(U, \mathit{phi}, m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shunya Tamura; Tomoki Yamagami (2026). *Hadamard Rigidity of Positive Sojourn Time Distributions for Rotation Coins*. DOI: [10.48550/arXiv.2609.05033](https://doi.org/10.48550/arXiv.2609.05033). URL: <https://arxiv.org/abs/2609.05033v1>.

*Commentary.*

Here H denotes conjugate transpose and 1 is the identity matrix in the unitarity equation. In the fixed direction basis, U factors as D R E with diagonal unitaries D and E and R having rows (c,s) and (s,−c), where c and s are nonnegative. A return word takes equally many left and right steps. Its projected product therefore has a common phase depending only on its length and transforms by multiplication by the adjoint of E on the left and by E on the right. The conditional law for U on the initial vector equals the law for R on that vector multiplied by E. For R, the sum of the Gram matrices at counts two and six minus twice the Gram matrix at count four is 2c⁴s⁶(c²−s²)²(c²+s²) times the identity. The weight at count four must be positive, which excludes either parameter being zero. Equality of the three weights then forces c = s. For the balanced coin, the path recurrence has a solution in formal series whose coefficients are polynomials in the sojourn marker. On each half-line the solution is a power of a two-by-two transfer matrix. The transfer matrices satisfy the first-return recurrence with the Catalan series. The equation at the origin determines the return series. Rescaling time by the imaginary unit and adding gives the even-in-semilength projection. At time 4m the resulting sojourn polynomial is the sum of the powers with exponents 2,4,…,4m−2 times the matrix with rows (1,1) and (−1,1), scaled by (−1)ᵐ Cat(m−1)/4ᵐ. Konno's Hadamard return series gives the same coefficients. The matrix has Gram matrix 2I. Thus each unit initial state gives 2m−1 equal, positive weights and no others. The all-time condition includes time eight.

## References

- Truth anchor: `D5/S3/Quantum/Walks/HadamardSojournRigidity.amplitude`
- Truth anchor: `D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform`
- Truth anchor: `D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform_rigidity`
- Truth anchor: `D5/S3/Quantum/Walks/HadamardSojournRigidity.weight`
