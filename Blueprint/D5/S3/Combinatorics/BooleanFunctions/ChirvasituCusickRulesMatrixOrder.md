# A trace obstruction to the rules-matrix order conjecture

## Abstract

A zero trace of the twenty-fourth power contradicts the proposed order at (8,4).

**Definition 1.1 (The first Hadamard block).**

$$\operatorname{H0} = \begin{pmatrix}1&1\\1&-1\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.H0` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Section 6, page 18, defines H0 := [[1, 1], [1, −1]]. Entries are integers.

**Definition 1.2 (The second Hadamard block).**

$$\operatorname{H1} = \begin{pmatrix}1&1\\-1&1\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.H1` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Section 6, page 18, defines H1 := [[1, 1], [−1, 1]]. Entries are integers.

**Definition 1.3 (Column padding).**

$$\forall r \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(c\right), \mathbb{Z}\right),\; \operatorname{pad}\left(k, M\right) = (\operatorname{fun} a: \operatorname{Fin}\left(r\right) \mapsto \operatorname{fun} b: \operatorname{Fin}\left(c \cdot (k + 1)\right) \mapsto \operatorname{if} \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(b\right), k + 1\right) = 0 \operatorname{then} M\left(a, \operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(b\right), k + 1\right)\right)\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.pad` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Section 6, page 19: “by πₖ(M) (or πₖM) the matrix obtained by appending k all-0 columns after each column of M (‘π’ is meant to stand for ‘pad’);” Indices start at zero. Nat.div is natural-number division; Fin.mk displays the index value, with its bound proof suppressed.

**Definition 1.4 (Simultaneous row rotation).**

$$\forall r \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; [\operatorname{NeZero}\left(n\right)] \forall k \in \mathrm{Nat},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right),\; \operatorname{rot}\left(k, M\right) = (\operatorname{fun} a: \operatorname{Fin}\left(r\right) \mapsto \operatorname{fun} b: \operatorname{Fin}\left(n\right) \mapsto M\left(a, \operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(b\right) + n - \operatorname{Nat}.\operatorname{mod}\left(k, n\right), n\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.rot` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Section 6, page 19: “and by ρₖ(M) (or ρₖM) the matrix obtained by rotation all rows of M simultaneously rightward k times.” The formula uses natural subtraction and reduction modulo n; Fin.mk suppresses its bound proof.

**Definition 1.5 (The alternating Hadamard block choice).**

$$\forall j \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{blockH}\left(j, k\right) = \operatorname{if} \operatorname{Nat}.\operatorname{mod}\left(\operatorname{Nat}.\operatorname{div}\left(k, 2^{j - 1}\right), 2\right) = 0 \operatorname{then} \operatorname{H0} \operatorname{else} \operatorname{H1}$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.blockH` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Section 6, page 19: “Specifically, the rows in (6-2) alternate in whether or not an H₁ is substituted in batches of 2ʲ⁻¹:” Block k uses H0 first, followed by H1 after each batch. Nat.div is natural-number division and j − 1 is natural subtraction.

**Definition 1.6 (The binomial rules matrix).**

$$\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{R}\left(i, j\right) = (\operatorname{fun} a: \operatorname{Fin}\left(2^{i - 1} \cdot (2)\right) \mapsto \operatorname{fun} b: \operatorname{Fin}\left(2 \cdot (2^{i - 1})\right) \mapsto \operatorname{let} p=\operatorname{finProdFinEquiv}.\operatorname{symm}\left(a\right); \operatorname{rot}\left(\operatorname{val}\left((p).1\right), \operatorname{pad}\left(2^{i - 1} - 1, \operatorname{blockH}\left(j, \operatorname{val}\left((p).1\right)\right)\right)\right)\left((p).2, \operatorname{Fin}.\operatorname{cast}\left(b\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.R` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Equation (6-3), page 19, stacks the rotated padded blocks in increasing block index. The same page states: “Again, this is a 2ⁱ × 2ⁱ matrix.” The dimension 2ⁱ applies for 1 ≤ i, including the source range i > j ≥ 1. The inverse finProdFinEquiv assigns row a to block p.1 and row p.2; its forward map sends (k,c) to c + 2k. Fin.cast changes the column bound using 2^(i−1) − 1 + 1 = 2^(i−1); proof arguments are suppressed.

**Definition 1.7 (The real square rules matrix).**

$$\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{Rsq}\left(i, j\right) = \operatorname{Matrix}.\operatorname{map}\left(\operatorname{Matrix}.\operatorname{submatrix}\left(\operatorname{R}\left(i, j\right), \operatorname{Fin}.\operatorname{cast}, \operatorname{id}\right), (\operatorname{Int}.\operatorname{cast}): \mathbb{Z} \to \mathrm{Real}\right)$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.Rsq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Rsq reindexes the rows of R to its column type using commutativity of natural multiplication, then maps every integer entry to the real numbers. Fin.cast suppresses the equality proof.

**Definition 1.8 (Chirvasitu–Cusick Conjecture 6.1).**

$$\operatorname{claim} = (\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; (1 \le j) \Rightarrow ((j < i) \Rightarrow ((\forall mu \in \mathrm{Complex},\; (mu \in \operatorname{spectrum}\left(\mathrm{Complex}, \operatorname{Matrix}.\operatorname{map}\left(\operatorname{Rsq}\left(i, j\right), \operatorname{Complex}.\operatorname{ofReal}\right)\right)) \Rightarrow (\exists n \in \mathrm{Nat},\; (0 < n) \land (\frac{mu}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(2\right)\right)}^{n} = 1))) \land (\operatorname{orderOf}\left((\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Real}.\operatorname{sqrt}\left(2\right)\right), \operatorname{Rsq}\left(i, j\right)\right))\right) = 2 \cdot (\operatorname{Nat}.\operatorname{lcm}\left(4, \operatorname{Nat}.\operatorname{lcm}\left(i - j, i + j\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.claim` (`✓ std3`).

*Citation.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

Conjecture 6.1, page 19: “For i > j ≥ 1 the eigenvalues of the matrix R(i, j) of (6-3) are all √2-scaled roots of unity. Moreover, the multiplicative order of R(i,j)/√2 is precisely 2 · lcm(4, i − j, i + j).” Both conjuncts range over natural i and j with 1 ≤ j < i. The first uses the complex spectrum; the second uses orderOf in the monoid of real square matrices. The square root in the first conjunct is cast from Real to Complex.

**Theorem 1.9 (Refutation at (8,4)).**

$$\neg (\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; (1 \le j) \Rightarrow ((j < i) \Rightarrow ((\forall mu \in \mathrm{Complex},\; (mu \in \operatorname{spectrum}\left(\mathrm{Complex}, \operatorname{Matrix}.\operatorname{map}\left(\operatorname{Rsq}\left(i, j\right), \operatorname{Complex}.\operatorname{ofReal}\right)\right)) \Rightarrow (\exists n \in \mathrm{Nat},\; (0 < n) \land (\frac{mu}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(2\right)\right)}^{n} = 1))) \land (\operatorname{orderOf}\left((\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Real}.\operatorname{sqrt}\left(2\right)\right), \operatorname{Rsq}\left(i, j\right)\right))\right) = 2 \cdot (\operatorname{Nat}.\operatorname{lcm}\left(4, \operatorname{Nat}.\operatorname{lcm}\left(i - j, i + j\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/chirvasitu-cusick-2024-rules-matrix-order-conjecture-6-1` (refuted) by `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chirvasitu-cusick-2024-rules-matrix-order-conjecture-6-1","declaration_gid":"D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Chirvasitu; T. W. Cusick (2024). *Quadratic rotation symmetric Boolean functions*. DOI: [10.1016/j.dam.2023.10.010](https://doi.org/10.1016/j.dam.2023.10.010). URL: <https://arxiv.org/abs/2304.12734v1>.

*Commentary.*

For i = 8 and j = 4 the asserted order is 24. The reindexed integer matrix R(8,4) has zero trace after its twenty-fourth power: a signed Pauli transport ends with the opposite sign. Order 24 would instead force that power to equal 4096 times the identity, whose trace is 1048576. This disproves the conjunction. The exact order 48, a corrected universal order formula and the universal eigenvalue assertion are not proved here.

## References

- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.H0`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.H1`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.R`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.Rsq`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.blockH`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.claim`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.pad`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result`
- Truth anchor: `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.rot`
