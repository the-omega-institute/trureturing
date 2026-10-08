# Counting the forms of a two-row coefficient matrix

## Abstract

The corresponding coefficient matrices of an ordered complementary two-row support are indexed by compositions of the number of columns.

**Definition 1.1 (Ordered binary basis strings).**

$$\forall n \in \mathbb{N},\; \operatorname{BasisString}\left(n\right) = \operatorname{Fin}\left(2^{n}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.BasisString` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

An n-qubit basis string is a natural number below 2 to the power n. Bit positions increase with significance, so the first qubit in the source's notation is the most significant digit. Increasing natural-number order is the binary order of the occupied basis states.

**Definition 1.2 (Support on a qubit set).**

$$\forall n \in \mathbb{N},\; \forall P \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall x \in \operatorname{BasisString}\left(n\right),\; (\operatorname{Supported}\left(P, x\right)) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(n\right),\; (\neg (i \in P)) \Rightarrow (\operatorname{testBit}\left(x.\operatorname{val}, i.\operatorname{val}\right) = \operatorname{false}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.Supported` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

A string supported on P has bit zero at every qubit outside P.

**Definition 1.3 (The complementary row and column factors).**

Lean statement: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.Config`

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.Config` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

For natural numbers n and p, Config n p consists of a nonempty finite set P of bit positions in Fin n, two strings x and y in BasisString n, and a function sigma from Fin p to BasisString n. The string x is supported on P and has bit zero at its greatest position. At every position in P the bit of y is the Boolean complement of the bit of x; outside P its bit is zero. The function sigma is strictly increasing, its strings are supported on the complement of P, and for every position outside P there is a column whose bit is zero and a column whose bit is one. Thus every row qubit changes between the rows and every column qubit changes among the columns. These are the support conditions of Eq. (120), including the absence of a fixed qubit.

**Definition 1.4 (Occupied basis strings).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall c \in \operatorname{Config}\left(n, p\right),\; \forall r \in \operatorname{Fin}\left(2\right),\; \forall j \in \operatorname{Fin}\left(p\right),\; \operatorname{occupied}\left(c, r, j\right) = (\operatorname{if} r = 0 \operatorname{then} c.\operatorname{x}.\operatorname{val} \operatorname{else} c.\operatorname{y}.\operatorname{val}) + c.\operatorname{sigma}\left(j\right).\operatorname{val}$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.occupied` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

The first row uses x and the second uses y. Adding a column string inserts its bits at disjoint positions, so the addition has no carries.

**Definition 1.5 (The coefficient-index matrix).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall c \in \operatorname{Config}\left(n, p\right),\; \forall r \in \operatorname{Fin}\left(2\right),\; \forall j \in \operatorname{Fin}\left(p\right),\; \operatorname{form}\left(c, r, j\right).\operatorname{val} = \operatorname{card}\left(\{z : \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(p\right) \mid \operatorname{occupied}\left(c, \operatorname{fst}\left(z\right), \operatorname{snd}\left(z\right)\right) < \operatorname{occupied}\left(c, r, j\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.form` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

The matrix entry is the number of occupied strings preceding that row and column. Indices begin at zero in Fin (2 p); adding one gives the subscript of b in the source. The columns remain in increasing sigma order and the first row has zero at the greatest row position.

**Definition 1.6 (Forms over all numbers of qubits).**

$$\forall p \in \mathbb{N},\; \forall f \in \operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(p\right) \to \operatorname{Fin}\left(2 \cdot p\right)\right),\; (f \in \operatorname{forms}\left(p\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; \exists c \in \operatorname{Config}\left(n, p\right),\; \operatorname{form}\left(c\right) = f)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.forms` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

A form belongs to this set exactly when some configuration on some number of qubits has that matrix of coefficient indices.

**Definition 1.7 (Forms on a fixed number of qubits).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall f \in \operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(p\right) \to \operatorname{Fin}\left(2 \cdot p\right)\right),\; (f \in \operatorname{formsAt}\left(n, p\right)) \Leftrightarrow (\exists c \in \operatorname{Config}\left(n, p\right),\; \operatorname{form}\left(c\right) = f)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formsAt` (`✓ std3`).

*Citation.* D. Li (2025). *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients*. DOI: [10.48550/arXiv.2510.16561](https://doi.org/10.48550/arXiv.2510.16561). URL: <https://arxiv.org/abs/2510.16561v1>.

*Commentary.*

Here the number of qubits is fixed, with the same conventions on row and column order.

**Definition 1.8 (The form associated with a composition).**

$$\forall p \in \mathbb{N},\; \forall d \in \operatorname{Composition}\left(p\right),\; \forall r \in \operatorname{Fin}\left(2\right),\; \forall j \in \operatorname{Fin}\left(p\right),\; \operatorname{formOf}\left(d, r, j\right).\operatorname{val} = j.\operatorname{val} + d.\operatorname{sizeUpTo}\left(d.\operatorname{index}\left(j\right).\operatorname{val} + r.\operatorname{val}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If a column lies in a part starting at s and ending at t, its first-row index is j + s and its second-row index is j + t. Reading the rows in increasing index order gives a top run and a bottom run of each part's size.

**Theorem 1.9 (Recovering the parts).**

$$\forall p \in \mathbb{N},\; \operatorname{Injective}\left(\lambda d : \operatorname{Composition}\left(p\right), \operatorname{formOf}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formOf_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting j from each top-row index recovers the start of its part. These starts together with the endpoint p recover all composition boundaries.

**Theorem 1.10 (Every form comes from a composition).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall c \in \operatorname{Config}\left(n, p\right),\; \exists d \in \operatorname{Composition}\left(p\right),\; \operatorname{form}\left(c\right) = \operatorname{formOf}\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be the greatest row position. Group the columns by their bits above q. The groups occur consecutively, since the columns are increasing. Within a group every first-row string precedes every second-row string: their highest differing bit is q. Each row separately preserves column order. The nonempty group sizes therefore give the required composition.

**Theorem 1.11 (Every composition can be realized).**

$$\forall p \in \mathbb{N},\; [hp : 1 \le p] \Rightarrow (\forall d \in \operatorname{Composition}\left(p\right),\; \forall n \in \mathbb{N},\; [hn : 2 \cdot \operatorname{clog}\left(2, p\right) + 1 \le n] \Rightarrow (\exists c \in \operatorname{Config}\left(n, p\right),\; \operatorname{form}\left(c\right) = \operatorname{formOf}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be the number of parts and a the largest part. Use ceil(log base 2 a) bits below the row bit and ceil(log base 2 k) bits above it. The upper bits encode the part index and the lower bits the position within that part. Every upper bit varies among the part indices, and every lower bit varies inside a largest part. Any extra least significant bits are assigned to the row factor, which is zero in the first row and one in the second. This preserves the order and leaves no fixed qubit. Both k and a are at most p, giving the stated uniform bound.

**Theorem 1.12 (The complete set of forms).**

$$\forall p \in \mathbb{N},\; [hp : 1 \le p] \Rightarrow (\operatorname{forms}\left(p\right) = \operatorname{range}\left(\lambda d : \operatorname{Composition}\left(p\right), \operatorname{formOf}\left(d\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.forms_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix decomposition and the construction in the other direction identify the forms with the range of the composition map.

**Theorem 1.13 (Answer to the coefficient-matrix question).**

$$\forall p \in \mathbb{N},\; [hp : 1 \le p] \Rightarrow ((\operatorname{ncard}\left(\operatorname{forms}\left(p\right)\right) = 2^{p - 1}) \land (\forall n \in \mathbb{N},\; [hn : 2 \cdot \operatorname{clog}\left(2, p\right) + 1 \le n] \Rightarrow (\operatorname{formsAt}\left(n, p\right) = \operatorname{forms}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-2025-coefficient-matrix-forms-count` (proved) by `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-2025-coefficient-matrix-forms-count","declaration_gid":"D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

There are exactly 2 to the power p minus one forms, for every positive p, and hence for every prime p in Li's question. Compositions of p are counted by choices of cuts in its p minus one gaps. Every form is already realized at each number of qubits at least twice ceil(log base 2 p) plus one. For p equal to two or three this yields the two and four forms recorded in the source. The count concerns support indices, independently of the nonzero amplitudes in the two factors.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.BasisString`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.Config`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.Supported`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.form`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formOf`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formOf_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.forms`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.formsAt`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.forms_eq_range`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.necessity`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.occupied`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.realization`
- Truth anchor: `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.result`
