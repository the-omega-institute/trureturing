# The First-Column Bridge for OEIS A370380

## Abstract

A factorial convolution invariant identifies the first column of A370380.

All indices and values are natural numbers. The notation range(t) means the natural numbers strictly below t. The function a is abstract: its interpretation as connected-permutation cardinalities is assumed through a(1)=1 and Bowen's factorial convolution, not proved here.

**Definition 1.1 (The recursively defined array).**

$$\begin{aligned}A: \mathbb{N} \to \mathbb{N} \to \mathbb{N}\\\forall k: \mathbb{N}, A\left(0, k\right) = 1\\\forall n, k: \mathbb{N}, A\left(n + 1, k\right) = \left(k + 2\right) \cdot A\left(n, k + 1\right) + \sum_{j \in \operatorname{range}\left(k + 1\right)} (A\left(n, j\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.array` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A370380, a recursively defined triangular array*. URL: <https://oeis.org/A370380>.

*Commentary.*

The zeroth row is constant one. Each later entry is the shifted previous entry multiplied by k+2, plus the previous row's prefix through k.

**Theorem 1.2 (The two-variable convolution invariant).**

$$\forall n, k: \mathbb{N}, \sum_{r \in \operatorname{range}\left(n + 1\right)} ((r)! \cdot A\left(n - r, k\right)) = \left(n + 1\right) \cdot \operatorname{ascFactorial}\left(k + 2, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.factorial_convolution_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on n separates the final factorial term. Linearity turns the remaining row recurrence into a shifted convolution and a prefix of convolutions. Adjacent ascending factorials telescope that prefix.

**Theorem 1.3 (The first column is determined by Bowen data).**

$$\forall a: \mathbb{N} \to \mathbb{N}, (\operatorname{a}\left(1\right) = 1 \land \forall m: \mathbb{N}, 1 \le m \implies (m)! = \sum_{r \in \operatorname{range}\left(m\right)} ((r)! \cdot \operatorname{a}\left(m - r\right))) \implies \forall n: \mathbb{N}, A\left(n, 0\right) = \operatorname{a}\left(n + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.factorial_convolution_first_column` (`✓ std3`). ∎

*Citation.* Mikhail Kurkov (2024). *OEIS A370380, a recursively defined triangular array*. URL: <https://oeis.org/A370380>.

*Commentary.*

At k=0 the invariant equals (n+1)(n+1)!. Bowen's convolution at n+2, after separating its last term and using a(1)=1, has the same value. Strong induction cancels all terms with positive factorial index and identifies the remaining zeroth terms.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.array`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.factorial_convolution_first_column`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.factorial_convolution_invariant`
