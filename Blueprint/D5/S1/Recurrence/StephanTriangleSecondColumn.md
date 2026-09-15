# Stephan's A054096 Second-Column Conjecture

## Abstract

The second column of Kimberling's row-sum triangle is A006183 shifted right.

**Definition 1.1 (Finite row sum).**

$$\forall T \in \mathrm{Nat} \to \left(\mathrm{Nat} \to \mathbb{Z}\right), n \in \mathrm{Nat},\; rowSum\left(T, n\right) = \sum_{k = 0}^{n} T\left(n, k\right)$$

*Formalization.* `D5/S1/Recurrence/StephanTriangleSecondColumn.rowSum` (`✓ std3`).

*Citation.* Clark Kimberling; Ralf Stephan (2004). *OEIS A054096, T(n,2), array T as in A054090*. URL: <https://oeis.org/A054096>.

*Commentary.*

For a triangle T and a natural row index n, rowSum(T,n) is the sum of T(n,k) over all column indices k from zero through n.

**Definition 1.2 (The A054090 triangle equations).**

$$\forall T \in \mathrm{Nat} \to \left(\mathrm{Nat} \to \mathbb{Z}\right),\; IsA054090Triangle\left(T\right) \Leftrightarrow \left((\forall n \in \mathrm{Nat},\; T\left(n, 0\right) = 1) \land ((\forall n \in \mathrm{Nat},\; T\left(n + 1, 1\right) = \sum_{j = 0}^{n} T\left(n, j\right)) \land (\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; ((2 \le k) \land (k \le n)) \Rightarrow T\left(n, k\right) = T\left(n, k - 1\right) - (-1)^{k} \cdot \sum_{j = 0}^{n - k} T\left(n - k, j\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/StephanTriangleSecondColumn.IsA054090Triangle` (`✓ std3`).

*Citation.* Clark Kimberling; Ralf Stephan (2004). *OEIS A054096, T(n,2), array T as in A054090*. URL: <https://oeis.org/A054096>.

*Commentary.*

The zeroth entry of every row is one. The first entry of row n+1 is the sum of row n. For columns k from two through n, the next entry is obtained from the preceding entry by subtracting (-1)^k times the sum of row n-k.

**Definition 1.3 (The shifted A006183 recurrence).**

$$\forall B \in \mathrm{Nat} \to \mathbb{Z},\; IsShiftedA006183\left(B\right) \Leftrightarrow \left((B\left(1\right) = 1) \land ((B\left(2\right) = 2) \land (\forall j \in \mathrm{Nat},\; (3 \le j) \Rightarrow B\left(j\right) = j \cdot B\left(j - 1\right) + (3 - j) \cdot B\left(j - 2\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/StephanTriangleSecondColumn.IsShiftedA006183` (`✓ std3`).

*Citation.* Clark Kimberling; Ralf Stephan (2004). *OEIS A054096, T(n,2), array T as in A054090*. URL: <https://oeis.org/A054096>.

*Commentary.*

The offset-one sequence A006183 becomes B(1)=1 and B(2)=2 after the shift. For every j at least three, its recurrence is B(j)=j B(j-1)+(3-j) B(j-2).

**Theorem 1.4 (Row-sum invariant).**

$$\forall T \in \mathrm{Nat} \to \left(\mathrm{Nat} \to \mathbb{Z}\right), n \in \mathrm{Nat},\; (IsA054090Triangle\left(T\right)) \Rightarrow rowSum\left(T, n + 1\right) = n \cdot rowSum\left(T, n\right) + 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/StephanTriangleSecondColumn.rowSum_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Ralf Stephan (2004). *OEIS A054096, T(n,2), array T as in A054090*. URL: <https://oeis.org/A054096>.

*Commentary.*

Every triangle satisfying the A054090 equations has rowSum(T,n+1)=n rowSum(T,n)+2. A cross-row induction relates adjacent rows, and summing those relations telescopes across the row. Its standalone statement allows subsequent results about other columns and the row-sum sequence to use it directly.

**Theorem 1.5 (Stephan's second-column conjecture).**

$$\forall T \in \mathrm{Nat} \to \left(\mathrm{Nat} \to \mathbb{Z}\right), B \in \mathrm{Nat} \to \mathbb{Z},\; ((IsA054090Triangle\left(T\right)) \land (IsShiftedA006183\left(B\right))) \Rightarrow \left(\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow T\left(n, 2\right) = B\left(n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/StephanTriangleSecondColumn.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a054096-stephan-triangle-second-column` (proved) by `D5/S1/Recurrence/StephanTriangleSecondColumn.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a054096-stephan-triangle-second-column","declaration_gid":"D5/S1/Recurrence/StephanTriangleSecondColumn.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Ralf Stephan (2004). *OEIS A054096, T(n,2), array T as in A054090*. URL: <https://oeis.org/A054096>.

*Commentary.*

For every A054090 triangle T and every shifted A006183 sequence B, the second-column value T(n,2) equals B(n-1) for every n at least two. The cross-row induction yields the row-sum invariant; a telescoping step identifies T(n,2) with a difference of successive row sums, and a final induction matches that difference to the shifted recurrence.

## References

- Truth anchor: `D5/S1/Recurrence/StephanTriangleSecondColumn.IsA054090Triangle`
- Truth anchor: `D5/S1/Recurrence/StephanTriangleSecondColumn.IsShiftedA006183`
- Truth anchor: `D5/S1/Recurrence/StephanTriangleSecondColumn.result`
- Truth anchor: `D5/S1/Recurrence/StephanTriangleSecondColumn.rowSum`
- Truth anchor: `D5/S1/Recurrence/StephanTriangleSecondColumn.rowSum_succ`
