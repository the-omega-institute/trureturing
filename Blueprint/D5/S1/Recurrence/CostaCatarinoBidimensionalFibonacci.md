# Costa–Catarino Bidimensional Fibonacci Matrices

## Abstract

Bidimensional Fibonacci matrices have nonzero determinant at every pair of natural indices.

**Definition 1.1 (The two-coordinate Fibonacci sequence).**

$$\forall f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \operatorname{IsSourceSequence}\left(f\right) \Leftrightarrow ((\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; 2 \le m \Rightarrow f\left(m, n\right) = f\left(m - 1, n\right) + f\left(m - 2, n\right)) \land \left((\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; 2 \le n \Rightarrow f\left(m, n\right) = f\left(m, n - 1\right) + f\left(m, n - 2\right)) \land \left(f\left(0, 0\right) = 0 \land \left(f\left(1, 0\right) = 1 \land \left(f\left(0, 1\right) = \operatorname{Complex}.\operatorname{I} \land f\left(1, 1\right) = 1 + \operatorname{Complex}.\operatorname{I}\right)\right)\right)\right))$$

*Formalization.* `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.IsSourceSequence` (`✓ std3`).

*Citation.* Eudes Antonio Costa; Paula M.M.C. Catarino (2026). *On Matrices with Bidimensional Fibonacci Numbers*. DOI: [10.2478/amsil-2025-0014](https://doi.org/10.2478/amsil-2025-0014). URL: <https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885>.

*Commentary.*

Definition 2.1, p. 63: “For integers $m \ge 0$ and $n \ge 0$, the bidimensional Fibonacci numbers $\{f_{(m,n)}\}_{m,n \ge 0}$ are defined recursively by” (2.1) and (2.2), “with initial terms $f_{(0,0)} = 0$, $f_{(1,0)} = 1$, $f_{(0,1)} = i$, $f_{(1,1)} = 1 + i$, where $i$ is the imaginary unit and $i^{2} = -1$.” The two guarded equalities below state those recurrences on natural indices, with values in the complex numbers.

**Definition 1.2 (The Fibonacci closed form).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{sourceClosedForm}\left(m, n\right) = (\operatorname{Nat}.\operatorname{fib}\left(m\right): \mathbb{C}) \cdot (\operatorname{Nat}.\operatorname{fib}\left(n + 1\right): \mathbb{C}) + \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{Nat}.\operatorname{fib}\left(m + 1\right): \mathbb{C}) \cdot (\operatorname{Nat}.\operatorname{fib}\left(n\right): \mathbb{C})$$

*Formalization.* `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.sourceClosedForm` (`✓ std3`).

*Citation.* Eudes Antonio Costa; Paula M.M.C. Catarino (2026). *On Matrices with Bidimensional Fibonacci Numbers*. DOI: [10.2478/amsil-2025-0014](https://doi.org/10.2478/amsil-2025-0014). URL: <https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885>.

*Commentary.*

Lemma 2.5, p. 64: “For non-negative integers $n$ and $m$, the bidimensional Fibonacci numbers are described as follows:” $f_{(m,n)} = f_{m} \cdot f_{n + 1} + i \cdot f_{m + 1} \cdot f_{n}$, equation (2.6). Here Nat.fib is the ordinary Fibonacci sequence with initial terms zero and one; each occurrence is cast to ℂ.

**Definition 1.3 (The order-two matrix).**

$$\forall f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{sourceMatrix}\left(f, m, n\right) = !![f\left(m + 2, n + 2\right), -f\left(m + 1, n + 1\right); f\left(m + 1, n + 1\right), -f\left(m, n\right)]$$

*Formalization.* `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.sourceMatrix` (`✓ std3`).

*Citation.* Eudes Antonio Costa; Paula M.M.C. Catarino (2026). *On Matrices with Bidimensional Fibonacci Numbers*. DOI: [10.2478/amsil-2025-0014](https://doi.org/10.2478/amsil-2025-0014). URL: <https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885>.

*Commentary.*

Definition 3.1, p. 67: “For all non-negative integers $m$ and $n$, the bidimensional Fibonacci matrices $\{\mathcal{F}_{(m,n)}\}_{m,n \ge 0}$ are given by” (3.1), “where $\{f_{(m,n)}\}_{m,n \ge 0}$ is the bidimensional Fibonacci sequence.” The matrix below retains both negative entries and uses Matrix (Fin 2) (Fin 2) ℂ.

**Definition 1.4 (The nonsingularity conjecture).**

$$claim \Leftrightarrow ((\exists f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \operatorname{IsSourceSequence}\left(f\right)) \land (\forall f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \operatorname{IsSourceSequence}\left(f\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Matrix}.\operatorname{det}\left(\operatorname{sourceMatrix}\left(f, m, n\right)\right) \ne 0\right)))$$

*Formalization.* `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.claim` (`✓ std3`).

*Citation.* Eudes Antonio Costa; Paula M.M.C. Catarino (2026). *On Matrices with Bidimensional Fibonacci Numbers*. DOI: [10.2478/amsil-2025-0014](https://doi.org/10.2478/amsil-2025-0014). URL: <https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885>.

*Commentary.*

Unnumbered Conjecture, §4, p. 73: “Let $\{\mathcal{F}_{(m,n)}\}_{m,n \ge 0}$ be the sequence of bidimensional Fibonacci matrices of order 2. For all non-negative integers $m$ and $n$, the determinant is non-vanishing, that is, the determinant satisfies:” $|\mathcal{F}_{(m,n)}| \ne 0$. The bars denote determinant. The proposition below also asserts existence of the recursively specified sequence; its universal statement includes both axes and the diagonal.

**Theorem 1.5 (All bidimensional Fibonacci matrices are nonsingular).**

$$(\exists f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \operatorname{IsSourceSequence}\left(f\right)) \land (\forall f \in (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{C}\right)),\; \operatorname{IsSourceSequence}\left(f\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Matrix}.\operatorname{det}\left(\operatorname{sourceMatrix}\left(f, m, n\right)\right) \ne 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eudes Antonio Costa; Paula M.M.C. Catarino (2026). *On Matrices with Bidimensional Fibonacci Numbers*. DOI: [10.2478/amsil-2025-0014](https://doi.org/10.2478/amsil-2025-0014). URL: <https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885>.

*Commentary.*

The closed form satisfies the two recurrences and four corner values, which determine the sequence uniquely. Cassini's identity expresses the imaginary part of the determinant as a signed sum of two positive consecutive Fibonacci products. These products strictly increase with the index. Equal signs give a nonzero sum; opposite signs cannot cancel at distinct indices, and equal indices have equal signs. Thus the imaginary part, and hence the determinant, never vanishes.

## References

- Truth anchor: `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.IsSourceSequence`
- Truth anchor: `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.claim`
- Truth anchor: `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.result`
- Truth anchor: `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.sourceClosedForm`
- Truth anchor: `D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.sourceMatrix`
- Dependency: [D5/S1/Recurrence/FibVajda](FibVajda.md)
