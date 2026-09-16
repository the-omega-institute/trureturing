# Rotating-Memory Tail Hankel Nonsingularity

## Abstract

Every rational tail Hankel matrix of a rotating-memory Fibonacci sequence is nonsingular.

The source defines the rotating-memory Fibonacci sequence and proves its period-collapse factor for k at least two. Natural subtraction gives the source convention that negative-index summands contribute zero. Nonsingularity of the arbitrary-size tail Hankel matrix is derived here.

**Definition 1.1 (The rotating-memory sequence).**

Lean statement: `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.rotatingMemory`

*Formalization.* `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.rotatingMemory` (`✓ std3`).

*Citation.* Walid Abdelaidoum; El-Mehdi Mehiri; Hacene Belbachir (2026). *Rotating-Memory Fibonacci Numbers and Periodic Tilings*. URL: <https://arxiv.org/html/2609.12569v1>.

*Commentary.*

The values at zero and one are zero and one. For n at least two, the value is the sum of the preceding 2 plus n modulo k terms. The formal function is total in k; the cited definition assumes k at least one.

**Theorem 1.2 (One full period).**

$$\forall k \in \mathbb{N}, n \in \mathbb{N},\; 2 \le k \Rightarrow \left(k \le n \Rightarrow \operatorname{rotatingMemory}\left(k, n + k\right) = 3 \cdot 2^{k - 2} \cdot \operatorname{rotatingMemory}\left(k, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.period_collapse` (`✓ std3`). ∎

*Citation.* Walid Abdelaidoum; El-Mehdi Mehiri; Hacene Belbachir (2026). *Rotating-Memory Fibonacci Numbers and Periodic Tilings*. URL: <https://arxiv.org/html/2609.12569v1>.

*Commentary.*

For k at least two and n at least k, advancing by k multiplies the sequence by 3 times 2 to the k minus 2. This is Theorem 1 of the cited paper and supplies the factor for entries on or beyond the Hankel antidiagonal.

**Theorem 1.3 (Every tail Hankel matrix is nonsingular).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \operatorname{det}\left((\operatorname{Rat}\left(\operatorname{rotatingMemory}\left(k, k + i + j\right)\right))_{i, j \in \operatorname{Fin}\left(k\right)}\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.tail_hankel_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Walid Abdelaidoum; El-Mehdi Mehiri; Hacene Belbachir (2026). *Rotating-Memory Fibonacci Numbers and Periodic Tilings*. URL: <https://arxiv.org/html/2609.12569v1>.

*Commentary.*

For every k at least two, the k by k matrix with entry R at index k+i+j has nonzero determinant over the rationals. Each entry factors as the positive value R at k, a power of two from each index, and a threshold coefficient equal to one below the antidiagonal and three quarters on or beyond it. Subtracting consecutive threshold rows isolates every positive-index kernel coordinate; the first row then isolates coordinate zero. The source does not state this tail Hankel determinant or full-rank consequence.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.period_collapse`
- Truth anchor: `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.rotatingMemory`
- Truth anchor: `D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.tail_hankel_det_ne_zero`
