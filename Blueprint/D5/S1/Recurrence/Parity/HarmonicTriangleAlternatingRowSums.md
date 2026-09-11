# Alternating Fibonacci Harmonic Row Sums

## Abstract

Schulte's alternating row sums of the Fibonacci harmonic triangle have the conjectured closed form.

All indices are natural numbers. F denotes Nat.fib, with F(0)=0 and F(1)=1. Index and exponent subtraction is natural subtraction. The denominator is natural-valued, the row sums and their differences are rational, and the two-step Cassini identity is an integer identity. Fibonacci values in rational or integer arithmetic are coerced into that field or ring.

**Definition 1.1 (The moving diagonal denominator).**

$$\forall n, k: \mathbb{N}, \mathrm{denominator}\left(n, k\right) = \mathrm{if} (k = n) \mathrm{then} (\mathrm{F}\left(n\right) \cdot \mathrm{F}\left(n + 1\right)) \mathrm{else} (\mathrm{F}\left(k\right) \cdot \mathrm{F}\left(k + 2\right))$$

*Formalization.* `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the triangle, the diagonal denominator is F(n)F(n+1); each earlier entry has denominator F(k)F(k+2). The Lean definition extends this piecewise expression to all natural n and k.

**Definition 1.2 (The alternating row sum).**

$$\forall n: \mathbb{N}, \mathrm{altRowSum}\left(n\right) = \sum_{k \in \mathrm{Icc}\left(1, n\right)} (\frac{(-1)^{k - 1}}{\mathrm{denominator}\left(n, k\right)})$$

*Formalization.* `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.altRowSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum runs from k=1 through k=n, with a positive first term and numerator one before applying the alternating sign.

**Lemma 1.3 (The row difference).**

$$\forall n: \mathbb{N}, 2 \le n \implies \mathrm{altRowSum}\left(n + 1\right) - \mathrm{altRowSum}\left(n\right) = \frac{2 \cdot (-1)^{n}}{\mathrm{F}\left(n + 1\right) \cdot \mathrm{F}\left(n + 2\right)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.altRowSum_succ_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split each row into its unchanged prefix and diagonal. In the next row the old diagonal acquires denominator F(n)F(n+2), and a new diagonal appears. The Fibonacci recurrence simplifies their combined change.

**Lemma 1.4 (The two-step product identity).**

$$\forall n: \mathbb{N}, \mathrm{F}\left(n + 1\right) \cdot \mathrm{F}\left(n + 3\right) - \mathrm{F}\left(n\right) \cdot \mathrm{F}\left(n + 4\right) = 2 \cdot (-1)^{n + 2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.fib_cassini_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the repository's fib_vajda at i=1 and j=3. This is a thin wrapper used to compute the difference of the proposed closed forms.

**Theorem 1.5 (Schulte's conjecture from row two onward).**

$$\forall n: \mathbb{N}, 2 \le n \implies \mathrm{altRowSum}\left(n\right) = \frac{\mathrm{F}\left(n - 2\right)}{\mathrm{F}\left(n + 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378277-harmonic-triangle-alternating-row-sums` (proved) by `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378277-harmonic-triangle-alternating-row-sums","declaration_gid":"D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2024). *OEIS A378277, denominators in a harmonic triangle based on products of Fibonacci numbers*. URL: <https://oeis.org/A378277>.

*Commentary.*

The second row sums to zero. The row-difference identity and the two-step product identity give identical increments for the finite sum and the Fibonacci quotient, so induction proves every n at least two.

**Theorem 1.6 (The first row).**

$$\mathrm{altRowSum}\left(1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture_one` (`✓ std3`). ∎

*Citation.* Werner Schulte (2024). *OEIS A378277, denominators in a harmonic triangle based on products of Fibonacci numbers*. URL: <https://oeis.org/A378277>.

*Commentary.*

The first row is 1. This is the separate first-row clause of the OEIS conjecture, whose convention is F(-1)=1; no negative natural index is introduced in Lean.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.altRowSum`
- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.altRowSum_succ_sub`
- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.denominator`
- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.fib_cassini_two`
- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.schulte_conjecture_one`
- Dependency: [D5/S1/Recurrence/FibVajda](../FibVajda.md)
