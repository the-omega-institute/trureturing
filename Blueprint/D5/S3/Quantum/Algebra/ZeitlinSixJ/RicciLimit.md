# Zeitlin Ricci Curvature Limit

## Abstract

Averaged Ricci curvature of the Zeitlin metric.

Nat and Real denote natural and real numbers. real is the natural-to-real or rational-to-real cast. Natural subtraction is truncated at zero. range(n) is {0,...,n-1}; the shifted indices i+1 and j+1 therefore traverse 1,...,N-1. div is field division and ite selects a value according to its condition. W is the six-j symbol with equal bottom-row spins (N-1)/2; casimir(k)=k(k+1). harmonic(l) is rational and is cast to Real.

**Definition 1.1 (Positive contribution).**

$$\forall l \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (\mathrm{rPlus}\left(l, N\right):\mathit{Real}) = (\mathrm{div}\left(\mathrm{real}\left(N\right), \mathrm{div}\left(4, ((\mathrm{real}\left(N\right))^{2}) - (1)\right)\right)) \cdot (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(\sum_{j\in\mathrm{range}\left((N) - (1)\right)}(\mathrm{ite}\left(\mathrm{Odd}\left((((i) + (1)) + ((j) + (1))) + (l)\right), (\mathrm{div}\left(((\mathrm{casimir}\left(l\right)) \cdot (((2) \cdot (\mathrm{real}\left((i) + (1)\right))) + (1))) \cdot (((2) \cdot (\mathrm{real}\left((j) + (1)\right))) + (1)), (\mathrm{casimir}\left((i) + (1)\right)) \cdot (\mathrm{casimir}\left((j) + (1)\right))\right)) \cdot ((\mathrm{W}\left(N, l, (i) + (1), (j) + (1)\right))^{2}), 0\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rPlus` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Equation (2.4) gives the positive contribution. The prefactor N divided by 4/(N squared minus 1) is N divided by the squared quantization parameter. Only odd total top-row parity contributes.

**Definition 1.2 (Negative contribution).**

$$\forall l \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (\mathrm{rMinus}\left(l, N\right):\mathit{Real}) = (\mathrm{div}\left(\mathrm{real}\left(N\right), \mathrm{div}\left(4, ((\mathrm{real}\left(N\right))^{2}) - (1)\right)\right)) \cdot (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(\sum_{j\in\mathrm{range}\left((N) - (1)\right)}(\mathrm{ite}\left(\mathrm{Odd}\left((((i) + (1)) + ((j) + (1))) + (l)\right), (\mathrm{div}\left(((((\mathrm{casimir}\left((i) + (1)\right)) - (\mathrm{casimir}\left((j) + (1)\right)))^{2}) \cdot (((2) \cdot (\mathrm{real}\left((i) + (1)\right))) + (1))) \cdot (((2) \cdot (\mathrm{real}\left((j) + (1)\right))) + (1)), ((\mathrm{casimir}\left((i) + (1)\right)) \cdot (\mathrm{casimir}\left((j) + (1)\right))) \cdot (\mathrm{casimir}\left(l\right))\right)) \cdot ((\mathrm{W}\left(N, l, (i) + (1), (j) + (1)\right))^{2}), 0\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rMinus` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Equation (2.4) gives the negative contribution, weighted by the squared difference of the two summation Casimirs.

**Definition 1.3 (Averaged Ricci curvature).**

$$\forall l \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (\mathrm{rTilde}\left(l, N\right):\mathit{Real}) = \mathrm{div}\left((\mathrm{rPlus}\left(l, N\right)) - (\mathrm{rMinus}\left(l, N\right)), ((\mathrm{real}\left(N\right))^{2}) - (1)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rTilde` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Equation (2.15) divides the Ricci curvature by the dimension N squared minus 1.

**Definition 1.4 (The Ricci limit conjecture).**

$$(\mathit{claim}:\mathit{Prop}) = \left(\forall l \in \mathit{Nat},\; (2 \le l) \Rightarrow ((\mathrm{Tendsto}\left(((N:\mathit{Nat})\mapsto\mathrm{rTilde}\left(l, N\right)), \mathit{atTop}, \mathrm{nhds}\left(\mathrm{div}\left(-\left((\mathrm{real}\left(\mathrm{harmonic}\left(l\right)\right)) - (1)\right), 2\right)\right)\right)) \land (\exists N0 \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (\mathit{N0} \le N) \Rightarrow (\mathrm{rTilde}\left(l, N\right) < 0)))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.claim` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Conjecture 2 in section 2.2 asserts that for every fixed label at least two the averaged curvature tends to minus one half of the harmonic number minus one, and is negative for all sufficiently large dimensions. The threshold may depend on the fixed label.

**Theorem 1.5 (Decay at fixed odd labels).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; (\mathrm{Odd}\left(((a) + (b)) + (c)\right)) \Rightarrow (\mathrm{Tendsto}\left(((N:\mathit{Nat})\mapsto(\mathrm{real}\left(N\right)) \cdot ((\mathrm{W}\left(N, a, b, c\right))^{2})), \mathit{atTop}, \mathrm{nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.fixed_labels_odd_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed odd-parity triple, N times the squared six-j symbol tends to zero. The odd weighted Casimir moment tends to zero by the terminating Racah expansion. Its nonnegative summands bound each fixed positive label; a zero label has inadmissible odd parity and contributes zero.

**Theorem 1.6 (Vanishing positive contribution).**

$$\forall l \in \mathit{Nat},\; (2 \le l) \Rightarrow (\mathrm{Tendsto}\left(((N:\mathit{Nat})\mapsto\mathrm{div}\left(\mathrm{rPlus}\left(l, N\right), ((\mathrm{real}\left(N\right))^{2}) - (1)\right)), \mathit{atTop}, \mathrm{nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rPlus_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed label at least two, the normalized positive contribution tends to zero. Each fixed row vanishes because triangle support leaves only finitely many odd-parity terms. Away from the diagonal row, the inverse-Casimir identity gives a summable bound independent of N; the diagonal row also vanishes. Dominated convergence therefore applies to the sum of rows.

**Theorem 1.7 (Exact negative contribution).**

$$\forall l \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (2 \le l) \Rightarrow ((l < N) \Rightarrow (\mathrm{div}\left(\mathrm{rMinus}\left(l, N\right), ((\mathrm{real}\left(N\right))^{2}) - (1)\right) = \mathrm{div}\left((\mathrm{real}\left(\mathrm{harmonic}\left(l\right)\right)) - (1), 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rMinus_eq` (`✓ std3`). ∎

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

For dimensions greater than the fixed label, the normalized negative contribution is one half of the harmonic number minus one. The source's Theorem 3 states this value under its Conjecture 1, which SumRules proves. Expanding the squared Casimir difference and interchanging the two summation labels reduces the double sum to odd moments. Orthogonality, signed parity addition and the weighted sum rules leave the harmonic sum rule. The values at labels two and three are one quarter and five twelfths.

**Theorem 1.8 (Harmonic limit and eventual negativity).**

$$\forall l \in \mathit{Nat},\; (2 \le l) \Rightarrow ((\mathrm{Tendsto}\left(((N:\mathit{Nat})\mapsto\mathrm{rTilde}\left(l, N\right)), \mathit{atTop}, \mathrm{nhds}\left(\mathrm{div}\left(-\left((\mathrm{real}\left(\mathrm{harmonic}\left(l\right)\right)) - (1)\right), 2\right)\right)\right)) \land (\exists N0 \in \mathit{Nat},\; \forall N \in \mathit{Nat},\; (\mathit{N0} \le N) \Rightarrow (\mathrm{rTilde}\left(l, N\right) < 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/lichtenfelz-modin-preston-2026-zeitlin-ricci-limit` (proved) by `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lichtenfelz-modin-preston-2026-zeitlin-ricci-limit","declaration_gid":"D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every fixed label at least two, the averaged curvature tends to minus one half of the harmonic number minus one. The positive contribution vanishes and the negative contribution is exact. Since the harmonic number exceeds one, the limit is strictly negative, and convergence gives a dimension threshold beyond which the curvature is negative.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.fixed_labels_odd_tendsto_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rMinus`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rMinus_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rPlus`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rPlus_tendsto_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.rTilde`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.result`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules](SumRules.md)
