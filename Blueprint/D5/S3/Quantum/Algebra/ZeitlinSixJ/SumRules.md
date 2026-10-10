# Zeitlin Six-J SumRules

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Theorem 1.1 (Six-j column cycle).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{sixJ}\left(a, b, c, d, e, f\right) = \mathrm{sixJ}\left(c, a, b, f, d, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_cycle_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cycling the three columns preserves the six-j symbol, including inadmissible labels where it vanishes.

**Theorem 1.2 (Six-j column interchange).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{sixJ}\left(a, b, c, d, e, f\right) = \mathrm{sixJ}\left(b, a, c, e, d, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_swap_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interchanging the first two columns preserves the six-j symbol for all doubled spin labels.

**Theorem 1.3 (Six-j paired flip).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{sixJ}\left(a, b, c, d, e, f\right) = \mathrm{sixJ}\left(d, e, c, a, b, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_flip_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interchanging the top and bottom entries in the first two columns preserves the six-j symbol.

**Theorem 1.4 (Shift a supported finite sum).**

$$\forall f \in \mathit{Nat} \to \mathit{Real},\; \forall n \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; (d \le r) \Rightarrow ((r \le n) \Rightarrow ((\forall i \in \mathit{Nat},\; ((i < d) \lor (r < i)) \Rightarrow (\mathrm{f}\left(i\right) = 0)) \Rightarrow (\sum_{t\in\mathrm{range}\left(((r) - (d)) + (1)\right)}(\mathrm{f}\left((d) + (t)\right)) = \sum_{i\in\mathrm{range}\left((n) + (1)\right)}(\mathrm{f}\left(i\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sum_shifted_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A function vanishing below d and above r has the same sum over the shifted range from d through r as over the full range from zero through n, provided d is at most r and r is at most n.

**Theorem 1.5 (Central six-j symbol).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{sixJ}\left((N) - (1), (N) - (1), (2) \cdot (i), (2) \cdot (j), (2) \cdot (l), (N) - (1)\right) = \mathrm{W}\left(N, i, j, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.central_symbol_is_W` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A paired flip and a column cycle identify the central symbol of the physical channel matrix with W.

**Theorem 1.6 (A central channel index).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (j \le n) \Rightarrow ((l \le n) \Rightarrow ((j \le l) \Rightarrow (\exists t \in \mathit{Nat},\; (t \le \mathrm{channelWidth}\left(n, j, l\right)) \land (\mathrm{channelLabel}\left(n, j, l, t\right) = n))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.channel_center_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ordered labels j and l at most n, the channel contains an index whose doubled spin label is n.

**Theorem 1.7 (Interchange the last two labels).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{W}\left(N, i, j, l\right) = \mathrm{W}\left(N, i, l, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.W_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equal bottom-row spins make W invariant under interchanging its last two top-row labels.

**Definition 1.8 (claim).**

$$(\mathit{claim}:\mathit{Prop}) = \left(\forall N \in \mathit{Nat},\; (2 \le N) \Rightarrow ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow ((j \ne l) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), \mathrm{casimir}\left((i) + (1)\right)\right)) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = \mathrm{div}\left(1, ((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)) \cdot (\left|(\mathrm{asReal}\left(\mathrm{real}\left(j\right)\right)) - (\mathrm{real}\left(l\right))\right|)) \cdot (((\mathrm{real}\left(j\right)) + (\mathrm{real}\left(l\right))) + (1))\right))))) \land ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(((((\mathrm{asReal}\left(-1\right))^{(i) + (1)}) \cdot (\mathrm{casimir}\left((i) + (1)\right))) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1))) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = (((\mathrm{asReal}\left(-1\right))^{(N) + (1)}) \cdot ((\mathrm{casimir}\left(j\right)) + (\mathrm{casimir}\left(l\right)))) \cdot (\mathrm{Wij}\left(N, l, j\right))))) \land ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(((\mathrm{casimir}\left((i) + (1)\right)) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1))) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = \mathrm{div}\left(((((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right))^{2}) - (1)) \cdot ((\mathrm{casimir}\left(j\right)) + (\mathrm{casimir}\left(l\right)))) - (((2) \cdot (\mathrm{casimir}\left(j\right))) \cdot (\mathrm{casimir}\left(l\right))), (\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)) \cdot (((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right))^{2}) - (1))\right)))) \land (\forall j \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), \mathrm{casimir}\left((i) + (1)\right)\right)) \cdot ((\mathrm{div}\left(1, \mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)\right)) + (((\mathrm{asReal}\left(-1\right))^{(((i) + (1)) + (j)) + (N)}) \cdot (\mathrm{Wij}\left(N, (i) + (1), j\right))))) = \mathrm{div}\left((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{harmonic}\left(j\right)\right)\right)), \mathrm{real}\left(N\right)\right))))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.claim` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Conjecture 1, page 6, section 2.2, equations (2.10)–(2.13): for every 1 ≤ j,l ≤ N−1, the four displayed identities hold; the inverse-Casimir identity alone requires j ≠ l. The complete source quotation, including the Casimir and harmonic-number conventions, is in the cited literature note. The encoding quantifies over natural N ≥ 2; W(N,i,j,l) is the top row i,j,l with bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) has top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2. Each sixJ argument is twice the corresponding spin. The sum variable i+1 in range(N−1) traverses exactly 1,...,N−1. The first identity alone assumes j≠l. Harmonic numbers are rational and are cast to Real.

**Theorem 1.9 (result).**

$$\forall N \in \mathit{Nat},\; (2 \le N) \Rightarrow ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow ((j \ne l) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), \mathrm{casimir}\left((i) + (1)\right)\right)) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = \mathrm{div}\left(1, ((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)) \cdot (\left|(\mathrm{asReal}\left(\mathrm{real}\left(j\right)\right)) - (\mathrm{real}\left(l\right))\right|)) \cdot (((\mathrm{real}\left(j\right)) + (\mathrm{real}\left(l\right))) + (1))\right))))) \land ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(((((\mathrm{asReal}\left(-1\right))^{(i) + (1)}) \cdot (\mathrm{casimir}\left((i) + (1)\right))) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1))) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = (((\mathrm{asReal}\left(-1\right))^{(N) + (1)}) \cdot ((\mathrm{casimir}\left(j\right)) + (\mathrm{casimir}\left(l\right)))) \cdot (\mathrm{Wij}\left(N, l, j\right))))) \land ((\forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(((\mathrm{casimir}\left((i) + (1)\right)) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1))) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = \mathrm{div}\left(((((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right))^{2}) - (1)) \cdot ((\mathrm{casimir}\left(j\right)) + (\mathrm{casimir}\left(l\right)))) - (((2) \cdot (\mathrm{casimir}\left(j\right))) \cdot (\mathrm{casimir}\left(l\right))), (\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)) \cdot (((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right))^{2}) - (1))\right)))) \land (\forall j \in \mathit{Nat},\; ((1 \le j) \land (j < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), \mathrm{casimir}\left((i) + (1)\right)\right)) \cdot ((\mathrm{div}\left(1, \mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)\right)) + (((\mathrm{asReal}\left(-1\right))^{(((i) + (1)) + (j)) + (N)}) \cdot (\mathrm{Wij}\left(N, (i) + (1), j\right))))) = \mathrm{div}\left((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{harmonic}\left(j\right)\right)\right)), \mathrm{real}\left(N\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result` (`✓ std3`). ∎

*Resolves.* `Problems/lichtenfelz-modin-preston-2026-zeitlin-sixj-identities` (proved) by `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lichtenfelz-modin-preston-2026-zeitlin-sixj-identities","declaration_gid":"D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The four identities hold over their complete stated ranges. The Green inverse, parity addition, Jacobi diagonal and harmonic antidifference give the four conjuncts.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.W_swap`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.central_symbol_is_W`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.channel_center_label`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_cycle_columns`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_flip_pair`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sixJ_swap_columns`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.sum_shifted_support`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Alternating](Alternating.md)
