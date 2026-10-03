# Zeitlin Six-J Alternating

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Theorem 1.1 (alternating moment open).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (2 \le N) \Rightarrow (((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}(((((\mathrm{asReal}\left(-1\right))^{(i) + (1)}) \cdot (\mathrm{casimir}\left((i) + (1)\right))) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1))) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = (((\mathrm{asReal}\left(-1\right))^{(N) + (1)}) \cdot ((\mathrm{casimir}\left(j\right)) + (\mathrm{casimir}\left(l\right)))) \cdot (\mathrm{Wij}\left(N, l, j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Alternating.alternating_moment_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity (2.11) holds for every positive j and l below N, including j=l. The parity anticommutator and the signed Racah addition matrix evaluate the alternating Casimir moment.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Alternating.alternating_moment_open`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Parity](Parity.md)
