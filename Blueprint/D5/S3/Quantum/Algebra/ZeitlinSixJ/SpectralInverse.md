# Zeitlin Six-J SpectralInverse

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Lemma 1.1 (physical spectral inverse).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (j \le n) \Rightarrow ((l \le n) \Rightarrow ((j < l) \Rightarrow (\mathrm{physicalSpectralInverse}\left(n, j, l\right) = \mathrm{physicalG}\left(n, j, l\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/SpectralInverse.physical_spectral_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit Green matrix equals the spectral inverse of the physical Jacobi matrix. Positive pivots and their exact gap identify the two inverses.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/SpectralInverse.physical_spectral_inverse`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality](Orthogonality.md)
