# Newton Power Sums Determine the Characteristic Polynomial

## Abstract

Newton identities recover a split characteristic polynomial from its bounded power sums.

**Theorem 1.1 (The first dimension-many spectral power sums determine the charpoly).**

$$\begin{aligned}\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right), \operatorname{CharZero}\left(K\right), n \in \mathbb{N},\\\forall A, B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right), lambda, mu \in \operatorname{Fin}\left(n\right) \to K,\\(\operatorname{charpoly}\left(A\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} (t - lambda(i)) \land \operatorname{charpoly}\left(B\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} (t - mu(i)) \land \forall k \in \mathbb{N}, k < n \Rightarrow \sum_{i \in \operatorname{Fin}\left(n\right)} lambda(i)^{k + 1} = \sum_{i \in \operatorname{Fin}\left(n\right)} mu(i)^{k + 1}) \Rightarrow\\\operatorname{charpoly}\left(A\right) = \operatorname{charpoly}\left(B\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/NewtonPowerSumCharacteristicPolynomial.matrix_charpoly_eq_of_spectral_power_sums_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two n-by-n matrices over a characteristic-zero field have enumerated split spectra. If the first n positive power sums of those spectra agree, then their characteristic polynomials agree.

Pinned Mathlib's Newton identity recursively recovers each elementary symmetric polynomial because every positive natural number is nonzero in the field. Mathlib's Vieta expansion then identifies the two products of linear factors.

Characteristic zero is explicit: without it, the natural-number factor in the Newton recurrence cannot always be cancelled. The split factorization hypotheses expose the spectral witnesses used by the source argument rather than assuming an unavailable trace-to-root bridge.

## References

- Truth anchor: `D5/S0/Observation/NewtonPowerSumCharacteristicPolynomial.matrix_charpoly_eq_of_spectral_power_sums_eq`
