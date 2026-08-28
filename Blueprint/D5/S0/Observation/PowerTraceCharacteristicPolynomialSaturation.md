# Characteristic-Polynomial Saturation of Power Traces

## Abstract

Cayley-Hamilton bounds the recurrence depth of every matrix power trace.

**Theorem 1.1 (The first dimension-many traces determine all later traces).**

$$\begin{aligned}\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right), n \in \mathbb{N},\\A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \Rightarrow\\(A^{n} = -\sum_{k < n} \operatorname{coeff}\left(\operatorname{charpoly}\left(A\right), k\right) \times A^{k}) \land\\(\forall m \in \mathbb{N}, \operatorname{tr}\left(A^{n + m}\right) = -\sum_{k < n} \operatorname{coeff}\left(\operatorname{charpoly}\left(A\right), k\right) \times \operatorname{tr}\left(A^{k + m}\right)) \land\\\forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right), (\operatorname{charpoly}\left(B\right) = \operatorname{charpoly}\left(A\right) \land \forall k \in \mathbb{N}, k < n \Rightarrow \operatorname{tr}\left(A^{k + 1}\right) = \operatorname{tr}\left(B^{k + 1}\right)) \Rightarrow \forall r \in \mathbb{N}, \operatorname{tr}\left(A^{r + 1}\right) = \operatorname{tr}\left(B^{r + 1}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation.power_trace_characteristic_polynomial_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an n-by-n matrix over any field, its monic characteristic polynomial and Cayley-Hamilton identity express the nth power as the negative coefficient-weighted sum of lower powers.

Multiplication by a further power and linearity of the matrix trace give the displayed recurrence at every offset. Strong induction then shows that two matrices with the same characteristic polynomial and the same first n positive-power traces have all positive-power traces equal.

The formal result strengthens the source context: characteristic zero is unnecessary for this Cayley-Hamilton consequence. Pinned Mathlib supplies the canonical Cayley-Hamilton theorem; repository and library searches found no exact result packaging all three public clauses.

## References

- Truth anchor: `D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation.power_trace_characteristic_polynomial_saturation`
