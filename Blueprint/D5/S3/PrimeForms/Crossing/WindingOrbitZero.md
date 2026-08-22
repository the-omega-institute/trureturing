# Unique Winding Zero on a Crossing Orbit

## Abstract

Exact crossing-sandwich propagation gives a unique zero on every admissible forward orbit with nonnegative even initial winding phase.

**Definition 1.1 (The crossing sandwich transformation).**

$$S(A)=MAM,\quad M=\begin{pmatrix}3&1\\2&1\end{pmatrix}$$

*Formalization.* `D5/S3/PrimeForms/Crossing/WindingOrbitZero.crossingSandwich` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The self-map S sends a positive-coordinate matrix A to M A M, where M = [[3,1],[2,1]] is the fixed determinant-one crossing matrix.

**Theorem 1.2 (An even winding phase reaches zero exactly once).**

$$\forall A=\begin{pmatrix}a&b\\c&d\end{pmatrix}, k\in\mathbb{N},\ 0<a \land 0<c \land 0<d \land ad=bc+1 \land \operatorname{Psi}(A)=2k \Rightarrow \exists! n\in\mathbb{N},\ \operatorname{Psi}(S^{n}(A))=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/WindingOrbitZero.sandwich_orbit_has_unique_winding_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A = [[a,b],[c,d]] have positive a, c, and d and determinant one. If its winding phase is the nonnegative even integer 2k, then the forward crossing-sandwich orbit has winding phase zero at exactly one natural time, namely k.

The imported exact propagation laws show that right and left multiplication by M lower the winding phase by two in total. Direct determinant arithmetic proves that positivity and the determinant-one relation survive every sandwich.

Mathlib's Function.Semiconj.iterate_right transports both the matrix orbit and the phase law through arbitrary iteration. The resulting closed form Psi(S^n(A)) = Psi(A)-2n makes existence and uniqueness a rational-arithmetic consequence.

This closes only the E.37 clause that exact stepwise descent yields the forward-orbit formula and a unique zero for an even nonnegative initial phase. It does not formalize the source's lattice-orbit classification, its all-integer two-sided orbit claim, or the m=36 genealogy.

Repository search found and reused the exact one-step Rademacher phase laws in ExactPropagation. Pinned-Mathlib searches found the exact iteration transport theorem Function.Semiconj.iterate_right but no matching constant-step unique-zero theorem.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/WindingOrbitZero.crossingSandwich`
- Truth anchor: `D5/S3/PrimeForms/Crossing/WindingOrbitZero.sandwich_orbit_has_unique_winding_zero`
