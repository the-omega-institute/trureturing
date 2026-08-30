# Passive Memory No-Backreaction

## Abstract

Passive upper-triangular memory can retain observer order in an off-diagonal holonomy while leaving scalar spectral roots unchanged.

**Theorem 1.1 (Adjacent-swap holonomy is purely off-diagonal).**

For

$$
U(B,L)=
\begin{pmatrix}
F&B\\
0&L
\end{pmatrix},
$$

set

$$
U_p=U((L_p-1)v,L_p),
\qquad
U_q=U((L_q-1)v,L_q).
$$

Then

$$
U_pU_q-U_qU_p=
\begin{pmatrix}
0&(L_q-L_p)(F-1)v\\
0&0
\end{pmatrix}.
$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the canonical injection $(L-1)v$, reversing two memory steps changes only the off-diagonal memory entry. The associated trace and determinant vanish by direct corollaries in the Lean module.

**Theorem 1.2 (Passive memory leaves the characteristic polynomial unchanged).**

For arbitrary $F,L,B_1,B_2\in\mathbb C$,

$$
\operatorname{charpoly}U(B_1,L)
=
\operatorname{charpoly}U(B_2,L).
$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_charpoly_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed diagonal data, replacing one memory injection by another does not change the characteristic polynomial. The passive triangular lift therefore cannot move scalar spectral roots without a feedback channel.

**Theorem 1.3 (Passive memory can still retain order).**

The matrices

$$
U_p=
\begin{pmatrix}
2&1\\
0&2
\end{pmatrix},
\qquad
U_q=
\begin{pmatrix}
2&2\\
0&3
\end{pmatrix}
$$

do not commute.

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_order_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed two-by-two matrices give a concrete noncommuting pair, so the off-diagonal memory channel is not definitionally or vacuously zero.

## Research boundary

This theorem formalizes a negative boundary for the current golden-prime memory observer. Upper-triangular memory can archive prime-word order, but its passive off-diagonal channel does not alter the scalar characteristic roots. Any route that lets memory affect a zeta zero must introduce a genuine feedback or transfer-function coupling and prove its exact relation to the Weil or completed-zeta object.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_formula`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_charpoly_invariant`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_order_witness`
