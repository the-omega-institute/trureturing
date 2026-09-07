# Finite Shifted Record Realization

## Abstract

Concrete finite shifted records realize the normalized coefficient coherence channel.

**Theorem 1.1 (Concrete normalized records and their signed overlaps).**

$$\forall S \in FiniteType, N \in Nat, c \in \mathbb{Z} \to \mathbb{C}, q \in S \to \mathbb{Z},\; \left(\left(\forall n \in \mathbb{Z},\; \left(n < 0 \lor N < n\right) \Rightarrow c\left(n\right) = 0\right) \land \sum_{n \in \operatorname{Icc}\left(0, N\right)} {\operatorname{norm}\left(c\left(n\right)\right)^{2}} = 1\right) \Rightarrow \operatorname{let} Q = \sum_{i \in S} {\operatorname{natAbs}\left(q\left(i\right)\right)}; \operatorname{let} L = N + 2 \cdot Q + 1; \operatorname{let} D = \operatorname{Icc}\left(-Q, N + Q\right); \operatorname{let} \forall a \in \operatorname{Fin}\left(L\right),\; coord\left(a\right) = \operatorname{int}\left(a\right) - Q; \operatorname{let} \forall i \in S, a \in \operatorname{Fin}\left(L\right),\; E\left(i\right)\left(a\right) = c\left(coord\left(a\right) + q\left(i\right)\right); \operatorname{let} \forall ell \in \mathbb{Z},\; \gamma\left(ell\right) = \sum_{n \in \operatorname{Icc}\left(0, N\right)} {c\left(n + ell\right) \cdot \operatorname{conj}\left(c\left(n\right)\right)}; \left(\left(\left(\operatorname{range}\left(coord\right) = D \land \operatorname{Injective}\left(coord\right)\right) \land \left(\forall i \in S, m \in \mathbb{Z},\; c\left(m + q\left(i\right)\right) \ne 0 \Rightarrow m \in D\right)\right) \land \left(\forall i \in S,\; \sum_{a \in \operatorname{Fin}\left(L\right)} {\operatorname{norm}\left(E\left(i\right)\left(a\right)\right)^{2}} = 1\right)\right) \land \left(\forall i \in S, j \in S,\; \sum_{a \in \operatorname{Fin}\left(L\right)} {\operatorname{conj}\left(E\left(j\right)\left(a\right)\right) \cdot E\left(i\right)\left(a\right)} = \gamma\left(q\left(i\right) - q\left(j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.shifted_coefficient_records` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S is an arbitrary finite system basis. Integer labels q may repeat or be negative, and S may be empty. The coefficient function is zero outside the integer interval from zero to N and its squared norms sum to one. Q is the sum of absolute labels, so the explicit interval D contains every shifted support. Its coordinate enumeration is both onto D and injective. The record norms and overlaps follow from the coefficient hypotheses by finite reindexing; they are conclusions, not additional hypotheses.

**Theorem 1.2 (The actual finite marginal is a completely positive trace-preserving channel).**

$$\forall S \in FiniteType, N \in Nat, c \in \mathbb{Z} \to \mathbb{C}, q \in S \to \mathbb{Z},\; \left(\left(\forall n \in \mathbb{Z},\; \left(n < 0 \lor N < n\right) \Rightarrow c\left(n\right) = 0\right) \land \sum_{n \in \operatorname{Icc}\left(0, N\right)} {\operatorname{norm}\left(c\left(n\right)\right)^{2}} = 1\right) \Rightarrow \operatorname{let} Q = \sum_{i \in S} {\operatorname{natAbs}\left(q\left(i\right)\right)}; \operatorname{let} L = N + 2 \cdot Q + 1; \operatorname{let} D = \operatorname{Icc}\left(-Q, N + Q\right); \operatorname{let} \forall a \in \operatorname{Fin}\left(L\right),\; coord\left(a\right) = \operatorname{int}\left(a\right) - Q; \operatorname{let} \forall i \in S, a \in \operatorname{Fin}\left(L\right),\; E\left(i\right)\left(a\right) = c\left(coord\left(a\right) + q\left(i\right)\right); \operatorname{let} \forall ell \in \mathbb{Z},\; \gamma\left(ell\right) = \sum_{n \in \operatorname{Icc}\left(0, N\right)} {c\left(n + ell\right) \cdot \operatorname{conj}\left(c\left(n\right)\right)}; \operatorname{let} \forall i \in S, a \in \operatorname{Fin}\left(L\right), j \in S,\; \operatorname{entry}\left(V, \operatorname{pair}\left(i, a\right), j\right) = \operatorname{ite}\left(j = i, E\left(i\right)\left(a\right), 0\right); \operatorname{let} \forall X \in \operatorname{Matrix}\left(S \times \operatorname{Fin}\left(L\right), S \times \operatorname{Fin}\left(L\right), \mathbb{C}\right), i \in S, j \in S,\; \operatorname{entry}\left(T\left(X\right), i, j\right) = \sum_{a \in \operatorname{Fin}\left(L\right)} {\operatorname{entry}\left(X, \operatorname{pair}\left(i, a\right), \operatorname{pair}\left(j, a\right)\right)}; \operatorname{let} \forall rho \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \Lambda\left(rho\right) = T\left(V \cdot rho \cdot V^{*}\right); \left(\left(\left(\left(\left(\left(\left(\left(\operatorname{range}\left(coord\right) = D \land \operatorname{Injective}\left(coord\right)\right) \land \left(\forall i \in S, m \in \mathbb{Z},\; c\left(m + q\left(i\right)\right) \ne 0 \Rightarrow m \in D\right)\right) \land \left(\forall i \in S,\; \sum_{a \in \operatorname{Fin}\left(L\right)} {\operatorname{norm}\left(E\left(i\right)\left(a\right)\right)^{2}} = 1\right)\right) \land \left(\forall i \in S, j \in S,\; \sum_{a \in \operatorname{Fin}\left(L\right)} {\operatorname{conj}\left(E\left(j\right)\left(a\right)\right) \cdot E\left(i\right)\left(a\right)} = \gamma\left(q\left(i\right) - q\left(j\right)\right)\right)\right) \land \left(\forall ell \in \mathbb{Z},\; \gamma\left(ell\right) = \sum_{n \in \mathbb{Z}} {c\left(n + ell\right) \cdot \operatorname{conj}\left(c\left(n\right)\right)}\right)\right) \land V^{*} \cdot V = 1\right) \land \left(\exists C \in \operatorname{QuantumChannel}\left(S, S\right),\; \forall rho \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{fromCstar}\left(\operatorname{apply}\left(C, \operatorname{toCstar}\left(rho\right)\right)\right) = \Lambda\left(rho\right)\right)\right) \land \left(\forall rho \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right), i \in S, j \in S,\; \operatorname{entry}\left(\Lambda\left(rho\right), i, j\right) = \gamma\left(q\left(i\right) - q\left(j\right)\right) \cdot \operatorname{entry}\left(rho, i, j\right)\right)\right) \land \left(\forall rho \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{trace}\left(\Lambda\left(rho\right)\right) = \operatorname{trace}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.finite_shifted_record_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual recording V sends basis vector i to i tensored with E(i). T sums equal environment coordinates and Lambda is defined by applying T to V rho V adjoint. The channel is never defined by the desired entry formula. The frozen environment marginal theorem supplies that formula after finite-coordinate transport and substitution of the proved overlap.

QuantumChannel is the canonical FiniteStateChannel bundle of Mathlib CompletelyPositiveMap on CStarMatrix and trace preservation. Its positivity holds at every finite amplification, and both its equality with Lambda and the entry identity hold for every complex matrix. toCstar and fromCstar denote CStarMatrix.ofMatrix and its inverse; adjoint means conjugate transpose. The integer gamma sum is the tsum of the zero-extended coefficients.

This is one finite isometric realization. It makes no claim of energy conservation for a specified Hamiltonian, spatial locality, zero operation cost, or universality over all reference devices. QUANTUM-REALITY definition74.1 and theorem74.1 supply the source provenance; commentary there about existing repository code is not an extra mathematical claim.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.finite_shifted_record_channel`
- Truth anchor: `D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.shifted_coefficient_records`
- Dependency: [D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel](EnvironmentMarginalChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
