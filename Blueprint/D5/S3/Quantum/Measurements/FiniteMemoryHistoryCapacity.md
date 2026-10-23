# Finite Memory History Capacity

## Abstract

Perfectly distinguishable density matrices number at most the memory dimension.

**Lemma 1.1 (Zero trace pairing forces zero product).**

$$\begin{aligned}\forall d: Nat,\\\forall E, rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}),\\\operatorname{PosSemidef}(E) \Rightarrow\operatorname{PosSemidef}(rho) \Rightarrow\\\operatorname{Tr}(E \cdot rho) = 0 \Rightarrow E \cdot rho = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite dimension d, positive semidefinite matrices E and rho with Tr(E rho) = 0 satisfy E rho = 0. Factoring each positive matrix as an adjoint times itself reduces the trace pairing to a squared matrix norm. The capacity theorem uses this product identity to place state ranges in effect kernels.

**Theorem 1.2 (Exact history capacity of finite quantum memory).**

$$\begin{aligned}\forall N, d: Nat,\\\forall \rho, E: \operatorname{Fin}(N) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}),\\(\forall i: \operatorname{Fin}(N), \operatorname{PosSemidef}(\rho_{i}) \land \operatorname{Tr}(\rho_{i}) = 1) \Rightarrow\\(\forall j: \operatorname{Fin}(N), \operatorname{PosSemidef}(E_{j})) \Rightarrow\\(\sum_{j: \operatorname{Fin}(N)} E_{j} = I) \Rightarrow\\(\forall i, j: \operatorname{Fin}(N), \operatorname{Tr}(E_{j} \cdot \rho_{i}) = \operatorname{if}(i = j, 1, 0)) \Rightarrow\\N \leq d.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity.finite_memory_history_capacity` (`✓ std3`). ∎

*Citation.* Stephen M. Barnett and Sarah Croke (2009). *Quantum state discrimination*. DOI: [10.1364/AOP.1.000238](https://doi.org/10.1364/AOP.1.000238).

*Commentary.*

The memory has complex dimension d. Histories are represented by the indexed density matrices rho, and E is one designated POVM. PosSemidef means positive semidefinite, Tr is the complex matrix trace, I is the identity matrix, and if selects its second or third argument according to its first argument.

A zero trace pairing of two positive matrices forces their product to vanish, so the state range lies in the effect kernel. Applying this to the positive complement of an effect with unit probability puts its state range in the one-eigenspace.

The state ranges are therefore pairwise orthogonal. Trace one makes every state nonzero. Choosing a nonzero vector in each range gives a linearly independent family in dimension d.

This bound concerns perfectly distinguishable records, rather than the number of real parameters of a density matrix. Barnett and Croke provide the literature context for discrimination and orthogonal supports; the cited note identifies the scope.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity.finite_memory_history_capacity`
- Truth anchor: `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero`
