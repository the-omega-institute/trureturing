# FinitePreparationChannel

## Abstract

Finite density-state preparation as an actual quantum channel

**Theorem 1.1 (Finite density-state preparation as an actual quantum channel).**

$$\forall u:\operatorname{Level}(),\ \forall v:\operatorname{Level}(),\ \forall a:\operatorname{Type}(u),\ {\operatorname{Fintype}(a)\land \operatorname{DecidableEq}(a)}\implies \forall b:\operatorname{Type}(v),\ {\operatorname{Fintype}(b)\land \operatorname{DecidableEq}(b)}\implies \forall rho:a\Rightarrow \operatorname{DensityState}(b),\ \exists Phi:\operatorname{QuantumChannel}(a, b),\ \forall X:\operatorname{Matrix}(a, a, \mathbb{C}),\ \operatorname{raw}(\operatorname{apply}(Phi, X))=\sum _{i}(\operatorname{entry}(X, i, i))\times (\operatorname{raw}(\operatorname{apply}(rho, i)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_preparation_quantum_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For an arbitrary finite family of actual density matrices, there exists a canonical CPTP map whose action on every complex input matrix X is the sum of its diagonal entries Xii times the respective density matrices. The construction uses columns of each positive square root as Kraus operators. The normalization follows from the actual trace-one condition, including singular outputs, and the full-algebra action is proved from the same Kraus family. For x in [0,1], take the two prepared qubits (I+xX plus or minus sqrt(1-x squared)Z)/2. On the diagonal input (I+tZ)/2, the formula gives (I+xX+t sqrt(1-x squared)Z)/2 for every real t. For t in [-1,1], these inputs and outputs are density states. This physical preparation operation asserts no entropy inequality by itself.

**Theorem 1.2 (Local preparation with an arbitrary quantum spectator).**

$$\forall u:\operatorname{Level}(),\ \forall v:\operatorname{Level}(),\ \forall w:\operatorname{Level}(),\ \forall a:\operatorname{Type}(u),\ {\operatorname{Fintype}(a)\land \operatorname{DecidableEq}(a)}\implies \forall b:\operatorname{Type}(v),\ {\operatorname{Fintype}(b)\land \operatorname{DecidableEq}(b)}\implies \forall s:\operatorname{Type}(w),\ {\operatorname{Fintype}(s)\land \operatorname{DecidableEq}(s)}\implies \forall rho:a\Rightarrow \operatorname{DensityState}(b),\ \exists Phi:\operatorname{QuantumChannel}(\operatorname{Prod}(s, a), \operatorname{Prod}(s, b)),\ \forall X:\operatorname{Matrix}(\operatorname{Prod}(s, a), \operatorname{Prod}(s, a), \mathbb{C}),\ \forall r,t:\operatorname{Prod}(s, b),\ \operatorname{entry}(\operatorname{raw}(\operatorname{apply}(Phi, X)), r, t)=\sum _{i}(\operatorname{entry}(X, \operatorname{pair}(\operatorname{fst}(r), i), \operatorname{pair}(\operatorname{fst}(t), i)))\times (\operatorname{entry}(\operatorname{raw}(\operatorname{apply}(rho, i)), \operatorname{snd}(r), \operatorname{snd}(t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_local_preparation_quantum_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Tensoring each preparation Kraus operator with the spectator identity gives an actual CPTP map on the joint matrix algebra. Its matrix entries are the sum over the measured input index of the original spectator block entry times the prepared density entry. Thus every off-diagonal spectator coherence is preserved. The spectator, input and output dimensions are arbitrary finite types, and prepared states may be singular. This is the physical local operation needed before applying canonical relative-entropy data processing; it assumes no mutual-information inequality.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_local_preparation_quantum_channel`
- Truth anchor: `D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_preparation_quantum_channel`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](FiniteKrausChannel.md)
