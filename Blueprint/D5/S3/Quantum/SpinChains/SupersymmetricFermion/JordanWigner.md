# Supersymmetric fermion chain: JordanWigner

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (Local).**

$$(\mathrm{Local}\left(\right):\mathit{Type}) = \mathrm{Matrix}\left(\mathit{Bool}, \mathit{Bool}, \mathit{Complex}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines Local.

**Definition 1.2 (FullOperator).**

$$\forall N \in \mathit{Nat},\; (\mathrm{FullOperator}\left(N\right):\mathit{Type}) = \mathrm{Matrix}\left(\mathrm{Assignment}\left(N\right), \mathrm{Assignment}\left(N\right), \mathit{Complex}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines FullOperator.

**Definition 1.3 (fermionWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall i \in \mathrm{Fin}\left(N\right),\; (\mathrm{fermionWord}\left(N, j, i\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left(i < j, \mathit{spinZ}, \mathrm{ite}\left(i = j, \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fermionWord.

**Definition 1.4 (fullC).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; (\mathrm{fullC}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{tensorOp}\left(\mathrm{fermionWord}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullC.

**Definition 1.5 (prefixCount).**

$$\forall N \in \mathit{Nat},\; \forall t \in \mathrm{Assignment}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; (\mathrm{prefixCount}\left(N, t, j\right):\mathit{Nat}) = \mathrm{card}\left(\mathrm{Finsetunivfilter}\left(i:\mathrm{Fin}\left(N\right)\mapsto((i < j) \land (t\left(i\right) = \mathit{true}))\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.prefixCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines prefixCount.

**Theorem 1.6 (fullC anticomm of lt).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; (i < j) \Rightarrow (((\mathrm{fullC}\left(i\right)) \cdot (\mathrm{fullC}\left(j\right))) + ((\mathrm{fullC}\left(j\right)) \cdot (\mathrm{fullC}\left(i\right))) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt` (`✓ std3`). ∎

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.7 (fullC CAR).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; ((\mathrm{fullC}\left(i\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullC}\left(i\right)\right))) + ((\mathrm{adjoint}\left(\mathrm{fullC}\left(i\right)\right)) \cdot (\mathrm{fullC}\left(i\right))) = (1:\mathrm{FullOperator}\left(N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR` (`✓ std3`). ∎

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.8 (fullC mixed anticomm of lt).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; (i < j) \Rightarrow (((\mathrm{fullC}\left(i\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullC}\left(j\right)\right))) + ((\mathrm{adjoint}\left(\mathrm{fullC}\left(j\right)\right)) \cdot (\mathrm{fullC}\left(i\right))) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt` (`✓ std3`). ∎

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.prefixCount`
- Dependency: [D5/S3/Quantum/Dynamics/ClauseHamiltonian](../../Dynamics/ClauseHamiltonian.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../../Information/StabilizerPairLocalUnitaryInequivalence.md)
