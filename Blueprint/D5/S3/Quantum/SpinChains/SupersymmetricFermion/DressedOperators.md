# Supersymmetric fermion chain: DressedOperators

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (dressedWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall i \in \mathrm{Fin}\left(N\right),\; (\mathrm{dressedWord}\left(N, j, i\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left((\mathrm{val}\left(i\right)) + (1) = \mathrm{val}\left(j\right), \mathit{spinP}, \mathrm{ite}\left(i < j, \mathit{spinZ}, \mathrm{ite}\left(i = j, \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), \mathrm{ite}\left(\mathrm{val}\left(i\right) = (\mathrm{val}\left(j\right)) + (1), \mathit{spinP}, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.dressedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines dressedWord.

**Definition 1.2 (fullD).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; (\mathrm{fullD}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{tensorOp}\left(\mathrm{dressedWord}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullD.

**Theorem 1.3 (fullD far mixed anticomm).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(i\right)) + (1) < \mathrm{val}\left(j\right)) \Rightarrow (((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left(j\right)\right))) + ((\mathrm{adjoint}\left(\mathrm{fullD}\left(j\right)\right)) \cdot (\mathrm{fullD}\left(i\right))) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_far_mixed_anticomm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.4 (fullD far anticomm).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(i\right)) + (1) < \mathrm{val}\left(j\right)) \Rightarrow (((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{fullD}\left(j\right))) + ((\mathrm{fullD}\left(j\right)) \cdot (\mathrm{fullD}\left(i\right))) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_far_anticomm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Definition 1.5 (neighbourPWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall k \in \mathrm{Fin}\left(N\right),\; (\mathrm{neighbourPWord}\left(N, j, k\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left(((\mathrm{val}\left(k\right)) + (1) = \mathrm{val}\left(j\right)) \lor (\mathrm{val}\left(k\right) = (\mathrm{val}\left(j\right)) + (1)), \mathit{spinP}, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.neighbourPWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines neighbourPWord.

**Theorem 1.6 (fullD CAR).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; ((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left(i\right)\right))) + ((\mathrm{adjoint}\left(\mathrm{fullD}\left(i\right)\right)) \cdot (\mathrm{fullD}\left(i\right))) = \mathrm{tensorOp}\left(\mathrm{neighbourPWord}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_CAR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Definition 1.7 (splitWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall k \in \mathrm{Fin}\left(N\right),\; (\mathrm{splitWord}\left(N, j, k\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left((\mathrm{val}\left(k\right)) + (1) = \mathrm{val}\left(j\right), \mathit{spinP}, \mathrm{ite}\left(k < j, \mathit{spinZ}, \mathrm{ite}\left(k = j, \mathrm{adjoint}\left(\mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right)\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (\mathrm{val}\left(j\right)) + (1), \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (\mathrm{val}\left(j\right)) + (2), \mathrm{adjoint}\left(\mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right)\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (\mathrm{val}\left(j\right)) + (3), \mathit{spinP}, 1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.splitWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines splitWord.

**Definition 1.8 (fullSplit).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; (\mathrm{fullSplit}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{tensorOp}\left(\mathrm{splitWord}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullSplit.

**Theorem 1.9 (fullD before split anticomm).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(i\right)) + (1) < \mathrm{val}\left(j\right)) \Rightarrow (((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{fullSplit}\left(j\right))) + ((\mathrm{fullSplit}\left(j\right)) \cdot (\mathrm{fullD}\left(i\right))) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_before_split_anticomm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Definition 1.10 (numberWord).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall k \in \mathrm{Fin}\left(N\right),\; (\mathrm{numberWord}\left(N, i, k\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left(k = i, (1) - (\mathit{spinP}), 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.numberWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines numberWord.

**Theorem 1.11 (fullD number same).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; ((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{boolReindex}\left(\mathrm{localOp}\left(i, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) = \mathrm{fullD}\left(i\right)) \land ((\mathrm{boolReindex}\left(\mathrm{localOp}\left(i, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{fullD}\left(i\right)) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_number_same` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.12 (fullD number commute).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall j \in \mathrm{Fin}\left(N\right),\; (i \ne j) \Rightarrow ((\mathrm{fullD}\left(i\right)) \cdot (\mathrm{boolReindex}\left(\mathrm{localOp}\left(j, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) = (\mathrm{boolReindex}\left(\mathrm{localOp}\left(j, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{fullD}\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_number_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.dressedWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_CAR`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_before_split_anticomm`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_far_anticomm`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_far_mixed_anticomm`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_number_commute`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullD_number_same`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.fullSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.neighbourPWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.numberWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.splitWord`
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner](JordanWigner.md)
