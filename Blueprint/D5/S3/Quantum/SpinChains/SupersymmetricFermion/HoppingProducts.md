# Supersymmetric fermion chain: HoppingProducts

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (fullPAt).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{fullPAt}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{tensorOp}\left(k:\mathrm{Fin}\left(N\right)\mapsto(\mathrm{ite}\left(\mathrm{val}\left(k\right) = j, \mathit{spinP}, 1\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullPAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullPAt.

**Definition 1.2 (fullLeftP).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{fullLeftP}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{tensorOp}\left(k:\mathrm{Fin}\left(N\right)\mapsto(\mathrm{ite}\left((\mathrm{val}\left(k\right)) + (1) = j, \mathit{spinP}, 1\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullLeftP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullLeftP.

**Definition 1.3 (hopWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathrm{Fin}\left(N\right),\; (\mathrm{hopWord}\left(N, j, k\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left((\mathrm{val}\left(k\right)) + (1) = j, \mathit{spinP}, \mathrm{ite}\left(\mathrm{val}\left(k\right) = j, \mathrm{adjoint}\left(\mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right)\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (1), \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (2), \mathit{spinP}, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.hopWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines hopWord.

**Definition 1.4 (fullHop).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{fullHop}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{ite}\left((j) + (1) < N, \mathrm{tensorOp}\left(\mathrm{hopWord}\left(j\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullHop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullHop.

**Definition 1.5 (fourHopWord).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathrm{Fin}\left(N\right),\; (\mathrm{fourHopWord}\left(N, j, k\right):\mathrm{Local}\left(\right)) = \mathrm{ite}\left((\mathrm{val}\left(k\right)) + (1) = j, \mathit{spinP}, \mathrm{ite}\left(\mathrm{val}\left(k\right) = j, \mathrm{adjoint}\left(\mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right)\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (1), \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (2), \mathrm{adjoint}\left(\mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right)\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (3), \mathrm{Matrixsingle}\left(\mathit{false}, \mathit{true}, (1:\mathit{Complex})\right), \mathrm{ite}\left(\mathrm{val}\left(k\right) = (j) + (4), \mathit{spinP}, 1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fourHopWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fourHopWord.

**Definition 1.6 (fullFourHop).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{fullFourHop}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{ite}\left((j) + (3) < N, \mathrm{tensorOp}\left(\mathrm{fourHopWord}\left(j\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullFourHop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullFourHop.

**Theorem 1.7 (hop dressed).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (1) < N) \Rightarrow (\mathrm{fullHop}\left(N, \mathrm{val}\left(j\right)\right) = (\mathrm{adjoint}\left(\mathrm{fullD}\left(j\right)\right)) \cdot (\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) + (1)\right):\mathrm{Fin}\left(N\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.hop_dressed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.8 (split at left).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (2) < N) \Rightarrow ((\mathrm{fullD}\left(j\right)) \cdot (\mathrm{fullSplit}\left(j\right)) = (\mathrm{adjoint}\left(\mathrm{fullHop}\left(N, (\mathrm{val}\left(j\right)) + (1)\right)\right)) \cdot (\mathrm{fullLeftP}\left(N, \mathrm{val}\left(j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_at_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.9 (split at right).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (2) < N) \Rightarrow ((\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) + (2)\right):\mathrm{Fin}\left(N\right))\right)) \cdot (\mathrm{fullSplit}\left(j\right)) = -\left((\mathrm{fullHop}\left(N, \mathrm{val}\left(j\right)\right)) \cdot (\mathrm{fullPAt}\left(N, (\mathrm{val}\left(j\right)) + (3)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_at_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.10 (split before).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (2) < N) \Rightarrow ((0 < \mathrm{val}\left(j\right)) \Rightarrow ((\mathrm{fullSplit}\left(j\right)) \cdot (\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) - (1)\right):\mathrm{Fin}\left(N\right))\right)) = \mathrm{adjoint}\left(\mathrm{fullFourHop}\left(N, (\mathrm{val}\left(j\right)) - (1)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.11 (split after).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (3) < N) \Rightarrow ((\mathrm{fullSplit}\left(j\right)) \cdot (\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) + (3)\right):\mathrm{Fin}\left(N\right))\right)) = -\mathrm{fullFourHop}\left(N, \mathrm{val}\left(j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_after` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.12 (fullHop PAt commute).**

$$\forall N \in \mathit{Nat},\; \forall h \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; (k \ne h) \Rightarrow ((k \ne (h) + (1)) \Rightarrow ((\mathrm{fullHop}\left(N, h\right)) \cdot (\mathrm{fullPAt}\left(N, k\right)) = (\mathrm{fullPAt}\left(N, k\right)) \cdot (\mathrm{fullHop}\left(N, h\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullHop_PAt_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Definition 1.13 (fullOccupationAt).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{fullOccupationAt}\left(N, j\right):\mathrm{FullOperator}\left(N\right)) = (1) - (\mathrm{fullPAt}\left(N, j\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullOccupationAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullOccupationAt.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fourHopWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullFourHop`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullHop`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullHop_PAt_commute`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullLeftP`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullOccupationAt`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.fullPAt`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.hopWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.hop_dressed`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_after`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_at_left`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_at_right`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.split_before`
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators](DressedOperators.md)
