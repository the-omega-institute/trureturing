# Supersymmetric fermion chain: CubicCompression

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (fullR).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; (\mathrm{fullR}\left(N, a, b, \mathit{cc}\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{ite}\left(0 < N, ((((\mathrm{smul}\left(\mathrm{asReal}\left((a) \cdot ((\mathit{cc})^{2})\right), \mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left(0\right):\mathrm{Fin}\left(N\right))\right)\right)\right)) - (\mathrm{smul}\left(\mathrm{asReal}\left(((a)^{2}) \cdot (\mathit{cc})\right), \mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left((N) - (1)\right):\mathrm{Fin}\left(N\right))\right)\right)\right))) + (\sum_{k\in\mathrm{Fin}\left((N) - (2)\right)}(\mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{periodThree}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (3)\right)) \cdot ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (2)\right))^{2})\right), (\mathrm{boolReindex}\left(\mathrm{localOp}\left((\mathrm{mk}\left(\mathrm{val}\left(k\right)\right):\mathrm{Fin}\left(N\right)), \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(k\right)) + (2)\right):\mathrm{Fin}\left(N\right))\right)\right))\right)))) - (\sum_{k\in\mathrm{Fin}\left((N) - (2)\right)}(\mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{periodThree}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (1)\right)) \cdot ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (2)\right))^{2})\right), (\mathrm{boolReindex}\left(\mathrm{localOp}\left((\mathrm{mk}\left((\mathrm{val}\left(k\right)) + (2)\right):\mathrm{Fin}\left(N\right)), \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left(\mathrm{val}\left(k\right)\right):\mathrm{Fin}\left(N\right))\right)\right))\right)))) + (\mathrm{smul}\left(\mathrm{asReal}\left(((a) \cdot (b)) \cdot (\mathit{cc})\right), \sum_{k\in\mathrm{Fin}\left((N) - (2)\right)}(\mathrm{fullSplit}\left((\mathrm{mk}\left(\mathrm{val}\left(k\right)\right):\mathrm{Fin}\left(N\right))\right))\right)), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fullR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullR.

**Definition 1.2 (HCBlock).**

$$\forall N \in \mathit{Nat},\; \forall A \in \mathrm{FullOperator}\left(N\right),\; (\mathrm{HCBlock}\left(N, A\right):\mathit{Prop}) = \left(\forall s \in \mathrm{Assignment}\left(N\right),\; \forall t \in \mathrm{Assignment}\left(N\right),\; (A\left(s, t\right) \ne 0) \Rightarrow ((\mathrm{Adm}\left(N, s\right)) \Leftrightarrow (\mathrm{Adm}\left(N, t\right)))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.HCBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines HCBlock.

**Theorem 1.3 (HCBlock fullNumber).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \mathrm{HCBlock}\left(\mathrm{boolReindex}\left(\mathrm{localOp}\left(i, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.HCBlock_fullNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Definition 1.4 (chainG).**

$$\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{chainG}\left(a, b, \mathit{cc}, j\right)\right) = \mathrm{periodThree}\left(a, b, \mathit{cc}, (j) + (1)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.chainG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines chainG.

**Definition 1.5 (blockR).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall k \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(k\right)) + (2) < N) \Rightarrow ((\mathrm{blockR}\left(N, a, b, \mathit{cc}, k\right):\mathrm{FullOperator}\left(N\right)) = (j:\mathrm{Fin}\left(N\right)\mapsto(((\mathrm{smul}\left((\mathrm{asReal}\left((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (2)\right)) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (1)\right))^{2})\right):\mathit{Complex}), (\mathrm{boolReindex}\left(\mathrm{localOp}\left(k, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left(j\right)\right))\right)) - (\mathrm{smul}\left((\mathrm{asReal}\left((\mathrm{chainG}\left(a, b, \mathit{cc}, \mathrm{val}\left(k\right)\right)) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (1)\right))^{2})\right):\mathit{Complex}), (\mathrm{boolReindex}\left(\mathrm{localOp}\left(j, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left(k\right)\right))\right))) + (\mathrm{smul}\left((\mathrm{asReal}\left(((a) \cdot (b)) \cdot (\mathit{cc})\right):\mathit{Complex}), \mathrm{fullSplit}\left(k\right)\right))))\left(\mathrm{mk}\left((\mathrm{val}\left(k\right)) + (2)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.blockR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines blockR.

**Definition 1.6 (blockDiagonal).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall k \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(k\right)) + (2) < N) \Rightarrow ((\mathrm{blockDiagonal}\left(N, a, b, \mathit{cc}, k\right):\mathrm{FullOperator}\left(N\right)) = (j:\mathrm{Fin}\left(N\right)\mapsto((\mathrm{smul}\left((\mathrm{asReal}\left(((2) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (2)\right))^{2})) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (1)\right))^{2})\right):\mathit{Complex}), (\mathrm{boolReindex}\left(\mathrm{localOp}\left(k, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{tensorOp}\left(\mathrm{neighbourPWord}\left(j\right)\right))\right)) - (\mathrm{smul}\left((\mathrm{asReal}\left(((2) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, \mathrm{val}\left(k\right)\right))^{2})) \cdot ((\mathrm{chainG}\left(a, b, \mathit{cc}, (\mathrm{val}\left(k\right)) + (1)\right))^{2})\right):\mathit{Complex}), (\mathrm{boolReindex}\left(\mathrm{localOp}\left(j, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right)) \cdot (\mathrm{tensorOp}\left(\mathrm{neighbourPWord}\left(k\right)\right))\right))))\left(\mathrm{mk}\left((\mathrm{val}\left(k\right)) + (2)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.blockDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines blockDiagonal.

**Definition 1.7 (hopCurrent).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; (\mathrm{hopCurrent}\left(N, a, b, \mathit{cc}, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{smul}\left((\mathrm{chainG}\left(a, b, \mathit{cc}, (j) + (2)\right):\mathit{Complex}), \mathrm{symOp}\left(\mathrm{fullHop}\left(N, j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.hopCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines hopCurrent.

**Definition 1.8 (fourCurrent).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; (\mathrm{fourCurrent}\left(N, a, b, \mathit{cc}, j\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{smul}\left((\mathrm{chainG}\left(a, b, \mathit{cc}, (j) + (3)\right):\mathit{Complex}), \mathrm{symOp}\left(\mathrm{fullFourHop}\left(N, j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fourCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fourCurrent.

**Definition 1.9 (bulkCurrent).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; (\mathrm{bulkCurrent}\left(N, a, b, \mathit{cc}, j\right):\mathrm{FullOperator}\left(N\right)) = (C\mapsto((x\mapsto(((((C\left((j) + (1)\right)) \cdot ((1) - (\mathrm{ite}\left(j = 0, 0, x\left((j) - (1)\right)\right)))) - ((C\left(j\right)) \cdot ((1) - (x\left((j) + (3)\right))))) + ((C\left((j) + (2)\right)) \cdot (x\left(j\right)))) - ((\mathrm{ite}\left(j = 0, 0, C\left((j) - (1)\right)\right)) \cdot (x\left((j) + (2)\right)))))\left(\mathrm{fullOccupationAt}\left(N\right)\right)))\left(\mathrm{hopCurrent}\left(N, a, b, \mathit{cc}\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.bulkCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines bulkCurrent.

**Definition 1.10 (fullBoundary).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; (\mathrm{fullBoundary}\left(N, a, b, \mathit{cc}\right):\mathrm{FullOperator}\left(N\right)) = \mathrm{ite}\left(0 < N, (\mathrm{smul}\left((\mathrm{asReal}\left((a) \cdot ((\mathit{cc})^{2})\right):\mathit{Complex}), \mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left(0\right):\mathrm{Fin}\left(N\right))\right)\right)\right)) - (\mathrm{smul}\left((\mathrm{asReal}\left(((a)^{2}) \cdot (\mathit{cc})\right):\mathit{Complex}), \mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left((N) - (1)\right):\mathrm{Fin}\left(N\right))\right)\right)\right)), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fullBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullBoundary.

**Definition 1.11 (w).**

$$\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{w}\left(a, b, \mathit{cc}, j\right)\right) = ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (j) + (1)\right))^{2}) \cdot ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (j) + (2)\right))^{2})$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.w` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines w.

**Definition 1.12 (occReal).**

$$\forall N \in \mathit{Nat},\; \forall s \in \mathrm{HardCore}\left(N\right),\; \forall j \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{occReal}\left(N, s, j\right)\right) = \mathrm{ite}\left(\mathrm{occupied}\left(\mathrm{val}\left(s\right), j\right), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.occReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines occReal.

**Definition 1.13 (diagonalCoefficient).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall s \in \mathrm{HardCore}\left(N\right),\; \mathrm{asReal}\left(\mathrm{diagonalCoefficient}\left(N, a, b, \mathit{cc}, s\right)\right) = ((((a)^{2}) \cdot ((\mathit{cc})^{2})) \cdot ((\mathrm{occReal}\left(s, (N) - (1)\right)) - (\mathrm{occReal}\left(s, 2\right)))) + (\sum_{i\in\mathrm{Finsetrange}\left((N) - (2)\right)}((((\mathrm{w}\left(a, b, \mathit{cc}, (i) + (1)\right)) \cdot (\mathrm{occReal}\left(s, (i) + (1)\right))) \cdot ((1) - (\mathrm{occReal}\left(s, (i) + (4)\right)))) - (((\mathrm{w}\left(a, b, \mathit{cc}, (i) + (3)\right)) \cdot (\mathrm{occReal}\left(s, (i) + (3)\right))) \cdot ((1) - (\mathrm{occReal}\left(s, i\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.diagonalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines diagonalCoefficient.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.HCBlock`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.HCBlock_fullNumber`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.blockDiagonal`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.blockR`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.bulkCurrent`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.chainG`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.diagonalCoefficient`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fourCurrent`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fullBoundary`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.fullR`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.hopCurrent`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.occReal`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.w`
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicProducts](CubicProducts.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel](HardCoreModel.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts](HoppingProducts.md)
