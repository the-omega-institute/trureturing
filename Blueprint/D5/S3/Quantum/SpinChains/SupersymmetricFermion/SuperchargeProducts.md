# Supersymmetric fermion chain: SuperchargeProducts

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (fullQ).**

$$\forall N \in \mathit{Nat},\; \forall coupling \in \mathrm{Fin}\left(N\right) \to \mathit{Real},\; (\mathrm{fullQ}\left(N, \mathit{coupling}\right):\mathrm{FullOperator}\left(N\right)) = \sum_{i\in\mathrm{Fin}\left(N\right)}(\mathrm{smul}\left((\mathit{coupling}\left(i\right):\mathit{Complex}), \mathrm{fullD}\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines fullQ.

**Theorem 1.2 (fullD support).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall s \in \mathrm{Assignment}\left(N\right),\; \forall t \in \mathrm{Assignment}\left(N\right),\; (\mathrm{fullD}\left(i, s, t\right) \ne 0) \Rightarrow ((t\left(i\right) = \mathit{true}) \land (s = \mathrm{Functionupdate}\left(t, i, \mathit{false}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullD_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.3 (fullSplit eq dressed product).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; ((\mathrm{val}\left(j\right)) + (2) < N) \Rightarrow (\mathrm{fullSplit}\left(j\right) = ((\mathrm{adjoint}\left(\mathrm{fullD}\left(j\right)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) + (2)\right):\mathrm{Fin}\left(N\right))\right)\right))) \cdot (\mathrm{fullD}\left((\mathrm{mk}\left((\mathrm{val}\left(j\right)) + (1)\right):\mathrm{Fin}\left(N\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullSplit_eq_dressed_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullD_support`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullQ`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts.fullSplit_eq_dressed_product`
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators](DressedOperators.md)
