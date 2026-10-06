# Supersymmetric fermion chain: HardCoreCompression

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Theorem 1.1 (fullD hardCore iff).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \forall s \in \mathrm{Assignment}\left(N\right),\; \forall t \in \mathrm{Assignment}\left(N\right),\; (\mathrm{fullD}\left(i, s, t\right) \ne 0) \Rightarrow ((\mathrm{Adm}\left(N, s\right)) \Leftrightarrow (\mathrm{Adm}\left(N, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.fullD_hardCore_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.2 (restrictOp fullD).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \mathrm{submatrix}\left(\mathrm{fullD}\left(i\right), \mathrm{Subtypeval}\left(\right), \mathrm{Subtypeval}\left(\right)\right) = \mathrm{annihilationAt}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.restrictOp_fullD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

**Theorem 1.3 (restrictOp fullNumber).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; \mathrm{submatrix}\left(\mathrm{boolReindex}\left(\mathrm{localOp}\left(i, \mathrm{finTwoReindex}\left(\mathrm{visibleProjector}\left(\right)\right)\right)\right), \mathrm{Subtypeval}\left(\right), \mathrm{Subtypeval}\left(\right)\right) = \mathrm{number}\left((\mathrm{val}\left(i\right)) + (1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.restrictOp_fullNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.fullD_hardCore_iff`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.restrictOp_fullD`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.restrictOp_fullNumber`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel](HardCoreModel.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts](SuperchargeProducts.md)
