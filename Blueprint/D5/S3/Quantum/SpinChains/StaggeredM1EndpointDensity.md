# Supersymmetric fermion chain: StaggeredM1EndpointDensity

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (claim).**

$$(\mathrm{claim}\left(\right):\mathit{Prop}) = \left(\forall n \in \mathit{Nat},\; (1 \le n) \Rightarrow (\forall y \in \mathit{Real},\; (y \ne 0) \Rightarrow (\forall psi \in \mathrm{HardCoreSpace}\left((3) \cdot (n)\right),\; (\mathit{psi} \ne 0) \Rightarrow ((\mathrm{H}\left((3) \cdot (n), \mathrm{stagII}\left(y\right), \mathit{psi}\right) = 0) \Rightarrow (\mathrm{density}\left((3) \cdot (n), \mathit{psi}\right) = \mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{inv}\left(y\right))^{2}\right), \mathrm{density}\left(1, \mathit{psi}\right)\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.claim` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 3.2.3, printed page 13: “As similar pattern is found by probing if a particle is present on the last site. The data is consistent with ρ_n^{(N)}(y) = y^{−2} ρ_n^{(1)}(y) for finite n ≤ 8. We conjecture this to hold for arbitrary system sizes.” Here N = 3n with n ≥ 1, y is real and nonzero, and density(j,psi) is the normalized occupation expectation at the one-based site j. The claim quantifies over every nonzero zero-energy state; it contains the source ground-state assertion without assuming existence or uniqueness.

**Theorem 1.2 (result).**

$$\forall n \in \mathit{Nat},\; (1 \le n) \Rightarrow (\forall y \in \mathit{Real},\; (y \ne 0) \Rightarrow (\forall psi \in \mathrm{HardCoreSpace}\left((3) \cdot (n)\right),\; (\mathit{psi} \ne 0) \Rightarrow ((\mathrm{H}\left((3) \cdot (n), \mathrm{stagII}\left(y\right), \mathit{psi}\right) = 0) \Rightarrow (\mathrm{density}\left((3) \cdot (n), \mathit{psi}\right) = \mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{inv}\left(y\right))^{2}\right), \mathrm{density}\left(1, \mathit{psi}\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/beccaria-hagendorf-2012-staggered-m1-endpoint-density` (proved) by `D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"beccaria-hagendorf-2012-staggered-m1-endpoint-density","declaration_gid":"D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The period-three identity for R has expectation zero in every zero-energy state, since Q and its Hilbert adjoint both annihilate that state. With couplings (y,y,1) the remaining boundary term gives density(N,psi)=y⁻² density(1,psi). The argument holds for every nonzero zero-energy state and does not prove its existence or uniqueness.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result`
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity](SupersymmetricFermion/EndpointIdentity.md)
