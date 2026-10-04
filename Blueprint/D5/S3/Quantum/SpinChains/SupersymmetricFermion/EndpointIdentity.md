# Supersymmetric fermion chain: EndpointIdentity

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (EndpointIdentity).**

$$(\mathrm{EndpointIdentity}\left(\right):\mathit{Prop}) = \left(\forall n \in \mathit{Nat},\; (1 \le n) \Rightarrow (\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; (q\mapsto((r\mapsto((((q) \cdot (r)) + ((r) \cdot (q))) + (\mathrm{adjoint}\left(((q) \cdot (r)) + ((r) \cdot (q))\right)) = \mathrm{smul}\left(\mathrm{asReal}\left((2) \cdot ((b)^{2})\right), (\mathrm{smul}\left(\mathrm{asReal}\left((\mathit{cc})^{2}\right), \mathrm{number}\left(1\right)\right)) - (\mathrm{smul}\left(\mathrm{asReal}\left((a)^{2}\right), \mathrm{number}\left((3) \cdot (n)\right)\right))\right)))\left(\mathrm{Rmat}\left((3) \cdot (n), a, b, \mathit{cc}\right)\right)))\left(\mathrm{Qmat}\left((3) \cdot (n), \mathrm{periodThree}\left(a, b, \mathit{cc}\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity.EndpointIdentity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symmetrized anticommutator of Q and R is 2b²(c² n₁−a² nN) for every length N=3n and all real a,b,c. This operator equation imposes no nonzero-coupling hypothesis.

**Theorem 1.2 (endpoint identity).**

$$\forall n \in \mathit{Nat},\; (1 \le n) \Rightarrow (\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; (q\mapsto((r\mapsto((((q) \cdot (r)) + ((r) \cdot (q))) + (\mathrm{adjoint}\left(((q) \cdot (r)) + ((r) \cdot (q))\right)) = \mathrm{smul}\left(\mathrm{asReal}\left((2) \cdot ((b)^{2})\right), (\mathrm{smul}\left(\mathrm{asReal}\left((\mathit{cc})^{2}\right), \mathrm{number}\left(1\right)\right)) - (\mathrm{smul}\left(\mathrm{asReal}\left((a)^{2}\right), \mathrm{number}\left((3) \cdot (n)\right)\right))\right)))\left(\mathrm{Rmat}\left((3) \cdot (n), a, b, \mathit{cc}\right)\right)))\left(\mathrm{Qmat}\left((3) \cdot (n), \mathrm{periodThree}\left(a, b, \mathit{cc}\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity.endpoint_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local Jordan-Wigner products cancel the bulk hopping and four-site currents. Compression to the hard-core space and the remaining diagonal telescoping give the exact boundary occupation operator. The identity holds for all real period-three couplings, including b=0.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity.EndpointIdentity`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity.endpoint_identity`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion](../../Dynamics/PronkoFredkinAntiAdjointExpansion.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity](FullEndpointIdentity.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression](HardCoreCompression.md)
