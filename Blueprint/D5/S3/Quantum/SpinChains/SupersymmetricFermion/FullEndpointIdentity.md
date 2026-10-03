# Supersymmetric fermion chain: full endpoint identity

## Abstract

The full occupation-space calculation of the period-three boundary sum rule.

Nat, Real and Complex denote the natural, real and complex numbers. Fin(N) denotes the finite index type; val is its natural value. mk displays a Fin value with its proof component suppressed. All finite-type sums range over the displayed type; subtraction in Nat is truncated at zero. mod is natural remainder, smul is scalar multiplication and asReal retains the real scalar annotation. fullQ, fullR, chainG, fullPAt and blockDiagonal are the chain definitions. symOp(A)=A+adjoint(A), with the matrix conjugate transpose. finTwoReindex and boolReindex transport matrices in opposite directions through finTwoEquiv : Fin 2 ≃ Bool, applied pointwise to occupation configurations. antiAd is the existing operator antiAd(A,B)=AB+BA. These coordinate notations do not define new Lean operators.

**Theorem 1.1 (Full-space period-three identity).**

$$\forall N \in \mathit{Nat},\; (3 \le N) \Rightarrow ((\mathrm{mod}\left(N, 3\right) = 0) \Rightarrow (\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \mathrm{symOp}\left(\mathrm{boolReindex}\left(\mathrm{antiAd}\left(\mathrm{finTwoReindex}\left(\mathrm{fullQ}\left(((i:\mathrm{Fin}\left(N\right))\mapsto\mathrm{chainG}\left(a, b, \mathit{cc}, \mathrm{val}\left(i\right)\right))\right)\right), \mathrm{finTwoReindex}\left(\mathrm{fullR}\left(N, a, b, \mathit{cc}\right)\right)\right)\right)\right) = (\mathrm{smul}\left((\mathrm{asReal}\left((((2) \cdot ((a)^{2})) \cdot ((\mathit{cc})^{2}):\mathit{Real})\right):\mathit{Complex}), (\mathrm{fullPAt}\left(N, 1\right)) - (\mathrm{fullPAt}\left(N, (N) - (2)\right))\right)) + (\sum_{k\in\mathrm{Fin}\left((N) - (2)\right)}(\mathrm{blockDiagonal}\left(a, b, \mathit{cc}, (\mathrm{mk}\left(\mathrm{val}\left(k\right)\right):\mathrm{Fin}\left(N\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity.full_symmetrized_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N at least three and divisible by three, and all real a,b,c, localization of the cubic products and cancellation of the hopping currents leave precisely the displayed diagonal terms. The statement is an identity on the full Boolean occupation space; the hard-core transport and occupation telescope give the endpoint identity in the next module.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity.full_symmetrized_diagonal`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion](../../Dynamics/PronkoFredkinAntiAdjointExpansion.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression](CubicCompression.md)
