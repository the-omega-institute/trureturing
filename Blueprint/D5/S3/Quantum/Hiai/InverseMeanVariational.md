# InverseMeanVariational

## Abstract

An inverse-mean trace variational formula in every finite complex dimension.

**Theorem 1.1 (Shared column Gram spectral trace).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ A: \operatorname{Matrix}(d, d, \mathbb{C}), r: \mathbb{R}, 0<r\implies\ \operatorname{rpow}(\operatorname{schattenNorm}(A, r), r)=\operatorname{tracePower}(\frac{r}{2}, \operatorname{adjoint}(A)A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_gram` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

For every finite complex square matrix A and r > 0, the Schatten r expression to exponent r equals tracePower (r/2) of A* A. This original proof is consumed by both the inverse-mean variational bound and reverse trace Young. It also includes empty dimension and singular A. The audit remains unfinished under #5214: no faithful enrolled template supplies the full matrix telescope with rigid universe reconstruction and sensitivity evidence.

**Theorem 1.2 (Universal bound and explicit optimizer).**

$$\forall u: \operatorname{Level}(),\ d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ X, M: \operatorname{Matrix}(d, d, \mathbb{C}),\ r: \mathbb{R},\ \operatorname{PosDef}(X)\land \operatorname{PosDef}(M)\land 0<r\implies\ \exists Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{IsUnit}(Z)\land Z=\operatorname{inverse}(M)X\land \operatorname{objective}(r, X, M, Z)=\operatorname{tracePower}(r, X\operatorname{inverse}(M)X)\land(\forall W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{objective}(r, X, M, W)\le\operatorname{tracePower}(r, X\operatorname{inverse}(M)X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

Let X and M be positive definite square complex matrices and r > 0. Write R = X M inverse X. The objective at Z is twice the real trace of (Z* X squared Z) to exponent r/2, minus the real trace of (Z* M Z) to exponent r. Every spectral power uses the actual matrix continuous functional calculus. For every complex Z the objective is at most the trace of R to exponent r.

The invertible optimizer is M inverse X, which need not be selfadjoint. Both Z* M Z = R and X Z = R hold at this optimizer. The universal bound even allows singular Z, whereas attainment uses an invertible Z. No commutation assumption is made on X and M.

Factor X Z as U V, with U = X M to exponent minus one half and V = M to exponent one half times Z. Product Schatten Holder with exponents r, 2r, 2r and scalar Young give the bound. The row Gram matrix of U is R and the column Gram matrix of V is Z* M Z. Characteristic polynomial cyclicity identifies row and column spectral traces.

For the spectral sandwich geometric mean, put D = X to exponent minus one half times Y times X to exponent minus one half, and M = X to exponent one half times D to exponent theta times X to exponent one half. Direct inversion gives R = X to exponent one half times D to exponent minus theta times X to exponent one half. The same bound and optimizer therefore apply to the trace power of this negative-exponent mean. Identifying it with the original Hiai inner matrix Y geometric mean of exponent one plus theta with X requires an additional normalized-unitary identity.

This is a concrete specialization of Zhang's variational method, not a claim of mathematical originality. For Hiai's target set X = B to exponent p and M = X weighted geometric mean A to exponent p. Joint convexity still requires the Carlen-Lieb fixed-congruence trace convexity and the Hiai outer-power geometric-mean trace concavity. Neither curvature supplier is assumed by this theorem.

**Theorem 1.3 (Support-sensitive PSD variational formula).**

$$\forall u: \operatorname{Level}(),\ d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ X, M: \operatorname{Matrix}(d, d, \mathbb{C}),\ r: \mathbb{R},\ \operatorname{PosSemidef}(X)\land \operatorname{PosSemidef}(M)\land (\forall v: d \to \mathbb{C}, \operatorname{mulVec}(M, v)=0\implies\operatorname{mulVec}(X, v)=0)\land 0<r\implies\ \exists Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ Z=\operatorname{rpow}(M, -1)X\land \operatorname{objective}(r, X, M, Z)=\operatorname{tracePower}(r, X\operatorname{rpow}(M, -1)X)\land(\forall W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{objective}(r, X, M, W)\le\operatorname{tracePower}(r, X\operatorname{rpow}(M, -1)X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.psd_variational_bound_and_attainment` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

For arbitrary finite complex positive semidefinite X and M, assume every vector in the kernel of M is also in the kernel of X. For every r > 0, the same inverse variational objective has the universal upper bound tracePower r of X M to exponent minus one X. The actual spectral generalized inverse vanishes on the kernel. The explicit optimizer M to exponent minus one times X attains the bound and may be singular. All dimensions, zero inputs and noncommuting matrices are included.

The proof derives support action from the kernel hypothesis, then factors X Z through the inverse square root and square root of M. It consumes the existing Schatten Holder and row/column Gram trace suppliers rather than repeating their proofs. The spectral support is the library's canonical cfc indicator of nonzero spectrum. At the generalized optimizer the two Gram matrices reduce to the same PSD sandwich; the PSD square-power identity gives equality.

This establishes a support-sensitive PSD supplier for the Hiai extension. It does not yet identify the original PSD geometric mean or prove its common epsilon I trace limit and joint convexity. Invertibility of the optimizer is not asserted. The four-slot escape audit remains unfinished under issue #5214: the full source bridge, variation and sensitivity compile, but native binding fails at contract.discovery rigid_universes. No declared_validated status is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_gram`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.psd_variational_bound_and_attainment`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment`
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Recovery/SpectralTransposeRecovery.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](../Schatten/Holder.md)
