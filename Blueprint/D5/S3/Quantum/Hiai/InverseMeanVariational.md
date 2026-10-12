# InverseMeanVariational

## Abstract

An inverse-mean trace variational formula in every finite complex dimension.

**Theorem 1.1 (Universal bound and explicit optimizer).**

$$\forall u: \operatorname{Level}(),\ d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ X, M: \operatorname{Matrix}(d, d, \mathbb{C}),\ r: \mathbb{R},\ \operatorname{PosDef}(X)\land \operatorname{PosDef}(M)\land 0<r\implies\ \exists Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{IsUnit}(Z)\land Z=\operatorname{inverse}(M)X\land \operatorname{objective}(r, X, M, Z)=\operatorname{tracePower}(r, X\operatorname{inverse}(M)X)\land(\forall W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{objective}(r, X, M, W)\le\operatorname{tracePower}(r, X\operatorname{inverse}(M)X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

Let X and M be positive definite square complex matrices and r > 0. Write R = X M inverse X. The objective at Z is twice the real trace of (Z* X squared Z) to exponent r/2, minus the real trace of (Z* M Z) to exponent r. Every spectral power uses the actual matrix continuous functional calculus. For every complex Z the objective is at most the trace of R to exponent r.

The invertible optimizer is M inverse X, which need not be selfadjoint. Both Z* M Z = R and X Z = R hold at this optimizer. The universal bound even allows singular Z, whereas attainment uses an invertible Z. No commutation assumption is made on X and M.

Factor X Z as U V, with U = X M to exponent minus one half and V = M to exponent one half times Z. Product Schatten Holder with exponents r, 2r, 2r and scalar Young give the bound. The row Gram matrix of U is R and the column Gram matrix of V is Z* M Z. Characteristic polynomial cyclicity identifies row and column spectral traces.

For the spectral sandwich geometric mean, put D = X to exponent minus one half times Y times X to exponent minus one half, and M = X to exponent one half times D to exponent theta times X to exponent one half. Direct inversion gives R = X to exponent one half times D to exponent minus theta times X to exponent one half. The same bound and optimizer therefore apply to the trace power of this negative-exponent mean. Identifying it with the original Hiai inner matrix Y geometric mean of exponent one plus theta with X requires an additional normalized-unitary identity.

This is a concrete specialization of Zhang's variational method, not a claim of mathematical originality. For Hiai's target set X = B to exponent p and M = X weighted geometric mean A to exponent p. Joint convexity still requires the Carlen-Lieb fixed-congruence trace convexity and the Hiai outer-power geometric-mean trace concavity. Neither curvature supplier is assumed by this theorem.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment`
- Dependency: [D5/S3/Quantum/Schatten/Holder](../Schatten/Holder.md)
