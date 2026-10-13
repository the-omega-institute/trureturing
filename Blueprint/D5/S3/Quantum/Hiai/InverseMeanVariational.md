# InverseMeanVariational

## Abstract

An inverse-mean trace variational formula in every finite complex dimension.

**Theorem 1.1 (Shared column Gram spectral trace).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ A: \operatorname{Matrix}(d, d, \mathbb{C}), r: \mathbb{R}, 0<r\implies\ \operatorname{rpow}(\operatorname{schattenNorm}(A, r), r)=\operatorname{tracePower}(\frac{r}{2}, \operatorname{adjoint}(A)A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_gram` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

For every finite complex square matrix A and r > 0, the Schatten r expression to exponent r equals tracePower (r/2) of A* A. This original proof is consumed by both the inverse-mean variational bound and reverse trace Young. It also includes empty dimension and singular A. The audit remains unfinished under #5214: no faithful enrolled template supplies the full matrix telescope with rigid universe reconstruction and sensitivity evidence.

**Theorem 1.2 (Shared row Gram spectral trace).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ A: \operatorname{Matrix}(d, d, \mathbb{C}), r: \mathbb{R}, 0<r\implies\ \operatorname{rpow}(\operatorname{schattenNorm}(A, r), r)=\operatorname{tracePower}(\frac{r}{2}, A\operatorname{adjoint}(A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_rowGram` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

The original row Gram proof is public at its source. The inverse-mean variational formula and the actual TILDE midpoint classification consume this same declaration directly. No proof is copied and no generated private declaration name is used. Its faithful full-telescope audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the observational-dependence proof's CFC.one_rpow rewrite did not match the concrete CFC.rpow identity-matrix target. The failed attempt is preserved outside accepted source and is not a validated registration.

**Theorem 1.3 (Shared two-factor Holder and Young bound).**

$$\forall u: \operatorname{Level}(),\ d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ U, V: \operatorname{Matrix}(d, d, \mathbb{C}),\ r: \mathbb{R},\ 0<r\implies\ 2\operatorname{rpow}(\operatorname{schattenNorm}(UV, r), r)-\operatorname{rpow}(\operatorname{schattenNorm}(V, 2r), 2r)\le\operatorname{rpow}(\operatorname{schattenNorm}(U, 2r), 2r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseMeanVariational.holder_two_young` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

The original two-factor Schatten Holder and scalar Young proof is public at its source for every r > 0. It is consumed directly by both variational formulas. These are existing mathematical suppliers, not additional originality claims. Its faithful full-telescope audit attempt remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the observational-dependence proof reaches a deterministic whnf timeout at 1000000 heartbeats, including after explicit CFC rewrites. The failed attempt is preserved outside accepted source and is not a validated registration.

**Theorem 1.4 (Universal bound and explicit optimizer).**

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

- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.holder_two_young`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_gram`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_rowGram`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment`
- Dependency: [D5/S3/Quantum/Schatten/Holder](../Schatten/Holder.md)
