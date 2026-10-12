# ForwardTraceYoung

## Abstract

ForwardTraceYoung

**Theorem 1.1 (Forward tracial Young inequality).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p: \mathbb{R},\ \forall M, W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(M)\land \operatorname{PosDef}(W)\land 0<p\land p\le 1\implies\ \operatorname{objective}(p, M, W)\le p\operatorname{tracePower}(\frac{1}{p}, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/ForwardTraceYoung.forward_trace_young` (`✓ std3`). ∎

*Citation.* Eric A. Carlen and Elliott H. Lieb (2008). *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II*. URL: <https://arxiv.org/abs/0710.4167v3>.

*Commentary.*

For all finite complex matrix dimensions, positive definite M and W and 0<p<=1, Re Tr(M W^(1-p))-(1-p) Re Tr W <= p Re Tr(M^(1/p)). For 0<p<1, apply the existing Schatten Holder supplier to M^(1/2) W^((1-p)/2) at exponents 2, 2/p and 2/(1-p). The public column-Gram identity and trace cyclicity give the mixed trace. Raising the bound to two and applying scalar weighted Young proves the result. The endpoint p=1 is calculated separately. Empty dimension and noncommuting M,W are retained.

**Theorem 1.2 (Explicit attained maximum).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p: \mathbb{R},\ \forall M: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(M)\land 0<p\land p\le 1\implies\ \exists W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(W)\land W=\operatorname{rpow}(M, \frac{1}{p})\land \operatorname{objective}(p, M, W)=p\operatorname{tracePower}(\frac{1}{p}, M)\land (\forall V: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(V)\implies\ \operatorname{objective}(p, M, V)\le \operatorname{objective}(p, M, W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/ForwardTraceYoung.maximum_and_attainment` (`✓ std3`). ∎

*Citation.* Eric A. Carlen and Elliott H. Lieb (2008). *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II*. URL: <https://arxiv.org/abs/0710.4167v3>.

*Commentary.*

The positive definite optimizer is exactly W0=M^(1/p), and the objective equals p Re Tr(M^(1/p)) there and dominates its value at every positive definite W. The equality uses same-matrix spectral power arithmetic. No positive definite optimizer is asserted for singular M. The mean-trace concavity proof interpolates the two actual endpoint optimizers; it needs joint concavity in the auxiliary variable, not a supremum of separately concave functions.

These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/ForwardTraceYoung.forward_trace_young`
- Truth anchor: `D5/S3/Quantum/Hiai/ForwardTraceYoung.maximum_and_attainment`
- Dependency: [D5/S3/Quantum/Hiai/InverseMeanVariational](InverseMeanVariational.md)
