# ReverseTraceYoung

## Abstract

Reverse trace Young and its attained minimum for noncommuting positive definite matrices.

**Theorem 1.1 (Unconditional reverse trace Young).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ M, W: \operatorname{Matrix}(d, d, \mathbb{C}), a: \mathbb{R},\ \operatorname{PosDef}(M)\land \operatorname{PosDef}(W)\land 1\le a\implies\ a\operatorname{tracePower}(\frac{1}{a}, M)\le\operatorname{objective}(a, M, W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/ReverseTraceYoung.reverse_trace_young` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

For positive definite complex M and W and every real a >= 1, a times Re Tr(M to exponent 1/a) is at most Re Tr(M W to exponent 1-a) plus (a-1) Re Tr W. Powers are spectral continuous functional calculus. No commutation, nonempty dimension, or strictly positive trace is assumed.

For a > 1 factor M to exponent one half as U V, with U = M to exponent one half times W to exponent (1-a)/2 and V = W to exponent (a-1)/2. Apply general Schatten Holder at r=2/a, p=2, q=2/(a-1), allowing positive exponents below one. The original norm_rpow_gram API identifies the three spectral traces. Trace cyclicity gives the mixed trace from U* U; it is nonnegative without asserting that M W to exponent 1-a is selfadjoint. Weighted AM-GM with weights 1/a and (a-1)/a finishes the proof. At a=1 split first: the identity avoids division by a-1.

This is a classical tracial Young derivation using the attributed physlib Schatten Holder supplier, Apache-2.0. It supplies the variational step in the Carlen-Lieb path; it does not establish operator convexity or solve Hiai Problem 5.18.

**Theorem 1.2 (Explicit attained minimum).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ M: \operatorname{Matrix}(d, d, \mathbb{C}), a: \mathbb{R},\ \operatorname{PosDef}(M)\land 1\le a\implies\ \exists W0: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(W0)\land W0=\operatorname{rpow}(M, \frac{1}{a})\land \operatorname{objective}(a, M, W0)=a\operatorname{tracePower}(\frac{1}{a}, M)\land\ (\forall W: \operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{PosDef}(W)\implies \operatorname{objective}(a, M, W0)\le\operatorname{objective}(a, M, W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/ReverseTraceYoung.minimum_and_attainment` (`✓ std3`). ∎

*Citation.* Haonan Zhang (2020). *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*. URL: <https://arxiv.org/abs/1811.01205v2>.

*Commentary.*

The positive definite W0 = M to exponent 1/a attains objective a M W0 = a tracePower (1/a) M and has objective at most that of every positive definite W. The same-base CFC power composition proves M W0 to exponent 1-a = W0. At a=1 all positive definite W attain equality. No attained positive definite optimizer is asserted for singular M.

CarlenLiebConvexity consumes this exact optimizer at both endpoints, together with the dimension-independent power convexity on the full positive cone, public Jensen perspective and its trace transport. The positive definite mixture of the endpoint optimizers supplies the convexity comparison. Hiai still needs mean-trace concavity, inverse-mean identification, full parameter assembly and its support-constrained semidefinite extension.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/ReverseTraceYoung.minimum_and_attainment`
- Truth anchor: `D5/S3/Quantum/Hiai/ReverseTraceYoung.reverse_trace_young`
- Dependency: [D5/S3/Quantum/Hiai/InverseMeanVariational](InverseMeanVariational.md)
