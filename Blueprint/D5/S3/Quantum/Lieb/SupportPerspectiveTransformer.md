# SupportPerspectiveTransformer

## Abstract

Exact supported perspective transformer for positive finite matrix maps.

**Theorem 1.1 (Positive maps contract the supported perspective).**

$$\forall u: \operatorname{Level}(),\ n: \operatorname{Type}(u),\ [\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)], m: \operatorname{Type}(u),\ [\operatorname{Fintype}(m)], [\operatorname{DecidableEq}(m)], f: \mathbb{R} \to \mathbb{R},\ Phi: \operatorname{PositiveLinearMap}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{Matrix}(m, m, \mathbb{C})),\ A: \operatorname{Matrix}(n, n, \mathbb{C}),\ B: \operatorname{Matrix}(n, n, \mathbb{C}),\ \operatorname{OperatorConvexOnAll}(u, \operatorname{Ici}(0), f), \operatorname{ContinuousOn}(f, \operatorname{Ici}(0)), \operatorname{PSD}(A), \operatorname{PSD}(B), \operatorname{ker}(B)\subseteq \operatorname{ker}(A) \implies \operatorname{persp}(f, \operatorname{Phi}(A), \operatorname{Phi}(B))\le\operatorname{Phi}(\operatorname{persp}(f, A, B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/SupportPerspectiveTransformer.supportedPerspective_transformer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex matrix algebras with carriers in Type u, let Phi be any complex-linear positive map and A,B be PSD, with ker B contained in ker A. Let f be continuous on [0,infinity) and satisfy the actual OperatorConvexOnAll.{u} supplier there. Write W_B=spectralInverseSqrt(B), the existing spectral inverse square root which is zero on the kernel. The expression persp(f,A,B) denotes sqrt(B) cfc(f,W_B A W_B) sqrt(B). The conclusion below assumes no complete positivity, unitality or trace preservation of Phi, faithfulness, commutation, or restriction on f(0). Empty carriers and Phi(B)=0 are included.

The mixed products sqrt(B) W_B and W_B sqrt(B) equal the existing spectralSupport(B), by finite spectral multiplication. The complement I-support(B) maps into ker B, so the exact kernel hypothesis gives both support identities for A and the reconstruction sqrt(B) (W_B A W_B) sqrt(B)=A. Apply the previously authored ambient positive-unital Jensen to X=W_B A W_B. Its scalar correction localizes away on the output support under CFC, then vanishes after congruence by sqrt(Phi(B)). The remaining normalized image reduces to Phi(persp(f,A,B)) using signed sandwich support. Thus a negative value of f(0) does not require a positivity claim for f(X).

The analytic power supplier is the existing attributed Physlib transplant by Kei Tsukamoto, Kento Mori and Hayata Yamasaki, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. PowerConvexity.condIciAll_rpow supplies all-Hilbert operator convexity of x^(1+h) on [0,infinity) for 0<h<=1. For these h the affine correction g_h(x)=(x^(1+h)-x)/h is operator convex on that interval: subtract the affine operator argument in the power inequality and multiply by the positive scalar 1/h.

UniformPowerSlope.rpow_slope_tendsto_uniformly reuses Alex Meiburg's estimate from Physlib QuantumInfo/Entropy/Relative.lean at the same revision, under Apache-2.0. It supplies uniform convergence of g_h(x) to x log x on every [0,K], including x=0. For a positive bounded operator S its entire real spectrum lies in [0,norm(S)]. Mathlib.tendsto_cfc_fun therefore passes this uniform convergence through CFC. Apply it to A, B and (1-t)A+tB; closed operator order passes their Jensen inequality to the limit. This establishes the actual OperatorConvexOnAll condition for x log x in every original Hilbert universe. The limit is cfc(x log x,S), with value zero at zero. Spectra accumulating at zero are allowed; no bounded CFC logarithm or factorization as S times log(S) is used.

For the concrete entropy application let a,b be arbitrary finite decidable types in the same universe, including empty types. Let Phi be positive and complex-linear, and require trace(Phi(Z))=trace(Z) for every matrix Z. For PSD A,B assume exactly ker B contained in ker A. Set f(x)=x log x, using Real.continuous_mul_log for continuity and the preceding all-Hilbert limit for operator convexity. The transformer gives persp(f,Phi(A),Phi(B)) <= Phi(persp(f,A,B)). Apply the positive trace map, substitute the literal trace preservation law, and take real parts. The result is Re trace(persp(f,Phi(A),Phi(B))) <= Re trace(persp(f,A,B)). No complete positivity, unitality, normalization, invertibility or commutation is required. This is the supported maximal, or Belavkin-Staszewski-type, entropy perspective. It is not an identification with Umegaki entropy, and the finite matrix conclusion is not an infinite-dimensional quantum data-processing theorem.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransformer.supportedPerspective_transformer`
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransport](SupportPerspectiveTransport.md)
