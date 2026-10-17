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

The three mathematical modules have passed explicit targeted Lean builds. Their joint scoped report records only propext, Quot.sound and Classical.choice. Information-audit binding is assessed separately and is not claimed complete here. The finite-effect to rectangular-isometry to endomorphism contraction bridge remains an explicit authored dependency; it is not an assumed new axiom. The analytic supplier is the existing attributed Physlib transplant by Kei Tsukamoto, Kento Mori and Hayata Yamasaki, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. No official acceptance or mathematical novelty is asserted by this document.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransformer.supportedPerspective_transformer`
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransport](SupportPerspectiveTransport.md)
