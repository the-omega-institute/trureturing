# Bilateral Fibonacci Lift Classification

## Abstract

The bilateral Fibonacci lift is the unique two-line golden eigenlift up to independent component scales.

**Theorem 1.1 (The bilateral lift is two-dimensional and componentwise unique).**

$$\begin{gathered}\operatorname{finrank}\left(\mathbb{R}, \operatorname{Sol}\left(fibRec\right)\right) = 2 \land\\{}\operatorname{Sol}\left(fibRec\right) = \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right) \land\\{}\varphi = \frac{1+\sqrt{5}}{2} \land\psi = -\operatorname{inv}\left(\varphi\right) \land\\{}S\left(e_{\varphi}\right) = \varphi \cdot e_{\varphi} \land S\left(e_{\psi}\right) = \psi \cdot e_{\psi} \land\\{}\operatorname{inv}\left(\sqrt{5}\right) \neq 0 \land -\operatorname{inv}\left(\sqrt{5}\right) \neq 0 \land\\{}(\forall k: \mathbb{N}, F\left(k\right) = \frac{e_{\varphi}\left(k\right) - e_{\psi}\left(k\right)}{\sqrt{5}}) \land\\{}F \in \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right) \land (\forall u: \operatorname{Seq}\left(\mathbb{R}\right), u \in \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right) \Rightarrow S\left(u\right) \in \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right)) \land\\{}(\forall W: \operatorname{Submodule}\left(\mathbb{R}, \operatorname{Seq}\left(\mathbb{R}\right)\right), F \in W \land (\forall u: \operatorname{Seq}\left(\mathbb{R}\right), u \in W \Rightarrow S\left(u\right) \in W) \Rightarrow \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right) \subseteq W) \land\\{}\operatorname{finrank}\left(\mathbb{R}, \operatorname{span}\left(\mathbb{R}, e_{\varphi}, e_{\psi}\right)\right) = 2 \land\\{}(\forall u, v: \operatorname{Seq}\left(\mathbb{R}\right), S\left(u\right) = \varphi \cdot u \land S\left(v\right) = \psi \cdot v \Rightarrow \exists! c: \mathbb{R} \times \mathbb{R}, u = c_1 \cdot e_{\varphi} \land v = c_2 \cdot e_{\psi}) \land\\{}(\forall k: \mathbb{N}, (e_{\varphi}\left(k\right), e_{\psi}\left(k\right)) = (\varphi^{k + 1}, \psi^{k + 1})) \land\\{}\forall k: \mathbb{N}, F\left(k + 1\right) - \varphi F\left(k\right) = \psi^{k + 1}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftClassification.bilateral_lift_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement retains the solution-space dimension, golden scalar identities, shift eigenlaws, nonzero Binet coefficients, least invariant carrier, its dimension, unique component scalars, canonical weight pair, and exact contracting residual.

## References

- Truth anchor: `D5/S1/Recurrence/BilateralLiftClassification.bilateral_lift_classification`
- Dependency: [D5/S1/Recurrence/BilateralLiftUniqueness](BilateralLiftUniqueness.md)
