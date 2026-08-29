# Rational Contact Support

## Abstract

A Gram-kernel contact polynomial vanishes on the positive residual support of a rational unit-circle completion.

**Theorem 1.1 (Kernel contact polynomials vanish on residual support).**

$$\begin{aligned}\forall n: \mathbb{N}, p: \operatorname{Fin}(n) \to \operatorname{Polynomial}(\mathbb{C}),\\D: \operatorname{Polynomial}(\mathbb{C}), hD: \forall z \in Circle,\; \operatorname{eval}(D, z) \neq 0,\\\alpha: \mathbb{R}_{\geq0}, tau: \operatorname{FiniteMeasure}(Circle),\\\operatorname{let}(\psi: Circle \to \left(\operatorname{Fin}(n) \to \mathbb{C}\right), \forall z: Circle, i: \operatorname{Fin}(n), \psi(z)(i) = \frac{\operatorname{eval}(p(i), z)}{\operatorname{eval}(D, z)}\;muStar: \operatorname{FiniteMeasure}(Circle) = \alpha \cdot \operatorname{normalizedCircleHaar}() + tau\;G: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}), \forall i: \operatorname{Fin}(n), j: \operatorname{Fin}(n), G_{i,j} = \operatorname{integral}(muStar, (z: Circle \mapsto \psi(z)(i) {\psi(z)(j)}^{*}))\;B: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}), \forall i: \operatorname{Fin}(n), j: \operatorname{Fin}(n), B_{i,j} = \operatorname{integral}(\operatorname{normalizedCircleHaar}(), (z: Circle \mapsto \psi(z)(i) {\psi(z)(j)}^{*}))\;P: \left(\operatorname{Fin}(n) \to \mathbb{C}\right) \to \operatorname{Polynomial}(\mathbb{C}), \forall c: \operatorname{Fin}(n) \to \mathbb{C}, P(c) = \sum_{i\in \operatorname{Fin}(n)} {c(i)}^{*} \cdot p(i))\;\\\forall c: \operatorname{Fin}(n) \to \mathbb{C}, \operatorname{mulVec}(G - \alpha \cdot B, c) = 0 \Rightarrow\\\operatorname{support}(muStar - \alpha \cdot \operatorname{normalizedCircleHaar}()) \subseteq \left\{\operatorname{eval}(P(c), z) = 0 \mid z \in Circle\right\}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/RationalContactSupport.rational_contact_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement constructs every source object. Polynomial numerators and a denominator without unit-circle zeros determine the rational feature vector, while normalized Haar and an arbitrary finite positive residual determine the completion.

Both complex Gram matrices are displayed entrywise as integrals on the exact unit-circle carrier. The contact polynomial is the conjugate-coefficient combination of the supplied polynomial numerators.

The completion Gram matrix splits into its normalized-Haar floor and residual Gram matrix. A kernel vector therefore has zero residual quadratic form, hence its squared contact function vanishes almost everywhere.

Polynomial evaluation is continuous, so its zero set is closed. The almost-everywhere vanishing statement therefore places the full support of the completion residual inside that zero set.

## References

- Truth anchor: `D5/S3/Observer/Tomography/RationalContactSupport.rational_contact_support`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](../../Weil/Budget/FullCirclePrimalAttainment.md)
