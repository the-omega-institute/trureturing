# Schwartz Cutoff Graph Convergence

## Abstract

Scaled compact cutoffs converge in the actual Schwartz differential graph norm.

**Theorem 1.1 (Compact tests approximate the vector and the full differential sum).**

$$\forall d \in Nat, a \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, b \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, f \in \operatorname{Schwartz}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right), chi \in \operatorname{Schwartz}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{R}\right),\; \left(\operatorname{HasCompactSupport}\left(chi\right) \land \left(chi\left(0\right) = 1 \land \left(\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right),\; \Vert chi\left(x\right) \Vert \le 1\right)\right)\right) \Rightarrow \left(\exists psi \in Nat \to \operatorname{Schwartz}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \left(\forall n \in Nat, x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right),\; psi\left(n\right)\left(x\right) = chi\left(\frac{x}{n + 1}\right) \cdot f\left(x\right)\right) \land \left(\left(\forall n \in Nat,\; \operatorname{HasCompactSupport}\left(psi\left(n\right)\right)\right) \land \left(\operatorname{TendstoL2}\left(\left(\operatorname{J}\left(psi\left(n\right)\right)\right)_{n \in Nat}, \operatorname{J}\left(f\right)\right) \land \operatorname{TendstoL2}\left(\left(\operatorname{J}\left(\operatorname{H}\left(a, b, psi\left(n\right)\right)\right)\right)_{n \in Nat}, \operatorname{J}\left(\operatorname{H}\left(a, b, f\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/SchwartzCutoffGraph.scaled_cutoff_graph` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors; Anthropic PBC (2026). *Scaled cutoff and derivative approximation argument*. URL: <https://github.com/the-omega-institute/trureturing/blob/43cdec3b5cfa62c75aac586f4edc2066e2cac4ca/D5/S3/Weil/ZetaPntBase/Sobolev.lean>.

*Commentary.*

For every natural dimension d, arbitrary real coordinate coefficients a and b, and complex Schwartz function f, let chi be a real Schwartz function with compact support, value one at zero and absolute value at most one everywhere. The functions psi of n equal chi applied to x divided by n plus one, times f of x. They are smooth and compactly supported. Their actual complex Lebesgue L2 vectors converge to f, and their differential images converge to the image of f.

The differential is the finite sum of minus a of j times the second coordinate derivative, plus b of j times the coordinate squared times the function. The physical coefficients are included. Dimension zero uses the empty sum.

The product rule gives both first derivative terms and the second cutoff derivative. Scaling bounds these terms by inverse powers of the radius. Squared dominated convergence gives the actual L2 limits. The cited W21 argument is one-dimensional and uses an L1 norm; the present statement extends its method.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/SchwartzCutoffGraph.scaled_cutoff_graph`
