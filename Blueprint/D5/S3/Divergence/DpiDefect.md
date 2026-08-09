# Nonnegativity of the Classical Data-Processing Defect

## Abstract

Finite classical channels have a nonnegative Kullback-Leibler data-processing defect.

**Theorem 1.1 (The classical data-processing defect is nonnegative).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0< p(x)) \land \sum_{x}p(x)= 1) \Rightarrow\\((\forall x, 0< q(x)) \land \sum_{x}q(x)= 1) \Rightarrow\\((\forall x, y, 0< W(x, y)) \land (\forall x, \sum_{y}W(x, y)= 1)) \Rightarrow\\D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq)\geq 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/DpiDefect.dpi_defect_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite alphabets, with X nonempty. Let p and q be strictly positive normalized real mass functions, and let W be a strictly positive row-stochastic channel. The divergence D and the output masses Wp and Wq are exactly the finite real-valued objects established by the preceding declarations.

The chain identity rewrites the displayed defect as a finite sum over outputs. Each summand is the positive output mass (Wp)(y) multiplied by the divergence between the p- and q-posteriors at y. Those posteriors are normalized positive mass functions, so the established finite Gibbs inequality makes every posterior divergence nonnegative. Finite summation therefore proves the claim.

This declaration records only nonnegativity. The existing zero-defect theorem supplies the separate posterior-equality characterization; no equality argument is repeated here.

## References

- Truth anchor: `D5/S3/Divergence/DpiDefect.dpi_defect_nonneg`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
