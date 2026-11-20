# Cauchy estimates for the completed Mangoldt transform

## Abstract

Cauchy bounds after removing a zeta pole from the complete Mangoldt transform

**Definition 1.1 (The completed transform).**

$$\left(\forall s \in \mathbb{C},\; s \ne 1 \Rightarrow F\left(s\right) = T\left(s\right)\right) \land F\left(1\right) = 1 + \gamma - A'\left(1\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.completed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write T for the explicit complete Mangoldt transform, h for the entire normalized zeta function, and A for its logarithmic derivative. Away from 1, h(s)=(s−1)ζ(s). At 1 its value is 1 and its derivative is Euler's constant γ. Thus A(1)=γ. The completed transform is denoted by F.

**Theorem 1.2 (The unique fill and its single-pole Cauchy estimate).**

$$\left(\left(\left(\forall s \in \mathbb{C},\; s \ne 1 \Rightarrow F\left(s\right) = T\left(s\right)\right) \land F\left(1\right) = 1 + \gamma - A'\left(1\right)\right) \land \left(\left(\forall s \in \mathbb{C},\; \left(s \ne 0 \land \zeta\left(s\right) \ne 0\right) \Rightarrow \operatorname{AnalyticAt}\left(\mathbb{C}, F, s\right)\right) \land \left(\forall G \in (\mathbb{C} \to \mathbb{C}),\; \left(\operatorname{ContinuousAt}\left(G, 1\right) \land \left(\forall s \in \mathbb{C},\; s \ne 1 \Rightarrow G\left(s\right) = T\left(s\right)\right)\right) \Rightarrow G = F\right)\right)\right) \land \left(\forall p \in \mathbb{C},\; \forall z \in \mathbb{C},\; \forall r \in \mathbb{R},\; \left(0 < r \land \left(p \ne z \land \left(\zeta\left(z\right) = 0 \land \left(\forall w \in \mathbb{C},\; w \in \operatorname{closedBall}\left(p, r\right) \Rightarrow \left(w \ne 0 \land \left(\zeta\left(w\right) = 0 \Rightarrow w = z\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\forall n \in \mathbb{N},\; \left|\operatorname{iteratedDeriv}\left(n, F, p\right) - \frac{\operatorname{c}\left(z\right) \cdot \left(-1\right)^{n} \cdot \operatorname{factorial}\left(n\right)}{\left(p - z\right)^{n + 1}}\right| \le \frac{\operatorname{factorial}\left(n\right) \cdot B}{r^{n}}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.completed_disk_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original rational expression on the punctured neighborhood of 1 equals [1+γ−(A(s)−A(1))/(s−1)]/s. The term 1/(s−1) in the negative logarithmic derivative cancels the double pole after these fractions are combined. The divided difference extends analytically with value A′(1).

At every other nonzero point with ζ(s) nonzero, the ordinary quotient rules give analyticity. Equality to T off 1 preserves its half-plane integral and its punctured expansions at the zeta zeros. Continuity at 1 forces the same limit for any other function agreeing with T everywhere else.

Let p be the center and r the radius of the closed disk. The disk excludes 0 and every zeta zero other than the selected zero z. The center differs from z. The disk may contain 1 and may include z in its interior or on its boundary. Write c(z)=m/[z(1−z)] for the residue, where m is the order of ζ at z.

Subtract c(z)/(s−z) from F(s). At z assign to the difference the value of the analytic local Laurent remainder. This yields a single function analytic near every point of the disk, including 1. Its supremum on the circle bounds every Taylor coefficient at p by the Cauchy estimate. The derivative of the subtracted pole contributes the term c(z)(−1)ⁿn!/(p−z)ⁿ⁺¹.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.completed`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.completed_disk_cauchy`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent](CompleteMangoldtLaurent.md)
