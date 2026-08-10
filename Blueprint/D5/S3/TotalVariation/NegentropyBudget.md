# The Finite Negentropy Budget

## Abstract

Distance from the uniform law is controlled by the finite Shannon entropy deficit in nats.

**Theorem 1.1 (Total variation from uniform is bounded by the entropy deficit).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall r: \iota\to \mathbb{R},\\((\forall i, 0\le r(i)) \land \sum_{i}r(i)=1) \Rightarrow\\2 \operatorname{TV}(r, (i\mapsto \operatorname{card}(\iota)^{-1})) \le \sqrt{2 (\log(\operatorname{card}(\iota))-H(r))}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/NegentropyBudget.total_variation_uniform_le_sqrt_entropy_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be a nonnegative normalized mass function on a nonempty finite alphabet and let u be the uniform mass. The theorem proves 2 TV(r,u) <= sqrt(2(log |iota| - H(r))). Total variation uses the repository's probability normalization, and the logarithm and Shannon entropy are both measured in nats.

The proof is an assembly of previously frozen results. Pinsker gives 2 TV(r,u)^2 <= D(r||u), the entropy-divergence identity rewrites the right side as log |iota| - H(r), and total-variation nonnegativity allows mathlib's square-root order lemma to convert the squared bound to the displayed form. No analytic inequality is re-proved here.

The statement is deliberately about a finite probability mass r. The repository has no state-dependent quantity muStar and no theorem identifying finite Shannon entropy of a supplied spectrum with a density matrix's von Neumann entropy. The observer perturbation seminorm concerns permutation update defects and is not such a quantity. Accordingly, this theorem does not claim a muStar bound.

No forgetting monotonicity, endpoint saturation, fourth-order qubit expansion, pure-end rank estimate, or numerical certificate is asserted. The existing total-variation data-processing theorem applies a channel to both reference masses; it does not preserve this uniform reference without an additional uniform-preservation hypothesis.

## References

- Truth anchor: `D5/S3/TotalVariation/NegentropyBudget.total_variation_uniform_le_sqrt_entropy_deficit`
- Dependency: [D5/S3/Entropy/EntropyDivergenceIdentity](../Entropy/EntropyDivergenceIdentity.md)
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
