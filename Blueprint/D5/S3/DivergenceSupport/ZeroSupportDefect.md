# The Data-Processing Defect on General Support

## Abstract

Nonnegativity of the finite classical data-processing defect on general support.

**Theorem 1.1 (The forgetting quantity stays nonnegative on general support).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\(\forall x: X, q(x)=0 \Rightarrow p(x)=0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq)\ge 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ZeroSupportDefect.dpi_defect_nonneg_zero_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, let p and q be nonnegative normalized masses with discrete absolute continuity, and let the channel W be nonnegative with unit row sums. The displayed D and channel output are the definitions imported from the frozen ClassicalDPI module, total at zero under the stated conventions. The difference on the left is the forgetting quantity: the divergence lost by passing both masses through the channel.

The proof composes two frozen results. The general-support chain identity classical_dpi_identity_zero_support rewrites the difference as the output-weighted sum of posterior divergences, and the finite Gibbs inequality kl_divergence_nonneg makes each summand nonnegative once absolute continuity is transported to the posteriors. No strict positivity is assumed anywhere; zero-mass branches contribute zero by convention and the inequality survives at the boundary.

## References

- Truth anchor: `D5/S3/DivergenceSupport/ZeroSupportDefect.dpi_defect_nonneg_zero_support`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDPI](ZeroSupportDPI.md)
