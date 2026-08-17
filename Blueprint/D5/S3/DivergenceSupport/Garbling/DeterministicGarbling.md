# Kullback-Leibler Loss under Deterministic Forgetting

## Abstract

Deterministic finite forgetting has nonnegative Kullback-Leibler information loss.

**Theorem 1.1 (Deterministic forgetting has nonnegative KL loss).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, f: X\to Y,\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\(\forall x: X, q(x)=0 \Rightarrow p(x)=0) \Rightarrow\\D(p\Vert\Vert q) - D(f_{*}p\Vert\Vert f_{*}q) \ge 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/Garbling/DeterministicGarbling.deterministic_forgetting_kl_loss_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, let p and q be nonnegative normalized mass functions on X, and assume discrete absolute continuity: every zero of q is also a zero of p. A function f : X -> Y forgets distinctions inside its fibers; f_*p and f_*q are the resulting pushforward laws.

The graph of f defines a zero-one channel with nonnegative entries and unit row sums. Applying the frozen general-support data-processing defect theorem to that channel proves the displayed inequality. The only local argument identifies its channel outputs with the deterministic pushforwards.

## References

- Truth anchor: `D5/S3/DivergenceSupport/Garbling/DeterministicGarbling.deterministic_forgetting_kl_loss_nonnegative`
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDefect](../ZeroSupportDefect.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
