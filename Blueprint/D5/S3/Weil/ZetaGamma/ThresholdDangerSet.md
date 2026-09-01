# Threshold Danger Set

## Abstract

A positive threshold defines the strict sublevel danger set of an abstract real multiplier.

**Theorem 1.1 (A danger set is a strict multiplier sublevel).**

$$\begin{aligned}\forall m: \mathbb{R} \mapsto \mathbb{R}, a: \mathbb{R},\\0 < a \Rightarrow \operatorname{thresholdDangerSet}\left(m, a\right) = \{xi \in \mathbb{R} | \operatorname{m}\left(xi\right) < a\}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ThresholdDangerSet.threshold_danger_set_definition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplier is an abstract real-valued parameter because the digested definition does not define its multiplier locally. The positivity premise is retained exactly.

The zero multiplier at threshold one proves realizable nonemptiness, while the constant-one multiplier at the same threshold proves that the construction can also be empty.

Repository searches found only a private abstract confinement helper and a public theorem for a specific completed-zeta multiplier. Pinned Mathlib and third-party package searches found no matching public strict-sublevel constructor.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ThresholdDangerSet.threshold_danger_set_definition`
