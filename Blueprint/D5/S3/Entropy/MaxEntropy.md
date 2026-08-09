# Maximum Entropy on a Finite Alphabet

## Abstract

Finite Shannon entropy in nats is at most the natural logarithm of the alphabet cardinality.

**Theorem 1.1 (Finite Shannon entropy is at most log-cardinality).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\\sum_{i}\operatorname{negMulLog}(p(i)) \le \log(\operatorname{card}(\iota)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MaxEntropy.entropy_le_log_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The units are nats: Real.log is the natural logarithm, consistent with the repository's klDivergence. The definition deliberately wraps Mathlib's Real.negMulLog term by term and supplies only the finite sum that Mathlib does not provide. This division of responsibility is deliberate: Mathlib owns the per-term lemmas for nonnegativity on the unit interval, the product rule, and concavity; open-coding -sum p log p and re-deriving them would duplicate upstream work.

The proof introduces the uniform distribution u(i) = (card iota)^-1 locally. It is deliberately not frozen as a definition of this module because it has exactly one consumer. The bound is obtained from D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg through the identity D(p||uniform) = log card - H(p); no part of KL nonnegativity is re-proved here.

The hypotheses are nonnegativity and normalization only, not strict positivity. Zero-mass letters are permitted. Their terms vanish because Real.negMulLog 0 = 0 and Real.log 0 = 0, following the same endpoint convention already fixed by klDivergence.

The Nonempty iota hypothesis is genuinely required, not decorative: without it the cardinality is zero and the uniform mass fails to be a distribution.

This module proves the upper bound only. It does not characterize the equality case that the maximum is attained exactly at the uniform distribution. It introduces no conditional or joint entropy.

## References

- Truth anchor: `D5/S3/Entropy/MaxEntropy.entropy_le_log_card`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
