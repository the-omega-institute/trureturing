# The Entropy-Divergence Consistency Identity

## Abstract

Divergence from the uniform law equals the finite Shannon entropy deficit in nats.

**Theorem 1.1 (Divergence from uniform is the entropy deficit).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\D(p\Vert\Vert (i\mapsto \operatorname{card}(\iota)^{-1}))=\log(\operatorname{card}(\iota))-H(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/EntropyDivergenceIdentity.kl_divergence_uniform_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem identifies the divergence of p from the uniform law with the entropy deficit log |iota| - H(p). Both sides use the repository's existing imported definitions, klDivergence and shannonEntropy; this module defines nothing of its own. The units are nats, consistent with klDivergence and shannonEntropy.

This equality is a consistency pin between the two definitions. On the probability simplex, it fixes shannonEntropy pointwise, but only because klDivergence is independently attested by other frozen identities. The anchor is klDivergence; this is a pin between the two definitions, not an isolated certificate of entropy.

The residual limitation is plain: the identity is blind to every correction that vanishes on normalized inputs. For example, adding a multiple of (sum_i p(i) - 1) to shannonEntropy is invisible under the theorem's hypotheses, because the corrupted entropy agrees with the true one everywhere those hypotheses hold. Off-simplex behaviour therefore remains unpinned; the theorem does not fully machine-attest the entropy definition.

The reference is specifically the uniform law i -> (card iota)^-1. The identity does not hold against a non-uniform reference. A definition named uniform is deliberately not frozen in this bucket: it has a single consumer, so the reference is written inline.

The hypotheses are nonnegativity and normalization only, not strict positivity. Zero-mass letters are permitted, and their terms vanish. The Nonempty iota hypothesis is genuinely required, not decorative: the proof needs positive cardinality.

The same relation is derived inside MaxEntropy's proof as a proof-local step, but that step is not citable from outside the proof. This theorem is the first citable source of the fact and introduces no new definition. Frozen modules cannot gain declarations, so the relation is re-proved here rather than lifted out of MaxEntropy.

## References

- Truth anchor: `D5/S3/Entropy/EntropyDivergenceIdentity.kl_divergence_uniform_eq`
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
