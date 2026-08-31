# Maximal Forward-Invariant Subkernel

## Abstract

Every equivalence relation has a greatest forward-invariant subrelation.

**Theorem 1.1 (The forward-orbit kernel is the greatest invariant subkernel).**

$$\forall X: \operatorname{Type}, F: X \to X,\\K_{q}: \operatorname{Set}(X \times X), \operatorname{Equivalence}\left(K_{q}\right) \Rightarrow\\K_{infinity} = \{(x, y) \mid \forall n\in \mathbb{N}, (F^{n}(x), F^{n}(y)) \in K_{q}\} \land\\\operatorname{Equivalence}\left(K_{infinity}\right) \land K_{infinity} \subseteq K_{q} \land\\(\forall x, y, (x, y) \in K_{infinity} \Rightarrow (F(x), F(y)) \in K_{infinity}) \land\\\forall R: \operatorname{Set}(X \times X), (R \subseteq K_{q} \land \forall x, y, (x, y) \in R \Rightarrow (F(x), F(y)) \in R) \Rightarrow R \subseteq K_{infinity}.$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/MaximalForwardInvariantSubkernel.maximal_forward_invariant_subkernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Kq be an equivalence relation on X and let F be a self-map of X. The relation K-infinity consists of the pairs whose complete forward orbits remain related by Kq.

K-infinity is itself an equivalence relation contained in Kq and is preserved by applying F to both coordinates. Every relation contained in Kq with the same forward-invariance property is contained in K-infinity, which proves both existence and maximality.

The module also identifies K-infinity with the greatest fixed point of the monotone one-step refinement operator. The repository's general Knaster-Tarski wrapper supplies the extremal fixed-point facts; pinned Mathlib supplies OrderHom.gfp and the complete lattice of relations.

## References

- Truth anchor: `D5/S1/FixedPoints/MaximalForwardInvariantSubkernel.maximal_forward_invariant_subkernel`
- Dependency: [D5/S1/Dynamics/KnasterTarski](../Dynamics/KnasterTarski.md)
