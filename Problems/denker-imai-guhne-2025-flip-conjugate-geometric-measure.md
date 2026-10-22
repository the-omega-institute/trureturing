---
slug: denker-imai-guhne-2025-flip-conjugate-geometric-measure
bibkey: denkerimaiguhne2025chiral
doi: null
url: https://arxiv.org/abs/2506.15609v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.result
---

# The geometric measure of the flip-conjugate symmetric subspace

## Problem

S. Denker, S. Imai and O. Gühne, *Chiral Symmetries and Multiparticle Entanglement*, arXiv:2506.15609v1, Appendix H.2:

> **Conjecture:** The geometric measure of entanglement for any state in the flip-conjugate symmetric subspace $\mathcal{H_I}$ (and respectively $\mathcal{H}_{\bar{\mathcal{I}}}$) is given by $G(\ket{\psi}) = 1-\frac{d^2}{(d^2-1)(d+1)}$, where $d$ denotes the local dimension, which coincides with the dimension $\dim(\mathcal{H}_\mathcal{I})$ of the subspace.

Here:
- **The subspace:** $\mathcal H_{\mathcal I}\subset(\mathbb C^d)^{\otimes3}$ is spanned by $\phi_n=(\bar z_d\sum_i|ini\rangle+z_d\sum_i|iin\rangle)/\sqrt{d+1}$ with $z_d=\tfrac12(1+i\sqrt{(d+1)/(d-1)})$.
- **The geometric measure:** $G(\psi)=1-\max|\langle abc|\psi\rangle|^2$ over unit product vectors.

The definitions are quoted in [the literature note](../Library/QuantumContext/denkerimaiguhne2025chiral.md).

Issue [#20037](https://github.com/the-omega-institute/trureturing/issues/20037) fixes the reading: for every $d\ge2$ and every unit vector of either subspace, $G=1-d^2/((d^2-1)(d+1))$. This is proved.

## Motivation

The source builds highly entangled three-qudit subspaces from chiral and flip-conjugate symmetries; every pure state in such a subspace is genuinely multipartite entangled, and a large uniform geometric measure makes the subspace useful for entanglement certification. The source computes the geometric measure numerically for $d\le12$ and proves only the weaker bound $G\ge1-d/(d^2-1)$ in general.

## Gap

The literature check before any Lean is recorded in #20037:
- arXiv lists only v1, with no journal reference;
- the TeX sources of five citing works do not mention the subspace, and the search seat reports the same for a sixth;
- a Zenodo full-text query returns nothing;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Reduction to one vector.** The $\phi_n$ are orthonormal, and every unit vector of $\mathcal H_{\mathcal I}$ is $(\bar U\otimes U\otimes U)\phi_0$ for a unitary $U$. So all states share the product-overlap set of $\phi_0$.
2. **Upper bound.** $\sqrt{d+1}\langle abc|\phi_0\rangle=\langle a,\chi\rangle$ with $\chi_i=\bar z\bar b_0\bar c_i+z\bar c_0\bar b_i$, so the maximum over $a$ is $\|\chi\|^2$. Cauchy–Schwarz and AM–GM give $\|\chi\|^2\le F(x,y)/(d-1)$ with $x=|b_0|^2$, $y=|c_0|^2$ and a concave quadratic $F$ whose maximum is $d^2/(d+1)$. Hence $|\langle abc|\phi_0\rangle|^2\le d^2/((d^2-1)(d+1))$.
3. **Attainment.** At $x=y=d/(d+1)$, with the relative phase of the second components matched to $z^2$, every inequality is an equality.
4. **The conjugate subspace** follows by complex conjugation.

## Falsifier

The proof would not answer the conjecture if the module's subspace or measure differed from the source's. The module:
- defines $z_d$, the basis vectors and both subspaces exactly as the source;
- defines $G$ as one minus the supremum of the squared overlap over all unit product vectors;
- proves the formula for every unit vector of both subspaces and every $d\ge2$.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.lean` (546 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.lean.json`, statement `sha256:e06454beab4383aa1b80c52dc4d79b4c73b7f877af074b741a0c58435789a4e2`.

Declaration statements:
- `result`: `sha256:1b1d37f95a6fd52d813fcd63fce0a05685d3a3950566bc71f3a9136b636150a2`;
- `claim`: `sha256:18042ec55bd598d29c61829fd0664583106e9c9983f69560d3632467f7fad5e5`.

## Triage

Tier 1 conjecture of a 2025 preprint, preregistered in issue #20037 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** every unit vector of $\mathcal H_{\mathcal I}$ or $\mathcal H_{\bar{\mathcal I}}$ has geometric measure $1-d^2/((d^2-1)(d+1))$, for every $d\ge2$.

**Computed, not formalized** (orchestrator, numerical optimization, recorded in #20037): for $d=2,3,4,5$ the maximal product overlap of $\phi_0$ and of a random unit vector of the subspace agree with $d^2/((d^2-1)(d+1))$ to eight decimals.

**Argued, not formalized.**
- *Mechanism.* After fixing $a$ optimally the overlap becomes a quadratic form in the two weights $|b_0|^2,|c_0|^2$. The negative real part of $z_d^2$ penalizes simultaneous weight on the special index, and the maximum sits at the symmetric interior point $d/(d+1)$, not at the product configurations that the source's biseparable bound uses.
- *Comparison with the source's bound.* The source's bound $G\ge1-d/(d^2-1)$ replaces the product maximization by a biseparable one; the exact value exceeds it by $d/((d^2-1)(d+1))$.
- *Asymptotics.* $G=1-1/d+O(d^{-2})$.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; one citing work was read only by the search seat. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
