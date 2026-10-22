---
slug: uola-et-al-2021-heisenberg-channel-compression-equivalence
bibkey: uola2021subspaces
doi: 10.1103/PhysRevA.103.022203
url: https://arxiv.org/abs/2010.04048v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.result
---

# Compatibility under every Heisenberg channel equals compatibility in every subspace

## Problem

R. Uola, T. Kraft, S. Designolle, N. Miklin, A. Tavakoli, J.-P. Pellonpää, O. Gühne and N. Brunner, *Quantum measurement incompatibility in subspaces*, arXiv:2010.04048v2 (Phys. Rev. A 103, 022203, 2021), section on incompressible incompatibility:

> It is worth mentioning that one can modify the concept of incompressible incompatibility by demanding that a measurement assemblage becomes compatible under every Heisenberg channel (a channel preserving identity, but not necessarily trace preserving) to a smaller dimensional system. Although we will leave open the question of whether this provides a strict subset of measurement assemblages that are compatible in every subspace, …

Here:
- **Compatible in every subspace of dimension $n$:** every compression $\{V^\dagger M_{a|x}V\}$ by an isometry $V:\mathbb C^n\to\mathbb C^d$ has a parent POVM.
- **Heisenberg channel:** a completely positive unital map $\Phi:M_d\to M_n$, applied to each effect.

The definitions are quoted in [the literature note](../Library/QuantumContext/uola2021subspaces.md).

Issue [#20047](https://github.com/the-omega-institute/trureturing/issues/20047) fixes the reading: for each $n\le d$ the two conditions are equivalent, so the subset is not strict. This is proved.

## Motivation

Compressing an incompatible assemblage to a subspace models measuring a system of bounded dimension; the source shows that some incompatibility disappears in every smaller subspace. The channel version models any physical preprocessing into a smaller system, and it is the formulation that appears in steering with a steered party of bounded dimension.

## Gap

The literature check before any Lean is recorded in #20047:
- Crossref counts 13 citations and Semantic Scholar lists 17 citing works;
- the TeX sources of Loulidi–Nechita (compatibility dimension), the Rev. Mod. Phys. review, Ioannou et al. and three later papers state neither the equivalence nor a separation;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Channels contain compressions.** $X\mapsto V^\dagger XV$ is completely positive and unital.
2. **Compressions generate channels.** Write $\Phi(X)=\sum_rK_r^\dagger XK_r$.
   - Each $K_r:\mathbb C^n\to\mathbb C^d$ factors as $K_r=V_rC_r$ with $V_r$ an isometry.
   - Compatibility of each compression $V_r^\dagger\mathcal MV_r$ gives parents $G^{(r)}$ on a common joint-outcome index.
   - Then $H=\sum_rC_r^\dagger G^{(r)}C_r$ is a parent of $\Phi(\mathcal M)$: it is positive, sums to $\Phi(I)=I$, and has the right marginals.

## Falsifier

The proof would not answer the question if the module's channels or compressions were restricted. The module:
- quantifies over every completely positive unital map into $M_n$, with no trace condition;
- quantifies over every isometry, equivalent to the source's $P_nU^\dagger\cdot UP_n$ for every unitary $U$;
- allows any finite number of settings and outcomes.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.lean` (217 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.lean.json`, statement `sha256:85480177f8a69d022451674927a23a51cb02aee0042c20536c4ed19c2170869a`.

Declaration statements:
- `result`: `sha256:1942b2927e565a8a0d83126d717e8748472f11be464853348f35092e5440f381`;
- `claim`: `sha256:eb47d9923aed293dec78232040833b131c5898813d508505378865711ea528b6`.

## Triage

Tier 1 question of a 2021 paper, preregistered in issue #20047 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\le d$, a finite POVM family is compatible in every $n$-dimensional subspace exactly when it is compatible after every Heisenberg channel to $M_n$.

**Argued, not formalized.**
- *Mechanism.* A unital completely positive map into $M_n$ is an average of compressions followed by contractions: each Kraus operator sees only an $n$-dimensional subspace of the input. Parents for the compressions therefore combine into a parent for the channel image.
- *Stronger form.* The argument uses only that each Kraus operator has rank at most $n$, so it also covers unital completely positive maps into larger output algebras whose Kraus operators have rank at most $n$.
- *Steering.* Combined with the source's channel picture of steering, compatibility in every $n$-dimensional subspace is equivalent to the impossibility of steering with states of Schmidt number at most $n$ on the steered side.
- *Effect on the paper.* The channel version of incompressible incompatibility coincides with the subspace version, so the source's Peres-conjecture construction gives incompressibility in both senses at once.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized; the steering equivalence was derived by the search seat and checked only in outline by the orchestrator.
