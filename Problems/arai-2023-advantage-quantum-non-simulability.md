---
slug: arai-2023-advantage-quantum-non-simulability
bibkey: arai2023diversity
doi: null
url: https://arxiv.org/abs/2302.12361v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.result
---

# Advantage-quantum measurements are not quantum n-simulable

## Problem

H. Arai, *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*, Ph.D. thesis, arXiv:2302.12361v1, Section 5.2 (Open Problems), Theme B:

> Similarly, it is considered that AQ measurement might be non-simulable because AQ measurement also has an extraordinary performance. This is an open problem.

Here:
- **DOVM:** a two-outcome measurement $\{M_1,M_2\}$ on $\mathcal H_A\otimes\mathcal H_B$ whose effects are block positive (nonnegative on product vectors) and sum to $I$.
- **AQ:** one effect satisfies $\lambda_1(M_i)<0$ and $1+\lambda_1(M_i)<\lambda_d(M_i)<1$.
- **Domain:** the states $\rho$ with $\mathrm{tr}\,\rho M_i\ge0$ for both $i$.
- **Quantum $n$-simulable:** some POVM $\{N_i\}$ on $(\mathcal H_A\otimes\mathcal H_B)^{\otimes n}$ has $\mathrm{tr}\,\rho^{\otimes n}N_i=\mathrm{tr}\,\rho M_i$ on the domain.

The definitions are quoted in [the literature note](../Library/QuantumContext/arai2023diversity.md).

Issue [#20035](https://github.com/the-omega-institute/trureturing/issues/20035) fixes the reading: no AQ DOVM is quantum $n$-simulable for any $n$, with the simulation identity required only on trace-one domain states, which makes the statement stronger than the literal domain. This is proved.

## Motivation

The thesis studies entanglement structures beyond standard quantum theory and asks whether their measurements can be reproduced inside quantum theory by acting on several copies of the state. It proves that beyond-quantum (BQ) DOVMs cannot be simulated, because they discriminate non-orthogonal states perfectly, and leaves the AQ class open.

## Gap

The literature check before any Lean is recorded in #20035:
- arXiv lists only v1;
- the follow-up papers arXiv:2307.11271 and 2411.01873 by Arai and Hayashi do not treat deterministic $n$-copy simulation on the domain;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Let $E=M_i$ be the AQ effect, with $\lambda_1<0$ and $\lambda_d<1$.
1. **Positive top eigenvalue.** Block positivity makes the diagonal of $E$ in a product basis nonnegative, so $\mathrm{tr}\,E\ge0$. With $\lambda_1<0$ this forces $\lambda_d>0$.
2. **A domain state with positive probability.** The top eigenprojector $\rho_+$ has $\mathrm{tr}\,\rho_+E=\lambda_d\in(0,1)$, so it lies in the domain.
3. **A full-rank domain state with zero probability.** Mixing $I/d$ with the bottom eigenprojector gives $\rho_0$ with $\mathrm{tr}\,\rho_0E=0$ and $\rho_0\ge(p/d)I$.
4. **Contradiction.** $\rho_0^{\otimes n}$ is positive definite, so $N_i\ge0$ and $\mathrm{tr}\,\rho_0^{\otimes n}N_i=0$ force $N_i=0$. That contradicts $\mathrm{tr}\,\rho_+^{\otimes n}N_i=\lambda_d>0$.

## Falsifier

The proof would not answer the question if the module's notions were weaker than the thesis's. The module:
- requires both effects to be Hermitian and block positive with sum $I$;
- defines AQ by the extreme eigenvalues exactly as the thesis does;
- quantifies over every $n$ and every two-outcome POVM on $n$ copies;
- imposes the simulation identity only on trace-one domain states, a subset of the thesis's domain.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.lean` (244 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.lean.json`, statement `sha256:7b5cca381c12b63c49c5041bd4d9631d56ae5ead3a1148584182391e7900569e`.

Declaration statements:
- `result`: `sha256:3a3045f47532c4d3cf4598d42341e237f0cb4a530a67dea205c25b4cdb02f697`;
- `claim`: `sha256:880e3d905c4146b47ce1cf6479d0299e4616e465d1ca9c28a57286e3df67259d`.

## Triage

Tier 1 open problem of a 2023 thesis, preregistered in issue #20035 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** no AQ DOVM is quantum $n$-simulable, for any $n$.

**Argued, not formalized.**
- *Mechanism.* Simulation must hold on every domain state. Because the domain contains a full-rank state on which the indefinite effect has probability zero, any simulating effect is forced to vanish. The obstruction is not the discrimination performance the thesis suggests; it is the shape of the domain.
- *Scope.* The argument never uses the AQ inequality $1+\lambda_1<\lambda_d$. It applies to every binary DOVM with an effect satisfying $\lambda_1<0$ and $0<\lambda_d\le1$, which covers the AQ class, the NAQ class and the marginal case $\lambda_d=1$. Together with the thesis's theorem for BQ ($\lambda_d\ge1$), no binary DOVM outside the POVMs is quantum $n$-simulable.
- *Effect on the thesis.* Theme B's open problem is answered negatively for AQ, and the related question at l. 2254, whether other classes of DOVMs are $n$-simulable, is answered negatively for all binary DOVMs with a negative eigenvalue.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the related multi-copy implementation papers were screened by the search seat. The statements in "Argued, not formalized" are not formalized.
