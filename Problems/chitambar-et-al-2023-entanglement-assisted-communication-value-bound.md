---
slug: chitambar-et-al-2023-entanglement-assisted-communication-value-bound
bibkey: chitambargeorgedoolittlejunge2023communication
doi: 10.1109/TIT.2022.3218540
url: https://arxiv.org/abs/2109.11144v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.result
---

# Entanglement assistance raises the communication value by at most the output dimension

## Problem

E. Chitambar, I. George, B. Doolittle and M. Junge, *The Communication Value of a Quantum Channel*, arXiv:2109.11144v1 (IEEE Trans. Inf. Theory 69, 1660–1679, 2023), section on the entanglement-assisted communication value:

> \noindent\textit{Conjecture}: For any channel $\mc{N}\in\cptp(A\to B)$, $\cv^*(\mc{N})\leq d_B\cdot \cv(\mc{N})$.

Here:
- **cv(N):** the supremum, over all finite families of input states $\rho_x$ and output POVMs $\{\Pi_y\}$, of $\sum_y\max_xP(y|x)$ with $P(y|x)=\mathrm{tr}[\Pi_y\mathcal N(\rho_x)]$.
- **cv\*(N):** the same supremum when sender and receiver share a state $\varphi^{A'B'}$ of any dimension, the sender applies channels $\mathcal E_x^{A'\to A}$ and the receiver measures $BB'$.

The definitions are quoted in [the literature note](../Library/QuantumContext/chitambargeorgedoolittlejunge2023communication.md).

Issue [#20033](https://github.com/the-omega-institute/trureturing/issues/20033) fixes the reading with the operational definitions of the source. This is proved.

## Motivation

The communication value measures how well a single use of a channel transmits a classical message in a guessing game; its entanglement-assisted version is the zero-error cost of simulating the channel with quantum non-signalling resources. The source shows that shared entanglement can raise cv by at most a factor 2 for qubit channels and conjectures the dimension factor $d_B$ in general, the single-shot analogue of bounding entanglement-assisted capacity gains by the dimension.

## Gap

The literature check before any Lean is recorded in #20033:
- Semantic Scholar lists 19 citing works and Crossref counts 15 citations;
- the TeX sources of thirteen of them, including George–Chitambar's cone-restricted information theory and Wolff et al.'s capacity-ratio bound, state no proof or refutation;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Write $b=d_B$ and $J$ for the Choi matrix of $\mathcal N$.
1. **Assisted protocols as operators.** Every assisted protocol value equals $\mathrm{tr}[J\Omega]$ for a positive semidefinite $\Omega$ with $\mathrm{tr}_A\Omega=I_B$.
2. **Depolarizing Bob's factor.** The channel $D_b(X)=[X+\mathrm{tr}(X)I]/(b+1)$ is entanglement breaking, with an explicit finite measure-and-prepare decomposition from a phase-averaging identity. So $\Omega'=(\mathrm{id}\otimes D_b)\Omega$ is a finite sum of products of positive matrices with $\mathrm{tr}_A\Omega'=I_B$.
3. **Back to an unassisted protocol.** $\Omega'$ defines an unassisted protocol of value $(\mathrm{tr}[J\Omega]+b)/(b+1)$. Hence every assisted value is at most $(b+1)\,\mathrm{cv}-b$.
4. **Conclusion.** Every unassisted value is at most $b$, so $(b+1)\mathrm{cv}-b\le b\,\mathrm{cv}$.

## Falsifier

The proof would not answer the conjecture if the module's quantities differed from the source's. The module:
- defines cv and cv\* operationally, by the source's Definition 1 and its entanglement-assisted definition, with the classical communication value $\sum_y\max_xP(y|x)$;
- lets the shared state range over every density matrix of every finite dimension, which contains the source's entangled states, so the bound proved is at least as strong as the conjecture.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.lean` (472 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.lean.json`, statement `sha256:6106aeaecbe533d3988424e655508ef1e2885301e1c196a61b508bfbbcf78bdf`.

Declaration statements:
- `result`: `sha256:49fc685b2c2e7ddf76561d5c6117d2d219f6fafa236ad1cdbb45daae965371dd`;
- `claim`: `sha256:79bf299b3952b17f0cdcc148a486452099c53c83448afa43900e9998ca5c3afb`.

## Triage

Tier 1 conjecture of a 2021 preprint kept in the 2023 journal version, preregistered in issue #20033 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** $\mathrm{cv}^*(\mathcal N)\le d_B\,\mathrm{cv}(\mathcal N)$ for every channel.

**Computed, not formalized** (orchestrator, cvxpy, recorded in #20033): for random channels with $(d_A,d_B)\in\{(2,2),(2,3),(3,2),(3,3)\}$, the depolarized optimal assisted operator keeps the marginal $I_B$ and has objective $(c^*+b)/(b+1)$.

**Argued, not formalized.**
- *Stronger bound.* The route gives $\mathrm{cv}^*\le(d_B+1)\mathrm{cv}-d_B$, and the same construction on the input side gives $\mathrm{cv}^*\le(d_A+1)\mathrm{cv}-d_A$. Both are sharp for every partially depolarizing channel, including the identity channel, where $\mathrm{cv}=d$ and $\mathrm{cv}^*=d^2$.
- *Mechanism.* Depolarizing the receiver's half of any assisted strategy at the entanglement-breaking threshold destroys the entanglement while keeping a fixed fraction $1/(b+1)$ of the score and adding a fixed offset. The dimension factor is the price of that threshold.
- *Effect on the paper.* The multiplicative enhancement of the communication value by entanglement is bounded by $\min(d_A,d_B)$, refining the qubit bound of factor 2 to an affine bound in every dimension.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; the published version's numbering and text were read only by the search seat.
