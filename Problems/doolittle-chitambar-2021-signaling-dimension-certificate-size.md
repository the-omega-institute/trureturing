---
slug: doolittle-chitambar-2021-signaling-dimension-certificate-size
bibkey: doolittlechitambar2021certifying
doi: 10.1103/PhysRevResearch.3.043073
url: https://arxiv.org/abs/2102.12543v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.result
---

# At most binomially many inputs certify failure of d-message simulation

## Problem

B. Doolittle and E. Chitambar, *Certifying the Classical Simulation Cost of a Quantum Channel*, arXiv:2102.12543v1 (Physical Review Research 3, 043073, 2021), define a classical channel by its conditional probabilities $P(y|x)$ and define d-simulation by
\[
P(y|x)=\sum_\lambda q(\lambda)\sum_{m\in[d]}R_\lambda(y|m)T_\lambda(m|x).
\]
Their signaling polytope $\mathcal C_d^{n\to n'}$ is the set of channels with such a simulation. Immediately after Theorem `Thm:main2`, the source states (main.tex, line 409):

> We conjecture that in general, no more than $\binom{n'}{d}$ inputs are needed to certify that a channel $\mbf{P}\in\mc{P}^{n\to n'}$ has a signaling dimension larger than $d$.

The settled finite formulation uses natural numbers $m,k,d$, a channel `p : \mathrm{Fin}\,m \to \mathrm{Fin}\,k \to \mathbb R`, the imported predicate `IsRowStochastic p`, and the finite shared-randomness predicate `IsSimulable d p`. For $1\le d$ and $d<k$, if $p$ is row stochastic and is not d-simulable, the theorem asserts a nonempty finite input set $i$ with $i.\mathrm{card}\le k.choose\ d$ such that the input restriction $(i : \mathrm{Set}\ _) .\mathrm{domRestrict}\ p$ is not d-simulable.

## Motivation

A bounded certificate makes failure of classical simulation testable on a small subchannel. The source's $n'=4$, $d=2$ case gives six inputs; the general bound makes the size of a separating input family depend on the output and message alphabets, rather than on the total number of inputs.

## Gap

Issue [#23056](https://github.com/the-omega-institute/trureturing/issues/23056) records a bounded prior-settlement search over the source literature, citing works, and repository. It records the v1 paper and the reported repetition of the conjecture in Doolittle's 2023 dissertation, with no prior settlement found in that search scope. The issue labels the conjecture Tier 1 and records the six-input check for $k=4,d=2$. The bounded search does not establish exhaustive worldwide novelty or priority.

## Route

For $S$ the subtype of $d$-element subsets of $\mathrm{Fin}\,k$, the private definition `feasible (d := d) p x` consists of vectors $q:S\to\mathbb R$ with nonnegative coordinates summing to one, and arrays $a:S\to\mathrm{Fin}\,k\to\mathbb R$ that are nonnegative, supported on each subset, satisfy $\sum_y a\ s\ y=q\ s$, and satisfy $\sum_s a\ s\ y=p\ x\ y$.

1. `channel_decomposition` has finite types α and β, decidable equality on α and β, a function $p:\alpha\to\beta\to\mathbb R$, and the hypothesis hp : IsRowStochastic p. It proves nonnegative product weights for every $f:\alpha\to\beta$, that their sum is one, and the row-marginal equation recovering p.
2. `mixture_common` has finite types α and ι, naturals k and d, hk : d < k, a function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$, weights $w:\iota\to\mathbb R$ with hw : \forall j,\ 0\le w\ j and hs : \sum_j w\ j=1, maps $v:\iota\to\alpha\to\mathrm{Fin}\,k$ with hv : \forall j,\ (\mathrm{Finset.univ.image}(v\ j)).\mathrm{card}\le d$, and hp : \forall x\ y,\ p\ x\ y=\sum_j w\ j\cdot\mathrm{if}\ v\ j\ x=y\ \mathrm{then}\ 1\ \mathrm{else}\ 0. It constructs q with $\forall x,\ q\in\mathrm{feasible}\ (d:=d)\ p\ x$.
3. `simulable_common` has finite α, naturals k and d, hd : 1 \le d, hk : d < k, a function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$, and h : IsSimulable d p. It produces a q common to all feasible sets by applying channel_decomposition to each row-stochastic encoder and decoder and then mixture_common.
4. `finite_simulation` has finite ι, a function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$, q : ι → ℝ, t : ι → α → Fin d → ℝ, and r : ι → Fin d → Fin k → ℝ. Its hypotheses are hq : ∀ l,\ 0\le q\ l, hs : \sum_l q\ l=1, ht : \forall l,\ IsRowStochastic (t\ l), hr : \forall l,\ IsRowStochastic (r\ l), and hp : \forall x\ y,\ p\ x\ y=\sum_l q\ l\cdot\sum_\mu r\ l\ \mu\ y\cdot t\ l\ x\ \mu. It concludes IsSimulable d p.
5. `common_simulable` has finite and nonempty α, naturals k and d, hd : 1 \le d, hk : d < k, a function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$, and h : \exists q,\ \forall x,\ q\in\mathrm{feasible}\ (d:=d)\ p\ x. It constructs encoders and deterministic decoders and invokes finite_simulation. The zero-coordinate branch uses an element of Fin d, so hd is required.
6. `empty_inputs_simulable` has empty α, naturals k and d, hd : 1 \le d, hk : d < k, and a function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$; it constructs IsSimulable d p directly.
7. `feasible_convex` has an arbitrary function $p:\alpha\to\mathrm{Fin}\,k\to\mathbb R$ and input x : α and proves Convex ℝ (feasible (d := d) p x) by combining two feasible points with coefficients b and c satisfying 0 ≤ b, 0 ≤ c, and b+c=1.
8. `helly_normalized` has finite α and β, nonempty β, a family $f:\alpha\to\mathrm{Set}(\beta\to\mathbb R)$, hc : ∀ x, Convex ℝ (f x), hn : ∀ x q, q ∈ f x → \sum_s q\ s=1, and he : ¬∃ q, ∀ x, q ∈ f x. It returns a nonempty finite subfamily of cardinality at most Fintype.card β with empty intersection, using Convex.helly_theorem' after deleting one coordinate.
9. In `result`, the hypotheses are m k d : ℕ, hd : 1 ≤ d, hk : d < k, p : Fin m → Fin k → ℝ, hp : IsRowStochastic p, and h : ¬ IsSimulable d p. The empty-input lemma rules out m=0; d<k makes the d-subset type nonempty; common_simulable rules out a common feasible q; helly_normalized supplies i; and the cardinality identity gives i.card ≤ k.choose d. If the restriction to i were simulable, simulable_common applied to that finite restricted input type would contradict the empty-intersection conclusion.

## Falsifier

The correspondence would fail if the source's channel orientation, row-stochastic convention, number of messages, or shared-randomness mixture differed from these definitions. In the source, $P(y|x)$ is an $n'\times n$ column-stochastic matrix; the Lean function $p\ x\ y$ places the input first and requires corresponding rows to be stochastic. It would also fail if restricting to i did not mean the subtype input restriction used by `Set.domRestrict`, or if the source required a stronger simulation notion than `IsSimulable`.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.lean.json`.

Declaration statements:

- `result`: `sha256:acef840d3a54f9e171156a0fc9e54847988ea6a6ba5322b4ee9819979e34c60d`.

- **Proof.** It proves `result`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2021 paper, preregistered in issue [#23056](https://github.com/the-omega-institute/trureturing/issues/23056) before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every $m,k,d\in\mathbb N$, every $1\le d$ and $d<k$, every row-stochastic $p:\mathrm{Fin}\,m\to\mathrm{Fin}\,k\to\mathbb R$, and every hypothesis that p is not `IsSimulable d p`, there is a nonempty $i:\mathrm{Finset}(\mathrm{Fin}\,m)$ with $i.\mathrm{card}\le\binom{k}{d}$ such that `¬ IsSimulable d ((i : Set _).domRestrict p)`.

**Computed, not formalized:** the source's six-input case ($k=4$, $d=2$) agrees with $\binom{4}{2}=6$.

**Argued, not formalized.**

- For a finite nonempty input type, `simulable_common` and `common_simulable` give the two directions between d-simulation and a common point of the feasible sets; `empty_inputs_simulable` handles the empty input type separately. The resulting convex family lies in a simplex of distributions on d-element output subsets, and normalized Helly bounds a failed total intersection by at most the simplex number of coordinates. This explains the binomial coefficient; it supplies no sharpness example.
- Whether $\binom{k}{d}$ is sharp for any or all pairs $(k,d)$ is open here. The theorem is an upper bound and does not assert that a witness of size exactly $\binom{k}{d}$ is necessary.
- The source's six-input consequence for four outputs and two messages is compatible with this specialization, but its facet classification, Bell-inequality enumeration, and numerical polytope calculations are not formalized by `result`.
- The source's quantum-channel applications and its statements about physical input or output Hilbert-space dimensions require separate channel-to-correlation and Bell-inequality arguments. They are not consequences of this finite classical theorem; statements depending on those ingredients retain their separate conditions and evidence.

## ASSUMED-UNVERIFIED

The literature check in issue #23056 is bounded and does not establish exhaustive novelty or priority. The reported repetition in Doolittle's 2023 dissertation was not independently verified. Sharpness of the binomial bound, facet classifications, numerical searches, and quantum-channel consequences are not formalized here. The statements under “Computed, not formalized” and “Argued, not formalized” are not Lean declarations; statements from source sections outside the cited TeX passages remain unverified.
