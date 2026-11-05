---
slug: czartowski-deoliveirajunior-korzekwa-2023-thermal-recall-truncation
bibkey: czartowskideoliveirajuniorkorzekwa2023thermalrecall
doi: 10.1103/PRXQuantum.4.040304
url: https://arxiv.org/abs/2303.12840v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result
---

# Removing intermediate memory resets can increase permutation approximation error

## Problem

J. Czartowski, A. de Oliveira Junior and K. Korzekwa, *Thermal Recall: Memory-Assisted Markovian Thermal Processes*, PRX Quantum 4, 040304 (2023), arXiv:2303.12840v2, introduce a memory-assisted protocol for approximating permutations by sequential two-level thermalisations. Conjecture 1, “Improved convergence,” is stated in the source TeX `TR.tex`, lines 417–427:

> In the infinite temperature limit, $\beta=0$, and for an $N$-dimensional memory, $\widetilde{\mathcal{P}}^{{\Pi}}$ gives a better approximation of a permutation $\Pi$ than $\mathcal{P}^{\Pi}$:
> $$\delta\left( \Pi \mathbf p,\tilde{\mathbf q}\right) \leq  \delta\left( \Pi \mathbf p, \mathbf{q}\right),$$
> where $\tilde{\mathbf{q}}$ and $\mathbf{q}$ are defined via $\widetilde{\mathcal{P}}^{{\Pi}}(\mathbf{p}\otimes \boldsymbol\eta_M) = \tilde{\mathbf{q}}\otimes \boldsymbol\eta_M$ and $\mathcal{P}^{{\Pi}}(\mathbf{p}\otimes \boldsymbol\eta_M) = \mathbf{q}\otimes \boldsymbol\eta_M$.

The repository proposition `claim` is the following exact finite reading. For every $d,n\in\mathbb N$, $p:\mathrm{Fin}\,d\to\mathbb R$, and word $w:\mathrm{List}(\mathrm{Fin}\,d\times\mathrm{Fin}\,d)$, if $0<n$, $(\forall i,\ 0\le p(i))$, $\sum_i p(i)=1$, `StrictAnti p`, and `IsReducedNeighbourWord p w`, then
\[
\operatorname{totalVariation}(\operatorname{applySwaps}(p,w),\operatorname{truncatedOutput}(n,p,w))
\le
\operatorname{totalVariation}(\operatorname{applySwaps}(p,w),\operatorname{resetOutput}(n,p,w)).
\]
Here `applySwaps` folds the word by precomposing with each `Equiv.swap`; `totalVariation` is one half of the finite sum of absolute coordinate differences. `average` replaces the values at two selected joint states by their arithmetic mean. `block` applies these averages for every first memory index and, inside each round, every second memory index, both in increasing `List.finRange` order. `joint` couples $p$ to a uniform memory, `reset` replaces a joint state by the product of its system marginal and that uniform memory, `truncatedOutput` folds the blocks without intermediate resets, and `resetOutput` folds a reset after each block. `IsReducedNeighbourWord` requires, at every position, an increasing index pair whose two current population values are ordered with no current value strictly between them.

The Lean declaration is `result : \lnot claim`.

## Motivation

The conjecture would make the protocol without intermediate memory resets, which lets memory correlations pass between successive transpositions, uniformly at least as accurate as the protocol that resets the memory after each transposition. Such a guarantee would control the approximation error for the reduced neighbour-transposition words used to reach permutation vertices of the infinite-temperature thermal cone. A counterexample identifies a limit of that guarantee and separates one-block convergence behaviour from compositions of blocks.

## Gap

The bounded literature check recorded in issue [#23571](https://github.com/the-omega-institute/trureturing/issues/23571) found no settlement in the source, the listed citing works, or the repository records. The source TeX and the closest cited papers were checked for this conjecture; the search scope is recorded in that issue.

`not-found-in-searched-scope`.

## Route

1. The module defines the infinite-temperature elementary operation `average`, the nested-round operation `block`, the uniform-memory coupling `joint`, the memory `reset`, and the two folded outputs. The outer fold of `block` uses the first memory index $k$ in increasing order; the inner fold uses the second index $l$ in increasing order, matching the textual order of the source protocol.
2. It defines `IsReducedNeighbourWord` from the current population function `r := applySwaps p (w.take n)`: for every $n<w.length$, with $z=w[n]$, it requires $z.1<z.2$, $r(z.2)<r(z.1)$, and $\forall c,\ \neg(r(z.2)<r(c)\land r(c)<r(z.1))$. The proposition `claim` then adds exactly the positivity, mass, strict-order and reduced-word hypotheses displayed above.
3. The witness is the private vector $p=(1/2,1/4,2/9,1/36)$ on `Fin 4` and the word $w=[(0,1),(2,3),(0,3)]$. The private theorem `instance_hypotheses` proves `Probability p ∧ StrictAnti p ∧ IsReducedNeighbourWord p w`; its `Probability` component supplies $(\forall i,\ 0\le p(i))$ and $\sum_i p(i)=1$, and the application of `claim` also supplies $0<2$.
4. The private theorem `target_values` gives `applySwaps p w = (2/9,1/2,1/36,1/4)`. The theorem `joint_values` gives the eight joint entries for `joint 2 p`. The three theorems `truncated_block_one`, `truncated_block_two`, and `truncated_block_three` evaluate the three successive blocks without resets. The corresponding reset path is evaluated by `reset_block_one`, `reset_block_two_raw`, `reset_block_two`, `reset_block_three_raw`, and `reset_block_three`.
5. The private theorems `truncated_values` and `reset_values` therefore give
   \[
   \operatorname{truncatedOutput}(2,p,w)=(31/144,13/32,29/288,5/18),
   \]
   and
   \[
   \operatorname{resetOutput}(2,p,w)=(2/9,13/32,29/288,13/48).
   \]
   The private theorem `distance_gap` proves the exact identity
   \[
   \operatorname{totalVariation}(\operatorname{applySwaps}(p,w),\operatorname{truncatedOutput}(2,p,w))
   =
   \operatorname{totalVariation}(\operatorname{applySwaps}(p,w),\operatorname{resetOutput}(2,p,w))+1/144.
   \]
6. The theorem `result` assumes `claim`, instantiates it at $d=4$, $n=2$, this $p$ and this $w$ with all of the hypotheses from `instance_hypotheses`, and combines the resulting inequality with `distance_gap` to derive a contradiction.

## Falsifier

The refutation would not apply to the source conjecture if the Lean operations differed from the source's infinite-temperature protocol. In particular, a mismatch in the increasing round or inner-step order, in the marginal reset, in the total-variation normalization, or in the interpretation of a reduced neighbour word would break the source-to-module correspondence. The module uses zero-based `Fin` indices; its word corresponds to the source's successive exchanges of levels $1,2$, then $3,4$, then $1,4$. The formal result covers the stated reduced-word reading only; it does not settle non-reduced words, non-neighbour words, finite temperature, or asymptotic memory-size claims.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** `#print axioms` on `result` reports only `propext`, `Classical.choice`, and `Quot.sound`; the module contains no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:b74f629ecf698a2b8ecadfffb51ff6bde06fea9b88867ecb46856bf89baed48b`;
- `claim`: `sha256:8449e5c22b65b2844c85279c8e2f30fb750baf564d63de1e7a8400749ce1ba60`.

## Triage

Tier 1 conjecture of a 2023 PRX Quantum paper with numerical support, preregistered in issue #23571 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; its per-declaration proof shapes are bind-only definitions and private lemmas consumed on the proof path of `result`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the formal proposition `claim` is false.

**Computed, not formalized** (orchestrator, Claude Code/Opus, recorded in #23571): the instance also violates the conjecture under the three other readings of the loop order and with the other reduced word of the same permutation, in exact rational arithmetic.

**Argued, not formalized.**

- The mechanism is correlation transfer. Each block is a sequence of linear averages on joint system-memory cells. A reset discards the joint correlations by replacing the state with its system marginal times a uniform memory; omitting the reset carries those correlations into the next block. For a composition of reduced transpositions, the carried correlations can move mass in a direction that increases the final distance to the ideal permutation, as the certified witness demonstrates.
- The missing structure is a condition controlling those cross-block correlations. The source conjecture imposes reduced neighbour ordering but no condition that prevents a later block from exploiting the correlations created by an earlier block. A restriction to a single $\beta$-cycle or another class with a separate convergence argument could survive; this module does not prove such a restriction.
- The source's claim that the truncated protocol is uniformly advantageous for arbitrary reduced compositions is therefore unavailable under this formal reading. The source's separate finite-temperature statements, asymptotic $O(N^{-1/2})$ estimates, and Conjecture 2 are outside `claim` and are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded to the source, the cited-work search and repository searches recorded in issue #23571; it does not establish exhaustive worldwide novelty or priority. The broader numerical searches and the source's numerical reports are not formalized. The interpretation of the source's one-based protocol notation as the module's zero-based `Fin` operations is checked for the stated word and loop order, but a formal equivalence for every alternative protocol convention is not supplied. The mechanism discussion, the surviving restricted classes, all non-reduced or non-neighbour words, finite-temperature behaviour, and asymptotic statements in $N$ remain unverified by this module.
