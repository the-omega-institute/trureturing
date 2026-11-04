---
slug: bulchandani-burnell-sondhi-2023-polygon-game-classical-value
bibkey: bulchandaniburnellsondhi2023polygon
doi: 10.1103/PhysRevB.107.045412
url: https://arxiv.org/abs/2206.11252v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/PolygonGameClassicalValue.result
---

# The classical value of the odd polygon game is its Fibonacci bound

## Problem

V. B. Bulchandani, F. J. Burnell and S. L. Sondhi, *Playing nonlocal games with phases of quantum matter*, Phys. Rev. B 107, 045412 (2023), arXiv:2206.11252v2, Section 4.1, "Classical winning probabilities", state in `ArxivResub.tex`, lines 714–717, the equation labelled `eq:classwinbound` and its conjecture:

> $p_{\mathrm{cl}}^*(P) \geq \frac{2^P - F_{P-1}}{2^P} = 1 - \frac{F_{P-1}}{2^P}, \quad P \,\mathrm{odd}.$
>
> We conjecture that this bound is tight.

Here $P\ge3$ is the number of players and $F_1=F_2=1$. The game's rules are in the same section, `ArxivResub.tex`, lines 629–655; see also [the literature note](../Library/Resource/bulchandaniburnellsondhi2023polygon.md).

Index players and oriented edges by $\mathbb Z/P$, with edge $i$ joining $i$ to $i+1$. A deterministic strategy assigns triples $(a_i,b_i^0,c_i)$ on input $0$ and $(d_i,b_i^1,e_i)$ on input $1$. The module allows the middle bit to depend on the input. For a matching $M$, let $x_M$ be the input whose ones are exactly its covered vertices. On input $x$, the strategy wins when every returned triple has even parity, the returned middle bits have even total parity, and, for every matching with $x_M=x$,

$$\sum_{i\in M}(d_i+e_{i+1})+\sum_{j\text{ uncovered by }M}a_j\equiv |M|\pmod2.$$

The empty matching gives Condition 3; matchings with one, two and more edges give Conditions 4–6. Inputs are uniform over all $2^P$ Boolean strings, including those arising from no matching. Write $w_P(s)$ for the fraction of these inputs won by a deterministic strategy $s$, and $W_P(\mu)=\sum_s\mu(s)w_P(s)$ for a nonnegative weight function of total mass one on all deterministic strategies.

Issue [#26289](https://github.com/the-omega-institute/trureturing/issues/26289) fixes the reading: for every odd $P\ge3$, every such $\mu$ satisfies $W_P(\mu)\le1-F_{P-1}/2^P$, and some deterministic $s$ attains equality. This is proved.

## Motivation

The paper compares classical performance with a cluster-state quantum strategy and with strategies using states in a symmetry-protected topological phase. The conjecture determines the exact classical benchmark for the polygon games, rather than only the success probability of one explicit classical strategy. Allowing both shared randomness and input-dependent middle outputs makes the benchmark apply to arbitrary classical local response tables.

## Gap

The bounded literature check recorded in #26289 reports:

- the arXiv v2 source retains the conjecture;
- the citing works examined through OpenAlex record W4315785039 did not settle the equality;
- the orchestrator's reading of Liu–Bulchandani, arXiv:2512.16654, and web searches for the classical value and Fibonacci bound found no settlement;
- the repository and Zenodo searches found no existing settlement record.

The source passage is directly checked; the other reported readings and searches are bounded evidence, not an exhaustive literature survey. `not-found-in-searched-scope`.

## Route

Fix an odd $P\ge3$ and a deterministic strategy $s$. All parity arithmetic below is in $\mathbb Z/2$; the named helpers are private declarations of the module.

1. **Discard parity violations.** If $s$ is not `locallyLegal`, meaning that some player returns an odd-parity triple for some input bit, `local_violation_half` gives at least $2^{P-1}$ losing inputs. If $s$ is not `fixedMiddle`, meaning that some player's middle bit changes with the input, `varying_middle_half`, with $P\ge3$, gives the same bound. If the middle bits are fixed and their sum on input $0$ is nonzero in $\mathbb Z/2$, `odd_middle_all` says that all $2^P$ inputs lose. The reused `FibonacciRankEulerTail.fibonacci_lt_two_pow` bounds $F_{P-1}$ by $2^{P-1}$, so these cases suffice for the required loss bound.
2. **Express the matching condition affinely.** Suppose $s$ is locally legal and has fixed middle bits $b_i$. Put $A=\sum_i a_i$, $t_i=a_i+d_i$, and $q_i=1+t_i+t_{i+1}+b_{i+1}$, the module's `baseline` and `edgeCharge`. For every $M$ satisfying `IsMatching P M`, `affine_matching_rule`, under precisely these local-legality and fixed-middle hypotheses, identifies the matching equation with $A+\sum_{i\in M}q_i=0$.
3. **Find a marked edge.** When $P$ is odd and $\sum_i b_i=0$, `marked_edge` gives an edge $j$ with $q_j=1$: summing the charges cancels every $t_i$ twice and leaves $P+\sum_i b_i=1$.
4. **Keep distinct inputs distinct.** For odd $P\ge3$, `matching_input_injective` says that two matchings $M,N$ with $x_M=x_N$ are equal. Let `avoiding P j` be the matchings containing none of the edges $j-1,j,j+1$. For $P\ge3$, an edge $j$ and $N$ in this family, `insert_avoiding` proves that both $N$ and $N\cup\{j\}$ are matchings and their inputs have different bits at vertex $j$.
5. **Pair and count losses.** For odd $P\ge3$, a locally legal fixed-middle strategy, and an edge $j$ satisfying $q_j=1$, `pairing_losses` injects `avoiding P j` into the losing inputs: at least one input of each pair $N,N\cup\{j\}$ loses. For every $P\ge3$ and $j\in\mathrm{Fin}\,P$, `avoiding_count` gives $|\operatorname{avoiding}(P,j)|=F_{P-1}$ by a bijection with Boolean words of length $P-3$ having no adjacent ones, reusing `AdmissibleCount.admissibleWord_card_eq_fib`. Together with the parity cases, `deterministic_losses` gives at least $F_{P-1}$ losses for every strategy when $P$ is odd and $P\ge3$.
6. **Attain the bound.** The strategy `attainingStrategy` returns $(1,1,0)$ on both inputs at players $1,\ldots,P-1$, and returns $(0,0,0)$ on input $0$ and $(1,0,1)$ on input $1$ at player $P$. For odd $P\ge3$, `attaining_charges` proves local legality, fixed middle bits of even total parity, $A=0$, and exactly one charge equal to one. Under the same hypotheses on $P$, `attaining_losses` gives at most $F_{P-1}$ losses, and `attainment` combines this with `deterministic_losses` to obtain the exact winning fraction.
7. **Allow shared randomness.** For odd $P\ge3$ and a weight function $\mu$ with $\mu(s)\ge0$ for every strategy and $\sum_s\mu(s)=1$, `mixture_bound` averages the deterministic upper bound using the reused `BargmannImaginaryMaximizers.Fourier.weighted_edge_bound`. `result : claim` combines this with deterministic attainment.

## Falsifier

The proof would not answer the conjecture if it changed the game or optimized over too small a strategy class. The module's `IsMatching` excludes consecutive selected cycle edges, which for $P\ge3$ is exactly disjointness of their endpoints. `matchingInput` records those endpoints, and `wins` imposes all matching equations compatible with the actual input, together with both parity conditions. Inputs coming from no matching retain the parity conditions; they are not automatically losses when two specified players receive input $1$.

The strategy type is the full set of Boolean response tables, including tables violating local parity and tables with input-dependent middle bits. `winProbability` is a finite weighted sum over these tables, with nonnegativity and normalization imposed by `claim`. The result asserts both an upper bound and a deterministic attaining strategy, rather than a bound on a possibly empty or unbounded supremum. It concerns uniform inputs and odd $P\ge3$.

## Evidence

The canonical source is `D5/S3/QuantumBounds/PolygonGameClassicalValue.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/PolygonGameClassicalValue.lean.json`.

Declaration statements:

- `result`: `sha256:7c43bb1d76d5ac7d9bd410793486c98793f5bd91091646a4f6e9c15ead6ada12`;
- `claim`: `sha256:eda1b1c0af965756bc0bb0b27fe82b03248f717a139824735489e12fa0574015`.

## Triage

Tier 1 conjecture of a 2022 preprint kept in the 2023 journal version, preregistered in issue #26289 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every odd natural number $P\ge3$, every nonnegative real weight function on all deterministic local response tables whose weights sum to one has `winProbability` at most $1-F_{P-1}/2^P$, and there exists a deterministic response table whose fraction of winning Boolean inputs is exactly $1-F_{P-1}/2^P$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and sharpness.* For odd $P\ge3$, a locally legal strategy with fixed middle bits of even total parity has a marked edge by `marked_edge`; with that edge's charge equal to one, `pairing_losses` applies under the same local-legality and fixed-middle hypotheses. For $P\ge3$ and any edge $j$, `avoiding_count` counts the remaining compatible choices along a path. This explains the Fibonacci number as a compatibility count. The explicit attaining strategy concentrates its nonzero charge on one edge; the argument does not classify all optimal strategies.
- *Why oddness matters.* For even $P\ge4$, assign $(1,1,0)$ on both inputs to every player. Each local parity is even and the middle parity is $P$, also even. For a matching with $r$ edges, the matching sum is $r+(P-2r)$, which has parity $r$. Thus every input wins. This directly verifies the even-case strategy displayed in the source, `ArxivResub.tex`, lines 685–691, but is not a conclusion of `result`.
- *A nonuniform extension with a limited conclusion.* For odd $P\ge3$, `deterministic_losses` gives at least $F_{P-1}$ losing inputs for every deterministic strategy. Consequently, if a probability law on inputs assigns each input mass at least $m\ge0$, every strategy loses with probability at least $mF_{P-1}$. Averaging against any nonnegative normalized strategy distribution independent of the input law preserves this bound. The argument gives a bound, not an exact optimum for arbitrary nonuniform input laws; that optimum remains open here.
- *The large-player limit.* With $\phi=(1+\sqrt5)/2$, the Fibonacci recurrence and $\phi^2=\phi+1$ give $F_n\le\phi^{n-1}$ for $n\ge1$ by induction from $n=1,2$. Hence $0\le F_{P-1}/2^P\le\phi^{-2}(\phi/2)^P\to0$. The source's conclusion that the classical value tends to one along odd $P$ (`ArxivResub.tex`, lines 717–725) already follows from its lower bound and the probability upper bound one; the settlement additionally makes the finite-$P$ deficit exact. This limit argument is not formalized in the module.
- *Effect on the paper and remaining bridges.* Section 4.2 compares an approximate quantum winning probability with the classical lower bound (`ArxivResub.tex`, lines 775–815). The conjectural classical benchmark is now exact for the uniform-input $P$-player game. Applying it to the $N$-player inscribed game still requires the separate classical-value equivalence asserted in Section 4.1, line 755, which this module does not formalize. The factorization estimate for string correlations, the approximation to the quantum winning probability, the claimed threshold behaviour and the conclusion about states away from the cluster-state fixed point are not established by this settlement. Nor does it settle the paper's separate claim that a perfect quantum strategy does not uniquely determine the cluster state.

## ASSUMED-UNVERIFIED

The literature check is limited to the scope reported in #26289 and does not establish exhaustive novelty or priority. The citation readings reported there were not independently reproduced: Hart et al., PRL 134, 130602 (2025); Herringer et al., PRX Quantum 6, 040314 (2025); arXiv:2412.14288v1, 2502.13218v2, 2410.07321v1, 2403.04829v1, 2410.02716v1 and 2604.07451v1. The orchestrator's reading of Liu–Bulchandani, arXiv:2512.16654, its latest-version check, and the reported web, repository and Zenodo searches were not independently reproduced.

The orchestrator's exhaustive computation for $P=3,5$ was not reproduced; it is attributed to #26289. The search contributor's reported random-strategy checks for $P=3,5,7,9$ and affine-form minimization for odd $P\le19$ were not reproduced and are not used as formal evidence. The statements labelled "Argued, not formalized" carry no additional formal conclusion beyond the cited declarations. The even-case verification, the nonuniform bound, the Fibonacci limit argument, the inscribed-game equivalence, quantum strategies, SPT estimates, noise thresholds and characterization of all optimizers are outside `result`.
