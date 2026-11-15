---
slug: anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap
bibkey: andersfostergreenwoodgarciakrawzik2025wildnumber
doi: 10.48550/arXiv.2508.06711
url: https://arxiv.org/abs/2508.06711v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result
---

## Problem

Anders, Foster-Greenwood, Garcia and Krawzik, *The Wild Number of an Edge-Colored Graph*, arXiv:2508.06711v1, Section 7, Question 7.5, ask: “How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .” The exact settlement is preregistered in [#20098](https://github.com/the-omega-institute/trureturing/issues/20098).

For every integer $r\ge1$, there is a finite connected simple graph with a surjective four-edge-coloring whose wild number is $5r$, with at least one greedy output, and with every greedy output having $6r$ edges. Thus the additive error is unbounded. The family has ratio $6/5$.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Finite simple edge-colored graph | `SimpleGraph (Fin n)` and edge coloring into `Fin 4` | The existential order and coloring are explicit. |
| Connected, with every color present | `G.Connected` and `Function.Surjective` | No extra hypothesis on a supplied graph is introduced. |
| Wild number | `Greedy.wildNumber` | Least cardinality of a color-connecting edge set. |
| Algorithm 5.10 | `Greedy.IsGreedyStep`, `IsGreedyRun`, `IsGreedyOutput` | Maximal dip first, then maximal lexicographic potential; every tie choice is retained. |
| More than one or two | `Result.claim` for every $r\ge1$ | Optimum $5r$, an output exists, and every output has size $6r$. |
| Nonvacuous universal assertion | Existence of a greedy output | Excludes a conclusion true only because no output exists. |

The source conventions for color-connecting sets, dip numbers, potentials and greedy outputs are the public definitions in `Greedy`; `Result.claim` uses those existing same-delivery definitions.

## Motivation

The question distinguishes a single poor tie choice from a graph on which every tie choice incurs a large error. A connected family with four colors shows that increasing the additive error needs neither more colors nor disconnected components.

## Gap

The preregistration's literature screen identifies only the source's v1 and no journal version. Dawkins, Nappo, Tong and Zimbizi, arXiv:2610.22142v1, Section 3.3.5, give conditional gaps of at least one or two for complete-graph colorings under a saturation hypothesis. The recorded screen does not identify an arbitrary additive gap forced for every tie choice. A student poster by B. Price was unreadable. These are attributed literature readings; completeness is ASSUMED-UNVERIFIED.

## Route

Use the four-colored wheel of Example 5.12. Its five-edge color-connecting set gives the upper bound. The fourth color class has six components, and each inserted edge lowers its component count by at most one, giving the matching lower bound. The finite-state invariant in `WheelCertificate` proves that every greedy output has six edges.

Glue the roots of $r$ copies. `AmalgamGraph.component_count_star_difference` supplies the component-count differences. Within a block, dip numbers depend only on that block's selected edges. `MultisetLex.sort_add_lex_iff` preserves comparisons when the other blocks contribute a common multiset. The private `AmalgamWild.greedy_step_restrict` therefore restricts each global greedy step to a legal step in its block. Color-connected blocks have zero dip and are not selected while another block has positive dip. Each global run is an interleaving of block runs.

`AmalgamWild.amplify` combines the blockwise optimum and output cardinalities. `Relabel` transfers the construction to a finite ordinal, and `Result.result` proves `Result.claim`. The proof chooses order $7r+1$; its public conclusion requires only an existential finite order.

## Falsifier

A legal greedy output of the wheel with cardinality different from six would contradict the finite-state step. A global greedy step whose block restriction is not legal would invalidate the amalgamation argument. A color-connecting set of fewer than $5r$ edges would contradict the lower bound. The compiled settling theorem excludes these outcomes in its formal model.

## Evidence

The settling declaration is `D5.S3.Combinatorics.EdgeLabeling.WildNumber.Result.result`, with type `Result.claim`. Its Scribe theorem node displays the expanded quantified claim and carries the Proved resolution for this dossier. Lean is the mathematical authority; the experiment is finite corroboration.

### Experiments

The source experiment directory is [pinned at `fee5fd5f673a7ff07d7a2b8f5df4792810d3cbe8`](https://github.com/the-omega-institute/trureturing-experiments/tree/fee5fd5f673a7ff07d7a2b8f5df4792810d3cbe8/docs/reports/anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap). The exact `check.py` blob has SHA-256 `583b5ca75466f182823c210ee7b27c2cd8fd4de94c8083801a7d2c948c8a1952`. In the experiments checkout's ignored extraction directory `/Users/auric/trureturing-experiments/.lake/scratch/op-afgk2508-stageb`, command `PYTHONDONTWRITEBYTECODE=1 python3 -u check.py` exits 0. It computes the wheel optimum 5 and all greedy output sizes $\{6\}$; the chain sizes are $\{12\}$ at $r=2$ and $\{18\}$ at $r=3$, on 15 and 22 vertices with 28 and 42 edges. It reproduces Example 5.11's dip and potential tables, optimum 3 and greedy size 3, and verifies that Example 5.12's printed order is legal and terminates color-connected.

The star experiment directory is [pinned at `34215f188cb483c0d1791c8b4e5807817858331f`](https://github.com/the-omega-institute/trureturing-experiments/tree/34215f188cb483c0d1791c8b4e5807817858331f/docs/reports/anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap). The exact `star.py` blob has SHA-256 `8ed18e5fb05414ff2a0a9f968a8c2195bc2a416939981b3edff0e36ad5df57a7` and uses the preceding `check.py` blob. In that same directory, command `PYTHONDONTWRITEBYTECODE=1 python3 -u star.py` exits 0 and computes every tie choice for $r=1,2,3$, giving output sizes $\{6\}$, $\{12\}$, $\{18\}$, respectively. The tested orders are 8, 15, 22 and the tested edge counts are 14, 28, 42. The uniform family statement is proved by Lean rather than inferred from these three cases.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** `Result.result` gives wild number $5r$, existence of a greedy output, and size $6r$ for every output for every $r\ge1$. Its scope is the formal source conventions in `Greedy`.
- **Proved in prose from `Result.result`:** the additive gap is $6r-5r=r$. Given any bound $M$, choose $r=M+1$. In particular, $r=3$ gives gap three. The ratio is $6r/(5r)=6/5$, since $r\ge1$.
- **Proved, kernel-checked mechanism:** `AmalgamWild.amplify` proves additive optimum and exact output size for copies of any connected surjectively colored rooted block with an optimum witness of size $a$, a matching lower bound, and every greedy output of size $b$. Its proof uses the block restriction and common-multiset comparison described above.
- **Proved in prose, broader additive lower bound:** for a finite block with optimum $a$ and every greedy output larger than $a$, let $b$ be the smallest output size. Existence and finiteness give $b>a$. Restricting a terminal amalgamated run to each block gives a terminal block run, so the total has at least $rb$ edges, whereas the optimum is $ra$; the gap is at least $r(b-a)$. This consequence is a prose derivation, not an additional Lean statement.
- **Computed:** the experiment entry gives the exact tested wheel, chain and star readings. These finite checks do not establish a uniform extension; that conclusion is carried by `Result.result`.
- **Open:** whether multiplicative error is bounded over all edge-colored graphs. The constant ratio $6/5$ of this family does not answer that question.
- **Open:** source-owner four-slot escape registration, tracked in [#21209](https://github.com/the-omega-institute/trureturing/issues/21209). Every new public theorem of the eight delivered modules is an audit target; no completed registration is claimed.
- **Integration scope:** eight canonical Lean modules and their eight Scribe mirrors; no judge changes. Source-owner registration remains open under the linked issue.

The source's other proved results keep their stated hypotheses and conclusions. Question 7.5 is a question, so its affirmative answer withdraws no theorem. The source's wheel example is extended to arbitrarily large additive error.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source and follow-up readings above are attributed to the preregistration's producers. No exhaustive novelty claim or unbounded multiplicative approximation claim is made. Four-slot escape registration remains unfinished under the linked issue.
