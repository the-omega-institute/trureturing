---
slug: teimoori-faal-2021-flat-graph-clique-roots-conjecture-1
bibkey: teimoorifaal2021flat
doi: 10.48550/arXiv.2112.09721
url: https://arxiv.org/abs/2112.09721v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result
---

# A ring of four complete blocks refutes the flat-graph clique-root conjecture

## Problem

H. Teimoori Faal, *On Clique Roots of Flat Graphs*, arXiv:2112.09721v1,
Conjecture 1, page 6, states:

> The class of 2-connected K₅-free flat graphs without isolated triangles has only clique roots. In particular, this class has always the clique root r = −1 of multiplicity 2.

The [source note](../Library/GraphInvariants/teimoorifaal2021flat.md)
contains the definitions and locators. The preregistration is
[#19709](https://github.com/the-omega-institute/trureturing/issues/19709).
The quoted conjecture is **Refuted** by a twelve-vertex graph.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite simple graph | `V`, `Fintype V`, `SimpleGraph V` in `claim` | Arbitrary finite vertex type; undirected and loopless |
| $C(G,x)=\sum_j c_j(G)x^j$, with $c_0=1$ | `cliquePoly` | Integer clique counts from `SimpleGraph.cliqueFinset`; sum through the vertex count, with higher terms zero |
| Every edge is in at most two triangles (Definition 2.2) | `IsFlat` | Counts the common neighbours of each adjacent pair |
| No isolated triangle (Definition 4.1) | `NoIsolatedTriangle` | Every triangle has a common neighbour of all three vertices |
| 2-connected | Existing `D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected` and `3 ≤ Fintype.card V` | Connected before and after deletion of any vertex; more than two vertices |
| $K_5$-free | `SimpleGraph.CliqueFree 5` | No five-vertex clique |
| Has only clique roots | First conjunct of `claim` | Every complex zero has imaginary part zero |
| $-1$ has multiplicity exactly two | Second conjunct of `claim` | `Polynomial.rootMultiplicity (-1) = 2` |
| Implementation instances | `DecidableEq V`, `DecidableRel G.Adj` | Finite graph operations; no additional graph restriction |
| Negative answer | `result : ¬ claim` | The first conjunct fails on one graph satisfying every hypothesis |

## Motivation

Flatness controls the number of triangles through each edge. It still permits
complete four-vertex blocks. Joining four such blocks around a cycle preserves
flatness, removes cut vertices, and changes the clique polynomial from the
cubic setting of the source's $K_4$-free theorem to a quartic.

## Gap

The literature screen recorded in #19709 covers arXiv v1; the author's later
papers arXiv:2205.08133, 2206.02044, 2206.11159, 2206.12306, 2602.18771 and
2602.24151; MathDB; the `google-deepmind/formal-conjectures` snapshot; and
repository owners. No settlement of Conjecture 1 was located in that scope.
The repository's `FaalNonStable` concerns a different marked multivariate
question from arXiv:2602.24151 and is not on this module's dependency path.
Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The [settling module](../D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.lean)
uses the four complete blocks
$\{0,1,4,5\}$, $\{1,2,6,7\}$, $\{2,3,8,9\}$ and $\{3,0,10,11\}$,
with no other edges. Its private certificates verify all graph hypotheses.
The Hamiltonian cycle $(4,5,0,10,11,3,8,9,2,6,7,1)$ supplies a spanning path
after deletion of any vertex. The existing `Biconnected` predicate occurs
in `claim` and private `r4_biconnected`.

Private `cliquePoly_R4` proves

$$C(R_4,x)=1+12x+24x^2+16x^3+4x^4=4(1+x)^4-4x-3.$$

For the corresponding real polynomial $p$, private `p_deriv` gives
$p'(x)=16(1+x)^3-4$. Private `p_deriv_roots_card_le_one` bounds the
number of real derivative roots counted with multiplicity by one.
Mathlib's `Polynomial.card_roots_le_derivative`, used in private `p_not_splits`,
then rules out splitting of the quartic over the reals. Private
`p_has_nonreal_root` uses splitting over the complexes to contradict the
assertion that every complex zero is real. Public `result` applies this to
`claim` without assuming the conjecture's multiplicity clause.

Every proof step is conservatively classified `bind-only`; admission is
`open-problem-resolution (#19709; Refuted)`. No escape witness is claimed.

## Falsifier

The conjecture would force every complex zero of $C(R_4,x)$ to be real,
contradicting private `p_has_nonreal_root` through the coefficient-map bridges.
The witness contains four-vertex cliques, so it supplies no counterexample to
a statement restricted to $K_4$-free graphs.

## Evidence

The only public theorem is
`D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.result`.
The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The auxiliary experiment is in
[trureturing-experiments at commit `78b2e5d7ad07410a01039cfe2087cbfec0d88e6c`](https://github.com/the-omega-institute/trureturing-experiments/tree/78b2e5d7ad07410a01039cfe2087cbfec0d88e6c/docs/reports/teimoori-faal-2021-flat-graph-clique-roots-conjecture-1).
The command
`python3 ../trureturing-experiments/docs/reports/teimoori-faal-2021-flat-graph-clique-roots-conjecture-1/check.py`
exits 0 with `RESULT PASS`; `check.py` has SHA-256
`02d5ed425f9080c8841ebb04f5a47b0a51b11956eac4ca5dcd9779076ac4b7b5`.
Its tested scope is exactly $r=4,5,6,7,8$, of orders $12,15,18,21,24$.
For these five graphs it checks 2-connectedness, $K_5$-freeness, flatness,
absence of isolated triangles, clique counts $(1,3r,6r,4r,r)$, two nonreal
numerical roots, and $C(R_r,-1)=1$. The numerical root count is corroboration;
the Lean refutation uses the exact splitting obstruction at $r=4$.

## Triage

| Item | Status and evidence |
| --- | --- |
| Conjecture 1 | **Proved (kernel-checked refutation):** public `result`, with every graph hypothesis and the failure of its main root clause |
| Twelve-vertex graph hypotheses | **Proved (kernel-checked):** private `r4_biconnected`, `r4_cliqueFree`, `r4_flat`, `r4_noIsolatedTriangle` |
| Clique counts for $R_4$ | **Proved (kernel-checked):** private `r4_c0` through `r4_c12`; `cliquePoly_R4` identifies the polynomial |
| Quartic derivative obstruction | **Proved (kernel-checked):** private `p_deriv_roots_card_le_one`, `p_not_splits`, `p_has_nonreal_root` |
| Rings at $r=4,5,6,7,8$ | **Computed:** the pinned experiment entry above; no larger tested range is asserted |
| Uniform ring family for all $r\ge4$ | **Open:** no uniform Lean theorem is delivered |
| Second clause on $K_4$ alone | **Proved in prose:** the binomial clique counts give $(1+x)^4$, so $-1$ has multiplicity four, rather than exactly two |
| Source Theorem 3.1 | **Literature reading:** the source's $K_4$-free theorem is not refuted by this witness |
| Further real-rooted subclass classification (Question 4.2) | **Open:** no classification is delivered |
| Literature status | **Literature reading:** no settlement located in the screen recorded in #19709; completeness `ASSUMED-UNVERIFIED` |

### What the settlement shows

**Proved (kernel-checked):** a 2-connected $K_5$-free flat graph with no
isolated triangles can have a nonreal clique-polynomial root. The exact
quartic and its derivative expose the failure even though each local
triangle condition is satisfied. The graph's four-vertex cliques distinguish
it from the source's cubic $K_4$-free setting.

**Proved in prose:** already $K_4$ has $\binom4j$ cliques of size $j$ and hence
clique polynomial $(1+x)^4$. Its triangles each have the remaining vertex as
a common neighbour, its edges each belong to two triangles, and deleting any
vertex leaves $K_3$ connected. Thus the multiplicity-exactly-two clause also
fails separately. For $R_4$, substituting $x=-1$ into the kernel-checked
polynomial gives $C(R_4,-1)=4\cdot0^4+4-3=1$, so it is not a root.
These substitutions and the $K_4$ comparison are prose consequences, not
additional Lean theorems.

**Literature reading:** Theorem 3.1 states that $K_4$-free flat graphs without
isolated edges have only clique roots and always have the root $-1$.
The witness lies outside that class. The refutation therefore supplies no
contradiction to that theorem; it prevents replacing its $K_4$-free hypothesis
by the conjecture's $K_5$-free hypothesis together with 2-connectedness and
absence of isolated triangles. Any argument that assumes Conjecture 1 needs
a separate valid hypothesis or replacement. No judgement about the source's
other theorems is asserted.

**Computed:** the five finite ring cases have the readings in the experiment
entry. **Open:** a uniform Lean verification for all $r\ge4$ and a sharp
classification of real-rooted subclasses remain outside this settlement.

## ASSUMED-UNVERIFIED

Literature completeness and priority are unverified. Numerical evidence is
restricted to the five tested ring sizes. No uniform Lean family theorem or
general classification is asserted.
