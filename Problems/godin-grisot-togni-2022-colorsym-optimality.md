---
slug: godin-grisot-togni-2022-colorsym-optimality
bibkey: godingrisottogni2025colorsym
doi: 10.5614/ejgta.2025.13.1.5
url: https://arxiv.org/abs/2209.03436
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result
---

# ColorSym optimality is false

## Problem

Jean-Christophe Godin, Rémi Grisot and Olivier Togni, *On List Coloring with
Separation of the Complete Graph and Set System Intersections*, arXiv:2209.03436v1,
Section 3.1; *Electronic Journal of Graph Theory and Applications* 13(1),
57–74, DOI 10.5614/ejgta.2025.13.1.5, Section 3.1, p. 63:

> We conjecture that this algorithm is optimal (i.e., produces an (L, b)-coloring if K_n is (L, b)-colorable).

The algorithm is ColorSym. An $a$-list assignment associates to every vertex
a set of $a$ integers. An $(L,b)$-coloring assigns a $b$-element subset of
each vertex's list, with disjoint subsets at adjacent vertices. For $K_n$
every pair of distinct vertices is adjacent.

### Statement echo

The binding semantics are recorded in
[preregistration #16679](https://github.com/the-omega-institute/trureturing/issues/16679).
The public definitions and the claim use those expressions. The paper's
vertices $1,\ldots,n$ correspond to Lean's `Fin n` values $0,\ldots,n-1$.

| Source clause | Lean counterpart | Correspondence |
| --- | --- | --- |
| An $a$-list assignment assigns $a$ integers to each vertex. | The `claim` parameters $n,a,b$, the finite integer lists $L$, and the list-cardinality hypothesis. | All natural parameters are quantified, including degenerate cases. |
| Proper intersections are the intersection of selected lists minus the union of the other lists. | `supp` and `Ip`. | A color is selected exactly when its support is the specified set; the empty support contributes no color from the union. |
| A coloring assigns $b$ colors from each list, disjoint on every edge. | `IsColoring` and `Colorable`. | The exact cardinality, list inclusion and pairwise disjointness are all retained. |
| “for each set S with \|S\| = i” in steps of increasing $i$. | `AdmissibleOrder` and `runSupports`. | Every support of size at least two occurs once; sizes are nondecreasing; equal-size order is arbitrary. |
| “Remove a color from Ip(S) and assign it to vj.” | `AdmissiblePick` and `assign`. | Every choice from a nonempty integer pool is allowed; insertion and load increment are explicit. |
| “let j ∈ S be the index for which w(j) is minimum (if more than one j with minimum w, then take the smallest index)” | `best`. | The minimum-load vertices are sorted by index and the first is selected. |
| “If wi ≥ b for each i or i = n + 1, then Stop.” | `stopped`, `runPool` and the terminal case of `runSupports`. | Global stopping is rechecked at each color assignment; exhausting the finite support order implements the terminal step. |
| “Goto Step i until Ip(S) is empty.” | `runPool`. | The pool loses one chosen color per assignment; initial fuel is its cardinality. |
| “Color every proper intersections of sets of size 1: vi gets \|Ip({i})\| colors. Thus wi = \|Ip({i})\|.” | `initial`. | Singleton atoms determine both the initial outputs and loads. |
| “produces an (L, b)-coloring if K_n is (L, b)-colorable” | `colorSym`, `claim` and `result`. | The claim asks for some admissible order and pick whose output contains a valid $b$-coloring; `result` negates it. |

The existential choice of order and pick and the allowance to trim an output
to $b$ colors give the algorithm the weakest favorable reading. Every
admissible execution fails on the witness, so this allowance does not rescue
the conjecture. The fuel parameter, option for an empty support, product
state and shifted indices implement the algorithm; they impose no additional
hypothesis on the public claim. There is no separation bound in the conjecture.

## Motivation

A colorable list assignment can have an ordering of scarce shared supply
that defeats balancing by current load. The four-vertex example isolates
that distinction without changing the paper's list-coloring notion or
its index-based tie break.

## Gap

This is the externally published, author-stated conjecture preregistered as
GGT-1 in #16679, with admission basis
`open-problem-resolution (#16679; Refuted)`. The source statement occurs in
both the arXiv v1 and the journal article. The bounded literature screen
recorded in that issue found no prior resolution; completeness is
`ASSUMED-UNVERIFIED`.

## Route

Take $n=4$, $a=6$, $b=4$ and

$$L_1=\{1,2,3,4,5,6\},\quad L_2=\{1,2,3,4,7,8\},$$
$$L_3=\{5,6,9,10,11,12\},\quad L_4=\{5,6,13,14,15,16\}.$$

The disjoint subsets
$\{1,2,5,6\}$, $\{3,4,7,8\}$, $\{9,10,11,12\}$ and
$\{13,14,15,16\}$ give an $(L,4)$-coloring. The only nonempty proper
intersections are the pair atom $I_p(\{1,2\})=\{1,2,3,4\}$, the triple
atom $I_p(\{1,3,4\})=\{5,6\}$, and the singleton atoms
$I_p(\{2\})=\{7,8\}$, $I_p(\{3\})=\{9,10,11,12\}$ and
$I_p(\{4\})=\{13,14,15,16\}$.

The initial loads are $(0,2,4,4)$. Processing the pair gives
$(1,2,4,4)$, $(2,2,4,4)$, $(3,2,4,4)$, $(3,3,4,4)$.
Processing the triple then gives $(4,3,4,4)$ and $(5,3,4,4)$.
There is only one active support of each size. The private theorem
`forced_order` reduces every admissible order to pair then triple after
discarding empty atoms. The general private theorem `runPool_w` proves
that arbitrary admissible picks have the deterministic load recursion;
`runPool_coherent` identifies these loads with output cardinalities.
The private theorem `every_run_card` gives exactly three colors at paper
vertex 2. The cardinality bound prevents a four-color subset of that output,
and the public theorem `result` proves the negation of `claim`.

## Falsifier

A valid four-coloring contained in an admissible ColorSym output on these
lists would falsify the obstruction. A difference between the literal
source's support order, global stopping, index tie break or integer-list
coloring and the formal definitions would invalidate the source correspondence.
The theorem quantifies over every admissible order and pick; testing two
pick functions alone would not establish it.

## Evidence

The settling declaration is
`D5.S3.ConceptDynamics.GraphColoring.ColorSymOptimalityRefutation.result : ¬ claim`
in [the Lean module](../D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.lean).
The literal definitions and the result are described by its
[Blueprint](../Blueprint/D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.md).
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[The numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/79d222b49e0bc4f062dd55072d900f9569e5a609/docs/reports/godin-grisot-togni-2022-colorsym-optimality)
is pinned to commit `79d222b49e0bc4f062dd55072d900f9569e5a609` of
`the-omega-institute/trureturing-experiments`. In that directory the command
`python3 check.py` exits 0 with `ALL_OK`. The script's SHA-256 is
`04bf0bc6614b7a95d1d0ede7baee2ee2c4ef71019402e73a1088f0ca0f13a0d7`.

For the witness it checks all four list sizes, pairwise intersection sizes
$(4,2,2,0,0,2)$, the displayed coloring, a max-flow colorability check,
and final loads $(5,3,4,4)$ under three tested support orders and two pick
functions (minimum and maximum). For each $m=2,\ldots,12$ it checks
colorability and the vertex-2 load $m+\lfloor m/2\rfloor$ using the
default lexicographic support order and minimum-color pick. The unbounded family and arbitrary choices
for that family are not certified by this computation.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked at the witness.** `witness_atoms`,
  `initial_w`, `afterPair_w`, `afterTriple_w` and `every_run_card` are private
  declarations on `result`'s proof path. The pair supply is allocated partly
  to vertex 1 despite its later triple supply; vertex 2 has no later supply.
  Thus every admissible run leaves vertex 2 with $3<4$ colors. The later
  supply is private relative to vertex 2, rather than a singleton atom.
- **Family — computed for $m=2,\ldots,12$.** Put
  $P=[1,2m]$, $T=[2m+1,3m]$, $Q_2=[3m+1,4m]$,
  $Q_3=[4m+1,6m]$, $Q_4=[6m+1,8m]$ and
  $L=(P\cup T,P\cup Q_2,T\cup Q_3,T\cup Q_4)$, with
  $a=3m$ and $b=2m$. The experiment above finds every tested instance
  colorable and the vertex-2 load $m+\lfloor m/2\rfloor<2m$.
  The universal assertion for all $m\ge2$ remains **open in this delivery**;
  this module contains no Lean theorem of that family.
- **Deficit and slack — open uniformly.** On the tested family the deficit
  is $m-\lfloor m/2\rfloor$. If the unbounded family formula is established,
  that expression grows without bound and no fixed additive slack suffices.
  The finite computations do not prove the uniform conclusion or sharpness
  of the source's symmetry hypothesis.
- **Boundary — published result with a prose check of applicability.**
  Corollary 15 of arXiv v1 (Corollary 3.1 in the journal article) proves
  the symmetrical case. Symmetry requires equal proper-intersection sizes
  on all supports of the same cardinality. Here the singleton sizes are
  $0,2,4,4$, so the assignment is not symmetrical. The refutation does
  not contradict that corollary. The paper's other results that use
  symmetry keep that hypothesis; no change to those results is asserted.
- **Quasi-symmetrical assignments — open.** The source's Section 3.3
  permits same-size atom cardinalities to differ by at most one. The
  singleton sizes here differ by four, so this witness does not settle
  ColorSym optimality on that class.
- **Other balancing rules — open.** Larger-support-first processing and
  balancing by remaining private supply are distinct algorithms. Their
  correctness is not proved or refuted here.
- **Experiment — computed.** The single pinned experiment entry above
  records the script, command, exit code, SHA-256 and exact tested scope.
- **Literature — bounded reading; completeness `ASSUMED-UNVERIFIED`.**
  The source and literature checks recorded by the orchestrator in #16679
  report no citing works from the Semantic Scholar query. Godin–Togni,
  *JGAA* 29(1), DOI 10.7155/jgaa.v29i1.3096, concerns multicoloring
  handles rather than ColorSym. The supplied search record includes
  inaccessible fallbacks (HTTP 402/429); it does not establish exhaustive
  literature coverage or a worldwide priority claim.

## ASSUMED-UNVERIFIED

Completeness of the prior-art screen is unverified. The family for all
$m\ge2$, a uniform deficit without additive slack, optimality for
quasi-symmetrical assignments, and correctness of the alternative balancing
rules remain open here. The four-vertex result requires none of them.
