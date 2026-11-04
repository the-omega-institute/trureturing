---
slug: barker-2018-oeis-a299289-tsi-coordination-sequence
bibkey: barker2018a299289
doi: null
url: https://oeis.org/A299289
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/TsiCoordinationSequence.result
---

# Barker’s coordination formulas for the tsi alternating prism graph

## Problem

N. J. A. Sloane, *Coordination sequence for "tsi" 3D uniform tiling*, OEIS A299289 (2018), records the following conjectures of Colin Barker. The source is the OEIS entry itself. Its plain-text response at `https://oeis.org/search?q=id:A299289&fmt=text`, entry revision 16, has this verbatim `%F` block at lines 14–18:

> Conjectures from _Colin Barker_, Feb 11 2018: (Start)
>
> G.f.: (1 + 6*x + 12*x^2 + 6*x^3 + x^4) / ((1 - x)^3*(1 + x)).
>
> a(n) = (13*n^2 + 4) / 2 for n>0 and even.
>
> a(n) = (13*n^2 + 3) / 2 for n odd.
>
> a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n>4. (End)

The next `%F` line, line 19, records a further conjecture:

> Conjectured e.g.f.: ((4 + 13*x + 13*x^2)*cosh(x) + (3 + 13*x + 13*x^2)*sinh(x) - 2)/2. - _Stefano Spezia_, Jun 08 2024

The graph `tsiGraph` has vertices $(i,j,k)\in\mathbb Z^3$. Within a layer, edges change exactly one horizontal coordinate by $1$ in either direction. Between layers $k$ and $k+1$, every $(i,j,k)$ is adjacent to $(i,j,k+1)$ and also to $(i+1,j,k+1)$ for even $k$, or to $(i,j+1,k+1)$ for odd $k$; all these edges are undirected. Define $a(n)=\operatorname{shell}(n)$ as the natural cardinality of the vertices at graph distance exactly $n$ from $(0,0,0)$.

Issue [#26425](https://github.com/the-omega-institute/trureturing/issues/26425) fixes the reading: for every positive even natural $n$, $2a(n)=13n^2+4$, and for every odd natural $n$, $2a(n)=13n^2+3$. This is the proposition `claim`, proved by `result`. The generating functions, recurrence and partial sums are not conjuncts of `claim`.

The source and its encoding are described in [the literature note](../Library/StatisticalMechanics/barker2018a299289.md). The OEIS entry cites B. Grünbaum, *Uniform tilings of 3-space*, Geombinatorics 4 (1994), 49–56, tiling 12, and links the RCSR `tsi` net; the geometric identification is external to the Lean statement.

## Motivation

A coordination sequence measures the growth of graph-distance spheres in a periodic net. The two formulas replace finite enumerations by an exact answer at every positive radius in the alternating prism graph. Their parity dependence records the alternation of the two slab directions, and determines the ordinary and exponential generating functions and cumulative growth of this model.

## Gap

Issue #26425 records the bounded literature check before any Lean:

- The OEIS entry retains Barker’s formulas as conjectures; the directly read revision 16 also labels Spezia’s exponential generating function conjectural.
- The search-seat readings reported there cover Goodman–Strauss–Sloane, arXiv:1803.08530v3; Inoue–Nakamura, arXiv:2305.08177v2 and arXiv:2310.19569v2; Kopczyński, arXiv:2307.15803v1; and Shutov–Maleev, DOI 10.1515/zkri-2020-0002. The issue reports no settlement of A299289 in that scope.
- The preregistration reports no earlier repository record of this problem.

`not-found-in-searched-scope`. The later-literature readings are attributed to the search seat in #26425, rather than independently reproduced here.

## Route

All lemma names below refer to the settlement module; the helpers are private. The proof treats the specified alternating graph, without quantifying over arbitrary slab-orientation sequences.

1. **Exact distance.** For integers $c,i$, put $\delta_c(i)=(\min(0,c)-i)_++(i-\max(0,c))_+$, where the positive parts are natural-valued as in `gap`. For any integer triple $v=(i,j,k)$, define $\rho(v)=|k|+\delta_{\lfloor(k+1)/2\rfloor}(i)+\delta_{\lfloor k/2\rfloor}(j)$, the module’s `potential`; the divisions at negative layers are integer floor divisions. For any vertices $u,v$ with `tsiGraph.Adj u v`, `potential_step` gives $\rho(u)\le\rho(v)+1$. For any vertex $v$ with $0<\rho(v)$, `potential_descent` supplies an adjacent $u$ with $\rho(u)+1=\rho(v)$. Strong induction gives `geodesic`: every vertex $v$ has a walk from the origin of length $\rho(v)$. Consequently `distance_formula` states $\operatorname{dist}((0,0,0),v)=\rho(v)$ for every vertex $v$.
2. **Rectangle shells.** For all integers $c,e$ and natural $d$, `rectangle_shell_mem` identifies `rectangleShell c e d` with the pairs $(i,j)$ satisfying $\delta_c(i)+\delta_e(j)=d$. For all integers $c,e$, `rectangle_shell_card_zero` counts $(|c|+1)(|e|+1)$ pairs when $d=0$. For all integers $c,e$ and every natural $d>0$, `rectangle_shell_card_pos` counts $2(|c|+|e|)+4d$ pairs. These formulas include degenerate rectangles.
3. **Finite layer decomposition.** For every natural $n$, `layer_sum` gives
   $a(n)=\sum_{k=-n}^{n}\bigl|\operatorname{rectangleShell}(\lfloor(k+1)/2\rfloor,\lfloor k/2\rfloor,n-|k|)\bigr|$, with integer layer indices. Its proof identifies the sphere with a finite disjoint union of these finite sets. For every natural $n>0$, `stack_sum` evaluates this as
   $a(n)+2n=6n^2+2(\lfloor n/2\rfloor+1)(\lfloor(n+1)/2\rfloor+1)$.
4. **Parity.** For natural $n>0$ with `Even n`, `even_formula` gives $2a(n)=13n^2+4$. For natural $n$ with `Odd n`, `odd_formula` gives $2a(n)=13n^2+3$; oddness already implies positivity. `result` pairs these two conclusions.

## Falsifier

The settlement would not answer the registered reading if its graph, center, distance or cardinality differed from that reading. The module explicitly uses the alternating adjacency above, `SimpleGraph.dist` from $(0,0,0)$, and `Set.ncard` of the exact-distance sphere. `geodesic` supplies a walk to every vertex, and the finite-set identification in `layer_sum` prevents an infinite set from being assigned a misleading natural cardinality. The even formula explicitly excludes $n=0$.

The identification of this combinatorial graph with the geometric `tsi` tiling is the source-model correspondence, not a theorem of this module. Likewise, `result` specifies one center; an argument for independence of center is given below with its formalization boundary.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/TsiCoordinationSequence.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/TsiCoordinationSequence.lean.json`.

Declaration statements:

- `result`: `sha256:e2eb358de0c0cbe99f63f2645a9b15b4998f18b1f8df52e1a017f8d126b86adc`;
- `claim`: `sha256:c7a0874a927287cc586ca36c83e22b536b492fbeb1740c3925fbcbdc06ab3826`.

## Triage

Tier 1 conjecture of a 2018 OEIS entry, preregistered in issue #26425 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every positive even natural radius $n$, twice the number of vertices of `tsiGraph` at graph distance $n$ from $(0,0,0)$ is $13n^2+4$, and for every odd natural radius $n$, twice that number is $13n^2+3$.

**Computed, not formalized.** None.

**Argued, not formalized.**

- *Decisive mechanism.* For natural $n>0$, the decomposition in `layer_sum` and the rectangle counts separate two extreme layers, each with $(\lfloor n/2\rfloor+1)(\lfloor(n+1)/2\rfloor+1)$ vertices, from interior integer layers $|k|<n$, each contributing $4n-2|k|$. This explains the `stack_sum` identity for $n>0$: the parity correction comes from the balanced side lengths of the two extreme rectangles. The metric and shell lemmas formalize these ingredients for this graph; there is no formal theorem here for arbitrary nonalternating stacks.
- *Other centers in the same graph.* Horizontal integer translations preserve every adjacency clause. The bijection $F(i,j,k)=(j,i,k+1)$, with inverse $(i,j,k)\mapsto(j,i,k-1)$, also preserves adjacency: it swaps the two horizontal directions and simultaneously reverses the parity selecting the shifted interlayer direction. Composing powers of $F$ with horizontal translations sends the origin to any integer triple. Such graph automorphisms preserve walks, distances and sphere cardinalities, so the origin formulas extend to every center by this argument. That extension is not a conjunct of `result` and is not separately formalized here.
- *Ordinary generating function and recurrence.* `distance_formula`, for every vertex, gives $a(0)=1$: a zero potential forces $k=0$, and then both horizontal intervals are $[0,0]$, forcing $i=j=0$. The two positive-radius formulas combine as $a(n)=(26n^2+7+(-1)^n)/4$ for $n\ge1$. Summing the geometric series and $\sum_{n\ge0}n^2x^n=x(1+x)/(1-x)^3$ gives
  $A(x)=\frac{13x(1+x)}{2(1-x)^3}+\frac7{4(1-x)}+\frac1{4(1+x)}-1=\frac{1+6x+12x^2+6x^3+x^4}{(1-x)^3(1+x)}$.
  The subtraction of $1$ corrects the unified expression at radius zero. Multiplication by $(1-x)^3(1+x)=1-2x+2x^3-x^4$ and comparison of coefficients above degree $4$ gives exactly Barker’s recurrence for $n>4$. These are derivations from the proved formulas and the zero-radius observation, not additional compiled declarations.
- *The further source conjecture.* The same unified expression gives the exponential generating function $E(x)=((26x^2+26x+7)e^x+e^{-x}-4)/4$: use $\sum n^2x^n/n!=(x^2+x)e^x$ and correct the zero-radius term. Writing $e^{\pm x}=\cosh x\pm\sinh x$ yields exactly Spezia’s quoted expression. Thus both source generating-function conjectures and Barker’s recurrence follow for this model by the displayed arguments; they are not separately formalized.
- *Growth and neighbouring questions.* Dividing the two closed forms by $n^2$ leaves $13/2$ plus $2/n^2$ or $3/(2n^2)$, so the quadratic leading coefficient is exactly $13/2$. The parity correction cannot be replaced by a single constant, since both parity classes occur at arbitrarily large radii. The entry links A299290 as its partial sums; cumulative sums of these model shells have ordinary generating function $A(x)/(1-x)$, by interchanging the finite coefficient sums. The separate A299290 entry has not been checked. The other uniform tilings listed by the source are outside the settlement, and no assertion about their sequences follows here.

## ASSUMED-UNVERIFIED

The bounded literature check in #26425 does not establish exhaustive worldwide novelty or priority. Its search-seat readings of the five later works listed in Gap have not been independently reproduced; only their reported search conclusion is used. The OEIS revision 16 conjecture block, including the additional exponential generating function, was read directly from the source.

The geometric identification with Grünbaum’s tiling 12 and the RCSR `tsi` net is not formalized; neither Grünbaum’s paper nor the RCSR realization was independently checked. The claims in “Argued, not formalized” are not additional Lean results. In particular, the all-center extension, generating functions, recurrence, asymptotic statement and cumulative generating function have only the arguments specified above. The companion entry A299290, arbitrary slab-orientation generalizations and the other tilings are not settled here.
