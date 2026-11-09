---
slug: barker-2018-oeis-a299285-tea-coordination-sequence
bibkey: barker2018a299285
doi: null
url: https://oeis.org/A299285
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/TeaCoordinationSequence.result
---

# Barker's coordination formulas for the tea slab graph

## Problem

Colin Barker's 2018 formulas occur in N. J. A. Sloane's OEIS entry A299285, *Coordination sequence for "tea" 3D uniform tiling*. The source is an OEIS entry, without a DOI or an arXiv version. Its plain-text representation at [the source endpoint](https://oeis.org/search?q=id:A299285&fmt=text), revision 25, has the following verbatim text in its five consecutive `%F` records, lines 15–19:

> From _Colin Barker_, Feb 11 2018: (Start)
> G.f.: (1 + 8*x + 14*x^2 + 17*x^3 + 14*x^4 + 8*x^5 + x^6) / ((1 - x)^3*(1 + x)*(1 + x^2)).
> a(n) = 2*a(n-1) - a(n-2) + a(n-4) - 2*a(n-5) + a(n-6) for n>6. (End)
> [I suspect Barker's formulas only conjectures. - _N. J. A. Sloane_, Jun 12 2024]
> If the above formulas are true, then a(n) = (31 - 3*(-1)^n + 126*n^2 + 4*A056594(n))/16 for n > 0. - _Stefano Spezia_, Jun 08 2024

OEIS A056594 defines the period-four sequence $1,0,-1,0$. Issue [#26493](https://github.com/the-omega-institute/trureturing/issues/26493) fixes the graph reading of Spezia's closed form. The vertices are $(i,j,k)\in\mathbb Z^3$. In each layer, the six horizontal edge differences are $(1,0)$, $(-1,0)$, $(0,1)$, $(0,-1)$, $(1,-1)$ and $(-1,1)$. An edge from layer $k$ to layer $k+1$ has horizontal shift in

$S_k=\{(0,0),(1,0),(0,1)\}$ if $k\equiv0\pmod4$;

$S_k=\{(0,0),(-1,0),(0,-1)\}$ if $k\equiv2\pmod4$;

$S_k=\{(0,0)\}$ if $k$ is odd.

All edges are undirected. Let $a(n)$ be `shell n`, the natural cardinality `Set.ncard` of the vertices at graph distance exactly $n$ from $(0,0,0)$ in `teaGraph`. The proposition `claim` says that, for every positive natural number $n$,

$8a(n)=63n^2+c_r$, where $r=n\bmod4$ and $(c_0,c_1,c_2,c_3)=(16,17,12,17)$.

The module proves `result : claim`. The [literature note](../Library/StatisticalMechanics/barker2018a299285.md) records the source and its geometric interpretation.

## Motivation

A coordination sequence counts the sizes of successive distance spheres in a net. The source supplies a rational generating function and recurrence for the tea tiling, but labels their status conjectural. An exact graph metric and a count of every sphere replace finite agreement with an all-radius formula for the specified combinatorial model.

## Gap

The bounded literature check in #26493 records:

- the OEIS entry retains Sloane's conjecture remark and Spezia's conditional formula; revision 25 also retains them in the directly read source;
- the search seat reports no proof of A299285 in Goodman-Strauss–Sloane (2018 preprint, arXiv:1803.08530v3) or Inoue–Nakamura (2023 preprints, arXiv:2305.08177v2 and arXiv:2310.19569v2);
- its repository search reports no duplicate settlement of A299285 or A299286; #26425 concerns the distinct tsi net, A299289.

`not-found-in-searched-scope`. The named-paper readings are reported by the search seat in #26493, rather than independently reproduced readings.

## Route

All divisions of integers below are floor divisions. For every integer layer $k$, write $p_k=$ `plusSlabs k` and $q_k=$ `minusSlabs k`. If $k\ge0$, these are $\lfloor(k+3)/4\rfloor$ and $\lfloor(k+1)/4\rfloor$; if $k<0$, they are $\lfloor(-k+2)/4\rfloor$ and $\lfloor(-k)/4\rfloor$. The lemma `slabs_nonneg` gives $p_k,q_k\ge0$ for every $k$.

For integers $i,j,p,q$, define the residual used in the module by

$\rho(i,j;p,q)=\max(0,i-p,j-p,i+j-p,-q-i,-q-j,-q-i-j)$.

For all integers $i,j,p,q,d$, `residual_le_iff` identifies $\rho(i,j;p,q)\le d$ with $d\ge0$ and $-q-d\le i,j,i+j\le p+d$. The natural-valued `potential` is $\Phi(i,j,k)=|k|+\rho(i,j;p_k,q_k)$, with the nonnegative residual converted by `Int.toNat`.

1. **Exact distance.** For adjacent vertices $u,v$, `potential_step` gives $\Phi(u)\le\Phi(v)+1$. For integers $i,j,k,p,q$ with $p,q\ge0$ and $\rho(i,j;p,q)>0$, `residual_descent` gives a neighbour $(a,b,k)$ of $(i,j,k)$ whose residual is exactly one less. For integers $i,j,k$ with $k\ne0$ and $\rho(i,j;p_k,q_k)=0$, `inside_descent` gives a neighbour whose potential is exactly one less. These combine in `potential_descent`: every vertex $v$ with $\Phi(v)>0$ has such a neighbour. Strong induction gives `geodesic`, a walk of length $\Phi(v)$ from the origin to every vertex $v$. The edge bound and this walk give `distance_formula`, namely $\operatorname{dist}((0,0,0),v)=\Phi(v)$ for every $v\in\mathbb Z^3$.
2. **Horizontal counts.** For integers $p,q\ge0$, `hexagon_card` counts the integer pairs with $-q\le i,j,i+j\le p$: twice their cardinality is $p^2+4pq+q^2+3p+3q+2$. Under the same hypotheses, `region_shell_zero` gives this count for residual zero. For integers $p,q\ge0$ and a positive natural number $d$, `region_shell_pos` gives the integer cardinality $3(p+q)+6d$ for residual exactly $d$, by subtracting nested hexagons.
3. **Layer sum.** For every natural number $n$, `layer_sum` identifies the distance sphere with a finite image of the horizontal shells and gives $a(n)=\sum_{k=-n}^{n}|\operatorname{regionShell}(p_k,q_k,n-|k|)|$. Thus `Set.ncard` counts a finite sphere. For every natural number $m$, `paired_slabs` gives $p_m+q_m+p_{-m}+q_{-m}=m$. For positive natural $n$, `weighted_layer_sum` uses the horizontal counts and paired layers to evaluate eight times the sum as $60n^2+4Q_n+16$, where $Q_n=p_n^2+4p_nq_n+q_n^2+p_{-n}^2+4p_{-n}q_{-n}+q_{-n}^2$. For positive natural $n$, `period_four_sum` evaluates this expression under each hypothesis $n\bmod4=r$, for $r=0,1,2,3$, giving the four constants in `claim`.

## Falsifier

The theorem would not settle the source's geometric question if `teaGraph` were not the edge graph of its tea tiling. The precise shifts and specified origin above are part of the formal statement; identifying this integer slab model with Grünbaum's tiling #4 and the RCSR tea net is not formalized. Agreement of finite coordination sequences does not establish that identification or an all-root statement.

There is no disconnected-vertex convention hidden in the count: `geodesic` constructs an origin-to-$v$ walk for every vertex $v$, and the proof of `layer_sum` gives a finite representation of every sphere. The hypothesis $n>0$ in `claim` is essential to its displayed formula; it makes no assertion at $n=0$.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/TeaCoordinationSequence.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/TeaCoordinationSequence.lean.json`.

Declaration statements:

- `result`: `sha256:f4c640110c6824fff2f5a3109392544d81e17b72b95cc90e916354222b1cb3b6`;
- `claim`: `sha256:9bd8849d58a6a5f4c0e8f25f161ee08f124f62412f13643d05015d96fb120ea1`.

## Triage

Tier 1 OEIS conjectural formulas of 2018, preregistered in issue #26493 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every positive natural number $n$, the natural cardinality $a(n)$ of the distance-$n$ sphere about $(0,0,0)$ in `teaGraph` satisfies $8a(n)=63n^2+16$, $63n^2+17$, $63n^2+12$ or $63n^2+17$ when $n$ has remainder $0$, $1$, $2$ or $3$ modulo four, respectively.

**Computed, not formalized.** None.

**Argued, not formalized**.

- *Decisive mechanism.* The edge estimate is attained: `potential_step` bounds a single step for adjacent $u,v$, while `potential_descent` supplies a decreasing step whenever $\Phi(v)>0$, and `geodesic` reaches every $v$ with exactly that length. This matching of a lower bound with an actual walk makes horizontal hexagon counts sufficient for the exact sphere count, rather than merely a growth estimate.
- *Radius zero and the source formulas.* For every vertex, `distance_formula` gives its distance as its potential. At distance zero it forces $k=0$ and $\rho(i,j;0,0)=0$, whose six inequalities force $i=j=0$. Hence $a(0)=1$ by this argument. Put $e_n=1,0,-1,0$ periodically and $A(x)=\sum_{n\ge0}a(n)x^n$. The positive-radius formula gives $A(x)=\frac1{16}\left(\frac{31}{1-x}-\frac3{1+x}+\frac{126x(1+x)}{(1-x)^3}+\frac4{1+x^2}\right)-1$, using the geometric series and $\sum_{n\ge0}n^2x^n=x(1+x)/(1-x)^3$. Bringing these terms to a common denominator gives precisely Barker's quoted generating function. Its denominator is $1-2x+x^2-x^4+2x^5-x^6$; coefficient comparison in degrees greater than six gives his quoted recurrence. These are formal-power-series arguments, with no analytic convergence premise.
- *Sharpness and scope.* Dividing the four equalities by $n^2$ gives $a(n)/n^2\to63/8$. The correction $8a(n)-63n^2$ has least positive period four: period one is excluded by $c_0\ne c_1$, period two by $c_0\ne c_2$, and period three would force all four residues equal. These exact corrections leave no asymptotic error to estimate for the specified origin. An all-radius formula for other root layers, other slab patterns or other uniform tilings is not supplied by `result`; those extensions remain open here.
- *Effect on dependent source statements.* Spezia's conditional formula is established for this graph. The algebra above also supplies Barker's generating function and recurrence for this graph. These consequences apply to the geometric tea net subject to the stated identification. The source's partial-sum link A299286 is addressed by the identity $\sum_{n\ge0}(\sum_{j=0}^n a(j))x^n=A(x)/(1-x)$, since each $a(j)$ contributes in every degree at least $j$; neither this identity nor an A299286 formula is a separate Lean conclusion.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The named-paper readings in #26493 are search-seat reports not independently reproduced here. Its additional reference to Shutov–Maleev lacks a year and identifier and cannot be resolved to a particular source from that issue. No geometric isomorphism with Grünbaum's tiling #4 or the RCSR tea net is proved or independently checked. Counts from roots in other layers are not proved here. The arguments labelled above are not formalized; in particular `result` does not separately state $a(0)=1$, a generating-function identity, a recurrence, minimal period, an asymptotic limit or a partial-sum formula.
