# Circular-arc certificate for a partial MUB constellation

## Mathematical target and result

The actual fixed edge is `(I,H/sqrt(6))` in complex dimension six. The base
matrix remains the exact seed over `Q(i,sqrt(21))`:

```math
b=(-3+4i)/5,\qquad e=(-2+i\sqrt{21})/5,
```

```math
H_0=\begin{pmatrix}
J_3+(b-1)I_3&J_3+(e-1)I_3\\
J_3+(\bar e-1)I_3&-J_3-(\bar b-1)I_3
\end{pmatrix}.
```

For any actual order-six complex Hadamard `H` with

```math
\sigma(H,H_0):=\max_a\sum_j|H_{ja}-H_{0,ja}|\le3/4096,
```

the computer-assisted certificate excludes three complete pairwise MUBs
containing this edge together with two orthogonal vectors unbiased to all three.
The literal set sizes are `(6,6,6,2)`; this is not the convention that suppresses
a redundant final vector in a complete basis. In particular, a quartet is
excluded. The ball contains the whole entrywise neighborhood of radius `2^-13`.
It is still a small neighborhood, not a complete X-family branch cover.

A quantitative version uses unit-entry matrices `U : C^(6x6)` and
`V : C^(6x2)`. Define

```math
D_H(W)=\sum_{a,i}(|(H^*W)_{ai}|^2-6)^2,
\qquad O(W)=\frac1{36}\sum_{i<j}|(W^*W)_{ij}|^2,
```

```math
B(U,V)=\sum_{i,j}\left(\frac{|(U^*V)_{ij}|^2}{36}-\frac16\right)^2.
```

Then the checked inequalities and finite cover imply

```math
\boxed{D_H(U)+D_H(V)+O(U)+O(V)+B(U,V)\ge2^{-16}.}
```

Restricting a proposed fourth complete basis to two columns yields the same
lower bound for the full two-six-frame merit. Coordinate moduli are exactly
one; arbitrary amplitude noise has not been included.

## Why the new enclosure is stronger

Independent Cartesian boxes for the real and imaginary parts of a unit phase
forget their common unit-circle equation. The new checker keeps each relative
phase on an oriented minor arc and uses exact support inequalities before
squaring the sum of the complex amplitudes.

Write `c(t)=(1+it)/(1-it)` and let `t` and `s` range independently in closed
intervals `[tl,th]` and `[sl,sh]`. The relative phase `conj(c(t))*c(s)` lies on
the arc whose endpoints are `conj(c(th))*c(sl)` and `conj(c(tl))*c(sh)`.
Signs multiply both endpoints by the same unit phase.

Arc membership does not rely on a numerical angle. Relative to the lower
endpoint the phase is `c(k1)c(k2)`, with

```math
k_1=(t_h-t)/(1+t_ht),\qquad k_2=(s-s_l)/(1+ss_l).
```

The checker proves both denominators positive, both numerators nonnegative and
`k1*k2<1`. Since

```math
\Im(c(k_1)c(k_2))=
\frac{2(k_1+k_2)(1-k_1k_2)}{(1+k_1^2)(1+k_2^2)},
```

the first wedge inequality follows. The upper-endpoint version proves the
second. Endpoint dot and cross tests restrict the arc to a positive acute
angle. All guards are rational inequalities.

For unit endpoints `l,h`, put `a=l+h` and `q=1+Re(conj(l)h)`. Every arc point
satisfies `Re(conj(a)z)>=q`. In rotated coordinates `l=(1,0)`, `h=(a,b)`, the
identity proving this cap condition is

```math
((1+a)x+by)^2-(1+a)^2-2(1+a)y(bx-ay)
=(1+a)^2(x^2+y^2-1)+y^2(a^2+b^2-1).
```

For a real direction vector `g`, the checker either uses the Cauchy bound
`g.z<=||g||`, with an integer-certified rational square-root upper bound, or
finds an endpoint `v` and rational `lambda,mu>=0` satisfying

```math
g=\lambda v-\mu(l+h).
```

The exact dual identity is

```math
\boxed{
\lambda-\mu q-g\mathbin{\cdot}z
=\frac\lambda2\|z-v\|^2+\mu((l+h)\mathbin{\cdot}z-q)\ge0.
}
```

Bounds for `g` and `-g` enclose each projection. The five relative phase arcs
and the fixed first coordinate are summed in common directions, including the
exact rational center-sum direction. Only then is squared modulus bounded.
No circle critical point, floating-point minimizer, or endpoint guess is trusted.

## Executed finite and global checks

At tube radius `1/16`, residual tolerance `1/128` and candidate tolerance
`tau=1/256`, the replay gives:

| Check | Result |
| --- | ---: |
| Whole-tube overlap pairs, including equal labels | 1830 |
| Possible orthogonality edges | 372 |
| Possible unbiasedness edges | 875 |
| All first six-cliques | 2403 |
| Distinct common-partner sets | 2 |
| Largest common-partner set | 1 |
| First cliques with a nonempty partner set | 1029 |
| Union of possible partner labels | `{5}` |
| Completed compact Cayley charts | 32 |
| Global sublevel boxes | 8750929 |
| Pending / unresolved | 0 / 0 |

The other 1374 first cliques have no partner. These counts concern a conservative
finite relation, not actual completion bases or a complete list of exact roots.
The executable verifier and committed replay records are the source for these
counts; the previous prose value 252 was a transcription error.

For every first clique `C`, the entire set `intersection_(c in C) N_B(c)` has
cardinality at most one. A fourth pair would need two different tube labels,
because every same-tube squared overlap exceeds `3/4`. It therefore cannot
exist. Root existence, root uniqueness and persistence of symmetry are not
used in this implication.

For `tau=1/256`, `sigma=3/4096`, the residual-transfer budget is

```math
\tau+\sigma(5+\sigma)=126985/16777216<1/128.
```

If the total partial-constellation merit were less than `tau^2`, all eight
candidate vectors would enter the covered sublevel, all internal squared
normalized overlaps would be less than `tau^2`, and all cross deviations would
be less than `tau`. Their labels would violate the singleton-partner result.

## Controlled comparison and unsuccessful probes

The comparison must use the SAME centers, tube radius `1/16` and `tau=1/256`.
Its separately executed report records the Cartesian and circular-cap edge
counts and the number of improved interval bounds. This measures enclosure
quality, not the number of actual solutions.

A preliminary anchor mass-conservation filter pruned zero first cliques at the
tested radii/tolerances. It is not advertised as a successful certificate.
A stronger sublevel `1/64` at the same `1/16` tube radius did not complete:
chart 11 exhausted a 1500000-node cap with 32 pending boxes. A larger retry was
interrupted. No claim is made that its sublevel is covered or that the larger
region is mathematically infeasible.

## Reproduction and verification boundary

```sh
python3 scripts/research/check_real_x_arc_constellation.py \
  docs/develop/certificates/real_x_two_relation/centers.txt \
  --output /tmp/arc-constellation --full-cover --jobs 4

python3 scripts/research/test_real_x_arc_constellation.py \
  docs/develop/certificates/real_x_two_relation/centers.txt \
  --cover-reports /tmp/arc-constellation \
  --output /tmp/arc-constellation/tests.json
```

The optional development test needs NetworkX. The accepting checker does not.
It recomputes the whole graph, enumerates every first clique and runs the full
sublevel traversal when `--full-cover` is supplied. It never consumes a stored
success report. Finite-only mode is explicitly labeled as conditional on full
coverage.

The current run also passed 6000 exact rational arc/projection samples, 600
whole-overlap samples, twelve corruption rejections and an independent maximal-
clique enumeration (877 maximal cliques, giving the same 2403 six-cliques).
These are single-author development checks, not independent expert review or
a universal proof of the implementation.

`UnitCircleArcSupport.lean` and its Scribe supply the circular-cap endpoint-dual
mathematical theorem. Lean/lake elaboration was not executed. The full Cayley
arc adapter, interval-expression enclosure, traversal reflection and numeric
partial-constellation instance remain kernel obligations. This result is a
computer-assisted proof subject to that explicit analytic interpretation.

## Literature and cross-project connection

- Stephen Brierley and Stefan Weigert, *Constructing Mutually Unbiased Bases
  in Dimension Six*, Phys. Rev. A 79, 052316 (2009), arXiv:0901.4051:
  joint orthogonality of unbiased vectors is a decisive constraint beyond
  finding individual vectors. Locator: https://arxiv.org/abs/0901.4051
- Stephen Brierley and Stefan Weigert, *Maximal Sets of Mutually Unbiased
  Quantum States in Dimension Six*, Phys. Rev. A 78, 042312 (2008),
  arXiv:0808.1614: MU constellations are the appropriate partial-basis objects.
  Locator: https://arxiv.org/abs/0808.1614
- Mate Matolcsi, Akos K. Matszangosz, Daniel Varga and Mihaly Weiner,
  *Triplets of mutually unbiased bases*, J. Algebraic Combinatorics 63,
  article 26 (2026), published 4 March 2026, DOI 10.1007/s10801-026-01506-x.
  Conjecture 3 explicitly asks to exclude every member of the Szollosi X
  family from a MUB quartet. This local certificate does not settle that
  entire conjecture or the full dimension-six problem.
  Locator: https://doi.org/10.1007/s10801-026-01506-x
- Duff and Lee, arXiv:2402.07053, provides certified Krawczyk continuation
  context. Tracking known roots does not replace full residual-sublevel
  coverage. Locator: https://arxiv.org/abs/2402.07053
- The cross-author audit read loning's #5296 emphasis on combining amplitudes
  before taking squares, and #5895's actual normalized-readout disk source,
  where retaining covariance gives a stronger bound than separate errors.
  The present circle-cap algorithm has its own proof; no unproved RH or Weil
  statement is imported into the MUB argument.

Primary publisher/arXiv metadata were checked on 6 September 2026. The initial
README's attribution of the triplet paper to a different author group, expanded
title and article number was incorrect and has been replaced here.

No priority claim is made for classical circular-cap duality, interval arithmetic
or graph clique bounds. The concrete research output is the replayable stronger
partial-constellation exclusion on the specified ambient Hadamard neighborhood.
