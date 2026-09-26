---
bibkey: scottsokal2003repulsive
authors: "Alexander D. Scott; Alan D. Sokal"
year: 2003
title: "The repulsive lattice gas, the independent-set polynomial, and the Lovász local lemma"
doi: 10.48550/arXiv.cond-mat/0309352
url: https://arxiv.org/abs/cond-mat/0309352
claim: "For the hard-core independence polynomial, the positive component in the negative orthant characterizes simultaneous positivity on all induced vertex subsets."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# A positive ray certifies all induced subgraphs

The inspected version is [v2](https://arxiv.org/html/cond-mat/0309352v2),
dated 16 September 2004; first version 2003. Checked 16 September 2026.
Theorem 2.10(a) and (b′), with hard-core self-repulsion, identifies a
positive path from zero to a negative weight vector with positivity of
every induced-subset polynomial.

Consequently, if `Z_V(t)` is positive for all `0 <= t <= 1`, then every
`Z_U(1)` is positive. The [Erdős #7 dossier](../../Problems/erdos-7-odd-covering-systems.md)
also gives a finite deletion-recurrence argument for this specialization.
Positivity only at the endpoint is insufficient. This criterion alone does
not establish the required ray positivity for arbitrary congruence families.

## Conditional avoidance under the same source

Theorem 4.1(a), equation (4.3), of the same v2 was checked against the
original PDF on 20 September 2026. If the event-probability bounds satisfy
the theorem's conditional non-neighbor hypothesis (4.1) and lie in its
strict region R(G), then, for any event-index sets Y and Z,

    P(avoid Y | avoid Z) >= Z_G(-p 1_(Y union Z)) / Z_G(-p 1_Z) > 0.

Product-coordinate independence supplies (4.1) for events whose dependency
graph joins overlapping coordinate supports. The strict-region condition
must still be proved for the particular bounds; a positive value of the
full polynomial alone is insufficient. This ratio concerns conditional
avoidance in the same original probability space, not a resampling output
law. The [coupled first-root result](../../docs/reports/erdos7-odd-covering/problem-details/21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
uses it after checking the complete support-polynomial region for one
specified block and its descendant-domain bounds.

Citation and source-boundary note only; no source text or code is vendored.

## Literal laminar conflicts under actual conditioning

The same Theorem 4.1 permits any graph satisfying its lopsided hypothesis
(4.1), as its Remark 1 explicitly states. For product laws on complete
prime-power coordinates, a coordinatewise conditioning coupling preserves
all compatible literal prefix events: compatible prefixes are nested.
Thus the residue-conflict graph satisfies (4.1), even when the digits
inside a coordinate are dependent. An independent rare query coordinate
and (4.3) then give a query ratio for the actual law conditioned on
avoiding the original events. The complete argument and its strict-region
premise appear in [the laminar-prefix application](../../docs/reports/erdos7-odd-covering/problem-details/24-laminar-prefix-conflicts-under-actual-conditioning.md).
This is an application of the cited theorem; it neither identifies the
conditional law with a resampling terminal law nor supplies universal
strict feasibility for AP families. The v2 primary theorem and Remark 1
were checked on 20 September 2026.

## Ratio monotonicity and virtual upper response tables

Proposition 2.26(b), equation (2.74), and Corollary 2.27(c) of
[v2](https://arxiv.org/pdf/cond-mat/0309352v2), printed pages30–31, were
checked against the original PDF on26September2026. Write
`p(x)=Z_W(-x)` for a hard-core independent-set polynomial. If
`0<=x<=y` and every induced polynomial at `y` is strictly positive, then
Theorem2.10(b′) puts `y` in `R(W)`, and Proposition2.26 yields

    p(lambda x)/p(x) <= p(lambda y)/p(y),   0<=lambda<=1.

Corollary2.27(c) is an equivalent multiplicative route, but its function
is the nonnegative extension defined in(2.75): it equals the raw
polynomial only in the strict region. Full-polynomial positivity alone
is insufficient, and zero boundary denominators do not permit this
ratio argument.

For the graph `L(K5)`, independent sets are matchings of at most two
edges. If `lambda_T` retains only edges disjoint from the queried
coordinate set `T`, and both response tables use the same positive
coordinate masses `Z_q`, then

    x_e=beta_e/(Z_q Z_s),
    H_T=product_(q notin T) Z_q * p(lambda_T x).

Increasing all edge caps from `beta` to `beta_plus` within the strict
region gives `r=H_empty_plus/H_empty` in `(0,1]`, exact empty-support
mass `r H_empty=H_empty_plus`, and simultaneous bounds
`r H_T<=H_T_plus`. Multiplying one actual source by this same cellwise
`r` preserves its domination and all queries. If `r` is independent of
weak-marker indices, it also preserves both weak-marker priority
inequalities. A virtual cap need not itself be a globally realizable
phase layout. Positivity of its complete charged gate remains a separate
obligation; this comparison does not supply it.

For the0/1 masks needed here, the ratio monotonicity also follows from a
finite deletion induction. Let `q_A` be the induced polynomial and
`R_(A,v)=q_A/q_(A\{v})`. The recurrence

    q_A=q_(A\{v})-x_v q_(A\N_A[v])

and a successive deletion of the neighbors of `v` express
`R_(A,v)=1-x_v/product R_smaller`. Induction on `|A|` proves
`R_(A,v)(x)>=R_(A,v)(y)>0` whenever `x<=y` and all induced polynomials
at `y` are positive. This also proves positivity at `x`. Telescoping
reciprocals over deleted vertices gives `q_B(x)/q_A(x)<=q_B(y)/q_A(y)`
for `B subset A`. This is an elementary verification of the cited
specialization, not a new originality claim or a proof for arbitrary
fractional `lambda`.
