# Reweighting28 actual315 sources releases further old prime heights

There are two finite-height noncoverage consequences.

1. For every finite family of distinct odd numerical moduli greater than1
   dividing

       315*11*13*17*19^H19*23^H23 * product_(i=1)^6 q_i^E_i,

   where the six distinct fresh primes are sorted at least29,31,37,41,43,47,
   the actual uncovered Haar density is strictly greater than

       144433/49258905696 > 1/350000.                    (RW1)

2. For every such family dividing

       315*11*13*17^H17*19^H19*23^H23 * product_(i=1)^5 q_i^E_i,

   where the five distinct fresh primes are sorted at least29,31,37,41,43,
   the actual uncovered Haar density is strictly greater than

       11011445/809559406656 > 1/75000.                  (RW2)

All displayed heights are arbitrary nonnegative finite integers, and all
original phases are arbitrary and fixed globally. Both results retain
v3<=2 and v5,v7<=1 in EVERY original, including fresh-bearing originals.
The first also retains v11,v13,v17<=1; the second retains v11,v13<=1.
These are ordinary finite source-transfer proofs and exact computations.
They do not settle unrestricted Erdős#7 and do not add Lean verification.

## 1. The actual-source choice is made before the future query

Use the established canonical six-shape45 pruning and its315 extension.
Only the first shape changes. Its45 survivor set S has17 points; after
excluding the pure7 root, each of the five nonpure7 labels deletes an
old cylinder at one of six live roots. Missing or inactive labels can
be completed by auxiliary source restrictions, producing a smaller actual
survivor source. This does not alter any original arithmetic phase.

Write b(x) for the number of deleted live roots above x in S and
r(x)=6-b(x). The complete actual catalogue has19324 such vectors b,
partitioned into192 groups by

    N=sum_x r(x),
    M=42+sum_(d in{3,5,9,15,45}) max_(a mod d)
                         sum_(x in S, x=a mod d)r(x).

For the uniform probability on these N actual surviving cells, M/N is
the exact maximum nonunit complete315 query mean. A group is a uniform
bound over its actual sources, not a claim that a maximizing source can
be chosen separately for every later query.

The source-selection rule is fixed as follows.

* In190 groups, namely all except(N,M)=(86,185),(86,184), retain the
  uniform actual315 source and that group's established complete-query law.
* The exceptional groups contain6 and22 vectors b respectively. Match the
  actual vector b to its entry in the fixed28-row rational weight dictionary.
  That entry specifies an old45 marginal probability u_x. On each actual
  surviving7 cell above x assign probability

      mu(x,y)=u_x/r(x).                                (RW3)

* In the other five canonical45 shapes, retain the already verified
  pruned315 source, hinge law and Haar domination bound.

Thus exactly223 source contracts cover all cases:190 uniform groups,
28 explicitly reweighted supports, and five inherited shapes. Source
selection depends only on the same actual original configuration.
It is never selected again for a hinge, auxiliary multiplier, fresh field
or favorable continuation. The labels N,M identify the original uniform
support class; after reweighting, the actual query mean is computed again.

The weights are nonnegative rational numbers summing to1. Numerical linear
optimization was used only to propose them. Their feasibility, each actual
cylinder reading and every later inequality are checked exactly; no claim
of LP optimality is needed. The dictionary is explicit in the fixed rational weight data, and the
source vector b identifies its row unambiguously.

## 2. Complete convex-query control survives the reweighting

At most five live7 roots are used by the original deletions, so one live
root remains untouched above the whole set S. The law(RW3) gives the same
cell weight w_x=u_x/r(x) to every surviving row above each fixed x.

Write a complete315 query as its zero-seven complete45 block A and its
positive-seven query slots. For increasing convex phi, concentrating all
positive-seven slots on the untouched row, with their old phases unchanged,
does not decrease the reading. At each x, this follows from the
superadditivity of phi(A+v)-phi(A) in nonnegative increments v. Multiplying
by the common w_x preserves the pointwise inequality.

Consequently its exact maximum is

    max_Q E_mu phi(Q)
      = max_(A,B) sum_x w_x
          [(r(x)-1)phi(A(x))+phi(A(x)+B(x))].            (RW4)

Both A and B are genuine complete45 queries on the same points x. There
is no independent sorting, movement of old phases, or free replacement
of actual original constraints. The query phases in(RW4) are test parameters,
not reselected original phases.

There are4760 distinct A layouts and4760 B layouts. For each of the28
fixed weighted sources, the native exact consumer evaluates all22657600
ordered pairs and their12 hinge readings. Integer weights are obtained by
clearing the exact cell-probability denominators. The returned envelopes

    H(t)=max_Q E_mu(Q-t)_+, t=0,...,11,

have H(0)-H(1)=1 and H(12)=H(13)=0. The consumer verifies that

    P(Y=y)=H(y-1)-2H(y)+H(y+1), y=1,...,12,

is nonnegative, sums to1, and reproduces every hinge. It follows that
EVERY complete315 query on this same weighted actual source is dominated
in increasing-convex order by the corresponding genuine law Y.

The six formerly worst185 sources have nonunit means and Haar caps

| Source IDs | c=E Y-1 | D315 |
|---|---:|---:|
|0,2|3383/1800|21/2|
|1,3|1811/938|1275/134|
|4,5|239/126|75/7|

For the22 sources in group184, c ranges from50659/27000 to6845/3612;
the largest D315 is2415/229. The individual exact values, weights and
hinge laws are retained, not replaced by these summary ranges.

In every case the actual probability obeys

    mu<=D315 Haar315,
    D315=315 max_x(u_x/r(x)).                           (RW5)

This replaces the old uniform cap315/N on a reweighted branch. Borrowing
that old cap would be invalid. A zero u_x is allowed: it simply chooses a
smaller supported source. Each law remains supported outside every
actual315 original.

## 3. The same actual source is extended through all old heights

Let P={11,13,17,19,23}. Choose J={19,23} for(RW1), and
J={17,19,23} for(RW2). At every p in J use the established root-balanced
actual pure-survivor law: avoid the pure first root, then remove all actual
higher pure powers within each remaining root, assigning equal total mass
to each surviving first root. Its density and cylinder caps are

    rho_p<=p/(p-2) Haar_p,
    u_p(1)=1/(p-1),
    u_p(e)=p^(1-e)/(p-2), e>=2.

At p outside J, the permitted old height is at most1; use the law uniform
on its p-1 live roots. The full carrier includes the old exponents of
fresh-bearing originals as well as old-only originals.

For the chosen315 probability, form ONE product source sigma. Put

    z_p=1/(p-2) if p in J, otherwise1/(p-1),
    D=D315 product_(p in J)p/(p-2)
                 product_(p notin J)p/(p-1).

Restrict sigma ONCE by all actual old-only mixed originals. The nonunit
cofactor query costs at most c=E Y-1 on a singleton outside support;
a larger outside support may also use the unit, with cost c+1.
Distinct numerical labels ensure at most one original per old cofactor
and fixed outside exponent tuple. Summing all actual finite heights using
the deterministic geometric caps gives retained mass at least

    delta=c+2+sum_p z_p-(c+1)product_p(1+z_p)>0.          (RW6)

All223 branches pass this exact positivity check for each of the two J.
For the normalized actual restricted source mu_old,

    (delta/D)mu_old<=Haar_old.                          (RW7)

Each delta, D and ratio is calculated from the SAME selected315 source.
No separately optimal source, reference or normalization is inserted.

## 4. Unbounded auxiliary tails and all fresh fields remain included

For p in J, introduce independent comparison integers N_p with
P(N_p>=e)=u_p(e); for p outside J use independent B_p with
P(B_p=1)=1/(p-1). They are also independent of Y. The raw comparison is

    Z=Y product_(p in J)(1+N_p) product_(p notin J)2^B_p.

The event-increment and Jensen argument applies the315 query bound to
EACH fixed auxiliary query slot before averaging those auxiliary variables.
Thus every complete full-old query on sigma is increasing-convex dominated
by Z, even when different exponent slots select different315 queries.
The independence belongs to this comparison construction, not to the
actual mixed originals or their eventual restriction.

Choose one upper-delta quantile t of Z, with

    P(Z>t)<=delta<=P(Z>=t).

For any increasing convex phi, every full old query on mu_old satisfies

    E phi(Q)<=phi(t)+E(phi(Z)-phi(t))_+/delta.

Equivalently, one genuine upper-tail law V dominates every such query.
The quantile can vary with the selected source branch; it cannot vary
with a later query within that branch. The exact consumer computes it
from finite low atoms and includes the entire geometric tail analytically.

Every nonempty fresh support has its actual geometrically weighted finite
query field, with constant-one padding for missing layers. Jensen transfers
the same comparison to all63 fields of(RW1), or all31 fields of(RW2).
The original exponent tuples, numerical labels and phases remain fixed.
No independence between these fields is required.

## 5. Two existing scalar gates close the two source budgets

For(RW1), reuse the complete six-direction gate with capacities

    r=(28,30,36,40,42,46), kappa=1/5000, target19100.

For(RW2), reuse the complete five-direction gate with capacities

    r=(28,30,36,40,42), kappa=1/125, target18000.

Their pair penalty g interpolates squares at the fixed18 knots through384
and continues with slope640. All conjugate arguments remain below640
(the six-direction maximum is503.685, the five-direction maximum447.72).
Therefore both scalar inequalities hold for unbounded old-query fields;
no artificial upper cutoff384 is reintroduced by the old height lifts.

Each scalar gate has the pointwise form

    kappa W+F(C)>=target.

Here F charges every unary, pair and higher-support field on the same
source, and W is the actual carving response. Taking expectations and
using(RW7) gives

    Haar(full survivors)
       >=(delta/D)[target-E F(C)]_+/(kappa product r).   (RW8)

The exact consumer evaluates all223 actual source contracts for each
scope, retaining branch identities, delta, D, delta/D, the common quantile,
and a certified rational cost ceiling. Cost ceilings are upper bounds,
not claims that the arithmetic source attains them. The retained data use
integer ceilings obtained from exact rational calculations, avoiding
repeated thousand-digit intermediate fractions.

| Scope | Global strict fee bound | Minimum paired delta/D | Margin |
|---|---:|---:|---:|
|19,23 full; six fresh|18974|288866/26558675|126|
|17,19,23 full; five fresh|17420|151882/15935205|580|

The worst fee is now the unchanged uniform source group(85,181), with
respective bounds18973.122388266187... and17419.122947657448... . The28
reweighted branches and all five other canonical shapes pass separately.
The minimum Haar factors come from reweighted branches; they are never
computed using the old uniform density cap. For the displayed conservative
bounds, each branch has both h>=the listed minimum and fee below the listed
uniform ceiling, so their product in(RW8) has the stated positive bound.

Inserting the constants gives

    (288866/26558675)*126*5000/(28*30*36*40*42*46)
       =144433/49258905696>1/350000,

    (151882/15935205)*580*125/(28*30*36*40*42)
       =11011445/809559406656>1/75000.

The actual fresh-prime capacities may be larger than the reference r.
The established normalized fibre response is nondecreasing in those
capacities, with the actual fields and phases held fixed. This preserves
both bounds at the stated fresh-prime minima and all larger choices.

## Exact artifacts and remaining boundaries

The [actual source catalogue](745-actual-source-catalogues-and-sharp-convex-query-laws.md)
provides all19324 vectors,192 group laws and the complete28-vector
exceptional set. The [fixed rational weights](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_reweighted_source_weights.json)
assign exactly one probability to every vector in that set. No numerical
optimizer is invoked by the final consumer.

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_adaptive_source_continuation.py),
[native weighted query checker](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_reweighted_source_hinges.cpp)
and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_adaptive_source_continuation.json)
verify that source dictionary against the pinned catalogue, reconstruct
every cell probability, compile and run all22657600 query pairs for every
weighted source with undefined-behavior checks, and rebuild all28 genuine
laws. A separate exact cylinder calculation verifies each law's first
moment. The actual Haar cap is computed from the same probabilities.

The consumer then recomputes all446 source/scope rows, complete geometric
tails, common quantiles, fee ceilings and the two uniform Haar conclusions.
It reconstructs the six-direction aggregate coefficients from the pinned
scalar gate and checks them against the existing unbounded interface.
The five-direction gate and old-height source are inherited from
[Report743](743-two-old-full-heights-and-five-fresh-directions.md);
the six-direction gate is inherited from
[Report741](741-an-actual-full-height23-source-supports-six-fresh-primes.md).
Their domain enclosures and the earlier unweighted source catalogue are
not rerun inside this consumer. A stale retained result is rejected.

An independent weighted enumeration matches all336 hinge values. A
separate tail computation uses the exact finite low-end product law and
its analytic first moment to complement the entire infinite tail; it
matches all446 source/scope budgets and the displayed density bounds.
Thus it does not reuse the primary recursive tail algorithm. Independent
checks also verify the source dictionary, normalized probabilities,
all density caps and the final integer fee ceilings.

These are ordinary proofs and exact computations. No LP optimality,
untested extra prime direction, new Lean verification or arbitrary old
3/5/7 height statement is used. Fixed finite original families are covered
at every displayed finite height, with original numerical labels and
phases preserved throughout.

The improvement comes from changing the actual source probability while
preserving its support and all declared query interfaces. On six bad
uniform sources the old convex-query law was already sharp; reweighting
changes that law and its Haar cap together. The remaining old height and
prime-support restrictions require further source or continuation results.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_adaptive_source_continuation.py
```
