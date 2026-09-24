[Index](../../marked_head_profile.md) · [Synchronized sources](354-synchronized-prime-private-cofactor-matching.md) · [Column heights](355-column-height-matching-bound.md) · [Original private sets](357-original-private-swaps-and-prime-reset-transport.md)

# Synchronized-parent capacities and a shared all-prime surplus allocation

A source whose synchronized tuple varies from point to point can be charged
to genuine original parent intersections without a tuple-count factor.
Across primes, dividing each target point's charge by its actual number of
original prime labels prevents reuse of the covering surplus. The capacities are exact finite CRT
quantities. The source's exclusion of all other prime classes strengthens
the resulting inequality and cancels a support-size loss in a simple bound.

These are ordinary finite capacity deductions. They retain the full original
heights and actual selected sources, but do not construct a coordinate-
preserving return map, remove the synchronized-good-tail loss, or settle
unrestricted Erdős #7. No Lean verification or literature novelty is claimed.

## 1. Actual selected sources and original parent capacities

Use the hypothetical extremal cover and original Haar law H of 357. Its
distinct numerical moduli form a divisor ideal above one; every support
prime is an original label; comparable original classes are disjoint.
Let Lambda be its prime support, Q its complete period, and

    N(y)=number of original labels covering y,
    H_cov=integral (N-1) dH.

For each q, let G_q be any subset of the synchronized-good points in
`Priv_q` from 354. At each source choose one actual matching: q-1 children
`q^e m`, one on every nonprime first-q root, with distinct cofactors m>1.
The choices may vary arbitrarily with the source point. All spaces are
finite, so a deterministic choice is available.

Let S_(q,e,m) contain the source points selecting that particular original
child. For fixed q,m these sets are disjoint over e. Put

    S_(q,m)=disjoint-union_e S_(q,e,m),
    E_(q,m)={e>=1:q^e m is an original modulus},
    alpha_(q,m)=q sum_(e in E_(q,m)) q^(-e).

Only m with a selected child and a genuine original parent A_m are used.
Divisor closure supplies these parents in the hypothetical extremal cover.
For checks on other covers their existence is an explicit premise; it
cannot be replaced by a newly invented AP. Numerical distinctness ensures
that there is at most one original child for each q,e,m.

Each source belongs to exactly q-1 different S_(q,m), hence

    sum_m H(S_(q,m))=(q-1)H(G_q).                     (CA1)

Write the full carrier as `F_q x T_q x X_q`. Moving the original child's
first root to that of A_q, without changing its tail prefix or cofactor
class, gives a cylinder of Haar mass `1/(q^e m)`. The selected set
S_(q,e,m) is a subset of that cylinder. Thus

    H(S_(q,m)) <= alpha_(q,m)/(q m).                  (CA2)

The genuine target is `T_(q,m)=A_q intersect A_m`. Since q does not divide
m, CRT gives `H(T_(q,m))=1/(q m)`, even when different parents have common
prime factors. No independence between different parent intersections is
asserted.

At a target point in k different T_(q,m), the k parents are distinct
original labels and A_q is one further label. Therefore

    sum_m 1_(T_(q,m))(y) <= N(y)-1,
    sum_m H(S_(q,m))/alpha_(q,m) <= H_cov.            (CA3)

For the full original q-height H_q define

    alpha_q=q/(q-1) (1-q^(-H_q)).

Since `alpha_(q,m)<=alpha_q`, CA1--CA3 imply

    (q-1)H(G_q) <= alpha_q H_cov.                    (CA4)

The same argument for any actual measure `lambda_q<=M_q H` on G_q,
with M_q>0, gives `(q-1)lambda_q(G_q)<=M_q alpha_q H_cov`.
This improves the deterministic two-to-one capacity bound's constant 2
to the finite geometric sum alpha_q, which is below 3/2 for odd q.
No transport is needed to prove this inequality. A fractional realization
by independently sampling target Haar is possible, but changes the source
coordinates and must be described as resampling.

## 2. Prime-private sources have a smaller exact containing cylinder

For a q-free parent m let

    F_(q,m)=Lambda minus ({q} union supp(m)),
    rho_(q,m)=product_(p in F_(q,m)) (1-1/p).

The selected source is private to A_q, so it avoids every other original
prime class. Inside its lifted child cylinder, the prime roots at p|m
already avoid A_p: the original child is comparable with and disjoint
from A_p. This remains true if the original parent m is itself prime;
the child has the nonprime root at m, while the target A_m has the prime
root. For p in F_(q,m), the prime root remains unconstrained by the
lifted cylinder. These distinct CRT coordinates are independent under H.

Consequently the lift after excluding all other prime classes has exact
mass `rho_(q,m)/(q^e m)`. The actual selected source is a subset, so

    H(S_(q,m)) <= alpha_(q,m) rho_(q,m)/(q m).        (CA5)

This does not claim that the containing cylinder is prime-private: other
composite originals may cover part of it. It is an upper bound on the
actual source with only some of its necessary exclusions imposed.
In particular CA3 strengthens to

    sum_m H(S_(q,m))/(alpha_(q,m) rho_(q,m))
      <= H_cov.                                     (CA6)

The disjoint-height premise in CA1 and the prime-private premise in CA5
are separate. Omitting either changes the capacity problem.

## 3. All primes share one pointwise surplus budget

Let `k(y)=number of original prime labels covering y`. For every allowed
ordered pair q,m define the allocated target capacity

    c_(q,m)=integral_(T_(q,m)) 1/k(y) dH(y).

The denominator is positive on this target. Define the integrand to be
zero away from the target, including at points where k=0. At a point y,
each of its k prime labels can pair with at most N(y)-1 other original
labels. The allowed parent pairs are a subset of these pairs. Hence

    sum_(q,m) 1_(T_(q,m))(y)/k(y) <= N(y)-1,
    sum_(q,m) c_(q,m) <= H_cov.                      (CA7)

This includes both directions of a prime-parent pair. A point covered by
A_p and A_q may receive the ordered charges (p,q) and (q,p); dividing
each by k prevents their unweighted double charge. A merely acyclic
orientation of arbitrary label edges would not suffice: acyclic graphs
can have more than N-1 edges. CA7 supplies the actual pointwise allocation.

The capacity has an exact CRT formula. Put

    b_(q,m)=2 if m is prime, and 1 otherwise.

On T_(q,m), A_q is present. If m is prime, A_m is a second forced prime
label. If m is composite, every prime dividing m is absent by comparable-
class disjointness. For p in F_(q,m), presence of A_p is an independent
Bernoulli event of probability 1/p. Thus

    beta_(q,m)
      = integral_0^1 t^(b_(q,m)-1)
          product_(p in F_(q,m)) (1-1/p+t/p) dt,
    c_(q,m)=beta_(q,m)/(q m).                        (CA8)

The identity uses `1/j=integral_0^1 t^(j-1)dt` for positive integers j.
All factors and the integral are rational finite quantities. It preserves
the actual original prime-label law; parents with overlapping supports
are not treated as independent of one another.

Combining CA5, CA7 and CA8 yields the shared all-prime budget

    sum_(q,m) [beta_(q,m)/(alpha_(q,m) rho_(q,m))]
      * H(S_(q,m)) <= H_cov.                        (CA9)

More generally, each q may carry a different actual source measure
`lambda_q<=M_q H` supported on G_q. The same target allocation gives

    sum_(q,m) [beta_(q,m)/(alpha_(q,m) rho_(q,m))]
      * lambda_q(S_(q,m))/M_q <= H_cov.             (CA10)

The measures need not arise from one shared preparation, because each
is compared to the same original H with its explicit density bound.
The conclusion concerns those supplied measures simultaneously; it does
not assert that independently optimized preparations are jointly feasible.
The target capacities are allocated only once, by CA7.

## 4. Cancellation of a support-size loss

The source exclusion factor strengthens CA9 beyond uniform allocation
weights of size `1/|Lambda|`. In fact

    beta_(q,m)/rho_(q,m)
      = integral_0^1 t^(b_(q,m)-1)
          product_(p in F_(q,m)) (1+t/(p-1)) dt
      >= 1/b_(q,m).                                (CA11)

Thus each selected composite parent contributes at least 1/alpha_q,
and each selected prime parent contributes at least 1/(2 alpha_q),
to the normalized source weight. If c_q(z) and p_q(z) count the
composite and prime parents chosen at z, then `c_q(z)+p_q(z)=q-1` and

    sum_q integral_(G_q)
      [c_q(z)+p_q(z)/2]/(M_q alpha_q) d lambda_q(z)
      <= H_cov.

In particular,

    sum_q (q-1)/(2 alpha_q)
      * lambda_q(G_q)/M_q <= H_cov.                 (CA12)

This is a simultaneous all-prime inequality, with no prime-support
cardinality factor. The sharper coefficients in CA10 retain both the
actual column heights and parent supports.

Distinct parent cofactors also give `p_q(z)<=min(q-1,|Lambda|-1)`.
The coefficient `(q-1)/(2 alpha_q)` in CA12 can therefore be increased to
`[q-1-min(q-1,|Lambda|-1)/2]/alpha_q`. The preceding integral with the
actual selected parent types retains at least this much information.

## 5. Remaining scope and finite checks

The sources G_q are still synchronized-good sources. For raw prime-
private Haar, 355 only guarantees

    H(G_q) >= (1/q) integral_(R_q) q^(1-L_q(x)) dH_X(x)

when G_q includes all good tails. That genuine finite-height loss remains
in CA12. For smaller q, R_q must not be replaced by the chronological
pre-q survivor. The inequalities above are necessary capacity constraints;
no contradiction with another required budget is established here.

The [mean partial-matching bound](360-mean-partial-matching-without-tail-loss.md)
uses a different selection: keep partial matchings on every tail and
integrate their sizes. It applies the same allocation to the whole raw
prime-private source, avoiding the full-matching tail-probability loss.
That extension still does not give a contradictory surplus bound.

The [standard-library checker](../../frontier/cover-geometry/parent_capacity_allocation.py)
enumerates complete periods 12, 144 and 960 for the same three even-cover
fixtures used in 357. It chooses actual synchronized matchings, compares
their existence with Hall's finite criterion, checks the full-height lift
and its exact prime-exclusion factor, compares CA8 with pointwise CRT
enumeration, and verifies CA7, CA9 and CA12 with exact rational arithmetic.
It also checks CA10 for nonconstant source densities and nonunit bounds M_q.
The checks cover 27 original APs, 1,116 complete carrier points, 12 parent
columns, 19 full-height child lifts, and 470 Hall-subset comparisons.

| Complete period | CA9 source charge | Allocated target capacity | Original H_cov |
| --- | --- | --- | --- |
| 12 | 5/24 | 1/4 | 1/3 |
| 144 | 13/72 | 1/4 | 13/36 |
| 960 | 67/1440 | 89/576 | 79/120 |

Without the inverse prime-multiplicity allocation, the same eligible
ordered target pairs exceed N-1 at 2, 24 and 64 points respectively.
Normal and physically relocated isolated, optimized Python executions
from `/` produce identical output; the checker does not import sibling files.

The period-144 and period-960 fixtures do not contain every possible
cofactor parent. Their missing parents are reported and removed from
matching options before any source is selected. The resulting G_q may
therefore be smaller than the good set obtained without that premise;
these fixtures do not test divisor closure or the theorem that all good
sources have original parents. None of these even covers is an odd-cover
counterexample. The checker and its arithmetic are not a formal proof.
