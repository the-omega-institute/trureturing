[Index](../marked_head_profile.md) · [Complete source](349-real-odd-cover-private-cylinders-and-transport-obstruction.md) · [Reserved palette](352-complete-private-region-exceeds-the-reserved-palette.md)

# Joint private demand survives arbitrary pure-power reassignment

For the complete HSW source and old-3 memory map, every numerical pure
power `3^e`, `e>=2`, may be reassigned, at arbitrary height, while a joint
private-region obstruction remains. Under the interface below, outputs
using no fresh primes leave Haar mass greater than `3/100` uncovered.
Even allowing any two fresh odd primes leaves mass greater than `1/160`
uncovered. Thus complete repair through this interface requires at least
three fresh prime factors in the combined support of the relevant
source descendants. Three primes are not asserted sufficient.

This releases the complete pure-power reservation and accounts jointly
for all 22 original pure-3 labels. Its support restriction applies to
that whole source family; [352](352-complete-private-region-exceeds-the-reserved-palette.md)
restricted the extra descendants of only `1 mod3`. The two hypotheses
must therefore be compared by their stated interfaces. The argument
neither releases mixed standard moduli nor excludes general odd covers.
The proofs below are ordinary finite and measure arguments with exact
rational checks, not Lean verification or a new existence claim for HSW.

## 1. The interface and common source

Retain all original HSW classes, including every height `1,...,22`.
Write

    A_t = 3^(t−1) mod 3^t,  1<=t<=22,
    P0 = {3,5,7,11,13,17,19,23}.

At each complete cofactor state, choose three of the four old roots
`0,1,2,3` and inject them into the three new roots. These choices may
depend on all retained coordinates, including additional prime and
higher precision coordinates. For output coordinate `x3`, the old
3-coordinate is always `floor(x3/3)`. The old 11 root is recovered from
the chosen injection; the other old prime coordinates are retained.
Additional output 11 coordinates, when used, are auxiliary coordinates. One actual choice of map is used throughout.
Use normalized product Haar measure on the output coordinates.

Every emitted AP has one fixed original source label and is sound for
that label on its entire progression. All numerical output moduli are
pairwise distinct, odd, and greater than one. Descendants attributed to any of `A_1,...,A_22` satisfy:

- Their prime support is contained in `P0 union F`, where `F` is one
  common finite set of fresh odd primes, disjoint from `P0`.
- Every pure `3^e` is available, including all standard candidates and
  every higher power. There is at most one emitted AP for each `e`.
- Every **mixed** numerical modulus in the complete standard candidate
  pool of 352 remains unavailable for reassignment to this source
  family, whether or not selected by the particular root map.

Other original labels may have arbitrary whole-source-sound descendants;
they cannot meet a point private for an `A_t`. Standard mixed images
with their own original labels therefore do not repair these regions.
This is a restriction on the descendants of the specified 22 sources,
not a claim that every reserved mixed modulus is actually occupied.

## 2. All source heights give one joint demand

The pullback of `A_t` is the band

    B_t = {3^t, 3^t+1, 3^t+2} mod 3^(t+1).                (JR1)

These bands are pairwise disjoint. Every other normal family containing
3 has first nonzero 3 digit 2 and misses `A_t`; the other heights of the
pure-3 family also miss. The 3-free competitors consequently give the
same joint private-root mask table at every `t`:

| root mask M | 0 | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| nonzero digit tuples | 48186 | 1159 | 876 | 5078 | 2180 | 1837 | 2886 | 8840 | 11902 |

Here the five digit coordinates belong to `5,7,13,17,19`; a set bit
means that this original root is private for the **same** `A_t`.
There are 82,944 digit tuples in total. Measure the target only on
cofactor tuples whose mask has at least three private roots. This
restricts the same probability space; Haar measure is not renormalized,
and the source labels, closing residues, and root map stay the same.
For `C={M: |M|>=3}`, the two counts are

    beta = sum_(M in C) count(M) max(|M|−1,0) = 63518,
    rho  = sum_(M in C) count(M)             = 25808.     (JR2)

The second number counts eligible joint masks, not a replacement of
the joint table by a single-root marginal. Both demand and AP supply
below carry exactly this same cofactor indicator.

If the old 23 residue is `j`, privacy requires `j>=t`: for `j<t` the
original closing class `0 mod3^j, j mod23` covers `A_t`. It also requires
each of the five other first nonzero heights to be at most `j`. Define

    g_p(j) = sum_(h=1)^j p^(−h),
    K_t = (1/23) sum_(j=t)^22 product_(p=5,7,13,17,19) g_p(j).   (JR3)

This retains all source heights and excludes the terminal zero cases,
which the closing classes cover. The `K_t` are positive and decreasing.

At every retained cofactor state, selecting three roots retains at least
`max(|M|−1,0)` private points. The old-3 prefix contributes `3^(−t)`;
one output-root position contributes another `1/3`. Summing this
pointwise bound over the disjoint source bands gives actual total
private demand in the restricted target at least

    D = beta sum_(t=1)^22 K_t / 3^(t+1)
      = 0.117270379770998634... .                          (JR4)

No independently attained optima or separately sampled source histories
are combined: JR4 holds for each single allowed map before integration.

## 3. All pure powers have a common supply bound

An AP contributing to the private demand must be assigned to its
unique original `A_t`. Whole-AP soundness puts it inside `B_t`.
Reduction modulo `3^(t+1)` shows that its modulus must be divisible by
`3^(t+1)`: an AP with smaller 3-valuation visits more than the one
permitted residue with its fixed lowest digit (or visits every lowest
digit when the valuation is zero). Hence a contributing pure-power AP
has exponent `e>=t+1` and fixes one new root.

For any fixed such AP, contribution to the restricted private target
is possible only at cofactor tuples with `M in C`. Grant the most
favorable root choice at every one of these tuples. The AP has 3-coordinate mass `3^(−e)`, and the eligible
cofactor mass is `rho K_t`; therefore its actual private intersection
has mass at most

    rho K_t / 3^e <= rho K_1 / 3^e.                      (JR5)

A pure AP assigned to another source contributes zero. Distinct
numerical moduli allow at most one AP for each exponent. Granting
every exponent, including an infinite tail beyond every original
height, gives the uniform pure-power capacity

    U = rho K_1 sum_(e=2)^infinity 3^(−e)
      = rho K_1/6
      = 0.048429267908662451... .                         (JR6)

This bound permits arbitrary assignment among all 22 source labels;
it does not reserve each power for a former owner. The use of `K_1`
only relaxes the bound for assignments to later sources.

## 4. Mixed capacity and the positive gaps

For `g_p=g_p(22)`, the complete standard pool of 9-divisible numerical
candidates has reciprocal sum

    P = (g_3/3)[(1+g_5)(1+g_7)(1+g_19)(1+g_13+g_17)+1/23].    (JR7)

It contains 12,045,352 distinct numerical moduli after merging source
collisions. Removing its pure-3 members leaves exactly the mixed
reservation above. The reciprocal sum over all `P0`-supported numerical
moduli divisible by 9, at arbitrary heights, is

    E = (1/6) product_(p in P0, p!=3) p/(p−1)
      = 676039/1990656.

Grant additional descendants the entire capacity

    V_F = E product_(ell in F) ell/(ell−1) − P.           (JR8)

Every nonpure admissible AP contributing to the private demand has
its modulus in this remaining pool. JR8 also includes high pure powers
already credited in JR6; this double counting only enlarges the
permitted supply. In particular,

    V_empty = 0.038386319153508714... .

By the union bound, the uncovered private mass is at least `D−U−V_F`.
Exact outward rational comparisons give

    D > 117270/1000000,
    U <  48430/1000000,
    V_empty < 38387/1000000,
    D−U−V_empty > 30453/1000000 > 3/100.                 (JR9)

The exact gap lies strictly between `0.030454792708827467` and
`0.030454792708827468`.

The first fresh odd primes are 29 and 31. For every common set of
at most two fresh primes,

    product_(ell in F) ell/(ell−1) <= (29/28)(31/30) = 899/840.

Consequently the same joint obligation gives

    D−U−V_F >= D−U−(899E/840−P) > 1/160.                (JR10)

The right-hand gap lies strictly between `0.006601504312104645` and
`0.006601504312104646`. Complete repair thus requires at least three
fresh primes in the **combined** support, while keeping the stated
mixed reservation and whole-source soundness.

More generally the necessary reciprocal-budget condition is

    product_(ell in F) ell/(ell−1) > (D−U+P)/E
      = 1.089676802424983842... .                        (JR11)

The inequality is in fact strict for a finite AP list, because the
infinite pure-power grant JR6 cannot be saturated. The three primes
29,31,37 pass this necessary test. Passing supplies no AP arrangement
or covering certificate.

The same formulas also apply to the unfiltered private target: use
all nonempty masks in JR2. That parallel case has `beta=71309`,
`rho=34758`, `D=0.131654546917254032...`, and
`U=0.065224135693168377...`; its zero-fresh and at-most-two-fresh gaps
are respectively `0.028044092070576939...>1/40` and
`0.004190803673854117...>1/240`. Both exact cases are retained in the
checker. The restricted target gives the stronger final bounds without
changing the admissible output interface.

## 5. Why one source alone does not suffice after reallocation

A concrete legal local change explains the joint accounting. Fix
`old2 -> new0`, `old3 -> new1`, `old1 -> new2`, and keep `3 mod9` for
`A_1`. For `e=3,...,7`, replace the former `A_(e−1)` image

    1+3^(e−1) mod3^e

by the whole-AP-sound `A_1` descendant

    4+3^(e−1) mod3^e.

The five numerical moduli are 27,81,243,729,2187. The new APs are
pairwise disjoint. Under this fixed map, their gain on the actual
private region is

    G = 25465 K_1 sum_(e=3)^7 3^(−e).

The remaining `A_1` demand becomes

    R_1 = (43309/9)K_1−G = 0.03831719013069467... < V_empty.

The prior single-source capacity cut no longer excludes repair. But
the actual private mass lost by the former source holders is

    L = 25465 sum_(t=2)^6 K_t / 3^(t+1)
      = 0.01511048229713812... .

These losses lie in pairwise disjoint source bands and are disjoint
from the residual `A_1` region. Thus `R_1+L−V_empty>3/200`. This is a
local reassignment and its actual joint liability, not a partial
covering asserted to extend. The uniform result JR9--JR10 does not depend on
this particular choice of five APs.

## 6. Reproducible mathematical scope

The [standard-library checker](../frontier/hsw11_pure3_reallocation.py)
loads the literal HSW constructor. It compares every one of the
82,944 masks under two algorithms: direct row predicates and marking
Cartesian rectangles. It checks all local root injections, all original
height/closing-residue endpoints, two exact forms of the `K_t` sums,
two orders for JR4, finite numerical candidate deduplication, and the
infinite geometric tails in JR6. A small finite AP fixture checks the
congruence interface used in JR1 and JR5. Finite fixtures do not replace
the arbitrary-exponent congruence and measure arguments above.

The surviving restriction is explicit: mixed candidate moduli stay
reserved to their standard sources, and all descendants of the 22
specified sources share the support bound. Reassigning mixed moduli,
allowing sufficiently many fresh primes, changing the memory map, or
letting one AP change its source label along the progression falls
outside this exclusion.
