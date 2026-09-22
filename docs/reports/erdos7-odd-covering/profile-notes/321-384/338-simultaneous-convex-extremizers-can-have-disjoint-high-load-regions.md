[Index](../../marked_head_profile.md) · [Actual source and rotated tests](../001-064/26-conditional-head-deletion-with-a-priced-arbitrary-cofactor-tail.md#a-literal-obstruction-to-uniform-gated-tail-thresholds-with-its-cht6-consumer) · [Source-specific stability target](../001-064/57-common-deleted-measure-coupling.md)

# Simultaneous convex extremizers can have disjoint high-load regions

On the actual unit source already used in26, the two complete original
tests centered at1 and2 simultaneously maximize EVERY increasing convex
load cost among all independent original residue choices. Nevertheless,
their high-load regions `{A1>6}` and `{A2>6}` are disjoint, each of mass
`83/1440`. The new conclusion is this joint extremality and separation;
the actual source, rotation and product bound come from26.

This is a bounded obstruction to deriving overlap from scalar near
extremality without a source restriction. It does not satisfy333's
source guard: its9-class is contained in its3-class, so it lies outside
the effective9 chart required there. No future bad-event intersection,
333/335 hinge-upper attainment, or unrestricted covering result follows.
The argument is ordinary mathematics, with exact finite verification;
no Lean result is asserted.

## The same finite source and all original labels

Set `Q=3^2*5*7*11*13=45045`. As in26, forbid `0 mod d` for every divisor
`d>1` ofQ. These47 distinct odd original classes leave exactly
`U(Q)={x mod Q:gcd(x,Q)=1}`, with17280 points. Their redundancy is allowed;
no irredundancy claim is made. The actual through13 construction in26
has uniform law `nu` on these points.

For every `d|Q`, retain its own independent test residue `a_d mod d`,
including the single constant modulus-one term. Thus

    A(x)=sum_(d|Q) 1_(x=a_d mod d)

has48 original labels. Let `A_j` choose `a_d=j mod d` for every label,
for `j=1,2`. The map `x -> 2x mod Q` preserves this actual source and
satisfies `A2(2x)=A1(x)`.

The9-class of the forbidden family is `0 mod9`, already contained in
`0 mod3`. In302's effective9 chart the forbidden9 cylinder lies in a
surviving3 root. These conditions are incompatible. Consequently this
example is outside the entire guard of333, without assigning an
out-of-chart value to `qJ`.

## One center maximizes every increasing convex cost

Fix a prime-power coordinate `p^h` ofQ and fix all other coordinates.
The source is the product of uniform unit-coordinate laws by CRT. A
label with positive p-exponent contributes either zero, or the indicator
of one residue cylinder modulo `p^e` on `U(p^h)`. Its other-coordinate
condition stays fixed throughout the following operation.

First replace every nonunit p-residue by the residue of a chosen unit
center j. Its old cylinder was empty on the source, so this only increases
the load pointwise. Now each active p-cylinder of depth e has the fixed
cardinality

    m_e=phi(p^h)/phi(p^e).

Move every such cylinder, retaining its original label and depth, to the
common unit path `j mod p^e`. These new cylinders are nested. This is one
legal choice of residues independent of the fixed other-coordinate point.

To verify the convex comparison, write `b` for the load of labels with
p-exponent zero, and `s(x)` for the sum of the active cylinder indicators.
For any k coordinate points, their total contribution to `s` is at most

    sum_(active labels d) min(k,m_(e_d)).           (CE1)

For the nested replacement, order points from the smallest cylinder
outwards. Its first k points attain CE1 for every k. The total load sum
is unchanged, and every top-k partial sum increases. For any real t,

    sum_x (b+s(x)-t)_+
      =max_(0<=k<=phi(p^h)) [sum_(top k) (b+s(x))-kt]. (CE2)

Hence every hinge sum increases. A convex function on the finite integer
load range is an affine function plus a nonnegative combination of
integer hinges. Its affine sum is unchanged; therefore its sum also
increases. Together with the initial pointwise increase, this proves the
claim for every increasing convex function f.

The same residue replacement works simultaneously for every setting of
the other coordinates. Average their conditional comparisons and repeat
for each of the five prime coordinates. The resulting complete test is
exactly `A_j`. No original label is identified, deleted or chosen after
sampling. Thus, for both j=1 and j=2,

    E_nu f(A) <= E_nu f(A_j)
        for every complete original A and increasing convex f. (CE3)

In particular these two fixed tests simultaneously attain every hinge
maximum, every positive weighted sum of hinges, and the square maximum
for this source. CE3 concerns the exact maximum on this source, not the
possibly larger raw comparison operators used in333/335.

## Exact high-load separation at zero convex deficit

The complete divisor tests factor as

    A_j=(1+1_(x=j mod3)+1_(x=j mod9))
          *product_(p=5,7,11,13) (1+1_(x=j mod p)).

The centers1 and2 differ at the first digit of every prime. The product
of their two ternary factors is at most3, and the product of the two
factors at each other prime is at most2. Therefore pointwise

    A1*A2 <= 3*2^4=48.                             (CE4)

Their common complete histogram is:

| Load | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Count |4455|6246|1485|3006|1092|632|274|59|28|2|1|

A load greater than6 is at least8. If both tests exceeded6, their product
would be at least64, contradicting CE4. Thus

    nu(A1>6)=nu(A2>6)=83/1440>0,
    nu({A1>6} intersect {A2>6})=0.                 (CE5)

The same intersection is empty for any two thresholds at least6.
Selected exact hinge maxima from CE3 are:

| Threshold t |6|8|12|16|18|24|
|---|---:|---:|---:|---:|---:|---:|
| max_A E_nu(A-t)_+ |32/135|263/2160|3/80|1/60|113/8640|1/432|

For any two increasing convex costs, define each deficit as the exact
same-source maximum minus that test's cost. Both deficits here are zero.
Consequently, no positive lower bound on the intersection in CE5 can
follow solely from those deficits, even when all such costs are known.
Any bound of the form `intersection >= gamma - kappa1*deficit1
- kappa2*deficit2`, with `gamma>0`, fails on this source. A source-specific
hypothesis or an actual joint-location observation is necessary to
exclude this example. The high-qJ stability question remains unresolved
by this result, as does the relation between future assigned bad events.

## Complete finite verification

The [helper](../../frontier/source-budgets/source_pair_convex_extremizers.py) reconstructs
all47 forbidden classes, all48 test labels and all17280 actual survivors.
It checks the rotation, both complete load histograms, the sharp product
maximum48, all displayed hinge values, and the zero intersection. A
second calculation obtains the full histogram from the five coordinate
laws. Every check uses exact integers or fractions and explicit failure
conditions, including under `-I -S -O`.

There are no omitted original labels or exponent tails in this finite
source. The arbitrary-residue convex comparison CE3 is established by
the argument above; the helper does not enumerate all residue layouts
or certify that proof through Lean. The
[certificate](../../certificates/source_norms/source-budgets/source_pair_convex_extremizers.json)
binds the current proof, helper and referenced source descriptions.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_pair_convex_extremizers.py --check
```
