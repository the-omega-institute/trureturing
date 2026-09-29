# A fourth-moment improvement on the unchanged shallow source

[Report730's deletion-sensitive D2 comparison](730-one-common-shallow-source-supports-four-arbitrary-fresh-prime-heights.md) applies to h(t)=t^4 on the
same six actual pruned315 survivor laws. Its direct finite certificate
gives the uniform bound

    E L^4 <= 73199/128

for all complete315 queries. The existing increasing-convex comparator
instead gives1964937701/3350646. Transport through the SAME pure primes
11,13,17,19,23 and the SAME actual mixed-deletion restriction, preserving
the relation between each head shape and its retention bound, yields

    E_mu23 L^4 <= G4new =4005807477705/19895792
        < G4old =3350218780205/16165331.                  (QD1)

The improvement is ordinary finite mathematics, not new Lean
verification. It changes no source and uses no reweighting. The already
established simultaneous bounds

    E_mu23 L^2 <=2607189975/7283281,
    E_mu23 L^3 <=906617738995/159166336

therefore remain valid on this exact mu23.

## Same-source D2 certificate

Retain the notation and actual source construction of Report730 FC2-FC3.
S is an actual canonical pruned45 survivor, n=|S|, and D0={3,5,9,15,45}.
A and B are complete45 query loads with their unit terms. The actual
original7d classes remove b(x) distinct remaining7-digits over x, with
0<=b(x)<=5; the surviving315 cardinality is N=6n-sum b(x).

Concentrating all nonnegative query increments at one live digit gives

    N E L^4 <= 5 sum_x A(x)^4 + sum_x(A(x)+B(x))^4
                                   -sum_x b(x)A(x)^4.

The fourth-power pairing is increased by sorting both vectors in the
same order. Indeed, for s,u,v>=0,

    (s+u+v)^4+s^4-(s+u)^4-(s+v)^4
      =uv[12s^2+12s(u+v)+4u^2+6uv+4v^2]>=0.

Removing inversions proves the finite sorting inequality. Set

    J4(A)=max_(old query B) sum_j(A^up_j+B^up_j)^4.

The sorted pairing need not itself be realizable by an actual B: it is
used in the upper-bound direction. An exact sufficient condition for
E L^4<=g is, for EVERY old query A,

    5 sum_x A(x)^4+J4(A)
      +sum_(d in D0) max_(cylinder C mod d)
                       sum_(x in S intersect C)(g-A(x)^4)_+
      <=6n g.                                           (QD2)

To see this, subtract gN in the preceding numerator inequality. The
deletion contribution is sum b(x)(g-A(x)^4). Drop its negative terms,
then bound b(x) by the sum of actual original old-cylinder indicators.
Each d contributes at most its displayed cylinder maximum. This is the
same original-sensitive D2 argument used for the cubic bound; no
independence of queries or actual deletions is assumed.

The exact producer exhausts every effective old query layout and every
sorted histogram pair:

| Canonical shape | n | Layouts | Histograms | g | Minimum scaled D2 slack |
|---|---:|---:|---:|---:|---:|
| root1 same root / other column |17|4760|170|18231/32|16|
| root1 other root / same column |17|4760|135|143033/256|23|
| root1 other root / other column |17|4760|179|143033/256|23|
| root2 same root / other column |16|4480|139|73199/128|10|
| root2 other root / same column |16|4480|131|1137/2|0|
| root2 other root / other column |16|4480|162|1137/2|0|

Slacks use the common denominator256; zero is allowed because (QD2)
is non-strict. There are27720 layouts and141892 ordered histogram pairs.
An empty or missing query slot is completed upward to a nonempty
cylinder; this can only increase the nonnegative load and its fourth
power. Thus the tested complete queries dominate all actual cases.

The previous1/256-grid value fails this sufficient comparison for each
shape. This locates the finite certificate within its stated grid; it
does not assert sharpness of any actual fourth moment or optimality of
the underlying source.

## Propagation without a change of source

Report730's general integer-moment extension multiplies the fourth bound
by1+15/(p-1) for each pure-live prime. Hence

    product_(p=11,13,17,19,23)(1+15/(p-1))=17205/512.

The actual mixed-deletion source retains relative mass at least delta_i
for its own head shape i. These inherited bounds follow from the SAME
mean inventory used in Reports725 US6 and728 TC5-TC6:

    delta_i=c1_i+2+sum_p 1/(p-1)-(c1_i+1) product_p p/(p-1),

where p runs through11,13,17,19,23 and the six c1_i are
185/86,178/85,178/85,2,157/77,157/77. The shape pairing is

| Shape in the preceding table | Retained-mass lower delta_i | Propagated fourth upper |
|---|---:|---:|
| root1 same / other |1243487/13077504|4005807477705/19895792|
| root1 other / same |7609619/64627200|310624927012125/1948062464|
| root1 other / other |7609619/64627200|310624927012125/1948062464|
| root2 same / other |39317/253440|623397453525/5032576|
| root2 other / same |123881/887040|67782624525/495524|
| root2 other / other |123881/887040|67782624525/495524|

Restriction only decreases the unnormalized nonnegative fourth moment,
and normalizing this SAME restriction gives g_i(17205/512)/delta_i.
The maximum is the first row, yielding (QD1). The largest raw g_i alone
occurs in the fourth row; using a different shape's least retention
would weaken the bound.

For comparison, the unpaired extremes g_max=73199/128 and
delta_min=1243487/13077504 give the valid but larger bound

    G4unpaired=(73199/128)(17205/512)/delta_min
              =2297664900135/11369024.

The old fourth bound is reproduced from the existing eight-atom
increasing-convex comparator. The exact difference and ratio are

    G4old-G4new=1528003273115/258645296,
    G4new/G4old=30542813613/31439003216<1.

Every constant is evaluated exactly. The proof does not trade away the
same-source square or cubic bounds. It is another simultaneous
constraint on every complete query and consequently on every padded
finite-height support field through Jensen.

## What this does and does not settle

[Report731](731-selected-query-moments-do-not-force-five-direction-carving-positivity.md)'s particular five-atom selected-query table already violates
the old fourth bound; the new bound tightens that additional constraint.
Neither this rejection nor the improved number proves positivity of
the full five-direction carving objective. That remains a separate
joint-feasibility or inequality problem. The actual complete-query
dictionary must still be retained, and a feasible formal moment table
would not by itself be an actual congruence realization.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_head_quartic.py)
checks all six fixed sufficient bounds against every effective old query,
reconstructs both the uniform and shape-specific propagation, and compares
with the previous quartic bound. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_head_quartic.json)
records the complete counts, exact slacks and six paired source bounds.
An independent implementation uses histogram-count quantile coupling and
direct positive-cylinder sums; its rational slacks agree after accounting
for reduced denominators. No unrestricted-height source theorem or Lean
proof is claimed as reverified.
