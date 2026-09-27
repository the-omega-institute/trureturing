[Index](../../marked_head_profile.md) · [Actual endpoints](../001-064/50-sharp-source-survival-endpoints.md) · [Common deletion](../001-064/57-common-deleted-measure-coupling.md) · [J/K faces](../065-128/71-global-j-k-control-faces-and-exact-escape-gaps.md)

# The whole J face forces source anti-alignment

On either entire actual saturated J-control face of71, every complete
original357 identity test A, with independent residues at every original
modulus, satisfies

    limsup integral_survivor A <= 16/25,
    liminf (6*S-integral_survivor A) >= 13/50.       (J1)

The source geometry also gives a quantitative obstruction before mass
saturation. Let L be the cell of the first beta source label and x_L
the complete mass of late source labels with five-depth1 in that cell.
On the exact source face,

    S-D >= (2/5)*x_L
        >= (2/5)*(late_L-1/360)_+.                 (J2)

In particular, if the original late label (a,b)=(3,1) lies in L, the
surplus is at least2/675. Saturation remains possible when source labels
are appropriately separated, as the actual families in50 show.

These repo-derived ordinary results cover actual limits on both whole
beta-times-late faces. They neither realize the entire relaxed parameter
simplex nor provide an off-face theorem, a new global K, or Lean proof.

## 1. Actual label budgets restrict the source simplex

Use roots ROOT=(0,0,1,1,1), with the first face having

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/2-beta2,1/2-beta3,1/2-beta4),
    n=(1/24,1/12,d2/9-late2,d3/9-late3,d4/9-late4),
    sum beta_i=1/4, sum late_i=1/72 (i=2,3,4),
    s=1/4, C=1/2, D=s-C/5=3/20.                 (J3)

The shallow forbidden carrier is(root0,cell1). The second face exchanges
cells0 and1 and uses(root0,cell0). All source statements below concern
full original-label budgets in the exact limiting configuration.

Equality of each aggregate source budget with its complete raw capacity
forces every label to contribute its full additional mass. Therefore
the beta labels partition their masses5^-b among the three root1 cells.
The first label45 defines a cell L with beta_L>=1/5. Similarly the late
labels partition3^-a*5^-b, a>=3,b>=1, among these cells. The largest
late atom is1/135, larger than the remaining late budget7/1080; its
cell M is uniquely determined and has late_M>=1/135.

These are necessary conditions on actual sources, stronger than the
relaxed simplex constraints in(J3). A beta barycenter with all three
coordinates1/12 is excluded from the actual-source closure.

Let P,A,B be the first-five slots of source labels5,15,45. Full
additional budgets make them distinct. Every deeper pure5 or alpha
source cylinder avoids B: otherwise it would remove positive mass from
the first beta label in cell L. The deeper pure5 and alpha source
families are also mutually disjoint in the five coordinate. Let Q be
the parent of the pure5 source label25. It differs from P,A,B, leaving
one first slot X.

A full late label of five-depth1 in cell L cannot lie over P,A,B or Q.
The first three already delete it there; Q contains source25, which
deletes a positive portion of any ternary-times-Q rectangle. It must
lie over X. Its full additional mass contributes to source loss on X
both globally and in root1. The disjoint assigned contributions give
source loss at least x_L in those two cylinders.

For an arbitrary forbidden cofactor5 carrier, losses in P,A,B,Q are at
least h/5,h1/5,eta_L/5,h/25, respectively, where h=1/2 and h1=1/3.
Every one exceeds the total possible x_L<=1/90. On X the preceding
argument gives loss at least x_L. For cofactor15 in root1 the analogous
losses are h1/5,h1/5,eta_L/5,h1/25. In root0 its raw cap already loses
(h1-h0)/5=1/30. Thus both original cofactor families lose at least x_L
from every nominal old cap. Their complete seven-depth weight is1/5
each. The original union-cap argument of57 proves(J2), with no overlap
assumption on their old-coordinate projections.

All late labels with b>=2 have total raw mass

    (sum_(a>=3)3^-a)*(sum_(b>=2)5^-b)=1/360.

Consequently x_L>=(late_L-1/360)_+. If M=L the original(3,1) label
gives x_L>=1/135 and hence the sector surplus2/675. At saturation,

    x_L=0, late_L<=1/360, M!=L.                  (J4)

This sector bound is weaker than50's sharp2/375 surplus at a fully
aligned vertex; its added scope is the entire actual product face.

## 2. Saturation supplies one joint deleted measure

At S=D, the nonnegative decomposition in57 implies delta=V as
measures and equality of every individual old cofactor cap, including
every original seven depth. Therefore selected virtual deletions add
on the same actual source Lambda even if their old projections overlap.

A saturated cofactor5 must have a source-free first-five slot H. It
cannot be P,A,B,Q, so H=X. All deeper pure5 and alpha source cylinders
lie in Q, with five masses1/20 each. Forbidden cofactor15 must use
root1 and H. These conclusions do not identify forbidden residues
with source residues or with any test residue.

Every full b=1 late source label is in root1. Its slot cannot be P or
A, which are deleted there; Q contains source25; H is source-free.
It must lie in B and outside L. Their complete mass is1/90. Unlike a
vertex specialization, this conclusion allows that mass to be shared
between the two root1 cells other than L.

For every saturated forbidden pure3 cofactor of depth a>=3, its old
cap is(3/4)*3^-a. A carrier in root1 has coefficient at most1/2, so
it lies in root0. If J_a is its ternary cylinder, equality in

    Lambda(J_a)<= (3/4)*eta(J_a)<= (3/4)*3^-a

forces full ternary Haar mass. Root0 has no alpha, beta or late source
deletion on this J face. Let q(F)=Haar5(F minus U_P), where U_P is
the complete pure5 source union. For every five-coordinate set F,

    Lambda(J_a times F)=3^-a*q(F).

Summing all original a>=3 and all positive seven depths therefore
gives the exact projected deletion

    V_pure3deep(full ternary times F)=q(F)/90.    (J5)

This does not force forbidden27 into cell1: the saturated off-diagonal
construction in50 uses a forbidden27 cylinder in cell0. K-face forced27
cannot be imported into this argument.

## 3. Uniform ternary and first-five caps

Complete forbidden5^b and3*5^b families give respective ternary
projections eta/20 and eta restricted to root1 divided by20. Keeping
also the shallow forbidden3 and9 yields, for every ternary event T,

    mu(T)<=Lambda(T)
          -[Lambda(T intersect root0)+Lambda(T intersect cell1)]/5
          -[eta(T)+eta(T intersect root1)]/20.     (J6)

The root caps from(J3) are3/40 and11/120. The five cell caps are

    11/360, 2/45,
    2/45-beta_i/9-late_i (i=2,3,4).

For arbitrary pure3 test cylinders of depth a>=3 the coefficients are

    11/20, 2/5, 2/5-beta_i (i=2,3,4),

all nonnegative. Thus every independent test3 has cap11/120, every
test9 cap2/45, and the complete pure3 tail cap11/360.

For first-five tests retain the four distinct forbidden families3,9,5,15:

    w=1-[1_root0+1_cell1+1_H+1_(root1 times H)]/5,
    mu<=w*Lambda.

Ignoring deeper beta and late source losses gives the source table
below, divided by eta_l. Additionally remove the full b=1 late mass
1/90 from column B in the root1 cells other than L.

| Cell | P | A | B | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| L | 0 | 0 | 0 | 1/10 | 1/5 |
| Other root1 cells | 0 | 0 | 1/5 | 1/10 | 1/5 |

The multiplier is1 in the affected root1/B entries, so the complete
column correction is exactly1/90 regardless of its cell allocation.
Now subtract(J5), a different forbidden family. The pure5 complements
of(P,A,B,Q,H) are(0,1/5,1/5,3/20,1/5). The resulting column bounds are

    (0,1/50,4/75,29/600,4/75).                   (J7)

Therefore mu(test5)<=4/75. The root-column table, even before the
extra(J5) subtraction, gives mu(test15)<=1/25. The certificate checks
all three choices of L and the two extreme late allocations for each;
affineness covers every allowed split of that1/90 mass.

For an arbitrary five cylinder F of depth b>=2, the shallow root0
and cell1 deletion gives coefficient h-(h0+eta1)/5=4/9 on q(F).
Subtract(J5) to obtain

    mu(F)<= (4/9-1/90)*q(F)<= (13/30)*5^-b.      (J8)

Its complete b>=2 sum is13/600. These caps concern the same actual
survivor but allow each test label its own independent residue.

## 4. Complete original load and a scoped inventory reserve

All exponent tails remain in this disjoint category partition:

| Original test category | Complete surviving cap |
| --- | ---: |
| unit | 3/20 |
| 3 | 11/120 |
| 9 | 2/45 |
| 3^a, a>=3 | 11/360 |
| 5 | 4/75 |
| 5^b, b>=2 | 13/600 |
| 15 | 1/25 |
| 3*5^b, b>=2 | 1/60 |
| 9*5^b, b>=1 | 1/36 |
| 3^a*5^b, a>=3,b>=1 | 1/72 |
| All positive-seven labels | 3/20 |

The last entry is the full raw source cap(s+C)/5; the remaining
three mixed categories keep their inherited full raw bounds. The
sum is16/25. Since6S=9/10, this proves(J1) in the exact saturated
configuration.

For the old49 identity direction40, barrier6, use the fixed layouts

    b=(2,3,1,1,1), c=(1,2,2,2,2).

In66(N14) and its cofactor expression the exact values throughout
the entire beta-times-late simplex are

    U=9/10, carrier=17/30, T=12991/9720.

The max branches stay fixed: max(k*d-c/5)=14/5 and max(k*d)=3,
with k=6-b. The remaining dependence is through the fixed beta and
late sums. The old margin is a minimum over layouts, so

    m40_old<=3/2-U-(carrier+T)/5=10661/48600.

The saturated-J replacement reserve relative to that old margin is

    13/50-10661/48600=79/1944.

Its complete inventory weight is94212612766226/1174116234095805,
giving weighted reserve3721398204265927/1141240979541122460.
This is a comparison to the old49 direction only. Later marked or
deep alternatives can already use these same deletion resources;
the reserve cannot be added to118 or subtracted from its global K
without a replacement comparison and new complete global checks.

## 5. Limits, actual witnesses and verification

For arbitrary finite actual families approaching a face and carrier
with S-D tending to0, take a labelwise diagonal subsequence of source,
forbidden and independent test residues. Complete raw geometric
tails give uniform convergence of the source/deletion measures and
the first-moment test integrals. Every label's nonnegative capacity
loss vanishes in the limit. The preceding exact argument therefore
gives the uniform limsup/liminf in(J1); it does not require that every
relaxed face point is realizable. The same argument interprets(J2)
for limits with a nonsaturated surplus and the specified exact source
face.

The compatible root0-cell exchange carries all original cylinders
and the carrier to the second face. Profile50 supplies actual finite
families saturating every off-diagonal control vertex after compatible
cell permutations, whereas its aligned vertices have strict surplus.

[j_face_alignment.py](../../frontier/j-geometry/j_face_alignment.py) checks the
complete sums, six slot tables, nine affine source witnesses and an
existing actual height3 off-diagonal construction. Its
[certificate](../../certificates/source_norms/j-geometry/j_face_alignment.json) retains
the rational data and full source pins. The ordinary arguments above,
not finite sampling, supply the arbitrary-source assertions.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_alignment.py --check
```

The unresolved next obligation is a quantitative transport away from
these J faces, followed by integration into the current full inventory.
