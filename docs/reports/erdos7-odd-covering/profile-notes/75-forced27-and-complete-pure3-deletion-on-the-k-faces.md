[Index](../marked_head_profile.md) · [Actual source construction](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Common deleted measure](57-common-deleted-measure-coupling.md) · [Entire controlling face](72-a-linear-gap-on-the-entire-controlling-beta-face.md)

# Forced27 and complete pure3 deletion strengthen both controlling faces

On the entire actual beta face398,410,422, with carrier(1,1) and
saturated mass S=D=53/360, every independently labelled complete
original357 test A satisfies

    limsup integral_survivor A<=1151/1800,
    liminf[6*S-integral_survivor A]>=439/1800.          (F27.1)

The bound improves profile72 by23/900. Compared with the old49
conditional margin, bounded above by9257/48600 on the entire face,
the strict margin gain is649/12150. The compatible root0-cell exchange
of72 gives the same result on616,628,640 with carrier(1,0).

The two additional facts are that saturation forces every forbidden
27 cofactor into the unthinned root0 cell, and that the complete
forbidden pure3 tail supplies an exact deletion measure on arbitrary
five-coordinate sets. Both hold uniformly over the actual beta face,
although its beta labels may occupy several root1 cells.

This is an ordinary endpoint theorem, not a replacement for72 or73,
a stronger finite neighborhood, or a new global K certificate. No
Lean verification or realization of every relaxed beta point is claimed.

## 1. Retain the original face and saturation data

Use profile72's source data, with beta_i>=0 and sum_(i=2..4)beta_i=1/4:

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/2-beta2,1/2-beta3,1/2-beta4),
    n=(1/36,1/12,d2/9,d3/9,d4/9),
    s=1/4, C=37/72, D=53/360.                       (F27.2)

The pure3 source has its full deep budget1/18 in cell0. Pure5 has
deletion budget1/4, all alpha deletion is on root1, all beta deletion
is in root1 cells, and all additional late35 deletion of mass1/72
is in cell0. The mixed7 mass cap is saturated: delta=V and each
individual original cofactor attains its cap.

The first beta label lies in some cell L in{2,3,4}. Profile72 proves
that P,A,B are distinct first-five source slots, H is the unique
source-free first slot, and Q is the remaining slot. The complete
pure5 and alpha deep source families lie in Q with mass1/20 each.
This uses the first beta label alone, and does not assume that beta
labels in different cells have disjoint five projections.

Keep the four distinct complete forbidden families3,9,5,15:

    mu<=w*Lambda,
    w=1-(1_root1+1_cell1+1_H+1_(root1 intersect H))/5.  (F27.3)

All extra forbidden families used below have different original
cofactors. Their projected old-coordinate supports may overlap;
their measures may be added because delta=V, not because the
projections are asserted disjoint.

## 2. Every saturated deep pure3 carrier has an exact five section

For a forbidden cofactor3^a, a>=3, the old-coordinate cap is
(3/4)*3^-a. At saturation its ternary cylinder J has exactly that
Lambda mass. Since d<=1/2 throughout root1, J must lie in root0,
where d=3/4. The inequalities

    Lambda(J)<=3*eta(J)/4<=3*3^-a/4

must both be equalities. Thus J retains its full ternary Haar mass
and has no late source deletion. There are no alpha or beta source
labels on root0. If U_P is the complete pure5 source union and

    q(F)=Haar5(F minus U_P),

then, for every five-coordinate measurable set F,

    Lambda(J times F)=3^-a*q(F).                     (F27.4)

The seven-coordinate residues may differ at every original label.
Nevertheless the original cap weights sum to1/5, so all forbidden
pure3 cofactors of depth a>=3 together delete exactly

    q(F)/90

on the event consisting of the whole old ternary coordinate times F.
Indeed sum_(a>=3)3^-a=1/18. On root0 their complete total deletion
is1/120, using q(full)=3/4. These conclusions use complete tails,
with neither nesting of test residues nor a cutoff in a or seven depth.

## 3. The original depth3 late label forces forbidden27 into cell1

Let S3 be the pure3 source cylinder of depth3. Full pure3 budget
makes every deep pure3 source cylinder present, disjoint from the
others, and contained in cell0. In particular S3 occupies one of
the three depth3 children of that cell.

The complete late source budget is1/72. Equality of its additional
mass with this raw budget forces every original late label, including
(a,b)=(3,1), to retain its full product mass1/135 in cell0. Write J3
for this label's ternary child. It is disjoint from every pure3 source
deletion and has eta(J3)=1/27, so it differs from S3.

Its first-five slot cannot be P, which is deleted. It cannot be Q,
which contains the complete positive pure5 source tail, and it cannot
be H, which is source-free over the whole eta support. It is in A
or B. No choice between these two slots is needed.

All deeper pure3 source cylinders have total mass1/54. They avoid S3
and J3, hence lie in the third depth3 child R. Therefore

    eta(R)=1/27-1/54=1/54.

A forbidden27 cofactor would require cap(3/4)/27=1/36. Its possible
old-coordinate masses in the three children of cell0 are bounded by

    Lambda(S3)=0,
    Lambda(J3)<=1/36-1/135=11/540,
    Lambda(R)<=3/(4*54)=1/72.                         (F27.5)

All are strictly below1/36. A depth3 child in root1 has cap at most
1/(2*27)=1/54, also too small. Thus every saturated forbidden27
cofactor is in cell1. Summing its complete seven depths supplies
compulsory deletion1/180 in cell1.

This reasoning is specific to27. It makes no assertion that every
deeper pure3 forbidden carrier lies in cell1. The later source labels
may use different A/B slots and do not form a single ternary partition.

## 4. Uniform independent cylinder caps over the entire beta face

First apply profile72's ternary caps, which already include complete
forbidden5^b and3*5^b deletion. Its root bounds are31/360 and7/90.
Subtract the complete deep pure3 deletion1/120 on root0 from(F27.4):

    mu(test3)<=7/90.

Its cell bounds are

    1/40,11/180,1/30-4*beta2/45,
                       1/30-4*beta3/45,1/30-4*beta4/45.

The compulsory forbidden27 deletion reduces the second bound by1/180.
Every other cell is already below1/18. Hence

    mu(test9)<=1/18.                                (F27.6)

The inherited deep pure3 coefficient7/10 from72 remains valid, so
the entire pure3 test tail is at most7/180. None of these calculations
requires all beta mass to occupy the first-beta cell L.

For five tests, use72's source-slot table that discards all deeper
beta source deletion. Apply(F27.3), and then subtract q(F)/90 from
the distinct complete deep pure3 forbidden family. The pure5 complement
in slots(P,A,B,Q,H) has masses(0,1/5,1/5,3/20,1/5). For every one
of the three possible L, the resulting column bounds are

    (0,2/75,14/225,7/150,7/150).                    (F27.7)

Thus any independent5-test has cap14/225. In particular the larger
Q allowance needed for a distributed beta face does not control
the column maximum. The root-column and cell-column maxima of the
same selected-deletion table, even without the extra deep pure3
deduction, give

    mu(test15)<=8/225, mu(test45)<=4/225.             (F27.8)

For arbitrary five cylinders F of depth b>=2, keep only the forbidden
root1 and cell1 families from(F27.3), discarding alpha and beta source
deletion. Their weighted pure5 complement has coefficient37/90.
Subtracting the full pure3 deletion(F27.4) gives

    mu(full ternary times F)<= (37/90-1/90)*q(F)
                              <=(2/5)*5^-b.         (F27.9)

On root1 the corresponding coefficient is(4/5)*h1=4/15. On root0
it is at most h0-eta1/5-1/90=2/15, using the entire deep pure3
deletion there. Therefore every independent3*5^b test has cap
(4/15)*5^-b. On each cell, the selected coefficient is at most4/45,
so every9*5^b test has cap(4/45)*5^-b. The complete b>=2 sums of
these three categories are1/50,1/75,1/225.

The deep mixed category a>=3,b>=1 retains its old full product cap,
of total1/72. No additional loss is inferred from the late geometry
for that category.

## 5. The complete load and unchanged positive-seven part

The disjoint nonunit zero-seven categories have the complete sums

| Category | Surviving cap sum |
| --- | ---: |
| 3 | 7/90 |
| 9 | 1/18 |
| 3^a, a>=3 | 7/180 |
| 5 | 14/225 |
| 5^b, b>=2 | 1/50 |
| 15 | 8/225 |
| 3*5^b, b>=2 | 1/75 |
| 45 | 4/225 |
| 9*5^b, b>=2 | 1/225 |
| 3^a*5^b, a>=3,b>=1 | 1/72 |

Their sum is611/1800. The unit contributes53/360. For positive
seven depth, drop mixed7 deletion and retain the complete raw35
cap sum, giving(s+C)/5=11/72. Thus

    integral A<=53/360+611/1800+11/72=1151/1800,
    6*(53/360)-1151/1800=439/1800.                   (F27.10)

The uncoupled full raw-cap bound is293/360; the new improvement over
it is157/900. Profile72 has numerator133/200, so the additional
improvement is23/900. These are comparisons between complete upper
bounds. The proof does not subtract a newly estimated deletion term
from an expression that has already used that same forbidden family.
Inside each individual cap, every retained forbidden family has a
distinct original cofactor. Reusing a valid uniform cylinder cap for
different test labels is ordinary linearity of integration.

## 6. Limits, symmetry and the actual mass-saturating construction

The proof above applies to exact limiting source and deletion data.
For arbitrary finite original families tending to either face with
S-D tending to0 and the corresponding carrier, use the labelwise
diagonal compactness argument of72. Original source and test labels
may vary independently along the sequence. Complete forbidden-union
tails and complete first-moment cylinder tails give uniform convergence
of the required integrals, yielding the limsup and liminf in(F27.1).

The root0-cell exchange of72 swaps cell0 with cell1 and preserves
all cylinder depths and original modulus labels. It transports the
entire proof, including the forced27 argument, to the second face.

The actual398 construction of48 already realizes saturated mass in
the limit. It uses pairwise disjoint deep ternary source cylinders
T_a(0,1), and late source rectangles T_a(0,2) times F_(2,b). Its five
disjoint mixed7 classes retain the originally specified independent
moduli. With the notation of48, its complete limits are

    t=1/18, q=1/4,
    H=4/9+t+q/9-t*q=37/72,
    S=1/4-H/5=53/360.

Thus the new proof improves the load comparison; it does not claim
a positive mass surplus above D at398. The existing finite398
original-label constructor is reused for a height3 consistency check.
No new realization is asserted for other points of the relaxed face.

## 7. Exact reproduction

The [checker](../frontier/endpoint_k_face_forced27.py) pins72's whole-face
table and the original398 construction. It verifies the strict27
exclusions, the affine beta root and cell bounds, all three first-beta
tables, the complete descendant-five coefficients and every original
test category. The
[certificate](../certificates/source_norms/endpoint_k_face_forced27.json)
retains these rational values, the full geometric sums and the actual
construction check.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_k_face_forced27.py --check
```

The checker uses only the Python standard library and the pinned
original-label constructor. Its finite arithmetic supplements the
ordinary geometric proof; it does not enumerate every actual family.
Only explicit `--output PATH` writes a certificate. The stronger
endpoint datum requires a separate quantitative argument before it
can replace any finite-neighborhood or global comparison.
