[Index](../../marked_head_profile.md) · [Actual source budgets](../001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Common deletion](../001-064/57-common-deleted-measure-coupling.md) · [Quantitative identity formula](66-explicit-linear-endpoint-neighborhood.md)

# A linear gap on an entire controlling beta face

The actual source geometry gives a strict identity-cost improvement
on the entire beta triangle spanned by source vertices398,410,422,
with carrier(root1,cell1) and saturated mass S=D. For every independently
labelled complete original357 test A,

    limsup integral_survivor A<=133/200,
    liminf[6*S-integral_survivor A]>=131/600.             (F1)

The old49 conditional margin is at most9257/48600 throughout this
face. Thus(F1) improves it uniformly by at least677/24300>0.
The same result holds on the second face616,628,640 with carrier
(root1,cell0), by exchanging the two root0 cells.

These are the beta faces containing the K controls of53; the theorem
covers actual families approaching any point of each face. It does
not assert that every point of the relaxed triangle is realizable.
It is an ordinary endpoint theorem, with no quantitative neighborhood,
new global K value, or Lean claim.

## 1. Source data on the face and what saturation means

Keep the five ternary cells and ROOT=(0,0,1,1,1). Write beta_i>=0
for i=2,3,4, with beta2+beta3+beta4=1/4. The face data are

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/2-beta2,1/2-beta3,1/2-beta4),
    n=(1/36,1/12,(1/2-beta2)/9,(1/2-beta3)/9,(1/2-beta4)/9).

The pure5 budget is1/4, the additional alpha budget is1/4 on root1,
and the additional late35 budget is1/72 on cell0. The beta source
labels have their full combined additional budget1/4 in the three
root1 cells. In particular

    s=1/4, n_root0=1/9, n_root1=5/36,
    max(n)=1/12, max(d)=3/4,
    C=37/72, D=s-C/5=53/360.                         (F2)

The complete old35 cofactor cap sum C is the same formula as66.
At actual mass S=D, profile57 implies delta=V as measures and every
individual nonnegative cap deficiency vanishes. Thus each forbidden
cofactor is present and attains its own source cap. The carrier
condition selects root1 for all forbidden cofactor3 labels and cell1
for all forbidden cofactor9 labels.

## 2. The first beta label, rather than the whole beta budget, fixes a slot

The source beta labels are the original9*5^b labels. Full additional
budget means each one contributes its full five-coordinate capacity
5^-b in its own ternary cell. In particular the b=1 beta label occurs
in some cell L in{2,3,4}, with full additional mass1/5. Therefore
beta_L>=1/5 for an actual face source. This necessary condition is
not imposed on the entire relaxed simplex in the arithmetic below.

Let P,A,B be the first five-coordinate slots of the source labels5,
15 and45, respectively; B is the beta first slot. They are distinct,
because otherwise one of these labels loses some of its full
additional source budget. The complete pure5 and alpha five-cylinder
families are disjoint: pure5 has its full union budget, and every
alpha label attains its additional budget relative to that union.

Every deeper pure5 or alpha cylinder must avoid B as well. Such a
cylinder in B would remove positive area from the first beta label
on cell L, contradicting that label's full additional budget. This
argument uses one beta label. It does not assume that beta labels
in different ternary cells have disjoint five-coordinate projections.

A saturated forbidden cofactor5 has source mass h/5=1/10, so its
first slot H has zero source loss over the eta support. It cannot
be P,A or B. All deeper pure5 and alpha source cylinders avoid H.
There is only one remaining first slot Q; the two deep source
families lie wholly in Q, with five mass1/20 each.

Ignore all deeper beta source deletions, and also ignore the late35
source deletion when bounding the first-slot table. Divided by eta_l,
the resulting upper table is

| Cell | P | A | B | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| L | 0 | 0 | 0 | 1/10 | 1/5 |
| Other root1 cells | 0 | 0 | 1/5 | 1/10 | 1/5 |

The source loss in each of P,A,B,Q is positive, so H is the unique
source-free first slot. Every forbidden cofactor5 uses H. A saturated
cofactor15 must use root1, since h1=1/3>h0=1/6, and on that root
only H is source-free. These statements concern forbidden labels,
separately from the source labels used to build the table.

The four complete forbidden families3,9,5,15 consequently give

    mu<=w*Lambda,
    w=1-(1_root1+1_cell1+1_H+1_(root1 times H))/5.       (F3)

They have distinct original labels; their projected supports need
not be disjoint. Additivity follows from delta=V, not from a new
independence assumption. Applying(F3) to the upper table, for each
of the three possible L, gives

    mu(test5)<=29/450, mu(test15)<=8/225.               (F4)

All independent test slots and both test15 roots are included.

## 3. The remaining cylinder categories and their complete tails

Every saturated forbidden cofactor5^b has a source-free five cylinder.
Every saturated3*5^b has a source-free five cylinder on root1. Their
complete virtual deletions on any ternary event T are respectively
eta(T)/20 and eta(T intersect root1)/20. No equality of their deeper
five residues is required. Together with forbidden3 and9 this gives

    mu(T)<=Lambda(T)-(Lambda(T intersect root1)+Lambda(T intersect cell1))/5
                         -[eta(T)+eta(T intersect root1)]/20.    (F5)

For cells, the right side is

    (1/40,11/180,1/30-4*beta2/45,
                      1/30-4*beta3/45,1/30-4*beta4/45).

The root sums are31/360 and7/90. Hence arbitrary tests have caps

    modulus3:31/360, modulus9:11/180.                  (F6)

For a pure3 test cylinder of depth a>=3, use Lambda(T)<=d_l*eta(T)
and eta(T)<=3^-a. The five nonnegative coefficients in(F5) are

    7/10,11/20,3/10-4*beta2/5,
                    3/10-4*beta3/5,3/10-4*beta4/5.

Their maximum is7/10 throughout the simplex, so the complete pure3
tail is at most(7/10)/18=7/180.

For a pure5 test of depth b>=2 retain just the forbidden3 and9
families, then bound the nonnegative weighted source by the full
eta-times-five product. Its cap is

    [h-(h1+eta1)/5]*5^-b=(37/90)*5^-b.                (F7)

The complete pure5 tail is37/1800. The remaining zero-seven caps
retain their inherited sums:1/60 for3*5^b,b>=2;1/36 for9*5^b,b>=1;
and1/72 for3^a*5^b,a>=3,b>=1. The entire positive-seven part is
bounded by(s+C)/5=11/72, separately for every original test residue.
The unit contributes D=53/360.

These disjoint categories sum exactly to

    53/360+31/360+11/180+29/450+8/225+7/180
                   +37/1800+1/60+1/36+1/72+11/72=133/200.

This proves(F1), with no exponent cutoff.

## 4. A fixed old layout bounds the comparison over the whole face

Use the exact identity-cost formula66(N14) and the following one
choice of its two ternary layouts:

    b=(2,3,1,1,1), c=(1,2,2,2,2), k=6-b=(4,3,5,5,5).

The cofactor expressions in66 then have

    z=(14/5,37/20,21/10-5*beta2,
                    21/10-5*beta3,21/10-5*beta4),
    w=(2,3,5,5,5).

Thus max(z)=14/5 and max(k_l*d_l)=3 at cell0 over the entire
triangle. All other max branches in this fixed-layout expression
are constant. Both its source term and carrier term depend on beta
only through beta2+beta3+beta4=1/4. Its exact margin is9257/48600.
The old margin takes the minimum over all layouts, so this single
choice proves the upper bound throughout the face. Subtracting
from131/600 gives677/24300. No interpolation of a patched bound
or inference from a sample of interior points is used.

Exchanging the two root0 children is a compatible permutation of
ternary residue cylinders at every depth. It preserves their Haar
masses, all original modulus labels and independent test residues.
It carries this source face and carrier to616,628,640 and(root1,cell0).
The same argument therefore covers both controlling beta faces.

## 5. Varying actual families and exact reproduction

For actual finite families approaching a face point with S-D tending
to zero and the prescribed carrier, take a labelwise diagonal limit.
Complete forbidden-union tails give convergence of the source measures;
all test-load tails above have uniform geometric domination. Each
fixed original label can stabilize while the test as a whole changes.
The endpoint proof therefore gives the stated uniform limsup and
liminf. No realization of every relaxed beta point is assumed.

The [checker](../../frontier/endpoint-bounds/endpoint_k_face_linear.py) verifies all three
first-beta tables, fixed max branches on the affine beta simplex,
the original source data, complete test sums and constant old-layout
witness. The [certificate](../../certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json)
retains those exact rational inputs and outputs.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_k_face_linear.py --check
```

The ordinary budget argument supplies the universal geometry; finite
arithmetic verification does not claim to enumerate actual families.
