[Index](../marked_head_profile.md) · [Exact forced27 face](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Actual concentration](106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Shared capacity budget](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Complete pure3 projection](119-the-complete-pure-three-family-has-one-projected-defect.md)

# The original forced27 exclusion has a quantitative defect

Let qK>=1-sigma with0<=sigma<=2/27, on the actual effective9
branch. Choose106's orientation with source deficit and late deletion
concentrated in cell0, and distinguished shallow carrier(1,1).
For every original forbidden cofactor27 outside cell1,

    Lambda(J)<=dmax/27-g27(sigma),
    g27(sigma)=1/135-sigma/72>=31/4860.              (Q27.1)

Absent labels incur at least the same capacity loss. Consequently
the complete wrong-cell seven weight and virtual mass are controlled
by the actual cofactor27 defect E27. A positive ideal deletion measure
supported in cell1 has defect

    Xi27(1)<=(z-dmax)/135+[dmax/(27*g27)]*E27,
    dmax/(27*g27)<=415/93.                         (Q27.2)

This extends75's forced27 conclusion to a finite neighborhood. It
requires no restriction on the best-five-slot loss r. When combined
with5/15 slot inequalities, their own packing guards still apply.
E27 is part of119's E3, never another copy of that capacity or rho.
These are ordinary proofs and rational certificates, not Lean results
or a new complete global comparison.

## 1. The original source27 child is exactly empty

Use48's actual raw ternary survivor eta and raw35 source Lambda.
Concentration gives

    deficit0>=(1-sigma)/2, late0>=(1-sigma)/72,
    alpha0<=sigma/4, beta0+beta1<=sigma/4,
    3/4<=z<=3/4+sigma/4, alpha1>=(1-sigma)/4.      (Q27.3)

The pure3 source deletion in cell0 has mass deficit0/9, at least
(1-sigma)/18. If the original source modulus27 were absent or
outside cell0, all pure3 deletion there would have to come from
depths a>=4. Their complete raw capacity is1/54. This contradicts
(1-sigma)/18>1/54 on the stated interval.

Thus the original source27 is present in cell0. Write S for its
depth3 child. All of S is source-deleted, so

    eta(S)=Lambda(S)=0.                            (Q27.4)

This uses the actual source cylinder, not an auxiliary child chosen
from deficit coordinates. Later source labels may overlap S; no
disjointness is assumed away from saturation.

The complete late source family has raw capacity1/72. Removing its
single original label(a,b)=(3,1) leaves capacity

    1/72-1/135=7/1080.

Let ell31 be the unique additional deletion contributed in cell0 by
that label after every other late label has been included. Then

    ell31>=late0-7/1080>=1/135-sigma/72=g27>0.      (Q27.5)

This proves that the label is present and its ternary depth3 child
J lies in cell0. Its five coordinate has raw mass1/5, whence

    eta(J)>=5*ell31>=1/27-5*sigma/72.              (Q27.6)

Since eta(S)=0, J differs from S. Let R be the third child. The
total surviving ternary mass in cell0 is at most(1+sigma)/18.
Subtract(Q27.6) and(Q27.4):

    eta(R)<=1/54+sigma/8.                          (Q27.7)

Only the individual original source labels27 and135 were singled
out. Every other source depth remains in the complete raw budgets.

## 2. Retaining the same actual availability sharpens all exclusions

Write d0=z-alpha0-beta0 and dmax=max_c d_c. Before late deletion,
the source on any cell0 child is bounded by d0 times its pure3
survivor mass. In J at least ell31 is additionally deleted. Thus

    Lambda(J)<=d0/27-ell31<=dmax/27-g27,
    Lambda(R)<=d0*(1/54+sigma/8).                  (Q27.8)

The comparison d0<=dmax is kept before estimating either quantity.
Since1/54-sigma/8>0, the third-child gap is at least

    dmax*(1/54-sigma/8)
       >=(3/4-sigma/2)*(1/54-sigma/8).             (Q27.9)

Here dmax>=3/4-sigma/2 follows directly from(Q27.3). For any
root1 cell, d_c<=z-alpha1<=1/2+sigma/2. A depth3 child in that
root therefore has gap at least(1/4-sigma)/27. Removed pure3
roots or mod9 cells have zero surviving mass. The four guards,
in the order S,J,R,root1, are consequently

    (3/4-sigma/2)/27,
    g27,
    (3/4-sigma/2)*(1/54-sigma/8),
    (1/4-sigma)/27.                               (Q27.10)

Each is at least g27 throughout[0,2/27]. The only quadratic check is

    third_guard-g27=7/1080-77*sigma/864+sigma^2/16.

Its derivative is at most-23/288 on the interval, and its value
at2/27 is13/58320>0. The root1 difference is

    1/540-5*sigma/216>=1/7290>0.

The S difference is11/540-sigma/216>0. These exact inequalities
prove(Q27.1), including the interval endpoints. No realization of
an arbitrary relaxed parameter vector is used.

## 3. One actual E27 pays for every wrong or absent original label

For each original forbidden label27*7^e use its actual ternary
cylinder J_e and weight u_e=6/(5*7^e). Absent labels have zero
virtual measure. Put

    V27=sum_(e>=1)u_e*(Lambda restricted to J_e),
    c27=dmax/27, E27=c27/5-V27(1)>=0.

A label is good precisely when present and J_e lies in cell1.
All other labels, including absent ones, are wrong. Define

    qwrong=sum_wrong u_e, 0<=qwrong<=1/5,
    V27=Vgood+Vbad.

By(Q27.1), each present wrong carrier has raw mass at most c27-g27.
Absent labels lose their full c27 cap, and c27>=g27. Summing all
original seven depths, including every missing depth, gives

    E27>=g27*qwrong,
    Vbad(1)<=(c27-g27)*qwrong
             <=(c27/g27-1)*E27.                  (Q27.11)

The second bound concerns the actual wrong-family virtual measure;
it does not assume the seven residues agree or are disjoint.

Let q be raw Haar5 restricted to the actual pure5 survivor, q(1)=z.
For each good label take the reference

    u_e*(Haar3 restricted to J_e) tensor q.

It dominates that label's actual virtual measure, by119's source
product domination. For every wrong or absent label choose any
depth3 child of cell1 as its reference, and credit none of its actual
wrong deletion. Summing these references defines Phi27. Then

    supp(Phi27) is in cell1,
    (Phi27)^5=q/135,
    Xi27=Phi27-Vgood>=0.                           (Q27.12)

The reference is chosen once for the original family, independently
of all later tests. Different good labels keep their different
actual children and seven residues. Taking total masses and using
(Q27.11) gives

    Xi27(1)=z/135-Vgood(1)
            =(z-dmax)/135+E27+Vbad(1)
            <=(z-dmax)/135+[dmax/(27*g27)]*E27.    (Q27.13)

The coefficient already includes E27 itself. Adding another E27
would discard the sharper wrong-carrier cap c27-g27 used here.
Since dmax<=z<=3/4+sigma/4 and g27 is positive and decreasing,

    dmax/(27*g27)<=415/93.

On the smaller interval sigma<=1/27, the corresponding uniform
values are g27>=67/9720 and dmax/(27*g27)<=820/201.

## 4. The complete later-depth family and the same residual

For every original forbidden3^a*7^e with a>=4, take its actual
depth-a ternary cylinder as reference when present, or any such
cylinder when absent. The product cap from119 gives

    Phi_ge4>=V_ge4,
    Xi_ge4=Phi_ge4-V_ge4>=0,
    Phi_ge4(1)=z/270,
    Xi_ge4(1)=(z-dmax)/270+E_ge4,
    E_ge4=dmax/270-V_ge4(1)>=0.                   (Q27.14)

The factor1/270 is the complete sum
sum_(a>=4,e>=1)3^-a*u_e, not a finite-depth substitute. Hence

    E3=E27+E_ge4.

Let Omega=V-delta>=0 be the one actual virtual/union error of57,
with Omega(1)=omega. Define

    Phi_deep=Phi27+Phi_ge4,
    Psi_deep=Xi27+Xi_ge4+Omega.

Since Vgood+V_ge4 is an actual subfamily of V,

    delta>=Phi_deep-Psi_deep,
    Psi_deep(1)<=(z-dmax)/90+E_ge4
                       +[dmax/(27*g27)]*E27+omega. (Q27.15)

If other distinct virtual families dominate(1-w)*Lambda, the same
identity retains their credit without another union error:

    mu<=w*Lambda-Phi_deep+Psi_deep.                (Q27.16)

This is a measure inequality; the signed reference
w*Lambda-Phi_deep is not asserted positive. In particular it does
not automatically satisfy115's separate positive-reference premise.

The complete cofactor5,15,27 and deeper pure3 capacities are disjoint
original families. Consequently

    E5+E15+E27+E_ge4+omega<=rho.                   (Q27.17)

Where117's G5,G15 guards hold, write x5=E5-r/5 and
x15=E15-r1/5. Then the simultaneous necessary constraints are

    x5>=G5*q5, x15>=G15*q15,
    x5+x15+E27+E_ge4+omega<=rho-(r+r1)/5.         (Q27.18)

The projected q5/q15 budget cannot be spent once and then assigned
again to E27 or E_ge4. The selected pure3 defect in102 is likewise
a contained subfamily, not an additional independent allowance.
Using119's z-dmax<=3*sigma/8 gives the conservative common bound

    Psi_deep(1)<=sigma/240+(415/93)*rho.           (Q27.19)

The separated form(Q27.15) retains more information for a consumer.

## 5. The positive defect also controls complete independent tails

A small total mass alone does not control an unbounded test load.
Here Xi27+Xi_ge4<=Phi_deep and Omega<=V supply cylinder bounds.
For any independently chosen original3^A5^B test cylinder C, put

    S3(A)=1/18                      if A<=3,
          (A-3/2)*3^-A             if A>=3.

Intersections of two ternary cylinders have mass at most
3^-max(a,A), whether their residues agree or not. Thus

    Phi_deep(C)<=(1/5)*S3(A)*5^-B,
    V(C)<=(1/5)*[(A+3/2)*(B+5/4)-1]*3^-A*5^-B.   (Q27.20)

The latter sum includes all nonunit old cofactors(a,b), and removes
only(a,b)=(0,0). Both are complete positive geometric sums. Therefore
Psi_deep(C) is at most the sum of(Q27.20), and also at most any
valid mass upper e from(Q27.15). In particular, for arbitrary
independent five-coordinate cylinders F_b of depth b,

    Psi_deep(full ternary times F_b)
       <=min(e,[(108*b+67)/360]*5^-b).             (Q27.21)

For a complete family b>=b0, let N>=b0 be the first integer where
[(108*N+67)/360]*5^-N<=e. When e>0 its full error is at most

    (N-b0)*e+[(270*N+235)/720]*5^-N.              (Q27.22)

At e=0 the error is zero. The displayed last term is the entire
remaining tail; no common residue or nesting is assumed for the
tests. The two-coordinate cap in(Q27.20) is also summable over
all A,B. These bounds establish a usable complete-tail defect,
without importing a saturation-only correction from another family.

## Exact checks and boundary

[quantitative_forced27.py](../frontier/quantitative_forced27.py) and its
[certificate](../certificates/source_norms/quantitative_forced27.json)
check the interval coefficients, complete tail identities and seven
finite actual families based on48's original398 source construction.
The source height is5 and its actual qK gives
sigma=28800389514256941173/389490222930908203125<2/27.
The forbidden27 labels use cell1, each of the three cell0 children,
root1, varying children with an absent label, or complete absence.
Their seven residues vary independently. The actual seven union,
virtual mass and one omega are computed separately.

The checks verify original source-child masses, complete wrong-label
weights, positive ideal27 measures, arbitrary five sections and the
shared E27+E_ge4=E3 budget. They include all omitted seven and later3
capacity tails. The continuum proof above supplies the generality.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/quantitative_forced27.py --check
```

At sigma=rho=0, qwrong=0, Xi27=0 and(Q27.12) recovers75's exact
cell1 deletion q/135, of total1/180. Off the face, the statement is
the quantitative defect inequality, not literal forcing of every
label into cell1. A complete global consumer still must combine this
bridge with the other source families and the original signed costs.
