[Index](../marked_head_profile.md) · [Actual source](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Mean correction](109-the-mean-and-all-hinges-share-one-original-test.md) · [Finite-source transport](116-signed-face-duals-transport-one-shared-finite-source.md)

# Two complete deep-five families transport the mean credit

The C5 portion of109's mean-head correction has an explicit actual
off-face replacement. It comes from two distinct complete forbidden
families,5^b*7^e and3*5^b*7^e with b>=2,e>=1. Their unused capacities
and every other cofactor defect share the existing residual rho.

Let eta be the actual raw pure3 survivor measure, of root masses
h0<h1 and total h. Put

    E5d=h/100-V5d(1), E15d=h1/100-V15d(1),
    R=h1/(h1-h0).                                 (DF1)

For a genuine head with ternary root r3 and depth-two cell c9,
define

    C5_actual=[(1+r3)*h_r3+(1+ROOT(c9))*eta_c9]/100,
    M5=1+I_(ROOT(c9)=r3),
    M15=I_(r3=1)+I_(ROOT(c9)=1).                  (DF2)

Then the virtual deletion contributed to the mean head by these
two complete families is at least

    C5_actual-M5*E5d-M15*R*E15d.                  (DF3)

At a saturated K face the defects vanish and this is exactly109's
C5. Formula(DF3) is an ordinary actual-measure statement, not a
consequence of continuity of an optimized endpoint LP. Its two
families are separate from the shallow5/15 and complete pure3
families. No additional copy of the union error is needed.

## 1. The first projection has exactly its existing capacity deficit

The source satisfies Lambda<=eta tensor Haar5. Therefore for an
arbitrary original five cylinder F of depth b,

    (Lambda restricted to F)^3<=5^-b*eta.          (DF4)

Here superscript3 denotes projection onto the ternary coordinate.
Use the actual F_(b,e) of each forbidden label; an absent label
has restricted measure zero. The complete coefficient is

    sum_(b>=2,e>=1)5^-b*6/(5*7^e)=1/100.

Thus

    Xi5=eta/100-(V5d)^3>=0,
    Xi5(1)=E5d.                                  (DF5)

The complete cofactor5^b capacity is h/20 in85; its shallow b=1
part is h/25. Their difference h/100 is exactly the deep family's
part of T. Hence E5d>=0 is an existing nonnegative capacity deficit.
No absence or exponent remainder is omitted.

## 2. The second projection retains its correct root

The effective9 source has h1>h0, as proved in48. The root removed
by the first ternary source label has no surviving mass. For
V15d, retain only labels whose ternary root is1, calling their
virtual measure V15correct. Their projection obeys

    (V15correct)^3<=eta restricted to root1 /100.

Define the positive measure

    Xi15=eta restricted to root1 /100-(V15correct)^3.

Its total mass is

    Xi15(1)=E15d+V15wrong(1).                      (DF6)

Every wrong surviving root0 label of depth b has old mass m<=h0*5^-b.
Against its actual capacity h1*5^-b, its unused-capacity amount
is at least(h1-h0)*5^-b. More precisely,

    m<=h0/(h1-h0)*(h1*5^-b-m).

Multiply by its original u_e and sum. Absent labels and labels
in the removed root contribute zero wrong mass and nonnegative
capacity deficit. Consequently

    V15wrong(1)<=h0/(h1-h0)*E15d,
    Xi15(1)<=R*E15d.                              (DF7)

The source cofactor3*5^b capacity is h1/20; its shallow part is
h1/25, leaving h1/100. Thus E15d is a separate nonnegative summand
of T-V(1). All residues of the five cylinders remain independent.

## 3. Both measures pay the same root and cell test

Let

    psi=I_(test3)+I_(test9).

This function depends only on the ternary coordinate. Its supremum
on the surviving ternary space is M5 in(DF2), and its supremum
on root1 is M15. A cell and a root overlap exactly when the root
label of the cell equals the chosen test root. This proves both
supremum formulas without choosing separate test layouts.

Since V15d>=V15correct, equations(DF5)--(DF7) give

    (V5d+V15d)(psi)
       >=[eta(psi)+eta(root1*psi)]/100
                           -Xi5(psi)-Xi15(psi)
       >=C5_actual-M5*E5d-M15*R*E15d.

This is(DF3). The remaining head indicators are nonnegative, so
their omission preserves a lower bound on this family's payment
against B-1. In particular the test5,15,45 residues are not fixed
or equated with forbidden residues to obtain this result.

Nonnegativity of virtual deletion also permits the positive part
of(DF3) as a lower bound. However, subtracting that clipped credit
from an upper-cost objective need not preserve convexity. A convex
shared-budget consumer can retain the affine expression(DF3), or
must prove the properties of its chosen clipped optimization.

## 4. One common residual pays the errors once

The complete families involved so far are disjoint as original
cofactor labels:

    shallow5, shallow15, deep pure3,
    deep5, deep3*5^b with ternary exponent1.

The last expression means3*5^b, b>=2, not a family of deep ternary
exponents. Their distinct unused capacities satisfy

    E5+E15+E3+E5d+E15d+omega<=rho.                (DF8)

Here E3 includes E27 and the remaining pure3 depths, while omega
is the single cap/union error(V-delta)(1). E27 must not be added
again to E3. Likewise, shallow5 and deep5 are distinguished by
b=1 versus b>=2, and the same separation holds for15.

On117's valid packing domain this implies

    G5*q5+G15*q15+E3+E5d+E15d+omega
                                      <=rho-(r+r1)/5.        (DF9)

To use(DF3) in116, retain both virtual families in the same
measure inequality before applying its bounded-head transfer.
Multiply the reference and both capacity penalties by the mean
coefficient a1. The existing single transfer term M_a*omega
already applies to the full retained finite cost. There is no
second M_a*omega, nor an extra a1*M*omega for each of these two
families. Formula(DF9) keeps all capacity penalties in one joint
optimization; it does not grant them separate copies of rho.

## 5. Concentration bounds the root price sharply

For qK>=1-sigma,0<=sigma<1/2, put x equal to the total root1
deficit and y to the total root0 deficit. By106/117,

    y>=(1-sigma)/2, x>=0, x+y<=1/2,
    R=(3-x)/(1+y-x).

For fixed x this decreases with y; at y=(1-sigma)/2 it increases
with x because2-y>0. Since x<=sigma/2,

    R<=(6-sigma)/(3-2*sigma).                    (DF10)

This uses one total-deficit budget. In particular the right side
is2 at sigma=0,161/79 at sigma=1/27 and160/77 at sigma=2/27.
These are bounds on the actual family price, not changes to the
underlying probability distribution.

## Verification and remaining obligations

[deep_five_mean_transport.py](../frontier/deep_five_mean_transport.py)
exports the exact reference, two prices and affine/clipped credits.
It reuses the existing actual source constructor and checks four
finite configurations of the two original families: correct roots,
wrong roots, mixed roots and absent labels. These40 head checks retain
one test root/cell per comparison; their clipped lower credits are zero.
A fifth genuine finite family places all labels2<=b<=6,1<=e<=6 in
an exactly verified source-free H fiber. One3*5^6*7^6 label is moved
to root0, producing nonzero wrong-root mass2/16544390625. All ten
root/cell heads then have strictly positive lower credit, at least
122390011/47269687500. All other exponent labels are absent and their
full capacity remains in the same defects. The
[certificate](../certificates/source_norms/deep_five_mean_transport.json)
also verifies complete geometric coefficients and the concentrated
root-price values. The ordinary measure arguments supply all heights.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/deep_five_mean_transport.py --check
```

This restores the C5 part of the additional mean-head credit. It
does not by itself transport all complete tail operators of98/109,
compute the full shared-budget maximum, or prove a new global K.
No Lean verification or unrestricted Erdős #7 resolution is claimed.
