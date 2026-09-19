[Index](../marked_head_profile.md) · [Retained deep source](91-cell-vector-markers-retain-the-selected-deep-deletion.md) · [Source dual](88-a-weighted-source-comparison-on-the-broad-slab.md)

# Vector marked gains hold on the entire actual K faces

The selected-deep comparison of91 has a uniform positive gain for all41
linear costs on every actual K-control beta face with r=0 and the fixed
actual carrier specified below. In particular it covers the rho=0
saturated faces. This extends its
canonical-source evaluation to six complete two-dimensional triangles,
including both root0 orientations. It does not extend the estimate to a
neighborhood of those faces or produce a new global K bound.

For the original positive weights w_i, the uniform gains g_i satisfy

    every g_i>0,
    sum_i w_i*g_i=0.040745842520311264...>1/25.       (F1)

The exact values equal the41 canonical gains in91. In particular the
gains of R17(0,0), R19(0,0), and R5(0,0) equal their old source margins,
and the identity gain is4/225. Thus their source margins at zero residual
are at least doubled throughout these saturated faces. With a nonzero
common mass residual rho, while retaining r=0 and the same face and
carrier conditions, the pointwise comparison is

    actual_margin_i>=m_i+[g_i-P_i*rho]_+.            (F2)

Here m_i is constant on these faces, and P_i is91's maximum branch
coefficient, also constant on the faces. All costs use the same rho;
their penalties must be summed with the original weights if combined.
The g_i compare against91's specified old carrier margins. They are not
additional payments that can all be subtracted from another already
improved numerator: a consumer must compare each resulting cost bound
against its current bound and keep the smaller one.
These are ordinary mathematical conclusions with exact rational checks,
not Lean-verified declarations or an unrestricted Erdős7 solution.

## 1. The actual face is three small triangles

In the canonical root0 orientation the parameter tuple is

    deficit=(1/2,0,0,0,0), alpha=(0,1/4),
    beta=(0,0,beta2,beta3,beta4),
    late=(1/72,0,0,0,0), z=3/4,
    beta2+beta3+beta4=1/4, beta_l>=0.                (F3)

The actual carrier is(root1,cell1), and r=0. The first source beta label
must lie in a cell L with beta_L>=1/5, by the necessary original-label
condition of88. For L=2 the complete domain is the triangle with vertices

    (1/4,0,0), (1/5,1/20,0), (1/5,0,1/20).         (F4)

Permuting cells2,3,4 gives the other two triangles. Swapping cells0,1
gives the other root0 orientation and moves the carrier's cell to0.

For(F3), the source data are

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/2-beta2,1/2-beta3,1/2-beta4),
    n=(1/36,1/12,d2/9,d3/9,d4/9),
    s=1/4, dmax=3/4,
    a=(1,4/5,4/5,4/5,4/5).                         (F5)

All original source-slot feasibility inequalities are affine on this
triangle, and the exact checks validate them at its three vertices.
The three groups{0},{1},{2,3,4} have constant masses

    (1/36,1/12,5/36).

After reserving the full H mass, their constant non-H budgets are

    (1/60,11/180,13/180).                           (F6)

The source caps and modified column objective coefficients in91 are
constant too. Therefore every capacity dual chosen once for a fixed
cost, original layout, source slot and selected deep cell remains the
same dual on the entire triangle. The verifier checks equality of the
complete dual data at all vertices; constancy follows directly from
(F5),(F6), not from interpolation of optimum values.

## 2. The improved fixed-branch margin is concave in beta

Fix one cost f and the same original layouts b,c5 used in91. The vectors
v,k and the carrier coefficients are constant. Each n_l,d_l,z_l is
affine in beta. Write sigma=13/1215.

First cancel the original seven block e=0 exactly in

    common=zero7_raw(f)-zero5_raw(zero).

Here zero is precisely the e=0 seven-block cost. The remaining expression
is an affine source-mass term plus the raw blocks e>=1 and a nonnegative
multiple of the complete affine tail's raw block. Each raw block is
convex in beta: its shallow part is affine, and its deep part is a
positive sum of running maxima of affine increments, followed by the
exact geometric tail. The original maximum over layouts preserves
convexity. All41 costs and their retained seven-block costs are
eventually affine; there is no truncation or omitted infinite tail in
this argument. In particular, convexity is not asserted for an arbitrary
difference of two convex raw bounds: the common block was canceled first.

The old fixed-branch margin subtracts this convex common term, another
convex deep term, affine terms, and positive multiples of maxima of
affine terms. It is therefore concave. Its selected-depth term is

    -sigma*max_l z_l.

Adding91's credit Q_v-DeepShift changes this term exactly to

    -sigma*max_l(z_l+v_l/5).                        (F7)

No difference of two remaining maxima needs a concavity claim.

For each non-H slot, Q_(v,J) is the minimum over cells of

    B_v+sigma*vmax*(3/4-d_l)-U_J(q^(l)).            (F8)

The dual upper U_J(q^(l)) is constant by(F5),(F6). Thus(F8) is a minimum
of affine functions. The H term is also a minimum of affine functions,
since r=0. Their joint minimum Q_v is concave.

Consequently the full improved margin for each fixed(b,c5) is concave.
The minimum over all100 original branches remains concave: its
hypograph is the intersection of their convex hypographs. Hence its
value throughout the triangle is at least the minimum of its values at
the three vertices. The same reasoning applies to the old minimum.

## 3. The old minimum is constant, not merely vertex bounded

New minus old need not be concave, so a separate old upper bound is
necessary. For each retained common raw block, the certificate gives an
active canonical support with the following two properties:

* its baseline values on cells2,3,4 are equal;
* its selected deep maximum uses cell0 or cell1.

Its shallow value depends on root1 only through sum_l>=2 n_l, and its
selected deep availability is3/4. This support is constant in beta. It
is a valid lower bound on that raw block everywhere and equals the raw
block at the canonical vertex. Summing these supports with their exact
nonnegative seven weights gives a constant lower bound on common,
attaining the canonical value.

For every cost the certificate also selects an old controlling branch
with equal root1 baseline values. Its own deep maximum, selected z
maximum, and remaining k*d maximum admit active root0 witnesses. Keep
these particular witnesses as lower bounds on the subtracted maxima.
All shallow and fixed-carrier terms then depend on root1 only through
its fixed total mass. This gives, throughout the triangle,

    old_minimum<=this_old_branch<=m_i,              (F9)

where m_i is its canonical value. Exact evaluation gives old_minimum=m_i
at each of the three vertices. Old concavity supplies the opposite
inequality in the interior. Therefore

    old_minimum=m_i throughout the triangle.       (F10)

This uses explicit fixed witnesses and does not infer constancy merely
from equal vertex values.

## 4. Exact endpoints close the whole-face estimate

For every one of the41 costs, the program checks all100 branches at
each of the three vertices. At all three vertices it obtains the same
old margin m_i and the same strictly positive new gain g_i. By section2,
the improved minimum throughout the triangle is at least m_i+g_i.
By(F10), this is a uniform gain over the actual old comparison.

The geometric gap G, derivative vectors and eta are constant on the
face, so91's maximum residual coefficient P_i is constant. Since r=0,
the root1 best-slot loss r1 is also zero, and91's shared remaining
budget rho-(r+r1)/5 is precisely rho. This proves(F2). Taking rho=0 and
the original positive linear weights proves(F1).

Permuting root1 cells or swapping root0 cells preserves the root map,
the full original layout set, every cost's cell coefficients, the
three-group constraints, and the max/sum formulas. The verifier checks
these finite relabellings for all41 costs and all original layouts.
The ordinary covariance argument therefore gives the same gain on all
three first-beta triangles in both orientations.

The gain is uniform on these faces, but(F3) still fixes the deficits,
late mass, alpha,z, carrier and best-slot loss. Moving away from these
conditions is a separate estimation problem. No global comparison
constant follows by treating this lower-dimensional statement as an
already established neighborhood bound.

## Reproduction

The program is[vector_marked_face.py](../frontier/vector_marked_face.py);
the exact table and fixed old supports are in
[its certificate](../certificates/source_norms/vector_marked_face.json).
It pins91's finalized source and semantic certificate, checks the same
capacity duals across the triangle, reconstructs all endpoint branches,
and retains the complete-tail supports used in(F9).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/vector_marked_face.py --check
```
