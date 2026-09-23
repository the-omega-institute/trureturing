[Index](../../marked_head_profile.md) · [Original-block allocations](../001-064/58-optimal-original-seven-thresholds.md) · [Full AP11 law](67-exact-endpoint-survival-and-its-scalar-boundary.md) · [Previous face denominator](86-peeling-surviving-tails-improves-the-k-face-comparison.md) · [Complete stop-loss profile](98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md)

# Neighboring hinges strengthen complete AP11 survival

The new second and third hinges from98 improve the actual full-AP11
survival comparison on both entire saturated K-control beta faces:

    d>=1358432973299/17084377926000
       =0.079513165722683861448078809024... .         (A1)

The gain over86's denominator, still used by98, is exactly

    117048319/85421889630
       =0.001370237997625527357465927320...>0.       (A2)

Keeping98's complete numerator unchanged gives

    C0+N98/d<=465.4686568736608945314719229429... .   (A3)

The preceding face comparison was473.25200672608988085436.... This
decrease uses the original AP11 probability law and preserves every
original test across all auxiliary outcomes. All52 numerator terms,
its negative mass coefficient, complete square complements and count
tails remain present.

The scope is r=rho=0, survivor mass D=53/360, and every actual beta
distribution on both saturated control faces. This is an ordinary
exactly checked result. It is not a scalar optimality theorem, an
off-face extension, a new global K bound, a Lean proof or a solution of
unrestricted Erdős7. The comparison remains above403.

## 1. Preserve the original complete AP11 dilation law

The physical AP11/T4, AP13/T5 argument used in67 and86 gives

    d>=D-U4/6-(1/7)*sum_(n>=1)p_n*n*U(5/n),        (A4)
    p1=28/33, p_n=50/(3*11^n) for n>=2.

Here U(t) is an upper bound for integral h_t(A), h_t(v)=(v-t)_+,
valid for every independently labelled complete original357 test on
the same surviving measure. The probability p_n is the original
auxiliary AP11 comparison law with cap5/3; it is not a new sampling
law for the test residues or an independence assertion about events.

More explicitly, if A_e denotes an original old-coordinate test in
AP11 block e, its contribution remains attached to that same A_e for
every auxiliary outcome n>e. The existing dilation argument bounds
the positive cost by

    sum_(n>=1)p_n*sum_(e<n) integral h_(5/n)(A_e).

Use the uniform bound U(5/n) on each of these fixed original tests.
There are n such terms at outcome n, which gives the sum in(A4).
This operation neither replaces A_e by a fresh test at each n nor
identifies different original blocks. Nonnegative terms justify the
order of the sums, and the complete first-moment tail below controls
their limit.

## 2. Integer loads give exact neighboring-hinge identities

Let n>=1 and write5=n*a+r, with0<=r<n. For every integer v>=1,

    (n*v-5)_+=(n-r)*(v-a)_++r*(v-a-1)_+.            (A5)

If v<=a, both sides vanish. If v>=a+1, the right side is
(n-r)(v-a)+r(v-a-1)=n*v-5, which is nonnegative. Thus(A5) is an
identity on the entire integer domain, not interpolation of measured
upper bounds. For the four non-affine count terms it reads

    n=1: (v-5)_+=h5(v),
    n=2: (2*v-5)_+=h2(v)+h3(v),
    n=3: (3*v-5)_+=h1(v)+2*h2(v),
    n=4: (4*v-5)_+=3*h1(v)+h2(v).                   (A6)

All coefficients are nonnegative. Apply these identities to the same
A_e already present in each original block. The upper bounds from98
therefore give the following admissible values of n*U(5/n):

| n | Complete dilated-cost upper bound |
| --- | ---: |
| 1 | U5=1523903/9724050 |
| 2 | U2+U3=416993/661500 |
| 3 | U1+2*U2=38719/31500 |
| 4 | 3*U1+U2=3229/1750 |

The code checks the finite values and identical affine slope and
intercept of each remaining infinite integer tail. The proof(A5)
supplies the general all-load identity.

The old denominator used the chord bound

    U_old(t)=(4-t)*(L-D)/3+(t-1)*U4/3, 1<=t<=4.    (A7)

The new values in(A6) are strictly smaller at t=5/2,5/3,5/4. The
improvement comes from the newly retained intermediate observations
H2,H3. It does not add deletion credits to already settled costs.

## 3. Sum every remaining count exactly

For every n>=5 and every integer load v>=1,

    n*h_(5/n)(v)=n*v-5.

Since each original test separately has integral A_e<=L, summing its
n block contributions gives at most n*L-5*D. Thus the entire remainder
in(A4) is bounded by

    T1*L-5*T0*D,
    T0=sum_(n>=5)p_n=5/43923,
    T1=sum_(n>=5)n*p_n=17/29282.                    (A8)

Both sums are complete geometric series. The checker reconstructs
them from geometric closed forms and from the pinned original count
functions, verifying total probability1 and total first moment7/6.
There is no omitted count tail and no substituted finite maximum.

With U1=L-D, substituting(A6),(A8) into(A4) gives the independent
coefficient form

    d>=(308186/307461)*D-(1451/614922)*L
         -(2400/102487)*U2-(50/2541)*U3
         -U4/6-(4/33)*U5.                          (A9)

Insert D=53/360, L=1151/1800 and98's complete U2,U3,U4,U5 to obtain(A1).
The exact positive denominator gains from counts2,3,4 are respectively

    99499/78440670,
    377996/3882813165,
    188998/42710944815.

Their sum is(A2). The n=1 term, standalone U4 term, probabilities and
entire n>=5 tail are unchanged.

The higher U6,U7,U8 do not occur directly in this fixed survival law:
all its dilated thresholds5/n are at most5. They were useful in98's
numerator, which is retained here. Their absence from(A9) is not a
claim that no further scalar or geometric combination could help.

## 4. Retain the entire numerator and compare on the same measure

Profile98's numerator remains

    N98=r_mass*D+sum_(i=1..52)w_i*B_i
                         +c_square*(374/75),
    r_mass<0, w_i>0, c_square>0.                    (A10)

Every one of its52 upper bounds and all signed and complete square-tail
coefficients are copied exactly into the new certificate, then(A10)
is recomputed. It gives the same positive value

    N98=35.29386893590073135079943897679... .

The positive denominator(A1) is larger than the previous positive
lower bound. With C0=185694867601/8599322160, the exact ratio bound is

    45999207373210865146487861100656558222373103324321601
    /98823426011466392651464381291661827125000000000000,

which is(A3). It lowers98's comparison by7.78334985242898632288....
The uniform numerator and denominator bounds concern the same actual
survivor; they require no shared maximizing residue configuration.

## Reproduction

[whole_face_ap11_survival.py](../../frontier/moments-survival/whole_face_ap11_survival.py)
pins98's complete stop-loss profile and current numerator, checks the
original AP11 count probabilities and complete moments, proves the
finite/affine integer identities and independently reconstructs both
denominator formulas. Its
[certificate](../../certificates/source_norms/moments-survival/whole_face_ap11_survival.json)
retains all52 numerator terms and the three disjoint positive gains.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/whole_face_ap11_survival.py --check
```
