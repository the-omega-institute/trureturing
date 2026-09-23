[Index](../../marked_head_profile.md) · [Original allocated survival](../001-064/53-allocated-seven-thresholds-sharpen-actual-survival.md) · [Original joint table](../065-128/71-global-j-k-control-faces-and-exact-escape-gaps.md) · [Joint source-mass interpolation](183-the-original-signed-gap-retains-its-own-mass-through-interpolation.md)

# The original survival margin pays its own target change

For every original effective actual source and every
0<=sigma=1-qK<=1, the original sufficient comparison satisfies

    Phi(K0-h)>=gamma2*sigma-(gamma2-gamma1)*sigma^2
                 -h*(c0+c1*sigma+c2*sigma^2)
                 +(A-(23/42)*h)*rho,                  (GD1)

provided0<=h<=H, where

    H=0.618581269720449377004926977441...,
    c0=240585528019/3208936500000,
    c1=90112853/106964550000,
    c2=272569433/3208936500000.                       (GD2)

The whole far interval1/2<=sigma<=1 supports this H. The preceding
joint mass argument183 supported0.31300623832873406089... there.
The improvement retains the original allocated survival margin in
the target change, rather than paying the target change with S.
Neither polynomial payment is asserted to be an upper bound on the
actual denominator by itself.

This is an ordinary source theorem with exact rational verification.
It supplies a stronger unmarked branch. A complete joined global
comparison, all its fallback bounds and terminal errors remain a
separate obligation; unrestricted Erdos7 is not resolved here.

## 1. The two true coefficients remain nonnegative

Retain exactly53(A14)--(A15) and the notation of183:

    q=23/42,
    E=q*S+sum_c pi_c*M_c(theta),
    A=q*(K0-b)-L,
    S0=sum_c pi_c*D_c(theta), rho=S-S0>=0.

The original sufficient signed function at the changed target is
exactly

    Phi(K0-h)=(A-q*h)*S
             +sum_c pi_c*[(K0-b-h)*M_c(theta)
                                      +C_c(theta)]. (GD3)

Unlike183, this formula has not used E<=S. The true functions D_c,
M_c and C_c are separately concave in each of the original five
source factors, as established in49 §7 and53 §7. The unchanged
numerator correction includes its positive margin coefficients and
the negative separately convex raw81 operator.

Consequently the true function

    F_(h,c)(theta)=(A-q*h)*D_c(theta)
                    +(K0-b-h)*M_c(theta)+C_c(theta) (GD4)

is separately concave whenever

    A-q*h>=0 and K0-b-h>=0.                       (GD5)

Both inequalities are strict at H and therefore hold throughout
the interval[0,H]. The helper verifies the original A directly
from q, K0, b and the complete original numerator slope L.

## 2. The denominator payment belongs to the same original row

At an original source vertex v and carrier c, let m_vc and k_vc
be the survival-margin and numerator-correction lower bounds used
to form71's original entry. That entry has the decomposition

    g_vc=A*D_c(v)+(K0-b)*m_vc+k_vc.                (GD6)

Define its associated denominator value

    e_vc=q*D_c(v)+m_vc.                           (GD7)

Because the two coefficients in(GD5) are nonnegative, application
of the original lower bounds to the reweighted true function gives

    F_(h,c)(v)>=(A-q*h)*D_c(v)
                    +(K0-b-h)*m_vc+k_vc
                =g_vc-h*e_vc.                    (GD8)

This is not the inference that an arbitrary lower bound for a gap
minus h times an arbitrary lower bound for a denominator remains
a lower bound. The positive-coefficient decomposition(GD4)--(GD8)
is what makes this subtraction valid. Replacing m_vc with a
different survival bound without reconstructing(GD6) would not
justify the same calculation.

The helper therefore reconstructs m_vc using the exact original53
allocation provider. For all1296 vertices and18 carriers it forms

    m_vc=m25_vc/22+m4_vc/6+(4/33)*m5_vc,

with53's full-root allocations and its rule of maximizing the
entire source expression over compatible completions of a partial
carrier. The routine independently recovers all46656 old full and
partial hinge margins before applying the allocations. Its complete
allocation statistics and conditional-margin digest must equal53's
existing certificate exactly. In particular,46's pre-allocation M
is not used in(GD7).

The same newly reconstructed margins are those used by
global_control_faces.analyze to form the71 table. The helper also
reconstructs all46656 entries of that original gap table from the
existing rational dictionary and checks its original ordered digest.
The paired table therefore preserves the specific source, carrier,
mass endpoint and allocated survival margin of every entry.

Iterated Jensen applied to(GD4), followed by averaging with the
same actual pi and using S=S0+rho, yields

    Phi(K0-h)>=sum_(v,c) Lambda_v*pi_c
                            [g_vc-h*e_vc]
                      +(A-q*h)*rho.                (GD9)

All residual terms refer to the same actual rho. The Jensen
surplus is nonnegative because(GD5) holds. No fixed-precision or
finite-vertex approximation of the actual source is asserted.

## 3. Exact joint layers of the full table

On the six original K controls the pair is(0,eK); on the eighteen
original J controls it is(gamma1,eJ), where

    eK=240585528019/3208936500000
       =0.07497360200770566821...,
    eJ=40593580507/534822750000
       =0.07590099805402818036... .                (GD10)

Set

    H=gamma1/eJ
      =15240056495574031935365456355486859072608164346131
        /24637112763633066609402747307132045210251692688000.

For every original row outside K union J, the exact table proves

    g_vc-h*e_vc>=gamma2-h*eB,
    eB=34755559087/458419500000
      =0.07581605731649722579...,
                              0<=h<=H.             (GD11)

It suffices to check h=0 and h=H because each difference is affine
in h. Both endpoint checks retain all23304 rows outside K union J.
The only controls at either endpoint are source386 with carrier(1,1)
and source592 with carrier(1,0). Their actual associated denominator
value is exactly eB and their old gap is exactly gamma2.

The upper actual-mass endpoint is also checked for every source and
carrier. Its gap is g_vc+A*(s-D_c), its associated denominator is
q*s+m_vc, and its excess over(GD8) is

    (A-q*h)*(s-D_c)>=0.

Among both mass endpoints of all rows outside K, the exact minimum
gap/associated-denominator ratio is H. Exactly the eighteen J lower
endpoints attain it. This is a property of the complete relaxed
table; it does not assert actual-family attainment.

## 4. Product exclusion gives a single continuum envelope

Let qK and qJ be the original product-barycentric masses, with the
same actual carrier factor. Write sigma=1-qK and u=sigma-qJ. The
original product separation retained in94 gives qJ<=sigma^2.
Equations(GD9)--(GD11) give

    Phi(K0-h)>=-h*eK*qK+(gamma1-h*eJ)*qJ
                       +(gamma2-h*eB)*u
                       +(A-q*h)*rho.               (GD12)

After inserting u=sigma-qJ, the coefficient of qJ is

    gamma1-gamma2-h*(eJ-eB)<0.

Thus qJ<=sigma^2 implies(GD1), with

    c0=eK, c1=eB-eK>0, c2=eJ-eB>0.

Both small differences in(GD2) are exact rational values; no
separate worst-case denominator is substituted for them.

At h=H the part independent of rho factors as

    (1-sigma)*[(gamma2-H*eB)*sigma-H*eK].          (GD13)

Here gamma2-H*eB=0.53469717427615405064...>0. At sigma=1/2,
(GD13) is0.11048566060631741021...>0; at sigma=1 it is zero.
Its lower root is0.08673557324896171041...<1/2. It follows that
(GD1) is nonnegative on the entire far interval. Smaller h retain
the result because the derivative of its right side in h is

    -(c0+c1*sigma+c2*sigma^2+q*rho)<0.

The estimate(GD1) itself holds for every0<=sigma<=1, including
the near and intermediate source ranges, whether or not its
right side is nonnegative without other information.

## 5. Reproduction and boundaries

The [helper](../../frontier/cover-geometry/joint_gap_denominator_escape.py) freshly
reconstructs all original allocated survival margins on each run.
The [certificate](../../certificates/source_norms/cover-geometry/joint_gap_denominator_escape.json)
retains their original digest, the same-source denominator-table
digest, both complete decrement-endpoint checks, the joint layer
constants and the exact polynomial. All calculations use rational
arithmetic and the canonical multipart reader/writer.

The ordinary proof retains the original source domain, all full,
partial and empty carriers, all independent numerator labels and
the complete exponent/count tails. It neither changes a canonical
earlier result nor asserts that the numerical payment polynomial
alone bounds the actual E. No Lean or frozen-state claim is made.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_gap_denominator_escape.py --check
```
