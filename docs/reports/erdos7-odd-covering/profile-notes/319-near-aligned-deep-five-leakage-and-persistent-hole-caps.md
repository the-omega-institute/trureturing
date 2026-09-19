[Index](../marked_head_profile.md) · [Actual virtual measure](57-common-deleted-measure-coupling.md) · [Sharp aligned surplus](311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md) · [Complete adjusted ledger](312-an-aligned-j-source-has-a-complete-own-test-and-residual-deletion-interface.md) · [Endpoint quadratic observations](316-complete-quadratic-observations-on-the-actual-aligned-source.md)

# Near-aligned deep-five leakage and persistent hole caps

These ordinary lemmas use311's near-face source geometry,312's adjusted
complete cap ledger, and57's actual-source virtual cofactor measure.
They concern necessary source inequalities. They assert neither a complete
numerical neighborhood comparison nor a new LP or Lean result.

## 1. Definitions and the complete deep-five subledger

Take any actual finite effective9 configuration with

    qJ>=1-delta, 0<=delta<=1/1000,

and original SOURCE45 and SOURCE135 in the same surviving mod9 cell L.
Choose311's orientation. Its four forced first-five slots are P,A,B,Q,
from original5,15,45,25; let H be the remaining slot. Original135 is
I times H, where I is an actual ternary27 cylinder inside L in root1.
No own-test residue is identified with any of these source residues.

Let eta be the actual pure3 surviving measure, h=eta(total),
h0=eta(root0), h1=eta(root1). Let Lambda be the single actual raw35
source measure. Then Lambda is dominated by eta tensor Haar5, and
it assigns zero mass to every present original old35 forbidden cylinder.

Use311's complete root1 late ledger, including missing labels:

    lambda=1/72-late(root1), 0<=lambda<=delta/72,
    q135>=1/135-lambda,
    g_delta=1/135-lambda,
    a=5g_delta=1/27-5lambda.

The letter a in these formulas is a real gap coefficient, not a ternary
exponent. In particular

    0<(8-15delta)/216 <= a <=1/27.

For original mixed7 labels use57's fixed weights
u_e=6/(5*7^e), with complete sum1/5. Define the positive virtual
measure E5vir on the actual raw source by retaining exactly the two
families with five exponent b>=2:

    E5vir = sum_(b>=2,e>=1) u_e Lambda restricted to F_(b,e)
          + sum_(b>=2,e>=1) u_e Lambda restricted to
                                      [R_(b,e) times F'_(b,e)].

The first family has old cofactor5^b. The second has old cofactor3*5^b;
R may be either surviving root or the killed root. Every original label
has its own carrier and seven residue. Absent labels have zero restricted
measure. This is a submeasure of V, not of Omega=V-Dact and not an assumed
summand of the actual union deletion Dact. In particular b=1 labels5/15
are excluded; their adjusted caps have a different role.

The unchanged nominal raw caps of these deep families are respectively
h*5^-b and h1*5^-b. Therefore their COMPLETE capacity-defect subledger is

    D5cap=(h+h1)/100-E5vir(1)
          =sum_(all deep labels) u_e [nominal cap-Lambda(carrier)] >=0.

The factor1/100 is(sum_(b>=2)5^-b)(sum_(e>=1)u_e)=(1/20)(1/5).
Every missing deep label still contributes its full nominal capacity
defect, so this identity does not truncate the finite family's absent
tails. For the adjusted complete ledger in312 put

    Dcap=(C-2g_delta)/5-V(1),
    epsilon_*=S-D-2g_delta/5=Dcap+Omega(1), D=s-C/5.

Only the b=1 cofactor5/15 caps were adjusted. Thus the deep-family
nominal caps above are unchanged terms of the same nonnegative ledger,
and

    0<=D5cap<=Dcap<=epsilon_*,
    epsilon_*<=rho-2/675+7delta/36.

## 2. Uniform leakage out of Q

For every present pure-five or alpha-five forbidden label with b>=2
whose quinary carrier lies outside Q, its actual raw mass m obeys

    m <= (k-a)*5^-b,
    k=h for pure-five, k=h1 for alpha-five.             (L1)

To see the H case, the assigned late piece of original135 is contained
in (I intersect pure3-survivor) times H. Therefore

    q135<=eta(I)/5, so eta(I)>=a.                       (L2)

For any depth-b quinary cylinder F inside H, original135 deletes all
of (I intersect pure3-survivor) times F. Hence

    Lambda(F)<=(h-eta(I))*5^-b,
    Lambda(root1 times F)<=(h1-eta(I))*5^-b.

Other source deletions only improve these inequalities. This proves the
H cases of(L1) without assuming that eta(I)=1/27.

For the other slots, source5 kills P, source15 kills root1 times A,
and source45 kills L times B. Relative to the indicated nominal
coefficient, the losses are at least:

| Family/carrier | P | A | B | H |
|---|---:|---:|---:|---:|
|pure5, relative to h|h|h1|eta(L)|eta(I)|
|alpha5 on root1, relative to h1|h1|h1|eta(L)|eta(I)|

For alpha on root0, use m<=h0*5^-b and loss h1-h0. On the killed root
m=0 and the loss is h1. The311 inequalities give

    h>=1/2, h1>=1/3-delta/18,
    eta(L)>=1/9-delta/18, h1-h0>=1/6-delta/9.

All four displayed lower bounds exceed1/27 on delta<=1/1000, and
lambda>=0 gives a<=1/27. Together with(L2) these prove(L1) for every
non-Q carrier, including all wrong-root alpha labels. A label supported
on Q contributes zero to the off-Q mass, regardless of its ternary root.

For one non-Q label let d_i=u_e(k*5^-b-m) be its own nonnegative capacity
defect. Since m<= (k-a)*5^-b and k<=h,

    u_e*m <= (k/a-1)*d_i <= (h/a-1)*d_i.               (L3)

Sum over all such original labels, keeping the full geometric tails.
Each depth-b quinary cylinder lies wholly in one first-five slot, so its
contribution outside Q is either its full mass or zero. Thus

    E5vir(Q^c) <= (h/a-1)*D5cap
               <= (h/a-1)*Dcap
               <= (h/a-1)*epsilon_*.                 (L4)

No Omega payment was used to prove the first two inequalities. Omega
enters only through Dcap<=epsilon_*; these are not additive error credits.
If one separately defines actual deletion by the union of this deep
family, its off-Q mass is at most E5vir(Q^c) by the union bound and
p_i<=u_i. That union need not be a disjoint component of total Dact.

The explicit common coefficient follows from h<=1/2+delta/18:

    h/a-1 <= (100+27delta)/(8-15delta)
            <=100027/7985 <13.                        (L5)

The rational function is increasing, with derivative
1716/(8-15delta)^2. Consequently the uniform convenient forms are

    E5vir(Q^c) <= (100027/7985)*epsilon_* <=13epsilon_*,
    E5vir(Q^c) <=13[rho-2/675+7delta/36].              (L6)

Use <=13epsilon_* to include epsilon_*=0; strict <13epsilon_* is only
valid when epsilon_*>0. At the exact endpoint epsilon_*=0 this recovers
full Q support. The total left side is the sum of all20 non-Q coarse
cell-slot masses, not an independently allocated error for each row.

A more precise split retains the two virtual subfamilies Vp and Va:

    Dp=h/100-Vp(1), Da=h1/100-Va(1), Dp+Da=D5cap,
    Vp(Q^c)<=(h/a-1)Dp, Va(Q^c)<=(h1/a-1)Da.          (L7)

Since h1<=1/3 by ambient root width, the alpha coefficient obeys

    h1/a-1 <=(64+15delta)/(8-15delta)<=12803/1597.

This sharper family accounting requires no new assumption; the combined
bound(L6) is a convenient common constant.

## 3. Why an uncorrected1/27 relative gap is not valid in general

The literal ambient135 rectangle has Haar mass1/135, but eta can already
have a pure3 hole inside I. Relative to the ACTUAL h or h1, the extra
hole coefficient is eta(I), not the ambient1/27. Equation(L2) is the
correct uniform finite-source lower bound for it.

There is a concrete finite near-aligned counterexample to the uncorrected
per-carrier gap. Start with311's finite construction at height N. Replace
only the pure3 source label T_N(0) by a depth-N cylinder J_N inside the
original I=T_3(1); all other raw35 source labels remain as in311.
For N>=4, the moved cylinder has Haar mass tau=3^-N and is disjoint
from all remaining pure3 exclusions. Hence h is unchanged but

    eta(I)=1/27-tau.

All source exclusions other than pure3 and original135 avoid H in that
construction. Therefore every quinary depth-b cylinder F inside H has
exactly

    Lambda(F)=(h-1/27+tau)*5^-b,

strictly larger than the proposed(h-1/27)*5^-b. If an actual mixed7
forbidden carrier is desired, place one5^b*7^e label on F; this changes
neither the raw source nor the3/9 carrier mixture defining qJ.

Writing t_N=(1-3^(2-N))/18 and q_N=(1-5^-N)/4, the modified source has

    h=5/9-t_N, lambda=1/72-t_N*q_N+tau/5,
    qJ=(4q_N)^3 * [72(t_N*q_N-tau/5)]
                   * [18t_N-18tau] * (1-7^-N).

In71's qJ factors, a2=z0=sum_root1 b_i=4q_N,
sum_root1 l_i=72(t_N*q_N-tau/5), d1=18(t_N-tau),
pi_(0,1)=1-7^-N and pi_(0,0)=0. These give the formula above directly.

At N=10 direct exact rational evaluation gives

    0<1-qJ=0.0008537600395517632...<1/1000,
    h=29525/59049, eta(I)=2186/59049,
    lambda=5079437/922640625000.

For b=2 the excess over the proposed raw cap is exactly1/1476225.
This refutes the uncorrected individual raw-gap assertion. It does not
assert a counterexample to any aggregate epsilon_* bound that might
have a different proof. Bounds(L4)--(L6) remain valid.

## 4. Five absolute H own-test caps need no endpoint hypothesis

A separate, stronger-in-scope fact uses the full ambient Haar cell.
Suppose only that the actual raw source Lambda is dominated by raw35
Haar and that its forbidden labels include135=I times H, where I has
width1/27 inside its mod9 parent L of width1/9. Then for EVERY own
quinary depth-b cylinder F contained in H,

    Lambda(L times F)
      <=Haar((L minus I) times F)
      =(1/9-1/27)*5^-b=(2/27)*5^-b.                  (H1)

This is true even if pure3 already removes part of I, and even if there
are arbitrary additional source holes. It requires no qJ, rho,
epsilon_*, capacity equality, or AE3 product identity. The source hole
is kept literal throughout. Its possible prior overlap only strengthens
this absolute ambient-Haar bound.

For each independent own-test cylinder j, let its profile indicator be
1 exactly when its coarse carrier has the indicated projection below;
otherwise the event in L times H is empty. The resulting five raw
profile bounds are:

| Own label | Required own projection | Raw bound on its L,H event |
|---|---|---:|
|25|first-five slot H|2/675 times its profile indicator|
|75|root1 and first-five slot H|2/675 times its profile indicator|
|125|first-five slot H|2/3375 times its profile indicator|
|225|mod9 cell L and first-five slot H|2/675 times its profile indicator|
|375|root1 and first-five slot H|2/3375 times its profile indicator|

The factor2/27 is already the ternary L-minus-I mass. One must not
multiply it by another1/3 or1/9 for75/225/375 after conditioning on the
listed compatible coarse projection. The quinary denominators are25
for25/75/225 and125 for125/375. Convex containing profile coordinates
preserve these linear inequalities. Absent own events have zero left
side and satisfy the same bounds under the existing null conventions.

These are exactly the five H-own raw inequalities appended in316.
Their source justification is already valid off the endpoint whenever
that original135 label is present in the indicated rectangle. This
claim does not transfer the other rows, source equalities, tail prices,
or any complete comparison off the endpoint.
