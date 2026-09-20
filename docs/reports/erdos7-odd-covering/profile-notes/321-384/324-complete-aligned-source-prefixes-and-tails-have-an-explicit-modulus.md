[Index](../../marked_head_profile.md) · [Actual source-row transport](323-actual-aligned-source-and-row-transport.md) · [Original prefix modulus](../257-320/307-original-j-prefixes-and-complete-tails-have-an-explicit-modulus.md) · [Original quadratic modulus](../257-320/308-complete-j-quadratic-tails-have-an-explicit-modulus.md)

# Complete aligned source prefixes and tails: an explicit vanishing modulus

This is an ordinary quantitative lemma on the actual aligned domain of
notes319--321 and the [actual source-row theorem](323-actual-aligned-source-and-row-transport.md). It transports the precise endpoint
proof expressions used in 313--316. It neither optimizes those expressions
again nor asserts a numerical radius. Every source label and own-test
label keeps its assigned identity.

Let 0 <= delta <= 1/1000, 0 <= eps = epsilon_* <= 1/10000, and set

    r = 5 delta + 30 eps.

Use the ONE theta in [1/405,1/270] selected from the actual SOURCE405
allocation. Source135 remains its literal 27-by-first5 rectangle. Put

    lambda <= delta/72, a = 1/27 - 5 lambda,
    beta = chi = p + d_alpha + d_beta + lambda/a,
    sigma = delta/18, kappa = delta/4,
    gamma = beta/18 + 3 sigma/20.

The source-row proof gives beta <= (3/4+600/1597)delta <= r, sigma <= r,
kappa <= r, and gamma <= 37r/180. It also supplies the actual SECTION
bounds: only the Q entry of each normalized deep3 parent table gains
beta; only cell0 of each absolute deep5 column gains sigma. These section
bounds, and the literal H own-descendant cap 2/27, are hypotheses proved
from the source geometry. A finite matrix row residual alone would not
imply them for arbitrarily deep cylinders.

## The raw cap functional retains the fixed-H credit

Let U_theta be 313's exact aligned cap functional, including its negative
1/120 times minimum over the five B/Q support cells. Let ecap be the sum
of positive cell-cap excesses, egroup the sum of positive group-budget
excesses, and eH the joint deficit of the three fixed root1 H cells.
The source-row estimates give

    ecap <= delta + 5 eps,
    egroup <= delta,
    eH <= delta/90 + 5 eps.

For every coarse function 0 <= z <= Z, the same explicit capacity dual
as 313 therefore gives

    Lambda(z) <= U_theta(z) + Z Rraw,
    Rraw = ecap + egroup + eH <= r.                 (T1)

For clarity, write m = min_SUPPORT z. The B/Q cap prices are z_i-m >= 0,
the root1 group price is m, and the fixed H prices are z_H-m, which may
be negative. Their negative contribution is paid by eH. Root0 uses its
nonnegative cell-cap prices. This proves (T1) without deleting the minimum
credit or pretending that clipping alone restores the H equalities.
Every later affine use retains this same theta.

## Complete first- and second-order clipping series

Define

    B1(e) = sum_(a,b>=0; a+b>0) min(e,3^-a 5^-b),
    B2(e) = sum_(a,b>=0) (2a+1)(2b+1) min(e,3^-a 5^-b).

Both vanish at zero. For L>=1 and A,B>=0,

    B1(e) <= (L^2-1)e + (15/8)(3^-L+5^-L),
    B2(e) <= e(A+1)^2(B+1)^2
             +(15/8)(A+2)/3^A +3(4B+7)/(8*5^B).    (T2)

These are 307/308's complete-series arguments, reused with the present
source error. The weights 2a+1 count ordered exponent pairs with maximum
a. Thus B2 controls EVERY subcollection of ordered LCM payments; unordered
distinct pairs cost at most B2/2. The outer strips are paid, not discarded.

Let H = {0,1,2} x {0,1} be the six-label old head. For every original
old label d outside H, the source-row own-cylinder inequalities give

    mu(C_d) <= c_d^aligned + r,
    mu(C_d) <= 1/d.

Here the only non-exact categories are pure3 at depth >=3 and pure5 at
depth >=2; mixed categories retain their original raw product/Haar caps.
Consequently the positive change in the assigned surviving cap is at most
min(r,1/d). Every punctured old remainder, including the complement of
25,27,75,81,135,125,225,375, gains at most B1(r). Every old-old pair
remainder gains at most B2(r)/2.

For raw cylinders outside H there is the sharper multiplicative bound

    Lambda(C_d) <= Cr(d) + kappa/d.                 (T3)

Indeed deep pure3 uses z <= 3/4+delta/4, deep pure5 uses
h <= 1/2+delta/18; root-five and cell-five caps remain 1/3 and 1/9,
and deep mixed cylinders remain Haar bounded. If one label is outside
H, its LCM with ANY old label is still outside H. Therefore no altered
shallow cofactor5/15 cap enters these pair series.

## Positive-seven linear remainders, with the shallow hole retained

The b=1 own raw caps are h/5-g_delta and h1/5-g_delta, where
g_delta=1/135-lambda. They apply to independent test carriers by 311/320,
not only to the forbidden labels. Their positive changes from the aligned
endpoint are at most delta/90+lambda and lambda. Other positive changes
in the complete nonunit raw-cofactor cap series are bounded by

    cofactor3: delta/2; cofactor9: delta/2;
    pure3 depth>=3: delta/72;
    pure5 depth>=2: delta/360.

The remaining cofactor categories have zero positive change. The total
is at most (19/18)delta. Multiplying each original seven depth by
u_e=6/(5*7^e), whose complete sum is 1/5, gives

    positive nonunit seven remainder change <= (19/90)delta <= r. (T4)

Every removed assigned payment is removed label by label before summing
its complement. Thus (T4) applies to Z2,Z4,Z6,Z7,Z8 and any adopted
punctured subset, without subtracting an upper bound from actual mass.
The pure-seven family is already wholly present in the seven kernel.
For the whole positive-seven diagonal add raw unit drift delta/10;
the resulting total remains <= r.

## Raw pair paths and conditional PZZ

For a six-label own head 1<=B<=6, the complete omitted raw operator T
from 314 changes by at most Z gamma on any 0<=z<=Z. The discounted
prime-path proof of 265/308 is unchanged because its premises are exactly
the section coefficients above. Its pure3 and pure5 block errors are

    pair:   13 beta/36, 5 sigma/16;
    square: 7 beta/9, 27 sigma/40.

Replace precisely the same disjoint cross/self-pair/diagonal subseries
as in 314. The residual LCM series is a subseries of the complete ordered
Haar sum 45/8, so the following uniform errors suffice:

    EP = 15 Rraw + 6 gamma + 13 beta/36 + 5 sigma/16
                             +(45/8)kappa <= 25r,
    EQ = 36 Rraw +12 gamma + 7 beta/9 +27 sigma/40
                             +(45/8)kappa <= 50r.       (T5)

Each actual same-head pair/square expression is bounded by its original
314 endpoint expression at theta plus EP/EQ. Path blocks are rebuilt
symbolically on the perturbed upper coefficients; no old numerical saving
is subtracted from an unrelated new whole moment. The remaining original
cap terms are all nonnegative subseries, so the bounds above may overpay
some already replaced terms harmlessly.

Finite cofactor45 completion maxima, profile maxima and the common-theta
affine endpoint interpolation preserve a uniform additive error. In 316
keep the TWO independent 500-profile tables. Their first and second depth
weights are (6/35,1/70) and (6/245,1/70); the whole remaining tail has
weights (1/245,1/210). Summing gives pair weight 1/5 and square weight
1/30 exactly. Thus the conditional PZZ expression, including every depth,
has error at most

    EP/5 + EQ/30 <= (20/3)r.                       (T6)

No two positive-seven depths, own loads or optimizing completions are
identified.

## Exactly the remainders used by the retained quadratic body

Keep K = {25,27,75,81,135,125,225,375} and Zsel exactly as in 316.
The finite body retains Phi_k(B+K) and h_k(B+K)Zsel, so its maximum
retained load is 14. Those finite terms belong to the original matrix
objective and are priced by its dual/zero-column restoration; they are
NOT bounded by a six-label slope. All outside terms have h=h_k(B)<=6.

Let the remaining old set be R. The original all-integer decomposition
has h(R+Zr), K R, choose(R,2), K Zr, R Z and choose(Z,2). Exactly the
28 K-K payments and 72 K-Zsel payments are absent from its assigned cap
series. Preserve those labels. The positive complements have errors:

    hR: 6 gamma + 6 B1(r),
    hZr: (36/5)Rraw + (6/5)gamma,
    remaining OO: B2(r)/2,
    remaining OZ: (9/8)kappa,
    conditional ZZ: (20/3)r.                       (T7)

For hR, apply the same actual density measure Xi (mass <=r) to each own
cylinder; clip its possible error by that cylinder's Haar cap before
summing. This gives 6B1(r), not an infinite number of independent scalar
credits. The raw section coefficient contributes 6gamma. For hZr,
the full six raw mask families have total weight at most 6/5 and coefficient
at most 6; the omitted raw old operator has weight 1/5. The retained
projection weights (1/245,1/245,1/245,1/245,1/5) only reduce these payments.
The outside-old LCM observation (T3) proves the OZ line, since all seven
depths have sum 1/5 and (45/8)/5=9/8.

Summing (T7), a safe complete factorial-tail modulus is

    Tquad(r) = 25r + 6B1(r) + B2(r)/2.             (T8)

The same bound covers the unretained analytic fallback, where the full
nonnegative OO/OZ complements are paid. The five exact remaining old
weights REM in 316 are subweights of (1/18,1/20,1/20,1/20,1/72);
no extra finite-head error is hidden in (T8).

## The complete mean and exact mass

The endpoint shallow own caps from 312 also transport on this same source.
The projected inequality R14 of the row companion, together with the
actual root and cell upper bounds, gives

    mu(own3) <= 11/120+2/675+r,
    mu(own9) <= 2/45+r.                            (TM1)

For own3 in root1 use Lambda(root1)<=1/8+delta/2,
h1>=1/3-delta/18, and zeta_tilde(1)<=1/135 in R14. The raw/reference
drift is at most delta/2+delta/180; adding Xi_T<=delta+20eps is less
than r. Root0 has the smaller endpoint cap 3/40, with raw/reference
drift at most (2/5+1/180)delta. For own9 in cell1 use its 3/5 raw
coefficient and eta1>=1/9-delta/18. Cell0 has endpoint coefficient
11/360<2/45 and only an O(delta) increase bounded by delta. In root1
use d_c<=1/2+delta/2 and eta_c<=1/9, giving 2/45+delta/18. In L the
literal source135 term is favorable after its at-most-lambda earlier
overlap is paid, exactly as R15. In each case Xi_T and lambda still
leave a total below r. No source135 mass is distributed among children.

For own5, keep the actual deep3 quinary reference q/90. Its positive
mass loss is E3, and replacing its slot by q* costs at most qerr/90.
Apply (T1) and the one density discrepancy to w times each whole slot.
The endpoint upper table is exactly 312(AE6), since ignoring additional
negative source deletions only increases it. Consequently

    mu(own5) <=41/675+3r.                          (TM2)

For own15 use w times its own root/slot mask. The endpoint maximum is
11/270 as in 312; discarding the additional deep3 deletion is favorable.
The raw functional and density costs suffice:

    mu(own15) <=11/270+2r.                         (TM3)

Together with all remaining old labels paid by B1(r), the nonunit old
cap sum is at most 79/225+7r+B1(r). The whole positive-seven diagonal
costs at most r by (T4), and |S-413/2700|<=r by the source-row lemma.
Thus, conservatively,

    integral A dmu <=293/450+12r+B1(r),
    |S-413/2700|<=r.                              (TM4)

Every own load is independent. These two additional observations are
therefore covered by the common final modulus (T13); signed external
mass coefficients still use the actual S as prescribed below.

## Analytic prefix and retained-body interfaces

For every nonnegative coarse 0<=f<=Z, the actual deep3 reference loses at
most Z[4E3+qerr/90], where

    E3 <= eps+delta/180, qerr <=5delta/4+2lambda/a.

For the ordinary E5 row-minimum credit add Z[5eps+delta/450]. For 316's
stronger Q-only credit use 321's negative-variation estimate and add
Z[14eps+delta/450]. In both cases the total deletion-reference loss is
at most Zr. Combining the SAME density measure Xi of mass <=r and (T1),

    mu(f) <= U_theta(wf)-D_endpoint(f)+3Zr.          (T9)

This is a comparison of bounded coarse integrals. It does not claim
full fine-coordinate variation convergence of E5.

For a positive hinge combination F(v)=sum_j a_j(v-j)_+, A=sum_j a_j,
the original analytic telescopes retain at most four extra old labels.
Their selected hinge <=9A, raw base coefficient <=6A, each of four
selected finite differences <=A, and the base deletion coefficient
<=5A. The source section drifts pay at most Ar per selected operator;
all original mixed CRT alternatives remain exact. Including (T4) and
the punctured old tail therefore gives the convenient uniform bound

    analytic hinge error <= A[64r+B1(r)],
    retained LP hinge tail error <= A[B1(r)+r].     (T10)

The factor 64 has room over 9+6+4+5+1. This applies to both the
threshold-selected and all-four policies, and to all two/four/six/seven/
eight positive-seven prefixes actually used in 313--315. Their actual
per-threshold assigned old remainders are outside H throughout.

The analytical factorial fallback in `prefix_functions.phi_lines` uses
Phi_k(B)<=15; it does not use Phi_k(B+K). By (T9) its finite head costs
at most 45r. Combining (T8), the convenient bound is

    analytic factorial error <=80r+6B1(r)+B2(r)/2. (T11)

This also covers the conditional-PZZ versions of those prefixes by
(T6). Taking minima of alternative bounds or maxima over completion
profiles preserves their common error and their original branch cover.

For an original function

    F(v)=a+sum_j a_j(v-j)_+ + f Phi_k(v), A=sum_j a_j,

let D_F be the maximum original row-price L1 norm across every actually
adopted dual, including seeds and inherited consumers. Let R_F be a bound
on its restored endpoint-zero objective coefficients, in units of r,
using the original 2645-step induction. Then the uniform transport is

    actual integral F <= endpoint B_F + omega_F,
    omega_F = (D_F+R_F+64A+80f+a)r
                 +(A+6f)B1(r)+(f/2)B2(r).           (T12)

The coefficient a assumes a>=0, as in the source observations. Signed
mass coefficients in the 59 external envelopes must instead retain actual
S and only pay their absolute values after combination. The actual source
mass error is <=r. Dual feasibility and every physical coefficient remain
obligations of the retained finite certificate; (T12) does not replace them.

For the six 316 targets, (a,A,f) are respectively
(1,3,2), (0,0,1), (0,0,1), (0,0,1), (0,5,2), (0,3,2).
The heavy hinge has A=403/8 and f=a=0. Thus the nonlinear part of a common
bound for the hinge/quadratic observations can be taken as

    (D+R+3300)r + 51B1(r) + B2(r).                  (T13)

Here D and R must include their actual adopted source banks. This is
explicit and vanishes as r tends to zero. No numerical delta/eps box or
unrestricted Erdős7 conclusion is asserted by this lemma.

The coefficient bounds above have been checked with exact rational arithmetic.
Their measure and section hypotheses are supplied by323 and the cited
complete-tail proofs. No new Lean verification is asserted.
