# A two-centre star boundary closes complete height-three tails

Let P={3,5,7,11,13,17,19} and P9=P union {23,29}. Consider any finite
family of pairwise distinct numerical moduli greater than one,
supported on P9, with one arbitrary globally fixed residue per modulus.
Suppose every P-supported mixed modulus is squarefree or has some
prime exponent at least 3. Pure prime-power originals and originals
touching 23 or 29 are unrestricted. Then

    H(full survivor)>=2488465975171529051
                       /2403540259968514867200
                     =0.0010353335937897403...>1/1000.   (TC1)

Mixed means supported on at least two primes. Original counts and all
finite exponent heights are unrestricted. The excluded P-supported
labels are precisely non-squarefree mixed labels whose largest
exponent is 2; section 6 also allows a small weighted inventory of them.

This strengthens the exponent threshold 4 in
[Report590](590-root-balanced-star-screening-allows-complete-height-four-tails.md)
to 3. It is an ordinary proof with an exhaustive exact rational
consumer, not a new Lean result or a solution of unrestricted Erdős #7.
No law or original phase is selected separately for different queries.

## 1. Source and the finite boundary retained

Write V={7,11,13,17,19} and Q={5} union V. For each p in P, exclude
the actual forbidden first digit when the original p is present; if
it is absent, exclude any fixed first digit. In every retained root,
impose the complete actual pure-power inventory. As in Report590,
each root's relative Haar survivor mass is at least (p-2)/(p-1)>0.

For p in Q, use Report590's root-balanced probability rho_p. Its
retained first digits each have mass 1/(p-1), and its cylinder caps are

    c_p(1)=1/(p-1),
    c_p(e)=1/[(p-2)p^(e-1)], e>=2.                     (TC2)

For p=3 instead use normalized Haar on the COMPLETE pure survivor
inside its two retained roots. At most 1/6 of ternary Haar is lost
to deeper pure originals, since sum_(e>=2)3^(-e)=1/6. This survivor
has Haar mass at least 1/2. Denote its two root masses by t_0,t_1.
They satisfy

    t_0+t_1=1, 1/3<=t_0,t_1<=2/3,
    rho_3([a]_(3^e))<=2/3^e, e>=2.                   (TC3)

For the lower root bound, each root retains at least 1/6 Haar and the
other root has at most 1/3; normalize these two masses. The upper
bound follows by exchanging the roots. All deeper pure originals
are included, whether or not a pure-3 original was present.

Set rho=product_(p in P)rho_p. This single probability avoids all
actual pure originals and has density

    rho<=D H_P, D=2 product_(p in Q)p/(p-2)=3458/405.    (TC4)

Its deeper ternary caps are smaller than those of the root-balanced
ternary source in Report590. The first-digit masses are now unequal;
both changes must enter every original and query estimate.

## 2. Eleven auxiliary stars and an exact 2 by 4 grid

Retain every positive-rho actual event at the labels

    15, and 3q,5q for q in V.

For each missing or rho-null slot, add one fixed auxiliary event at
that label using retained roots. An auxiliary event is an additional
deletion, not a rephasing of a positive-mass original. Let J be the
union of these eleven events. Rename the retained 3 and 5 roots so
that the 15 event deletes cell (0,0) in their 2 by 4 grid.

For each q in V, write r_q in {0,1} for the ternary root of its 3q
event and c_q^* in {0,1,2,3} for the 5-root of its 5q event. Let
epsilon_q be 1 when the q-roots of those two events coincide, and
0 otherwise. There are 2*4*2=16 possible local layouts per q.
Since q>=7, both equality possibilities are feasible among retained
roots. The names of the q-roots do not otherwise affect these bounds.

For each T subset V define the outside-T avoidance table

    g_T(i,j)=1_((i,j)!=(0,0)) product_(q in V without T)
      [1-(1_(i=r_q)+1_(j=c_q^*)
                 -epsilon_q 1_(i=r_q)1_(j=c_q^*))/(q-1)].  (TC5)

Each factor is exact: on that grid cell, the q-coordinate must avoid
zero, one, or two distinct retained roots, each of mass 1/(q-1).
The product uses independence only under the original rho. Conditions
on q in T have been dropped; thus this table also bounds avoidance
when the tested cylinder itself fixes the coordinates in T.

In particular, the exact auxiliary-survivor mass is

    a(t)=sum_i t_i (sum_j g_empty(i,j))/4.             (TC6)

Let U be the FULL actual P-supported survivor and define

    eta=rho restricted to U intersect J^c.             (TC7)

This explicitly retains auxiliary deletions even when the
corresponding original stars were absent. In particular eta<=rho|J^c,
as required to use the same grid for all queries.

## 3. Six support screens distinguish first and deeper ternary digits

For each T subset V put h_i(T)=(sum_j g_T(i,j))/4, and define

    A_T=sum_i t_i h_i(T),
    B_T=max_j sum_i t_i g_T(i,j),
    C_T=max_i t_i h_i(T),
    D_T=(1/3)max_i h_i(T),
    E_T=max_(i,j) t_i g_T(i,j),
    F_T=(1/3)max_(i,j) g_T(i,j).                       (TC8)

The support outside the two centres is T. These screens have the
following meanings:

| Centre coordinates in the cylinder | Screen |
|---|---|
| neither 3 nor 5 | A_T |
| 5, but not 3 | B_T |
| 3 at exponent 1, but not 5 | C_T |
| 3 at all exponents at least 2, but not 5 | D_T |
| 3 at exponent 1 and 5 | E_T |
| 3 at all exponents at least 2 and 5 | F_T |

Multiply a screen by the product of TC2 caps for the other fixed
coordinates. Average an unqueried centre and maximize a queried
centre's root. This proves the corresponding cylinder upper bound
after retaining TC5. In D_T,F_T the entire deeper ternary series has
already been summed: sum_(e>=2)2/3^e=1/3. The e>=3 subseries is
1/9, one third of this value. It must not be confused with the
first-digit contribution C_T,E_T.

These arguments apply to each actual original and each arbitrary
query residue on the SAME rho and eta. Dropped within-T conditions
only enlarge a bound. No independence after conditioning on J^c or U
is asserted.

For S subset Q define the complete nonternary profiles

    r(S)=product_(p in S)1/(p-2),
    l(S)=product_(p in S)[1/(p-2)-1/((p-2)(p-1)p)],
    w(S)=product_(p in S)1/(p-1).                     (TC9)

Empty products equal one. The difference r-l sums ALL exponent
vectors with at least one exponent at least 3, by the geometric
series in TC2. Thus no original or query height is truncated.

## 4. A single deletion and query bound for each layout

Sum the following nonnegative original charges to obtain L(t).

For a nonempty S subset Q, use T=S intersect V and let X be A_T
when 5 is absent, B_T when it is present. If |S|>=2, charge

    X[r(S)-l(S)]

for the complete mixed tail, and additionally X w(S) for its
squarefree label unless S={5,q}. Those star labels were already
removed by J. If |S|=1 there is no original charge here: all pure
originals were imposed in rho.

For support {3} union S with nonempty S subset Q, let (Y,Z) be
(C_T,D_T) when 5 is absent and (E_T,F_T) when it is present. Charge

    Y[r(S)-l(S)] + Z[r(S)-l(S)+l(S)/3]                (TC10)

for the complete mixed tail. The first term has ternary exponent 1
and some other exponent at least 3. In the second, either some
other exponent is at least 3 or the ternary exponent is at least 3.
Additionally charge Y w(S) for the squarefree label when |S|>=2.
For |S|=1 it is one of the 3q or 15 stars and has already been removed.

It follows that s=eta(1)>=s_0(t):=a(t)-L(t). Define

    R_P(mu)=sum_(d>1, P-supported) max_(b mod d)mu([b]_d).

All its heights are bounded by the complete query sum Q(t):

* For each nonempty S subset Q, add X r(S).
* For each S subset Q, INCLUDING S empty, add (Y+Z)r(S).

Here the second line uses the same Y,Z as TC10 and includes pure
ternary queries. Therefore

    R_P(eta)<=Q(t),  Gs-R_P(eta)>=Gs_0(t)-Q(t),
    G=566/49.                                        (TC11)

For each fixed layout, a(t) is affine in t_0. Every other screen
is affine, constant, or the maximum of finitely many affine
functions. All coefficients in L,Q are nonnegative. The right
side of TC11 is consequently concave in t_0. Its minimum on
[1/3,2/3] occurs at an endpoint. This reduces the continuous pure
geometry to two evaluations without replacing the actual law.

There are 16^5 layouts after fixing the central cell, hence exactly
2*16^5=2097152 endpoint cases. Exhaustive integer arithmetic gives

    min_(layout,t_0=1/3 or 2/3)[Gs_0(t)-Q(t)]
       =delta=2488465975171529051/22392201998694528000
       =0.11113091849191997...>0.                     (TC12)

One minimizing layout has t_0=2/3, all r_q=1, columns 1 for q=7,19,
columns 2 for q=11,13,17, and epsilon_q=0 for all q. Direct rational
grid evaluation at this layout gives

    a=150457/248832,
    squarefree nonstar charge=91201/414720,
    complete mixed-tail charge=28577416079794457/182793485703628800,
    s_0=41751119899166803/182793485703628800,
    Q=35018859461/13856832000.

These values reconstruct TC12. The universal result uses the full
layout scan and the concavity argument, not just this witness.

## 5. Same-law continuation and the Haar lower bound

Apply the raw 23/29 continuation of
[Report569, SD15--SD16](569-complete-suffix-debits-close-the-six-prime-query-target.md)
to this actual eta. Condition each new coordinate on its complete
actual pure survivor. Originals touching exactly one new prime
cost at most R_P(eta)/21+R_P(eta)/27; those touching both cost at
most [s+R_P(eta)]/567, retaining the old unit's actual mass s.

Thus the remaining raw mass is at least

    [566s-49R_P(eta)]/567>=49delta/567.

The density bound is D*616/567. Dividing gives

    H(full survivor)>=49delta/(616D),

which is TC1. All original phases and heights involving 23 or 29
are retained. The supported submeasure need not have full support
on the original survivor; auxiliary deletions cause no difficulty.

## 6. Remaining mixed squares and verification boundary

For additional P-supported mixed labels m with largest exponent 2,
use the same source caps c_p for p in Q, and set c_3(1)=2/3,
c_3(2)=2/9. If their complete weight inventory is

    v=sum_m product_(p|m)c_p(v_p(m))<delta/G,
    delta/G=2488465975171529051/258652782270634752000
           =0.009620874569088477... ,                  (TC13)

delete them under the same eta. Raw mass decreases by at most v;
raw query maxima cannot increase. TC11 retains margin delta-Gv>0.
Hence any covering within P9 would require a non-squarefree mixed
inventory of maximum exponent 2 with weight at least delta/G.
This necessity does not settle arbitrary such inventories, or
unrestricted support primes.

The exact [producer](../../frontier/cover-geometry/two_centre_star_profile.py),
[integer engine](../../frontier/cover-geometry/two_centre_star_scan.cpp), and
[data](../../frontier/cover-geometry/two_centre_star_profile.json) are retained
beside Report590's program. Python derives rational coefficients
from TC9--TC11 and verifies the minimizing grid directly. The C++
consumer exhaustively scans all layouts and both endpoints in signed
128-bit integer arithmetic. The producer checks an absolute bound on
every accumulated expression before invoking it; floating point is
not used to decide any inequality. Full exponent series enter the
coefficients symbolically, not through finite enumeration of heights.

The same minimizing H=3 layout, evaluated with the complete H=2
tail instead, has gate -6910755601249/1539032140800<0. Thus this
envelope for threshold 2 does not give a positive uniform margin;
no full H=2 scan is needed to establish this failure. It is not a
covering example. The next arithmetic
obligation is to retain enough of the actual mixed-square phases
to control their joint deletion and future queries, together with
a continuation over arbitrary additional primes. Root independence,
central-star compatibility, and original numerical-label ownership
must remain explicit in such a strengthening.

[Report592](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)
controls the joint second moment of this same seven-prime source and
extends continuation to 23,29,31. Its ordered-prime transport gives a
ten-prime result with the same first-seven exponent restriction. It also
records an actual mixed-square dead fibre showing why the complete old
first-root marginal cannot always be preserved when that restriction is
removed. The present nine-prime density and extra-square budget remain
available independently.

[Report593](593-a-joint-triple-block-admits-two-mixed-square-labels.md)
instead retains 105,147,245 in one joint prefix block. It allows arbitrary
phases at the two added mixed-square labels 147 and245, within the
nine-prime support, without a separate extra-weight charge for them.
[Report594](594-five-joint-blocks-admit-ten-mixed-square-labels.md)
retains all five 15q blocks together with 3q^2 and5q^2 for
q=7,11,13,17,19. A common thinned source and a separate second-moment
certificate combine all ten added square labels with the ten-prime
continuation, giving Haar density greater than1/3400; on nine primes
the stronger bound is greater than1/500. Remaining core mixed squares
and unrestricted additional prime support are still outside this result.
