# Integer selectors strengthen capped budgets, but axis limits survive

A pure-prime boundary can retain the actual first-level selector of each
original numerical label while relaxing the remaining levels by complete
weighted budgets. The resulting finite union of polyhedra can be strictly
stronger than the former convex budget region, even after taking its convex
hull. An explicit four-point example lowers the maximum total normalized
loss from24 to167/7.

This improvement is not universal. For the triple of
[report501](501-complete-weighted-boundaries-cut-a-binary-obstruction.md),
explicit original-label phases realize axis vectors tending to its minimizing
pair. The fixed weighted axis objective consequently still has infimum32.
A second four-point construction has limiting objective-14. These are
ordinary proofs with exact arithmetic certificates, not Lean verification.
They locate a remaining joint-axis and mixed-label obligation rather than
establish a new source-mass bound or settle unrestricted Erdos#7.

## One integer first layer and a complete weighted tail

Fix a prime p, put h=p-1, and fix k tested old points with common old
references. Let D be a finite set of distinct old cofactors coprime to p.
The two permitted old residues of d have membership masks A_d,B_d in{0,1}^k.
Each present numerical modulus d*p^j has one selector and one p^j phase,
both shared across all tested points. Selectors may differ between complete
labels, including different heights j.

On the full uniform p-coordinate fibre, let alpha_i be the pure-p union
deletion fraction and t_i=h*alpha_i. Define

    S={sum_d C_d : C_d in{A_d,B_d}},
    N(w)=sum_d max(w dot A_d,w dot B_d),
    P={r>=0 : w dot r<=N(w) for all w>=0}.

S is the set of actually reachable integer activation vectors. Replacing it
by conv(S) intersect Z^k is invalid: report502's vector(1,1,1,1) is integral
and lies in the convex hull of the two-label selector sums, but is not one
of those sums. Activation counts also need not equal distinct phase counts.

Choose n in S from the actual j=1 selectors. For an absent j=1 label,
choose a virtual selector only to complete an upper bound. Set

    r=p*h*sum_(present d,j>=2) p^(-j)*C_(d,j).

The coordinatewise union bound and one shared selector per complete label
prove

    0<=t<=h,
    p*t<=h*n+r,
    r in P.                                             (I1)

Indeed w dot r<=p*h*sum_(j>=2)p^(-j)*N(w)=N(w). No independent selector
is supplied to different tested points, and no absent class is added to
the original family. If every present height is at most J, the sharper
condition is

    r in tau_J*P, tau_J=1-p^(1-J).                       (I2)

At J=1 the tail is zero. Precise missing heights can further decrease the
label weights. The height-independent interface uses the envelope tau=1.
For either choice, the necessary region is

    U_(p,tau)=union_(n in S)
       {t in[0,h]^k : exists r in tau*P, p*t<=h*n+r}.      (I3)

This is not sufficient for actual phase realization. The tail still uses
activation budgets instead of a common phase arrangement, and n omits
first-level collisions. The model uses a full uniform pure-axis fibre;
conditioning on an event involving p requires a separate measure argument.

## Convexification and the axis cap

Let Z=conv(S)=sum_d conv{A_d,B_d}. The support-function representation from
[report502](502-complete-weighted-inventories-do-not-realize-one-selector-family.md)
extends to any finite number of tested points:

    P=(Z-R_+^k) intersect R_+^k.                         (I4)

For clarity, Z is compact, so Z-R_+^k is closed and convex. A separating
functional with finite supremum must be nonnegative, since this set contains
every negative coordinate recession ray. Its support value is N(w), proving
I4. This covers empty D, zero masks and lower-dimensional Z.

Put lambda=(h+tau)/p. Three distinct statements hold.

1. Without the cap t<=h, the convex hull of I3 is exactly lambda*P.
2. With the cap retained, relaxing n in S to z in Z gives exactly
   lambda*P intersect[0,h]^k.
3. The convex hull of the capped integer union I3 can be strictly smaller.

For the common forward inclusion, dot p*t<=h*n+r with w>=0. This gives
w dot t<=lambda*N(w). For statement1's converse, every lambda*n,n in S,
is feasible using r=tau*n. Each branch is downward closed in the nonnegative
orthant, and so is the convex hull of their union: if v<=sum_j a_j v_j,
scale every coordinate of each v_j by the corresponding ratio
v_i/(sum_j a_j v_ji), taking zero when the denominator is zero. The scaled
vectors remain in their respective branches. Thus the convex hull contains
the whole downward closure lambda*P.

For statement2's converse, write t=lambda*u,u in P. Choose z in Z with
z>=u using I4, and take r=tau*u. Then h*z+r>=p*t and the assumed cap remains
satisfied. In particular tau=1 reproduces the old capped budget domain.
Statement3 follows from the next explicit example; imposing caps within
each branch and imposing them only after convexification need not commute.

## An exact strict gap with literal old labels

Take p=7 and four old points, with five distinct old labels3^1,...,3^5
and seven distinct labels5^1,...,5^7. Use old centres0 and1 and points

    (0,1,156250,18828126) mod(3^5*5^7).

The first five labels have masks A=1001,B=0110; the other seven have
C=1010,D=0101. These are actual common-centre CRT memberships. The reachable
first-count vectors are exactly

    n(a,b)=(a+b,12-a-b,5-a+b,7+a-b),
    a,b in Z, 0<=a<=5, 0<=b<=7.                         (I5)

Their convex hull contains v=(6,6,6,6), the average of n(0,0) and n(5,7).
Thus v belongs to the old capped domain and its total24 is maximal there.

For complementary pair weights A and B, both tail budgets equal17, while

    A dot n=7+2a, B dot n=17-2a.

At least one pair has activation at most11. For that pair, I1 gives
7*w dot t<=6*11+17=83. The other pair contributes at most12 by the axis cap.
Every point in U_(7,1), and therefore its convex hull, satisfies

    sum_i t_i<=167/7=24-1/7.                             (I6)

This bound is sharp for the lifted relaxation. Take

    n=n(2,3)=(5,7,6,6), r=n(5,6)=(11,1,6,6),
    t=(41/7,6,6,6).

Here r in S is itself a complete-budget witness and
7*t<=(6*n+r)=(41,43,42,42). No actual finite-height phase realization of
this sharp relaxed point is asserted. The strict comparison concerns the
necessary interface and does not identify these old labels with the full
inventory of the current source chart.

## When a retained selector vector really is an axis limit

There is a direct sufficient construction for some n in S. Fix one selector
C_d for each d across all heights. Give each label a digit c_d in{1,...,p-1},
requiring c_d!=c_e whenever the selected masks of d and e overlap at a tested
point. Thus the intersection graph of the selected masks has a proper
coloring with p-1 colors.

For every1<=j<=J, take exactly one original modulus d*p^j, with the fixed
old selector and new phase

    c_d*p^(j-1) modulo p^j.                              (I7)

CRT produces its single original residue. The moduli are distinct because
the old d are distinct and coprime to p. All are odd and greater than one
for the odd primes and odd old labels used here, including d=1.

At one tested point, cylinders at different heights have different p-adic
valuations. At the same height, any two active labels have distinct first
nonzero digits. The active cylinders are therefore disjoint. Exactly,

    t_J=(1-p^(-J))*n.                                    (I8)

Every J is finite; n is a limit rather than an asserted finite attainment.
The proof of I8 is the valuation and geometric-sum argument, not an
extrapolation from the checks below. It demonstrates that passing I3 can
sometimes be strengthened to an actual axis construction, while I3 in
general remains only necessary.

## Two literal profile systems retain their old limiting objectives

Use old primes(3,5,7,11,13,17,19), split at the first three coordinates.
A profile s has A-box factors
(max(1,s3),max(1,s5),max(1,s7),s11,s13,s17,s19), and B-box factors using
the negatives at the split coordinates. Each box consists of exponent
labels below these factors, and d is the corresponding product of old
prime powers. The certificate gives one selector and one digit per label.

The triple is report501's

    (4,2,-4,1,2,1,1),
    (5,-2,4,1,1,1,1),
    (-5,-3,-2,1,1,1,1).

The four-point system is

    (3,2,2,1,2,1,1), (3,2,2,2,1,1,1),
    (-3,-2,2,2,2,1,1), (-3,0,-2,2,2,1,1).

| System | Old labels | p | Reachable selected n | Digits used |
| --- | ---: | ---: | --- | ---: |
| Triple | 51 | 23 | (18,21,18) | 21 |
| Triple | 51 | 29 | (21,13,24) | 24 |
| Four points | 45 | 23 | (22,22,16,13) | 22 |
| Four points | 45 | 29 | (8,8,24,24) | 24 |

Each coloring uses at most p-1 digits and satisfies every common-point
conflict. Each n is an actual selector sum, so taking r=n already proves
membership in the infinite-tail interface. I8 gives the stronger actual
finite-family approximation.

The masks themselves have simultaneous old CRT realizations. Choose A=0
in every old prime coordinate, B=1 on the three split coordinates and0 on
the others. For a split profile entry f>=2 choose x=p^(f-1); for f<=-2
choose x=1+p^(abs(f)-1); for f=0 choose x=2. At a common factor f>=1 choose
x=p^(f-1). Take carrier exponents E_p at least every relevant abs(f), and
combine each point's coordinates by CRT. All profiles above satisfy these
conditions. Direct congruence checks recover both masks of every label.
This is a common arithmetic realization of the old interfaces, not a claim
that a given completed conditional source assigns them positive mass.

The two prime axes can be constructed together because d*23^j and d*29^k
are different numerical labels; their selectors need not coincide. Let

    g_w(t,u)=sum_i w_i(22-t_i)(28-u_i)-N(w).

For the triple, w=(17,16,13),N(w)=892. Substituting the two limiting n gives

    g_w=17*28+16*15+13*16-892=32.                         (I9)

Report501 already proves g_w>=32 on the entire complete weighted domain.
The finite axis constructions lie in that domain and tend to I9. Thus the
infimum over these actual pure-axis families is exactly32; imposing only
additional valid single-axis realization restrictions cannot increase it
by a uniform positive amount. This does not assert that mixed labels attain
the subtraction N(w), or that the actual survivor bound itself is sharp.

For the four points, w=(1,2,1,2),N(w)=110. The constructed limiting pair gives

    g_w=6*4+2*9*4-110=-14.                               (I10)

The29-axis vector here is(8,8,24,24), not(0,0,24,24). The first two terms
vanish at the23-axis limit22, so I10 holds for the actual constructed vector.
No global minimum claim for this four-point domain is needed: continuity
already supplies finite actual axis families with a negative g_w. That
negative lower-bound expression is not evidence of an actual covering.

## Remaining joint obligation and reproduction

The integer interface detects information absent from complete convex
budgets. These two constructions show that it does not remove every existing
minimizing configuration, even when the missing single-axis phases are
supplied. A further improvement must use other point relations, actual-source
restrictions, or compatibility between the two axis survivor sets and the
original mixed labels d*23^j*29^k. Requiring the23 and29 selectors to agree
would impose an unauthorized condition on different original labels.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/integer_selector_tail_interface.py

The standard-library consumer checks all48 branches of I5 and its sharp
relaxed witness. For both profile systems it reconstructs numerical old
labels, common old CRT points, each label's selector, all coloring conflicts,
and full-label CRT residues. Direct finite-fibre counts at J=2 check I8;
the general J proof remains the derivation above. It also checks I9 and I10.
A default run compares the full result with the adjacent JSON. No selector
search, floating solver, transient file or completed-source replacement is
an input.
