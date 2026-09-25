# Joint damaged reserves retain every original height

Fix `P={3,5,7,11,13,17,19}`, `Q=P without3`, and one finite actual
P-supported family with distinct odd nonunit numerical moduli and globally fixed
original residues. The pure3 originals are exactly `1 mod3` and
`3 mod9`. At every nonunit Q cofactor choose at most two fixed phases
containing all original projections at ternary exponents0 through3,
including Q-only originals. Let `nu` be ONE actual selected PA law
from [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md). Put

    B=432040125182653876501/86355045355449035400,
    alpha_min=7575003978548161/73724315753088000.

Then `R_Q(nu)<=B` and `nu<=9H_Q/alpha_min`. All query heights are included.
No selected phase, original residue or source law is changed when a
query is tested.

Let `u_A` be ternary Haar conditioned on `[0]_9 union[6]_9`, and let
`u_B` be ternary Haar conditioned on `[2]_3`. With the COMPLETE actual
survivor mask `chi`, define `c_j(x)=integral chi(t,x) du_j(t)`.
The additional same-source hypothesis is

    2c_A+3c_B>=4,   c_A>=5/9,     nu-almost everywhere.       (JR1)

Under JR1 there is one supported probability `mu`, with Q marginal
exactly `nu`, such that

    R_P(mu)<=1795085660881088508439/155439081639808263720
           =11.54848344408491... <566/49.                   (JR2)

Every remaining original supported on `P union{23,29}` and touching23
or29 may have arbitrary fixed residue and arbitrary finite height.
The established same-law
continuation gives

    H(full survivor)>=19322824958140352009
                      /18870953593726484490240000
                     >1/1000000.                          (JR3)

This permits both ternary branches to lose actual mass and imposes no
upper cutoff on original heights. It retains the fixed pure3 and
shallow two-phase assumptions and JR1; it does not settle unrestricted
Erdos #7.

## 1. The complete-query proof already supplies a sharper second hinge

Report569 SD5--SD10 prove more than its displayed query-norm bound.
Write `lambda` for its unnormalized actual final source, `s=lambda(1)`,
and `N` for a complete finite query count INCLUDING the unit once.
Write `alpha_PA(x,y)=xy-1/12-sum_q a_q F_q(x,y)` for SD3's bilinear
prefix-dependent mass lower bound, which is at least alpha_min.
With `H=integral(N-3)_+ d lambda`, SD10 gives

    (B-2)s-H >= (B-2)alpha_PA-Phi+D0+sum J >=0.                (JR4)

The last inequality is the same four-corner comparison used there:
each corner quotient `2+(Phi-D0-sum J)/alpha_PA` is at most B, and the
interpolation is bilinear. The requirement `B-2>=zeta0` is satisfied.
In particular the joint cap-slack term J is already included; it is
not subtracted a second time.

For any finite partial nonunit one-phase Q query layout L, extend it
to a complete finite box N. Pointwise `N>=1+L`. Normalize the SAME
actual source by s and take the established complete-box limit. Then

    integral(L-2)_+ d nu <= K2 := B-2
      =259330034471755805701/86355045355449035400.           (JR5)

This holds for EVERY alternative finite one-phase query layout under
nu, not only actual original layers. JR5 follows from the hinge
inequality JR4, not from `R_Q(nu)<=B` alone.

Consequently [Report584](584-weighted-query-costs-retain-the-actual-damaged-branch.md)'s weighted-query argument gives, for any
measurable `0<=f<=h`,

    R_Q(f nu)<=h(B-2)+2 integral f d nu.                    (JR6)

Indeed `fL<=h(L-2)_++2f`. Integrate, maximize the phases of each
distinct numerical label on a finite inventory, and exhaust the
complete inventory. No source is reselected in this maximization.

## 2. A single supported law when both branches are damaged

The first condition of JR1 alone implies `c_A>=1/2,c_B>=2/3` because
both reserves are at most1. Define

    a_A=c_A/2,   a_B=1-c_A/2,   f=(1-c_A)/2,
    mu=chi[(a_A/c_A)u_A+(a_B/c_B)u_B]nu.                    (JR7)

The division by c_B is necessary when that branch is damaged. Each
conditional fibre has total mass `a_A+a_B=1`, so this law has Q
marginal exactly nu and is supported on all actual originals.

Its normalized A coefficient is1/2. The joint inequality in JR1 is
exactly the condition

    a_B/c_B=(1-c_A/2)/c_B<=3/4.                            (JR8)

For every Q-smooth numerical d, including d=1, the root-A query has
mass at most `(1/2)q_d(nu)`. The root-B query has mass at most
`(1/2)q_d(nu)+q_d(f nu)`, since its complete conditional mass is
`a_B=1/2+f`, regardless of which subcylinders were deleted. Thus the
depth1 contribution is at most

    (1/2)(1+B)+m+R_Q(f nu),  where m=integral f d nu.

For every ternary query depth e>=2, the conditional Haar coefficient
is at most `(1/2)(9/2)=9/4` in A and at most `(3/4)3=9/4` in B.
One cylinder cannot meet both roots, so these bounds are not added.
The COMPLETE deep coefficient is

    sum_(e>=2)(9/4)3^(-e)=3/8.

Retaining the unchanged Q marginal and the unit cofactor exactly once
at each positive ternary depth now gives

    R_P(mu)<=B+(7/8)(1+B)+h(B-2)+3m,  provided f<=h.         (JR9)

The same disjoint-support calculation gives `mu<=81H_P/(4alpha_min)`.
For additional originals supported on `P union{23,29}`, the23/29
density factors are22/21 and28/27. Hence any
right side R of JR9 below566/49 yields

    H(full survivor)>=alpha_min(566-49R)/12474.                (JR10)

## 3. All original heights supply the required mean bound

On the selected source, original exponents0 through3 are already
avoided. For e>=4 let `L_(A,e)` and `L_(B,e)` count actual residual
original projections whose ternary cylinders lie in A and B,
respectively. Define the all-height incidence weights

    Y_j=sum_(e>=4)54*3^(-e)L_(j,e).

Actual numerical-modulus uniqueness makes each fixed-height count a
partial one-phase Q query layout. Its original phases are fixed, so
`E L_(A,e)<=R_Q(nu)<=B`. The actual union bound gives

    1-c_A<=Y_A/12,   1-c_B<=Y_B/18.

All terms are nonnegative and

    sum_(e>=4)54*3^(-e)=1.

Therefore, without an original-height cutoff,

    m=E(1-c_A)/2<=E Y_A/24<=B/24.                        (JR11)

Under JR1, `f<=2/9`. Substituting h=2/9 and JR11 into JR9 gives

    R_P(mu)<=2B+7/8+(2/9)(B-2),                           (JR12)

which is exactly JR2. Its gap below566/49 is

    19322824958140352009/7616515000350604922280
      =0.0025369640783548487... .

This also closes the arbitrary-original-height mean-loss gap stated
in Report584 W10 whenever `c_B=1,c_A>=5/9`: those conditions imply
JR1. W10's third-hinge calculation remains valid, while the stronger
all-layout second hinge makes its additional mean improvement
unnecessary.

A direct sufficient joint-load condition for JR1 is

    Y_A<=16/3,   Y_A+Y_B<=6.                              (JR13)

Indeed `c_A>=1-Y_A/12>=5/9` and
`2c_A+3c_B>=5-(Y_A+Y_B)/6>=4`. Retaining the actual joint reserves can
be less restrictive than JR13 when original cylinders overlap.

More generally, for `0<=u<6`, conditions `Y_A<=u,Y_A+Y_B<=6` give
`h=u/24` and

    R_P(mu)<=2B+7/8+(u/24)(B-2).                          (JR14)

This crosses the same continuation gate exactly when

    u<68029220008060721916648/12707171689116034479349
      =5.353608314455152... .                             (JR15)

JR13 is a simple rational member of this all-height domain.

## 4. An actual29-original family with simultaneous damage

Order `Q=(5,7,11,13,17,19)`. Keep the two pure3 originals. For each
q add exponent0 with Q phase0 and exponent1 with ternary phase2 and
Q phase1. At cofactors `5,7,11,13,17,25`, add exponent4 originals with
Q phase2 and respective ternary phases `0,6,9,15,18,24`. At cofactor19
add exponent4 with ternary phase2 and Q phase2. At the six prime
cofactors add exponent5 with Q phase2 and respective ternary phases
`27,33,36,42,45,51`. At cofactor25 also add exponent0/Q phase0 and
exponent1/ternary phase2/Q phase1. Every pair of coprime ternary and
Q phases determines one fixed original residue by CRT. All29 numerical
moduli are distinct.

Select `{0,1}` at the six prime cofactors and at25. The actual PA
source is the product of uniform first digits `2,...,q-1` with Haar
higher digits. The selected25 cylinders are already excluded by the
selected5 roots, so they do not alter this source. All later PA caps
are inactive. On the positive source event with Q coordinate2 at all
primes and coordinate2 modulo25, every deep original is incident.
Its source mass is `1/(5 product_(q in Q)(q-2))`.

The ternary cylinders are pairwise disjoint within each branch,
including unequal heights. Thus this common event has

    Y_A=16/3, Y_B=2/3, c_A=5/9, c_B=26/27,
    2c_A+3c_B=4.

These are also the worst joint loads, so JR13 holds everywhere. The
example is outside Report584's `c_B=1` class. It verifies simultaneous
actual damage under one admissible source, not merely separately
attainable branch summaries.

Replacing the q=19 exponent5 original by exponent H with the SAME
ternary phase51 and Q phase2, for any integer H>=5, leaves the source
unchanged. All cylinders remain disjoint and

    max Y_A=46/9+54*3^(-H)<=16/3,
    max(Y_A+Y_B)<=6.

Both branches still lose mass on the same positive event. This gives
arbitrarily large actual original heights within JR13.

At H=5 the actual essential capacity minima from
[Report581](581-common-fibre-capacity-allocates-the-two-ternary-roots.md) are
`a=20/3,b=52/3,r=20/3,beta=24`. Its optimized raw uniform-cap
coefficient is79/72, so using the SAME supplier bound B gives

    B+(79/72)(1+B)=11.5897666670218... >566/49.

The mean exponent4 A count is86/99, independent of H. This exceeds
[Report580](580-actual-branch-loads-extend-the-height-four-query-certificate.md)'s
retained rho-only sufficient threshold. That is a
comparison between specified budget interfaces. The explicit source
has a much smaller actual query norm, and older instance-specific
certificates already establish its noncoverage. No failure of all
older methods is claimed, nor is the raw-budget separation asserted
for every H. The general theorem, rather than this finite control,
carries the arbitrary-family and all-height conclusion.

## 5. Remaining assumptions and verification scope

Distinct moduli have not been shown to force JR1 or JR13. The argument
does not remove arbitrary shallow projected multiplicity, generalize
the fixed pure3 geometry, or handle arbitrary support primes beyond
the stated nine-prime continuation. It keeps every original phase,
the complete query inventory and one actual probability throughout.

The [exact producer](../../frontier/cover-geometry/joint_weighted_query_reserve.py)
and [data](../../frontier/cover-geometry/joint_weighted_query_reserve.json)
pin Report569's exact source data and the existing
all-threshold envelope, and checks its four
second-hinge corner margins, suffix/cap coefficients, complete
geometric tails, the new rational budget and continuation, and the
actual29-original control. All140 named checks pass, including all96
actual incidence patterns at each of heights5 and11. The mathematical
proof supplies the
unbounded-height and all-layout quantifiers. These are ordinary
deductions with exact rational controls; no new Lean verification is
claimed.

Run with Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_weighted_query_reserve.py
