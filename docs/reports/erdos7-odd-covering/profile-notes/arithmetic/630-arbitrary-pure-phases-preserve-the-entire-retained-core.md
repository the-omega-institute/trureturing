# Arbitrary pure phases preserve the entire retained core

All pure phases and all phases of the156 retained mixed labels can be
arbitrary, without any shared-endpoint condition. There is one actual
product pure-survivor probability rho whose simultaneous retained
survivor has mass at least

    delta=2023457597/269374248000 >3/400.                 (RC1)

On the seven reference primes its Haar mass is at least

    h=289065371/262856056320 >1/910.                    (RC2)

The same Haar bound holds for the corresponding retained inventory on
any seven increasing odd primes. These statements concern the declared
156 mixed slots and arbitrary finite pure powers only. They do not pay
any additional mixed original or the complete L/W continuation gate.
They are ordinary mathematical deductions with exact finite arithmetic,
not new Lean verification or a solution of unrestricted Erdős #7.

The proof joins [Report613](613-arbitrary-star-and-pair-phases-leave-a-retained-core-survivor.md)'s
whole-source union estimate to [Report624](624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md)'s
actual arbitrary-pure source and numerical corner comparison. Report613
fixed the central pure phases. Here those restrictions are removed,
while retaining fully independent endpoint choices within each edge.

## 1. Exact original inventory and one actual source

First use P={3,5,7,11,13,17,19} and Q={7,11,13,17,19}. The family is
finite; its numerical moduli are distinct, odd and greater than1. Each
original has one residue fixed globally. All pure powers of primes in P
may occur at arbitrary finite heights and with arbitrary phases. The
only mixed moduli permitted in this result are a subset of the slots

    15;
    3q,5q,15q,9q,25q,3q^2,5q^2                    for q in Q;
    3^a5^b q^e s^f                                for q<s in Q,
       a,b in{0,1}, (e,f) in{(1,1),(2,1),(1,2)}.        (RC3)

These are1+35+120=156 distinct numerical labels. Every present star and
pair label has arbitrary central and outside components. No endpoint
sharing, root alignment, or agreement between different exponent types
is imposed. Missing slots can only reduce the debits below.

Construct the actual probability sources of Report624 before making
any numerical comparison. At3 and5 their Haar domination constants are2
and4/3, respectively. After an actual or auxiliary first pure root and an actual or
auxiliary square leaf have been deleted, write their live-root leaf
masses as w_l, l=0,...,5, and v_m, m=0,...,19. They satisfy

    sum_l w_l=sum_m v_m=1,
    w_z3=0, 0<=w_l<=2/9,
    v_z5=0, 0<=v_m<=4/75.                            (RC4)

Their higher-digit densities are supported on the complements of every
actual pure original. These are not arbitrary leaf weights detached
from the actual source. The finite original heights are unrestricted.

At q in Q use the actual root-balanced pure survivor rho_q, with

    r_q=1/(q-1),  a_q=1/[q(q-2)],
    rho_q(mod-q cylinder)<=r_q,
    rho_q(mod-q^2 cylinder)<=a_q,
    rho_q<=[q/(q-2)] Haar_q.                         (RC5)

All factors belong to the same actual family. Let rho be their product.
Its full Haar domination constant is

    D=2*(4/3)*product_(q in Q) q/(q-2)=13832/2025.     (RC6)

Keep the actual15 rectangle if its endpoints remain live. If the slot is
absent or already source-null, impose one live auxiliary rectangle.
Transport all original phases and reference leaves by the same rooted
digit permutations so that this rectangle is(row0,column0), with
row=l//3 and column=m//5. The actual or auxiliary rectangle is denoted M.
An auxiliary deletion shrinks the witness; it is not a new original and
does not change any numerical label. This is the normalization of
Report624 section3, including its source-null case.

## 2. Bound every event outside the same central mask

For the central product law define

    mu=rho_central(M complement),
    R=max mass of a mod3 row outside M,
    C=max mass of a mod5 column outside M,
    P=max mass of a(mod3,mod5) point outside M,
    A=max mass of a mod9 leaf outside M,
    B=max mass of a mod25 leaf outside M.             (RC7)

The maxima range over the complete actual role menus, including
source-null roles with mass0. They all use the same w and v.

For a fixed q, the five first-power star events have total mass outside
M at most r_q(R+C+P+A+B). The two square stars cost at most a_q(R+C).
This follows from product factorization between the central and outside
coordinates, followed by the union bound; no disjointness is assumed.

For an edge{q,s}, put kappa_qs=r_qr_s+a_qr_s+r_qa_s. Its unconditional,
row, column and point variants have total central coefficient at most
mu+R+C+P for each outside exponent type. Thus all120 pair originals
together cost at most(sum kappa_qs)(mu+R+C+P), even when every label has
independent endpoints and central roles. Uniform upper bounds on each
fixed original are being summed; no incompatible maximizing choices are
claimed to occur simultaneously.

Consequently the actual survivor U, including all pure and present
retained mixed originals, satisfies

    rho(U)>=F(w,v),
    F(w,v)=mu
      -(sum_q r_q)(R+C+P+A+B)
      -(sum_q a_q)(R+C)
      -(sum_(q<s) kappa_qs)(mu+R+C+P).               (RC8)

The auxiliary mask, if used, only strengthens the avoided set. The
constants in this single-source estimate are

    sum_q r_q=337/720,
    sum_q a_q=4099/77805,
    sum_(q<s) kappa_qs=607991257/5986094400.           (RC9)

No condition is imposed separately at a central cell. In particular
[Report629](629-free-pair-endpoints-need-a-common-source-with-dead-fibres.md)'s
actual empty fibre is compatible with this positive global estimate.

## 3. Separate concavity reduces the actual source to twenty corners

For fixed v, every mass in RC7 before taking a maximum is linear in w.
The corresponding statement holds after exchanging w and v. Hence mu
is separately affine, each of R,C,P,A,B is separately convex, and F is
separately concave. The coefficients of all five maxima in RC8 are
nonpositive. No joint concavity in(w,v) is needed.

For a fixed null leaf z3, the five nonnull deficits2/9-w_l are
nonnegative and sum to1/9. The weights9(2/9-w_l) express w as a convex
combination of the five vectors with one weakened mass1/9 and four
masses2/9. Likewise75(4/75-v_m) express v as a convex combination of
the nineteen vectors with one weakened mass3/75 and eighteen masses4/75.
Apply separate concavity first in w and then in v. This proves that F
on the actual source is at least its minimum on those numerical corners.
It does not replace the actual higher-digit source by a corner law.

There are30 ternary and380 quinary ordered(null,weakened) corners.
Leaf permutations within each root, together with permutations of the
three nondistinguished quinary roots, preserve M and all role menus.
The complete orbit representatives and orbit sizes are those of
Report624:

    THREE=((0,1),(0,3),(3,4),(3,0)), sizes=(6,9,6,9);
    FIVE=((0,1),(0,5),(5,6),(5,0),(5,10)), sizes=(20,75,60,75,150).

Thus the30*380=11400 numerical corners reduce to20 types. Exact
evaluation of all57 role masses in each type gives the minimum

    F_min=2023457597/269374248000,

attained in cases2 and4, namely(null3,weak3,null5,weak5)=(0,1,5,6)
and(0,1,5,10). At either minimizer,

    mu=41/45, R=2/3, C=4/15, P=8/45, A=2/9, B=4/75.

Substitution into RC8--RC9 gives the displayed rational minimum. Its
excess over3/400 is3150737/269374248000>0. This proves RC1 for every
actual source constructed above. Dividing by D proves RC2, with

    h-1/910=1487933/1839992394240>0.

## 4. Prime transport and the continuation boundary

For any seven increasing odd primes r_i, use the digit injections of
[Report628](628-digit-injections-transport-free-endpoint-heads-and-common-sources.md)
from reference primes(3,5,7,11,13,17,19). For every fixed injection, a
target prefix original pulls back to empty or one source prefix with
the same exponent vector. Distinct numerical labels remain distinct.
The pure/retained inventory RC3 depends only on these vectors, and all
phases are already arbitrary. Every pulled-back family therefore has
the same Haar survivor lower bound h before averaging. Independent
uniform digit shifts restore target Haar exactly, so the target
survivor also has Haar mass at least h>1/910. Heights need only resolve
the finite input family; no uniform height cutoff is introduced.

On the reference primes eta=rho restricted to U is one supported
submeasure of mass at least delta and with the same product-source
joint prefix upper bounds. Report628's explicit simultaneous-source
transport also preserves such bounds if this same eta is selected for
each pulled-back family. These observations do not give a sufficiently
small complete query norm: positive mass and a density upper bound do
not by themselves establish eta(1)-c Gamma(eta)>0.

In particular this result does not add arbitrary remaining core mixed
moduli, the unrestricted23/29/31 continuation, small-owner networks or
private interfaces. The outstanding gate must still pay those original
deletions and all declared future queries on one actual source.

## 5. Exact finite verification

The [portable producer](../../frontier/cover-geometry/arbitrary_pure_retained_core_bound.py)
and [data](../../frontier/cover-geometry/arbitrary_pure_retained_core_bound.json)
retain every corner's complete role menus, maxima, debits and lower
bound, the156-label inventory, density conversion and source orbit
sizes. The producer has85 named checks and uses only exact rational
arithmetic from the standard library:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_pure_retained_core_bound.py

An independent computation constructs the120-cell integer weight grid
and every complete role menu at all11400 corners, without importing the
producer. It obtains the same20 orbit values and minimum, with1260
minimizing corners. These checks establish the finite arithmetic; the
source construction, separate-concavity argument and digit transport
carry the arbitrary-phase and arbitrary-height conclusions.
