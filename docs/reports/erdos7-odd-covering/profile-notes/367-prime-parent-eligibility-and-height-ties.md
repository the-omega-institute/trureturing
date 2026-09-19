[Index](../marked_head_profile.md) · [Common source](363-common-source-antichain-capacity.md) · [Forced colors](364-singleton-cofactor-ideal-and-forced-colors.md) · [Complete repair interfaces](365-coloring-literature-and-reconfiguration-interface.md) · [Shallow truncation](366-shallow-tail-truncation-on-the-actual-source.md)

# Actual prime-parent eligibility and the limit of minimizing height

Keeping the intersection of the two prime-parent eligibility conditions
in 363 sharpens its source allowance. This uses the same original
classes and Haar law; it is a direct support refinement, not a new
matching theorem. In the divisor-closed period-450 control, it improves
366's complete lower bound from 2/25 to 11/120 within the same 11/50
target budget.

A separate actual control shows why minimizing selected heights does
not solve joint selection. Two original sources can both attain their
minimum height and still use the same residual original-label slot.
An equal-height exchange repairs that particular collision, but height
does not strictly decrease. The missing general step is an exchange
that preserves every source's rank and forced edges and improves a
shared objective without creating new conflicts.

Both complete covering controls contain even moduli. None is a
counterexample to an extremal odd-cover assertion. The arguments and
exact experiments below do not resolve unrestricted Erdos #7, add a
Lean declaration, or claim literature novelty.

## 1. Preserve the exact joint support of prime-parent selections

Use the hypotheses and original quantities of 363 and 366. In
particular D is divisor-closed above one, every support prime is an
original label, all points are covered, comparable original classes
are disjoint, and H is the uniform law on the complete original period.
Let Z be the region avoiding the prime classes, and put

    E(x) = {d composite in D : x in A_d},
    K(x) = intersection_(d in E(x)) supp(d),
    F_q = {d in D : q|d and d/q^(v_q(d)) is prime}.

Every E(x), x in Z, is a nonempty antichain. Retain the actual
prime-parent selected mass P_q, the original private mass pi_q,
u_q=sum_(d in F_q) pi_d, and epsilon_q, Delta_q^F from 363.
Define the exact residual eligibility mass

    Gamma_q = H({x in Z : |E(x)|>=2,
                 q in K(x), E(x) intersect F_q nonempty}). (PE1)

For the same actual shallow maximum matchings as in 366,

    P_q <= U_q^Gamma := min((s-1)pi_q, u_q+Gamma_q),       (PE2)
    Gamma_q <= min(epsilon_q, Delta_q^F),
    U_q^Gamma <= U_q.

Indeed 363's fixed-q lift is injective at each original target point.
A selected prime-parent lift at x must both reset to Priv_q and use
an original label in F_q. On singleton E its mass is at most u_q.
On the residual it is contained in the event PE1 and has multiplicity
at most one. The first bound by epsilon_q drops only the F_q condition;
the second bounds the event indicator by the number of active F_q
labels and integrates to Delta_q^F. The distinct-prime-parent count
gives the other term (s-1)pi_q. All statements concern the same lifted
set, not independently optimized sources.

The exact event can be written from the same original active-family
distribution lambda_A=H({x in Z:E(x)=A}):

    Gamma_q = sum_(|A|>=2, q in intersection supp(A),
                  A intersect F_q nonempty) lambda_A.     (PE3)

It generally requires more joint data than the separate scalars
epsilon_q and Delta_q^F. Computing Gamma_q from all cells does not
by itself give an efficient formula or a uniform arithmetic bound.

Keeping the original full-height alpha_q, the actual rbar_q and the
forced composite-color count f_q of 366, its same proof gives

    sum_q [f_q pi_q
       + ((rbar_q-f_q)pi_q-U_q^Gamma)_+/alpha_q]
       <= M_comp.                                        (PE4)

Thus PE4 dominates ST5. It still need not contradict the original
budget. No point-dependent denominator is introduced.

## 2. Prime-parent slots have no additional cross-prime competition

At a residual point x with |E(x)|>=2, an original label d cannot
belong to F_q and F_r for different q,r in K(x). Such membership
would force d=qr: a number of the form q^e p with prime p can also
have a prime r-free cofactor, with r!=q, only when p=r and e=1.
But q and r divide every member of E(x). Then d divides every member
of E(x), contrary to its being a nonsingleton antichain containing d.

Further, if q is eligible in PE1, some d in E(x) has support exactly
{q,p}. Consequently K(x) is a subset of {q,p}. If |K(x)|>=3, no
prime-parent direction is eligible. If |K(x)|=1, there is at most
one eligible direction. If |K(x)|=2, there are at most two, and their
eligible original labels are disjoint by the preceding argument.

In particular, after restricting 365's residual label-slot model
to actual prime-parent eligibility, per-direction capacity w_E on
each active-family cell already implies its total |E|w_E capacity.
For two eligible directions, |E|>=2; for one, the inequality is
immediate. No extra cross-prime slot cut is obtained this way.

This observation is specific to prime parents. Composite-parent
selections can share one original label across different primes.
Nor does it construct local matchings: choices at several target
points must still belong to one matching at each original source.
The improvement in PE4 comes from keeping joint eligibility, not
from an additional prime-parent resource competition.

## 3. Strict improvement on the complete period-450 cover

Use the fourteen original classes of 366:

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6),
    (4 mod 9), (9 mod 10), (7 mod 15), (11 mod 25),
    (13 mod 30), (1 mod 45), (31 mod 50), (46 mod 75),
    (1 mod 150), (16 mod 225).

For q=3, the residual cells with 3 in K have these exact masses:

| Active family E | H(cell) | Has an F_3 label |
| --- | --- | --- |
| {9,30} | 5/450 | no |
| {9,75} | 1/450 | no |
| {9,150} | 1/450 | no |
| {45,150} | 1/450 | yes |
| {9,15} | 5/450 | yes |
| {45,75} | 1/450 | yes |

Thus Gamma_3=7/450, whereas epsilon_3=7/225 and
Delta_3^F=1/15. With u_3=1/9 and pi_3=13/150,

    U_3 = 32/225,
    U_3^Gamma = min(26/150, 1/9+7/450) = 19/150.

Here f_3=0, alpha_3=4/3 and rbar_3=76/39, so the q=3
summand changes from 1/50 to

    ((76/39)(13/150)-19/150)/(4/3) = 19/600.

The q=2 and q=5 summands remain 2/75 and 1/30. At q=5 the
eligibility mass also decreases, but the other term (s-1)pi_5
already determines U_5, so that change gives no target-budget gain.
The complete bound is therefore

    2/25 < 11/120 <= M_comp=11/50,
    11/120 - 2/25 = 7/600.                              (PE5)

The strict gap compares two necessary lower bounds in an actual
even cover. It does not claim that the stronger bound is optimal.

## 4. Minimum total height can still reuse an original residual slot

Consider the distinct original APs of period 3150:

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6),
    (0 mod 7), (4 mod 9), (7 mod 10), (3 mod 14),
    (4 mod 15), (19 mod 21), (6 mod 25), (8 mod 35),
    (25 mod 42), (16 mod 45), (21 mod 50), (55 mod 63),
    (23 mod 70), (1 mod 75), (1 mod 105), (16 mod 175),
    (223 mod 315), (436 mod 525).

The whole period is covered, every class is essential, D is
divisor-closed above one and comparable classes are disjoint.
There are 605 prime-private source points, counting each pair
(q,y) on its actual complete source.

At each (q,y), take the truncated nonpure graph of 366. Restrict
to its maximum matchings with the original forced height-one
edges retained. Define the total selection height

    Phi(M) = sum_(q,y in Priv_q) sum_(d selected at y) v_q(d).

Before imposing any cross-source slot condition, these source
menus form a Cartesian product. Hence Phi is minimized by choosing
a minimum-height matching independently at each source.

At z=1, the actual active family is E(z)={75,105} and
K(z)={3,5}. Resetting only the first prime digit gives

    T_3 z=351 in Priv_3,
    T_5 z=3025 in Priv_5.

Both sources have cutoff one. Their complete maximum matching menus
are:

| Source | Maximum original-label matchings | Minimum height |
| --- | --- | --- |
| (3,351) | {75,6} or {105,6} | 2 |
| (5,3025) | {105,10,35,15} | 4 |

Each listed edge has q-height one, the absolute minimum. Select
{105,6} at the first source and the unique matching at the second.
Both selections lift their 105-edge to the same original point z=1,
so the actual slot (1,105) is used twice. The remaining sources can
each take a minimum-height matching independently. Exact enumeration
gives global minimum Phi=908, attained also by this colliding family.

Thus minimizing total height alone does not imply unit residual
slot use, even for a whole irredundant divisor-closed cover. This
does not refute that assertion with an additional extremal odd-cover
hypothesis, nor exclude a suitable secondary objective.

Replacing 105 by 75 at source (3,351) retains both roots, both
distinct colors, maximum rank, forced edges, cutoff and original
coordinates. The q=5 source has no 75-edge available at z=1 because
75 has 5-height two, above its cutoff one. Hence this particular
exchange moves to a slot unavailable to the competing direction.
Its height is unchanged, so a strictly decreasing height argument
cannot certify the exchange process.

In a general source graph, the alternative color may already be
used at another root. Then an alternating sequence is needed; it
must stay inside the actual truncated graph and can create a
collision at another original point. Neither the active antichain
nor 366 proves an available endpoint or a strict decrease of a
global collision objective. Finiteness of a proposed potential
does not supply a decreasing move when one is needed.

## 5. Verification and the remaining implication

The [standalone exact checker](../frontier/prime_parent_eligibility_and_height.py)
retains literal AP residues, complete original periods and tails,
forced edges and exact rational Haar masses. It checks PE1--PE5
on the period-450 fixture and the entire source menu product's
separable height minimum on the period-3150 fixture. The latter
enumerates each local matching menu, not all global combinations.
An explicit pair of local minima then certifies that a global
minimum can collide. These are finite controls, not Lean proofs.

The checker passes 10,222 checks across 3,600 complete-period points,
733 actual sources and 3,102 Hall subsets. It enumerates 1,001 local
maximum matchings, of which 997 minimize height within their source.
An isolated copy in a path containing spaces produces identical JSON
with `python3 -I -S -O -B`; checks remain active under optimization.
The program uses only the Python standard library and requires no
repository imports, external data or solver.

The reusable arithmetic question remains whether a hypothetical
extremal odd cover admits simultaneous actual shallow selections
with sufficient global compatibility to improve the original
cover. Joint eligibility reduces an upper allowance but does not
answer that question. A unit-slot matching would itself still
need a separate proof that an AP replacement preserves every joint
coverage liability and strictly improves the extremal objective.
