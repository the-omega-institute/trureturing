# Actual phase unions and a common affine reference enlarge the certified families

[Report 718](718-one-reference-source-releases-132-shallow-phases-and-all-higher-heights.md)
released 132 shallow phases while keeping the other 59 matched to a
reference. Here common affine transport handles the eight pure anchors,
and one actual union bound replaces literal matching of the mixed phases.
The sufficient test retains overlaps on the same source. Four complete
201-original examples lie outside all four former template orbits and
still have positive certified survivor density.

All conclusions retain distinct odd nonunit numerical moduli, prime
support in {3,5,7,11,13,17,19,23,29}, and whole-family v3 <= 2. The
universal positivity of the new test for arbitrary mixed phases remains
unproved. These are ordinary finite proofs and exact rational checks,
not new Lean verification or a solution of unrestricted Erdős #7.

## Common affine reference and the eight pure anchors

The 59-slot phase condition from the shared-source repair theorem contains
eight pure slots:3,9,5,7,11,13,17,19. Their numerical residues are mostly
reference choices. One simultaneous affine transport can normalize all
of them, while preserving every original numerical modulus and the
joint consistency of all mixed phases. After this normalization the
remaining substantive conditions concern seven head mixed labels and
44 singleton-outside mixed labels, or their weaker actual-union versions.

### One affine map on one common finite period

Let F be one actual finite family with distinct odd nonunit numerical
moduli and support contained in 3,5,7,11,13,17,19,23,29, withv 3<=2. Let M
be a common multiple of its original LCM and 9*5*7*11*13*17*19. Adding
unused period coordinates changes neither covering nor survivor density.

For integers u,v with gcd(u,M)=1, the map

    x mod M -> ux+v mod M

is a permutation of the SAME finite residue space. An actual original
cylinder a_m mod m maps exactly to(ua_m+v)mod m. Its numerical label m is
unchanged; different labels remain distinct; all intersections and
survivor counts are preserved. In particular survivor density and
noncoverage are preserved. The inverse is u^(-1)(x-v)mod M.

This is a permutation of Z/MZ. When |u| is not 1 it is not asserted to be
a bijection of the integers themselves; periodicity is what transfers
the covering and density statement. Equivalently, on each relevant
p-adic factor u is a unit and the map preserves Haar measure.

For each prime-power factor p^E of M choose local u_p invertible mod p^E
and local v_p. CRT combines all of these into ONE pair(u,v)mod M.
Independent local coordinate choices are therefore legitimate only in
this precise sense: every original involving several primes receives
the simultaneously induced phases from that one pair. No original
label receives a separately chosen rephasing.

### Nonternary pure roots

If the actual pure q original has residue a_q mod q, choose any nonzero
local first-digit multiplier u_q and set

    v_q=-u_q a_q mod q.

Then its image is 0 mod q. This can be done simultaneously for all six
q in Q={5,7,11,13,17,19}. Every such first-digit choice lifts to a unit
and translation modulo the actual q^E: choose any compatible higher
digits. Higher originals retain their complete numerical labels and
are sent to some transformed phases, which the all-height theorem
already permits to be arbitrary.

If a pure q label is absent, there is no phase to constrain. The source
may still exclude a chosen root as an auxiliary restriction; it does
not thereby claim that a pure q original exists in F.

### The two actual ternary pure slots

Suppose both pure 3 and pure 9 occur, with residues a 3 mod 3
anda 9 mod 9. There are two genuinely different incidence cases.

Ifa 9 mod 3!=a3, choose a unit u mod 9 satisfying

    u(a9-a3)=1 mod3,
    v=1-u a9 mod9.

Thenua 3+v=0 mod 3 andua 9+v=1 mod 9. Such a unit always exists; exactly
three of the six units mod 9 have the required residue mod 3. Thus the
nonredundant two-class pure family has the canonical anchors 0 mod 3 and
1 mod 9, giving the same five retained leaves 4,7,2,5,8.

Ifa 9 mod 3=a3, the pure 9 cylinder is already contained in the forbidden
pure 3 cylinder. Take v=-u a9 mod 9 to send both into 0 mod 3 (and pure 9 to
0 mod 9). That actual pure 9 event is automatically avoided by a source
supported outside 0 mod 3. One may additionally restrict the SOURCE to
avoid 1 mod 9 and use the same five-leaf construction. This is not a
second actual 9 original and does not reassign the existing numerical
label 9. Every actual mixed original remains at its actual transported
phase. Only the pure 9 slot's literal matching condition is replaced
by the proved fact that the source already avoids it.

If only pure 9 occurs, send it to 1 mod 9 and optionally restrict the
source outside 0 mod 3. If only pure 3 occurs, send it to 0 mod 3 and
optionally remove 1 mod 9 from the source. If both are absent, both
reference exclusions may be made as auxiliary source restrictions.

Thus the eight pure phase slots can be accommodated without a
numerical-phase restriction. The mixed relative phases cannot be
normalized independently by this argument.

### Residual reference freedom and actual invariants

After the nonredundant ternary anchors are 0 mod 3 and 1 mod 9, an affine
map preserving both must satisfy

    u in{1,4,7}mod9, v=1-u mod9.

This residual three-element group fixes the two retained leaves 4,7
individually and cycles the other root's leaves 2,5,8. It does not
permit an arbitrary permutation of the five retained leaves or an
exchange of the roots. The root weights and all common source data
must be transported with the same map.

For each nonternary q, after the pure anchor is 0, residual first-digit
maps have v_q=0 and u_q any nonzero residue. If an original has first
phase a_m at q, its anchor-relative difference

    delta_(m,q)=a_m-a_q mod q

transforms to u_q delta_(m,q). Therefore the following are invariant:
zero versus nonzero anchor-relative phase, equality of two relative
phases, and ratios delta_(m,q)/delta_(n,q) when the denominator is
nonzero. At higher exponents, multiplication by a unit preserves
p-adic valuations of phase differences on their common precision.
These are shared cross-label relations; one scalar u_q acts on EVERY
original carrying q.

For a finite list of required template phases, membership in a common
affine orbit can be checked coordinate by coordinate. A nonzero
relative phase determines the local multiplier; all remaining required
phases must agree with that SAME multiplier. The ternary check tests
its finite common affine options modulo 9. The resulting local choices
are joined by CRT once, then verified against each full original label.
A failed check cannot be repaired by choosing a different multiplier
for a different cofactor of the same prime.

### Consequence for the four template classes

The 132-phase release theorem transports to the common affine orbit
of each of its four 59-slot templates, with exactly the same Haar
lower bound. In the redundant pure 9 case the reference source's
extra leaf deletion supplies the same proof, provided the MIXED
transported phase conditions (or the weaker actual-union debit test)
hold. The numerical labels and all nonternary heights remain intact.

The effective literal mixed conditions are the seven head labels
15,45,21,63,35,105,315 and the 44 singleton-outside mixed labels c*q,
where q in{11,13,17,19} and c is a nonunit divisor of 315 withv 3(c)<=2.
This counts 51 numerical slots, not 51 independent scalar invariants:
each slot has several prime components, tied by the same reference
transport. Their cross-cofactor relative phases are the remaining
obstruction to this sufficient method. One may replace literal agreement by the
rowwise union conditions below, which
preserve actual overlaps and can admit further phase variation.

This identifies the proper parameter space for a future forcing
argument: globally consistent mixed phase relations modulo the common
affine reference group. It does not prove that all such relations lie
in the four template orbits or satisfy a positive repaired gate.
The argument is ordinary finite CRT mathematics, not new Lean work.

## Actual unary phase unions replace literal phase matching

The 132-phase release proof need not require literal agreement of the
other 59 phases. A further sufficient condition can be evaluated from
the ACTUAL unions those phases induce on each retained head row.
The sufficient condition is a finite, exact four-coordinate calculation
on one common reference measure.

Fix ONE reference source eta with the same row masses, unary laws xi,
sixteen responses H, and one uniform thinning as before. No row chooses
a different reference or a different query source. The target family
may now have arbitrary shallow phases. All numerical labels and their
phases are fixed globally before forming the following row data.

For each retained head row u, test all actual target head-only originals
in the numerical head slots dividing 315. If any forbids u, its entire
row mass Z(u) is lost. Otherwise, for q in B={11,13,17,19}, let A_q^F(u)
be the actual forbidden-root union from all target shallow originals
whose outside support is exactly{q}, including the pure q slot. Let

    delta_q(u)=xi_(q,u)(A_q^F(u)),
    m_q(u)=xi_(q,u)(1).

These are subprobability masses under the REFERENCE unary law; roots
already removed by the reference cost zero. Repeated target roots
are counted once. Inactive head phases contribute nothing. This is
not the number of changed labels or the sum of their individual caps.

For nonempty J subset B, the exact union mass under the coordinate product
of the reference unary laws is

    d_J(u)=product_(q inJ)m_q(u)
                -product_(q inJ)(m_q(u)-delta_q(u)).       (UP1)

This is just independence of different coordinates under that
DOMINATING product. The reference source zeta_u itself need not be a
product. Its simultaneous marginal-measure bounds give

    zeta_u(union_(q inJ){x_q inA_q^F(u)})
       <=H_J(u)d_J(u).                                  (UP2)

For every set partition Pi of the four actual coordinates, union-bound
the packets and then clip by the row mass. Thus the actual new unary
loss on a retained target-compatible row is at most

    d_star(u)=min{Z(u),
         min_(Pi a set partition ofB)
                     sum_(J inPi)H_J(u)d_J(u)}.           (UP3)

There are 15 set partitions, not a phase scan. All 15 bounds concern the
SAME actual row union and SAME zeta_u; their minimum is valid. The
singleton partition supplies sum_qH_{q}delta_q. The single-packet
partition supplies product_Bm-product_B(m-delta), because H_B=1.
Intermediate partitions preserve some smallerH_J multipliers while
capturing actual cross-coordinate overlap inside each packet.

Set d(u)=Z(u) on rows killed by a target head original, and d(u)=d_star(u)
on the remaining rows. Then

    D_actual=sum_u a(u)d(u)

bounds the loss needed to repair every head and singleton-outside
shallow slot, with NO literal phase-matching assumption. Continue to
pay all 132 multi-outside-support shallow slots by B_R, or replace that
uniform upper by a certified smaller actual union debit. All deep
originals are still paid by A from the original prefix-constanteta,
and the complete query upper K still applies by measure restriction.
Hence

    (566/49)(S-D_actual-B_R-A)-K>0                       (UP4)

certifies that this entirely actual family does not cover, with the
same Haar-density conversion as before. Pure outside 23/29 originals
and every original involving 23 or 29 are handled by the existing
actual pure-conditioned continuation. Onlyv 3<=2 and the fixed
nine-prime support remain global structural assumptions.

This removes literal 59-phase matching from the FORM of the test. It
does not prove UP 4 positive for every possible target phase family.
That uniform positivity is still the missing theorem.

## Exact zero-cost phase changes and the operative obstruction

If the target head-only forbidden set misses every retained reference
head row, and A_q^F(u) is contained in the reference's already excluded
root set for every positive row and every q, then all delta_q vanish.
Consequently D_actual=0 even when many original residues differ from
the reference. Literal matching is therefore sufficient but unnecessary.

For example, in an ALIGNED template every mixed singleton-outside
label c*q has a head phase lying in the actual forbidden head cylinder
oflabel c. Its outside residue can be changed arbitrarily without
altering that rowwise null event. More generally, any head phase whose
head-cylinder projection has empty intersection with the retained
reference head support has the same zero-cost property. Alternatively,
a q-root already excluded by xi makes the event null regardless of its
head phase. These are statements about one actual intersection, not
permission to choose phases independently on separate rows.

Thus the remaining difficulty is not intrinsically the count 59. It
is whether globally consistent actual phase choices can force a large
positive discrepancy union across every viable common source. UP1--UP4
preserve the joint data needed to study that question. Merely bounding
the individual number of changed residues would discard the collisions,
row incompatibility and already forbidden roots which the packet
calculation retains.

The proof uses the source's existing marginal-measure domination and
ordinary finite union formulas. It does not introduce new Lean results
or claim that the generic packet argument establishes universal
Erdős#7 positivity. The product hypothesis holds because xi is the declared dominating
unary product; no product structure is imposed on zeta_u or on the
final restricted source.

## Large simultaneous null-phase menus on the actual 75/85 heads

For each nonunit head cofactor c dividing 315, define

    N_c={a mod c : H_head intersect[a]_c=empty}.

The full phase of an originalc*q, q inB, is null on the reference
source whenever either its head residue lies in N_c or itsq residue
is 0. The permitted menu is the union of those two conditions, with
exact cardinality

    c+(q-1)|N_c|.                                    (UP5)

Every label still receives one actual complete residue modulo c*q.
All 44 menu choices can be made simultaneously: each actual event is
null on the SAME reference support, so no different source or per-row
phase selection is involved. These are permitted choices for different
originals of a new target family, not independent rephasings claimed
to describe one old family.

The exact projection-complement counts are:

| c | opposite-root head,75 cells | same-root head,85 cells |
| --- | ---: | ---: |
|3|1|1|
|5|1|1|
|7|1|1|
|9|4|4|
|15|8|8|
|21|10|10|
|35|13|12|
|45|29|28|
|63|36|36|
|105|70|70|
|315|240|230|

These are projections of the entire actual head survivor sets, not
counts inferred from the two head totals. The exact checker enumerates
every full phase of each c*q and confirmsUP 5. For example c=315,q=11
has 2715 allowed phases on the 75-cell head and 2615 on the 85-cell head,
all jointly null on their respective reference sources.

## Four complete target families outside the old affine templates

The exact artifact [retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_unary_packets.json) contains four
complete 201-original phase lists. Here is a reproducible specification
before one common affine transport.

For each of the two heads, begin from the corresponding ALIGNED 191
reference family. Keep its 11 head originals and four outside pure
originals. Replace every one of its 44 mixed singleton-outside phases
at c*q by the unique CRT residue with

    a mod c=max N_c, a mod q=q-1.

Replace every one of the 132 multi-outside-support phases by the
corresponding actual SPREAD phase of that same head's declared 191
family. All 176 of these shallow residues differ from the aligned
reference. This defines the ZERO-DEBIT variant. It has exactly the
same empty actual additional unary-root unions as the aligned source
on every retained head row, despite changing all 44 singleton residues.
All 132 arbitrary multi-support phases are still charged by the common
B_R bound from the phase-release theorem.

For the POSITIVE-PACKET variant, additionally override just the labels
315*11 and 315*13 with the common live head residue b=min H_head and
outside root 2. Thus b=4 for the opposite head andb=2 for the same head.
These two actual forbidden cylinders are live; they are not members
of the null-phase menu. On exactly that head row the new forbidden
root sets are{2} at 11 and{2} at 13; they are empty on all other head
rows and at 17,19. This is checked directly from the complete global
original phase list on EVERY retained head cell.

Adjoin the following ten distinct originals to each variant:

    7mod25,9mod49,13mod121,19mod169,23mod289,29mod361,
    5mod23,7mod29,31mod667,
    1234567 mod(9*25*7*11*23*29).

Their core-only deep labels and 23/29-bearing labels are covered by the
already proved complete-height budgets. There are 201 original numerical
labels, all distinct, odd and greater than 1, withv 3<=2.

Finally replace every original residue a mod m, including every deep
and outside original, by

    (a-1)*2^(-1) mod m.                               (UP6)

Because every m is odd, the SINGLE affine permutation x->2 x+1 modulo
one common period sends the entire final actual family back to the
specified canonical family. The pure phases are now noncanonical as
well. No label receives its own affine multiplier or translation.
The source, all actual events and survivor density transport together.

These four target families are outside ALL FOUR earlier 59-template
affine orbits. A short invariant witnesses this: in the canonical
target the 99 original has head residue 6 mod 9, so its cylinder lies
inside the pure 3 forbidden root 0. In every earlier reference the 99
phase is 1(ALIGNED) or 98(SPREAD), and neither lies in its pure 3 root 0.
Common affine transport preserves this inclusion between the original
numerical labels 99 and 3. Therefore no such transport matches their
required 59 slots. The exact checker also solves all local affine
congruence systems and confirms failure for every reference orbit.

This exclusion is not evidence of coverage: the following common-
source certificates prove that these new families and their declared
arbitrary-height extensions remain noncovering.

## A positive actual loss and a strictly stronger packet certificate

For the aligned reference, the outside unary masses all equal 1. Its
actual c=1 multi-support events forbid two or more coordinates taking
root 1. The full product has 34560 cells; exactly 33513 avoid those
reference events. The joint polynomial mass is

    Z=3335/3456.

The reference zeta is ONE uniform thinning of those 33513 actual cells
to this mass Z. On the special live head row, the target positive-packet
variant forbidsx 11=2 orx 13=2. Among those 33513 reference survivors,
exactly 5963 satisfy that actual new union. Its EXACT thinned mass is

    Z*5963/33513=19886605/115820928.

The dominating-product masses aredelta 11=1/10,delta 13=1/12, with the
other two deltas 0. Group 11 and 13 in one packet. Its union mass is 7/40,
and its multiplier H_{11,13}=1-1/(16*18)=287/288. Thus

    exact actual union <= 2009/11520 < 1561/8640,

where the last value is the separate singleton debit. All 15 partitions
are checked; the minimum 2009/11520 is achieved by the partition
{{11,13},{17},{19}} and by{{11,13},{17,19}}. The strict row-level saving
is 217/34560. This comparison retains the actual root overlap under one
reference zeta; no independent pointwise source maxima are combined.

The actual head coefficients are 1/96 at b=4 and 1/144 at b=2. Therefore
D_actual's packet upper is 2009/1105920 for the opposite head and
2009/1658880 for the same head. Relative to separate singleton charges,
the source-level savings are 217/3317760 and 217/4976640.

After paying this actual unary debit, all 132 arbitrary multi-support
shallow phases, all core deep phases at every nonternary height, and
the actual 23/29 continuation, the gates and Haar density bounds are:

| Target variant | Exact gate | Exact Haar lower | Decimal Haar lower |
| --- | --- | --- | ---: |
|opposite zero-debit|29470785747941/26968451973120|29470785747941/1486773449441280|0.01982197473261|
|opposite positive-packet|5780978999905/5393690394624|5780978999905/297354689888256|0.01944135806997|
|same zero-debit|10100409786827/8989483991040|10100409786827/495591149813760|0.02038052897155|
|same positive-packet|9974656287179/8989483991040|9974656287179/495591149813760|0.02012678452980|

The same bounds remain valid when the 132 multi-support shallow phases
and all additional deep/23/29 originals are replaced arbitrarily,
provided numerical distinctness, the fixed nine-prime support and
whole-familyv 3<=2 are retained. The zero-debit singleton phases may
range simultaneously over their UP 5 menus. In the positive variant the
two stated live singleton events are additionally paid as above; no
universal claim is made for arbitrary phases of every singleton slot.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_unary_packets.py) verifies
the menus, all actual head-row unary unions, the same reference source's
full 34560-cell conditional calculation, the 15 packet comparisons,
complete 201-label lists and common affine normalization, exclusion
from all four old affine template orbits, and the strict rational gates.
These finite results substantiate the displayed ordinary proofs and
scope. They do not establish universal positivity for all possible
mixed phase relations or constitute new Lean verification.


```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_unary_packets.py
```
