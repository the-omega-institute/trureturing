# One global two-parent network preserves a common survivor

Keep the ten-prime head restrictions of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md).
All outside entries can now belong to ONE increasing two-parent network,
with arbitrary connections between roots based on different head pairs.
Roots whose two head parents are among the first seven primes may connect
to roots using23,29 or31 through later nodes. The proportion of complete
head configurations admitting an avoiding extension is greater than1/90000,
uniformly over all finite original heights and globally fixed phases.

[Report612](612-shared-head-pair-networks-join-multiple-root-entries.md)
kept different head-pair networks disjoint. Here that restriction is removed.
The construction first samples the roots that only depend on the seven
initial head coordinates, then extends those head coordinates through the
existing23,29,31 physical kernels, and finally samples every remaining
outside entry. All violations are paid under the SAME joint law. No outside
blocker is deleted before head continuation, so the proof does not require
an early extension predicate to remain independent of the later head.

The change loses a small part of Report601's early-restriction saving.
The existing positive reserve pays that loss, retaining the same1/90000
simple head bound as Report612. This is an ordinary mathematical proof
with exact rational certificates, not new Lean verification or a resolution
of unrestricted Erdős #7.

## Complete original scope

First use the reference head

    P0={3,5,7,11,13,17,19}, P1={23,29,31}, P=P0 union P1.

These are the ten smallest primes in the actual finite family. Pure head
originals and all head originals touching P1 are unrestricted. A mixed
original on P0 must have an exponent at least three, exponents at most
one at3 and5, or at least five prime divisors, exactly as in Report598.
Every numerical original modulus is distinct and has one arbitrary
residue fixed once for that actual original.

The outside network has an arbitrary finite set of distinct entry primes
v>=37. Each entry has two FIXED distinct parents among all ten head
coordinates and the smaller outside entries. It owns any subset of

    a_v^i b_v^j v^e, i,j>=0, i+j>0, e>=1.       (GN1)

Thus both parents are numerically smaller than their owner. A root has
two head parents. An early root has both parents in P0; a late root has
at least one parent in P1. A nonroot has at least one outside parent
and is therefore at least41. Its parents may lie below different roots,
use different head pairs, or join any previously separate branches.
There is no partition of the outside coordinates by head pair or by
early/late root type. Both parents may themselves be outside entries.

There is no finite uniform bound on network depth, width, number of roots
or prime co-occurrence treewidth. The two-parent choice is nevertheless
fixed for each owner; a node is not granted several different parent-pair
inventories. All actual labels retain their complete exponent vectors
and phases. The largest introduced prime, with positive exponent, is
the unique owner of each mixed network original.

Each entry v has an allowed Report599 ordinary private block tree,
including pure-v originals. Its interior is disjoint from all network
entries and other private interiors away from its own attachment root.
The nontrivial blocks remain those of Report601: at most twelve vertices,
simple cycles, or the permitted oriented blocks with k>=4 children and
smallest child at least k(k+3)+3. Their depths and finite number remain
unrestricted, with their existing conditions unchanged. Ordinary Type I
attachments to one head coordinate and separate ordinary components are
also retained. There are no extra originals crossing these ordinary
interiors beyond their declared attachment interfaces.

Every original is assigned once to the head, an owner's fixed mixed
inventory, or one ordinary block. All original heights are arbitrary
finite quantities. The transport argument below gives the same result
for any ten ordered odd head primes that are the ten smallest in the
family, leaving all outside prime coordinates fixed.

## The actual homogeneous head continuation is a normalized process

Choose finite coordinates resolving all original head and outside heights.
Report598 supplies an actual submeasure eta on P0, supported on its allowed
head survivor, with

    eta<=rho=product_(p in P0)rho_p,
    eta(1)-c Gamma(eta)>=K,
    c=1084133/201247200,
    K=26345885990886052732242307711
          /9055182074115772514304000000000.     (GN2)

The product rho is a probability, as constructed in Reports590/591 and
retained in Reports597/598. Its density constants are

    rho_3<=2H_3,
    rho_p<=p/(p-2)H_p for p>=5,
    rho<=D H_(P0), D=3458/405.                  (GN3)

Thus eta(1)<=1 and every P0 pair marginal of eta is bounded by10/3 times
product Haar. Eta need not be a product and is not normalized below.
The complete query norm Gamma includes the unit and is homogeneous:
Gamma(eta/s)=Gamma(eta)/s when s=eta(1)>0.

The continuation used here is the actual normalized physical-kernel
construction, not merely the existence of a head survivor set.
[Report592, Section4](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)
uses controls2/5,9/20,1/2 at23,29,31; every row is normalized and
preserves the entire preceding joint law, including mass on forbidden
fibres. There is no conditioning on survival between steps.
[Report595, Section4](595-outside-square-extension-leaves-an-eighty-label-pair-core.md)
gives total forbidden-event charge at most c Gamma(eta/s) for the
normalized input. Multiplication by s gives an actual unnormalized
full-head law mu, with

    mu(1)=eta(1),
    mu(head_bad)<=c Gamma(eta),
    mu<=C H_P,
    C=D*(200/33)=138320/2673, alpha=1/C.         (GN4)

Its marginal on P0 is eta. The head kernels depend only on the current
head coordinates and actual head originals. The positive gate in GN2
ensures the existing continuation hypotheses. Its bounds remain valid
at the full resolving heights chosen for the network.

## Preload early roots, then lift the unchanged head kernels

For each outside entry v let V_v^0 be its actual ordinary private-domain
set, including pure-v originals and excluding its mixed network inventory.
The existing ordinary-domain induction gives

    H_v(V_v^0)>=1-2/(v-1).

For selected nonunit parent patterns, retain every actual positive-v-height
tower at that pattern. If N_v patterns are selected, their complement
R_v inside V_v^0 satisfies

    H_v(R_v)>=D_v/(v-1), D_v=v-3-N_v>0.         (GN5)

For roots, use exactly Report612's choices: Report601's minimizing finite
patterns through967, and its rectangle patterns in the entire larger-prime
tail. Every finite D_q is at least4, and tail choices have D_q>=485.
The actual chosen root fees G_E(q),G_L(q) satisfy

    S_E:=sum_(q>=37 prime)G_E(q)<1/2600,
    S_L:=sum_(q>=37 prime)G_L(q)<1/125000.       (GN6)

Finite G_E,G_L are the Report601 minima for references(3,5),(3,23).
Tail fees use the explicitly chosen rectangles, not an assumption that
those rectangles minimize each individual fee. Report612's full sums
already certify GN6 with these actual choices.

Starting from eta on P0, sample ALL early roots, using the normalized row

    nu_q(.|x0)=H_q(.|R_q(x0)).                 (GN7)

An early root's selected complement depends only on its two P0 parents,
its fixed original phases and its ordinary domain. No early root depends
on any outside entry. They can therefore all be sampled now, including
roots whose primes exceed some nonroots that will be sampled later.
Conditioned on x0, their joint kernel is the product of these root rows.

Apply the head-only continuation kernel K_head to this enlarged space,
without letting its rows read any outside coordinate. The exact joint law
at this point is

    eta(dx0) K_head(dx1|x0)
                  product_(early roots q)nu_q(dz_q|x0). (GN8)

Consequently the head marginal is exactly the law mu in GN4. Every early
root event retains its original mass. Conditional on a full head word
(x0,x1) of positive mu mass, the early roots still have the same product
kernel in GN8. In particular the passage through P1 does not alter their
conditional prefix bounds. This factorization is an actual construction;
it does not follow merely from equality of some marginals.

## Complete the one outside law without restrictions on root crossings

Now sample all late roots and all nonroots in increasing numerical order,
skipping the early roots already sampled. Every actual parent is present:
all head coordinates and all early roots are present, and every other
outside parent has a smaller prime. Numerically larger preloaded roots
may appear in the conditioning history, but cannot be parents of a smaller
owner. Their presence does not affect the uniform row bounds.

A late root q again uses only H_q(.|R_q), with conditional density at most

    A(q)=(q-1)/D_q                             (GN9)

relative to original q-Haar. We do not claim A(q)<=6: the retained late
root choice at41 has A(41)=10. Its row depends only on its two head words.

For a nonroot v use the normalized selected-complement base H_v(.|R_v)
and the same capped kernel, selected patterns and thresholds as Report612.
If alpha_v is the base mass of the remaining forbidden fibre and delta_v
is its threshold, the row is the complement conditioning when
alpha_v<=delta_v; otherwise its relative densities are

    (alpha_v-delta_v)/(alpha_v(1-delta_v)) on the forbidden part,
    1/(1-delta_v) outside it.

The resulting ORIGINAL-Haar conditional density is at most6 at EVERY
complete prior history. All rows are normalized, even when the remaining
forbidden fibre is full. Let Pi denote the final unnormalized joint law.
Its mass remains eta(1), its head marginal remains mu, and no stage has
been conditioned on whole-network or head survival.

Every entry lies in V_v^0 and avoids its selected towers. Let E_v be its
remaining mixed-violation event. The two root classes have bounds

    Pi(E_q)<=(10/3)G_E(q) for early roots,
    Pi(E_q)<=C G_L(q) for late roots.           (GN10)

For early roots this follows before head continuation from eta's pair
bound and is preserved by all later normalized rows. For late roots use
mu<=C H_P and the root complement calculation on the same head words.
Both use the full original height sum and fixed phases. Neither requires
these roots' parent pairs to be disjoint or independently distributed.

## Every queried outside coordinate keeps the same two prefix bounds

For every root q>=37 and positive j, GN9 with D_q>=4 implies

    A(q)/q^j <=(1/4)q^(1-j)
               <=(37/4)37^(-j),
    A(q)/q^j <=3^(-j).                         (GN11)

For every nonroot w>=41, its cap6 similarly gives

    6/w^j<=(37/4)37^(-j),
    6/w^j<=3^(-j).                             (GN12)

Early-root versions hold conditional on the full head and all other
preloaded roots, by GN8. Later versions hold conditional on the full
sampling past. These are stronger than marginal prefix statements.

Order the actual parents of a nonroot as a<b. The larger is outside.
For a joint parent-cylinder bound, eliminate queried outside coordinates
in REVERSE SAMPLING ORDER, integrating unqueried normalized rows without
cost. This need not be reverse numerical order, because early roots were
preloaded. If queried early roots remain at the end, use their conditional
product kernel in GN8. Each outside coordinate has both GN11/GN12 bounds,
so the smaller parent's role uses3^(-i) and the larger parent's role uses
(37/4)37^(-j), regardless of which was sampled last.

If both queried parents are outside, the resulting integral is bounded
by those factors times eta(1)<=1. If the smaller parent is a head prime,
use the preserved mu marginal and mu<=C H_P to bound its cylinder by
C*a^(-i)<=C*3^(-i). Thus in all cases the joint bound is at most C times
Report612's reference kernel

    k((i,j),(i',j'))
      =3^(-max(i,i'))37^(-max(j,j'))
         *[1 if max(j,j')=0, otherwise37/4].     (GN13)

There is only one factor C, including when both exponents on a head
coordinate occur in a square. Repeated queries intersect at the maximum
exponent. Incompatible phase cylinders contribute zero. No product of
unconditional marginal bounds is used.

Let M(N) be Report612's complete unselected-label moment, and let J(v)
be its corresponding nonroot fee. The same load-square expansion and
capped-row inequality, now integrated against the unnormalized Pi, give

    Pi(E_v)<=C J(v) for every nonroot v.        (GN14)

The inequality(z-delta)_+<=z^2/(4delta) is pointwise, so normalization
of eta is unnecessary. All selected and unselected actual labels retain
their numerical identities and fixed phases before the infinite majorants.
Report612's151 finite rows and complete rectangle tail yield

    W:=sum_(41<=v<=967 prime)J(v)
          +510/(2*3^22*971)
      approximately0.000003859592591261608
      <1/250000.                              (GN15)

Every outside prime is used at most once as an entry. The same complete
positive series therefore bounds all nonroots in the one global network,
without multiplying by the number of root pairs or crossing interfaces.

## Pay all actual bad events on that same joint law

The head-bad event has mass at most c Gamma(eta), by GN4 and preservation
of the head marginal. The ordinary Type I nonextension blockers are sets
on head coordinates with total head-Haar fee at most2^-17 from Report599.
Pulled back to Pi, their total mass is at most C*2^-17. These attachments
need not be sampled into Pi; good head words retain their actual avoiding
extensions. Their interiors are disjoint from the network.

Remove head-bad, all early-root E_q, all late-root E_q, all nonroot E_v,
and the Type I blocker events. One union bound gives

    Pi(good)
      >=eta(1)-c Gamma(eta)
           -(10/3)S_E-C(S_L+2^-17+W)
      >=K-(10/3)S_E-C(S_L+2^-17+W).             (GN16)

These are events under ONE law, with no independent witness selection,
source restart, separate optimum or undeclared coupling. Every original
phase is fixed before the construction. Overlap between bad events only
makes this upper union charge more conservative.

For every good joint configuration all head and mixed network originals
are avoided. Each selected entry word has its actual ordinary private
witness, and the disjoint ordinary interiors glue at those same words.
The Type I and separate ordinary components also extend. Thus the head
projection of good is contained in the actual head extension set U_ext.
Since Pi's head marginal mu<=C H_P,

    H_P(U_ext)>=alpha Pi(good)
      >=alpha K-alpha(10/3)S_E-S_L-2^-17-W.     (GN17)

The full projected set is used; no chosen outside witness is asserted to
have Haar distribution.

To compare directly with Report601, its exact lower bound is

    alpha K-alpha(1-c)(10/3)S_E-S_L-2^-17.

Not restricting early exterior blockers loses only alpha*c*(10/3)S_E.
Since S_E<1/2600, the additional loss is less than

    alpha*c/780=3252399/24368664320000.         (GN18)

Using Report601's simple reserve and GN15 therefore gives

    H_P(U_ext)
      >31991/2048000000
          -3252399/24368664320000-1/250000
       =447881975781/38989862912000000
       >1/90000.                              (GN19)

In particular GN16 is positive. The exact retained arithmetic gives a
head lower bound approximately0.000012310484307332786; the rational
inequalities, not that decimal, establish the conclusion.

Choose one good head word and one full network witness over it. All
cross-root and cross-head-pair interfaces already agree inside this
assignment. With the ordinary witnesses attached, CRT supplies an integer
avoiding every original class. If Q_off is the product of all outside
resolving prime powers, full survivor density is greater than
1/(90000 Q_off). The uniform1/90000 is a bound on extendible head words,
not full density independent of outside heights.

For arbitrary ten ordered odd head primes, use Reports601/612's head-only
shifted digit injections and padded pullbacks. Each transformed original
retains its full exponent/support vector and fixed parent assignment,
with a one-to-one correspondence between original and transformed
numerical labels. Empty pullbacks are padded at the same vector with one
fixed phase. All outside coordinates and their order remain fixed; early
and late root roles refer to the first-seven/last-three head positions.
A padded-source extension maps to a target extension with the same
outside witness. Averaging the head injections transfers GN19.

## An actual crossing outside Report612's decomposition

Take early root37 with parents(3,5), late root41 with parents(3,23),
and node43 with parents(37,41). Use the three actual squarefree originals

    3*5*37, 3*23*41, 37*41*43,

all with residue zero. Include the seven remaining head primes through
pure-prime originals; ordinary interiors may be empty. This is an admitted
global network, and the last original joins an early and a late root.

These actual supports force a larger class than Report612. The first two
originals force37 and41 to be roots with their displayed distinct head
pairs: a nonroot's two fixed parents cannot supply both required head
coordinates, and a private ordinary or Type I attachment cannot introduce
a second head interface. A single fixed head-pair network cannot contain
both forced root inventories. The remaining original joins their outside
coordinates, which Report612 disallows between different head-pair
networks. Moving a forced root into an ordinary private interior would
also violate that report's disjointness conditions. The ten-smallest-prime
head is fixed and cannot absorb37 or41. Thus the original family does not
admit an alternative Report612 decomposition. It is not a covering example.

## Remaining scope and the retained certificate

The removed restrictions are root-pair separation and early/late outside
separation. The remaining hypotheses include Report598's missing head
labels, ONE fixed pair of smaller parents for each network owner, and
ordinary private interiors with their declared interfaces. Several
parent-pair inventories at one owner would change its local square
moment; non-increasing parent assignments would invalidate the sampling
schedule; additional crossings through ordinary private interiors would
invalidate their domain/witness decomposition. None is implicitly admitted.

The [producer](../../frontier/cover-geometry/global_two_parent_forward_kernels.py)
and [data](../../frontier/cover-geometry/global_two_parent_forward_kernels.json)
check167 named conditions. They retain the Report612151-row and full-prime-tail
budget through its checked certificate, check the homogeneous head constants,
the exact same-source budget identity, the lost early unit gain and the
positive final reserve. Both direct input producer fingerprints are checked.
No full head scan or new moment optimization is repeated. GN4, GN8 and the
reverse-sampling-order argument supply the conditional-law obligations
beyond this arithmetic certificate.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/global_two_parent_forward_kernels.py

[Report616](616-three-parent-entries-with-two-outside-parents-preserve-a-common-survivor.md)
uses the actual single-head and head-pair marginal bounds to admit owners
with three fixed smaller parents, at least two outside the head. All
existing two-parent owners and global root crossings remain permitted.

## A capped root admits a different three-parent extension

[Report618](618-a-capped-root-admits-three-two-head-one-outside-children.md)
changes the first root's normalized row and jointly pays three children
with two head parents and that same outside root. It retains all later
two-parent crossings and the present head class, with extendible head
Haar mass greater than1/220000. These triples differ from Report616's
class with at least two outside parents.
