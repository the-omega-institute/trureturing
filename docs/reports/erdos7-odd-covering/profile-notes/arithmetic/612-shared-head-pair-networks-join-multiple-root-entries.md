# Shared-head-pair networks join multiple root entries

Keep the ten-prime head restrictions of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md).
For each fixed pair of head primes, arbitrarily many two-head-parent
entries can now belong to ONE increasing two-parent network. Later
nodes may use parents from different such entries. The proportion of
complete head configurations admitting an avoiding extension is greater
than1/90000, uniformly over all finite original heights and globally
fixed phases.

[Report610](610-normalized-kernels-close-increasing-two-parent-networks.md)
allowed arbitrary increasing two-parent networks behind a single primary
entry, but required different primary components to have disjoint outside
coordinates and no cross-component originals. Here the whole network
starts directly from its head pair. Root entries and nonroot entries are
sampled in one increasing order, and their violation events are paid
under that same normalized law. There is no primary backward amplification.
Different HEAD-PAIR networks still have disjoint outside coordinates.

This is an ordinary mathematical proof with exact rational certificates.
It adds no Lean verification and does not settle unrestricted Erdős #7.

## Complete original scope

First use the reference head

    P0={3,5,7,11,13,17,19}, P1={23,29,31}, P=P0 union P1.

These are the ten smallest primes occurring in the family. Pure head
originals and every head original touching P1 are unrestricted. A mixed
original on P0 must have some exponent at least three, exponents at most
one at3 and5, or at least five prime divisors, as in Report598. Every
actual numerical original modulus is distinct, with one arbitrary residue
fixed once for that original.

A network chooses two distinct head primes p,r. Its outside entries
form an arbitrary finite increasing sequence of distinct primes at least37.
Every entry v has two distinct FIXED parents among p,r and the earlier
outside entries of this SAME network. Both parents are smaller than v.
The entry owns any subset of actual mixed originals

    a_v^i b_v^j v^e, i,j>=0, i+j>0, e>=1.       (SN1)

An entry is a root exactly when its declared parents are(p,r). There
may be arbitrarily many roots. They may be interspersed with nonroot
entries in increasing prime order. A nonroot has at least one earlier
outside parent; consequently it is at least41. Its two parents may
come from different roots' subsequent networks and need not have been
adjacent. There is no tree, depth, width or co-occurrence treewidth bound.

At every entry v, attach an allowed Report599 ordinary private block
tree, including pure-v originals. Its interior is disjoint from all
network entries and from every other private interior, except for its
own attachment root. The blocks are those already admitted in Report601:
at most twelve vertices, simple cycles, or the permitted oriented blocks
with k>=4 children and smallest child at least k(k+3)+3. These ordinary
blocks retain their own hypotheses; their edges need not follow the
increasing network order.

Different networks share only head coordinates. Their outside entries
and ordinary interiors are disjoint, with no cross-network original.
Several networks with the same head pair can be treated as one network;
allowing later originals between their entries is precisely the new
permission. Ordinary Type I attachments to one head coordinate and
separate ordinary components remain unchanged from Report601.

Every original belongs exactly once to the head, one entry's mixed
inventory, or an ordinary block. In SN1 the entry v is the unique largest
introduced prime and has positive exponent. Its two declared parents
are fixed even when one exponent is zero. No numerical label, exponent,
residue or common interface is merged by the representation.

All original heights, numbers of entries and ordinary block depths are
arbitrary finite quantities. For ten other ordered odd head primes that
are the ten smallest in the family, the head-only transport below gives
the same result while leaving every outside coordinate unchanged.

## Actual ordinary domains and unchanged root choices

Resolve the entire original family on finite full coordinates X_v,
with normalized counting measure H_v. Let V_v^0 be the actual words
that extend through v's ordinary private block tree, including pure-v
originals and excluding its mixed entry inventory. The existing actual
domain induction gives

    H_v(V_v^0)>=1-2/(v-1).                      (SN2)

Given both complete parent words, select N_v nonunit parent exponent
patterns and delete ALL actual positive-v-height originals with those
patterns. Their complement R_v inside V_v^0 obeys

    H_v(R_v)>=D_v/(v-1), D_v=v-3-N_v>0.         (SN3)

This follows because every selected parent pattern has at most one
actual numerical original at each positive v-height, and the full
height sum is1/(v-1). All original phases remain fixed before this bound.

For roots, use reference parents(3,5) when p,r both lie in P0, and
(3,23) otherwise. At37<=q<=967 use exactly Report601's selected-label
counts and exponent patterns. All304 retained rows have D_q>=4. The
minimum for(3,5) is6. The only row with D_q=4 is reference(3,23),
q=41,N_q=34; no old root choice or fee is changed.

For q>=971 choose n>=22 with

    2n^2+3<=q<=2(n+1)^2+1,

and select the parent rectangle0<=i,j<n excluding the unit. Thus
N_q=n^2-1 and D_q>=n^2+1>=485. Write G_t(q) for the complete
reciprocal-tail bound divided by D_q under these actual choices,
t in{E,L}. For finite q these are Report601's minimizing fees; in the
tail the rectangle is the specific choice used to prove its series bound.
We do not assert that the rectangle minimizes each tail fee. The same
finite sums and complete rectangle tail therefore give

    sum_(q>=37 prime)G_E(q)<1/2600,
    sum_(q>=37 prime)G_L(q)<1/125000.           (SN4)

This is exactly the root budget already paid by Report601.

## One normalized law starts at the head pair

Fix one actual network. Start(p,r) with H_p times H_r. Process EVERY
outside entry in increasing order; no earlier entries are removed or
resampled. Both parents of every new entry have already been introduced.
At every complete earlier history define its row as follows.

For a root q use only

    nu_q=H_q(.|R_q).                           (SN5)

There is no capped deletion at a root. Its conditional density relative
to ORIGINAL q-Haar is bounded by

    A(q)=(q-1)/D_q.                            (SN6)

We do not claim A(q)<=6: the retained late root at41 has A(41)=10.
The root's selected complement depends only on its two full head words,
its fixed phases and its ordinary domain, even when other entries have
already been sampled. Its row is normalized at every such history.

For a nonroot v use the actual base law nu_v=H_v(.|R_v). Let F_v
be the union of its remaining unselected mixed originals in that fibre,
and alpha_v=nu_v(F_v). For0<delta_v<=1/2 use Report610's capped row:
condition on the complement when alpha_v<=delta_v; otherwise give
relative densities

    (alpha_v-delta_v)/(alpha_v(1-delta_v)) on F_v,
    1/(1-delta_v) outside F_v.                  (SN7)

Every row is normalized, including a fully forbidden remaining fibre.
The parameters below guarantee, relative to original Haar and conditional
on EVERY complete earlier history,

    density at v<=(v-1)/[(1-delta_v)D_v]<=6.     (SN8)

These rows define one joint law on the whole actual network. Every later
normalized row preserves every earlier marginal, in particular the initial
product-Haar head pair. There is no conditioning on whole-network survival.
All entry words already lie in their actual ordinary domains and avoid
their selected complete towers. Only unselected mixed violations remain.

Let E_v denote such a remaining violation at entry v. For a root,
put L_q equal to its remaining original Haar-fibre load. By SN3 and
SN5, the conditional violation probability is at most(q-1)L_q/D_q.
Averaging this over the preserved product-Haar head pair gives

    Pr(E_q)<=G_t(q).                            (SN9)

The selected-pattern comparison and the entire positive-q-height sum
are those of Report601. This bound holds even for a root appearing after
several nonroots: all preceding rows integrate to one at each head pair.

## Earlier outside parents have the required joint prefix bounds

For every positive exponent j, root q obeys

    A(q)/q^j <=(1/4)q^(1-j)
              <=(37/4)37^(-j),
    A(q)/q^j <=3^(-j).                         (SN10)

The first line uses D_q>=4 and q>=37. For the second, use
1/4<1/3 and q>=3. A nonroot w has

    6/w^j<=(37/4)37^(-j),
    6/w^j<=3^(-j),                             (SN11)

because w>=41,6<37/4 and6/41<1/3. These are conditional prefix bounds
at every complete past, not just statements about coordinate marginals.
A head coordinate has its exact Haar prefix bound.

Order the parents of a nonroot as a<b. Its larger parent is outside.
To bound a simultaneous cylinder on its parents, eliminate the latest
queried outside coordinate first using SN10 or SN11, then the earlier
one; intervening unqueried normalized rows integrate out. Finally any
head queries are integrated against the preserved initial product Haar.
Consequently, writing c=37/4, the joint parent-cylinder bound is

    3^(-i) c*37^(-j) for j>0,
    3^(-i) for j=0.                            (SN12)

This includes two roots, a root and a nonroot, or two nonroots from
arbitrary earlier branches. No product of merely marginal inequalities
is used. In a square expansion two cylinders on the same parent intersect
at the maximum exponent; there is ONE factor c for that coordinate,
not c squared. Incompatible phase cylinders contribute zero.

For reference exponent pairs z=(i,j),z'=(i',j'), define

    k(z,z')=3^(-max(i,i'))37^(-max(j,j'))
               *[1 if max(j,j')=0, otherwise c].

Let S_N contain the unit and the N smallest nonunit3,37-smooth labels,
and set

    M(N)=sum_(z notin S_N,z' notin S_N)k(z,z'). (SN13)

Use those same exponent patterns on the actual ordered parents. If
L_v is the remaining original Haar-fibre load at nonroot v, SN12 and
the full positive-v-height series give

    E[L_v^2]<=M(N_v)/(v-1)^2.

Since alpha_v<=(v-1)L_v/D_v and
(z-delta)_+<=z^2/(4delta), the capped row yields

    Pr(E_v)<=J(v)
       :=M(N_v)/[4delta_v(1-delta_v)D_v^2].     (SN14)

The root bounds SN9 and nonroot bounds SN14 concern the SAME joint law.
They do not use separately optimized witnesses or independent phases.

## Finite nonroot choices and the entire prime tail

The exact moment formula is Report610's complement formula with r=37,
c=37/4. Explicitly, write

    R_3(i)=3^(-i)(i+1+1/2),
    R_(37,c)(0)=1+c/36,
    R_(37,c)(j)=c*37^(-j)(j+1+1/36) for j>=1,
    M_all=3[1+c(3/36+2/36^2)].

Then

    M(N)=M_all-2 sum_(z in S_N)R_3(i)R_(37,c)(j)
                      +sum_(z,z' in S_N)k(z,z').        (SN15)

For every prime41<=v<=967 minimize SN14 over integers N>=0 with
6(v-3-N)>v-1, using

    D=v-3-N,
    delta=min{1/2,1-(v-1)/(6D)}.                (SN16)

All151 exact rational rows are retained. The finite sum is approximately
0.0000038595842226512676; this decimal is not a proof input.

For v>=971 choose the same interval index n>=22 as above, use the
rectangle0<=i,j<n excluding the unit, and set N=n^2-1,delta=1/2.
Then D>=n^2+1 and(v-1)/[(1-delta)D]<=4, so SN8 still holds.
The moment over two labels outside the rectangle is bounded by the
moment over one outside and one unrestricted label. Splitting the
outside label into i>=n or j>=n and summing the rows in SN15 gives

    M_rectangle
      <=(4627/1728)(n+2)3^(-n)
         +(1369/48)(n+19/18)37^(-n)
      <=(32n+37)3^(-n).                        (SN17)

For the second inequality, replace37^(-n) by3^(-n) and use

    4627/1728+1369/48=53911/1728<32,
    2(4627/1728)+(1369/48)(19/18)=15319/432<37.

There are2n+1 odd integers in the interval. As in Report610,

    (4n+11)(n^2+1)-(2n+1)(2n^2+4n+3)
       =(n-2)(n-4)>=0,
    (4n+11)/(n^2+1)<=5/n,
    32+37/n<34                                 (n>=22).

Using SN14 with delta=1/2, the complete weighted interval contribution
is at most170*3^(-n). Therefore

    sum_(v>=971 prime) v J(v)<=510/(2*3^22),
    sum_(v>=971 prime) J(v)<=510/(2*3^22*971).   (SN18)

No truncation of the prime set or extrapolation from finite rows occurs.
The complete nonroot budget is

    W=sum_(41<=v<=967 prime)J(v)+510/(2*3^22*971)
       approximately0.000003859592591261608
       <1/250000.                              (SN19)

Global distinctness of the original entry primes lets this one all-prime
sum pay every actual nonroot at most once, across all networks. Root
primes are also distinct. Using the full positive root series SN4 and
the full nonroot series SN19 is a simultaneous upper bound; it does not
assert that their separate maxima occur together.

## Whole-network blockers, one head source and actual gluing

For each head-pair network, let B_(p,r) be the actual pairs with no
avoiding extension through ALL its entries and their ordinary private
trees. Its definition excludes head-only originals. If a head pair is
in this blocker, every assignment generated by the single normalized
law must violate some unselected mixed original. Otherwise all mixed
constraints hold in that same assignment, and the disjoint ordinary
private witnesses glue at the chosen entry words to give an extension.

Since the initial pair has product Haar, one union bound gives

    H_(p,r)(B_(p,r))
       <=sum_(roots q of this network)G_t(q)
          +sum_(nonroots v of this network)J(v).        (SN20)

This is a blocker of the entire network; no separate cross-root witnesses
are chosen. Each network is early if both head coordinates are in P0,
and late otherwise. Its blocker depends only on those two coordinates,
regardless of the number or interleaving of its roots.

Let W_E,W_L be the sums of nonroot fees over early and late networks.
Then W_E+W_L<=W. The root sums in SN20 are exactly the early and late
budgets already paid in Report601. For the additional early blockers,
use the same P0 source and pair-density multiplier10/3. Its query
restriction and23,29,31 continuation convert their extra fee to final
head-Haar loss at most beta W_E, where

    beta=alpha(1-c_head)(10/3)=46191477/720966400<1.

Here c_head is Report601's continuation coefficient; it is distinct
from the parent cap c=37/4 above. The initial source is restricted
ONCE by the union of whole early-network blockers, and the continuation
is run afresh on that same source. The restricted early gate is positive
because its resulting head lower bound exceeds1/32000-beta W>0.
Late-network blockers are then paid on the resulting actual head
submeasure dominated by head Haar, with additional fee W_L.

The unchanged root and Type I fees already leave Report601's simple
reserve31991/2048000000. Thus

    H_P(U_ext)>31991/2048000000-beta W_E-W_L
      >=31991/2048000000-W
      >31991/2048000000-1/250000
       =23799/2048000000>1/90000.                (SN21)

For every head word in this actual set, each complete network has ONE
avoiding assignment. All cross-root interfaces agree within that
assignment. Different networks share only these fixed head words and
have disjoint outside coordinates with no further crossing originals;
their complete assignments glue. The ordinary Type I and separate
components retain their existing witnesses. CRT gives an integer
avoiding every original class. If Q_off is the product of all outside
resolving prime powers, the full survivor density is greater than
1/(90000 Q_off). The height-uniform1/90000 concerns extendible head words,
not a full density independent of outside heights.

For arbitrary ten ordered odd head primes, use the same head-only
shifted digit injections and padded pullbacks as Reports601/610.
Each transformed original retains its full exponent/support vector
and fixed parent assignment, with a one-to-one correspondence between
original and transformed numerical labels. Empty pullbacks are padded
at the same vector with one fixed allowed phase. Every outside
coordinate and its order remain unchanged. A padded-source network
extension maps to a target extension with the same outside witness.
Averaging the head injections transfers SN21. No invariance of the
query optimizer is asserted.

## An actual cross-root family outside Report610's decomposition

Use the fixed ten-prime head, the pair(3,5), and two roots37 and41.
Let43 have parents(37,41). Take the three actual squarefree originals

    3*5*37, 3*5*41, 37*41*43,

with all residues zero, and include the remaining eight head primes
through their pure-prime originals. Ordinary interiors may be empty.
These labels are distinct and obey SN1. They form an admitted network.

This example cannot be returned to Report610's class merely by renaming
its decomposition. The originals3*5*37 and3*5*41 force37 and41 to be
separate primary entries with head pair(3,5): neither is head-only,
a Type I attachment, an ordinary private interior with only one entry
interface, or a later node with an allowed pair containing an outside
parent. In particular, a later fixed parent pair cannot contain both3
and5 under Report610. The remaining original37*41*43 then connects the
two forced primary components. Placing it in an ordinary private block
would also identify a distinct primary entry with a private interior,
which that report excludes. The fixed ten-smallest-prime head cannot
be changed to absorb37 or41. Thus this is an actual enlargement of
the admitted family, not merely a new declared decomposition of an old
example. It is not a covering example.

## Remaining scope and reproducibility

The theorem still excludes Report598's missing head labels, multiple
different parent-pair inventories at one node, arbitrary crossings
between networks based on DIFFERENT head pairs, and non-increasing
network prime assignments. A larger joint head interface would change
the staged early/late accounting and is not supplied here. Allowing
several parent pairs for one owner would change the local square moment.
The result removes the one-primary-per-network restriction while retaining
these exact boundaries.

The [producer](../../frontier/cover-geometry/shared_head_pair_forward_kernels.py)
and [data](../../frontier/cover-geometry/shared_head_pair_forward_kernels.json)
check1903 named conditions, including all304 unchanged finite root
choices, all151 nonroot rows, literal moment enumeration, conditional
caps, the entire analytic tail and the positive staged reserve. The
producer imports Report610's existing exact moment and optimizer routines
and verifies both source certificate fingerprints; it repeats no full
head scan. The whole-law argument, exponent-uniform prefix comparisons,
rectangle series and actual witness gluing supply the ordinary
mathematical quantifiers beyond the arithmetic certificate.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/shared_head_pair_forward_kernels.py
