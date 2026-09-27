# A binary support survives1608 triple exclusions

There is a binary auxiliary upward support U satisfying all positive
theoretical pair exclusions, the432 old triple exclusions and all1176
symmetry images of the weighted seeds in
[report499](499-weighted-mixed-budgets-exclude-old-zero-triples.md), with

    eta(U)=0.01615225568961777...
          >m7=7235955529/450000000000,
    eta(U)-m7=0.00007235451406221579... .                  (B1)

Thus integrality does not make this specified1608-triple system sufficient
to force the auxiliary mass below m7. This is a counterexample to that
system's sufficiency, not an actual-source realization or an original
covering family. Additional weighted or multi-point relations are not
included in the obstruction claim. All calculations below are exact
integer/rational checks with ordinary proofs; no new Lean verification
or solver optimality is claimed.

## Exact support and its comparison measure

Use the six-anchor chart and reference(2,7,3,4) of
[report495](495-genuine-triples-and-order-leave-a-fractional-obstruction.md):
split old coordinates3,5,7, common coordinates11,13,17,19, and new
coordinates23,29. The common bad-fibre threshold is1/3696. Each signed
split coordinate represents +f=(f,1), -f=(1,f), or0=(1,1); signed3 is
nonzero. For boxes A_v,B_v let Q_v=|A_v union B_v|.

Set z_v=0 on Q<=19, z_v=1 on all Q>=39, and retain15799 of the20076
middle profiles20<=Q<=38. The certificate records the sorted4277-index
complement. These are Boolean values, with no fractional memberships.
It includes all middle points for purposes of the order check, including
any point of zero comparison mass.

The consumer reconstructs the profile order and exact eta weights from
the literal675-cell anchor complement and geometric valuation shells.
The complement has221 cells. The later comparison caps are
(3/2,5/3,3/2,2,9/5) at(7,11,13,17,19). All infinite overflow is
accounted for exactly as

    eta(Q>=39)=221/675-eta(Q<=19)-eta(20<=Q<=38).

Adding the retained middle weights gives the exact value

    53710335286108758012877270605896441892043825795755225952064673697878899753110088905041765805971256705683577
    /3325252913166319803873999980149547178129988724985893078987901476417226030410061707589932020604610443115234375.

The exact positive difference from m7 is retained in the adjacent JSON.
No floating-point rounding or rounded integer objective supplies B1.
The source inputs are pinned, including m7 and the joint-density cap27/2;
eta is still an auxiliary comparison measure, not the actual completed
source nu.

Every immediate upward arrow fixes3/5 and enlarges one later coordinate.
The16858 middle-to-middle arrows and88764 middle-to-overflow arrows obey
z_parent<=z_child. Arrows from Q<=19 obey the order because z=0 there;
arrows within overflow obey it because z=1 there. This proves the full
declared upward order.

## A compressed exact proof covers every pair

For any two profiles x,y, the literal selector inventory is

    N_xy=Q_x+Q_y-I_xy*(C_xy-2),                             (B2)

where I_xy is the product of the four common-coordinate minima, and
C_xy is the sum of the two opposite-centre split-box intersection sizes.
The Boolean expansion in report495 proves this identity. C_xy>=2, and
the common unit label gives N_xy>=max(Q_x,Q_y)+1.

At capacities(q,r,N), a zero witness consists of nonnegative axis vectors
t,u with individual bounds min(q,22),min(r,22) and min(q,28),min(r,28),
shared sums at most N, and residuals c_i=(22-t_i)(28-u_i) satisfying
c1<=q,c2<=r,c1+c2<=N. This gives zero for the old pair survivor
relaxation. Feasibility persists when q,r,N increase.

The consumer covers all190 unordered load-class pairs20<=q<=r<=38.
For144 classes, N>=r+1 already admits an explicit rational zero witness.
For the other46 it groups the actual support by load and split signature.
Within a group the common-factor product P is fixed. Because
I_xy<=min(P_x,P_y), B2 implies

    N_xy>=q+r-min(P_x,P_y)*(C_xy-2).                       (B3)

Of335592 relevant group pairs, B3 certifies335186. For the remaining406,
the consumer computes the exact maximum I_xy over both finite common-box
sets. Only78 different pairs of such sets occur, requiring2175 integer
intersection evaluations. These maxima and B2 certify the remaining
pairs. An upper bound for I gives a lower bound for N because C_xy-2>=0.

All members of each group are covered; representatives are not sampled.
The groups partition the actual15799-point support, accounting for all
124796301 unordered distinct middle pairs. The certified capacity
thresholds need not be exact pair minima: every threshold has a directly
verified zero witness, and every actual capacity is at least its threshold.

Any pair involving overflow and another Q>=20 profile dominates
(20,39,40), where t=(20,20),u=(18,22),c=(20,12) is feasible. Pairs
incident to z=0 already satisfy a support exclusion. Therefore U satisfies
every positive theoretical pair exclusion, including all clique
consequences valid for binary pair-admissible supports.

## The complete declared triple family

The consumer recomputes exact vertex certificates for the nine old seeds
and the24 weighted seeds from report499. It applies simultaneous
permutations of the three split coordinates, permutations of the four
common coordinates, and global A/B exchange. Images with signed3=0 are
excluded from this chart. Point weights stay in their ordered point slots.

The nine old seeds yield432 distinct edges. The24 weighted seeds have
6912 transformations, of which4896 are eligible and2016 have signed3=0.
Literal membership-pattern checks give1176 distinct new edges, disjoint
from the old432. Every resulting edge e obeys

    sum_(v in e) z_v<=2.                                  (B4)

These genuine local constraints do not exhaust all valid three-point
constraints. Including all overflow in U does not assert that every
other triple touching overflow has zero bound.

The pinned half-integral witness from report495 also satisfies all1176
new edges. Its doubled-cover sums are2,3,4,5 on456,528,180,12 edges,
respectively. Thus report495's fractional lower value survives this
extension. The integer upper bound from
[report496](496-integer-triangle-cuts-give-a-strict-relaxation-gap.md)
still applies, so the same strict fractional-versus-binary gap lower
bound remains valid for the extended system. Neither optimum is claimed.

## Consequence and reproduction

The existing bridge would give

    Haar(original survivors)>=(m7-U_bound)/49896>0

from a certified auxiliary upper bound U_bound<m7. B1 rules out deriving
such an upper bound solely from this pair/order/1608-triple system,
even with exact binary optimization. Additional joint-label information,
phase compatibility and other genuine edges remain available as stronger
inputs. The actual-source gap, other chart configurations and unrestricted
Erdos#7 remain unresolved.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_binary_support_barrier.py

The standard-library consumer checks its adjacent result on a default
run. Its inputs are the support complement, pinned source data and
existing seed certificates; no optimizer, proposed conflict graph,
NumPy package or transient search output is needed.
