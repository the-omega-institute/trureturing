# Normalized kernels close increasing two-parent networks

Keep the head-only restrictions of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md).
The two levels of shared pair interfaces in
[Report607](607-two-level-triangle-interfaces-preserve-a-common-survivor.md)
may be replaced by an arbitrary finite increasing two-parent network
behind each primary entry. Each later node chooses two fixed earlier
parents, at least one outside the head. The parents need not already
share an edge: connections between earlier branches and pairs of
generated outside parents are allowed. The proportion of complete
head configurations with an avoiding extension is greater than
1/200000, uniformly over all original finite heights and globally fixed
phases. The admitted class has no bound on co-occurrence treewidth.

The proof does not iterate Report607's scalar amplification at every
separator. It starts one normalized sequential law from the primary
component's three initial coordinates and generates the whole later
network in increasing prime order. Every generated coordinate has a
conditional Haar-density bound of six. Only the two actual parents of
a local original enter its second moment. The whole network is then
charged once through its primary entry on the head-pair boundary.

This is an ordinary mathematical proof with exact rational certificates.
It does not add Lean verification or settle unrestricted Erdős #7.

## Complete family and increasing two-parent scope

Let P be the ten smallest primes occurring in the finite family. First
use the reference head P={3,5,7,11,13,17,19,23,29,31}, with first seven
coordinates P0 and last three P1. Pure head originals and every head
original touching P1 are unrestricted. A mixed original on P0 must have
some exponent at least three, exponents at most one at3 and5, or at
least five prime divisors. All numerical original moduli are distinct,
and each has one arbitrary globally fixed residue.

An exterior primary component has the following complete decomposition.

* A primary outside prime q>=37 chooses two distinct head parents p,r,
  with q>max(p,r). Its primary triangle originals are any subset of

      p^i r^j q^e, i,j>=0, i+j>0, e>=1.

* Further globally distinct outside primes v_1<...<v_k, all greater
  than q, form any finite increasing sequence. Each node v chooses
  two distinct fixed parents a_v,b_v from

      {p,r,q} union {earlier generated nodes of this component}.

  At least one parent is outside the head, so the later pair(p,r)
  is forbidden. The node v exceeds both parents and owns any subset
  of the actual triangle originals

      a_v^i b_v^j v^e, i,j>=0, i+j>0, e>=1.

* At the primary q and at every generated node v, an ordinary private
  block tree is allowed, including the pure powers of that entry.
  Its interior is disjoint from all network entries and all other
  ordinary interiors, away from its declared attachment root.

The parent pair is fixed for each node but may differ between nodes.
Parents need not already be adjacent. They may lie in formerly
separate branches, and both may be generated outside nodes. Arbitrarily
many later nodes may use the same parent pair. There is no tree or
existing-edge requirement on these parent choices.

Different primary components share only head coordinates. Their
outside entries and ordinary interiors are disjoint, and there are no
cross-component originals. Every original is assigned once to the
head, a primary triangle, one later-node triangle or an ordinary
private block. Within a mixed triangle original the owner is its
unique largest introduced prime, with a positive exponent. This keeps
the complete original exponent vector, numerical-label identity and
fixed residue; crossing parent choices cannot create a second owner.

Ordinary Type I attachments directly to one head coordinate and separate
ordinary components remain as in Report601. The ordinary nontrivial
blocks are those of Report599: at most twelve vertices, simple cycles,
or oriented blocks with k>=4 children and smallest child at least
k(k+3)+3. Their depths and finite numbers are unrestricted; their own
edges need not follow increasing prime order. The increasing condition
applies to the two-parent network entries.

The number of nodes, network depth, width and all original heights
are arbitrary finite quantities, with no uniform upper bound. This
is a specified class of actual original families, not an assertion
about unrestricted supports or arbitrary prime assignments.

## Actual ordinary domains and one whole-network backward step

Resolve all original exponents on the full finite coordinate X_v, with
normalized counting measure H_v. Let V_v^0 be the actual set of words
extending through v's ordinary private tree, including its pure-v
originals but excluding primary or later-node triangle originals.
The existing actual-domain induction gives

    H_v(V_v^0)>=1-2/(v-1).                       (RF1)

Fix one primary component with initial coordinates(p,r,q). Define

    B_down subset X_p times X_r times X_q

as the triples with no avoiding extension through ALL further network
nodes and their ordinary private trees. This relation does not impose
p/r head legality, q's ordinary domain, or the primary triangle
originals. These are paid separately by the head source, the actual
primary complement and the primary load.

Let B_primary subset X_p times X_r be the head pairs with no extension
through the entire primary component, excluding head-only originals.
Select N<q-3 complete nonunit primary parent labels, retaining every
actual q-height in each selected tower. At x=(x_p,x_r), let R_x be
their actual complement inside V_q^0. Then

    H_q(R_x)>=(q-3-N)/(q-1)>0.

On the SAME full three-coordinate space there is the pointwise bound

    1_(B_primary)(x)1_(R_x)(t)
      <=sum_(unselected actual d q^e)
          1_(its parent cylinder)(x)1_(its q-cylinder)(t)
        +1_(B_down)(x_p,x_r,t).

Indeed, if the left side is one and no unselected primary original
holds, t lies in its ordinary domain and avoids every primary original.
If the triple were also outside B_down, its full network extension
and q's ordinary witness would produce an extension of the primary
component, a contradiction. Integrating against H_p times H_r times H_q
and summing all positive q-heights therefore gives

    H_(p,r)(B_primary)
      <=T(S)/(q-3-N)
        +(q-1)/(q-3-N)H_(p,r,q)(B_down).         (RF2)

The primary amplification in RF2 is paid exactly once for the whole
later network. For a primary whose two parents belong to P0, use
Report601's minimizing reference parent labels(3,5); otherwise use
(3,23). Write

    F_E(q)=F_(3,5)(q), F_L(q)=F_(3,23)(q),
    A_t(q)=(q-1)/(q-3-N_t(q)), t in{E,L}.         (RF3)

The existing complete-label tails and original selected-pattern
comparison bound the first term of RF2 by F_t(q). Also A_t(q)<=q-1.

## One normalized law throughout the whole later network

Start all three initial coordinates with H_p times H_r times H_q.
This is precisely the auxiliary Haar law required by RF2. It is not
the law of the primary q-word after conditioning on R_x and not the
distribution of a finally selected witness. Dependence of R_x on both
head words remains on the lower side of the pointwise bound; deleting
R_x on the upper side is an inequality, not an independence claim.

Process every further network node in increasing prime order. Both
fixed parents of every node have already been introduced. Original
phases and the same full initial coordinates are retained throughout
this single construction.

At a node v choose a set of N_v nonunit labels on its two parents. Given
the entire earlier history, let R_v be the complement of all these
actual selected parent towers inside V_v^0. Each selected parent label
has at most one original at every positive v-height. Consequently

    H_v(R_v)>=1-(N_v+2)/(v-1)
                =D_v/(v-1), D_v=v-3-N_v>0.      (RF4)

This accounts for BOTH the ordinary private domain and the selected
towers. R_v depends on the same full parent words as every remaining
original. Define the actual normalized base law

    nu_v=H_v(.|R_v).

Let F_v be the union of the remaining actual v-triangle cylinders in
that fibre and alpha_v=nu_v(F_v). On nu_v apply the existing capped
kernel with threshold0<delta_v<=1/2: if alpha_v<=delta_v, condition on
F_v's complement; otherwise use relative density

    (alpha_v-delta_v)/(alpha_v(1-delta_v)) on F_v,
    1/(1-delta_v) outside F_v.                   (RF5)

Every row is normalized, including alpha_v=1, and its density relative
to nu_v is at most1/(1-delta_v). Thus its density relative to ORIGINAL
coordinate Haar is at most

    (v-1)/[(1-delta_v)D_v].                     (RF6)

The choices below keep RF6 at most6 at every complete earlier history,
including the same-source initial triple. RF4 holds even for histories
to which the final law assigns zero mass. The kernels are not
conditioned on simultaneous survival. They define one actual law on
all generated coordinates, preserve every complete earlier marginal,
and keep the initial triple Haar law unchanged. All sampled v-words
lie in V_v^0 and avoid selected towers. Remaining triangle violations
alone need payment.

For a violation event E_v at node v,

    Pr(E_v)=E[(alpha_v-delta_v)_+]/(1-delta_v)
      <=E[alpha_v^2]/[4delta_v(1-delta_v)].       (RF7)

This uses(z-delta)_+<=z^2/(4delta), not independence.

The probability of E_v is unchanged by every later normalized kernel.
If the initial triple belongs to B_down, every generated assignment
must violate some remaining triangle original. Otherwise all triangle
constraints hold in that ONE assignment, and each v-word has an
ordinary private witness. The disjoint ordinary interiors then glue
to give the forbidden full extension. Thus one union bound under the
single whole-network law gives

    H_(p,r,q)(B_down)<=sum_(v in this network)Pr(E_v).
                                                       (RF8)

There is no decomposition into independently estimated child subtrees.
Connections between earlier branches are actual later-node triangle
originals and are checked in the same assignment before witness gluing.

The method is the local conditional-cap and preserved-prefix method
of [Chapter07](../../problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md),
DG1--DG5, after the additional selected-tower deletion. Its
selected-coordinate probability passage already has the reusable
Lean declaration `SequentialKernelCylinder.selected_cylinder_bound`;
this report does not create another wrapper or claim that the new
arithmetic constants are thereby Lean verified.

## Only actual parent coordinates enter the tail moment

For any queried earlier generated coordinates, remove the latest one
first using RF6 and the tower law; unqueried coordinates integrate out
without a factor. Hence an intersection of cylinders on two generated
parents a,b has probability at most

    (6/a^i)(6/b^j) if i,j>0,                    (RF9)

with a factor1 for a zero exponent. A queried initial
coordinate instead contributes its Haar factor a^(-i). The initial
triple is independent Haar before generation; generated coordinates
need not be independent of it or of each other. This argument uses
conditional bounds at EVERY earlier history, not merely marginal caps.

A node is in direct mode D exactly when both parents are initial.
Since the later pair(p,r) is forbidden, its parents are exactly(p,q)
or(r,q), coordinatewise at least(3,37). A direct node need not be the
first processed node. All preceding normalized kernels integrate to
one at every initial triple, so its two-parent marginal remains exact
product Haar and both caps are one.

A node is in deep mode I exactly when at least one parent is generated.
All generated nodes exceed q, so the larger parent is generated and
at least41. The smaller parent is either an initial Haar coordinate
at least3, or another generated coordinate at least41. In the latter
case

    6/a^i<=3^(-i), i>=1, a>=41.                 (RF10)

The generated-parent intersection bound RF9 follows by removing the
latest queried coordinate first, then the earlier queried one;
intervening unqueried normalized kernels integrate out. It is not a
product inferred from marginal caps. After ordering the two parents,
all deep-mode pair-cylinder intersections are consequently bounded by

    3^(-i) 6*41^(-j), j>0,
    3^(-i), j=0.                                (RF11)

This includes two generated outside parents and every allowed crossing
between earlier branches. The initial q has its Haar cap, while a
generated coordinate is never silently treated as initial Haar.

For reference pair(3,r) and second-coordinate cap c, define

    k_(r,c)((i,j),(i',j'))
       =3^(-max(i,i')) r^(-max(j,j'))
          *[1 if max(j,j')=0, otherwise c].

Use(r,c)=(37,1) in direct mode and(41,6) in deep mode. Let S_N contain
the unit and the N smallest nonunit3,r-smooth numerical labels, and
put

    M_(r,c)(N)=sum_(u notin S_N, w notin S_N)k_(r,c)(u,w).
                                                       (RF12)

All sums extend over nonnegative exponent pairs. Apply the same
selected exponent patterns to the actual ordered parents. The bound
is for the complete unselected-label second moment, with both labels
retained, not the square of their reciprocal sum.

Indeed the raw original Haar-fibre load from unselected labels is

    L_v=sum_(unselected actual d v^e)
                1_(actual parent cylinder of d v^e) v^(-e).

RF4 gives alpha_v<=(v-1)L_v/D_v. On expansion of L_v^2, incompatible
parent cylinders contribute zero; compatible ones contribute at most
the corresponding k coefficient by RF9--RF11. Two occurrences of the
same generated parent intersect in one cylinder at the maximum exponent,
so its density factor is6 once, not36. Summing the full two
positive v-exponent series gives

    E[L_v^2]<=M_(r,c)(N_v)/(v-1)^2,
    Pr(E_v)<=J_mode(v)
      :=M_(r,c)(N_v)/[4delta_v(1-delta_v)D_v^2]. (RF13)

All labels and their original phases were kept before the nonnegative
infinite majorants. Parent-cylinder phases may vary independently
between original v-heights; the intersection estimate permits this.

## Exact finite parameters and the entire infinite tail

For each prime41<=v<=967 and each mode, minimize RF13 over integers
N>=0 with6(v-3-N)>v-1. Put D=v-3-N and choose

    delta=min{1/2,1-(v-1)/(6D)}.                 (RF14)

This is the best threshold for that N subject to the cap-six condition.
It is positive; RF6 is at most6. These choices, the tail moments and
all resulting fractions are retained by the producer.

The infinite moments in RF12 have a finite exact expression. For
z=(i,j), define

    R_3(i)=3^(-i)(i+1+1/2),
    R_(r,c)(0)=1+c/(r-1),
    R_(r,c)(j)=c r^(-j)(j+1+1/(r-1)) for j>=1,
    M_all=3[1+c(3/(r-1)+2/(r-1)^2)].

Then

    M_(r,c)(N)=M_all
       -2 sum_(z in S_N)R_3(i)R_(r,c)(j)
       +sum_(z,w in S_N)k_(r,c)(z,w).            (RF15)

This is exactly the complement of the selected rows and columns.
The producer uses rational arithmetic and independently checks the
literal prefix by an exponent grid. The unit is included in S_N,
so the table indexed by N really excludes N nonunit labels.

For v>=971 no finite optimization is needed. Choose n>=22 so that

    2n^2+3<=v<=2(n+1)^2+1,

select the rectangle0<=i,j<n excluding the unit, and set N=n^2-1,
delta=1/2. Then D>=n^2+1 and D/(v-1)>=1/2, so the local Haar-density
cap is at most4, hence still at most6.

Both modes are dominated by reference(3,37) with second cap6. The
moment over two unselected labels is no larger than the sum over one
unselected label and one unrestricted label. The unselected label is
outside the rectangle, so the row sums in RF15 give

    M_rectangle
      <=(163/72)(n+2)3^(-n)
        +(37/2)(n+19/18)37^(-n)
      <=(21n+25)3^(-n).                         (RF16)

There are2n+1 odd integers in the interval. Because

    (4n+11)(n^2+1)-(2n+1)(2n^2+4n+3)
       =(n-2)(n-4)>=0,
    (4n+11)/(n^2+1)<=5/n,
    21n+25<=23n                                 (n>=22),

RF13 yields the complete weighted tail

    sum_(v>=971 prime) v J_mode(v)
      <=sum_(n>=22)115*3^(-n)
       =345/(2*3^22)=115/20920706406.            (RF17)

This estimate includes every larger prime and every possible descendant
depth. It uses a uniform geometric majorant, not extrapolation from the
finite table.

## Every generated node is charged once within its primary component

Combining RF2 and RF8, the additional fee at primary entry q is

    epsilon_q=A_t(q)
                 sum_(v generated in its component)J_mode(v).
                                                       (RF18)

Each node has exactly one primary component. Direct mode means that
both parents are initial; deep mode means that at least one parent
is generated. Ordinary private interiors have already been included
in V_v^0 and are not charged again. Connections between earlier branches
and two generated parents do not create additional primary charges.

For finite node prime v define

    A_1(v)=max_(t in{E,L}, prime37<=q<v)A_t(q),
    A_2(v)=max_(t in{E,L}, prime37<=q<w<v for some prime w)A_t(q),

with the empty maximum zero. A direct node satisfies q<v. A deep node
has an ACTUAL generated parent w with q<w<v, so A_2 applies even
without any tree-shaped ancestry. In particular A_2(41)=0 and
A_2(43)=36/5. Each actual node is in exactly one mode, giving

    sum_q epsilon_q
      <=sum_(41<=v<=967 prime)
                max{A_1(v)J_D(v),A_2(v)J_I(v)}
         +345/(2*3^22)=:W.                      (RF19)

For the tail we used only A_t(q)<=q-1<v, so RF17 is enough. Global
distinctness of generated primes permits summation over all primes
once. No independence of branches, no independent choice of phases,
and no simultaneous attainment of their worst fees is assumed.

The finite sum is approximately0.000010543305695913667. Adding the
entire analytic tail gives

    W approximately0.000010548802642229352,
    W<1/94500.                                  (RF20)

The exact rational sum, not the displayed decimal, proves RF20.
For scale, the first three weighted charges at41,43,47 are respectively
approximately1.906259e-6,4.668514e-6,2.639368e-6. The first is direct,
and the latter two are deep bounds. All151 finite rows are included.

## One head source, one continuation and actual witness gluing

Reuse Report601's actual early seven-coordinate submeasure and its
unchanged query gate. Each B_primary still depends only on its original
head pair(p,r), even after its entire later network is included.
Therefore early and late primary blockers can be paid on exactly the
same two boundaries as before.

Write epsilon_E,epsilon_L for the additional RF18 fees of early and
late primary entries. Early deletion has pair-density multiplier10/3,
and the query restriction and23,29,31 continuation turn it into final
head-Haar loss at most

    beta epsilon_E,
    beta=alpha(1-c)(10/3)=46191477/720966400<1.   (RF21)

Late additional loss is at most epsilon_L. The old primary fees
F_E,F_L and the unchanged Type I fee2^-17 were already included in
Report601's simple reserve31991/2048000000. Since
beta epsilon_E+epsilon_L<=epsilon_E+epsilon_L<=W, we obtain

    H_P(U_ext)>31991/2048000000-W
      >31991/2048000000-1/94500
       =1950299/387072000000>1/200000.           (RF22)

The early restricted source is positive before continuation: its
resulting head lower bound exceeds1/32000-beta W>0. The continuation
is run afresh on that one restricted source, not on independently
optimized marginals. All parent blocker estimates concern actual full
coordinates and globally fixed original phases.

For a head word surviving these deletions, each primary q admits a
q-word in V_q^0 that avoids all primary originals and whose initial
triple lies outside B_down. Choose its ONE full later-network witness.
Every crossing interface already agrees within that assignment.
The ordinary private interiors are disjoint from the network and from
one another, so their actual witnesses glue on those same entry words.
Different primary components have disjoint outside coordinates and
share only the fixed head values, with no cross-component originals;
their whole-component witnesses therefore glue simultaneously. The
ordinary Type I and separate components retain their existing
extensions. CRT gives an integer avoiding the entire original family.

If Q_off is the product of all outside resolving prime powers, the
full survivor density is greater than1/(200000 Q_off). The uniform
constant concerns extendible head configurations, not full density
independent of original heights.

For arbitrary ten ordered odd head primes, use the existing head-only
shifted digit injections and padded pullbacks from Reports601/607.
Every outside coordinate stays fixed, and each pullback retains its
full exponent/support vector and unique original label. Empty
pullbacks are padded with one fixed allowed cylinder at that same
vector. The network, all fixed parent assignments, all ordinary domains,
and every strict outside prime order remain unchanged. Padded-source
extensions map to target extensions with the same outside witnesses; averaging the
head injections transfers RF22. No query-law invariance is asserted.

## Actual admissible networks have unbounded co-occurrence treewidth

Fix primary parents3,5 and q=37. For any positive integer m, choose
seed primes u_1<...<u_m, all greater than q, with parents(3,q).
For every pair i<j, introduce a fresh prime v_(i,j) larger than all
seeds, with parents(u_i,u_j). Use the actual squarefree originals

    3*5*q,
    3*q*u_i for every i,
    u_i*u_j*v_(i,j) for every i<j,

with, for example, all residues zero. Include the remaining eight head
coordinates through their pure-prime originals so the ten-prime head
is present. Ordinary interiors can be empty. Every numerical modulus
is distinct and has its stated unique largest-prime owner.

The actual prime co-occurrence graph induced on the seeds is K_m:
each pair occurs together in its own actual three-prime original.
This induced subgraph has treewidth m-1, so the whole admissible
co-occurrence graph has treewidth at least m-1. The parent pair(u_i,u_j)
need not have been an edge before v_(i,j) is introduced. These are
actual examples within the theorem's hypotheses, not covering examples
or an unrestricted #7 claim. The general distinction between local
parent count and co-occurrence treewidth is not claimed as new.

## Remaining scope and reproducible certificate

The remaining gaps for unrestricted Erdős #7 include the head labels
still excluded by Report598, later nodes whose parents are both head
coordinates, multiple different parent-pair inventories at one node,
arbitrary cross-primary originals, and prime assignments not following
the increasing construction. A later pair(p,r) requires a larger
(3,5) or(3,23) tail than the direct fee used here. Multiple parent
pairs at one node change its square moment. Cross-primary originals
require a larger joint initial interface or a different accounting;
they cannot be checked by gluing the present component witnesses.

Arbitrary finite network depth, connections between earlier branches,
two generated parents, and unbounded co-occurrence treewidth are no
longer restrictions for the admitted class. Failure of a hypothesis
outside this class is not a conclusion that an actual covering exists.

The [producer](../../frontier/cover-geometry/recursive_pair_forward_kernels.py)
and [data](../../frontier/cover-geometry/recursive_pair_forward_kernels.json)
check3017 named conditions: both literal moment tables, all151 finite
node rows, the inherited304 primary amplification choices, the
uniform conditional density, whole prime tail, early-source conversion
and strict final reserve. It imports only Report601's checked arithmetic
certificate; no full head scan is repeated.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/recursive_pair_forward_kernels.py

The source construction, selected-coordinate argument, moment majorants
and witness gluing establish the ordinary mathematical quantifiers
beyond the arithmetic certificate. The general capped kernel and
sequential-cap method are existing ingredients; this result adds their
selected complete-tower tail and a uniform whole-network arithmetic
budget for this explicit original family.

[Report612](612-shared-head-pair-networks-join-multiple-root-entries.md)
joins arbitrarily many primary entries based on the same head pair into
one network and admits originals between their later branches. Starting
the forward law directly at that head pair removes the primary
amplification, while retaining every original root fee. Its extendible
head bound is1/90000. Networks based on different head pairs still have
disjoint outside coordinates, and the head restrictions remain.
