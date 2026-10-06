[Index](../../../marked_head_profile.md) · [Paid completion and shared outputs](872-matched-prefix-completion-and-paid-banks.md) · [Actual-source sampling](870-matroid-prefix-rounding-and-divisor-hall-repair.md)

# Clean source colors and conflicts between shared outputs

Keep the conditional actual-source branch of Reports870--872: a globally
count-then-modulus-sum minimal odd distinct cover, ternary height two,
q=113 of height one, and common period 9qW with W coprime to 3q. The
cofactor prime pool has at most 27 members. The q-bearing originals
have labels q times 3^a times m, with a in {0,1,2}; the map from an
original to (a,m) is injective. Their actual divisor banks satisfy
P2 contained in P1 contained in P0. All 113 literal q-colors cover the
same exact residual E0 left by the q-free originals.

This gives a supply of colors without the smallest divisor obstructions
and a shared-output plan around each common actual point. A conflict
graph expresses the remaining global assignment problem exactly. None
of these results proves that a single assignment covers the entire E0.

## At least 29 complete colors contain only composite anchors

There are at most 28 low anchors: one and the 27 available primes.
At most one original uses each pair (row,anchor). Consequently at most
84 originals have a unit or prime anchor, and they occupy at most 84
q-colors. At least 29 complete colors contain no such original.

Call these colors clean. Every original in a clean color has a positive
composite cofactor. The conclusion is simultaneous over all five safe
old words, since exclusion was applied to the whole original color,
not to separate word-dependent lists. It supplies neither a bound on
the size of a clean color nor distinct anchors within that color.

Choose five different clean colors, one for each safe old word, and
take their actual compatible packets on that word. This mixed family
still covers E0: at a point, the color assigned to its old word is a
complete source color. At any one anchor there are at most three
selected packets. Indeed, an original has only one q-color, so cannot
be selected on two different old words; the three row slots then bound
the number of originals with that anchor.

## The remaining single-anchor tests are explicit

Suppose an anchor m lies in P2, so all of its divisors lie in all three
banks. Put t=tau(m) and let k be its selected packet count. Restrict
attention to these k packets. Their generated-downset tests in
Report872 MC4 reduce to

$$
2k\le t,\qquad 4k\le2t,\qquad 7k\le3t.
\tag{CC1}
$$

With k at most three and t at least three, their failure is exactly

$$
\boxed{(k=2\ \text{and}\ t\le4)
\quad\text{or}\quad(k=3\ \text{and}\ t\le6).}
\tag{CC2}
$$

These are necessary local tests for the full packet family; packets
at proper-divisor anchors can add further demand in that same downset.
Thus composite anchors alone do not settle even the single-anchor
tests. If m is outside P2, its smaller-bank divisor stock must be
counted separately; CC1 cannot be substituted for it. Passing every
single-anchor test also does not prove the tests for larger downsets
or nested chains.

There is no deduction of five conflict-free colors from only the
number 29 and the total available pair conflicts. Partition 29
vertices into groups of sizes 8,7,7,7 and make each group a clique.
There are 91 edges and no independent set of size five. This is an
untyped graph control, not an actual congruence-system construction.
It omits the old-word labels and exact E0 coverage. Its purpose is
only to rule out the stated inference from those two counts.

## A common actual point supplies a shared plan for its cluster

Fix an actual residual point (z,w). From any of the clean complete
colors choose an original containing that point, and retain its
compatible old-word packet at z. Every resulting anchor is composite,
and all literal cofactor phases satisfy alpha_p=w modulo m_p. The
same witness w supplies every divisor projection.

Choose B contained in P0 and containing all divisors of these anchors.
Every member of B is positive, odd and coprime to three. Give divisor d
child zero when d=1, child one when d is prime, and child two otherwise.
Give every output old word z and cofactor phase w modulo d. Each
composite anchor has the divisor one, a prime divisor, and its own
composite value. Its compatible neighborhood therefore sees all three
children. The shared CRT construction of Report872 produces one fixed
family of labels 27d covering the entire union of these packets, not
merely the witness point.

For B contained in P0, the labels fit the existing count and modulus-sum
budget. They replace all deleted q-bearing originals only if their
packet union covers E0. The construction assumes neither a matching
nor independent representatives. Different points can require different
w, z and phases for the same numerical divisor, so these local plans
cannot be united freely.

The same distinction appears in the weighted necessary bound. On any
one common-point cluster, with nonnegative packet weights w_p, the
maximum compatible weight for d equals the sum of weights of packets
whose anchors d divides. Summing over d gives

$$
\sum_{d\in B}C_w(d)=\sum_p w_p\tau(m_p)
\ge3\sum_p w_p.
\tag{CC3}
$$

For positive total packet weight, this strictly exceeds the factor-two
shared-tail bound. This
identity uses all divisors of each anchor in B. A potential obstruction
must mix incompatible source points or old words, or restrict the
available divisor bank further.

## An independent transversal expresses the shared assignment exactly

Fix a finite packet family whose union covers E0, and a finite divisor
bank B. Packet p has old word z_p, anchor m_p and literal phase alpha_p.
For each demand (p,c), c in {0,1,2}, make one part V_(p,c) containing
one candidate vertex for each d in B dividing m_p. Its output signature
is

$$
(d,z_p,c,\alpha_p\bmod d).
\tag{CC4}
$$

Join two vertices exactly when their divisors agree but their output
signatures differ. Vertices in the same part are nonadjacent. Copies
of one identical signature in different parts are also nonadjacent:
they may share the same numerical output.

An independent transversal chooses one candidate from each part and
has no conflicting pair. The chosen vertices with the same divisor
then all have the same signature and define one output. Conversely,
any shared assignment satisfying Report872 MC11 supplies a candidate
for every part, and these choices form an independent transversal.
Thus the graph encodes that sufficient whole-child certificate
exactly. It does not encode every possible cover of E0.

For d in B put

$$
N_d=\#\{p:d\mid m_p\},\qquad
H_d(z,\beta)=\#\{p:d\mid m_p,\ z_p=z,
\alpha_p\equiv\beta\pmod d\}.
$$

The degree of vertex (p,c,d) is exactly

$$
3N_d-H_d(z_p,\alpha_p\bmod d).
\tag{CC5}
$$

There are 3N_d candidate vertices with that divisor, of which precisely
H_d have its own signature, including the vertex itself. Between a
fixed vertex and any other part there is at most one neighbor, since
each part has at most one candidate with that divisor. The graph
therefore has local degree at most one. It generally has triangles:
the three child choices of any one packet at the same divisor form
one. Bipartite conflict-graph theorems cannot be used without another
representation.

The part size is t_p=|Div(m_p) intersect B|. For a nonempty part its
average full-graph degree is

$$
\frac1{t_p}\sum_{d\mid m_p,\ d\in B}
\bigl(3N_d-H_d(z_p,\alpha_p\bmod d)\bigr).
\tag{CC6}
$$

The subtraction retains genuine phase sharing. Replacing it by a
count of anchors alone discards part of the joint-source structure.

For five distinct word-selected colors, the three-packet-per-anchor
bound gives N_d at most three times the number of m in P0 divisible
by d, hence at most 3 tau(W/d). For one complete color v, writing
n_(a,v)(d) for its row-a originals whose cofactors are divisible by d,
the sharper source identity uses the actual selected old-word counts
and gives

$$
N_d\le5n_{0,v}(d)+3n_{1,v}(d)+n_{2,v}(d).
\tag{CC7}
$$

These are upper bounds from the declared source, not bounds on CC6
strong enough to settle a transversal. In particular a bound on the
number of prime factors of one anchor does not bound how many other
packets contain the same small divisor.

## Published independent-transversal results give a conditional route

Glock and Sudakov, *An average degree condition for independent
transversals*, Journal of Combinatorial Theory B 154 (2022), 370--391,
[DOI 10.1016/j.jctb.2022.01.004](https://doi.org/10.1016/j.jctb.2022.01.004),
[arXiv:2003.01683v2](https://arxiv.org/abs/2003.01683v2), Theorem 1.2
on printed page two, states: for every epsilon>0 there is gamma>0
such that a graph partitioned into parts has an independent transversal
if every part has size at least (1+epsilon)D, its average full-graph
degree is at most D, and the graph's local degree is at most gamma D.
The original theorem was read directly.

For the graph above, it therefore suffices to find one common D>0
such that

$$
1\le\gamma D,\qquad t_p\ge(1+\varepsilon)D,\qquad
\sum_{d\mid m_p,\ d\in B}
\bigl(3N_d-H_d(z_p,\alpha_p\bmod d)\bigr)\le D t_p
\tag{CC8}
$$

for every packet p. The first condition uses the proved local-degree
upper bound one. The missing arithmetic input is a packet family
still covering E0 and simultaneous bounds CC8, possibly after a
justified restriction of candidates. With individually restricted
lists the conflict counts must be recomputed for those lists; the
unchanged CC5 formula assumes each eligible divisor remains available
for all three children.

This is a published sufficient criterion, not a theorem that the
actual source meets it. Even the older maximum-degree condition
|V_i| at least 2 Delta can miss easy shared assignments. With at least
two packets, a common divisor bank, and an anchor having at most four
divisors, no deletion of divisors from that common bank can satisfy
this condition: keeping the unit divisor one gives Delta at least
twice the packet count, while deleting it leaves that part at most three candidates
and every remaining candidate still has its two other-child neighbors.
An empty part also fails. This argument concerns common-bank deletions,
not independent pruning of each part's candidate list. The common-point
construction above can nevertheless succeed in such cases.

## A common probability table gives another sufficient certificate

Fix nonempty eligible lists D_p contained in the available divisor bank
intersect Div(m_p), and set B to the union of these lists. Thus every
d in B appears in a list. For each such d let

$$
S_d=\{(z_p,\alpha_p\bmod d):d\in D_p\},\qquad s_d=|S_d|.
$$

Choose one value X_d in S_d times {0,1,2} for each divisor, independently
across divisors. These are auxiliary choices of replacement outputs;
no independence of the original phases, colors or source points is
assumed. Every packet uses the same table for a given divisor.

First take the uniform table. The bad event E_(p,c) says that none of
the packet's eligible divisors has selected its signature and child c.
Its exact probability and an exponential upper bound are

$$
q_p=\prod_{d\in D_p}\left(1-\frac1{3s_d}\right)
\le\exp(-w_p),\qquad
w_p=\sum_{d\in D_p}\frac1{3s_d}.
\tag{CC9}
$$

A direct sufficient condition is the union bound 3 sum_p q_p<1.
Equivalently, after clearing the common positive denominator,

$$
\sum_{(p,c)}\prod_{d\in B}
\left(3s_d-\mathbf1_{\{d\in D_p\}}\right)
<\prod_{d\in B}3s_d.
\tag{CC10}
$$

Each product on the left counts the complete assignments that miss
one specified demand. If their sum is smaller than the number of all
assignments, some common assignment misses no demand and supplies
MC11. This count does not assume independence between bad events.

For a local-lemma condition, join distinct packets when their lists
intersect and let Delta_P be the maximum degree of that graph. The
ordinary dependency degree among the three demands per packet is at
most 3 Delta_P+2. The symmetric Lovasz local lemma therefore applies
if e times 3(Delta_P+1) times max_p q_p is at most one. In particular,
it suffices that

$$
\min_p w_p\ge1+\log\bigl(3(\Delta_P+1)\bigr).
\tag{CC11}
$$

This reuses Bollobas--Pritchard--Rothvoss--Scott,
[arXiv:1009.6144v3](https://arxiv.org/abs/1009.6144v3), Lemma 8, already
used in Report869. If every list contains the unit divisor, the ordinary
packet dependency graph is complete. Then the direct union bound is
stronger than this symmetric condition; a local benefit needs genuine
sparsity or the more precise conflict structure below.

## Compatible shared signatures need not be lopsided neighbors

For two demands e and f, join them if some divisor in both lists has
different desired signatures, including the child. This can be a
strict subgraph of ordinary variable intersection.

To verify the applicable dependency notion, suppose the two desired
signatures agree on every common variable. Let assignments u,v differ
only on those common variables, with u missing e and v missing f.
If u served f, its serving divisor could not lie in the intersection:
there it would also serve e. Outside the intersection its value is
unchanged in v, contradicting that v misses f. Interchanging e,f
gives the other direction. Thus both u and v miss both demands.
This excludes precisely the adverse pair of assignments in the
variable-based lopsidependency definition.

Reuse Moser--Tardos, *A constructive proof of the general Lovasz Local
Lemma*, Journal of the ACM 57(2) (2010),
[DOI 10.1145/1667053.1667060](https://doi.org/10.1145/1667053.1667060),
[arXiv:0903.0544v3](https://arxiv.org/abs/0903.0544v3), Section 6:
the definition is on printed page nine and Theorem 6.1 on page ten.
These statements apply to general bad events determined by independent
variables, not only atomic events. The original source was read directly.
The desired-signature conflict graph is a valid supergraph of its
lopsidependency graph. Hence it suffices to find numbers x_e in (0,1)
such that, simultaneously,

$$
\Pr(E_e)\le x_e\prod_{f\in\Gamma_{\rm conflict}(e)}(1-x_f).
\tag{CC12}
$$

The published theorem gives a common assignment avoiding every bad
event. Its resampling algorithm has expected total resamplings at most
sum_e x_e/(1-x_e); this counts resamplings, not the cost of discovering
the original source, detecting events or producing suitable tables.

Biased tables are also allowed. If theta_d is one probability table on
S_d times {0,1,2}, shared by all packets, replace the event probability by

$$
\Pr(E_{p,c})=
\prod_{d\in D_p}
\left(1-\theta_d(z_p,\alpha_p\bmod d,c)\right).
\tag{CC13}
$$

Independent favorable tables chosen separately for different packets
cannot be combined. The remaining sufficient-condition supplier is a
single family of lists and tables on an actual packet cover of E0
satisfying CC10 or CC12. Neither has been supplied for the hypothetical
minimal cover. Failure of either test does not imply that no shared
repair exists: even one composite packet with exactly three divisors
has the explicit three-child assignment above while its uniform
symmetric local-lemma test fails.

## Verification and remaining obligation

The 84/29 source-slot count and the three-packet bound under five
distinct colors have exact finite Lean applications. CC2 and the
91-edge graph control also compile with default budgets and standard
axioms. Their arithmetic inputs are supplied by the stated actual
row uniqueness and prime-pool assumptions; no whole-cover conclusion
is inferred from the graph control.

The constructive common-point application is compiled through the
shared CRT consumer: a single witness, composite anchors, a bank
containing their divisors, and the coprimality of its output labels
give a cover of their entire packet union. The general weighted
identity CC3 is ordinary finite double counting. Exact Lean applications
also verify consistent candidate choice versus common signature
assignment, the neighbor formula and CC5, the common-bank arithmetic
obstruction, and the tagged divisor-inventory bound used above. They
use default budgets and standard axioms. The interpretation as an
independent transversal and the external graph theorem application
remain the ordinary reduction above; no new Lean proof of that
published theorem is claimed.

The finite product count and union-bound assignment implication in
CC10 also have exact Lean applications, including two packets with
overlapping five-candidate lists in a common six-variable alphabet.
The lopsided interface is checked separately: agreement on shared
desired values forbids the adverse assignment pair; a third possible
value on each coordinate gives the converse for a shared disagreement.
The three child values supply that third-value condition. These checks
do not formalize the external local lemma or assert its numerical
hypotheses for the actual source.

For actual point weights, Report870's existing fractional first-stage
solution already gives a positive margin in every corresponding
nonnegative weighted covering inequality. A new positive-weight
obstruction to that same fractional problem cannot bridge the
integer gap. Packetwise whole-tail obligations are stronger and
must not silently be identified with those actual point inequalities.

The remaining target is one simultaneous, paid, literal assignment
covering the exact E0. Local compatible plans, tests on one anchor,
and independent favorable choices of colors do not supply it.
Neither this conditional branch nor unrestricted Erdős #7 is settled.
