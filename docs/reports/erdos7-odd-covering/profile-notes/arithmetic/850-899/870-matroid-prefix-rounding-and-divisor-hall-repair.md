[Index](../../../marked_head_profile.md) · [Fractional source and coherent colors](869-fractional-fresh-prefix-transport-and-integral-gap.md) · [Earlier typed Hall repairs](865-whole-component-digit-stripping-and-shared-parent-repairs.md)

# Matroid prefix sampling with a divisor Hall repair

Keep the conditional whole-source branch of Report864: a globally
count-minimal, then modulus-sum-minimal odd distinct whole cover,
ternary height two, q=113 of height one, and Q=9qW with (W,3q)=1.
Let D be all q-bearing originals, F0 all q-free originals, and E0
the exact complement of F0 on 9W. Every original phase stays literal.
This branch is not asserted to exhaust unrestricted Erdős #7.

A published matroid rounding theorem supplies a legal partial
replacement with a controlled output count. A separate Hall condition
then repairs its entire uncovered source. The arithmetic hypothesis
that makes this repair possible is still missing. This construction
does not infer an integer cover from its expected covering load.

## The full deletion provides all 113 complete colors

Write the originals of D as q3^a m, a in {0,1,2}. Let P_a be the set
of cofactors occurring in row a, n_a=|P_a|, T=n_2, and N=|D|.
Numerical divisor closure gives

$$
P_2\subseteq P_1\subseteq P_0,\qquad
N=n_0+n_1+T,\qquad n_0\ge n_1\ge T\ge525.
\tag{MH1}
$$

P_0 is a finite divisibility downset, including one. Each of all 113
q-colors covers the same E0 after stripping q: for any point of E0
and any prescribed q-digit, CRT supplies a source point with those
coordinates. It misses every member of F0, so its actual owner lies
in D and has that q-digit. The three unit-cofactor colors may be used
here; exclusion from U served a different strict-count comparison.

For original i, let R_i be the safe words modulo nine compatible with
its ternary phase on which its literal cofactor class meets E0, and
write e_i=|R_i|. Original private integers give e_i>=1. The retained
pure guards give upper bounds 5,3,1 in rows zero, one, two.

Throughout, the full source is the lift of E0 to all higher ternary
digits and the same W-coordinate. One can work on any common finite
period containing every chosen prefix depth. Points are not sampled
from different laws, and the q-free exclusion is not replaced by an
arbitrary prescribed mask.

## A partition matroid controls the first-stage labels

For each i and each t modulo 27 with t modulo nine in R_i, use the
indexed candidate consisting of t modulo 27 and the literal cofactor
phase of i modulo m_i. Its numerical label is 27m_i. Keep separate
indices for identical geometric candidates; they belong to the same
numerical-label block. Put

$$
L_m=3\sum_{i:m_i=m}e_i\le27,\qquad
\Lambda=\sum_mL_m\le15n_0+9n_1+3T\le15N-18T.
\tag{MH2}
$$

There is at most one original of each row with any fixed cofactor.
Thus the three row contributions to L_m are at most 15,9,3.
Give every indexed candidate coordinate 1/27 and put

$$
r=\left\lceil\frac{\Lambda}{27}\right\rceil.
$$

These coordinates are in the independence polytope of the partition
matroid with at most one candidate per numerical-label block,
truncated to total rank r. Block sums are at most one and the total
sum is at most r. These two facts also bound every subset by the
rank min(r,number of its nonempty blocks).

Chekuri--Vondrák--Zenklusen, *Dependent Randomized Rounding for
Matroid Polytopes and Applications*,
[arXiv:0909.4348v2, Theorem 1.1](https://arxiv.org/abs/0909.4348v2),
applies to the independence polytope, not only the base polytope.
Randomized swap rounding preserves the marginals and outputs an
independent set; for any set A of candidate indices its all-zero
probability is at most the product of 1-x_j. Reuse this theorem;
no new proof of matroid rounding is claimed.

Every outcome is a family R of at most r APs with distinct labels
27m. At a full residual point, every complete color supplies a
containing candidate, so at least 113 indexed candidates contain it.
Consequently

$$
\Pr(x\notin\cup R)\le(26/27)^{113}<1/71.
\tag{MH3}
$$

The available repair budget b=N-r satisfies

$$
r\le n_0,\qquad
b\ge\left\lfloor\frac{12N+18T}{27}\right\rfloor
\ge2T\ge1050.
\tag{MH4}
$$

For example, any 0<theta<=1/max_m L_m can replace 1/27, with
r_theta=ceil(theta Lambda) and miss bound (1-theta)^113. That is a
budget tradeoff, not a proof that one of its choices covers E0.

## Repair whole packets using divisor labels

Fix one actual complete color v. For every i of that color and
compatible t modulo 81, let P_(i,t) be the full residual points
satisfying that ternary word and the literal cofactor phase of i.
These nonempty packets cover the whole residual. Activate a packet
exactly when some point in it is missed by R. A chosen representative
being covered does not certify that its packet is covered.

For any positive divisor d of m_i, the CRT class with ternary phase
t modulo 81 and cofactor phase projected from i modulo d contains
the whole packet. Its label is 81d; d=1 supplies the pure label 81.
Divisor closure puts all these d in P_0.

Hall's theorem gives distinct labels for all active packets precisely
when every divisibility downset J of P_0 satisfies

$$
\#\{\text{active packets with anchor }m_i\in J\}\le |J|.
\tag{MH5}
$$

Indeed the neighborhood of a packet is Div(m_i). The neighborhood
of any collection is a downset; that collection is contained in the
packets whose anchors lie in its neighborhood. Conversely a matching
sends every packet anchored in J to a distinct member of J. This is
a direct application of the existing Hall theorem to a real bipartite
matching problem, not an assertion that the covering system itself
is a graph or matroid. Only downsets generated by reference-color
anchors need checking.

All depth-three and depth-four labels are distinct across the two
stages, and fresh against F0. Their total modulus cost is at most

$$
27\sum_{m\in P_0}m+81\sum_{m\in P_0}m
=108\sum_{m\in P_0}m
<113\sum_{m\in P_0}m
\le\sum_{i\in D}q3^{a_i}m_i.
\tag{MH6}
$$

P_0 is nonempty. Thus at most N outputs already contradict the
secondary minimum; fewer than N contradict the primary minimum.

## Sibling packets activate together

The first-stage family has ternary depth exactly three, while E0
only uses the old two digits. For fixed original i and t modulo 27,
the three packets at t,t+27,t+54 modulo 81 have identical cofactor
sources and identical first-stage membership signatures. They either
all activate or all remain covered. No independence between these
three events is available.

Index the depth-three reference packets by p, with cofactor anchor
m_p, and let Y_p indicate that the packet has any missed point.
The total number of active depth-four packets is 3 sum_p Y_p, and
MH5 becomes exactly

$$
\sum_{p:m_p\in J}Y_p\le\left\lfloor\frac{|J|}{3}\right\rfloor.
\tag{MH7}
$$

This is a genuine restriction. For J={1}, every reference packet
anchored at one must already be covered in stage one. For a prime
anchor with only divisors 1,p, an activated parent alone exceeds its
two available labels. One cannot claim that generic positive divisor
stock repairs arbitrary activated packets.

## A sufficient condition on actual joint signatures

For parent packet p, let Sigma_p be the finite set of full membership
vectors in the indexed first-stage candidates actually realized
on that packet. For signature sigma let C(sigma) be the set of
containing indices and a(sigma)=|C(sigma)|>=113. Define

$$
u_p=\min\left\{1,\sum_{\sigma\in\Sigma_p}
(26/27)^{a(\sigma)}\right\},\qquad
\mu_v=\sum_p u_p,\qquad
\mu_{v,J}=\sum_{p:m_p\in J}u_p.
\tag{MH8}
$$

Points with the same full signature have the same miss event. The rounding theorem
and a union bound give E[Y_p]<=u_p. Equal service counts alone do
not identify two signatures.

Let J_v consist of the generated downsets whose potential parent
count exceeds floor(|J|/3); all remaining Hall inequalities hold
before sampling. Since b>0, the following strict-count criterion is
well defined:

$$
\boxed{
\frac{\mu_v}{\lceil b/3\rceil}
+\sum_{J\in\mathcal J_v}
\frac{\mu_{v,J}}{\lfloor |J|/3\rfloor+1}<1.
}
\tag{MH9}
$$

The first failure event is 3 sum_p Y_p>=b, equivalent to
sum_p Y_p>=ceil(b/3). A Hall failure at J is
sum_(m_p in J)Y_p>=floor(|J|/3)+1. Markov's inequality followed by
a union bound therefore leaves positive probability of at most b-1
repairs and every Hall condition simultaneously. Hall supplies fixed
APs for all active packets; all initially missed points lie in such
packets. The resulting full replacement has at most N-1 outputs.

For an equal-count comparison replace the first denominator by
floor(b/3)+1. Then at most b repairs suffice, and MH6 pays the strict
modulus-sum improvement. No independence of packet activations or
of Hall failures is assumed in either criterion.

Neither MH9 nor its equal-count version has been established for an
actual hypothetical minimal cover. At most 27 cofactor prime axes
does not give a small number of realized signatures. The squarefree
control in Report869 also shows that the independent-event criteria
can fail even when an explicit coherent-color plan exists. These
criteria are sufficient for the stated repair mechanism and are not
necessary for every possible improving exchange.

For a deterministic pretest, expand a complete color directly into
its depth-three packets. Hall gives a cover with at most n_0<N
outputs if, for every divisor downset J,

$$
3\sum_{i\in C_v,\ m_i\in J}e_i\le |J|.
\tag{MH10}
$$

For any fixed nonempty J, summing its left side over all 113 colors
gives at most 27|J| by MH2. Therefore at most 26 colors violate this
particular downset inequality. Blocking every color requires at least
five distinct downset obstructions. There is no proved upper bound
of four on the actual necessary obstructions.

## Semiprime repair packets have small Hall obstructions

Consider the restricted repair interface in which each active parent has a
distinct squarefree semiprime cofactor m=pq. Associate one graph edge pq to
each parent. For every nonempty edge subfamily F, the available divisor
labels are the unit, the incident prime vertices, and the distinct edge
labels. These categories are disjoint, so

$$
\left|\bigcup_{m\in F}\operatorname{Div}(m)\right|
=1+|V(F)|+|F|.
$$

Each parent contributes three children. Hence the entire family satisfies
Hall exactly when every nonempty subfamily satisfies

$$
2|F|\le |V(F)|+1.
\tag{MH11}
$$

This is equivalent to the graph being a matching together with at most
one component that is a path of two edges. For necessity, two distinct
adjacent-edge pairs sharing an edge give three edges on at most four
vertices, violating MH11. Two adjacent-edge pairs with disjoint edge sets
give four edges on at most six vertices, also violating it. Thus there is
at most one adjacent-edge pair. For sufficiency, each subfamily has either
2|F| or 2|F|-1 incident vertices.

The matching can also be written explicitly. Give an isolated edge pq
the labels p,q,pq. For the exceptional path p-q-r, give pq the labels
p,q,pq and qr the labels 1,r,qr. Assign these three distinct divisors to
the three children of each parent, using its literal projected phase.

Consequently every obstruction in this distinct-semiprime subinterface
has a witness of at most four parents. Two parents with the same
semiprime anchor already give a two-parent obstruction: four divisor
labels cannot serve six children. With at most 27 prime axes, MH11 bounds
a feasible distinct-semiprime family by 14 parents and 42 repairs. This
does not bound the higher-support or prime-power families.

Whole-parent feasibility is not a matroid, even in this subinterface.
Take

$$
A=\{35,77\},\qquad B=\{65,119,209\}.
$$

All subsets of A and of B satisfy the three-child Hall inequalities.
Their full divisor stocks have sizes six and ten, respectively. But for
each b in B, the three parents in A union {b} have only eight divisor
labels for nine children. Thus |A|<|B| and no element of B augments A.
All anchors are products of two distinct primes from
{5,7,11,13,17,19}. The exact divisor sets, all-subset Hall predicates,
stock sizes and failure of augmentation have been compiled in a scoped
Lean check using only the standard axioms. The general graph
characterization is the ordinary argument above.

This rules out applying the matroid sampler directly to whole repair
parents. The first-stage partition-matroid sampler remains applicable.
For semiprime parents one can instead test the bad two-, three-, and
four-parent witnesses. For such a witness F, the probability of their
joint activation is at most

$$
\sum_{(\sigma_p)\in\prod_{p\in F}\Sigma_p}
\left(\frac{26}{27}\right)^{|\bigcup_{p\in F}C(\sigma_p)|}.
\tag{MH12}
$$

This uses CVZ's all-zero bound for the union of candidate sets in one
common sample, followed by a union bound over realized signatures. It
does not multiply separate activation probabilities. No adequate bound
on this signature sum has been proved for an actual minimal cover.

Original private points do not automatically witness residual packet
activation. For example, packets {a,c} and {b,c} have private points a
and b before a first-stage cover removes {a,b}; both packets then activate
only at c. Any use of original-private-point bounds needs a separate
supplier. Shared-output repairs and other depths are outside MH11's
one-distinct-divisor-per-child contract.

## Arbitrary finite heights have a budget-dependent normalization

Suppose a finite legal replacement of the full residual uses M APs
with numerical labels 3^k d, k>=3, in this same cofactor-divisor
interface. It has a replacement with no more APs, no greater total
modulus sum and maximum height at most M+2.

Work on the product of ternary digit strings and the unchanged
W-coordinate. Number digit positions starting at one. If height j>=3
is unused and a larger height is used, insert a fixed digit at
position j and pull the entire cover back under that injection.
The inverse image of the residual is the same residual because its
first two ternary digits and W-coordinate have not changed. A prefix
of depth less than j is unchanged. A deeper prefix disappears if
its j-th digit disagrees with the inserted digit; otherwise it
shortens by one. Its cofactor phase stays fixed.

No label at height j was used. Therefore the shortened labels,
whose new heights are at least j, cannot collide with unchanged
shallower labels; distinct shortened labels remain distinct. Count
and cost do not increase. Repeating removes all gaps in occupied
heights. A final maximum K then uses every height 3,...,K, so
K-2<=M. This can equivalently be carried out on finite CRT periods
at each step; it is not a claim that changing an integer's ternary
digits alone preserves its residues modulo W.

Thus a plan with fewer than N outputs can be sought at heights at
most N+1, and an at-most-N plan at heights at most N+2. This does
not reduce the repair interface to the fixed depths three and four.
The latter are the sufficient scheme analyzed in MH5--MH9.

## Verification boundary

The CVZ original theorem and its independence-polytope scope were
checked in arXiv:0909.4348v2, printed page three, Theorem 1.1. Its
negative-correlation theorem is reused as published mathematics;
there is no new Lean proof of it here. Mathlib's finite Hall theorem
is applied directly in scoped Lean checks of both directions of the
downset criterion. Separate scoped applications check the all-color
CRT transport, MH4 arithmetic, the strict cost comparison, the miss
threshold, identical sibling activations, and the integer Hall
threshold. They use only the standard axioms and default budgets.
The entire sampler-to-arithmetic replacement, probability argument
and height normalization have independent ordinary proofs here;
they are not one compiled end-to-end theorem. Forcing an actual
repair condition, and unrestricted Erdős #7, remain unresolved.
