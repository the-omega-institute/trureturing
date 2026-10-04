[Index](../../../marked_head_profile.md) · [Paid packets](853-paid-packet-absorption-and-residual-moment.md) · [Long donors](854-long-paid-donors-and-cluster-moment.md) · [Permanent plans](855-permanent-owners-and-small-relative-packets.md)

# Coherent owner laws and bounded relative certificates

For one fixed source geometry, choose each active good group's
permanent owner under a finite probability law. The simultaneous
payment rule forces

$$
\sum_{m\in\mathscr B}\prod_{s\in\mathscr G}
       \bigl(1-\mu_s(J_{ms})\bigr)\ge1.
\tag{CO1}
$$

Here $J_{ms}$ contains the admissible owners of good group $s$
whose paid $27s$ enclosure contains at least one whole inverse
of bad group $m$. Each good group is chosen once for all targets.
Under uniform owner choices this implies

$$
\sum_{m\in\mathscr B}(2/3)^{D_m}\ge1,
\qquad D_m=\#\{s\in\mathscr G:J_{ms}\ne\varnothing\}.
\tag{CO2}
$$

An independent exact test handles a covering subpacket of at
most ten paid outputs: besides a compatible divisor donor, it
must contain all five relative phases modulo five, all seven
modulo seven, or four modulo-five parents and all five
modulo-25 children of the remaining parent. The test uses
literal phases from the same permanent packet.

These are conditional applications of the existing payment,
probability and covering results. Whole coverage has not supplied
enough compatible donors to violate CO1 or CO2, and these tests
do not resolve the height-two branch or unrestricted Erdős #7.

## 1. One geometry and one owner assignment

Keep [Report853's common source and EB1 hypotheses](853-paid-packet-absorption-and-residual-moment.md#1-one-actual-family-and-one-common-code): the original distinct odd whole cover
minimizes first its cardinality $K$ and then its numerical
modulus sum, with $H_3=2$, $q=113$ and $(W,3q)=1$.
Fix one lawful code, its geometry, all deeper dictionaries and
every actual cofactor phase. Write $\mathscr B$ for its bad
groups and $\mathscr G$ for its active good groups.

An active good group has at least one nonempty continuing
inverse. A group with no nonempty inverse is omitted and
requires no owner choice. For each $s\in\mathscr G$, let
$A_s$ be its admissible designated owners for the $27s$ output,
under [Report853's allocation rule](853-paid-packet-absorption-and-residual-moment.md#2-admissible-donors-and-simultaneous-payment).
With one or two nonempty inverses, every owner is admissible.
With three nonempty inverses, designating an owner must leave
at least one depth-five inverse for the $243s$ assignment.
Thus a group with exactly one long inverse has precisely its
two short owners available; a group with at least two long
inverses has all three owners available. There is no additional
no-designation option for an active group.
Thus

$$
1\le |A_s|\le3.
\tag{CO3}
$$

For each admissible owner, fix a legal completion of that
group's remaining $81s$ and, if needed, $243s$ assignments.
All selections from the different $A_s$ coexist under the
same fixed source. They do not change the code geometry or
any original residue. In particular, an owner available only
under another geometry is not an element of this $A_s$.

For $a\in A_s$, denote its designated whole enclosure by

$$
E_{s,a}=[\ell_{s,a}]_{27}\times[r_{s,a}]_s.
$$

Define the actual hit set

$$
J_{ms}=\{a\in A_s:\exists i\in\{0,1,2\},\,
                         B_{m,i}\subseteq E_{s,a}\},
\qquad h_{ms}=|J_{ms}|.
\tag{CO4}
$$

The containment is of an entire inverse. By PP11 it requires
the same ternary parent, $s\mid m$, and actual cofactor-phase
agreement. Neither pointwise supply nor cofactor divisibility
alone places an owner in $J_{ms}$.

One selection $a=(a_s)_{s\in\mathscr G}$ gives the lawful packet

$$
P_a=\bigcup_{s\in\mathscr G}E_{s,a_s}.
$$

Call a bad group singly hit when $a_s\in J_{ms}$ for some $s$.
Every singly hit group is absorbed by $P_a$; joint coverage by
several donors can absorb further groups. Report853 PP7 says
that every such packet leaves some bad group wholly unabsorbed.
Consequently

$$
\forall a\in\prod_{s\in\mathscr G}A_s\quad
\exists m\in\mathscr B\quad
\forall s\in\mathscr G,\ a_s\notin J_{ms}.
\tag{CO5}
$$

This conclusion retains the same owner assignment for every
target. It also implies $\mathscr B\ne\varnothing$; a code
with no bad group would already give the forbidden ordinary
allocation from Report853.

## 2. The common-owner inequality

For each $s$, let $\mu_s$ be any nonnegative rational probability
law on $A_s$. Sample the good-group owners independently under
$\bigotimes_s\mu_s$. Independence here concerns the chosen
owner coordinates; no independence between bad-group events
is assumed.

The probability that bad group $m$ is not singly hit is

$$
u_m=\prod_{s\in\mathscr G}\mu_s(A_s\setminus J_{ms})
   =\prod_{s\in\mathscr G}(1-\mu_s(J_{ms})).
\tag{CO6}
$$

By CO5 these failure events cover the entire assignment space.
The union bound gives $1\le\sum_m u_m$, proving CO1.
Equivalently, every selection has at least one unhit bad group,
so the expected number of unhit bad groups is at least one.
The sum counts groups, even when one owner covers two or three
inverses of the same group.

This probability step directly uses the existing finite product
law and cover union bound, respectively
`piLaw_prob_forall_bool` in
[FiniteProbability](../../../../../../D5/S3/Arith/Congruence/ConditionalComparison/FiniteProbability.lean)
and `one_le_sum_prob_of_cover` in
[CappedGainProbability](../../../../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainProbability.lean).
The conditional application has been Lean checked. Its premise
is CO5; this check does not establish the arithmetic source,
payment hypotheses or whole-inverse containments.

For uniform owner laws, CO1 becomes

$$
\sum_{m\in\mathscr B}\prod_{s\in\mathscr G}
       \left(1-\frac{h_{ms}}{|A_s|}\right)\ge1.
\tag{CO7}
$$

If $h_{ms}>0$, CO3 gives
$1-h_{ms}/|A_s|\le2/3$; otherwise the factor is one.
Thus each product in CO7 is at most $(2/3)^{D_m}$, proving CO2.
Repeated hits from one good group contribute one coordinate to
$D_m$, regardless of how many admissible owners or inverses
realize the hit. Empty good groups contribute no coordinate.

Every counted cofactor $s$ is a nonunit proper divisor of $m$:
$s\mid m$ by whole containment, and $s=m$ is impossible
because a fixed-code group cannot be both good and bad. Hence

$$
D_m\le\tau(m)-2.
$$

A bad prime-cofactor group has $D_m=0$ and contributes exactly
one to CO1 under every owner law. For such a geometry, this
single-donor criterion cannot yield a strict reverse inequality.
In the cofactor-$5,35,55$ example of Section 6, the two seed
options hit opposite bad groups. Their failure probabilities
are $p$ and $1-p$, so CO1 is equality for every seed law.

### Choosing a code that excludes a prescribed small inventory

The prime-target obstruction can be avoided for selected
cofactors by choosing the geometry first. Use the original
$q=113$ domain $U\times\mathcal A$ of
[Report388's common six-code construction](../350-399/388-source-global-substitution-collision-moment.md#a-weighted-finite-height-alternative-at-q-equal-to-113),
where $|U|=110$ and every row has five safe words. Each
actual shallow nonunit cofactor $m$ has one final cell
$(c_2(m),z_m)$. Being bad requires that cell to be selected
by the code, in addition to the lower-digit conditions.

Given any specified set of at most 524 such cofactors,
remove their final cells when those cells lie in this domain.
At least $550-524=26$ cells remain. Since each row contains
at most five cells, at least six distinct rows remain.
Choose one remaining cell in each of six rows. This is a
legal six-code and none of the specified cofactors is bad.
This uses the same missing-cell construction as
[Report388 SC473--SC474](../350-399/388-source-global-substitution-collision-moment.md#eligible-final-cells-and-capacity-nine-hall-matching).
It changes the code before its geometry and owner laws are fixed.

Under the original height envelope used in Report388 SC481,
there are at most 27 possible cofactor primes and at most
284 nonunit prime powers. The construction therefore permits
either of the following exclusions:

| Prescribed inventory | Upper bound | Consequence for every bad group |
|---|---:|---|
| All nonunit prime powers in the height envelope | 284 | $\omega(m)\ge2$ |
| All nonunit cofactors with $\tau(m)\le5$ | $4\cdot27+\binom{27}{2}=459$ | $\tau(m)\ge6$ |

For the second row, every such number is $p^a$ with
$1\le a\le4$, or $pq$ with distinct primes. These are
alternative inventories: their union can exceed the 524-cell
budget. Selecting a code by these exclusions does not preserve
the uniform code probabilities in SC479. After selection,
CO1 applies to the new fixed geometry, but the larger possible
divisor inventory gives no lower bound on its actual useful
donor count $D_m$ or its phase-compatible hit sets.

The finite six-row selection and the numerical bounds
$27$, $459\le524$ and $284\le524$ have been Lean checked.
This does not formalize the divisor-count classification,
the height envelope or the code's arithmetic completion.

### A strict reverse inequality constructs one packet

Suppose a specified geometry and specified laws satisfy
$\sum_m u_m<1$. The method of conditional expectations fixes
the good-group owners one at a time. At a current partial
assignment, the expected number of unhit bad groups is the
$\mu_s$-weighted average of the conditional values obtained
by fixing the next owner. Choose an option of positive
$\mu_s$-mass whose value is no larger than that average.
Such an option exists because the weights are nonnegative
and sum to one.

After all coordinates are fixed, the residual count is a
nonnegative integer strictly below one, hence zero. All bad
groups are singly hit by the one resulting legal packet.
Report853's simultaneous payment then gives an EB1 improvement.
This is a direct finite-averaging application; it supplies no
initial law or geometry satisfying the strict inequality.

The owner law may use the entire actual family. It remains
one law for all targets, and each coordinate is fixed
permanently. Summing probabilities obtained from different
target-dependent geometries or independently optimized owner
selections does not prove CO1's strict reverse inequality.

## 3. Exact relative phases and the reusable cyclic bound

Use one legal packet and a target cofactor class $[r]_m$,
with $m\mid W$. Write its cofactor coordinate as $w=r+mu$
on $\mathbb Z/(W/m)\mathbb Z$. A donor $[b]_s$, $s\mid W$,
has a nonempty restriction exactly when
$g=\gcd(m,s)$ divides the integer difference $b-r$.
Its actual relative class is

$$
[\rho_s]_{d_s},\qquad
d_s=\frac{s}{g},\qquad
\rho_s\equiv(m/g)^{-1}(b-r)/g\pmod{d_s}.
\tag{CO8}
$$

The unit relative modulus denotes the whole quotient. These
are [Report855 RO7's literal restrictions](855-permanent-owners-and-small-relative-packets.md#4-the-quantifiers-in-a-stopping-certificate), including its ternary-incidence condition.

Suppose two restrictions are nonempty and $d_{s_1}=d_{s_2}$.
Their reduced phases satisfy the inversion-free test

$$
\rho_{s_1}\ne\rho_{s_2}
\quad\Longleftrightarrow\quad
\gcd(s_1,s_2)\nmid b_1-b_2.
\tag{CO9}
$$

Indeed, two cosets of the same relative modulus have equal
phases exactly when they intersect. Such an intersection
solves the three original congruences modulo $m,s_1,s_2$.
Compatibility with $m$ already holds. Generalized CRT leaves
precisely $\gcd(s_1,s_2)\mid b_1-b_2$. Since the moduli
divide $W$, an integer solution belongs to the same finite
carrier. When $d_s=1$, both sides of CO9 are false.

Put $\Psi(n)=\sum_pv_p(n)(p-1)$. For an inclusion-minimal
whole cover of a cyclic group by relative classes indexed
by $I$, the published bound is

$$
|I|\ge1+\Psi(L_I),\qquad L_I=\operatorname{lcm}_{i\in I}d_i.
\tag{CO10}
$$

Reuse [Report388 SC39](../350-399/388-source-global-substitution-collision-moment.md#the-published-small-cover-bound-forces-five-complete-lower-classes), citing Simpson, *Regular coverings of the integers by
arithmetic progressions*, Corollary 2, pp.151--152,
[DOI 10.4064/aa-45-2-145-152](https://doi.org/10.4064/aa-45-2-145-152).
The same cyclic statement follows from Sun, *Finite covers
of groups by cosets or subgroups*,
[arXiv:math/0501451v4](https://arxiv.org/html/math/0501451v4),
Corollary 1.1 and Remark 1.2, equation (1.10).
There a minimal ordinary cover is a regular cover; no
disjointness hypothesis is required. Existing source notes in
[Jenkin--Simpson](../../../../../../Library/Arith/jenkin2003compositecovering.md)
and the [Simpson divisor-cut application](../../../../../../Library/Arith/mcnewsetty2026covering.md#4-lemma-31-is-already-supplied-by-the-existing-divisor-cut)
also retain this input.

The index in CO10 is the actual minimal subcover's LCM.
It need not equal $W/m$, and a redundant packet's LCM
must be recomputed after reduction. For example, the five
phases modulo five plus a redundant modulo-seven class cover
with six outputs. Their full LCM is 35, whereas the minimal
subcover has LCM five. CO10 applies to the latter.

Cyclicity is essential to this particular joint bound. The
[Lettl--Sun theorem](../../../../../../Library/Arith/lettlsun2008cosets.md)
used in Report855 controls each essential index in a general
abelian cover; it does not justify replacing that index by
an arbitrary abelian subgroup-intersection index. CO10 is the
explicit cyclic input for the classification below. It still
requires whole relative coverage, not a punctured residual mask.

## 4. Exact certificates using at most ten outputs

Fix an actual permanent packet of $27s$ outputs and one target
ternary parent. Discard outputs at another parent and empty
restrictions in CO8. Every remaining nonunit relative modulus
is odd and 3-free, so all its prime factors are at least five.
Repeated relative moduli are allowed.

Suppose some subpacket of at most ten outputs covers the
whole target inverse and has no unit restriction. Reduce it
to an inclusion-minimal relative cover $I$. CO10 gives
$\Psi(L_I)\le9$, hence

$$
L_I\in\{5,7,25\}.
\tag{CO11}
$$

An allowed prime at least eleven contributes at least ten;
$5\cdot7$ contributes ten, $7^2$ contributes twelve, and
$5^3$ contributes twelve. These exclude every other nonunit
LCM. For LCM five or seven, all classes have that prime
modulus and minimal coverage requires exactly all its phases.

For LCM 25, each essential class has modulus five or 25.
In each modulo-five parent either its broad class is present,
making every child there redundant, or all five modulo-25
children are required. If $t$ parents are refined, the count is

$$
|I|=(5-t)+5t=5+4t.
\tag{CO12}
$$

LCM 25 requires $t\ge1$, and $|I|\le10$ forces $t=1$.
Thus the minimal cover has four broad parents and the five
children of the remaining parent, with nine outputs.
Disjointness follows from this classification; it was not
assumed when applying CO10.

For $d\in\{5,7,25\}$, let $\Phi_d$ contain precisely the
phases in $\mathbb Z/d\mathbb Z$ supplied by already-paid,
compatible outputs of exact relative modulus $d$. The following
table is an exact test for a covering subpacket of at most ten:

| Available actual pattern | Number of selected outputs |
|---|---:|
| A compatible relative-modulus-one output | 1 |
| $\Phi_5=\mathbb Z/5\mathbb Z$ | 5 |
| $\Phi_7=\mathbb Z/7\mathbb Z$ | 7 |
| Some $a\in\mathbb Z/5\mathbb Z$ has every other parent in $\Phi_5$, and all five lifts of $a$ in $\Phi_{25}$ | 9 |

Necessity is CO11--CO12. For sufficiency, select one actual
output per listed phase. A single output has one exact
relative modulus and one phase, so the selected outputs are
distinct. Each pattern covers the entire quotient. The full
paid packet may be larger than ten: the table characterizes
existence of a covering subpacket within that budget, not
arbitrary coverage by its unrestricted union.

The ten-output limit cannot be replaced by eleven with the
same list of patterns. The four classes $0,1,2,3\pmod5$,
the six classes $0,1,2,3,4,5\pmod7$, and $34\pmod{35}$
form an irredundant eleven-class cover. The first two families
leave exactly the CRT cell $(4\pmod5,6\pmod7)$, which the
last class fills. Each modulo-five class has a private point
in phase six modulo seven, and each modulo-seven class has
one in phase four modulo five; 34 is private to the last
class. No complete modulo-five or modulo-seven phase set is
present, and there are no modulo-25 children. This is a
relative-cover boundary example, not an EB1 realization.

### Donor fibres and ternary slices

For a target with $h=v_5(m)$, Report855 RO9 identifies the
donor cofactors for the mixed nine-output pattern as

$$
\begin{aligned}
d_s=5&:\quad s=5^{h+1}a,\\
d_s=25&:\quad s=5^{h+2}a,
\end{aligned}
\qquad a\mid m/5^h.
\tag{CO13}
$$

Under the one-$27s$-owner convention, the child fibre needs
five different actual donor cofactors. Its numerical size
therefore requires $\tau(m/5^h)\ge5$. The broad fibre must
also supply its four actual phases. These fibre counts do
not produce the phases or compatible permanent owners.

For the full-output convention, lift the ternary coordinate
to modulo 243. A depth-four target has three slices and a
depth-five target has one. On a fixed slice, every paid
$27s$, $81s$ or $243s$ output is either absent or induces
CO8 on the same cofactor quotient. The table applies to that
slice's actual restrictions.

Whole-inverse containment must hold on every slice using one
permanent packet. Different size-ten subpackets found on
different slices may have a union larger than ten. Thus
independent slice tests do not certify one size-ten subpacket
for the whole inverse. If the entire fixed packet already
has at most ten outputs, applying the test on every slice
does certify its whole-inverse coverage.

The [common long-donor geometry](854-long-paid-donors-and-cluster-moment.md)
bounds distinct digit leaves, while this test counts outputs.
Several cofactor outputs may share one digit. Neither a
seven-output nor a nine-output arithmetic pattern supplies
its geometric realization automatically.

## 5. Target-specific pruning and first-entry obstructions

For one target slice, let $P_0$ index the nonempty restrictions
of one fixed legal packet. Iteratively set

$$
P_{n+1}=\{i\in P_n:\Psi(d_i)\le |P_n|-1\}.
\tag{CO14}
$$

The sequence stabilizes because it is decreasing and finite.
It preserves whether this target slice is covered. To prove
this, if $P_0$ covers, choose a minimal subcover $I$.
Every $i\in I$ is essential there, and the individual
Lettl--Sun bound gives $\Psi(d_i)\le |I|-1$.
Whenever $I\subseteq P_n$, every member of $I$ survives
CO14. Induction preserves $I$ through stabilization.
Conversely, the stabilized packet is a subset of $P_0$.
The empty packet cannot cover the nonempty quotient.

This uses the existing individual essential-index bound,
without needing the stronger joint bound CO10. The deletion
concerns only this target's coverage test. A discarded output
stays in its permanent group allocation and may remain
necessary for its own inverse or another target. A nonempty
stabilized core alone does not prove coverage.

### A necessary pair under a genuine output budget

Assume a legal packet of at most $\kappa<K$ outputs covers
one whole target slice and has no unit relative modulus.
Choose a minimal subcover $I$. If no relative modulus occurs
with different phases, merging identical restrictions yields
a distinct odd nonunit integer cover with fewer than $K$
classes, contrary to EB1. Thus some pair in $I$ has equal
relative modulus $d$ and different phases.

Reuse Report855 RO10's discrepancy divisor

$$
\mathfrak D(s,t)=\prod_{p:v_p(s)\ne v_p(t)}
                    p^{\max(v_p(s),v_p(t))}.
$$

That pair satisfies

$$
\mathfrak D(s_i,s_j)\mid m,\qquad
\gcd(s_i,s_j)\nmid b_i-b_j,\qquad
\Psi(d)\le\kappa-1,
\tag{CO15}
$$

as well as both target compatibility conditions in CO8 and
actual incidence on the chosen ternary slice. The first
condition gives equal relative moduli, the second is CO9,
and the last follows from essentiality in $I$.
An available pair is only a necessary condition for coverage.

When all paid levels are allowed, two outputs of the same
group can have $s_i=s_j$, different phases and
$\mathfrak D(s_i,s_j)=1$. They must remain separate labels.
The distinct-cofactor prime-chain consequence for $27s$-only
packets cannot exclude these full-output pairs.

### A correctly quantified first-entry fort

Let $R\ne\varnothing$ be a set of currently unrescued bad
groups. For each $m\in R$ and each of its three possible
omitted inverses, specify a ternary slice contained in that
inverse. On that slice, consider all jointly legal choices
of outside-group plans extending the current permanent
commitments. One may enlarge the choices to include plans
of outside groups that are not yet paid; this is an optimistic
test, not an authorization to pay them.

For each such slice, require a proved bound $\kappa<K$ on
the number of outputs in every candidate first-entry funding
packet considered by the test. Suppose that none of these
jointly legal choices supplies either a compatible unit
restriction or a pair satisfying CO15. Then no legal
sequential rescue enters $R$.

Indeed, the first proposed entry into $R$ would omit one of
the inverses quantified above. Its whole coverage would use
only outside outputs. That actual packet is among the
allowed choices and obeys their output bound. It would cover
the specified slice, contradicting the necessary alternative.
The slice may depend on the target and omission, but all
outside plan choices for that test are quantified jointly.

Testing only a fixed omission cannot exclude another omission.
A numerical $\kappa$ without the stated output count also
cannot certify a fort. Five phases modulo five cover, although
none has $\Psi(5)\le3$; assigning the false budget four would
give a false obstruction. The usual fewer-than-$K$ bound can
come from assigning each paid output to a distinct original
owner while the unrescued target's three originals remain
outside the funding packet. Any smaller budget needs its
own actual count.

For a first rescue, if every eligible different-phase pair
has $\Psi(d)\ge\beta$, no unit donor exists, and fewer than
$K$ outputs are available, CO15 requires at least $\beta+1$
outputs. If each seed contributes at most $b>0$ outputs on
the slice, at least $\lceil(\beta+1)/b\rceil$ seeds are
necessary. Here $b=1$ for $27s$-only accounting; the full
good-group allocation has the valid upper bound $b=3$.
This is a first-entry count, not a cost charged again for
every later target. Donor reuse remains free. It does not
exclude a separately verified simultaneous final repair.

## 6. The arithmetic owner conflict also blocks simultaneous plans

Use the actual interface example in
[Report855, Section 3](855-permanent-owners-and-small-relative-packets.md#3-an-actual-congruence-counterexample-to-forgetting-plans): $W=385$, seed cofactor five, and bad groups 35 and 55.
On $\mathbb Z/81\mathbb Z\times\mathbb Z/385\mathbb Z$,
the two legal seed packets are

$$
\begin{aligned}
P_0&=([2]_{27}\times[0]_5)\cup([29]_{81}\times[1]_5),\\
P_1&=([2]_{81}\times[0]_5)\cup([2]_{27}\times[1]_5).
\end{aligned}
$$

The bad inverses are

$$
B_{35,a}=[56]_{81}\times[5a]_{35},\qquad
B_{55,a}=[56]_{81}\times[1+5a]_{55},
\quad a\in\{0,1,2\}.
\tag{CO16}
$$

Each bad group chooses one omitted owner and assigns its
other two owners to $27m$ and $81m$, in either order.
Even allowing all these choices simultaneously cannot cover
both groups under either seed plan.

Under $P_0$, let $a$ be the omitted owner of group 55.
The point

$$
(z,w)=(56,1+5a)
\tag{CO17}
$$

belongs to its omitted inverse. The seed's broad output and
every output of group 35 have cofactor phase zero modulo
five, whereas $w\equiv1\pmod5$. The seed's narrow output
has ternary leaf 29, not 56. The retained group-55 owners
have phases $1+5k\pmod{55}$ with $k\ne a$, so their
outputs also miss this point. This remains true if both
retained outputs are enlarged to their modulo-27 parents.

Under $P_1$, let $a$ be the omitted owner of group 35.
The symmetric witness

$$
(z,w)=(56,5a)
\tag{CO18}
$$

misses the seed, the entire phase-one modulo-five fibre
containing every group-55 output, and both retained
group-35 phases. The witnesses satisfy $0\le z<81$ and
$0\le w<385$, and lift to the common modulo-243 carrier.
These two exact witness statements have been Lean checked.

The argument covers all $2\cdot6\cdot6=72$ simultaneous
two-output plan choices without assuming a sequential order.
It strengthens this interface counterexample only: it does
not realize an original odd distinct whole cover, establish
an EB1 occurrence, or exclude other replacement architectures.

## 7. What the combined interfaces still require

CO1 can use every actual compatible target under one geometry
and one owner law. CO11--CO13 detect joint coverage by several
outputs even when no single donor contains the inverse.
CO14--CO15 can reject impossible target certificates while
preserving all permanent payments. CO17--CO18 show why
independently successful owner choices need not combine into
even a simultaneous final family.

The remaining extraction must obtain from the actual original
whole cover a geometry and jointly legal owner choices with
enough whole-inverse containment or phase-complete packets to
pay the exchange. No result here supplies that abundance.
Neither the uniform exponent $D_m$, a numerical donor-fibre
count, nor a targetwise list of possible phases may replace
the actual common realization. The conditional probability
application and the explicit arithmetic witnesses do not
constitute a Lean verification of this unrestricted extraction.
