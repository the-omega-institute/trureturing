# Positive certification and continued use of the actual two-source relation

## 1. Positive evidence in the original shared-injection family

**Definition 1.1 (source, target and evidence).** Use the stationary finite
prepared source of [UJB §§5, 9](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md):
public $N\ge4$, $M=1944$, $\mathcal L=\{0,1\}^7$,
$\mathcal R=\{0,1\}^8$, and public $\theta\in[0,1]$.
The positive prior support $\mathcal G_\theta$ consists of exactly the
supported sources and every full pair of once-shared injections
$\lambda:A\hookrightarrow\mathcal L$,
$\varrho:T\hookrightarrow\mathcal R$, with the weights in UJB.9001.
Thus source zero is supported iff $\theta<1$, and source one iff $\theta>0$.
The observer has this support information; it requires no numerical
comparison with an unrepresented arbitrary real.

Here $F=\mathbb F_3$, $A=(F^2\setminus\{0\})\times F^2$,
$T=F^3\times F^2$, and the literal relations are

$$
\begin{aligned}
B_0(v,w)&=(v_1w_1+v_2w_2,\ v_1w_2+v_2w_3),\\
B_1(v,w)&=(v_1w_1-v_2w_2,\ v_2w_1+v_1w_2),\\
E_i&=\{((v,s),(w,z)):B_i(v,w)=s\},\\
\mathcal E_g&=(\lambda\times\varrho)(E_i).
\end{aligned}
\tag{PCR.1}
$$

There are $72$ literal left endpoints, $243$ literal right endpoints,
left degree $27$, right degree $8$, and exactly $1944$ edges. In particular
$w_3$ and all nine $z$ values remain in the literal source also for $B_1$.
Conditional on $g$, the originally prepared $Y_1,\ldots,Y_N$ are iid
uniform on $\mathcal E_g$. They are not a persistent sampler.

Let $D$ be the set of distinct full label pairs at some completed original
indices. In this section the only evidence used for certification is the
positivity of those complete pairs. No absent pair is an observed negative,
and no partial-bit cache is included in this certification test. Put

$$
\mathcal V_\theta(D)=\{g\in\mathcal G_\theta:D\subseteq\mathcal E_g\}.
\tag{PCR.2}
$$

For a particular $g$, a positive complete-label certificate is a set
$D\subseteq\mathcal E_g$ for which $\mathcal V_\theta(D)$ is nonempty
and every member has target relation $\mathcal E_g$. The target is the
whole transported relation, rather than a unique generator or its source bit.
The complete ordered samples still cost one slot each, including repetitions.

**Definition 1.2 (public recognition and reconstruction).** From $D$ alone
compute its used left and right label sets $X,Y$. If $|X|\ne72$ or
$|Y|\ne243$, reject. Otherwise, for each supported $i$, enumerate all
bijections $A\to X$ and $T\to Y$. Construct each transported $E_i$ from
(PCR.1), and retain it exactly when it contains $D$. Accept precisely when
at least one relation survives and all surviving relations are equal.
Return that relation, denoted $\widehat E(D)$; otherwise return failure.

These are computations on acquired words and public finite structures.
Canonical hidden coordinates are used to enumerate public candidates, not
supplied as the observer's true frame. The algorithm does not ask the
source for membership or for a chosen label. At most
$2\cdot72!\cdot243!$ candidate maps are enumerated, with unsupported
branches omitted. Each candidate can be constructed in $1944$ edge
insertions after its maps are specified and checked against $|D|$ pairs.
The literal edge lists can first be computed once from the public $B_i$
by $72\cdot243$ equation tests per supported branch. Map enumeration,
bit operations, integer lengths and working storage are additional finite
costs. This bound asserts termination, not efficient discovery.

**Proposition 1.3 (recognition on the actual positive domain).** On attained
complete-label evidence, Definition 1.2 accepts exactly the certificates
of Definition 1.1, and returns their common $1944$-edge target.

Proof. The support-necessity theorem in §4 shows that a certificate must
expose all $72$ and $243$ used endpoint labels. At those cardinalities,
every compatible full injection has image exactly $X$ or $Y$. Thus the
bijections enumerated in Definition 1.2 are precisely all the compatible
full maps on the supported branches, with repetitions of the same target
allowed. The equality test is exactly target constancy on this version set.
No prior mass is discarded except unsupported branches. $\square$

The generic target-constancy and target-disagreement criteria are already
supplied by `target_recovery_criterion` and
`target_sufficiency_iff_pair_cover`, cited in §7. The mathematical issue
below is the size of positive sets that satisfy this test in the actual
orbit family, not another abstract factorization criterion.

## 2. A 576-pair certificate for every transported G0

**Theorem 2.1 (uniform G0 certificate).** For every full shared relabeling
$g=(0,\lambda,\varrho)$ with $\theta<1$, there is a positive complete-label
certificate of exactly $576$ distinct pairs. It determines every edge of
$\mathcal E_g$ against all of $\mathcal G_\theta$, including source one
when $\theta>0$.

Proof. We first construct a literal set $D_0\subseteq E_0$. Use the exact
geometry of UJB Theorem 15.2. Left types are the $36$ affine lines in
$F^3$ with directions

$$
F(0,0,1),\quad F(1,0,0),\quad F(1,2,1),\quad F(1,1,1),
\tag{PCR.3}
$$

each with two literal representatives. Right types are the $27$ points
$w$, each with nine literal representatives $(w,z)$. Every incidence
lifts to all $2\cdot9$ edges, not one quotient edge in place of them.

For each point $w$, choose the right anchor $r_w=(w,(0,0))$ and put
all eight edges incident to $r_w$ in $D_0$. These give $27\cdot8=216$
pairs. Each literal left endpoint meets three anchor columns. The
columns have distinct eight-element neighborhoods, and each of the $72$
left endpoints is exposed.

Let $S=\{w:w_1\in\{0,1\}\}$, of size $18$. For every $w\in S$ and
every $z\ne(0,0)$, add two pairs: join $(w,z)$ to one literal left
representative of the line through $w$ in direction $F(1,0,0)$ and one
of the line in direction $F(0,0,1)$. These are different line types.
For each $w$ with $w_1=2$ and every $z\ne(0,0)$, add just the pair
to one representative of its $F(1,0,0)$ line. The representatives may be
chosen in any fixed public ordering of the literal $A$ for this existence
construction. The three blocks have disjoint right endpoints, and within
the second block the two left endpoints differ. Consequently

$$
|D_0|=216+18\cdot8\cdot2+9\cdot8=576.
\tag{PCR.4}
$$

All $72$ left and $243$ right endpoints occur. Transport this set by the
actual $\lambda,\varrho$ to obtain $D$. The observer need not know those
maps, the set $S$, or the choices of representatives.

Consider any compatible $g'$. Every right anchor has eight acquired
neighbors, so its whole neighborhood in $\mathcal E_{g'}$ is exactly that
eight-element set: every candidate right degree is eight. All $27$ such
sets are different. G1 has only nine distinct right neighborhoods, by UJB
Theorem 15.2, so $g'$ must have source zero. Its $27$ anchor labels thus
occupy all $27$ different right types, one apiece.

The saturated anchor columns also determine the entire adjacency pattern
of every exposed left label to those $27$ right types. Equality of these
patterns is exactly equality of the candidate's left types, since there
is an anchor at every right type. The observed patterns are the original
$36$ patterns, each on two left labels. Thus the two representatives of
every left type and the whole line-point incidence table are already
fixed in label coordinates. This argument neither identifies a hidden
affine frame nor assumes the observer has computed one.

For an added right endpoint above $w\in S$, its two observed neighbors
occupy the two distinct anchored line types through $w$. Two different
affine lines meet in at most one point. Their intersection is the point
type of $r_w$, already incident to both. Hence this right label must have
that type in every $g'$. Including $r_w$, its nine right labels exhaust
that point type's literal capacity. This holds at all $18$ points of $S$.

For $w_1=2$, the indicated line in direction $F(1,0,0)$ has exactly two
points in $S$ and the point $w$ outside it. Its first two right types
already have all nine labels assigned. The remaining observed right
label is a new distinct label adjacent to this line and therefore cannot
occupy either saturated type, by injectivity. It must occupy the third
point type, that of $r_w$. This assigns all its eight nonanchor labels.
Every right label has now been placed in its original point type, every
left type was already fixed, and incidence lifts to precisely the original
$1944$ pairs. Thus $\mathcal E_{g'}=\mathcal E_g$. The actual $g$ ensures
nonemptiness. Definition 1.2 accepts and returns that relation. $\square$

**Definition 2.2 (label-only reconstruction for this witness pattern).**
The proof also gives a sufficient public test on positive histories.
Require exactly $72$ exposed left labels and $243$ exposed right labels.
Find $27$ degree-eight evidence columns with different neighbor sets,
and group left labels by their membership patterns in those columns. Each anchor names a right type of capacity
nine. For every other right label, its possible anchor types are the
intersection of the anchor-type neighborhoods of all its observed left
neighbors. Assign a singleton domain, and remove types already occupied
by nine distinct assigned labels from all remaining domains. Reject this
sufficient test if a domain becomes empty, a capacity is exceeded, or
assignment stalls; accept only when every right label is assigned and each
of the $27$ types contains nine distinct labels. Return all pairs incident
in the inferred type table. Definition 1.2 remains an
exact recognition test even on certificates outside this sufficient pattern.

On the witness of Theorem 2.1, the initial $18\cdot8$ nonanchor singleton
domains fill $S$, and capacity elimination assigns the last $9\cdot8$.
All data in this reconstruction are full words and their evidence
incidences. The coordinates of $S$ enter only the existence proof.

## 3. A 324-pair certificate for every transported G1

**Theorem 3.1 (uniform G1 certificate).** For every full shared relabeling
$g=(1,\lambda,\varrho)$ with $\theta>0$, there is a positive complete-label
certificate of exactly $324$ distinct pairs, sound against every supported
full shared relabeling of both sources.

Proof. G1 has nine literal components $K_{8,27}$, retaining the free
$w_3$ and $z$ coordinates, by UJB Theorem 15.2. Choose one component.
In it choose three distinct left endpoints and ten distinct right endpoints
and include all $30$ pairs between them. Attach each of its other five
left endpoints to one of these right endpoints, and each of its other
seventeen right endpoints to one of these left endpoints. This is one
connected spanning positive graph on its eight and $27$ literal endpoints,
with $30+5+17=52$ pairs.

In each of the other eight components choose one left and one right
anchor and include the double star: all $27$ pairs at the left anchor,
and the seven additional pairs at the right anchor. Each is connected,
spans its entire component, and has $34$ pairs. Their disjoint union $D_1$
therefore has

$$
|D_1|=52+8\cdot34=324.
\tag{PCR.5}
$$

Transport by the actual full maps. Any compatible G0 would contain an
injective $K_{3,10}$, impossible by UJB Theorem 18.1: three distinct
literal left endpoints of G0 have at most nine common right neighbors.
This reuses the actual capacity obstruction; an uncapacitated quotient
would not justify it. Thus every compatible source is G1.

A connected evidence component lies wholly within one candidate G1
component. It already has eight left and $27$ right labels, so it fills
that component's two capacities. Distinct evidence components cannot
share a candidate component. There are nine, so all are filled and every
missing cross-pair within each is forced, while all pairs between them
are absent. The recovered relation is precisely the union of those nine
complete bicliques, of size $9\cdot8\cdot27=1944$. The actual generator
supplies a positive member of the version set. $\square$

For this witness a sufficient label-only test is to find exactly nine
connected evidence components, each with $8$ left and $27$ right labels,
and a $K_{3,10}$ in at least one. The test uses no hidden component names.
The complete-label observations determine each connected component;
checking its finite subgraphs is internal computation. The source-zero
obstruction and the source-one capacities then justify the returned
union of bicliques on the actual positive domain.

The $K_{3,10}$ obstruction is needed for this sufficient argument when
source zero is supported. Nine bare double stars have only $306$ pairs,
but can also occur in G0: take its nine parallel $F(0,0,1)$ lines and
the plane $w_1+w_3=0$. This plane meets each line of every direction in
(PCR.3) exactly once, since its normal is nonzero on each direction.
For each parallel line use one left representative as the left center,
all its $27$ right neighbors, and one right endpoint at its intersection
with the plane as the right center. The eight left endpoints incident
there supply its star. These nine sets of eight left endpoints are
disjoint and cover $A$, since every allowed line meets the plane once;
the nine right sets partition $T$. This gives the same abstract double-star
evidence as in G1, with all endpoint supports exposed. A suitable pair of
full injections realizes identical label evidence in the two sources,
while their full relations differ (G0 is connected; G1 is not).
When only G1 is supported, these $306$ pairs already certify its relation.

## 4. The positive-support necessity boundary

**Theorem 4.1 (all used labels must be exposed).** Assume the ambient
alphabets $128>72$, $256>243$, all full injections on each supported
source, and positive complete-pair evidence alone. Every certificate for
any supported $g$ must expose the entire left image of $\lambda$ and
the entire right image of $\varrho$. In particular it has at least $243$
distinct pairs, and complete-slot acquisition requires at least $243$ slots.

Proof. Suppose a used left label $\lambda(a)$ does not occur in $D$.
There is an unused ambient left word $\ell\notin\lambda(A)$. Replace
only $\lambda(a)$ by $\ell$. This is another full injection, has the same
supported source, and has strictly positive prior mass. It leaves every
pair of $D$ unchanged and valid. But $a$ has $27>0$ neighbors, so its
transported relation changes. This contradicts target constancy. The same
argument replaces an unexposed used right label by an unused ambient right
word; its degree is $8>0$. Every right label must occur in some evidence
pair, giving $|D|\ge243$. One completed slot supplies only one full pair,
so repetitions cannot reduce the slot lower bound. $\square$

This bound does not apply to an arbitrary partial-bit cache containing
additional restrictions: the changed map must preserve that evidence too.
It uses the actual ambient alphabet slack and full-injection prior,
and does not assert the same conclusion for a restricted prior or a
previously supplied complete support dictionary.

**Proposition 4.2 (support exposure is not sufficient).** There is a
$243$-pair complete-support positive set compatible with different
transported G1 relations, even when $\theta=1$.

Proof. In each true component order its eight left endpoints and $27$
right endpoints, and join right endpoint $j$ only to left endpoint
$j\bmod8$, for $0\le j<27$. Each of the eight left stars is nonempty;
three have four leaves and five have three. Across the nine components
this exposes every endpoint with $243$ pairs. Take two left stars with
the same number of leaves in different true components. Permute their
left labels and also exchange their right-label leaf sets by a bijection.
This is a permutation of the same full supports and preserves the positive
set exactly. It changes the full relation, since a star now shares its
component with different other stars. Both full maps have positive mass.
Thus neither $243$ nor full support is a sufficient general recognition
condition. The upper bounds in §§2–3 are not asserted optimal. $\square$

## 5. Targetblind acquisition in a fixed finite stationary preparation

**Definition 5.1 (finite scan and recognition).** Fix an integer cap
$0\le n\le N$. Starting from the public stationary original root, read
all fifteen bits of original sample $j$, for $j=1,\ldots,n$, using
UJB.7706. Retain its complete labels at that original index and form the
distinct set $D_m$ after each completed sample $m$. Run Definition 1.2
there; stop on acceptance, or report failure after $n$ samples. The cap is
public and targetblind. To reserve a wholly unread slot for an unread-law
inverse or continuation, require $n\le N-1$ and reserve original index
$N$. The scan never touches it. There is no extra draw after stopping.

For bit $b=15(j-1)+h$, $1\le h\le15$, the actual operand is
$R^{b-1}LL$. The replies $\beta$ and $\mathsf b$ give zero and one.
Thus scanning $m$ completed slots uses exactly $15m$ Read invocations,
with maximum literal operand length $15m+1$ and total operand length

$$
\frac{15m(15m+3)}2.
\tag{PCR.6}
$$

These charge from the original root on every invocation; no cursor or
rerooting is supplied. A stopped scan uses its actual $m$, bounded by $n$.
For an empty scan both invocation and address costs are zero. All $N$
slots were prepared already: UJB Proposition 5.3 gives $75N+4$ legal
preparation events independently of how many are scanned. The $N$ iid
edge draws, two full-map choices, preparation operands, installation,
computation and memory remain separate resources.

At most $n$ recognition calls are made, each with the finite candidate
bound of Definition 1.2. Storing the full indexed cache as $15N$ mask bits
and $15N$ value positions is sufficient payload storage; counters,
operands, controller and recognition working space are additional. A
$128\times256$ relation bit table uses $32768$ further bits; this is one
implementation choice, not a memory lower bound. A distinct certificate's
$576$ or $324$ pairs is neither a slot budget nor a total-resource claim.

**Theorem 5.2 (attained sufficient event and finite-prefix guarantee).**
For $i$ supported by the actual prior, let $q_0=576$, $q_1=324$ and fix
any actual full generator $g$ of that source. The scan has acceptance
probability, conditional on $g$, at least

$$
\begin{aligned}
F_{q_i}(n)
 &=\sum_{h=0}^{q_i}(-1)^h\binom{q_i}{h}
                         (1-h/1944)^n,\\
F_q(n)&\ge\max\{0,1-q(1-1/1944)^n\}
       \ge\max\{0,1-qe^{-n/1944}\}.
\end{aligned}
\tag{PCR.7}
$$

Here $F_q(n)=0$ for $n<q$ and $F_q(n)>0$ for $n\ge q$.
For the source mixture the corresponding sufficient lower bound is
$(1-\theta)F_{576}(n)+\theta F_{324}(n)$, including $\theta=0,1$.
The formula is the exact probability of covering one fixed mathematical
witness, not the exact probability of recognizing any certificate.

Proof. Choose the transported witness $W_g$ from Theorem 2.1 or 3.1,
only for this proof. The first $n$ original prepared slots cover every
pair of $W_g$ on a well-defined event $H_{g,n}$. Since each specified
edge has mass $1/1944$, ordinary inclusion–exclusion for missing edges
gives (PCR.7)'s first line. The union bound and $1-x\le e^{-x}$ give
the two lower bounds. These are standard occupancy ingredients.

When $n\ge q$, an explicit attained subevent has the first $q$ original
slots list the witness exactly once in any order and leaves all other
slots unrestricted. Its probability is $q!/1944^q>0$, uniformly over all
full relabelings; a particular ordering has probability $1944^{-q}$.
When $n<q$, coverage is impossible. Extra positive pairs cannot destroy
a certificate: they only restrict its nonempty version set, which still
contains the actual generator. Hence on $H_{g,n}$ recognition accepts
by time $n$, possibly earlier. If scanning stopped earlier, the unscanned
original slots still define $H_{g,n}$ in the original preparation; this
argument does not acquire them. Averaging the conditional bounds over
the full prior gives the asserted mixture bound. $\square$

For an integer-only expression, let $a_{m,k}$ count words of length $m$
in the $1944$-edge alphabet that have seen exactly $k$ of the $q$ fixed
witness edges. With out-of-range entries zero,

$$
a_{0,0}=1,\qquad
a_{m+1,k}=(1944-q+k)a_{m,k}+(q-k+1)a_{m,k-1},\qquad
F_q(n)=a_{n,q}/1944^n.
\tag{PCR.8}
$$

This is the usual occupancy recurrence: an old or nonwitness edge leaves
$k$ unchanged; a new witness edge increases it. In particular
$F_q(q)=q!/1944^q$. It counts draws with repetitions, without identifying
distinct-pair count with prepared-slot count.

There is no guaranteed acceptance on every finite run. For $n\ge1$,
the event that all scanned slots repeat one edge has probability
$1944^{1-n}>0$, and fails support exposure; for $n=0$ evidence is empty.
If $n<243$, Theorem 4.1 rules out any certificate of this evidence kind.
For $243\le n<q_i$, this particular witness supplies no positive guarantee;
other certificates are not excluded. Larger $n$ still permits rejection.
A source with zero prior weight supplies no attained event in the mixture.
If $N=q_i$ and all $N$ slots are scanned, success may certify $E$ but leaves
no unread slot. The reserved-slot guarantee from this construction needs
$N\ge q_i+1$, not just $N\ge q_i$. Exhaustion supplies no replacement
sample, reset, target-aware query or persistent sampler.

## 6. The certified relation feeds the existing indexed continuation

**Proposition 6.1 (substitution into UJB17).** Suppose an attained cache
$D^{\mathrm{idx}}$ retains every original index, mask and acquired value,
and its completed-pair set contains an accepted certificate. Let
$E=\widehat E$ be its returned relation. In UJB.9004–9005 every surviving
generator has that same $E$. Therefore, writing $B_j$ for the original
index's actual rectangle,

$$
Q_{E,j}(y)=\frac{\mathbf1_{\{y\in E\cap B_j\}}}{|E\cap B_j|},
\qquad
\mathsf I_{D^{\mathrm{idx}}}(y_1,\ldots,y_N)
       =\prod_{j=1}^N Q_{E,j}(y_j).
\tag{PCR.9}
$$

All denominators are positive on this attained domain. UJB Theorem 17.1
and its actual Read classification consequently give every allowed next
Read, every positive update, and every bounded adaptive continuation
with its declared common controller and resources.

Proof. Complete evidence already forces $E$ across its whole positive
version set. Additional attained partial evidence restricts that set;
it cannot add a generator with a different relation. The indexed factors
in UJB.9004 thus all equal $Q_{E,j}$, and their product can be taken
outside the posterior sum, whose weights sum to one. This is a substitution
into the existing conditional law and continuation theorem, not a new
generic conditioning or sufficiency principle. $\square$

A completed slot has a singleton rectangle intersection and replays its
own recorded pair. A partial slot keeps its own rectangle and its own
restricted set of edges, rather than the unrestricted $E$. An unread slot
keeps its original index and uniform law on $E$, without revealing its
realized pair. Completing a partial slot replaces its factor by the new
restriction; it does not count the old partial likelihood again. For the
reserved scan of §5, original slot $N$ is still genuinely unread. These
facts are exactly the consumer supplied by UJB17; the adaptive transcript
outputs need not be independent. Discarding the cache in favor of $E$
alone would lose completed-slot replay and old partial restrictions,
as the existing UJB §§10–13 counterexamples already establish.

UJB Theorem 17.2 transports this indexed law through Theorem 9.3's
ordered endpoint, oriented material support, terminal boundary and labelled
generation partial order. Its closure/unread-law inverse keeps the fixed
public prior, fixed indexed partial cache and a wholly unread original
sample. A variable-mask cache is not recovered from its law; a complete
generator posterior alone does not recover old-slot association. Neither
certification nor transport recovers the hidden frame, unacquired realized
bits, actual serial preparation history or physical spacetime. The four
expressions carry the stated mathematical laws and inverses on their
existing domains.

## 7. Mathematical suppliers and comparison domains

**Definition 7.1 (scope of the existing results).** UJB Proposition 3.6's full
$1944$-edge collection certificate already establishes complete relation
recovery after all edges have been acquired, with its stated persistent
paid-sampler contract. UJB §§12, 15–18 supply version sets, fixed-cache
closure inverses, the actual two-source geometry and capacities, exact
all-mask evaluation and the indexed Read consumer. The new constructions
in §§2–3 give smaller positive evidence sets for those literal graphs;
§5 connects their existence to the original fixed finite stationary
preparation, without importing a persistent sampler. The source-specific
counts, cross-source exclusion and capacity completion are ordinary
conditional arguments here, not additional Lean certification.

The existing formal declarations
[`TargetRecoveryCriterion.target_recovery_criterion`](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)
and
[`TargetSufficiencyPairCover.target_sufficiency_iff_pair_cover`](../../../D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover.lean)
provide, respectively, target constancy on observation fibers and separation
of every target-disagreement pair by a selected finite observation family.
For target constancy, take the finite domain of supported full-generator and
prepared-array realizations, the scan's actual completed-label readout, and
target $(g,y)\mapsto\mathcal E_g$. Its positive readout fiber projects to
(PCR.2). For the pair-cover criterion, the selected experiments are the
actual fifteen coordinate Reads at each completed index, their responses
are the corresponding bits, and the same relation is the target. A joint
bit-readout fiber fixes the ordered complete pairs; their multiplicities
and order do not further restrict (PCR.2), by UJB §12. These suppliers give
the abstract criterion, not the $576/324$ graph constructions, a targetblind
acquisition event or a cost-free source port. In particular a mathematical
candidate-membership check is not an extra selected source experiment.

[Goldman–Kearns, *On the Complexity of Teaching*, §2, PDF pp. 3–4,
and §3, p. 5](https://www.cis.upenn.edu/~mkearns/papers/teaching.pdf)
define a target-relative labelled sequence that leaves only one consistent
concept. Their general examples may be positive or negative and their
teacher knows the target. Here the concept is the transported relation,
only positive complete pairs are acquired, and the observer follows a
public fixed-slot Read scan. A target-relative existence witness does not
supply target-aware querying or the IID coverage event for free.

[Cavenagh–Wright, *The maximum, supremum and spectrum for critical set
sizes in (0,1)-matrices*, §§1–2, Lemma 4 and Corollary 5](https://arxiv.org/pdf/1812.08282v1)
work with all matrices having prescribed individual row and column sums.
Their defining sets meet every relevant cycle trade, and their critical
sets are inclusion minimal defining sets. That competitor class is not
the two actual graph orbits with unknown injected support labels. Their
numerical bounds and trade criterion are not imported here, and the two
upper bounds do not assert inclusion minimality or minimum size.

[Hatami–Qian, *Teaching dimension, VC dimension, and critical sets in
Latin squares*, introduction, PDF pp. 2–3](https://arxiv.org/pdf/1606.00032v2)
distinguish unique determination from a strong teaching set with iterative
local completion. Their quantitative Latin-square conclusions do not
transfer to (PCR.1). Public exhaustive recognition and a convenient
capacity-completion proof are separate issues here. These source
correspondences establish no world-originality claim for the bounds.

The C105/C106 results in [V96 §§57–69](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md)
assume their actual all-effects filter family, specified preparation and
readout paths, and a common-class continuity or boundary condition. The
stationary Read contract here supplies none of those operations or common
comparison bounds. Those stability results therefore do not provide an
acquisition or recognition bridge for this two-source experiment.

## 追加锚（本行以下为增补区）

## 8. Incidence-only affine recovery and the observable reverse

**Definition 8.1 (acquired quotient and transversal graph).** In this section
$E\subseteq X\times Y$ is the complete relation returned by Definition 1.2,
with surviving source $G_0$. Thus $X\subseteq\mathcal L$ and
$Y\subseteq\mathcal R$ are the actual used label sets, of sizes $72,243$.
All neighbourhoods below are computed from this acquired $E$. Put

$$
L=X/{\approx},\quad x\approx x'\iff N_E(x)=N_E(x'),\qquad
Q=Y/{\sim},\quad y\sim y'\iff N_E(y)=N_E(y').
$$

Retain the computable membership maps $\pi_X:X\to L$, $\pi_Y:Y\to Q$,
their fibres $X_\ell,Y_p$, and the induced incidence
$\bar E\subseteq L\times Q$. For $\ell\in L$ write
$P(\ell)=\{p:(\ell,p)\in\bar E\}$. Define a graph $\Gamma_E$ on $L$:
different vertices $\ell,m$ are joined precisely when

$$
P(\ell)\cap P(m)=\varnothing,\qquad
\bigl|\{n\in L:P(n)\cap P(\ell)\ne\varnothing,
                    \ P(n)\cap P(m)\ne\varnothing\}\bigr|=3.
\tag{RRO.8.1}
$$

The set $\mathfrak P$ of connected components of this graph is the selected
direction set. For each joined pair take the union of the point sets of its
three common transversals; let $\mathcal B$ be the set of these unions,
with repetitions removed. These are definitions by finite incidence tests.
An arbitrary partition of $Q$ by nine disjoint selected lines is not the
definition of a direction. For example, six $e_1$-lines with second
coordinate $0$ or $1$, and three $e_3$-lines with second coordinate $2$,
partition $F^3$ but mix two directions.

**Lemma 8.2 (the graph recovers exactly the four directions).** The quotient
has $27$ points, $36$ selected lines, capacities $|X_\ell|=2$,
$|Y_p|=9$, and $108$ incidences. The four components of $\Gamma_E$ are
exactly the four parallel classes of UJB Theorem 15.2, each with nine lines.
The set $\mathcal B$ consists of the $18$ affine planes whose direction
spaces are spanned by two different selected directions. Given $p\in Q$
and different $D,E'\in\mathfrak P$, there is a unique such plane
$B_{D,E'}(p)$ through $p$, and exactly three lines from each of $D,E'$
lie in it. There is a unique selected line $L_D(p)$ of direction $D$
through $p$.

Proof. Use UJB Theorem 15.2 as a correctness correspondence, rather than
as controller input: its map $\kappa:Q\to F^3$ sends $P(\ell)$ to an
affine line in

$$
K=\{F(0,0,1),F(1,0,0),F(1,2,1),F(1,1,1)\}.
\tag{RRO.8.2}
$$

The stated capacities and incidence counts are that supplier's exact literal
counts. Every three displayed direction vectors are independent: in the
listed order the four three-column determinants are $2,1,2,1$ in $F$.
In particular the four projective points form a frame.

Consider two different parallel lines $a+Fd,b+Fd$ in a direction
$Fd\in K$. For $Fe\in K\setminus\{Fd\}$, an $e$-line meets both
exactly when $b-a\in\operatorname{span}(d,e)$. If this condition holds,
the three $e$-lines through the three points of the first line are distinct,
meet the second, are disjoint, and exhaust that affine plane. If it fails,
there are none. The planes $\operatorname{span}(d,e)$ for the three
choices of $Fe$ intersect pairwise just in $Fd$, by triple independence.
Since $b-a\notin Fd$, at most one choice works. The common-transversal
count is therefore either zero or three, and the latter case is exactly a
join inside this parallel class.

For disjoint lines $a+Fd,b+Fe$ of different selected directions,
$b-a\notin\operatorname{span}(d,e)$. Each of the two other directions
$Ff$ gives a basis $(d,e,f)$. The unique expansion of $b-a$ in that
basis has nonzero $f$ coefficient. It gives exactly one $f$-line meeting
both lines. A line in direction $d$ or $e$ cannot meet both. Thus there
are exactly two common transversals, and no graph edge joins different
parallel classes.

Within a fixed $d$-class, identify its nine lines with $F^3/Fd$.
The graph joins cosets differing by a nonzero multiple of one of the three
other projected directions. Any two of these projected directions span this
two-dimensional quotient, again by triple independence. Moves along them
connect all nine cosets. The components are therefore exactly the four
classes, with no appeal to exact-cover enumeration.

For a joined pair its three transversals exhaust precisely a plane in the
two involved directions. Conversely every translate of
$\operatorname{span}(d,e)$ contains three parallel $d$-lines, so any two
of them produce that plane. There are six different two-direction spaces
and three translates each: a third selected direction belongs to none of
these spaces. This proves the $18$ count and all uniqueness assertions.
It also gives the disjoint-pair transversal histogram: for each direction,
the nine quotient vertices have six neighbours, yielding $27$ unordered
pairs with count three and nine with count zero. Across different directions
there are $6\cdot9\cdot6=324$ disjoint pairs, each with count two.
Hence the counts for $0,2,3$ transversals are $36,324,108$. $\square$

**Definition 8.3 (constructed charts and output representation).** Choose
$o\in Q$, an ordered triple of different selected directions
$(D_1,D_2,D_3)$, and a point $a_i\ne o$ on each $L_{D_i}(o)$.
Set $a_i(0)=o$, $a_i(1)=a_i$, and let $a_i(2)$ be the third point
on this line. Construct

$$
\begin{aligned}
u(x,y)&=L_{D_2}(a_1(x))\cap L_{D_1}(a_2(y)),\\
C(x,y,z)&=L_{D_3}(u(x,y))\cap B_{D_1,D_2}(a_3(z)),
                       \qquad (x,y,z)\in F^3.
\end{aligned}
\tag{RRO.8.3}
$$

Intersections in this formula mean their unique point. A chart is
$\phi=C^{-1}:Q\to F^3$. It retains the mark $D$ on each of the four
selected parallel classes, with coordinate direction
$\delta_\phi(D)\in\mathbb P^2(F)$. These four directions form a frame;
they need not equal the particular set (RRO.8.2). The first three are the
coordinate axes; the fourth has all three coordinates nonzero and depends
on the three chosen nonzero steps. Fixing its representative to $(1,1,1)$
is an optional normalization, not a condition on all constructed charts.
A point output is represented observably by its nine-label fibre $Y_p$,
for example as a sorted list. Its lexicographically first label is an
optional public representative, not the actual hidden $z=0$ label.

**Theorem 8.4 (constructive chart invariance).** All intersections in
(RRO.8.3) exist uniquely and $C$ is a bijection. There are
$27\cdot(4\cdot3\cdot2)\cdot2^3=5184$ constructed chart choices.
The operation

$$
H(p,q,r)=C\bigl(\phi(p)-\phi(q)+\phi(r)\bigr)
\tag{RRO.8.4}
$$

is independent of all these choices, of all twin representative orderings,
and of any coordinate chart that realizes the selected incidence as the
lines of a four-point projective frame over $F$. It is an affine ternary
operation on $Q$ and is equivariant under incidence isomorphisms.

Proof. Under the correctness map $\kappa$ of Lemma 8.2 let
$b=\kappa(o)$ and $v_i=\kappa(a_i)-b$. Each $v_i$ is nonzero,
and the three are independent. The remaining point on its axis is
$b+2v_i$. Lemma 8.2 identifies the first intersection in (RRO.8.3) as
$b+xv_1+yv_2$. Its $v_3$-line meets the plane
$b+zv_3+\operatorname{span}(v_1,v_2)$ at exactly one point. Consequently

$$
\kappa(C(x,y,z))=b+xv_1+yv_2+zv_3.
\tag{RRO.8.5}
$$

This proves existence, uniqueness and bijectivity, and proves every
constructed chart is affine relative to the source correspondence.
Inserting (RRO.8.5) into (RRO.8.4) yields

$$
\kappa(H(p,q,r))=\kappa(p)-\kappa(q)+\kappa(r),
\tag{RRO.8.6}
$$

which contains none of the choices. The three independent direction choices,
the origin, and the two choices on each axis give the displayed count.
Each construction uses only incidence, graph components and intersections.
Thus an incidence isomorphism carries a chosen construction to the
construction with the image origin, directions and axis points, proving
equivariance without access to $\kappa$.

More generally, let $\psi:Q\to F^3$ be any chart realizing the four
selected classes as a frame of affine directions. The proofs of Lemma 8.2
apply in those coordinates because they used only triple independence.
The same incidence construction then gives
$\psi(C(x,y,z))=b'+xv'_1+yv'_2+zv'_3$ with independent $v'_i$.
Comparing with (RRO.8.5) proves $\psi\kappa^{-1}$ is affine. An affine
change $f(x)=Ax+b$ satisfies
$f(x)-f(y)+f(z)=f(x-y+z)$; hence it gives exactly the same $H$.
This also proves uniqueness among $F_3$ affine torsor structures in which
the selected incidence realizes a four-direction frame. No claim of
uniqueness among arbitrary ternary tables satisfying only a few identities
is needed. Reordering labels inside fibres changes no incidence object.
Finally (RRO.8.6) proves
$H(p,q,q)=p$, $H(p,p,r)=r$, $H(p,q,r)=H(r,q,p)$ and
$H(H(p,q,r),s,t)=H(p,q,H(r,s,t))$ by coordinate cancellation.
Choosing any origin turns this torsor into a vector space over $F$,
without distinguishing that origin intrinsically. $\square$

**Theorem 8.5 (full affine lines, planes and incidence).** For $p\ne q$
define

$$
\ell(p,q)=\{p,q,H(q,p,q)\}.
\tag{RRO.8.7}
$$

For $r\notin\ell(p,q)$ define $\Pi(p,q,r)$ as the smallest subset
containing $p,q,r$ and closed under $H$. Then the distinct sets
$\ell(p,q)$ are exactly the $117$ full affine lines, in $13$ parallel
classes of nine. The distinct $\Pi(p,q,r)$ are exactly the $39$ full
affine planes, with nine points each. Point-line, point-plane and line-plane
incidence are respectively membership, membership and containment. Each
point lies on $13$ full lines, each plane contains $12$ full lines, and
each full line lies in four planes. All of these objects are independent of
charts. The four selected classes remain marked among the thirteen; each
original $P(\ell)$ is its corresponding full line.

Proof. In any constructed chart write $a=\phi(p)$ and
$d=\phi(q)-a$. Formula (RRO.8.7) is exactly
$\{a,a+d,a+2d\}=a+Fd$, including its third distinct point.
For a nonempty $H$-closed set $S$ and $a\in\phi(S)$, its translate
$V=\phi(S)-a$ contains zero, is closed under
$u+v$ by $H(u+a,a,v+a)$, and under negation by $H(a,u+a,a)$.
It is therefore an $F_3$ vector subspace. Conversely every coset of an
$F_3$ subspace is $H$-closed. It follows that

$$
\phi(\Pi(p,q,r))
 =\{a+x(\phi(q)-a)+y(\phi(r)-a):x,y\in F\}.
\tag{RRO.8.8}
$$

The noncollinearity condition makes its two generators independent, so it
has nine points and is precisely an affine plane. Every line and plane has
such generators, proving exhaustiveness rather than just producing some
incidences. The same argument recovers every affine flat by $H$-closure.

There are $(3^3-1)/(3-1)=13$ one-dimensional subspaces, each with nine
cosets. Two-dimensional subspaces are kernels of nonzero linear forms,
where precisely the two nonzero scalar multiples give the same kernel.
There are therefore $26/2=13$ plane directions and three cosets each.
Within a plane its four directions have three line cosets each. Plane
directions containing a fixed line direction correspond to the four
one-dimensional subspaces of the two-dimensional quotient. These counts
prove all asserted incidence numbers. Lemma 8.2 and (RRO.8.5) identify
the original $36$ blocks with the lines in the four selected directions.
Because definitions (RRO.8.7) and $H$-closure use the invariant $H$, their
sets and incidences are chart independent. $\square$

**Theorem 8.6 (observable literal reverse).** Retain $X,Y$, the actual
membership maps $\pi_X,\pi_Y$, their labelled fibres, the selected class
marks and the incidence of the $36$ selected full lines with $Q$. Define

$$
\operatorname{Lift}(\bar E,\pi_X,\pi_Y)
 =\{(x,y)\in X\times Y:(\pi_X(x),\pi_Y(y))\in\bar E\}
 =\bigcup_{(\ell,p)\in\bar E}X_\ell\times Y_p.
\tag{RRO.8.9}
$$

This lift is exactly $E$. Its twin quotient returns the same incidence,
capacities and selected direction marks. Thus full geometry with the four
selected classes and these attachments reverses to the literal label
relation. The full affine geometry by itself omits which four of its
thirteen directions were supplied and which labels attach to each line and
point; those fields are retained in this inverse.

Proof. If an edge has representatives $x,y$, changing $x$ inside its
left fibre preserves adjacency to $y$. Changing $y$ inside its right
fibre then preserves adjacency to the new $x$. Hence every incident
class pair lifts to the entire product of its fibres, and a nonincident
class pair lifts to none. This proves both inclusions in (RRO.8.9).
Taking equal neighbourhoods of this same $E$ recovers the defining
classes, and (RRO.8.1) recovers their marks. Each of $108$ incidences
lifts to $2\cdot9$ distinct edges, giving $1944$ in total.
For correctness only, if hidden injections $\lambda,\varrho$ transport
$E_0$ to $E$, the observable maps satisfy
$\pi_X(\lambda(v,s))=[(v,s)]$ and
$\pi_Y(\varrho(w,z))=[w]$ under the UJB identification. This is a
commuting correspondence with a hidden witness, not an extra input to the
lift. Neither map requires recovering those injections. $\square$

**Proposition 8.7 (lawful controller and separate costs).** A common
controller under UJB Assumption 5.2 can, on a successful positive
certificate scan, compute the preceding objects and compute $H$ on right
point classes of subsequently acquired input records. It returns the output
fibre $Y_{H(p,q,r)}$, or an explicitly declared public representative.
If input indices repeat, it uses the same acquired record on every
occurrence. The stationary original root and its original Read menu are
unchanged.

Proof. Install the finite recognition, graph and chart algorithms from the
public source tables and public $N$ only. On the acquired scan records run
Definition 1.2. Failure is a declared output; on success the returned $E$
and its surviving branch determine whether the $G_0$ construction applies.
Every later required input bit at original slot $j$, local coordinate $h$,
is acquired by the original decoder address in PCR.6, or reused from that
slot's cache. Right labels give $p=\pi_Y(y_j)$ directly; complete pairs
may also be retained for the reverse and inversion below. All subsequent
steps are finite computations on acquired records. No source-dependent
controller installation, hidden reference, chosen-label query or group
operation occurs. Multiple operands at one index refer to one $Y_j$.
UJB Theorem 17.1 supplies every adaptive continuation law with these very
masks, including deterministic replay. $\square$

Here are explicit finite computation bounds, independent of acquisition.
After $E$ is supplied, a $72$ by $243$ Boolean table suffices to compute
all neighbourhoods and memberships; sorting or comparing those bit rows
and columns adds its own finite work. After quotienting, there are
$\binom{36}{2}=630$ pairs and at most $630\cdot36=22680$ candidate
transversal tests, each involving two intersections of three-point sets.
Connected components, the $18$ plane sets, the $108$ point-direction
entries and the $162$ point/two-direction plane entries are finite tables.
One chart uses nine first intersections and $27$ second intersections;
enumerating all $5184$ choices uses at most $5184\cdot36=186624$
such singleton-intersection operations after these tables are present.
Only one chart and its inverse need be stored to evaluate $H$; storing its
entire table instead uses $27^3=19683$ point entries. Enumerating all point
pairs and all noncollinear triples recovers the full line and plane sets;
the resulting membership tables have $117\cdot3$ and $39\cdot9$
point entries. Comparisons, deduplication, arithmetic on indices and
coordinate words, and output storage are additional computation. These
bounds give no optimality or efficient-discovery claim.

Acquisition is the original tariff. A scan of slots $1,\ldots,m\le N$
that completes every pair makes $15m$ Read invocations, with operand-length
sum $15m(15m+3)/2$ and maximum length $15m+1$ by PCR.6. At $m=576$
these are $8640$, $37337760$, and $8641$. Completing a later partial
slot pays for its missing coordinates at their original addresses; an
invoked reread still costs an invocation even if it adds no information.
Input records, the fixed $N$ originally prepared slots, preparation events,
installation, mathematical computation and memory are separate resources.
An existence certificate does not promise that a fixed scan attains it;
$H$ creates neither a sample nor a Read reply.

## 9. Inversion and the full indexed conditional law

**Definition 9.1 (source inverse target).** In FGP, equations (1.2)--(1.3),
embed $a=(v,s)\in A$, $t=(w,z)\in T$ as
$\widetilde a=(v,0,s;0)$, $\widetilde t=(0,w,z;1)$.
Their two products have last vector coordinates
$s+z+B_i(v,w)$ and $z-s$ respectively; hence

$$
\widetilde a\widetilde t=\widetilde t\widetilde a
 \iff B_i(v,w)=s,\qquad
\iota(v,s)=(-v,-s),\qquad \widetilde t^{-1}=\widetilde t.
\tag{RRO.9.1}
$$

In particular $(a,t)\mapsto(\iota(a),t)$ is an involutive permutation
of $E_i$. For a full generator $g=(i,\lambda,\varrho)$ define its
label inverse target on $\mathcal E_g$ by

$$
J_g(x,y)=(\lambda(\iota(\lambda^{-1}(x))),y).
\tag{RRO.9.2}
$$

The first component alone is denoted $I_g(x)$. These are mathematical
targets associated to the actual paired-power witness; the observer is not
supplied an inversion port.

**Theorem 9.2 (fixed-input recovery and ambiguity).** For a certified $G_0$
relation and acquired edge $(x,y)$, $I_g(x)$ is the other member of
$X_{\pi_X(x)}$, so $J_g(x,y)$ is computable from acquired information.
If $G_1$ has positive prior weight, then for every transported $G_1$
relation and every input edge there are full supported realizations with
that same $E$, the same entire prepared label array containing the input,
and different inverse labels for that input. This holds at every fixed
$N\ge4$ for any prescribed such array.

Proof. In $G_0$, the exact left fibre in UJB Theorem 15.2 is
$\{(v,s),(-v,-s)\}$. Its members differ since $v\ne0$, and
(RRO.9.1) identifies the other member as the inverse.

For $G_1$, identify $F^2$ with $E_9=F[\iota]$, where
$\iota^2=-1$. A left fibre is
$C_c=\{(v,cv):v\in E_9^\times\}$, of size eight, and inversion
pairs $a$ with $-a$ inside it. For the actual literal preimage $a$ of
$x$, choose $b\in C_c\setminus\{a,-a\}$ and let $\sigma$
transpose $a,b$, fixing all other left endpoints. This preserves the
whole edge relation. Put $\lambda'=\lambda\circ\sigma$ and leave
$\varrho$ unchanged. Every prepared label pair remains exactly the same
by using its corresponding preimage under the new injection. All those
preimages remain edges. The two generators have positive full-injection
prior mass when $\theta>0$, and each compatible length-$N$ array has
conditional mass $M^{-N}>0$.

In the second realization the input $x$ has preimage $b$ and inverse
label $\lambda'(-b)=\lambda(-b)$; in the first it has inverse label
$\lambda(-a)$. The four endpoints $a,b,-a,-b$ are distinct, so these
outputs differ. All observed bits at all indices, including repeats, are
identical. Thus the failure is pointwise even with the full label array,
and cannot be removed by a more informative Read of that same array.
$\square$

**Definition 9.3 (actual finite measure on the full domain).** No
certification of $E$ is assumed in this definition or in Theorems 9.4--9.5.
Fix public $N,\theta$ and the full original prior of UJB.9001. With
$(q)_r=q(q-1)\cdots(q-r+1)$, let

$$
\pi_\theta(g)=\frac{w_i}{(128)_{72}(256)_{243}},\quad
w_0=1-\theta,\quad w_1=\theta,\qquad
\mu(g,\mathbf y)=\pi_\theta(g)M^{-N}
                 \prod_{j=1}^N\mathbf1_{\{y_j\in\mathcal E_g\}}.
\tag{RRO.9.3}
$$

Here $g$ ranges over both sources and all full injections; zero-weight
sources are omitted. The label array ranges over
$(\mathcal L\times\mathcal R)^N$, with one variable per original
index. This is a probability measure because every $\mathcal E_g$ has
$M=1944$ distinct edges. For any consistent indexed cache
$D=((m_j,d_j))_{j=1}^N$, with arbitrary masks in its fifteen coordinates,
write

$$
\begin{aligned}
A_j(g,D)&=\{y\in\mathcal E_g:y|_{m_j}=d_j\},\qquad n_j(g,D)=|A_j(g,D)|,\\
L_g(D)&=\prod_{j=1}^N\frac{n_j(g,D)}M,\qquad
Z(D)=\sum_g\pi_\theta(g)L_g(D),\\
W_D(g)&=\frac{\pi_\theta(g)L_g(D)}{Z(D)},\qquad
Q_{g,j,D}(y)=\frac{\mathbf1_{\{y\in A_j(g,D)\}}}{n_j(g,D)}.
\end{aligned}
\tag{RRO.9.4}
$$

The domain is exactly $Z(D)>0$. The last factor is used only when
$W_D(g)>0$, where all its denominators are positive. Empty masks have
$n_j=M$; a completed supported slot has $n_j=1$. Contradictory evidence
has zero normalizer and no conditional law. Duplicate observations impose
one restriction while their actual invocations retain their costs.

**Theorem 9.4 (normalized joint target pushforward).** Let $S\subseteq[N]$
be any set of distinct target indices. Let
$F(g,(y_j)_{j\in S})$ be any deterministic finite-valued target or vector
of targets, with repeated requested indices evaluated using that same
$y_j$. Then its actual law conditional on any positive cache is

$$
\begin{aligned}
\Pr(F=z\mid D)
 &=\frac{\sum_{g,\mathbf y}\mu(g,\mathbf y)
       \mathbf1_{\{\mathbf y\text{ satisfies }D\}}
       \mathbf1_{\{F(g,\mathbf y_S)=z\}}}{Z(D)}\\
 &=\sum_{g:W_D(g)>0}W_D(g)
   \sum_{(y_j)\in\prod_{j\in S}A_j(g,D)}
       \left(\prod_{j\in S}\frac1{n_j(g,D)}\right)
       \mathbf1_{\{F(g,\mathbf y_S)=z\}}.
\end{aligned}
\tag{RRO.9.5}
$$

This includes joint inverse targets at partial, complete and wholly unread
slots, regardless of whether $E$ is certified. It also includes geometric
targets and their joint laws with inverses as follows. On $i=0$, construct
$Q_g,H_g,\pi_{Y,g}$ from the candidate relation $\mathcal E_g$ by §8,
and encode a geometric output for indices $j,k,l$ as

$$
G_g(j,k,l)=Y^g_{H_g(\pi_{Y,g}(y_j^{R}),
                              \pi_{Y,g}(y_k^{R}),
                              \pi_{Y,g}(y_l^{R}))}.
\tag{RRO.9.6}
$$

This is a nine-element subset of the fixed ambient $\mathcal R$; it is
not a point name in an unshared hidden chart. On $i=1$ give this target
the separate failure tag $\bot$. Thus (RRO.9.5) defines the joint law on
the full original domain, including uncertainty about the source. A law
conditional also on $i=0$ instead restricts the sums to that event and
divides by its positive conditional probability. It does not assume that
an uncertified actual $E$ was acquired.

Proof. Summing $\mu$ over arrays satisfying $D$ factors into $N$
independent edge counts and gives exactly $Z(D)$. Conditional on a fixed
$g$ and $D$, the array coordinates are independent and uniform on their
own $A_j(g,D)$, proving (RRO.9.4). Summing out all indices outside $S$
gives one from each normalized coordinate factor, proving the second line
of (RRO.9.5). The first line is the direct event-indicator formula for the
same measure. Summing either expression over all outputs gives one, since
exactly one output indicator is true for each realized tuple.

The target vector uses a single $g$, so every component shares the same
source, full injections and inverse pairing. It uses one edge variable for
each distinct original index, so no occurrence is independently resampled.
For example, $(J_g(Y_j),J_g(Y_j))$ is supported on the diagonal and
$(J_g(Y_j),J_g(J_g(Y_j)))=(J_g(Y_j),Y_j)$ holds identically.
For different indices the factors separate only conditional on $g,D$;
the outer sum is still joint. Formula (RRO.9.6) is well-defined by the
chart invariance of Theorem 8.4 on each candidate $G_0$ relation. Applying
the preceding finite pushforward to it, or to it together with any inverse
coordinates, proves the remaining statements. $\square$

For a single partial slot the inverse formula is, explicitly,

$$
\Pr(J_g(Y_j)=u\mid D)
 =\sum_{g:W_D(g)>0} W_D(g)\frac{
       |\{y\in A_j(g,D):J_g(y)=u\}|}{n_j(g,D)}.
\tag{RRO.9.7}
$$

The indexed likelihood is already in $W_D$; the inner conditional count
is divided by $n_j$. Equivalently the full-array sum in the first line
of (RRO.9.5) uses $\mu$ and the cache indicator once, with no further
likelihood factor. A separately acquired fixed input is included by adding
its complete indexed record to $D$; if it is merely a proposed edge,
conditioning on its presence is an additional event, not an unannounced
premise. The formulas compute mathematical target laws. Theorem 9.2
prevents a $G_1$ latent inverse from being treated as a readable output
merely because its posterior can be evaluated.

**Theorem 9.5 (compatibility with native continuation).** Marginalizing
(RRO.9.5) to array coordinates gives exactly UJB.9005 and UJB.17002.
Conjoining new indexed masks gives the original ratio
$Z(D\wedge D')/Z(D)$ of UJB.17001, including original repeated indices.
Thus all native continuation laws, deterministic derived readouts of
acquired records, and their joint outputs are computed on the same actual
measure. No latent target becomes an observer port by this identity.

Proof. Taking the target to be the array itself gives the mixture of
$\prod_jQ_{g,j,D}$ with weights $W_D$, which is precisely UJB.9005.
The numerator for a new cylinder is its intersection with the old one,
so its mass is $Z(D\wedge D')$. A repeated known bit conjoins nothing
new and has conditional probability one; a contrary repeat has numerator
zero. Completing an old partial slot replaces its factor by the full
restriction in the same product, rather than multiplying a second partial
likelihood. UJB Theorem 16.2 evaluates these very normalizers with literal
capacities, and Theorem 17.1 supplies its exhaustive original-root operand
classification and controller composition. For any attained native
transcript under Assumption 5.2, UJB Proposition 9.2 proves its
controller/seed likelihood is constant across all arrays satisfying its
cache, so the source-dependent conditional law is the one above. For a
further common controller with array-indexed transcript measure $K_y$,
its observable continuation law is the unchanged finite mixture
$\sum_y\mathsf I_D(y)K_y$ of UJB.17003. A deterministic output computed
from actually acquired $E$ and inputs can be appended to that transcript.
An output depending on an unidentified $g$ has only the mathematical
pushforward (RRO.9.5) until a lawful acquisition proves it constant on the
observation fibre. $\square$

The formulas are exact finite expressions in the public $\theta$.
For rational $\theta$ and finite explicitly represented rational controller
weights, exhaustive enumeration terminates in rational arithmetic. With an
arbitrary real parameter they remain identities; no effective arithmetic
on an unrepresented real or arbitrary measurable controller measure is
assumed. One direct bound enumerates
$2(128)_{72}(256)_{243}$ generators, with unsupported branches omitted,
constructs $1944$ edges per generator, and tests their masks at all $N$
indices. For targets at $s$ distinct indices the inner product has at most
$1944^s$ edge assignments per generator. Full-array enumeration has at
most $1944^N$ per generator. Streaming can avoid retaining all assignments;
weights, growing integers, target computation and output storage still cost
resources. These are mathematical computation bounds, not additional
Reads or an acquisition saving. The existing capacity evaluator is reused
for the normalizers; no claim that it alone identifies a hidden inverse
matching is made.

**Proposition 9.6 (unread marginals and shared inverse matchings).** At
fixed $g$, $J_g$ permutes the $1944$ edges. A wholly unread original
slot therefore has the same conditional marginal law after applying $J_g$
as before applying it, even after averaging over $W_D$. At fixed $g$ its
inverse left endpoint is uniform on the $72$ used left labels. The latter
statement does not assert conditional uniformity over those labels after
arbitrary partial evidence, nor over a single shared set of $72$ labels
when that set itself is uncertain.

On a certified $G_1$ relation, for any positive indexed cache of label bits,
the latent inverse pairing inside each size-eight left fibre is uniform
among its $105$ perfect matchings, and the nine such pairings are independent.
For a fixed left input, each of the seven other labels has inverse
probability $1/7$. For distinct $x,x'$ in that fibre,

$$
\Pr(I(x)=x',I(x')=x\mid E,D)=1/7,
\tag{RRO.9.8}
$$

not $1/49$. A repeated request for the same input has the same inverse
with probability one. These certified-$E$ simplifications are special
cases of (RRO.9.5), not its general domain.

Proof. Bilinearity gives $B_i(-v,w)=-s$, so $J_g$ is an edge involution
with no fixed left endpoint. Every left endpoint has degree $27$.
An unread slot has $Q_{g,j,D}=M^{-1}\mathbf1_{\mathcal E_g}$;
pushing it through this permutation preserves that law, and then so does
the outer mixture. Conditioning a partially read input can break this
uniformity because its allowed edge set need not be invariant under $J_g$.

For a fixed $G_1$ labelled relation, every compatible generator gives
exactly the same likelihood $\prod_j|E\cap B_j(D)|/M$. It therefore
cancels from the conditional distribution of hidden associations within
that relation. The component decomposition is nine disjoint complete
bipartite graphs with capacities $8,27$. Given the component association,
all $8!$ bijections on each left fibre are independent and uniform, as are
all right bijections; permuting whole components leaves the following
local calculation unchanged. A fixed involution of four unordered pairs
transports to each perfect matching under exactly $2^4\cdot4!=384$
bijections. Hence the $8!/384=105$ matchings have equal mass, independently
in each fibre. There are $15$ matchings with a prescribed partner of $x$.
If $x$ is paired with $x'$, involutivity also pairs $x'$ with $x$;
this proves (RRO.9.8). The same matching is used on all indices and targets.
$\square$

**Example 9.7 (actual full-injection partial evidence).** The following
exact calculations use $\theta=0$, $N=4$ and the original ambient
$128$ left labels. They do not replace the source by a smaller model.
Let $K$ be the number of used left labels with first bit zero. Before
conditioning, $K\sim\operatorname{Hypergeom}(128,64,72)$.
If only that bit of slot two is acquired as zero, its likelihood is
$K/72$. Given the used label set, the input label is uniform on its $K$
zero-bit labels and its distinct inverse partner is uniform on the other
$71$ used labels by exchangeability of the full injection. Thus

$$
\Pr(\operatorname{bit}_1(I_g(Y_2^L))=0\mid \operatorname{bit}_1(Y_2^L)=0)
 =\frac{\mathbb E[K(K-1)]}{71\mathbb E[K]}=\frac{63}{127}.
\tag{RRO.9.9}
$$

Here $\operatorname{bit}_1$ reads the first bit of a left label. The
ratio follows also by choosing two distinct labels uniformly from $128$:
after a zero-bit
first label, exactly $63$ of the remaining $127$ have that bit zero.
A second multiplication by the likelihood instead gives the different
ratio $\mathbb E[K^2(K-1)]/(71\mathbb E[K^2])=287/575$.

If slot one is acquired completely as the pair $(0,0)$ of all-zero left
and right words, then under that event
$K=1+H$ with $H\sim\operatorname{Hypergeom}(127,63,71)$: the left
image contains zero, and its other $71$ labels are a uniform subset of the
remaining $127$. The right-edge constraint does not distinguish these
remaining label names. Now additionally acquire just the first left bit
of slot two as zero, leaving slots three and four unread. The inverse
partner of slot one's left label, conditional on this image, is uniform
among its other $71$ labels. The correct probability that this partner has
first bit zero is

$$
\frac{\mathbb E[K(K-1)]}{71\mathbb E[K]}=\frac{287}{575}.
\tag{RRO.9.10}
$$

Using the slot-two likelihood twice would instead give
$\mathbb E[K^2(K-1)]/(71\mathbb E[K^2])=32879/65475$,
whose difference from (RRO.9.10) is $4564/1505925>0$.
These evaluations follow from the hypergeometric factorial-moment identity
$\mathbb E[(H)_r]=(71)_r(63)_r/(127)_r$, and its
$(128,64,72)$ counterpart for (RRO.9.9). To prove that identity, count
ordered $r$-tuples of distinct marked population elements: each is included
in the uniform subset with probability $(71)_r/(127)_r$, and there are
$(63)_r$ such tuples. Expanding $K^2$ and $K^2(K-1)$ into factorial
powers gives the displayed rational values. These positive-cache examples
explain why full-realization event conditioning and normalized per-slot
conditioning must agree; an extra evidence factor changes the law.

## 10. References, retained memory and absent operations

**Proposition 10.1 (actual hidden references remain unidentified).** The
observable recovery of §8 does not recover the source's actual origin,
actual injections or its within-point right-twin reference.

Proof. For any $d\in F^3$, the simultaneous source permutations

$$
(v,s)\mapsto(v,s+B_0(v,d)),\qquad (w,z)\mapsto(w+d,z)
\tag{RRO.10.1}
$$

preserve $E_0$ by bilinearity. Compensate both full injections by the
inverse permutations and transport every literal prepared edge accordingly.
The complete labelled relation and every prepared label pair remain
unchanged, while a nonzero $d$ changes the actual coordinate origin's
label attachment. Both full-injection realizations have positive prior
weight whenever $G_0$ is supported, and all those arrays have the same
mass. Thus even completing every prepared slot cannot identify that
hidden reference. Independently, transposing any two of the nine right
endpoints $(w,z)$ at one fixed $w$, and compensating the right injection,
preserves all label observations while changing the actual $z$ attachment.
The operation $H$ is invariant under these alternatives. A publicly chosen
origin or output representative is a convention on acquired label sets;
it does not distinguish the actual hidden alternative. $\square$

**Proposition 10.2 (memory, history and G1 geometry boundaries).** The
following are failures of recovery under the stated forgetful maps.

1. Retaining $E$, an unordered set of completed pairs and the posterior of
   the full generator does not retain the completed slots' indexed replay.
2. A promised native endpoint determines its labelled generation order and
   its set of successful histories in the existing supplier domain, but
   does not determine the actual serial preparation word.
3. The $G_1$ literal relation is nine disjoint $K_{8,27}$ components;
   its twin quotient has nine left classes, nine right classes, and nine
   matching incidences, each a $K_{1,1}$. It does not supply an intrinsic
   $F_3$ affine plane on its nine components or the $G_0$ affine torsor.

Proof. For item 1 take $N\ge4$, different complete pairs $u,v$ of one
supported relation, and arrays with slots one and two respectively
$(u,v)$ and $(v,u)$, leaving at least slot three unread. Both events
have likelihood $M^{-2}\mathbf1_{\{u,v\in\mathcal E_g\}}$ for
every generator. Thus their generator posteriors, unordered completed sets
and joint unread laws coincide. Reading a differing bit of slot one gives
different deterministic replies. The original index record distinguishes
them, as UJB Theorem 17.1 requires.

For item 2, `NativePromiseCausalBoundary.result` has hypotheses
$N\ge4$ and the full promised assignment $z:\operatorname{Fin}(15N)\to
\mathsf{Bool}$. It characterizes all successful serial words by labelled
event linear extensions and gives two distinct successful words at the same
endpoint. Retaining the endpoint, or any quotient of it, therefore cannot
choose which word actually occurred. Recovering the entire set of possible
histories is different from selecting the actual one.

For item 3, UJB Theorem 15.2 identifies component value
$c=s/v=w_1+\iota w_2\in E_9$. Each component contains eight literal
left endpoints and $3\cdot9=27$ right endpoints; all free $w_3,z$
values remain. Arbitrary simultaneous permutations of whole components
preserve the incidence, as do arbitrary permutations within their twin
fibres. If a natural affine plane on the nine anonymous components were
recovered from incidence alone, every such permutation would preserve its
ternary operation. A transposition of two components fixes seven points.
A nonidentity affine map of $F_3^2$ has either no fixed point or a fixed
affine subspace of dimension at most one, hence at most three fixed points:
its fixed-point equation is $(A-I)x=-b$, and a two-dimensional solution
space would force the identity. Such a transposition cannot be affine.
Thus even the component-plane structure suggested by a hidden field chart
is not an invariant of this anonymous relation. $\square$

**Theorem 10.3 (retained interfaces and limits).** The exact domains are:

(a) A certified complete $G_0$ relation with its acquired label attachments
recovers $H$ and full affine incidence by §§8.1--8.5. Retaining the four
selected classes and the membership maps reverses to $E$ by Theorem 8.6.
Acquired right input records suffice for the controller's point-valued
operation. Complete edge records also allow its $G_0$ inverse target.

(b) Every positive attained indexed cache, including uncertified relations,
partial slots and repeated indices, has the full joint laws of §§9.3--9.5.
These preserve the one shared generator and all original array indices.
For the support-closure inverse of UJB Theorem 17.2, additionally retain the
fixed public prior, fixed partial cache and indexed completed values, and
require at least one completely unread slot. Without that last condition
the unread law can be an empty product; it has no claimed general inverse.
The direct indexed law still evaluates the remaining old-slot Reads.

(c) For a fixed $G_1$ input $x$, retaining its actual partner label suffices
to evaluate $I_g(x)$. For the whole inverse interface on all used labels,
retaining one actual inverse matching in each left fibre suffices. These are
sufficient extra data, not minimal reference claims. The relation and even
the complete prepared label array fail to supply the fixed input's partner
by Theorem 9.2; a distribution of partners is not a realized partner.

(d) An actual serial word requires information distinguishing the legal
linear extensions, together with an authorized history-readout contract.
The static relation and the stationary Read endpoint supply no such port.
The equations defining $B_i$, $H$ or $J_g$ introduce no source mutation,
multiplication/inversion call, extra prepared sample, fresh randomness or
quantum channel.

Proof. Parts (a)--(c) assemble the indicated constructions on exactly their
input domains. In (c) applying the retained partner map, or the retained
matching at the input label, computes the target; Theorem 9.2 proves failure
without the missing datum. Part (d) follows from Proposition 10.2 and the
exclusive original-root Read contract of UJB Assumption 5.2. Its controller
has only that declared source port; computing a mathematical relation on
records cannot add a permitted action. $\square$

## 11. Source correspondences and mathematical scope

**Definition 11.1 (reused suppliers and their parameters).** The source
correspondences used here are the following.

* UJB Theorem 15.2 identifies $Q$ with the actual $w\in F^3$ point
  coordinate and $L$ with the solution lines of $B_0(v,w)=s$, identifies
  the four kernels (RRO.8.2), and supplies their $2,9$ capacities. For
  $G_1$ it supplies the component equation $s/v=w_1+\iota w_2$ with
  capacities $8,27$, retaining every $w_3,z$. This is the correctness
  map in the incidence proof; it is not a controller input.
* UJB.9001--UJB.9005 give the full shared-injection probability measure:
  $\pi_\theta$ is unchanged, $n_j/M$ is its $r_j(g;D)$,
  $W_D=\pi_D$, and $Q_{g,j,D}$ is exactly its normalized indexed
  factor. UJB Theorem 16.2 supplies capacity evaluation of $Z$ for every
  cache. Theorems 17.1--17.2 supply updates, original-index replay,
  controller continuation and the fixed-partial-cache/unread inverse.
  No capacity or quotient compression removes the latent association
  required by the targets $J_g$.
* FGP equations (1.2)--(1.3), (3.4), (3.6)--(3.7), and UJB Proposition
  3.2 identify the actual $4374$-element groups and the order-six
  paired-power bijection onto the $1944$ edges, with all $72,243$
  endpoints. The commuting interpretation and inverse edge target use
  these embeddings; an abstract relation edge is not a supplied group call.
* Cara--Rottey--Van de Voorde,
  [arXiv:1207.4726v3, Corollary 3.7](https://arxiv.org/abs/1207.4726v3),
  supplies the general point-preserving rigidity theorem for
  $T_2^*(K)$ with $q>2$, full subgeometry closure and Property $(*)$.
  Here $q=3$; the four determinants in Lemma 8.2 prove the frame
  hypothesis. Its smallest subgeometry is all $\operatorname{PG}(2,3)$
  because $F_3$ has no proper subfield. Property $(*)$ excludes an
  intersection equal to two intersecting projective lines, with or without
  their intersection point. Such sets have seven or six points over $F_3$,
  whereas $K$ has four. The point and line sorts here are retained, so
  Corollary 3.7, rather than an unverified sort-exchange condition from the
  incidence-graph version in Corollary 3.6, is the applicable supplier.
  Its ambient hyperplane stabilizer restricts to an affine semilinear map;
  the field automorphism over $F_3$ is trivial. De Winter--Rottey--Van de
  Voorde, [arXiv:1407.3953v1, introduction and §2](https://arxiv.org/abs/1407.3953v1),
  gives the frame and smallest-subgeometry terminology. Theorem 8.4 also
  gives the explicit incidence construction in this finite instance. This
  is an application of established affine rigidity, not a new general
  rigidity claim; neither paper supplies acquired labels or Read tariffs.
* [`InvolutionDescent.kernelStable_iff_exists_descended`](../../../D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent.lean)
  takes a surjective readout and a transformation preserving its fibres;
  `descended_unique` gives uniqueness of its induced quotient map. Here
  inversion preserves each left twin fibre in both sources, so its induced
  action on $L$ is the identity. This says nothing about selecting a label
  within that fibre. Size two in $G_0$, together with no fixed point,
  selects the other label; size eight in $G_1$ leaves the ambiguity proved
  in Theorem 9.2.
* [`TargetRecoveryCriterion.target_recovery_criterion`](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)
  states constancy of a target on readout fibres exactly when it factors
  through that readout. For the inverse target take states to be supported
  full generators and prepared arrays with the input index retained, and
  the readout to be $(E,\mathbf y)$ or its acquired subrecord. Theorem
  9.2 supplies constancy for certified $G_0$ with acquired input and a
  pair of differing targets on one $G_1$ readout fibre.
  [`PushforwardComposition.pushforward_comp`](../../../D5/S3/Entropy/Forgetting/PushforwardComposition.lean)
  is finite real-mass pushforward composition. Its correspondence is the
  two equal summation orders in (RRO.9.5); it never authorizes independent
  redraws of the hidden generator for different outputs.
* [`ActualTreeReadoutAcquisition.readout`](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
  has an actual finite address and four possible replies. In UJB the
  decoder address extracts a designated bit of the same stationary comb;
  acquisition and address costs stay as in PCR.6. The hypotheses and final
  existential clause of
  [`NativePromiseCausalBoundary.result`](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativePromiseCausalBoundary.lean)
  are exactly those stated in Proposition 10.2, with $N\ge4$. These are
  source correspondences, not fresh compiled Lean applications.
* Existing RRO Proposition 92.2 in
  AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II is a support-safe
  variational supplier: restrict a norm calculation to the actual support
  before taking the indicated inverse. It supplies no omitted fibre or
  observer action here. C107 in
  [AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96,
  Definitions 70.1--70.2 and Theorem 72.2](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md)
  retains actual completely positive success branches, their success effects,
  common dimming, collective binary-cut bounds and the same calibration
  preparation/readout paths. Its joint boundary relation is a condition on
  that whole common comparison class, not on separate optimizers.
  [`StaticTensorWorld`](../../../D5/S3/Quantum/Foundation/StaticTensorWorld.lean)
  instead supplies finite positive Frobenius comparison objects with zero
  action and actual carrier equivalences to real tensor products; its
  `result` refutes universal associativity even under all finite static
  closure. Neither structure is supplied by this incidence and Read
  contract. Their mathematical tensor or preparation data cannot be inferred
  from recovered affine incidence, and they supply no quantum/random port.

**Proposition 11.2 (falsification polarity and retained scope).** The
positive recovery statements would fail if an actual transported $G_0$
relation violated Lemma 8.2, if (RRO.8.3) had a non-singleton required
intersection, if two allowed charts gave different $H$, if full affine
incidence differed from Theorem 8.5, if the observable lift differed from
$E$, or if conditional event summation disagreed with (RRO.9.5) on a
positive original cache. The mixed-direction cover in Definition 8.1
illustrates why a disjoint cover is insufficient to define a direction.
The $G_1$ differing-inverse pair and the distinct serial words at one
endpoint support the respective non-recovery statements; they are not
falsifiers of them. Refuting those negative statements would require
invalidating their witnesses under the stated source and Read assumptions.

The incidence construction and literal/indexed interfaces are ordinary
finite mathematical consequences for these actual sources, with the
literature and repository suppliers mapped above. They are not fresh Lean
verification, a novelty certificate, an optimal reference or certificate
catalogue, an acquisition improvement, or a physical spacetime claim.
All positive supported full injections, fixed finite $N$, masks and original
indices remain in the law's domain. Further recovery of an actual reference,
serial history, source action or quantum/random port requires the additional
information or interface described in §10. The long-term recovery problem
remains open beyond these conditional results.

## 追加锚（本行以下为增补区）

## 12. Right-label trades and complete recognition with all point anchors

**Definition 12.1 (actual-point domains and trades).** Keep Definition 1.1
without changing either alphabet, either literal source, the support of
$\theta$, or the complete transported relation target. In §§12–14 the true
source is $G_0$, so $\theta<1$. Use UJB Theorem 15.2 to denote its
$27$ points by $Q$, its $36$ selected lines by $L$, and its literal
fibres by $X_\ell,Y_p$, of sizes two and nine. These names refer to the
actual assignment for a proof; they are not observer inputs. Let
$D\subseteq\mathcal E_g$ expose all $72$ left and $243$ right labels.
For a right label $y$, let $p(y)$ be its actual point and put

$$
\begin{aligned}
\mathcal L_D(y)&=\{\ell\in L:\exists x\in X_\ell\ (x,y)\in D\},\\
C_D(y)&=\bigcap_{\ell\in\mathcal L_D(y)}P(\ell).
\end{aligned}
\tag{PCR.1201}
$$

There is at least one observed neighbour of $y$. Thus $C_D(y)$ is
exactly a selected three-point line if $\mathcal L_D(y)$ has one member,
and exactly $\{p(y)\}$ if it has at least two members. Distinct lines
through a point have no second intersection. The two literal twins of
one left type still give just one member of $\mathcal L_D(y)$.

Define a directed graph $\mathcal A_D$ on $Q$ by putting an arc
$p\longrightarrow q$, for $p\ne q$, exactly when some $y\in Y_p$
has $q\in C_D(y)$. A right-label assignment is a map $f:Y\to Q$
with $f(y)\in C_D(y)$ and $|f^{-1}(p)|=9$ for every $p$.
The actual assignment $p(y)$ is one such map. A cycle trade chooses
one witnessing label at each vertex of a directed simple cycle and
moves it to the next point, leaving every other label in place.

**Theorem 12.2 (exact fixed-left trade criterion).** With the actual left
injection held fixed and the right image held equal to $Y$, the following
are equivalent: the full relation is uniquely forced by $D$; the actual
point assignment is the only right-label assignment; and $\mathcal A_D$
has no directed cycle. Every other assignment differs from the actual one
by a union of capacity-preserving directed cycle trades. Every trade used
in this assertion is realized by a supported full injection of the original
literal $G_0$, not just by a matrix with the same margins.

Proof. For each $f$, biject the nine literal endpoints over $p$ to the
nine labels in $f^{-1}(p)$. Doing this at every point constructs a full
right injection with image $Y$. Keep the actual left injection. Every
observed pair is still positive by (PCR.1201), and conversely any such
right injection supplies exactly such an $f$. Different point assignments
change the relation, because different points have different eight-label
left neighbourhoods by UJB Theorem 15.2. Permutations within a point fibre
change no relation and are not ambiguity for this target.

For a different assignment draw one directed edge $p(y)\to f(y)$ for
each moved label. At every point, the number of incoming edges equals
the number of outgoing edges: both assignments have capacity nine there.
A nonempty finite balanced directed multigraph decomposes into directed
cycles. Indeed follow outgoing edges from an edge until a vertex repeats,
remove the resulting directed cycle, and repeat; deleting a cycle preserves
balance. Splitting at repeated vertices gives simple cycles. Their edges
are precisely moves allowed by $C_D(y)$.

Conversely, on a directed simple cycle choose a witnessing $y\in Y_p$
for each outgoing arc at $p$. These labels are distinct since their actual
points are distinct. Move one label out of and one into each cycle point.
Every capacity stays nine and every moved label stays in its domain.
This gives a different feasible assignment, realized by permuting the
images of those literal right endpoints in the actual full injection.
No left map, unused ambient word, or source branch has been changed.

Both generators have positive prior mass when $\theta<1$. For any
attained complete-pair history, keep its pairs, repetitions and original
indices in the alternative realization; all are still edges. Fill every
other original slot with any edge of the alternative relation. The same
fixed $N$ iid preparation gives each such compatible array mass
$1944^{-N}>0$. Thus the obstruction is compatible with the actual finite
source and its native preparation, not a new sampling permission. $\square$

**Definition 12.3 (full27-anchor class).** A full-support positive set
$D\subseteq\mathcal E_g$ for $G_0$ is in this class if it contains
$27$ distinct right labels
$a_1,\ldots,a_{27}$, each with eight distinct acquired left neighbours,
and these $27$ neighbourhoods are different. Choose one such collection.
Since the true right degree is eight, these are complete neighbourhoods;
the anchors lie one at each actual point. Extra positive edges and extra
saturated columns are allowed. This is the class used for the minimum
below, rather than a restriction of the full-injection prior. Attaining such a
set within the original fixed $N$ is a separate acquisition condition.

**Theorem 12.4 (singleton/capacity recognition is complete in this class).**
For a positive set in Definition 12.3, the existing algorithm of
Definition 2.2 accepts if and only if $D$ is a certificate against all of
$\mathcal G_\theta$. Equivalently, it accepts if and only if the graph
$\mathcal A_D$ of Definition 12.1 is acyclic. The selected anchors and
acquired pairs suffice for the algorithm; it needs no actual coordinates,
true injections, or hidden choice of $p(y)$. In particular this is exact
on attained full-support histories of this class. Testing a mathematical
witness set does not assert its acquisition within the fixed $N$.

Proof. Reuse the saturated-anchor argument in Theorem 2.1. In any
compatible generator the anchors' eight-neighbour sets are exact by the
right degree. They are $27$ distinct right types, ruling out $G_1$,
which has only nine. In $G_0$ they exhaust its point types. Hence the
left labels' membership patterns in these columns give the complete
line-point table and its $36$ two-label left fibres in label coordinates.
The table is the same for every compatible full left injection. Missing
anchor incidences are forced by saturation, not supplied as observed
negatives. Full support also forces both image sets to be exactly $X,Y$.

An anchor now names its singleton point type. Every other label has exactly
the domain (PCR.1201), computed from this table. Every assignment with
nine labels at each anchor type is realizable using the actual left map,
as in Theorem 12.2; every candidate with an arbitrary full left map has
one of these assignments in the same table. Thus uniqueness against all
supported generators is exactly the fixed-table uniqueness of Theorem 12.2.

For completeness of the particular algorithm, singleton assignment and
removal of a type already occupied by nine assigned labels preserve every
feasible assignment. On this positive domain they cannot produce a wrong
assignment, empty domain, or excess capacity, because the actual assignment
remains feasible throughout. If all labels are assigned, uniqueness follows.
If the algorithm stalls, consider the types with positive remaining capacity.
At each such type $p$ an actual label of $Y_p$ is still unassigned. Its
residual domain contains its true type and, because it is not a singleton,
another type of positive remaining capacity. Draw that outgoing arc from
$p$. Every vertex of this nonempty finite graph has an outgoing arc, so
following arcs gives a directed cycle. Its witnessing labels are unassigned
and its trade preserves all already assigned labels and all capacities.
Theorem 12.2 realizes a different full relation. Thus a stall is genuine
ambiguity, and a certificate cannot stall. This proves the exact criterion
and completeness of Definition 2.2 on the stated class. $\square$

**Proposition 12.5 (acyclic fixed-left domains need not certify unknown left
maps).** There is full-support positive $G_0$ evidence with every
$C_D(y)$ a singleton, no saturated columns, and a different compatible
full left injection. Thus outside the anchored class, absence of the
fixed-left cycle obstruction is only necessary for a certificate.

Proof. Name the four selected directions $d_1,d_2,d_3,d_4$, the two
literal representatives of each line $0,1$, and the nine right labels at
$p$ as $y_{p,0},\ldots,y_{p,8}$. These are construction names only.
At each point give column $0$ the representatives $0$ of its $d_1,d_2$
lines; column $1$ their representatives $1$; column $2$ the representatives
$0$ of its $d_3,d_4$ lines; and column $3$ their representatives $1$.
Give each of columns $4,\ldots,8$ the same two left neighbours as column
$2$. Every column has two neighbours from distinct line types.

Fix $p_0$ and let $x,x'$ be representatives $0$ of its $d_1,d_2$
lines. At the other points of the first line replace any use of $x$ by
its twin, and do the analogous replacement for $x'$ on the second line.
These replacements preserve two distinct line types in every column.
Every left label still occurs: $x,x'$ occur at column $y_{p_0,0}$,
their twins occur in column $1$, and all other line representatives occur
in the indicated columns at their points. All $243$ right labels occur,
so the resulting evidence has exactly $486$ distinct pairs and full support.
Every domain is a singleton, so $\mathcal A_D$ is empty.

Postcompose the actual left injection with the transposition of its image
labels $x,x'$, keeping the right injection. The only evidence involving these two labels is their
common column $y_{p_0,0}$, adjacent to both, so all evidence is preserved.
Their full line neighbourhoods differ, so the transported relation changes.
Both injections remain full and supported. For any fixed $N\ge486$ an
array listing these pairs and then repeating one of them is a positive
finite realization for both generators. This example grants no acquisition
at a smaller $N$. It shows why a fixed-left criterion alone cannot replace
the all-left-map argument in Theorem 12.4. $\square$

## 13. The six-point closure minimum for the actual four directions

**Definition 13.1 (selected-line closure).** For $S\subseteq Q$, let
$\operatorname{cl}_K(S)$ be the smallest set containing $S$ and the
third point of any selected line whose other two points it contains.
Only the $36$ lines of (PCR.3) are allowed; closure under all $117$
affine lines is a different operation. A generating set has
$\operatorname{cl}_K(S)=Q$.

**Theorem 13.2 (exact minimum six).** The minimum size of a generating set
for this selected-line closure is six. This holds in the actual $G_0$
geometry and hence under every transported incidence isomorphism.

Proof. Use the basis

$$
b_1=(0,0,1),\qquad b_2=(1,0,0),\qquad b_3=(1,2,1)
\tag{PCR.1301}
$$

of the actual $F^3$. Its fourth selected direction is
$F(b_1+b_2+b_3)=F(1,1,1)$, since
$b_1+b_2+b_3=(2,2,2)$. Thus in the coordinates
$w=xb_1+yb_2+zb_3$ the permitted directions are the three coordinate
axes and $F(1,1,1)$. This is a correctness change of coordinates for the
specified source, not an observer's known frame.

For the lower bound define the evaluation vector over $F_3$

$$
v(x,y,z)=(1,x,y,z,xy-xz,xy-yz)\in F_3^6.
\tag{PCR.1302}
$$

On any coordinate line each component is an affine function of the line
parameter, whose sum over $F_3$ is zero. On a diagonal line the sum of
each of $xy,xz,yz$ is $-1$, because $\sum_t1=\sum_t t=0$ and
$\sum_t t^2=-1$ in $F_3$. Their displayed differences therefore also
sum to zero. Consequently $v(a)+v(b)+v(c)=0$ on every permitted line.
Adding its third point cannot increase the span of the evaluation vectors
already present.

The $27$ evaluation vectors span all of $F_3^6$. To see this, a linear
functional vanishing on them would give a polynomial

$$
c_0+c_1x+c_2y+c_3z+c_4(xy-xz)+c_5(xy-yz)
\tag{PCR.1303}
$$

vanishing on $F_3^3$. A polynomial of degree at most one in each variable
that vanishes on this grid is zero: hold two variables fixed, use the
three roots in the remaining variable, and iterate. The coefficients of
$xz$ and $yz$ first give $c_4=c_5=0$, and then all the other
coefficients vanish. A proper subspace of $F_3^6$ has a nonzero
annihilating functional, proving the span assertion. Since closure cannot
increase this span, a generating set needs at least six points.

For the matching construction take

$$
S_* =\{(0,0,0),(1,0,0),(0,1,0),(1,1,0),(0,0,1),(1,0,1)\}
\tag{PCR.1304}
$$

in the coordinates (PCR.1301). Coordinate-line closure of the two
$2\times2$ squares fills both planes $z=0$ and $y=0$: first fill
the third entries of their two parallel rows, then their columns. For a
point $(x,y,z)$ with $y\ne z$, its diagonal line meets those two
planes at parameters $-z$ and $-y$, which are distinct. The point is
therefore in the closure as well. The only remaining possibilities have
$y=z\ne0$. At fixed $x,z\ne0$, the other two values of $y$ are
unequal to $z$ and already present; the coordinate $y$-line supplies
the missing value. All $27$ points are obtained. This is a finite
constructive completion order, proving the upper bound and exactness.
Transporting the lines transports the same closure argument. $\square$

The six-dimensional evaluation space uses the extra diagonal direction
as well as the finite field. The axis-parallel integer-grid value $2^3$
is not the minimum for these four selected directions. Neither the seed
coordinates nor the linear evaluations are additional observed data.

## 14. Defining points, the 480 anchored minimum and the 297 general bound

**Lemma 14.1 (acyclic trades force a generating set of pinned points).**
Under Definition 12.1 put

$$
S_D=\{p\in Q:C_D(y)=\{p\}\text{ for every }y\in Y_p\}.
\tag{PCR.1401}
$$

If $\mathcal A_D$ is acyclic, then
$\operatorname{cl}_K(S_D)=Q$, and in particular $|S_D|\ge6$.
With one saturated anchor at each point, membership in $S_D$ means
that all eight other labels at that point have singleton domains.

Proof. List the vertices of the acyclic graph in an order in which every
arc points to an earlier vertex. Process this order. If $p\in S_D$,
it is available as a seed. Otherwise some $y\in Y_p$ has a non-singleton
domain, which by Definition 12.1 is a selected line $\{p,q,r\}$.
Both $p\to q$ and $p\to r$ are arcs, so $q,r$ have already been
processed. The two-of-three rule now adds $p$. This proves generation;
Theorem 13.2 gives its minimum. An anchor has its eight incident left
neighbours, hence a singleton domain, giving the last assertion. $\square$

**Theorem 14.2 (uniform 480-pair G0 certificate).** For every supported
transported $G_0$ there is a certificate of exactly $480$ distinct
positive complete pairs in the full27-anchor class. It forces the entire
literal $1944$-edge relation against all supported full injections of both
branches, with no known-label promise or restriction of the prior.

Proof. Construct in the actual source coordinates and then transport.
Choose one literal right anchor at each of the $27$ points and acquire
all eight of its incident pairs, giving $216$ pairs as in Theorem 2.1.
Choose the six points $S_*$ of (PCR.1304). For each of their eight
nonanchor right labels include two incident pairs from distinct line types.
This adds $6\cdot8\cdot2=96$ pairs and makes all six point types
fully assigned by the singleton rule, including their anchors.

Order the other $21$ points by any construction of their selected-line
closure from $S_*$. When adding $p$, choose a selected line
$\{p,q,r\}$ whose other two points were added earlier. For each of the
eight nonanchor right labels at $p$, include just one pair to a literal
left representative of this line. This adds $21\cdot8=168$ pairs.
The blocks use disjoint right labels, so there are exactly

$$
216+96+168=480
\tag{PCR.1402}
$$

distinct pairs, not a count after suppressing literal twins. The anchors
expose all left labels and all other right labels have been included.

Theorem 12.4 fixes the complete labelled type table and excludes $G_1$.
The six seed types have all nine labels assigned. Inductively, a chosen
line for the next point has its other two capacities already filled by nine
distinct labels each. Every nonanchor label under consideration is distinct
from those eighteen labels. Its one positive incidence restricts it to this
line, so injectivity forces its remaining point. All eight labels there are
assigned, filling that type in turn. The algorithm assigns every right
label, returns the complete lifted relation and accepts. Coordinates,
anchors and representative choices specify an existence witness only;
Definition 2.2 recognizes attained evidence without being given them.
The full-injection and both-branch conclusion follows from Theorem 12.4,
not merely from a fixed-left calculation. $\square$

**Theorem 14.3 (480 is exactly minimal in the full27-anchor class).** Every
certificate in Definition 12.3 has at least $480$ distinct pairs, even
when arbitrary additional positive edges are permitted. Theorem 14.2
attains this lower bound.

Proof. Choose one of its $27$-anchor collections. Its columns contribute
exactly $216$ distinct pairs. Each of the $216$ other right labels must
occur at least once. Thus the starting count is $432$.

A certificate has no directed cycle by Theorem 12.4. Lemma 14.1 gives
at least six points in $S_D$. At each such point all eight nonanchor
labels have singleton domains. Each requires observed neighbours in at
least two different line types, so has degree at least two in the evidence.
These $8|S_D|$ distinct columns each contribute at least one pair beyond
the starting count. Therefore

$$
|D|\ge216+216+8|S_D|\ge432+48=480.
\tag{PCR.1403}
$$

An extra edge to the other twin of an already observed line does not make
a singleton domain. More edges in any column cannot evade this counting
argument. It applies to every anchor collection chosen as above and to all
extra positive evidence, without assuming that the evidence has the
particular shape of Theorem 14.2. $\square$

**Theorem 14.4 (297 necessary pairs for unrestricted G0 certificates).**
Every positive complete-pair certificate for a supported $G_0$ under
Definition 1.1 has at least $297$ distinct pairs, without an anchor
hypothesis. In particular an attained certificate needs at least $297$
completed original slots. This is a necessary bound, not an unrestricted
construction or a sufficient recognition rule.

Proof. Theorem 4.1 forces all $72$ and $243$ endpoint labels to be
exposed, using the actual alphabet slack $128>72$, $256>243$.
Hold the actual left injection fixed and permit every right injection on
the actual image, a subset of the original competitor family. A directed
cycle would already give a different supported relation by Theorem 12.2,
so the graph must be acyclic. Lemma 14.1 supplies at least six points
whose nine literal right labels all have singleton domains.

Every right column contributes at least one pair; the $9|S_D|$ columns
at these points each require at least a second pair from a distinct line
type. Thus

$$
|D|\ge243+9|S_D|\ge243+54=297.
\tag{PCR.1404}
$$

All those column counts refer to different acquired label pairs. Repetition
of a pair at several original indices does not increase $|D|$, and each
completed slot contributes at most one member of it. The cycle alternatives
are actual full-injection finite-source alternatives as in Theorem 12.2.
No sufficiency against changing the left map is inferred; Proposition 12.5
shows exactly why that inference would be invalid. $\square$

If $q_0^{\min}$ denotes the unrestricted minimum certificate size for a
fixed transported $G_0$, these results give
$297\le q_0^{\min}\le480$. The full-injection family makes this
minimum invariant under transport. Whether fewer than $480$ pairs can
force the full relation without all $27$ anchors remains unresolved here.
The value $480$ is asserted optimal only in Definition 12.3's evidence
class. No $G_1$ minimum or improved $G_1$ upper bound follows.
The former $576$ and $324$ sufficient witnesses remain valid.

## 15. Acquired forcing, original continuation and the scope of the increment

**Corollary 15.1 (the stronger witness reaches the existing consumers).**
Keep the actual fixed finite $N$, public $\theta$, original root Read
menu, full indexed cache and paid controller of §§5–6. For a cap
$0\le n\le N$, scan original complete slots as in Definition 5.1,
retaining their original indices, masks and values. At each completion,
the label-only algorithm of Definition 2.2 can be run whenever its
$27$-anchor pattern is present. On this attained class it is an exact
certificate test by Theorem 12.4. On other evidence it makes no completeness
claim; Definition 1.2 still gives the full-family recognition criterion.
No factorial map enumeration is needed for the new anchored test.

For each supported actual $G_0$ fix, for this probability argument only,
one transported $480$-pair witness of Theorem 14.2. Its coverage in the
first $n$ original slots has exact conditional probability $F_{480}(n)$,
where $F_q$ and its occupancy recurrence are those of PCR.7–PCR.8.
Thus this is a sufficient event for acceptance. If the scan retains the
existing full-family test as well, its mixture acceptance probability is
at least

$$
(1-\theta)F_{480}(n)+\theta F_{324}(n).
\tag{PCR.1501}
$$

This reuses the $G_1$ witness unchanged. The formula is not an exact
probability of finding any certificate or a deterministic acquisition
budget. The fixed witness can be covered only if $n\ge480$, and has
positive coverage probability when that holds. For the original scan,
$n<297$ excludes a $G_0$ certificate of positive complete pairs alone;
$n\ge297$ gives no guarantee of one. Finite repetitions still allow
failure at every cap. A wholly unread reserved original slot requires
$n\le N-1$; this witness supplies a positive reserved-slot event only
when $N\ge481$. No original slot or finite cap is enlarged.

Whenever certification succeeds, its output is the complete transported
$E$ with all $72$ left and $243$ right label attachments and all
$1944$ literal edges. For $G_0$ this is precisely the input of
Proposition 8.7, which already constructs and uses the intrinsic affine heap,
marked directions and full affine incidence from acquired data. There is
no replacement of $E$ by a source-bit decision, an anonymous point table,
or a promised coordinate frame. With the retained full indexed cache,
Proposition 6.1 and UJB Theorem 17.1 supply the original indexed
conditional array law, repeated/partial-slot updates, recorded replay,
all allowed replies and bounded adaptive continuation. Their existing
formula (PCR.9) and controller/resource assumptions apply unchanged.
The inverse domain of UJB Theorem 17.2 still keeps the fixed prior,
fixed partial cache, indexed completed records and an unread original slot.

Proof. A superset of a certificate is a certificate on the attained domain:
it only removes competitors, while the actual generator remains. Once the
fixed $480$ witness is covered its anchors are saturated and its whole
positive evidence is in Definition 12.3. Theorems 12.4 and 14.2 therefore
justify the anchored test at that completion. The original slots remain
iid conditional on the one shared generator, so the existing fixed-witness
occupancy calculation applies with $q=480$. Using the existing $324$
witness on the other branch gives (PCR.1501). These events have their
original finite-slot meaning. The final relation and continuation claims
are applications of the named existing consumers, rather than new proofs
of affine rigidity, generic target constancy or indexed conditioning.
$\square$

The acquisition tariff is still exactly $15m$ original-root Reads after
$m$ completed scanned slots, operand-length sum $15m(15m+3)/2$ and
maximum $15m+1$ for $m>0$, with zero costs for the empty scan. The
number $480$ counts distinct witness pairs, whereas $m$ counts actual
completed slots, including repetitions. All $N$ slots were already
prepared: UJB §§5.2–5.3 supply the actual $\alpha/\beta$ LAB $P/S$
construction and its $75N+4$ events. Its random edge preparation, iid
law and two shared full injections are model premises; they do not follow
from bare two-atom syntax. Map selection, preparation operands, installation,
source-blind controller, computation and storage remain separately paid.

The anchored computation is finite on small acquired sets: at most $243$
columns can have degree eight, and comparing their eight-label neighbour
sets finds the $27$ different anchor types. For a chosen collection there
are $72\cdot27$ left/anchor incidence entries and at most
$243\cdot27$ label/type domain entries. A direct implementation can
scan these entries, assign a singleton, delete newly saturated types and
repeat, with at most $243$ assignments and $27$ capacity saturations.
This supplies a finite bound without enumerating unknown injection
permutations. Comparisons of words, counters, scanning for anchors,
working domains and the returned relation still use computation and
storage; the graph $\mathcal A_D$ with the true assignment is only a
proof device. The observer never asks an unacquired membership question.

**Definition 15.2 (sources, novelty scope and unresolved recovery).** The
following are the mathematical correspondences and boundaries.

* The saturated anchors and basic capacity peeling are reused from §§2, 4;
  UJB Theorem 15.2 supplies the original line structure and literal
  capacities. §§8–11 and UJB §§16–17 already supply geometry, inversion
  boundaries, masks, records and continuation. The source-specific additions
  here are the realized cycle criterion, completeness of the existing
  peeling in the anchored class, the six-point closure proof and their
  connected certificate/minimality consequences.
* [Balister–Bollobás–Lee–Narayanan, *Line percolation*, Theorem 2.3
  and §6](https://arxiv.org/pdf/1403.6851v3) give the minimum $r^d$
  for axis-parallel line percolation on an integer grid and use polynomial
  vanishing to prove its lower bound. That numerical theorem does not
  cover the finite field with a fourth direction here. Theorem 13.2 uses
  the mature polynomial/evaluation-span method with the explicit source
  correspondence (PCR.1301), line-sum identities (PCR.1302) and a matching
  six-point construction. Its source-specific dimension is proved here.
* [Cavenagh–Ramadurai, *On the distances between Latin squares and the
  smallest defining set size*, Lemma 1.1](https://arxiv.org/pdf/1602.07734v1)
  states the necessary condition that a defining set meets every contained
  Latin trade. This is the mature trade-hitting perspective; the exact
  equivalence needed here is proved in Theorem 12.2. Prescribed-margin
  cycle trades are also credited in §7. Here the competitor family is the two
  actual full-injection orbits, not all margin matrices or Latin squares.
  Theorem 12.2 proves which right-label trades are realized in this source;
  anchors supply the additional all-left-map reduction in Theorem 12.4.
  No Latin-square or margin-matrix numerical bound is transferred.
* The formal target-fibre and experiment-pair-cover suppliers in §7 remain
  the abstract criteria with their existing hypotheses. These ordinary
  paper proofs do not add a Lean declaration or claim fresh kernel checking.
  The synthesis is repository-derived in the stated source. The literature
  correspondences give no worldwide originality or priority claim.

The claims have concrete failure tests: a directed cycle must realize the
specified changed full relation; an anchored stall must yield such a cycle;
a five-point closure generating all $27$ points would contradict the
six-dimensional invariant; and any anchored certificate below $480$ or
unrestricted $G_0$ certificate below $297$ would violate the corresponding
pinned-column count. These are statements about the original full family,
not permission to treat absent pairs as negative observations or to replace
the source by a relaxed incidence problem.

The unrestricted gap $297\ldots480$ remains open here. Certification still
does not recover hidden twin coordinates, the actual origin, unread realized
bits, a serial preparation history or physical spacetime. It supplies no
new owner permission, Busy query, source oracle, chosen-label query, sampler,
reset, interrupt, graft or physical inverse. All original slots, masks,
indices, repeated and partial values and the full record/reply/return
contract remain necessary inputs where the existing consumer requires them.
This closes a scoped relation-acquisition and recognition gap for that
consumer; it does not complete the long-term mutual-recovery programme.

## 追加锚（本行以下为增补区）

## 16. Eighteen acquired columns determine the missing incidences

**Definition 16.1 (the eighteen-core class).** Keep Definition 1.1,
including both supported branches, both ambient alphabets and all full
injections. Let $D$ be attained positive complete-pair evidence exposing
$72$ left words $X$ and $243$ right words $Y$. For $a\in Y$ write
$N_D(a)=\{x:(x,a)\in D\}$. An eighteen-core is a set $W\subseteq Y$
such that:

* $|W|=18$, every $N_D(a)$ for $a\in W$ has size eight, and these
  eighteen sets are different;
* every trace $s_W(x)=\{a\in W:x\in N_D(a)\}$ has size two;
* equality of these traces partitions $X$ into $36$ classes of size two.

Let $\mathcal C_{18}$ be the class of such attained evidence containing
an eighteen-core. Extra positive evidence is allowed. The selected columns
are complete by the original right degree eight; an absent pair in any
other column remains unobserved. The class restricts the acquired evidence,
not the supported source family. Its definition supplies neither actual
maps nor an affine chart. On the attained domain the last condition will
also follow from the first two in the proof below.

Form $H_W$ on the eighteen acquired words in $W$, with one edge for each
distinct trace; attach its two left words to that edge. This graph and its
attachments are computed from acquired incidences alone.

**Theorem 16.2 (intrinsic punctured-table completion under both maps).**
For $D\in\mathcal C_{18}$, its core determines all $36$ two-word left
fibres and the complete selected-line incidence table on $27$ point types.
Eighteen types are named by $W$; the other nine are intrinsically named
by their incident sets of four attached line types. Every generator in
$\mathcal V_\theta(D)$ has this same table, up to names of the nine
internal types. In particular this is joint rigidity under arbitrary
compatible full left and right injections, rather than rigidity with
either actual map fixed.

Proof. In every compatible generator each selected column has exactly
its eight acquired neighbours, by saturation. Eighteen different such
sets exclude $G_1$, whose right endpoints have only nine neighbourhood
types (UJB Theorem 15.2). Full endpoint exposure fixes both candidate
image sets to $X,Y$. Work for the moment inside any compatible $G_0$.
The anchors occupy eighteen different points $B\subset Q$.

Each candidate line type has two literal left representatives. Saturation
makes its trace on $B$ exactly the acquired trace of each representative,
so it meets $B$ exactly twice. Two different affine lines cannot contain
the same two points. Equal traces therefore identify exactly the two
representatives of one line; they cannot split or merge under a different
candidate left injection. This proves the last condition in Definition
16.1 from the first two, and identifies every candidate's $36$ lines
with the same attached edges of $H_W$. The omitted set $U=Q\setminus B$
has nine points and meets each of the $36$ selected lines exactly once.

We first determine the shape forced on $U$, using coordinates only inside
this candidate. In (PCR.1301) the directions are the three axes and
$F(1,1,1)$. The vertical-line condition writes

$$
U=\{(x,y,f(x,y)):x,y\in F_3\}.
\tag{PCR.1601}
$$

The other two axis conditions make every row and every column of $f$ a
permutation of $F_3$. Every permutation of $F_3$ is affine: its values at
zero and one specify a nonzero slope, and its remaining value is forced.
Write $f(x,y)=b_x y+c_x$ with $b_x\ne0$. If $b_x\ne b_{x'}$, the two
affine functions intersect at some $y$, contrary to the column-permutation
condition. Thus $b_x=b$ is constant. The $c_x$ form a permutation, so

$$
f(x,y)=ax+by+c,\qquad a,b\ne0.
\tag{PCR.1602}
$$

Meeting every diagonal line exactly once is equivalent to $1-a-b\ne0$.
Thus $U$ is an affine plane transverse to all four selected directions.
This classification follows uniformly from the acquired traces; it is not
a promise that the observer knows a missing plane.

Translate this plane to level $t=0$ of a nonzero linear functional $t$.
The two complementary planes have levels $1,-1$. Normalize a vector in
each selected direction to have $t$-coordinate one. Their four planar
offsets have no three collinear: a collinear triple would give a linear
dependence of three direction vectors, whereas every three of the axes
and diagonal are independent. Four points with no collinear triple in
$F_3^2$ form a parallelogram. Indeed put three at $00,10,01$; exclusion
of their three joining lines leaves only $11,12,21$ for the fourth,
and each choice gives a parallelogram. Center it and choose its two planar
basis vectors. Subtracting its center times $t$ is a permitted correctness
coordinate change. The four normalized directions now have offsets
$\{(\epsilon,\delta):\epsilon,\delta\in\{1,-1\}\}$.

It follows that $H_W$ has two nine-vertex parts, with coordinates
$r=(r_1,r_2)$ on level one and $s=(s_1,s_2)$ on level minus one, and

$$
r\sim s\quad\Longleftrightarrow\quad r_1\ne s_1\text{ and }r_2\ne s_2.
\tag{PCR.1603}
$$

Any two distinct vertices on one side have one or two common neighbours.
Hence all vertices of that side are connected by paths of length two,
and $H_W$ is connected. Its bipartition is consequently intrinsic up to
exchange. Choose either part $A$; no candidate coordinates are needed
for the following construction.

On $A$ join different vertices when they have exactly two common
$H_W$-neighbours. In (PCR.1603) this means agreement in exactly one
coordinate. The derived graph is the $3\times3$ rook graph. Its maximal
triangles are precisely the three rows and three columns: three pairwise
adjacent cells must share one coordinate. Two triangles are disjoint
exactly when they are distinct members of the same family. Thus its six
triangles recover both three-element coordinate families, up to exchanging
the families and permuting their members.

For a vertex $b$ in the other part, its four neighbours occupy a
$2\times2$ rectangle. Exactly one recovered row and one recovered column
contain no neighbour of $b$; let $m(b)$ be their intersection cell.
For an edge $ab$, the cells $a$ and $m(b)$ differ in both coordinates.
Define $\mu(ab)$ as the intersection of the third row and the third
column, omitting the respective rows and columns of $a,m(b)$. Partition
the $36$ attached edges according to this cell. These are nine blocks
of four. Introduce one internal point for each block, incident to its
four lines, and give each line its two anchor endpoints as well.

To verify this construction, return to the correctness coordinates of
any compatible candidate. There $m(b)$ has the planar coordinates of
$b$. The third point of the selected line through $(1,r_1,r_2)$ and
$(-1,s_1,s_2)$ is

$$
(0,-r_1-s_1,-r_2-s_2).
\tag{PCR.1604}
$$

For two different symbols of $F_3$, their negative sum is the third
symbol. Thus the graph construction groups two edges together exactly
when their lines meet at the same point of $U$. Each such point has its
four original selected lines. Permuting grid symbols or exchanging its
coordinate families changes no equality of $\mu$ values. Choosing the
other bipartition gives the same partition: (PCR.1604) is symmetric in
the endpoints. In each compatible candidate, separately, the construction
therefore recovers exactly its omitted-point concurrence partition.
Since the construction uses the same acquired graph and attachments,
all candidates have the asserted common complete table. $\square$

## 17. Exact recognition beyond full27 and the eighteen-core minimum

**Theorem 17.1 (exact acquired recognition on $\mathcal C_{18}$).**
For attained $D\in\mathcal C_{18}$, apply Theorem 16.2 to any core.
For each acquired right word intersect the three-point sets of its
acquired left line types in the completed table. Assign singleton domains
and delete point types already occupied by nine distinct assigned words,
as in Definition 2.2. This accepts if and only if $D$ is a certificate
against the entire supported family, and returns all $1944$ labelled
edges when it accepts. This class strictly contains the full27-anchor
class of Definition 12.3.

Proof. All compatible generators have source zero and the same table
by Theorem 16.2. Each right word's domain is exactly one selected line
or one point, as in Definition 12.1. Every feasible assignment of nine
words per point is realizable by the actual full left injection and a
full right injection, by Theorem 12.2. Conversely every compatible
generator, even with a changed left injection, induces such an assignment
in this common table. The fixed-table part of Theorem 12.4 now applies:
every singleton/capacity step preserves the actual feasible assignment;
completion forces all words, while a stall supplies a capacity-preserving
directed cycle and a different supported full relation. This reuses the
existing trade and peeling proofs after establishing their missing common-
table hypothesis. No initial anchor at an internal point is required by
that part of the argument.

For containment, in the actual geometry choose any transverse plane, for
example $-x+y+z=2$ in (PCR.1301). From a full27 collection choose the
eighteen anchors outside it. Every selected line meets these points twice;
the traces are distinct for distinct lines. This gives a core. The next
construction has only eighteen saturated columns and proves strictness.
$\square$

**Theorem 17.2 (uniform 417-pair certificate).** Every supported transported
$G_0$ has a $417$-distinct-pair certificate in $\mathcal C_{18}$, forcing
the complete relation against all supported full injections of both
branches. It has exactly eighteen saturated columns.

Proof. Use (PCR.1301) solely to construct a literal witness. Put

$$
\begin{aligned}
U&=\{(x,y,z):-x+y+z=2\},\qquad B=Q\setminus U,\\
S&=\{000,200,010,110,001,101\}.
\end{aligned}
\tag{PCR.1701}
$$

Here three digits denote the three field coordinates. The plane is
transverse to each permitted direction and $S\subset B$. The two points
$000,200$ first generate $100$ along their axis line. Thus the closure
of $S$ contains $S_*$ of (PCR.1304), and generates all of $Q$ by
Theorem 13.2. Fix a construction order of the other twenty-one points,
each with a selected line whose two other points are earlier.

At each of the eighteen points of $B$, choose one of its nine literal
right words as anchor and include its eight incident pairs. These give
$144$ pairs and an eighteen-core: every left word occurs in exactly two
of these columns. At every seed of $S$, give each of the eight nonanchor
right words two positive pairs from different incident line types. This
adds $96$ pairs. At each later point give every remaining right word one
pair to a representative of its completing line. There are twelve later
points in $B$, each with eight such words, and nine in $U$, each with
nine. Therefore

$$
|D|=18\cdot8+6\cdot8\cdot2+12\cdot8+9\cdot9=417.
\tag{PCR.1702}
$$

The blocks use disjoint right words. Their degrees are respectively eight
on eighteen words, two on forty-eight, and one on the other $177$.
All $72$ left words occur in the anchors, and all $243$ right words
occur. Transport by the actual two full injections. The observer is
not given $U,S$, these injections or the representative choices.

Theorem 16.2 fixes the full table. The two-line observations pin every
nonanchor seed word; their anchors are already pinned, filling all six
seed capacities. At each later point its completing line has the other
two capacities filled, so a distinct right word with its one acquired
incidence must occupy the third point. Induction assigns every word.
Theorem 17.1 therefore returns all $1944$ labelled edges. The degree
histogram also proves that this raw evidence is outside full27. $\square$

**Theorem 17.3 (417 is exact within $\mathcal C_{18}$).** Every certificate
in $\mathcal C_{18}$ contains at least $417$ distinct pairs. Consequently
the unrestricted minimum for $G_0$ satisfies

$$
297\le q_{0,\min}\le417.
\tag{PCR.1703}
$$

The old $480$ minimum remains exact in the narrower full27 class.
Neither $417$ nor eighteen saturated columns is asserted necessary for
unrestricted certificates.

Proof. Choose any core in the certificate. Its eighteen columns cost
$144$ pairs. The other $225$ right words each need at least one,
giving a starting count $369$. With the actual left map fixed, a cycle
would still refute certification by Theorem 12.2. Lemma 14.1 and
Theorem 13.2 therefore supply at least six points in $S_D$ whose nine
right words all have initial singleton domains. At a core point eight
noncore words need at least a second acquired pair from a different line
type; at an omitted point all nine do. Thus each such point costs at
least eight additional pairs beyond $369$, in different noncore columns.
Hence $|D|\ge369+8|S_D|\ge417$. Extra saturated columns or extra pairs
cannot reduce this count. Theorem 17.2 attains it; Theorem 14.4 supplies
the unrestricted lower bound and Theorem 14.3 retains its own domain.
$\square$

## 18. Realized simultaneous trades and the importance of arrangement

**Theorem 18.1 (two separately unique sides need not be jointly unique).**
For every supported transported $G_0$, there is full-support positive
evidence of $486$ distinct pairs, with no saturated columns and connected
evidence graph, which forces the entire relation whenever either actual
injection is held fixed but admits a different relation when both may
change. There is also an explicit $70$-edge set that every certificate
must hit for each of the following compensated trades.

Proof. Construct in the actual selected geometry and transport. Choose
two different selected direction vectors $d,e$ and a point $p$. Let

$$
\ell_0=p+Fd,\quad \ell_1=p+e+Fd,\quad
m_j=p+jd+Fe\quad(j=0,1).
\tag{PCR.1801}
$$

Choose one left word $x$ above $\ell_0$ and one $x'$ above $\ell_1$.
Choose right words $q_j$ above $p+jd$ and $r_j$ above $p+e+jd$.
Swap $x,x'$ on the left and simultaneously swap $q_j,r_j$ for both
$j$ on the right, fixing all other image words. Call the resulting
relation $E'$, and the actual one $E$. These permutations give actual
full injections with the same image sets in the original ambient
alphabets. They introduce no new operation or relaxed-margin competitor.

In $E\cap E'$, the neighbours of $q_j$ are exactly $x$ and the two
left words of $m_j$; those of $r_j$ are exactly $x'$ and the two of
$m_j$. The special row $x$ retains exactly $q_0,q_1$, and $x'$ exactly
$r_0,r_1$. Every unmoved right word over a point of $\ell_0$ loses only
$x$; over $\ell_1$ it loses only $x'$; other unmoved columns retain
all eight neighbours. This follows by intersecting the two point
neighbourhoods: the marked pair of points has precisely the two common
left words of its $e$-line. Thus

$$
\begin{aligned}
|E\setminus E'|&=2(27-2)+4(8-3)=70,\\
|E\cap E'|&=1874.
\end{aligned}
\tag{PCR.1802}
$$

The subtractions count the special rows first; their retained marked
entries are common, and the four marked columns lose five other entries
each, so these losses are disjoint. The right-degree histogram of this
intersection is four columns of degree three, fifty of degree seven and
$189$ of degree eight. Its saturated columns occupy the other twenty-one
point types. In particular $E\ne E'$: the edge from $x$ to any right
word above $p+2d$ is lost.

We construct a sparse common subset. At a point $w$, remove $x,x'$
from its actual eight-word neighbourhood to obtain $U_w$, of size seven
or eight. It retains at least one representative of each of the four
incident line types. Choose a spanning tree on $U_w$ using only pairs
from different line types. Such a tree exists because the complete
multipartite graph of these four nonempty classes is connected.
Assign its edges injectively to right words above $w$, putting the
corresponding two incidences in each column. Fill unused right words
with any tree edge.

At each of the four marked points reserve its specified $q_j$ or $r_j$
first, and give it the pair consisting of $x$ or $x'$ and one word of
$m_j$. On the other seven left words use a six-edge tree as above,
assigned to six of the eight remaining right words, and fill the last
two with tree edges. At unmarked points the trees have at most seven
edges and fit into their nine columns. All pairs are in $E\cap E'$.
Every one of $243$ right words has exactly two acquired neighbours,
from different actual line types. The result has $486$ distinct pairs.

Every left word other than $x,x'$ appears in the trees at all three
points of its line. The word $x$ sees the two different points $p,p+d$;
$x'$ sees $p+e,p+e+d$. Thus every left word occurs, and with the actual
right injection fixed its observed points force its original line.
With the actual left injection fixed, the two distinct line types in
each right column force its original point. Fibre permutations change
neither target. These are both one-sided uniqueness assertions.

They also hold against the other supported branch. Each local point
construction is connected on its retained left words and all nine right
words, including the special word at each marked point.
Along every selected line at least one retained left representative joins
the local constructions at all three points. The selected geometry is
connected by UJB Theorem 15.2, so the full $315$-vertex evidence graph
is connected. Any connected positive graph embedded into $G_1$ lies in
one $K_{8,27}$ component; this cannot contain all its $72$ left and
$243$ right words. Thus $G_1$ is excluded without fixing either map.
Full support also fixes the two candidate image sets. Nevertheless $E'$
contains the sparse evidence and differs from $E$, proving the assertion.

Finally, for any certificate $C\subseteq E$, if
$C\cap(E\setminus E')=\varnothing$, then $C\subseteq E'$ and the
displayed supported competitor survives. Therefore each compensated
trade gives the necessary $70$-edge cut

$$
C\cap(E\setminus E')\ne\varnothing.
\tag{PCR.1803}
$$

This is a necessary family of structural obstructions, not a sufficient
recognizer. The dense $1874$-pair intersection also has both one-sided
uniqueness properties: it contains the sparse evidence. $\square$

**Theorem 18.2 (recognized fibres and twenty-one anchors still do not suffice).**
For every supported transported $G_0$ there is a different coupled trade
whose $1800$-pair intersection has full support, twenty-one different
saturated neighbourhoods, and acquired incidences recognizing every
two-word left and nine-word right fibre. With either actual injection
fixed the entire relation is unique, but jointly it is ambiguous.
Thus anchor arrangement and joint concurrence, rather than anchor count
or recognition of the separate fibre partitions, are essential to the
positive theorem.

Proof. Choose $p$ and nonzero $u,v$ in two different selected directions,
and put $q=p+u+v$. Define four lines

$$
a=p+Fu,\quad b=p+u+Fv,\quad
c=p+Fv,\quad d=p+v+Fu.
\tag{PCR.1804}
$$

Swap the two points $p,q$ and swap line types $(a\ b)(c\ d)$.
Lift each line swap by paired bijections of its two literal left words,
and lift the point swap by bijecting their nine literal right words,
keeping every $z$ coordinate if desired. Fix all other words. Both
resulting injections are full; write the changed relation $E''$ and
$D_\square=E\cap E''$.

Every three of the four selected directions are independent. Hence
neither remaining direction lies in $\operatorname{span}(u,v)$.
The four displayed lines are distinct, and the four remaining-direction
lines through $p$ or $q$ are distinct from them and each other.
In the common quotient incidence, $a$ retains $p,p+u$ and loses $p+2u$;
$b$ retains $p+u,q$ and loses $p+u+2v$; $c$ retains $p,p+v$ and loses
$p+2v$; $d$ retains $p+v,q$ and loses $p+2u+v$.
Each of the four remaining-direction lines through $p$ or $q$ loses
just that endpoint. All other lines retain all three points. Thus eight
of the $108$ quotient incidences are lost. Every common incidence retains
its full $2\times9$ literal product, giving

$$
|D_\square|=100\cdot18=1800,\qquad
|E\setminus E''|=144.
\tag{PCR.1805}
$$

There are eight quotient rows of degree two and twenty-eight of degree
three. The six affected points are $p,q,p+2u,p+2v,p+u+2v,p+2u+v$;
the first two have common degree two, the next four degree three, and
the other twenty-one degree four. Consequently the literal row degrees
are $18$ on sixteen words and $27$ on fifty-six; the column degrees
are four on eighteen words, six on thirty-six and eight on $189$.
All endpoints occur. The twenty-one different complete neighbourhoods
exclude $G_1$ by UJB Theorem 15.2.

Each right word has neighbours in at least two actual line types, so
fixing the actual left injection pins its point. Each left word has at
least eighteen acquired right neighbours, while two different line types
share at most nine right words by UJB Theorem 18.1. Fixing the actual
right injection therefore pins its line. These prove both one-sided
uniqueness assertions within the original supported family.

The fibre partitions themselves can be recognized without either map.
Join two different right words if they have at least three common acquired
left neighbours. Actual right twins share at least four; different point
types have at most two by the geometric bound used in UJB Theorem 18.2.
This recovers exactly the twenty-seven nine-word fibres. Join two left
words if they have at least ten common acquired right neighbours. Actual
twins share at least eighteen, different line types at most nine. This
recovers exactly the thirty-six two-word fibres. These are consequences
of acquired positive incidences and the proved source bounds.

Nevertheless $E''$ remains compatible and changes the relation: a left
word of $a$ loses all edges to the right words above $p+2u$. Thus the
intersection is not a certificate, despite its fully recognized fibres.
This is a different trade from Theorem 18.1: its losses are $144$ literal
edges, not $70$, and its intersection is $1800$, not $1874$.

There is a direct disagreement at the geometry consumer too. Translate
$p=0$ for this proof and let $\sigma=(0\ u+v)$. With the acquired
right fibres named $Y_w$, the actual heap on the triple
$(Y_u,Y_0,Y_u)$ returns $Y_{2u}$. The alternative heap is the
$\sigma$-conjugate of $x-y+z$, and returns

$$
Y_{\sigma(\sigma(u)-\sigma(0)+\sigma(u))}=Y_{u-v}.
\tag{PCR.1806}
$$

These are different exposed fibres because $u,v$ are independent.
Repeated use of the first input is reuse of that input record, not a new
sample. This establishes why an anonymous geometry or the two fibre
partitions cannot replace Proposition 8.7's complete labelled relation.
$\square$

## 19. Original acquisition, indexed continuation and exact scope

**Corollary 19.1 (lawful acquisition and unchanged consumers).** Keep
the original finite prepared $N$, root Read menu, full indexed cache,
public prior and paid controller of §§5–6. On the attained class
$\mathcal C_{18}$, Theorem 17.1 recognizes exactly the full-relation
certificates. For the cap $0\le n\le N$ of Definition 5.1, coverage
of a fixed transported witness of Theorem 17.2 has exact probability
$F_{417}(n)$ conditional on the actual $G_0$. Retaining the existing
$G_1$ recognition supplies the sufficient mixture acceptance bound

$$
(1-\theta)F_{417}(n)+\theta F_{324}(n).
\tag{PCR.1901}
$$

This witness event is impossible below $417$ completed original slots
and positive at or above that count. It is not a deterministic acquisition
budget, the exact probability of any certificate, or permission to request
the witness pairs. Repetitions can prevent certification at every finite
cap. A reserved wholly unread original index needs $n\le N-1$;
this witness therefore gives a positive reserved-slot event only when
$N\ge418$. Other certificates are not excluded at smaller counts by
this construction; the unrestricted necessary bound remains $297$.

Proof. Extra positive evidence preserves an existing core: a saturated
column cannot gain a new neighbour in the actual source. It also preserves
certification, since it only removes competitors from a nonempty version
set containing the actual generator. The fixed-witness occupancy argument
of Theorem 5.2, with $q=417$, and the unchanged $G_1$ witness prove
(PCR.1901). That argument counts original iid prepared slots, including
repetitions, without acquiring unscanned values.

For a public finite recognition procedure, group degree-eight columns
by their acquired neighbour sets. There are at most twenty-seven such
sets on an attained $G_0$ and at most nine on $G_1$. If needed, inspect
the eighteen-element subsets of these groups, choosing one representative
column per group. There are at most $\binom{27}{18}=4,686,825$ subsets.
Trace tests and Theorem 16.2 then use an eighteen-vertex graph with
thirty-six edges, a nine-cell grid, and the completed table. Domains need
at most $243\cdot27$ label/type entries; capacity peeling makes at most
$243$ assignments and twenty-seven saturations. This is computation on
acquired words, with its own finite time and storage cost. It enumerates
no injection permutations and asks no absent-pair membership question.
Proposition 1.3 remains the exact general criterion outside the attained
class; no new completeness claim outside it is needed.

Acceptance returns the entire transported $1944$-edge relation, with
all literal $72/243$ label attachments, not just the core, source branch,
line classes or point partition. Proposition 8.7 can therefore recover
its intrinsic heap, marked directions and full affine incidence. With
the retained original indexed masks, values and completed records,
Proposition 6.1 and UJB Theorem 17.1 apply to this same relation.
They give $Q_{E,j}$ of (PCR.9), every original allowed reply, positive
partial update, completed-slot replay, repeat and bounded adaptive
continuation with their existing controller and resource hypotheses.
Completed indices replay their actual recorded values; partial indices
keep their own restrictions; unread indices keep their original law and
do not reveal realized values. The inverse domains of UJB Theorem 17.2
still retain the fixed prior, fixed indexed partial cache and an unread
original slot where required. $\square$

**Proposition 19.2 (the trade witnesses are attained finite-source limits).**
The two ambiguous constructions of §18 are attained complete-pair
histories in the original preparation at their stated distinct-pair
counts. Their separate-side tests and fibre information cannot justify
substitution of one certified relation into the continuation consumer.

Proof. Order the $486$ sparse pairs of Theorem 18.1 at that many original
indices. For any fixed $N\ge486$, this ordered event has probability
$1944^{-486}>0$ conditional on either displayed generator, leaving all
other slots unrestricted. The same construction with the dense
intersection needs $N\ge1874$; Theorem 18.2's distinct intersection
needs $N\ge1800$. Both generators have positive prior mass whenever
the actual $G_0$ is supported. Further specified slots can repeat common
edges and preserve the alternative. This proves attainment without
enlarging $N$, asserting a guaranteed scan outcome or acquiring arbitrary
chosen edges. Repetitions retain their own indices but add no distinct
pairs. A wholly unread reserved index needs respectively $N\ge487$,
$1875$, or $1801$. Additional actual positive or partial evidence may
remove a competitor and must be evaluated at its original indices.

For example choose an edge $e_*\in E\setminus E'$ in Theorem 18.1,
or $E\setminus E''$ in Theorem 18.2. After the ordered complete-pair
history and with all other indices unread, the posterior has positive
mass on a generator containing $e_*$ and on one excluding it. Its
probability at a designated unread index is therefore strictly between
zero and $1/1944$. Substitution of the actual $E$ alone would wrongly
give $1/1944$. UJB Theorem 17.1 instead retains the proper mixture.
When all $N$ slots are exhausted there is no unread-index assertion;
the conditional law on the remaining empty array is the empty product.
The heap disagreement (PCR.1806) independently prevents use of just
the recognized fibres as the geometric input. $\square$

**Definition 19.3 (resource and mathematical boundaries).** The results
above keep the following hypotheses and conclusion domains.

* After $m$ completed scanned slots the tariff is still $15m$ original-
  root Reads, operand-length sum $15m(15m+3)/2$ and maximum $15m+1$
  for $m>0$, with zero for the empty scan. All repeated slots count.
  UJB §§5.2–5.3 supply actual $\alpha/\beta$ LAB $P/S$ preparation
  with $75N+4$ events. The random preparation, iid edge law and once-
  shared full injections remain supplied premises, not consequences of
  bare two-atom syntax. Preparation operands, maps, controller installation,
  word comparisons, graph/table computation, output and retained indexed
  storage are separately paid. No free controller state is supplied.
* Theorems 16.2–17.3 are repository-derived source-specific ordinary
  mathematical conclusions. Their new bridge is intrinsic completion of
  the nine missing point incidences against both changing full maps.
  The fixed-table cycle, capacity peeling, selected-line closure minimum,
  support bounds and geometry/indexed consumers are reused from §§4,
  6, 8, 12–15 and UJB §§15, 17–18. The formal target-recovery and
  pair-cover results cited in §7 provide their abstract criteria only.
  No new Lean declaration or fresh kernel verification is asserted.
* The rook graph is the elementary $H(2,3)$ case of the established
  coordinate structure discussed by Mirafzal–Ziaee,
  [*A note on the automorphism group of the Hamming graph*, §3,
  proof of Theorem 3.4](https://arxiv.org/pdf/1901.07784v1).
  The relevant actions are independent coordinate-symbol permutations
  and coordinate permutations. The graph-to-missing-incidence
  correspondence here is proved in Theorem 16.2; it is not a claim
  supplied by that automorphism result. Twin and trade comparisons
  remain those in UJB §15 and PCR §§7, 15.2. No general literature
  theorem, numerical bound or worldwide priority is claimed for this
  partial-evidence recovery.
* The $417$ minimum is confined to $\mathcal C_{18}$, the $480$
  minimum to full27, and the unrestricted interval is $297\ldots417$.
  The trades show that even twenty-one saturated point types can fail
  with their displayed arrangements; they do not show that every class
  with fewer than twenty-seven anchors fails. Conversely eighteen-core
  sufficiency does not assert that eighteen anchors are always necessary.
  The $70$-edge cuts are necessary only; neither separate-side uniqueness
  nor the two recovered fibre partitions is an exact joint recognizer.
* The returned table and full relation recover no actual affine origin,
  hidden twin coordinates, unacquired realized bits, serial preparation
  history or physical spacetime. No new owner access, Busy query, source
  oracle, sampler, fork, reset, interrupt, graft or physical inverse is
  supplied. All original record/reply/return and private-owner permissions
  remain in force. The operational source obligations beyond the stationary
  Read preparation remain separate. The long-term mutual-recovery goal
  is unchanged by this scoped acquired-incidence bridge.

## 追加锚（本行以下为增补区）

## 20. Positive puncture profiles and full labelled recovery

**Definition 20.1 (proper indexed evidence).** Retain (PCR.1), the full
ambient alphabets, every full injection and the original finite prepared
array. Write $Q_d=\{0,1\}^d$, and let $x^h$ toggle coordinate $h$ of a
word. The open cube neighbourhood is
$\Gamma_d(S)=\{x^h:x\in S,\ 1\le h\le d\}$. It need not contain $S$.
For an attained indexed cache $K$, let $B_j(K)$ be its original
fifteen-bit coordinate rectangle, with repeated reads joined at that
same index. Its compatible generators are

$$
\mathcal V_\theta(K)=\{g\in\mathcal G_\theta:
       \mathcal E_g\cap B_j(K)\ne\varnothing\text{ for every }j\le N\}.
\tag{PCR.2001}
$$

A slot is proper when its acquired mask has fewer than fifteen
coordinates. Inference of its value does not enlarge that acquired mask.
A record with exactly fourteen acquired coordinates and omitted left
coordinate $h\le7$ gives only the positive clause
$\{(x,y),(x^h,y)\}$; its right word $y$ is fully read. An omitted right
coordinate gives $\{(x,y),(x,y^h)\}$ with fully read $x$. The two
presentations of the same clause are identified for computation only.
The indices, masks, values and full original records remain retained.
No absent pair or absent clause is an observed negative. Different
indices are never identified merely because their clauses overlap.

For $S\subseteq Q_7$, define its full incident-edge profile by

$$
\mathsf H(S)=\{\{x,x^h\}:x\in S,\ 1\le h\le7\}.
\tag{PCR.2002}
$$

This is a set of undirected cube edges, rather than a set of acquired
complete left words.

**Definition 20.2 (acquired profile and probe criterion).** The following
finite procedure is defined on the retained cache, without a supplied
relation, chart or hidden map.

1. From exactly-fourteen-bit records omitting a left coordinate, form
   the graph $H_y$ on all $128$ left words, one graph for each fully
   read right word $y$ in such records. Insert the corresponding cube
   edge for each record. Require exactly $243$ different such $y$.
2. Let $U_y$ be the degree-seven vertices of $H_y$. Require
   $|U_y|\in\{8,9\}$. Among its at most nine eight-element subsets,
   require a unique $S_y$ satisfying $H_y=\mathsf H(S_y)$. Construct
   $F=\{(x,y):x\in S_y\}$. Require exactly $72$ used left words,
   every row of $F$ to have degree $27$, and
   $|S_y\cap S_z|\le2$ whenever $S_y\ne S_z$.
3. Group the $243$ right words into classes $C$ according to equality
   of their $S_y$. For every incident pair $(x,C)$, meaning
   $x\in S_y$ for $y\in C$, form

$$
T_{x,C}=\{y\in C:\text{for every }1\le h\le8,
 \ \{(x,y),(x,y^h)\}\text{ occurs as an acquired right-omission clause}\}.
\tag{PCR.2003}
$$

   Require $|\Gamma_8(T_{x,C})|>27$ for every such $(x,C)$.
   Accept and return $F$ precisely when all these tests pass;
   otherwise return failure.

The equality in step 2 is a shape condition on the positive records
actually supplied to this procedure. It does not require a compatible
source to have no additional edges or clause profiles. Extra records
can make this sufficient criterion reject; it is not the exact general
criterion of UJB §16. It uses no enumeration of full injections.

**Theorem 20.3 (soundness, full profiles and six probes).** On every
attained cache accepted by Definition 20.2, every compatible generator
has exactly the returned $1944$-edge labelled relation $F$. The same
conclusion holds against either native branch with any full injections,
including the union of both branches before a value of $\theta$ is fixed.
For every eight-set $S\subseteq Q_7$, a graph $H_y=\mathsf H(S)$ passes
the profile test and returns $S$. Six distinct right words in each
$T_{x,C}$ suffice for its expansion test, regardless of their coding.

Proof. Two distinct vertices of $Q_7$ have at most two common neighbours:
a common neighbour entails distance two, and then the two changed
coordinates give exactly two choices. Thus the union of their two
seven-element neighbour sets has at least $7+7-2=12$ elements.

First verify the profile test. Every member of $S$ has degree seven in
$\mathsf H(S)$. A vertex $t\notin S$ has degree seven precisely when
all seven neighbours of $t$ belong to $S$. There is at most one such
$t$, since two would require at least twelve elements in an eight-set.
Consequently $S\subseteq U_y$ and $|U_y|$ is eight or nine.

Suppose two eight-sets $S,R$ have the same full profile. If $x\in S\setminus R$,
all seven neighbours of $x$ must lie in $R$ to meet its incident edges.
There cannot be two such $x$, by the twelve-neighbour bound. If the
sets differ, write $S=W\cup\{x\}$ and $R=W\cup\{t\}$, with $|W|=7$.
If $x,t$ are not adjacent, both neighbour sets must equal $W$, contrary
to their common-neighbour bound. If they are adjacent, each of
$\Gamma_7(\{x\})\setminus\{t\}$ and
$\Gamma_7(\{t\})\setminus\{x\}$ must lie in $W$. These two six-sets
are disjoint, since adjacent vertices have opposite parity and hence
neighbour sets of opposite parity. Again seven places cannot hold
twelve vertices. Thus $S=R$, proving the asserted exact-profile
recognition with at most nine candidates.

Now compare the constructed $F$ with any native relation $E'$ satisfying
all the acquired positive clauses. Every constructed $y$ occurs in a
left-omission clause, so $E'$ uses all $243$ of these right words and
no others. For each used $x$ of $F$, the expansion condition supplies
right-omission records with that fully read $x$. Hence $E'$ also uses
all $72$ constructed left words and no others. The literal degrees
of (PCR.1) give eight-element candidate columns $R_y$ and
$27$-element candidate rows.

If $x\in S_y\setminus R_y$, all seven left neighbours of $x$ must
belong to $R_y$: each edge incident to $x$ is an acquired clause and
must be met. Two lost vertices would put twelve neighbours in $R_y$.
Therefore

$$
|S_y\setminus R_y|\le1,\qquad |S_y\cap R_y|\ge7.
\tag{PCR.2004}
$$

UJB Theorem 15.2 and the proof of its Theorem 18.2 show that distinct
native column neighbourhoods intersect in at most two left words,
for both branches. If $S_y=S_z$, (PCR.2004) gives
$|R_y\cap R_z|\ge6$, forcing $R_y=R_z$. Conversely if $R_y=R_z$,
then $|S_y\cap S_z|\ge6$; step 2 forces $S_y=S_z$. Thus the entire
labelled right twin partition agrees in $F$ and $E'$, in both directions.
In particular its classes necessarily have the actual candidate
capacities, nine in $G_0$ or twenty-seven in $G_1$. If $F$ is itself a
transported native relation, those different class sizes exclude a
substitution of the other branch.

If an incidence $(x,y)$ of $F$ is absent from $E'$, its whole common
right class $C$ is absent from the candidate row at $x$. For each
$y\in T_{x,C}$, all eight acquired right-omission clauses then require
all eight words $y^h$ to belong to that row. They require
$\Gamma_8(T_{x,C})$ to fit inside a $27$-element set, contradicting
step 3. No incidence is lost. Both $F$ and $E'$ have $243\cdot8=1944$
edges, so $F=E'$. Attainment supplies at least one such native $E'$.
This argument has used only positive clause constraints; equality of
the acquired profile was never imposed on a competitor.

For the coding-independent six-probe assertion, use Harper's classical
vertex-isoperimetric theorem as an intermediate. Its precise
closed-neighbourhood statement is Theorem 1 of Eero Räty,
[*Uniqueness in Harper's vertex-isoperimetric theorem*,
arXiv:1806.11061v2](https://arxiv.org/html/1806.11061v2#S1): an equally
sized initial segment of the simplicial order minimizes
$|A\cup\Gamma_d(A)|$. The cited order first sorts by cardinality and
then lexicographically within a layer. The theorem is attributed there
to L. H. Harper, *Optimal numberings and isoperimetric problems on
graphs*, J. Combinatorial Theory 1, 385–393,
[doi:10.1016/S0021-9800(66)80059-5](https://doi.org/10.1016/S0021-9800(66)80059-5).
Only this minimization theorem is used, not a uniqueness or stability
conclusion.

For $Q_7$, the minima of the closed neighbourhood at sizes zero through
six are

$$
(f(0),\ldots,f(6))=(0,8,14,19,23,26,28).
\tag{PCR.2005}
$$

Indeed the nonempty initial segments here are the zero word followed
by $k-1$ unit vectors. For $1\le k\le6$ their closed neighbourhood
contains the zero word, all seven unit vectors and exactly the
weight-two words containing at least one of those $k-1$ coordinates:
$f(k)=8+\binom72-\binom{8-k}{2}$.

Split a six-set in $Q_8$ by parity, with sizes $r,6-r$. On each parity
class, deletion of the eighth coordinate is a bijection to $Q_7$.
Under that bijection its open $Q_8$ neighbourhood corresponds to the
closed $Q_7$ neighbourhood: toggling the eighth bit keeps the first
seven coordinates, and toggling any other bit changes just that
coordinate. The two resulting target parities are disjoint. Therefore

$$
|\Gamma_8(T)|\ge f(r)+f(6-r),\qquad
(f(r)+f(6-r))_{r=0}^6=(28,34,37,38,37,34,28).
\tag{PCR.2006}
$$

Thus six words always expand to at least $28>27$. Five unit vectors
have only $1+\binom82-\binom32=26$ open neighbours, whereas six have
$1+\binom82-\binom22=28$. Six is sharp for this cardinality-only
auxiliary expansion step. This proves no minimum number of native
probes, original slots or Reads. $\square$

**Proposition 20.4 (a full profile need not have a unique positive cover).**
Exact-profile recognition in Definition 20.2 cannot be replaced in its
proof by an assertion that a column's acquired profile has only one
positive eight-cover, even for a profile realizable at a native column.

Proof. Identify cube words with their binary integers and put

$$
S=\{0,1,2,4,8,16,32,127\},\qquad
R=\{1,2,4,8,16,32,64,127\}.
\tag{PCR.2007}
$$

Every edge incident to $0$ is met by one of the seven unit words in
$R$, and every other member of $S$ already belongs to $R$. Hence
$\mathsf H(S)\subseteq\mathsf H(R)$. The containment is strict, since
$\{64,65\}$ occurs only on the right. Thus $R$ meets every acquired
clause of $\mathsf H(S)$ without having the same profile. The eight
literal neighbours of any fixed right endpoint of either native
branch may be assigned the labels in $S$ by a full left injection;
all remaining literal endpoints can be assigned unused words.
This realizes the local ambiguity without changing the source family.
The common-twin and right-expansion steps of Theorem 20.3, rather
than a negative interpretation of missing profile edges, exclude full
native competitors. $\square$

## 21. Uniform attainment on the original fixed array

**Theorem 21.1 (no completed slot, every supported full injection).** Define

$$
\begin{aligned}
a&=7\cdot1944=13608,\\
b_0&=27\cdot8\cdot6\cdot8=10368,& q_0&=a+b_0=23976,\\
b_1&=9\cdot8\cdot6\cdot8=3456,& q_1&=a+b_1=17064.
\end{aligned}
\tag{PCR.2101}
$$

For every $\theta\in[0,1]$, every branch $i$ supported at that value,
every full injection pair on that branch and every originally fixed
$N\ge q_i$, a public source-independent original-root Read schedule
has an attained cache at its $q_i$-slot cut which passes Definition
20.2 and forces the entire actual labelled relation. Every scanned
slot has exactly fourteen acquired bits; every other original slot
is unread. Conditional on that generator, a specified sufficient event
has probability $1944^{-q_i}>0$.

Proof. Fix the generator only to describe an event in its original iid
preparation. Order its $1944$ actual edges. For each edge assign seven
separate original indices, one per omitted left coordinate. These
$a$ indices give exactly $H_y=\mathsf H(S_y)$ at every actual right
word. Every actual column is an eight-set, so the profile tests pass.
The support, degree and intersection conditions come directly from
(PCR.1) and UJB Theorem 15.2, with no coding restriction.

In each actual right twin class choose six of its distinct labels.
This is a mathematical choice for the event, not observer knowledge.
For each of the class's eight neighbouring left labels, and each of
its six chosen right labels, assign eight further separate indices,
one per omitted right coordinate. In $G_0$ there are twenty-seven
classes of size nine, giving $b_0$ indices. In $G_1$ there are nine
classes of size twenty-seven, giving $b_1$. Each $T_{x,C}$ contains
these six words and passes (PCR.2006). Thus the criterion returns the
entire actual relation against every full injection of both branches.

The single public sequence of omitted coordinates is

$$
h(j)=
\begin{cases}
1+((j-1)\bmod7),&1\le j\le a,\\
8+((j-a-1)\bmod8),&j>a.
\end{cases}
\tag{PCR.2102}
$$

At index $j$, read every other local coordinate with the canonical
original-root operand from UJB §5.3. The order of those fourteen
queries can be increasing coordinate order. The sequence uses only
$j$ and public constants. It has no branch, hidden map, chosen-edge
or sample-equality input. The two displayed cuts are public positions
in this same sequence; a controller with a declared public finite cap
may inspect the criterion there. No unknown branch is supplied as a
stopping instruction.

Order the witness edges at the fresh indices so that their intended
omissions follow (PCR.2102). Each index in the first portion lists
its edge's seven omissions consecutively; each index group in the
second lists its edge's eight right omissions. The event that the
first $q_i$ originally prepared samples equal this ordered edge sequence
has probability $1944^{-q_i}$. All remaining original slots are
unrestricted. The schedule does not assert that its samples realize
this event or that repeated partial records came from equal edges.
The event proves positive attainment; recognition uses only the
acquired clauses. All specified repetitions occupy distinct paid
indices. The theorem applies at the displayed cut without enlarging
$N$ or requesting a sample.

At $\theta=0$ the attained statement concerns every $G_0$ injection;
at $\theta=1$ every $G_1$ injection; for $0<\theta<1$ it concerns each
branch and every injection on that branch. Soundness was proved even
against the union of both native families. Unsupported branches do
not acquire positive prior mass at an endpoint. A wholly unread
reserved original index requires $N\ge q_i+1$ and leaving it untouched.
$\square$

**Proposition 21.2 (literal tariff at the two cuts).** The schedule through
a displayed cut $q=a+b_i$ makes exactly $14q$ original-root Reads. Its
sum of literal operand lengths is $105q^2+25a+(35/2)b_i$, and its
maximum literal operand length is $15q$. The values are

| Actual witness branch | Proper scanned slots | Read invocations | Operand-length sum | Maximum length |
| --- | --- | --- | --- | --- |
| $G_0$ | $23976$ | $335664$ | $60359622120$ | $359640$ |
| $G_1$ | $17064$ | $238896$ | $30574310760$ | $255960$ |

Proof. For acquired local coordinate $h$ of index $j$, UJB's operand
is $R^{15(j-1)+h-1}LL$, of length $15(j-1)+h+1$. Omitting $h(j)$
leaves length sum $210(j-1)+134-h(j)$ at that index. The first
$a$ omissions have mean $4$, since $a$ is divisible by seven; the
remaining $b_i$ have mean $23/2$, since $b_i$ is divisible by eight.
Summing gives

$$
105q(q-1)+134q-4a-\frac{23}{2}b_i
   =105q^2+25a+\frac{35}{2}b_i.
\tag{PCR.2103}
$$

The last omitted coordinate is fifteen. The last acquired coordinate
is fourteen at $j=q$, with length $15q$; all earlier lengths are
smaller. Every actual repetition or additional Read is charged at its
own invocation and length. The values count the prescribed cut, not
an assumed earlier successful stop. $\square$

## 22. Full relation recovery with genuinely unresolved realized bits

**Theorem 22.1 (some codings preserve many fair missing bits).** Among the
full injections allowed in Theorem 21.1 there are $G_0$ codings whose
attained witness caches retain at least $1944$ unresolved realized
bits, and $G_1$ codings with at least $5832$. Each listed bit is fair
conditional on the acquired cache, even though that cache forces the
entire labelled relation. These examples impose no coding condition
on Theorems 20.3 and 21.1.

Proof. In $G_0$, label the two endpoints in each of the thirty-six
literal left twin pairs by $p0,p1$, using thirty-six distinct six-bit
prefixes $p$. These are $72$ distinct seven-bit words. Any full right
injection is allowed. At each of the $1944$ first-portion indices
omitting the final left bit, the two possible left words are these
twins, with the same fully read right neighbour. Both completions
belong to the now-forced relation.

In $G_1$, assign the eight left endpoints of each of its nine components
the words $pu$, with nine distinct four-bit prefixes $p$ and all
three-bit suffixes $u$. Toggling any suffix bit stays in that component.
For each of the last three left coordinates, all $1944$ corresponding
first-portion indices therefore have two supported completions. This
gives $3\cdot1944=5832$ such indices. Both constructions extend to the
original full injections, and their right labels remain unrestricted.

Apply the existing UJB.9004–9005 conditional product law, equivalently
UJB Theorem 17.1, with the actual indexed masks retained. Once the
criterion has forced $E$, every compatible generator has this same
relation, and each of these rectangles has exactly two edges of $E$.
Its missing bit has probability $1/2$ for each value. The conditioning
here is on the acquired cache, not additionally on the unobserved
ordered witness event used to prove attainment. In particular that
event does not give the observer its prescribed full samples. The
original masks remain proper after relation inference. $\square$

**Definition 22.2 (unchanged recovery consumers).** On acceptance use the
returned whole $E$, together with the entire actual indexed cache,
as input to UJB Theorem 17.1 and Proposition 6.1. Their existing
$Q_{E,j}$ law supplies each original reply, positive partial update,
repeat, completed-slot replay and bounded adaptive continuation with
the declared controller. It does not identify unacquired realized
values. For $G_0$, the same returned $1944$-edge labelled relation is
valid input to Proposition 8.7 for intrinsic heap, marked directions
and full affine incidence. UJB Theorem 17.2 retains its fixed prior,
fixed indexed cache and actual wholly unread index on its stated
inverse domains. The reserved index in Theorem 21.1 is an original
slot, not a replacement sample.

## 23. Mask obstructions and essential endpoint evidence

**Theorem 23.1 (one globally unread coordinate always obstructs).** Fix
either supported actual branch, any full injections, any fixed $N$,
and any attained cache $K$. If some one of the fifteen coordinates
is omitted from every original index mask, then $K$ does not force
the entire labelled relation. This holds for every such injection,
including the invariant-left case, at every $\theta$ endpoint at
which the actual branch is supported.

Proof. Postcompose the corresponding entire label injection with the
fixed coordinate flip, as in the global transport of UJB §9.4. This
is another supported full injection on the same branch. Flipping that
coordinate in the actual samples leaves every acquired restriction
unchanged, because it was unread everywhere. If the transported
relation changes, it is already a compatible different target.

For a right coordinate the relation always changes: its used right
support has odd cardinality $243$ and cannot be invariant under a
fixed-point-free involution. For a left coordinate suppose instead
that the entire relation is flip invariant. Each used left word $x$
then has a used partner $x^h$ with the identical row neighbourhood.
Choose one $x$ and move only its literal endpoint's injection value
to an unused left word $u$; there are $128-72=56$ choices. Keep the
other injection values and branch unchanged. Any rectangle previously
met at an edge $(x,y)$ is still met at $(x^h,y)$, since the omitted
coordinate cannot distinguish them; all other edge witnesses remain
unchanged. Thus every original rectangle is still positive. The new
relation changes its left support from $x$ to $u$, so its target is
different. All these full injections have positive prior mass on the
same supported branch. The alternative generators and compatible
finite arrays are possible source worlds, not physical source edits,
inverses or extra operations. $\square$

**Theorem 23.2 (positive-essential endpoints and the finite-slot floor).**
For an attained cache $K$ with actual relation $E$, call an original
index $j$ right-essential for a used right word $y$ when the right
projection of $E\cap B_j(K)$ is exactly $\{y\}$. Define left-essential
symmetrically. If $K$ forces the entire actual $E$, each of its $243$
right words and $72$ left words has an essential original index.
Consequently at least $243$ distinct indices with nonempty acquired
masks are necessary, even if completed slots are allowed. In particular
no cache can force the whole target when the original $N<243$.

Proof. If $y$ has no essential index, every nonempty intersection
$E\cap B_j(K)$ has an edge whose right endpoint differs from $y$.
Move just the literal endpoint labelled $y$ to an unused right word,
keeping all other injection values and the branch. There are
$256-243=13$ unused choices. Each rectangle keeps its unchanged
witness at a different endpoint, so the new generator is compatible.
Its target differs, since the moved endpoint has degree eight. The
same proof on the left uses the $56$ unused words and degree $27$.
Each alternative remains a full injection on the same supported
branch with positive prior mass, including at its allowed $\theta$
endpoints.

One original index is right-essential for at most one right word.
An empty-mask rectangle meets all of $E$ and is essential for none.
Thus $243$ distinct nonempty-mask indices are required. A single index
can be essential on both sides, so adding $72$ and $243$ would not
prove a general $315$-index bound. This argument concerns the actual
partial rectangles, and does not assume that any whole endpoint was
physically read. $\square$

## 24. Domains and mathematical suppliers of proper-mask recovery

**Definition 24.1 (scope of the recovered structure).** The results in
§§20–23 keep the following mathematical and operational domains.

* The full source is (PCR.1), with $B_i(v,w)=s$ and unrestricted $z$.
  Its degrees, twin capacities and distinct-column intersection bound
  are reused from UJB §§15 and 18. The new source-specific bridge is
  positive proper-mask profile recovery, preservation of the entire
  labelled right twin partition under both varying injections, and
  exclusion of a lost incidence by the acquired right-probe expansion.
  The general target criteria cited in §7 and UJB's all-mask evaluator,
  exact posterior, continuation and closure results are suppliers,
  not new results of these sections.
* Harper's theorem is used only in the attributed intermediate step
  inside Theorem 20.3. The profile, native-capacity and attained-array
  argument is repository-derived ordinary mathematics. No general
  literature theorem or worldwide priority is claimed for it, and
  no new Lean declaration or fresh kernel verification is asserted.
* The witness gives positive attainment for every injection at the
  stated sufficient fixed-$N$ thresholds. It is not guaranteed on
  every preparation, an exact acceptance probability or a deterministic
  acquisition budget. Repeated samples may fail to expose enough
  evidence; once the original finite array is exhausted there is no
  new draw. The minimum feasible $N$, optimum Reads and recognition
  of all forcing partial caches are unresolved. Theorems 23.1–23.2
  are necessary obstructions, not a complete converse.
* All scanned witness slots remain proper and the complete-pair set
  used in Definition 1.1 is empty. This is a different recovery
  capability, outside the positive-complete-pair lower bounds of §4.
  No Read, address-length or acquisition-probability improvement over
  the existing $417$-pair $G_0$ or $324$-pair $G_1$ routes is asserted.
  The six-probe sharpness concerns only (PCR.2006), not native optimality.
* Actual $\alpha/\beta$ LAB $P/S$ preparation remains UJB §§5.2–5.3,
  with $75N+4$ events for the whole originally fixed $N$. Random
  preparation, its iid edge law and once-shared full injections remain
  supplied premises. Preparation operands and maps, controller
  installation and counters, graph and clause computations, comparisons,
  output and retained storage are separately paid resources. The
  acquired-profile computation uses at most $243\cdot9$ small profile
  candidates, each generated by $8\cdot7$ cube adjacencies, plus degree,
  intersection and finite probe tests on the $128/256$ ambient words.
  Deduplicating clauses for those tests does not discard the full
  indexed masks, values or original records. No source-aware state
  or free controller is supplied.
* Every original record/reply/return behavior and private-owner
  permission remains in force. No Busy query, membership or source
  oracle, chosen-edge port, sampler, fork, reset, interrupt, graft,
  physical inverse or new owner access is introduced. The returned
  relation does not recover a hidden frame, actual affine origin,
  twin coordinates, serial preparation history, physical spacetime
  or all unacquired realized bits. Its geometry and lawful continuation
  consumers have the exact domains in Definition 22.2. The broader
  mutual-recovery programme remains outside this finite local result.

## 追加锚（本行以下为增补区）

## 25. Acquired endpoint dictionaries and indexed erasure

The proper-mask results above can be joined to the positive-certificate
recognizer without changing an indexed mask.  The join is an erasure
construction: a word that is absent from one mask can be recovered from a
finite acquired dictionary, but the absent bit remains absent from the
physical record and from the retained cache.

**Definition 25.1 (field dictionaries of an indexed cache).** Write

$$
L=\{1,\ldots,7\},\qquad R=\{8,\ldots,15\},\qquad
\ell(y)=y|_L,\quad r(y)=y|_R.
$$

For an indexed cache $K=((m_j,d_j))_{1\le j\le q}$, define the two
full-field dictionaries

$$
\begin{aligned}
X(K)&=\{d_j|_L:L\subseteq m_j\},\\
Y(K)&=\{d_j|_R:R\subseteq m_j\}.
\end{aligned}
\tag{PCR.2501}
$$

The first set is obtained only from records whose seven left bits were
physically read, and the second only from records whose eight right bits
were physically read.  A dictionary is a set of acquired words; it is not
an inferred mask and does not replace any $m_j$.  We call $K$

* **support-exhausting** when $|X(K)|=72$ and $|Y(K)|=243$;
* **field-singleton** when, for every $j$,

  $$
  C_j(K)=\{(x,y)\in X(K)\times Y(K):
       x|_{m_j\cap L}=d_j|_{m_j\cap L},
       y|_{m_j\cap R}=d_j|_{m_j\cap R}\}
  \tag{PCR.2502}
  $$

  is a singleton.

When the second condition holds, write its unique member as
$\delta_j(K)=(x_j,y_j)$, and put

$$
D(K)=\{\delta_j(K):1\le j\le q\},
\tag{PCR.2503}
$$

with multiplicity removed only for the positive-certificate test.  The
ordered indices, masks, values and records remain part of $K$.

**Lemma 25.2 (support exhaustion fixes the two label images).** Suppose
an attained cache $K$ is support-exhausting for a generator $g$, and
let $g'$ be any full generator whose indexed rectangles contain the
same acquired records.  Then

$$
\lambda'(A)=X(K)=\lambda(A),\qquad
\varrho'(T)=Y(K)=\varrho(T).
\tag{PCR.2504}
$$

Proof.  If $x\in X(K)$, it is the completely read left field of one
record.  Any generator containing that record must therefore use $x$ as
one of its left labels.  Thus $X(K)\subseteq\lambda'(A)$.  The two sets
have cardinality $72$, so they are equal.  The right argument is the
same, with $243$ in place of $72$.  No hidden injection or source frame
has been supplied; the conclusion uses only the full words already
present in the two dictionaries and the declared injectivity. $\square$

**Lemma 25.3 (the indexed erasure bridge).** Let $K$ be attained by a
generator $g$, support-exhausting and field-singleton.  Then every
generator $g'$ compatible with $K$ contains every decoded pair in
$D(K)$:

$$
D(K)\subseteq\mathcal E_{g'}.
\tag{PCR.2505}
$$

In particular, if the full positive recognizer of Definition 1.2 accepts
$D(K)$, all compatible generators have the same $1944$-edge target.

Proof.  The actual pair at index $j$ belongs to $X(K)\times Y(K)$ and
has the acquired restrictions, so it lies in $C_j(K)$.  By the
singleton condition it is $\delta_j(K)$.  A compatible $g'$ also has
the same restrictions; Lemma 25.2 gives the same two label images, and
the singleton condition again puts its positive pair at the same
$\delta_j(K)$.  Hence (PCR.2505).  Definition 1.2 enumerates every
full injection on these two images on both supported branches and tests
target equality.  Its acceptance therefore applies to all of
$\mathcal G_\theta$, not merely to the coding class used to attain the
cache. $\square$

The lemma is deliberately weaker than completing a mask.  A missing bit
may be logically forced by (PCR.2502), while the original $m_j$, the
unread value, and its indexed position stay unchanged.  If a cylinder is
not a singleton, the record remains a proper partial record and no
decoded pair is entered in $D(K)$.  Thus the construction does not
interpret an absent value as a negative observation.

## 26. A common deterministic omission schedule

Use one public schedule, independent of source, injection, sampled edge,
dictionary and controller.  At index $j$, omit the coordinate

$$
h(j)=
\begin{cases}
14,&1\le j\le36,\\
15,&37\le j\le72,\\
7,&73\le j\le401,\\
6,&402\le j\le409,\\
5,&410\le j\le417,
\end{cases}
\tag{PCR.2601}
$$

and issue the fourteen standard original-root Reads for every other
coordinate.  The cut for $G_0$ is $q_0=417$; the cut for $G_1$ is
$q_1=332$.  The second cut stops in the $h=7$ block.  The first
seventy-two records read every left field in full, while the records with
omission $7,6$, or $5$ read every right field in full.  The schedule
is therefore a public field-acquisition policy, not a branch-dependent
choice of mask and not a random seed.

For a fixed branch $i$, call an actual full injection **dictionary-$q$
attaining** when there is an ordered positive event of $q$ original
samples such that the resulting cache is support-exhausting and
field-singleton, and the decoded set $D(K)$ is accepted by the exact
full positive recognizer against all supported competitors.  Denote the
two classes by $\mathfrak C_0^{417}$ and $\mathfrak C_1^{332}$.  This
is an observable finite condition on acquired words and the public source
description; it is not a promise that all full injections belong to the
class.  All full injections remain in the version set used by the
recognizer.

The classes are nonempty.  A concrete finite realization uses distinct
prefixes for the quotient types and the literal capacities: for $G_0$,
six-bit prefixes for the $36$ line types followed by one representative
bit, and five-bit prefixes for the $27$ point types followed by four
representative bits; for $G_1$, four-bit prefixes for its nine
components followed by three left bits, and five-bit prefixes followed by
three right bits.  Assign the suffixes in the fixed lexicographic order
of the literal endpoints.  In the $G_1$ realization, order the first
$324$ distinct pairs as the connected $K_{3,10}$ core and eight
connected spanning component witnesses of §3, then use eight separately
indexed repeats.  In the $G_0$ realization, order the $417$ chosen
incidences by the four affine direction classes and then by their literal
lifts.  The type-level incidence table has respectively $72$ and
$243$ distinct acquired words; applying (PCR.2502) to that table gives
singleton cylinders at every displayed index, and the decoded pairs pass
Definition 1.2.  This is a finite check on $36+27$ or $9$ quotient
types and their capacities, not an enumeration of the factorial family
of full injections.  It is a witness of nonemptiness, not a universal
coding theorem.

**Theorem 26.1 (source-independent positive attainment).** For every
$g\in\mathfrak C_i^{q_i}$, every $N\ge q_i$, and every value of
$\theta$ at which branch $i$ has positive prior weight, the common
schedule (PCR.2601) has a positive ordered attainment event at its
$q_i$-cut.  On that event it returns the whole labelled native relation
$\mathcal E_g$ against every supported competitor.

Proof.  Take the ordered positive edge tuple in the definition of the
class and require the first $q_i$ iid prepared slots to equal it.  Each
specified slot has probability $1/1944$, so the event has probability
$1944^{-q_i}$; all later slots are unrestricted.  The acquired
dictionary is computed from the records with the indicated full field,
and field-singleton decoding gives (PCR.2503).  Lemma 25.3 and the exact
recognizer then force the common target.  The controller does not inspect
the hidden source, choose an edge, or request a new sample.  A positive
event is not a guaranteed finite success of the random preparation. $\square$

For $G_1$, the first $324$ records in this witness are distinct
positive pairs and the last eight are repeats at separate original
indices.  Repetition is retained in the indexed cache and in the
continuation law.  For $G_0$, the $417$ records are likewise a
fixed finite witness event; no complete-pair certificate is claimed for
arbitrary $G_0$ codings outside $\mathfrak C_0^{417}$.

## 27. The scoped $332$-record result for $G_1$

The following lower bound is about a declared acquisition class, not an
unrestricted optimum over arbitrary partial caches.

**Definition 27.1 (full-field dictionary/$K_{3,10}$ class).** A
$G_1$ cache belongs to $\mathfrak K_{3,10}^{332}$ when it has the
support-exhausting and field-singleton properties of §25, its decoded
positive pairs contain a $K_{3,10}$ in one component, and its distinct
distinct decoded pairs contain a connected spanning subgraph on all eight left
and twenty-seven right labels in each of the nine components.  The
eight tail indices of (PCR.2601) are required to be separately indexed
dictionary-resolution records for the eight left labels of the
$K_{3,10}$ component.  This last clause is a continuation requirement:
it does not identify a repeated record with its earlier occurrence.

**Theorem 27.2 (exact $332$ tariff in the declared class).** Within
$\mathfrak K_{3,10}^{332}$, the common schedule attains the complete
labelled $G_1$ relation at $332$ original indices, and no schedule
with the same full-field dictionary, $K_{3,10}$, and indexed-tail
requirements can use fewer than $332$ indices.

Proof.  In the component containing $K_{3,10}$, the $30$ core edges
already expose three left and ten right vertices.  The core is one
connected component.  To attach the remaining five left and seventeen
right vertices to that component requires at least twenty-two further
edges: each added edge can reduce the number of connected components by
at most one, and there are twenty-two new vertices.  Thus that component
requires at least $30+5+17=52$ distinct pairs.
Every other component has $8+27$ vertices and must contain a connected
spanning positive subgraph, hence at least $8+27-1=34$ edges.  The
components are disjoint, so at least

$$
52+8\cdot34=324
\tag{PCR.2701}
$$

distinct positive pairs are necessary.  This is the same-capacity
argument as the $K_{3,10}$ obstruction and the connected witnesses in
§3; it keeps the literal $8,27$ capacities and does not replace them
by uncapacitated type weights.

Under the fixed schedule, the eight core left labels have to occur in
the separately indexed left-omission tail to make their field
dictionary and the old-slot continuation both available.  One original
index has one prepared edge and therefore resolves at most one of these
eight required tail occurrences.  The indexed-tail requirement costs at
least eight additional records, even when their decoded pair is a
repeat.  Hence $q\ge324+8=332$.  The construction in §26 has exactly
the $324$ distinct pairs and exactly those eight indexed repeats; its
field-singleton check and Lemma 25.3 give the matching upper bound.  No
claim follows for a cache that drops the full-field dictionary, omits the
$K_{3,10}$ source separation, or forgets original indices. $\square$

The first $324$ records are a positive complete-pair certificate in
the sense of §3 after erasure decoding.  The eight extra records are not
silently folded into that set: they remain available to UJB Theorem
17.1 as eight original indexed factors.

## 28. Resource comparison and the two cuts

For the standard operand at index $j$, local coordinate $h$ has
length $15(j-1)+h+1$, as in (UJB.9008).  Summing the fourteen read
coordinates at each scheduled index gives the following exact tariff.

| actual witness | cut | distinct positive pairs | Reads | operand-length sum | maximum length |
|---|---:|---:|---:|---:|---:|
| $G_0$ dictionary class | $417$ | $417$ witness records | $5838$ | $18\,267\,003$ | $6256$ |
| $G_1$ dictionary/$K_{3,10}$ class | $332$ | $324$ plus $8$ indexed repeats | $4648$ | $11\,580\,284$ | $4981$ |

For $G_0$, reading all fifteen coordinates through index $417$ would
cost $6255$ invocations, length sum $19\,571\,895$, and maximum
$6256$.  The common proper schedule saves $417$ invocations and
$1\,304\,892$ operand symbols while retaining the same maximum.  For
$G_1$, reading all fifteen coordinates of the $324$ distinct-pair
prefix would cost $4860$ invocations, length sum $11\,817\,090$,
and maximum $4861$.  The $332$-index schedule saves $212$ invocations
and $236\,806$ operand symbols, but its maximum is $4981$.  The two
rows are therefore a vector comparison, not a scalar optimum claim.

The calculation is direct. If $H_q$ is the omitted coordinate list,

$$
\sum_{j=1}^{q}\sum_{h\ne H_q(j)}(15(j-1)+h+1)
 =\sum_{j=1}^{q}\sum_{h=1}^{15}(15(j-1)+h+1)
  -\sum_{j=1}^{q}(15(j-1)+H_q(j)+1).
\tag{PCR.2801}
$$

For $q=332$ and $417$, the right side is respectively
$11\,580\,284$ and $18\,267\,003$; the largest acquired coordinate
is $14$ at the last index, giving $4981$ and $6256$.  Every repeat
is charged at its own original operand, and the fixed $N$, LAB
preparation $75N+4$, cache flags and values, dictionary construction,
controller, navigation, computation, output and retained records remain
separate paid axes.

## 29. Indexed continuation after erasure decoding

After recognition, retain the original $K=((m_j,d_j))$, including the
proper masks, all recorded values, repeated indices and any wholly
unread slots.  Use the recovered $E=\mathcal E_g$ as the relation input
to UJB Theorem 17.1.  For each old index, its factor remains

$$
Q_{g,j,K}(y)=
\frac{\mathbf 1_{\{y\in E\cap B_j(K)\}}}
 {|E\cap B_j(K)|},
\tag{PCR.2901}
$$

with the original $B_j(K)$, not a completed rectangle.  A bit inferred
from a singleton dictionary cylinder is marked logically forced in the
observer's computation; it is not added to $m_j$, and an unread
realized value is not claimed to have been physically acquired.  UJB
Theorem 17.1 therefore supplies the same replies, positive partial
updates, repeats, completed-slot replay and bounded adaptive
continuations as before.  Geometry and the affine incidence consumers
are called only after $E$ has been recovered, as in Definition 22.2.

The schedule has no random seed and no source-dependent branch.  This
removes seed entropy from the controller contract, but it does not make
the controller, address computation, dictionary, output or retained
state free.  The original source preparation, its supplied iid law and
full shared injections remain premises of UJB §§5.2--5.3.  No membership
query, source oracle, chosen-edge port, sampler, reset, interrupt, fork,
graft, physical inverse or extra owner permission is introduced.

## 30. Scope and unresolved boundary

The new bridge is the composition

$$
\text{full acquired support}
\longrightarrow
\text{singleton erasure cylinders}
\longrightarrow
\text{positive full-pair evidence}
\longrightarrow
\text{existing native recognizer and indexed continuation}.
\tag{PCR.3001}
$$

It preserves both source branches, unrestricted $z$, all $1944$
literal edges, every supported competing full injection, the original
record/reply/return contract, and the distinction between acquired and
logically forced bits. The $417$ assertion is only positive attainment
on the explicitly declared nonempty class $\mathfrak C_0^{417}$. The
$332$ equality is only the full-field dictionary/$K_{3,10}$ tariff of
Theorem 27.2. Neither is a deterministic success guarantee, an optimum
over arbitrary partial caches, or a replacement for the universal
proper-mask theorem of §§20--24.

The finite prefix-coded witnesses establish existence of actual coding
classes, while the recognizer continues to quantify over all supported
competitors. No claim is made that the dictionaries identify a hidden
affine frame, the realized preparation history, a serial extension, or
the complete realized array. The general mutual recovery of space, time,
boundary and memory remains outside this local source-specific bridge.
