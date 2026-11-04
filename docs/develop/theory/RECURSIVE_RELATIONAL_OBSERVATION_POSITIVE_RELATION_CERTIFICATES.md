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
