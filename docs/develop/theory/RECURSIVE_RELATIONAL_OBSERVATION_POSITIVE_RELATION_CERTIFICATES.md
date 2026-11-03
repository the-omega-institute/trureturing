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

## 8. The certified G0 relation carries an affine torsor

**Definition 8.1 (intrinsic quotient and marked parallel classes).** Let
$E\subseteq X\times Y$ be an acquired complete-label relation which has passed
Definition 1.2 with the unique surviving source $G_0$. Define

$$
\begin{aligned}
Q(E)&=Y/\{y\sim y'\Longleftrightarrow N_E(y)=N_E(y')\},\\
L(E)&=X/\{x\approx x'\Longleftrightarrow N_E(x)=N_E(x')\},
\end{aligned}
$$

where $N_E$ denotes the complete opposite-side neighbourhood. Write
$\bar E\subseteq L(E)\times Q(E)$ for the induced incidence. The capacities
are two for every class in $L(E)$ and nine for every class in $Q(E)$. Let
$\mathfrak P(E)$ be the finite set of subsets $\Pi\subseteq L(E)$ such that
$|\Pi|=9$, the point sets
$P_E(\ell)=\{q\in Q(E):(\ell,q)\in\bar E\}$ for its nine members are
pairwise disjoint and their union is $Q(E)$. Thus $\Pi$ is a partition of
the twenty-seven point classes by nine parallel line classes. A marked quotient is a bijection
$\delta:\mathfrak P(E)\to\mathbb P_0$, where

$$
\mathbb P_0=\{F(0,0,1),F(1,0,0),F(1,2,1),F(1,1,1)\}\subseteq\mathbb P^2(F).
$$

A marked affine chart is a pair $(\phi,\delta)$ with a bijection
$\phi:Q(E)\to F^3$ such that, for every $\Pi\in\mathfrak P(E)$ and
$\ell\in\Pi$,

$$
\phi(\{q\in Q(E):(\ell,q)\in\bar E\})
 =\{u+t d:t\in F\}
$$

for some $u\in F^3$ and $d\in\delta(\Pi)\setminus\{0\}$, and every affine line
of one of the four marked directions occurs in this way. The direction marks
are labels of the four intrinsic parallel classes; they are not an origin or
an injected endpoint map.

**Theorem 8.2 (origin-free affine operation).** For every transported $G_0$
relation $E=(\lambda\times\varrho)(E_0)$, the sets $Q(E)$, $L(E)$ and
$\mathfrak P(E)$ are intrinsic, $|Q(E)|=27$, $|L(E)|=36$,
$|\mathfrak P(E)|=4$, and a marked affine chart exists. For any such chart
put

$$
H_{\phi}(p,q,r)=\phi^{-1}\bigl(\phi(p)-\phi(q)+\phi(r)\bigr).
\tag{RRO.8.1}
$$

Then $H_{\phi}$ is independent of every permissible chart, ordering of
representatives inside a twin class, and choice of origin. It is the unique
origin-free affine ternary operation whose marked affine lines are the
incidence lines of $\bar E$. In particular, it recovers all incidences in the
four supplied directions and satisfies

$$
H(p,q,q)=p,\qquad H(p,p,r)=r,
$$

and the affine parallelogram law
$H(H(p,q,r),s,t)=H(p,q,H(r,s,t))$ whenever both sides are read in the same
marked affine torsor.

**Proof.** The equal-neighbourhood relation is exactly the twin relation in
UJB Theorem 15.2. Its proof gives two-element left classes, nine-element
right classes, the thirty-six affine lines, the twenty-seven points and the
four listed direction vectors. A finite enumeration of partitions of $Q(E)$
by the induced three-point incidence blocks therefore obtains exactly the
four members of $\mathfrak P(E)$; no coordinate, hidden map or unacquired
label is used in that enumeration.

Choose one chart supplied by the literal identification in UJB Theorem 15.2.
If $(\phi',\delta')$ is another admissible chart, the frame and full-closure
hypotheses of Cara--Rottey--Van de Voorde, arXiv:1207.4726v3,
Corollaries 3.6--3.7, apply to the order-three point classes and their four
marked line directions. Their rigidity conclusion says that the two
coordinatizations differ by an affine change
$\phi'=A\phi+b$ (with the corresponding permutation of the marked direction
classes), where $A$ is invertible over $F$. This is precisely the supplied
$G_0$ instance; the corollaries are used as a rigidity and correspondence
supplier, not as a new theorem about this repository relation.

For $x,y,z\in F^3$,

$$
(Ax+b)-(Ay+b)+(Az+b)=A(x-y+z)+b.
$$

Applying this identity and then $\phi'^{-1}$ gives
$H_{\phi'}=H_{\phi}$. Reordering the two representatives of a left class or
the nine representatives of a right class does not change $Q(E)$, $L(E)$ or
$\bar E$, so it cannot change $H$. Replacing the origin by $o$ replaces
$\phi$ by $\phi-o$, and the same identity again leaves (RRO.8.1) unchanged.
The two displayed identities and the parallelogram law are the corresponding
identities in $F^3$, transported through $\phi$. Conversely, the condition
that every marked line is an affine line determines the four-direction
incidence table, so the operation is the unique ternary operation with these
properties. $\square$

The construction has a finite, explicit input contract. It consumes the
complete acquired relation, the observed endpoint words and the declaration
that the unique surviving branch is $G_0$; it computes neighbourhood hashes,
twin classes, candidate partitions and a finite chart table. Its working
storage, finite-field arithmetic and chart enumeration are additional
computation costs. No claim of an optimal chart algorithm, a reduced
acquisition cost, or a lower bound on this computation is made.

**Theorem 8.3 (exact reverse correspondence and literal lift).** Let
$\mathcal A=(Q,L,\bar E,\mathfrak P,\delta)$ be the marked quotient of
Theorem 8.2, and retain actual bijections
$\lambda:A\to X$ and $\varrho:T\to Y$ from the literal endpoint sets to
the acquired labels. Let $[a]_L$ and $[t]_R$ denote the classes determined by
those associations. Define

$$
\operatorname{Lift}_{\lambda,\varrho}(\mathcal A)
 =\{(\lambda(a),\varrho(t)):
       ([a]_L,[t]_R)\in\bar E\}.
\tag{RRO.8.2}
$$

Then
$\operatorname{Lift}_{\lambda,\varrho}(\mathcal A)=
(\lambda\times\varrho)(E_0)$, and quotienting this lifted relation by equal
neighbourhoods returns $\mathcal A$ with its four marked directions. The
associations, the original indexed masks and values, and the capacities
$2,9$ are retained in this inverse; they are not replaced by the chart.

**Proof.** UJB Theorem 15.2 says that two literal left endpoints have the
same neighbourhood exactly when they are the pair $(v,s),(-v,-s)$, and two
literal right endpoints have the same neighbourhood exactly when they have
the same $w$ and arbitrary $z$. It also says that literal adjacency is exactly
incidence of the corresponding affine line and point, with every pair above an
incidence present. Substituting these two equivalences into (RRO.8.2) gives
the defining edge equation of $E_0$ in both directions. The same equivalences
show that quotienting recovers precisely the classes and incidence table.
No chart coordinate is consulted by this argument; the marked directions only
identify which quotient classes correspond to the four supplied literal
kernels. $\square$

A common controller can compute $H$ and the lifted relation from retained
labels and then continue with the existing stationary original-root Read
menu. The computation introduces no source action. The public $N$, the
original repeated-index coupling and all masks remain fixed. For a scan of
$m$ completed samples, the controller still makes exactly $15m$ original
Read invocations and pays the operands in (PCR.6); for later adaptive use it
uses the indexed ratios (UJB.17001)--(UJB.17003). The relation-derived output,
its finite arithmetic and its storage are charged separately from acquisition,
preparation, installation and the $N$ prepared slots.

## 9. Inversion labels: a source-specific recovery boundary

**Definition 9.1 (the commuting-edge inverse).** In the finite-group witness
of [FGP, Definitions 1.1--1.2](FINITE_GROUP_POWER_MAP_SEPARATION.md), write
$a=(v,s)\in A=(F^2\setminus\{0\})\times F^2$ and
$t=(w,z)\in T=F^3\times F^2$. Embed them in $S_i$ as

$$
\widetilde a=(v,0,s;0),\qquad
\widetilde t=(0,w,z;1).
$$

The multiplication in (1.2)--(1.3) gives

$$
\widetilde a\widetilde t=\widetilde t\widetilde a
\quad\Longleftrightarrow\quad B_i(v,w)=s,
\tag{RRO.9.1}
$$

and $\widetilde a^{-1}=(-v,0,-s;0)$. Thus the inverse-label map on an input edge
is

$$
\iota(v,s)=(-v,-s).
\tag{RRO.9.2}
$$

This is a group-theoretic interpretation of the already defined relation; it
is not an additional group-operation port supplied to the observer.

**Theorem 9.2 (G0 point recovery and G1 inversion ambiguity).** Fix an
acquired input edge $(x,y)\in E$ and suppose the certified branch is $G_0$.
The inverse label of $x$ is recovered from $E$ and the acquired input as the
unique label $x'\ne x$ having $N_E(x')=N_E(x)$. For the certified branch
$G_1$, there are supported realizations with the same complete relation $E$
and the same entire prepared label array but with different inverse labels
for that same input edge.

**Proof.** In $G_0$, UJB Theorem 15.2 gives the left class
$\{(v,s),(-v,-s)\}$, and $v\ne0$ implies that its two members are distinct.
Equation (RRO.9.1) identifies the second member with the group inverse, so
the equal-neighbourhood search returns exactly $\iota(x)$.

For $G_1$, identify the first two coordinates with the field
$E_9=F[\iota]$. A left class is

$$
C_c=\{(v,s):v\in E_9^\times,\ s=cv\},\qquad |C_c|=8,
$$

whereas inversion maps $(v,cv)$ to $(-v,-cv)$ inside the same class. Choose
$a,b\in C_c$ with $b\notin\{a,-a\}$, and let $\sigma$ transpose $a,b$ and
fix every other left endpoint. It preserves every $G_1$ neighbourhood. Start
with any full injections $(\lambda,\varrho)$ and put
$\lambda'=\lambda\circ\sigma$. Since $\sigma$ preserves every left
neighbourhood, both transports have exactly the same label relation and hence
the same prepared array of complete edge labels, while both have positive
prior weight under UJB.9001.

Take an edge whose left label is $x=\lambda(a)$; its right endpoint exists
because every member of $C_c$ has the same nonempty neighbourhood. Under
$(\lambda,\varrho)$ its inverse output is $\lambda(-a)$. Under
$(\lambda',\varrho)$ the literal preimage of $x$ is $b$, and the inverse
output is $\lambda'(-b)=\lambda(-b)$, which differs from $\lambda(-a)$ by the
choice of $b$. The relation and all prepared labels are unchanged, so pointwise
inverse recovery fails on this supported pair of realizations. $\square$

**Definition 9.3 (exact conditional inverse law).** Let $D$ be any retained
indexed cache and let $\Omega_D$ be the finite set of tuples
$\omega=(i,\lambda,\varrho,y_1,\ldots,y_N)$ with positive UJB weight that
satisfy $D$. For a complete input edge $e$ present at an acquired index, let
$I_\omega(e)$ be the observed label of $\iota(a)$ when $e=(a,t)$ in the
literal realization $\omega$. The exact conditional inverse law is

$$
\Pr(I(e)=u\mid D,e)=
\frac{\sum_{\omega\in\Omega_D:\ I_\omega(e)=u}w(\omega)e_\omega(D)}
     {\sum_{\omega\in\Omega_D}w(\omega)e_\omega(D)}.
\tag{RRO.9.3}
$$

For a partial slot $j$ with observed mask-value pair $(m,c)$, replace the
numerator by

$$
\sum_{\omega\in\Omega_D}w(\omega)e_\omega(D)
 \sum_{e\in\mathcal E_{i,\lambda,\varrho}}
 \mathbf1_{\{\operatorname{mask}_m(e)=c\}}
 \mathbf1_{\{I_\omega(e)=u\}},
\tag{RRO.9.4}
$$

and the denominator by the same expression without the last indicator.
Here $e_\omega(D)$ contains the fixed indexed likelihood, so a shared latent
reference is summed once and is never independently redrawn for each target.

**Proposition 9.4 (marginal versus pointwise inverse).** If an unread edge is
uniform on the $1944$ edges, then $\iota(a)$ is uniform on the $72$ left
endpoints in both sources. This marginal fact does not imply (RRO.9.3) is a
point mass, and it does not identify the joint coupling of an input with its
inverse. For a wholly unread slot the law is exactly the ratio in (UJB.17001);
for a known bit, (UJB.17001) returns its recorded value with probability one.

**Proof.** Every left endpoint has degree $27$ in either literal source, so
uniform edge sampling makes $a$ uniform on $A$; (RRO.9.2) is a bijection of
$A$. The conditional statements are the indexed continuation theorem: a
known coordinate is replayed, while a new coordinate is conditioned through
one common version set. Theorem 9.2 supplies a $G_1$ fiber with two distinct
inverse outputs, so a uniform marginal cannot be promoted to pointwise
recovery. $\square$

## 10. Reference, memory and operation boundaries

**Definition 10.1 (the forgetful maps).** A realized continuation state is
$\Sigma=(i,\lambda,\varrho,D,\mathbf y)$, with fixed public $N$ and with
$D$ recording masks and values at their original indices. Let
$U_E(\Sigma)=E_{i,\lambda,\varrho}$ be the transported relation, let
$U_{\rm set}(\Sigma)$ forget the indices and retain only the distinct
complete pairs, and let $U_{\rm law}(\Sigma)$ be the unread conditional law.
A recovery statement below is always relative to one of these maps and to the
listed retained fields.

**Proposition 10.2 (concrete ambiguity witnesses).** The following pairs of
states have the same stated observations but different hidden structure.

1. **Origin and injection.** If $\phi$ is an affine chart of a certified
   $G_0$ quotient, then every $o\in F^3$ gives
   $\phi_o(p)=\phi(p)-o$. These charts have the same $H$ and incidence but
   different origins. Independently, composing the literal association
   $\lambda$ with any nontrivial translation of $F^3$ (and the induced
   affine permutation of line classes) preserves the transported relation.
   Hence $E$ determines an affine torsor and its marked directions, not a
   distinguished origin or the actual hidden injection.

2. **Indexed memory.** Choose two completed original indices $j\ne k$ and
   two distinct complete pairs $u,v$. Let $\Sigma$ store $y_j=u,y_k=v$ and
   let $\Sigma'$ store $y_j=v,y_k=u$, with the same relation and the same
   unordered set. Then $U_{\rm set}(\Sigma)=U_{\rm set}(\Sigma')$ and their
   unread law is the same iid law, but a later original-root Read of $j$
   returns $u$ in the first state and $v$ in the second. Thus an unindexed
   posterior or complete-generator law cannot replace the fixed indexed cache.

3. **Serial history.** The endpoint relation is static. The exact supplier
   NativePromiseCausalBoundary.result gives, for every promised $N\ge4$
   source in its declared domain, two different successful call words with
   the same endpoint and the same labelled causal order. Therefore an endpoint
   or a geometric quotient does not encode an actual serial preparation history.

4. **G1 geometry.** In $G_1$, the quotient is nine disjoint
   $K_{8,27}$ components. Arbitrary permutations inside each component
   preserve the unlabelled relation, while the free $w_3$ and $z$ coordinates
   have no incidence signature. An affine plane, an origin, or a $3$-dimensional
   coordinate frame is therefore not recovered from this component structure.

5. **Operations and samples.** The equations $B_i(v,w)=s$ and the commuting
   interpretation (RRO.9.1) define a static relation. They supply neither an
   executable multiplication/inversion port nor a source mutation. The model
   contains exactly the prepared $N$ samples; computing $H$, testing a candidate
   edge, or evaluating a posterior does not create an additional sample.
   Nothing in the relation specifies a quantum channel, a fresh random
   operation, or an independent latent draw.

**Proof.** Items 1 and 4 are the chart and component descriptions in
Theorem 8.2 and UJB Theorem 15.2. Item 2 is a direct two-array construction;
its later-read distinction is exactly the completed-slot clause of UJB
Theorem 17.1. Item 3 is the final existential clause of
NativePromiseCausalBoundary.result. Item 5 follows from the source
definition and the resource separation in UJB §§5, 9 and 17. Each pair has
identical observations under the named forgetful map but differs in the
omitted field, proving the asserted ambiguity. $\square$

**Theorem 10.3 (explicit recovery domains).** The following recovery claims
hold on exactly the stated domains.

(a) From a certified complete $G_0$ relation and its acquired endpoint labels,
$H$, the four intrinsic parallel classes, and the complete transported
relation are recoverable by Theorems 8.2--8.3. A distinguished origin,
literal injection, serial history, source mutation, group-operation port,
extra sample, or quantum/random operation is not supplied by this data.

(b) From fixed $N,\theta$, the full indexed partial cache, retained completed
values, and at least one unread index, the unread closure and all native
continuation laws are mutually recoverable by UJB Theorem 17.2. If the
indexed cache is discarded, if no unread index remains, or if the source is
changed, that inverse domain is absent.

(c) From a certified $G_0$ relation and a complete input edge, the inverse
label is recoverable. For $G_1$ it is recoverable only after an additional
orientation/association datum that selects the inverse pairing inside every
size-eight left twin class; the relation alone leaves the alternatives of
Theorem 9.2.

(d) A serial history is recoverable only when its actual causal event record
and its legal history-readout contract are retained. The static relation,
its affine chart, and the indexed iid law do not meet that premise.

These are conditional domains, not claims of a universal reconstruction or of
minimal acquisition. In particular, retaining a complete relation does not
turn a derived coordinate chart into a physical reference frame.

## 11. Suppliers, correspondence and scope

**Definition 11.1 (supplier correspondence).** The following existing results
are used with their stated hypotheses and no stronger interpretation.

* UJB Theorem 15.2 supplies the literal $G_0/G_1$ twin classes, capacities,
  all $72$ and $243$ endpoints, the four $G_0$ directions, the nine $G_1$
  components, and the free coordinates. UJB Theorems 16.2 and 17.1--17.2
  supply the exact capacity evaluator, indexed cache update, unread closure,
  completed-slot replay and fixed-$N$ continuation. The present formulas use
  these outputs rather than repeating their enumeration or changing their
  cost contract.
* FINITE_GROUP_POWER_MAP_SEPARATION.md, equations (1.2)--(1.3), (3.4), and
  (3.6)--(3.7), supplies the two finite semidirect products, the commuting-edge
  interpretation, and $a\mapsto a^{-1}$. It does not supply an observer
  operation on the source.
* InvolutionDescent.kernelStable_iff_exists_descended and
  InvolutionDescent.descended_unique supply the general fact that a stable
  transformation descends uniquely through a surjective readout. Applied to
  the equal-neighbourhood quotient, they justify why a permitted label
  involution has one quotient action when it is constant on quotient fibres;
  Theorem 9.2 shows that quotient descent alone does not choose a pairing
  within a $G_1$ fibre.
* TargetRecoveryCriterion.target_recovery_criterion supplies target
  constancy on observation fibres. Here the target is either the complete
  relation or the inverse-label map; the latter is constant on the $G_0$
  fibres and is not constant on the supported $G_1$ fibres exhibited above.
  PushforwardComposition.pushforward_comp supplies composition of the
  resulting finite conditional laws; it does not identify independently
  sampled latent references.
* ActualTreeReadoutAcquisition.readout supplies an actual address-indexed
  readout and its distinct-address tariff. It is used only as the model of a
  legal source read; the geometry computation has no extra Read. The
  NativePromiseCausalBoundary.result supplier is the serial-history
  counterexample used in Proposition 10.2.
* Cara--Rottey--Van de Voorde, [arXiv:1207.4726v3,
  Corollaries 3.6--3.7](https://arxiv.org/abs/1207.4726), supplies the
  rigidity of the specified order-three frame/closure configuration. De
  Winter--Rottey--Van de Voorde, [arXiv:1407.3953v1](https://arxiv.org/abs/1407.3953),
  supplies the frame and closure terminology used to state the hypothesis.
  These references do not supply the transported labels, the positive
  certificate, or the controller and acquisition costs here.
* Existing RRO Proposition 92.2, AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II,
  §92, is a support-safe variational bound: it restricts a norm calculation to
  the actual support before applying an inverse. Its methodological
  correspondence here is that a quotient or support calculation cannot be
  treated as an acquired operation on an omitted fibre; no quantum conclusion
  is imported.
* The C107 collective-cut stability and StaticTensorWorld formal source are
  comparison domains only. Their common preparation, joint effects and
  tensor assumptions are not present in this two-source relation, so they do
  not supply a reference, quantum, or random-operation bridge.

**Proposition 11.2 (scope and falsifiers).** The constructions above are
ordinary finite mathematics on the declared $F_3$ source and its acquired
labels. They do not claim Lean certification, optimal certificate size,
minimum actual sample complexity, efficient chart construction, world
novelty, or existence of a physical spacetime interpretation. A finite
counterexample to any of the following would falsify the corresponding
claim: a second admissible chart not related affinely; a $G_0$ twin class of
size other than two; a $G_1$ supported label permutation changing the inverse
while preserving the complete relation; an indexed-cache pair with different
replay but identical retained law; or two legal serial histories at the same
endpoint. The existing supplier hypotheses, fixed prior, full-injection
support, complete-label acquisition and fixed indexed masks are binding.

The supplied results therefore close the affine-torsor and inversion-label
interfaces on their explicit domains while leaving the long-term problem
open: no geometric analogue here is a hidden origin, an actual source
operation, a new sample, a serial history, or a quantum/random port.

## 追加锚（本行以下为增补区）
