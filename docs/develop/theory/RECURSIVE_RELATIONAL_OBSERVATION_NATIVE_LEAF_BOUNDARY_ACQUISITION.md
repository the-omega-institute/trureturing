# Recursive Relational Observation: Native Leaf Boundary Acquisition

## 1. The common finite tree and its declared service

**Definition 1.1 (native source).** Let $\Gamma=(V,E)$ be a finite
connected simple tree, with unknown order $N=|V|$. Its authentically bound
ordered boundary $B=(\ell_1,\ldots,\ell_b)$ consists of exactly all its
degree-one vertices, where $b\ge3$. Write

$$
J=[e_{\ell_1},\ldots,e_{\ell_b}],\qquad I=N-b.
$$

The fixed native law is a symmetric matrix $T\in\mathbb Q^{V\times V}$.
For distinct vertices, $T_{uv}>0$ exactly when $\{u,v\}\in E$, and
$T_{uv}=0$ otherwise. Diagonal entries are arbitrary rationals. Neither
positive definiteness nor contraction nor simple spectrum is assumed.
The actual state is a field $x\in\mathbb Q^V$, authentically initialized
at zero. Native space means the unit-edge incidence metric, the local
coefficients, and the current field, modulo an isomorphism fixing each
ordered leaf. Manufacturer-private vertex names and a physical embedding
are not included.

**Definition 1.2 (complete menu and installed premises).** Operations are
serial and act on this one actual field:

| Operation | Actual successor | Complete declared reply |
| --- | --- | --- |
| Reset | $0\in\mathbb Q^V$ | fixed acknowledgement |
| Add$(j,u)$, $1\le j\le b$, $u\in\mathbb Q$ | $x+u e_{\ell_j}$ | fixed acknowledgement |
| Tick | $Tx$ | fixed acknowledgement |
| Read$(j)$ | $x$ | literal rational $x_{\ell_j}$ |
| Hold | $x$, with ticks prevented during local processing | fixed acknowledgement |

A requested Tick ends the preceding held interval and performs one
update; there are no other source ticks. Reading every leaf requires
$b$ scalar Read operations. Replies expose no size, work, timing or
other metadata. Fixedness, exact rational normalization and serialization,
the complete roster, leaf binding, full-field reset calibration, the
initial zero field, Hold, exclusive serialization, references, call
rights and their backing are hypotheses of the service. In particular,
Reset acts on every actual cell, including cells not yet identified.
These hypotheses are not conclusions of a numerical transcript and do
not assert a physical installation theorem. There is no coefficient,
internal-index, internal-actuator, eigenvalue or cloning port.

**Definition 1.3 (trials and chronological indices).** A unit-pulse trial
at leaf $j$ means an actual Reset followed by Add$(j,1)$. At its local
epoch $k$, after exactly $k$ further Ticks, the actual state is
$T^k e_{\ell_j}$. All leaf readings at that epoch are made before the
next Tick, under Hold. The trial counter and its tick counter belong to
the observer's retained control, not to a hidden size announcement.
Every local computation below uses only the roster, actual replies,
previously earned records and growing finite counters.

## 2. First arrivals earn the unit metric without order advice

**Lemma 2.1 (exact first arrival).** For any vertices $u,v$, put
$d=d_\Gamma(u,v)$. Then

$$
(T^k)_{uv}=0\quad(0\le k<d),\qquad
(T^d)_{uv}=\prod_{\{a,c\}\in[u,v]}T_{ac}>0.
\tag{2.1}
$$

The empty product for $u=v$ is one.

Proof. The matrix-power expansion is a sum over walks with diagonal
stays allowed. Every nonzero summand changes vertices only along an
edge. Reaching $u$ from $v$ needs at least $d$ such changes. At length
$d$ the unique simple path is the only contributing walk: a stay or
detour would use an additional step. Its edge factors are positive.
Arbitrary signed diagonal entries therefore cannot cancel this first
arrival. This is the elementary travel-time observation used in
inverse problems on graphs; it concerns the literal field response,
not a probability of a random first-passage event. $\square$

**Theorem 2.2 (paid leaf distances).** There is one controller, independent
of $N$ and of the coefficients, which uses exactly $b$ first-arrival
trials and terminates on every source of Definition 1.1. Its result is
the entire ordered leaf distance matrix
$d_{ac}=d_\Gamma(\ell_a,\ell_c)$. If

$$
D_a=\max_{c\ne a}d_{ac},\qquad D=\max_aD_a,
$$

these trials use exactly $\sum_a D_a$ Ticks and
$b\sum_a(D_a+1)$ scalar Reads.

Proof. In trial $a$, read all $b$ leaves at epoch zero and then after
each successive Tick. For each $c\ne a$, retain the first epoch with a
nonzero reply. End the trial once every such $c$ has replied nonzero at
least once. Lemma 2.1 identifies these epochs with $d_{ac}$ and proves
termination at exactly $D_a$. Later cancellations do not change a
retained first epoch. No bound is consulted before stopping. Reset and
Add in each subsequent trial act on the same specimen, so no clone or
parallel response oracle has been used. The stated counts include all
zero replies and the $b$ individual readings at each epoch. $\square$

**Lemma 2.3 (canonical native vertices from the leaf metric).** For each
pair $a<c$ and each integer $0\le r\le d_{ac}$, form the vector
$q(a,c,r)\in\mathbb Z^b$ whose $j$th coordinate is

$$
\begin{aligned}
t_j&=\frac{d_{aj}+d_{ac}-d_{cj}}2,\qquad
h_j=\frac{d_{aj}+d_{cj}-d_{ac}}2,\\
q(a,c,r)_j&=h_j+|r-t_j|.
\end{aligned}
\tag{2.2}
$$

Deduplicate these vectors, and join two distinct retained vectors when
their $\ell^\infty$ distance is one. The resulting graph is the entire
native unit tree, including every degree-two vertex. Its canonical
vertex corresponding to $v$ is

$$
\delta(v)=(d_\Gamma(v,\ell_j))_{j=1}^b,
\qquad
\|\delta(u)-\delta(v)\|_\infty=d_\Gamma(u,v).
\tag{2.3}
$$

Proof. The three paths joining $\ell_a,\ell_c,\ell_j$ have a unique
median vertex. Its position along $[\ell_a,\ell_c]$, measured from
$\ell_a$, is $t_j$, and its distance from $\ell_j$ is $h_j$.
Both are nonnegative integers. The vertex at integer position $r$ on
that path consequently has exactly the distance vector in (2.2).

Every vertex belongs to a path between two leaves. For a nonleaf,
choose two different components after removing it; each contains an
original leaf, by extending a path to its finite end. A leaf belongs
to its path to any other leaf. Thus the candidate set is exactly
$\delta(V)$, without contracting any unit subdivisions.

The triangle inequality gives the upper bound in (2.3). For $u\ne v$,
extend the path from $u$ through $v$ as far as possible beyond $v$.
Its final vertex is a leaf, and its distance difference from $u,v$
is $d_\Gamma(u,v)$. This proves the reverse bound, injectivity, and
the adjacency rule. Each ordered leaf has its own zero coordinate,
so the isomorphism fixes the roster. $\square$

**Corollary 2.4 (unknown native order).** The $b$ trials of Theorem 2.2
effectively determine $N$, $I=N-b$, and the native topology. The finite
candidate list has length at most

$$
Q=\sum_{a<c}(d_{ac}+1)\le {b\choose2}(D+1).
\tag{2.4}
$$

Furthermore $1\le I$ and $D\le I+1$.

Proof. Count the distinct vectors in Lemma 2.3. A tree with at least
three leaves has a nonleaf. A path between two distinct leaves has
only nonleaves as intermediate vertices, so its length is at most
$I+1$. $\square$

**Mathematical citation 2.5 (metric supplier).** Leaf-metric recovery is
classical tree-metric mathematics, not a new rigidity principle here.
Ilmavirta, Lassas, Lu, Oksanen and Ylinen,
[*Quantum computing algorithms for inverse problems on graphs and an
NP-complete inverse problem*, arXiv:2306.05253v2,
Theorem 1 and §5.1](https://arxiv.org/abs/2306.05253v2), prove the
stronger comparison with all connected simple graphs of a fixed
order and explicitly credit the tree-metric theorem for the tree-only
case. Their fixed-order hypothesis is not used as unknown-order advice.
Here the candidates are promised to be trees with unit edges and
exactly this complete leaf set; (2.2) explicitly restores the integer
subdivisions. The source-relative acquisition assertion is the actual
finite first-arrival experiment followed by this supplier, rather than
a claim that the leaf metric itself was previously unknown mathematics.

## 3. Earned moments and native polynomial coordinates

**Definition 3.1 (the second acquisition and its pairings).** After
Corollary 2.4 has earned $I$, put

$$
H=2I+1,\qquad L=b(I+1).
$$

Make a further $b$ unit-pulse trials, in the authentic leaf order,
reading every leaf at every epoch $0\le k\le H$. Trial $c$ gives
column $c$ of

$$
M_k=J^{\mathsf T}T^kJ,\qquad 0\le k\le H.
\tag{3.1}
$$

These are $b^2(H+1)$ actual scalar Reads and $bH$ actual Ticks.
For a vector polynomial $p(z)=\sum_r z^r p_r$, $p_r\in\mathbb Q^b$,
define its realized vector and pairings by

$$
\begin{aligned}
\mathcal E(p)&=\sum_r T^rJp_r,\\
\langle p,q\rangle_M&=\sum_{r,s}p_r^{\mathsf T}M_{r+s}q_s,\\
\langle p,zq\rangle_M&=\sum_{r,s}p_r^{\mathsf T}M_{r+s+1}q_s.
\end{aligned}
\tag{3.2}
$$

Only pairings within the indicated available degrees are used.
Symmetry of the actual $T$ gives

$$
\langle p,q\rangle_M=\mathcal E(p)^{\mathsf T}\mathcal E(q),\qquad
\langle p,zq\rangle_M=\mathcal E(p)^{\mathsf T}T\mathcal E(q).
\tag{3.3}
$$

This is the existing moment-Gram supplier, with boundary input $J$,
output $J^{\mathsf T}$ and the native Euclidean pairing. It uses
self-adjointness, not positivity of $T$. Main §§126.2–126.4 give this
same algebraic identity inside their positive continuous-time model;
their additional positive-generator and exponential hypotheses are
not assigned to the present arbitrary-diagonal law.

**Lemma 3.2 (all leaves force the entire tree).** Start with a set
$S\supseteq B$ of marked vertices. Whenever a marked vertex $v$ has
exactly one unmarked neighbor $w$, mark $w$. Unless $S=V$, such a pair
exists. Therefore selecting the lexicographically first eligible
$(\delta(v),\delta(w))$ marks every vertex in exactly $I$ additions
when initially $S=B$.

Proof. Suppose there is no eligible pair and put $U=V\setminus S$.
If $U\ne\varnothing$, retain the vertices of $U$, all marked vertices
adjacent to $U$, and exactly the edges with at least one endpoint in
$U$. This is a nonempty finite forest. Each unmarked vertex has its
original degree, which is at least two because all original leaves
are marked. Each retained marked vertex has at least two neighbors
in $U$, by the supposed absence of an eligible pair. Thus the forest
has minimum degree at least two, contrary to the existence of an
endpoint in every nonempty finite forest with an edge. There is an
edge because unmarked vertices have degree at least two. Each step
adds one of the $I$ original nonleaves. Lexicographic order of the
already earned integer vectors supplies a finite selector. $\square$

**Theorem 3.3 (finite native law reconstruction, including repeated
spectra).** The observations in Definition 3.1 effectively determine
every native coefficient and polynomials

$$
p_v(z)=\sum_{r=0}^{I}z^r p_{v,r},\qquad
\mathcal E(p_v)=e_v\quad(v\in V).
\tag{3.4}
$$

Thus $p_v(T)J=e_v$, when that notation denotes the vector-polynomial
action $\mathcal E$. Moments through precisely the allowed horizon
$H=2I+1$ suffice; no eigenvalue queries, spectral separation or simple
spectrum are required.

Proof. Initially $S=B$ and $p_{\ell_j}$ is the constant $j$th unit
vector of $\mathbb Q^b$. After $s$ additions maintain
$\mathcal E(p_u)=e_u$ and $\deg p_u\le s$ for every $u\in S$.
Take the pair $v,w$ selected by Lemma 3.2. Compute

$$
a=\langle p_v,zp_v\rangle_M,
\qquad c_u=\langle p_u,zp_v\rangle_M\quad
(u\in S,\ \{u,v\}\in E),
\tag{3.5}
$$

and the residual polynomial

$$
r=zp_v-a p_v-
\sum_{\substack{u\in S\\\{u,v\}\in E}}c_u p_u.
\tag{3.6}
$$

By (3.3), the computed $a,c_u$ are the actual $T_{vv},T_{uv}$.
The known topology and unique unmarked neighbor give the exact
native residual, without an internal observation:

$$
\mathcal E(r)=T e_v-T_{vv}e_v-
\sum_{\substack{u\in S\\\{u,v\}\in E}}T_{uv}e_u
=T_{wv}e_w.
\tag{3.7}
$$

Consequently $\langle r,r\rangle_M=T_{wv}^2>0$. Take its positive
rational square root $c$ and set $p_w=r/c$. The promise $T_{wv}>0$
proves $c=T_{wv}$ and gives the required orientation, not merely a
vector determined up to sign. Rational extraction is effective:
in the reduced positive fraction representing this square, numerator
and denominator are integer squares; integer square-root search and
exact squaring recover their positive roots.

At this step $s\le I-1$. Formula (3.5) uses moment degrees at most
$2s+1$, and (3.6) has degree at most $s+1$, so its squared norm uses
degrees at most $2s+2\le2I$. The new polynomial has degree at most
$s+1$. Induction and Lemma 3.2 produce (3.4) after exactly $I$ steps.
Finally compute, for every pair of native vertices,

$$
T_{uv}=\langle p_u,zp_v\rangle_M.
\tag{3.8}
$$

Its maximum required degree is $2I+1$. It recovers the diagonals as
well as all links; nonedges have the promised zero entries. The
procedure uses finite rational arithmetic and rational-square
extractions, with graph selection based only on distance vectors.
Every residual and coordinate identity holds in the same original
$\mathbb Q^V$. In particular it proves full boundary reachability
without decomposing any eigenspace. $\square$

**Mathematical citation 3.4 (infection supplier and exact correspondence).**
The one-neighbor residual in (3.7) is the mature infection method of
Burgarth and Maruyama,
[*Indirect Hamiltonian Identification through a small gateway*,
arXiv:0903.0612v1, §II, Lemma and equations (1)–(3)](https://arxiv.org/abs/0903.0612v1),
New Journal of Physics 11, 103019, DOI
[10.1088/1367-2630/11/10/103019](https://doi.org/10.1088/1367-2630/11/10/103019).
Their known topology, gateway $C$, single-excitation matrix and
unique healthy neighbor correspond to the earned topology, marked
$S$, native $T$ and $w$ here. Normalization of the residual determines
the coupling magnitude; its prescribed sign determines orientation.
Their spectral data and quantum tomography are not present ports
here, and their additional degeneracy-lifting field is not used.
Equations (3.2)–(3.8) realize that algebraic supplier directly with
earned finite moment pairings and establish the degree bound $I$.
The claim is this chronological finite realization of the supplier,
not a new general infection theorem.

**Corollary 3.5 (complete law and unique native answer).** The acquired
data determine $J^{\mathsf T}T^kJ$ for every $k\ge0$, and the finite
rational matrix function

$$
F(z)=J^{\mathsf T}(z\mathbf1-T)^{-1}J
=\sum_{k\ge0}M_k z^{-k-1}
\tag{3.9}
$$

at infinity. Two promised sources with the same acquired records are
isomorphic by the unique distance-vector identification of vertices,
and that identification preserves every coefficient.

Proof. Lemma 2.3 identifies their graphs and orders. The deterministic
construction of Theorem 3.3 uses identical inputs in that graph and
produces identical $p_v,T_{uv}$. Finite matrix arithmetic then computes
every power or the adjugate/determinant expression in (3.9). The series
identity is the formal geometric-series identity; it supplies local
predictions, not additional paid observations at arbitrary indices.
$\square$

## 4. A predictor installed at the actual last-trial cut

**Definition 4.1 (retained predictive configuration).** After the last
trial of Definition 3.1 the actual source is held at

$$
x_*=T^H e_{\ell_b}.
\tag{4.1}
$$

Retain the earned topology, coefficients, moment data and polynomials,
the same authentic source reference, all declared rights and backing,
and a locally calculated native field $\widehat x=x_*$. Retain also,
if using a predictive-block representation,

$$
\mathcal O x=(J^{\mathsf T}T^r x)_{r=0}^{I},\qquad
w=\mathcal O\widehat x\in\mathbb Q^L.
\tag{4.2}
$$

Local calculation of (4.1) and (4.2) takes no source Tick. Calls and
record updates are serialized; the next completed cut is exposed
only after the matching observer update. Hypothetical calculations
on scratch records do not send a command to the source.

**Lemma 4.2 (finite predictive coordinates).** Define the linear map
$D_p:\mathbb Q^L\to\mathbb Q^V$ by

$$
(D_p y)_v=\sum_{r=0}^{I}p_{v,r}^{\mathsf T}y_r.
\tag{4.3}
$$

Then $D_p\mathcal O=\mathbf1$. Hence $\mathcal O$ is injective.
The predictive block has the following exact updates on its actual
image:

$$
\begin{array}{c|c}
\text{command}&\text{new block}\\ \hline
\mathrm{Reset}&0\\
\mathrm{Add}(j,u)&(w_r+uM_r e_j)_{r=0}^{I}\\
\mathrm{Tick}&\mathcal O T D_p w\\
\mathrm{Read}(j),\ \mathrm{Hold}&w.
\end{array}
\tag{4.4}
$$

Read$(j)$ returns coordinate $j$ of $w_0$; every other reply is the
declared acknowledgement. The finite matrix $\mathcal O T D_p$ is
computed from the earned law. It requires no extra source sample.

Proof. By symmetry of $T$ and (3.4), for every actual $x$,

$$
\sum_r p_{v,r}^{\mathsf T}J^{\mathsf T}T^r x
=\mathcal E(p_v)^{\mathsf T}x=e_v^{\mathsf T}x.
\tag{4.5}
$$

This proves the left-inverse identity, on all rational fields, without
any positivity or inverse for $T$. The Add formula follows by
applying $\mathcal O$ to $x+u e_{\ell_j}$; the Tick formula follows
by substituting $x=D_p w$. Reset, Read and Hold have their stated
successors. For $r<I$ the Tick block merely shifts $w_r$ to
$w_{r+1}$; its final block is obtained from the earned native law,
so an unobserved $M_{H+1}$ is not being requested. $\square$

**Theorem 4.3 (all finite common adaptive continuations).** At the
endpoint (4.1), the actual source and the installed predictor have
corresponding fields. For every finite common adaptive continuation
in the complete menu of Definition 1.2, their complete replies are
identical and their successors correspond at every completed cut.
The policy may choose its next command, rational input or stopping
decision from previous replies and retained common information; a
common random tape is allowed. The invariant is

$$
\widehat x=x_{\mathrm{actual}},\qquad
w=\mathcal O x_{\mathrm{actual}}.
\tag{4.6}
$$

Proof. Each earlier trial was terminated by a real Reset, including
the final one, so the last trial contains exactly its own one pulse
and $H$ Ticks. Thus (4.1) is the actual endpoint, even though the
first-stage trial lengths differed. Hold preserves it throughout
decoding and installation. This establishes (4.6).

Update the native record by zeroing it for Reset, adding
$u e_{\ell_j}$ for Add, multiplying it by the earned actual $T$ for
Tick, and leaving it fixed for Read or Hold. These are exactly the
native successors, and Lemma 4.2 gives the matching predictive
updates and literal Read values. The fixed acknowledgements also
match. Induct on the continuation length. Identical preceding
replies make a common adaptive policy select the same next command
and input; the one-operation identities preserve (4.6). Fixing a
common random tape gives the same induction for each realized finite
continuation. This is the finite-word transport already supplied in
P, Theorem 40.2, with its initialization replaced by the actually
proved last-trial identity (4.1). It grants no rights beyond the
installed menu. $\square$

## 5. Passive recovery of an arbitrary actual current field

**Theorem 5.1 (one-specimen current recovery at the advanced cut).**
After the law has been earned, let the actual current field be any
$x\in\mathbb Q^V$. On that specimen, make no Reset or Add during the
window. Read all leaves initially and after each of $I$ actual Ticks,
retaining

$$
y_r=J^{\mathsf T}T^r x,\qquad 0\le r\le I.
\tag{5.1}
$$

The $b(I+1)$ scalar Reads recover the exact starting field
$x=D_p y$. The same source is then at $x_{\mathrm{end}}=T^I x$.
Holding it there while installing
$\widehat x=T^I D_p y$ and $w=\mathcal O\widehat x$ gives a
synchronized predictor at this actual advanced cut. All finite
common adaptive continuations again satisfy Theorem 4.3.

Proof. The recorded window is $\mathcal O x$ because Read is
nondestructive and no intervening changes other than the $I$ requested
Ticks occur. Equation (4.5) therefore gives $D_p y=x$, for every
rational starting field. Compute $T^I x$ locally and use the
actual tick count to initialize the predictor at the endpoint.
Equation (4.6) is now true there, so the same one-operation proof
applies. No inverse $T^{-1}$ is used: reconstruction concerns the
start of the retained window, whereas synchronized use concerns its
end. $\square$

**Corollary 5.2 (faithfulness for the declared continuation task).**
Within the promised class, two configurations with arbitrary rational
current fields have identical complete replies for every common finite
continuation if and only if a leaf-fixing native isomorphism preserves
their laws and current fields.

Proof. A native isomorphism intertwines each of the five operations,
so gives identical replies by finite induction. Conversely, equality
of all continuation replies includes the law-acquisition experiment
after Reset. Its stopping decisions agree, and Corollary 3.5 gives
the common native law and graph. Equality of replies also includes
the passive initial window of length $I$ from the two original
current fields. With that common law, (4.5) makes those fields equal
under the native identification. This is a comparison of two complete
services; it does not claim to perform both the initial passive
window and a destructive Reset at the same original cut. $\square$

## 6. Independent expressions and their exact recovery domain

**Definition 6.1 (four expressions on this source).** The following
data have meanings before any inverse is applied.

| Expression | Independently exposed data |
| --- | --- |
| Space | The unit native tree, its local $T_{uv}$ and the present field $x$, up to leaf-fixing isomorphism |
| Time | Trial-indexed, tick-indexed chronological scalar leaf readings actually acquired, together with the actual pulse/reset labels and tick counters |
| Boundary | The leaf input/output law $F$ of (3.9), the present restriction $J^{\mathsf T}x$, and the declared leaf menu; installation is separate |
| Memory | A retained native law and the finite predictive block $(J^{\mathsf T}T^r x)_{r=0}^{I}$, meaning the next $I$ autonomous leaf predictions from the present field |

Memory is a finite prediction window, not an unrestricted copy of the
control journal. Time counts actual source Ticks and ordered samples,
not wall time or local instructions. Boundary's present restriction
is an instantaneous reading, not a full-field register. The unit
metric in Space is incidence geometry, not response-energy geometry.

**Proposition 6.2 (proved routes and phase boundaries).** On the actual
acquisition image, the first-stage Time data recover the native
topology and the second-stage Time data recover the law and the
last-trial Space and Memory configurations. Their recovered law gives
Boundary's $F$. With the law retained, a passive window gives the
starting Space field and the advanced synchronized Memory of
Theorem 5.1. The native and predictive update routes commute with
every declared operation. All such routes agree under (4.5).

Neither Boundary's instantaneous field nor a present Space or Memory
configuration is claimed to recover an arbitrary past journal, an
unrecorded epoch or a physical duration.

Proof. The first assertions are Theorems 2.2, 3.3, 4.3 and 5.1,
whose native identifications all use the same injective $\delta$.
The update commutation is (4.4) and (4.6), and the common left inverse
is (4.5). The listed restrictions have exact witnesses. An internal
unit field $e_v$ and zero have the same instantaneous leaf restriction
when $v$ is a nonleaf. Equation (4.5) ensures that some reading in
the passive window distinguishes them; no instantaneous inverse
follows. A Reset erases every preceding field and pulse history.
Any number of Ticks at zero also gives zero, and inserted Holds or
Reads change a journal without changing the field. Their fixed
acknowledgements carry no duration information. Thus the acquisition
phase and the passive-window advancement are supplied by actual
retained chronology, not inferred from a generally injective clock
mark in the field. $\square$

## 7. One attained simultaneous resource account

**Definition 7.1 (encoding and charges).** Let $\mathcal B$ be the
total bit length of the $N$ diagonal and $N-1$ undirected link
coefficients, each encoded by a reduced signed numerator and a
positive binary denominator, with framing. Set

$$
\begin{aligned}
K&=\sum_aD_a+bH,\\
R&=b\bigl(K+2b\bigr),\\
W&=C\,N\bigl(\mathcal B+\log_2(N+1)+1\bigr),
\end{aligned}
\tag{7.1}
$$

where an absolute sufficiently large $C$ is used in the width bounds
below. $\mathcal B,N,W$ are analysis parameters, not advance advice
to the controller. Charge exact arithmetic, integer comparisons,
allocation, framing and serialization at the widths actually used.
A rational-square extraction is charged separately from rational
field operations. Let $A(W)$ bound field arithmetic, gcd/lcm and
integer arithmetic at $O(W)$ bits, and let $S(W)$ bound exact
integer-square-root extraction there. Elementary long arithmetic
and binary-search roots give conservative polynomial bounds
$A(W),S(W)=O(W^3)$; no real-number oracle is being priced at unit cost.

**Proposition 7.2 (actual calls and source work).** The complete
acquisition uses exactly

$$
\begin{array}{c|c}
\text{operation}&\text{number}\\ \hline
\mathrm{Reset}&2b\\
\mathrm{Add}(j,1)&2b\\
\mathrm{Tick}&K\\
\mathrm{Read}(j)&R\\
\mathrm{Hold}&K+2b.
\end{array}
\tag{7.2}
$$

Here one Hold is issued at each sampled epoch, including epoch zero
of every trial. The last held interval includes decoding and
installation. There are $2K+6b$ fixed acknowledgements in addition
to the $R$ rational replies. The source has $N$ cells, $N-1$ links
and $2N-1$ rational coefficient words. A direct two-buffer tree Tick
uses $3N-2$ scalar multiplications and $2N-2$ scalar additions.
Thus acquisition attains $K(3N-2)$ source multiplications and
$K(2N-2)+2b$ additions, in addition to $2bN$ Reset cell writes,
buffer movement and reading/serialization work.

Proof. Each of the $2b$ trials has one Reset, one Add, an epoch-zero
sample, and one more sample after each Tick. Their total number of
sampled epochs is $K+2b$, and every sample has $b$ Reads. This also
counts the Holds. Reset, Add, Tick and Hold each acknowledge once,
so their total is $2b+2b+K+(K+2b)$. A matrix with this tree sparsity
has $N+2(N-1)=3N-2$ diagonal/directed-edge products in a direct
matrix-vector multiplication. Accumulating each row from its first
term takes $(3N-2)-N=2N-2$ additions. This implementation retains
zero diagonal terms if present, so the count is attained regardless
of their values. Two buffers prevent overwritten inputs. Each Add
uses one scalar addition, and every Reset writes every actual cell.
The source work is not a claim that its acknowledgements reveal
that work. $\square$

**Proposition 7.3 (finite width and local decoding).** There is an
exact implementation of the stated acquisition, topology decoding,
polynomial reconstruction and installation whose numerical
intermediates have $O(W)$ bits. It uses at most

$$
O\bigl(bQ^2+bN^2+N^2L^2+NH\bigr)
\tag{7.3}
$$

elementary integer or rational arithmetic operations, plus $I$
positive rational-square extractions. An attained bit upper bound
for this local work is the expression (7.3) multiplied by $A(W)$,
plus $O(I S(W))$ and actual allocation, framing and output traffic.
It is not an optimality assertion.

Proof. Let $D_0$ be the product of denominators of the native
coefficients and write $T=A_0/D_0$ with $A_0$ integral. Then
$D_0\le2^{\mathcal B}$, $|T_{uv}|\le2^{\mathcal B}$, and
$|(A_0)_{uv}|\le2^{2\mathcal B}$. After $k$ Ticks in a unit trial,
the field denominator divides $D_0^k$, and

$$
\|T^k e_{\ell_a}\|_\infty
\le (N2^{\mathcal B})^k.
\tag{7.4}
$$

Thus every source state, reply and moment used here has width
$O(H(\mathcal B+\log(N+1))+1)$: first-stage depths are at most
$D\le I+1\le H$. The lcm $D_M$ of the acquired moment denominators
divides $D_0^H$. Every scaled moment $D_M M_k$ has the same order
of bit width. The observer computes this lcm from earned fractions;
$D_0$ is only a proof bound.

For polynomial widths, use a common denominator for the whole
currently marked family. A useful bound, again not an input, is
obtained from the actual forcing edges. After $s$ additions take

$$
Q_s^*=\prod_{\text{first }s\text{ forcing edges }(v,w)}(A_0)_{vw}.
\tag{7.5}
$$

All these factors are positive integers. The common-denominator
numerators for the marked polynomials can be bounded in magnitude
by

$$
\bigl((N+1)2^{2\mathcal B}\bigr)^s.
\tag{7.6}
$$

Indeed the forcing identity, written with actual integral
coefficients, is

$$
p_w=
\frac{D_0zp_v-(A_0)_{vv}p_v-
\sum_{u\in S,\,u\sim v}(A_0)_{uv}p_u}
{(A_0)_{wv}}.
\tag{7.7}
$$

On passing to denominator $Q_{s+1}^*$, each old numerator is
multiplied by $(A_0)_{wv}$; the new numerator is the sum in (7.7)
at denominator $Q_s^*$. There are at most $N+1$ terms and each
integral multiplier is at most $2^{2\mathcal B}$. This proves
(7.6) inductively from the constant leaf polynomials. Hence both
denominators and numerators have
$O(I(\mathcal B+\log(N+1))+1)$ bits. Using the lcm of the reduced
polynomial denominators gives no larger denominator: it divides
$Q_s^*$. Rescaling to it also gives no larger numerators.

Use these common denominators for the pairings (3.5), (3.8) and
the norm of (3.6). Each pairing is a sum of at most $L^2$ integral
products over the common denominator formed from $D_M$ and the
two polynomial denominators. The residual adds at most one extra
factor $D_0$ in its denominator before normalization. Equations
(7.4)–(7.7), and the extra $O(\log(L+1))$ bits for summation, put
all products, partial sums, reduced pairings and root inputs within
$O(W)$ bits. The root of the reduced promised rational square
has no greater bit width. Reducing fractions, taking lcms and
rescaling after each addition therefore realizes this bound,
without knowing its numerical value in advance. No linear solve
with unboundedly chosen precision is hidden here.

For counts, generate the $Q$ candidate vectors using (2.2) and
deduplicate by pairwise comparison, at most $O(bQ^2)$ integer
operations; compare the retained vectors for adjacency in
$O(bN^2)$. Store the two $L$-square moment pairing matrices,
with entries $M_{r+s}$ and $M_{r+s+1}$. Each bilinear evaluation
takes $O(L^2)$ operations. There are at most $IN$ evaluations
during forcing and $N^2$ in the final coefficient table. Polynomial
updates and common-denominator maintenance fit within
$O(N^2L^2)$ further operations. There are exactly $I$ norm-root
normalizations. Computing $T^H e_{\ell_b}$ and its predictive block
by sparse successive multiplication takes $O(N(H+I))$ operations,
which fits (7.3). A precomputed predictive update matrix
$\mathcal O T D_p$ also fits $O(N^2L^2)$ operations and $O(W)$
width by the same finite matrix-power and common-denominator
bounds. These operations all occur while the actual source is held.
$\square$

**Definition 7.4 (coexisting stores and traffic).** One attained layout
retains all of the following simultaneously at installation. It
keeps the raw readings and the moment table as separate copies.

| Actual store or resource | Attained bound or separate charge |
| --- | --- |
| Source coefficients and native structure | $\mathcal B$ bits, $N$ cells and $N-1$ links |
| Two source field buffers | $O(NW)$ bits |
| All raw scalar acquisition readings | $O(RW)$ bits, plus trial/tick framing |
| Separate moment table | $O(b^2(H+1)W)$ bits |
| Metric, candidate vectors and recovered vector names | $O((b^2+bQ+bN)\log(N+1))$ bits |
| Moment-pairing, polynomial and decoder scratch; optional predictive matrix | $O((L^2+NL+N^2)W)$ bits |
| Retained law, native predictor and predictive block | $O(\mathcal B+(N+L)W)$ bits |
| Program, parser, indices, trial and tick counters | actual allocated bits; indices and acquisition counters use $O(\log(N+1))$ bits each |
| Authentic roster, reference, full-field reset and Hold installation, permissions, assurance and backing | their actual simultaneous representations and resources |
| Input/output buffers and separately retained copies | their actual simultaneous encoded lengths |

Trial/tick framing for the retained acquisition record fits
$O((R+K+b)\log(N+1))$ additional bits. It can instead share
structured indices when that is the actual representation. These
rows are added, not minimized over incompatible implementations.
A shared backing is counted once only when it really is shared.
Literal scalar traffic is the sum of the actual $R$ rational word
lengths; it is at most $O(RW)$ here. Add inputs, leaf indices,
operation labels and all $2K+6b$ acknowledgements are charged in
addition. The mathematical service specifies no universal numerical
price for physical calibration, source assurance or authorization.

**Proposition 7.5 (continued use and growing exact widths).** Every
finite continuation admitted by Theorem 4.3 has an attained finite
resource account, with source, observer and rights coexisting.
One may update the native predictor by the sparse native rule and
the redundant predictive block by its retained $L$-square matrix.
A predictor Tick then uses $O(N+L^2)$ field operations; Add uses
$O(L+1)$, Reset writes $N+L$ coordinates, and Read serializes its
actual scalar. Source work is added to predictor work.

If the continuation has $f$ commands, $t$ Ticks, and total supplied
rational input length $U$, current source and predictor numerical
widths are bounded by

$$
O\bigl((H+t+I+1)(\mathcal B+\log(N+1))+U+\log(f+1)+1\bigr).
\tag{7.8}
$$

Every arithmetic operation, input and reply pays that growing
width. A retained continuation journal and its indices are additional
storage. Fixed native order does not give bounded exact memory or
bounded scalar traffic over all continuations.

Proof. Between Resets, the actual field is a sum of the propagated
starting field and the propagated supplied leaf inputs. A common
denominator divides the starting denominator times $D_0^t$ times
the product of supplied input denominators. The infinity-norm bound
in (7.4), the sum of at most $f+1$ terms and the total input length
$U$ give the numerator and denominator bound in (7.8). Reset can
only remove preceding terms. Applying the finite polynomial and
power matrices for the predictive record adds at most
$O((I+1)(\mathcal B+\log(N+1)))$ bits, by Proposition 7.3.
The operation counts follow from the chosen simultaneous
implementation and (4.4).

For unboundedness within this very class, take a three-leaf star
with $T=\tfrac12\mathbf1+\tfrac1{16}A_\Gamma$.
After law acquisition use legal Reset, Add$(1,1)$ and Add$(2,-1)$.
The resulting $e_{\ell_1}-e_{\ell_2}$ is an eigenvector with
eigenvalue $1/2$, since its two contributions at the center cancel.
After $k$ further Ticks, Read$(1)$ returns $2^{-k}$. Its reduced
denominator has $k+1$ binary digits. Retaining all such replies
through $k$ uses $\Theta(k^2)$ bits in this encoding. The matrix
even satisfies $0<T<\mathbf1$, since its other two nonconstant
eigenvalues are $1/2\pm\sqrt3/16$. Thus the width growth is not
caused by instability. $\square$

**Corollary 7.6 (cost of passive current recovery).** Theorem 5.1
adds exactly $I$ source Ticks, $b(I+1)$ scalar Reads and, with one
Hold per sampled epoch, $I+1$ Holds. Its source arithmetic is
$I(3N-2)$ multiplications and $I(2N-2)$ additions. Computing
$D_p y$ takes $O(NL)$ field operations, and advancing its recovered
field and computing the synchronized predictive block takes
$O(NI)$ further operations. If the starting field has total encoded
length $X$, all its numerical stores and these intermediates have
width $O(X+N(\mathcal B+\log(N+1))+1)$. Its retained window,
scratch and predictor coexist with the previously retained law and
service installation.

Proof. Count the actual calls in (5.1), and use the direct native
Tick count. Formula (4.3) has $NL$ scalar terms. Two sets of at
most $I$ sparse matrix-vector steps advance the field and compute
its predictions. A common initial denominator is bounded by the
product of starting-field denominators; apply (7.4) and the
polynomial denominator bounds to obtain the displayed width.
These are added costs on that one specimen, not a fresh
initialization or a replacement optimal observer. $\square$

## 8. Incomplete leaves and other exact failure boundaries

**Theorem 8.1 (different stable positive native orders with identical
complete visible-leaf service).** For every $b\ge3$ there are two
finite connected positive-link rational trees of orders $b+2$ and
$b+3$, both with $0<T<\mathbf1$, whose same ordered list of $b$
visible actual leaves has identical complete service in Definition
1.2 from authentic zero. In both trees that list omits actual leaves.
Equality includes all finite common adaptive continuations, full-field
Reset, arbitrary rational visible Add operations and literal Reads.

Proof. Put $a=1/(8(b+1))$. The first tree is a star with center $c$,
visible leaves $\ell_1,\ldots,\ell_b$ and one unlisted leaf $h$.
Give each edge weight $a$ and every diagonal value $1/2$.
In the second star replace $h$ by two unlisted leaves $h_1,h_2$,
with edge weights $3a/5,4a/5$, and leave all other coefficients
unchanged. Call the matrices $T,T'$.

Let $U:\mathbb Q^{b+2}\to\mathbb Q^{b+3}$ fix the center and all
visible leaves and send

$$
Ue_h=\tfrac35 e_{h_1}+\tfrac45 e_{h_2}.
\tag{8.1}
$$

It is an isometry and direct multiplication gives

$$
T'U=UT,\qquad J'=UJ,\qquad J'^{\mathsf T}U=J^{\mathsf T}.
\tag{8.2}
$$

For example, the return contribution at the center is
$(3a/5)(3/5)+(4a/5)(4/5)=a$; the outward contribution is
$aUe_h$. The orthogonal hidden vector
$-\tfrac45e_{h_1}+\tfrac35e_{h_2}$ has eigenvalue $1/2$.
The nonzero eigenvalues of either weighted adjacency matrix are
$\pm a\sqrt{b+1}$: a weighted star acts on its center and
normalized edge-weight vector by the matrix with off-diagonal
entry equal to the Euclidean norm of its edge weights. All other
adjacency eigenvalues are zero. Since
$a\sqrt{b+1}<1/2$, both $T$ and $T'$ are positive definite strict
contractions.

Initialize both actual fields at zero and maintain $x'=Ux$.
Reset sends both to zero, Add respects $J'=UJ$, Tick respects the
intertwiner, and Read respects the last identity in (8.2). Hold and
all fixed acknowledgements match. Finite induction, including
adaptive choices, proves identical complete service. The actual
orders differ, so no native isomorphism exists. Both visible
rosters consist of true leaves; their missing leaves are the exact
failed hypothesis. The comparison does not use a timing or
resource side channel, which the declared service excludes.
$\square$

**Corollary 8.2 (sufficiency, not necessity).** Authentic complete-leaf
coverage is sufficient for the uniform inverse in §§2–5. Removing
that premise from the class admits the stable positive countermodels
of Theorem 8.1, so no inverse uniformly recovers actual $N$ on the
enlarged class from complete visible-leaf service. This does not
assert that every particular incomplete interface fails.

Proof. Sufficiency was proved constructively. The two services in
Theorem 8.1 cannot yield different correct orders to any rule
depending only on their identical observations and common inputs.
Conversely, P's rooted-path theorem supplies a different class
where one accessible endpoint is sufficient, despite omitting the
other leaf when $N>1$. Its positive Jacobi-path and authentic
preparation hypotheses are additional restrictions, not a theorem
about all incomplete tree interfaces. $\square$

**Proposition 8.3 (normalization, precision and calibration boundaries).**
The inverse proved here supplies neither unrestricted link-sign
recovery, a class-wide finite-precision margin, nor certification of
the installed source and call premises.

Proof. A diagonal sign matrix $S$ fixing every leaf satisfies
$S J=J$. The law $STS$, with field correspondence $x\mapsto Sx$,
preserves Reset, visible Add, Tick, Read and Hold. Flipping a
nonleaf sign changes incident link signs while preserving complete
service. Positivity of the links fixes the sign choice used in
(3.7), so unrestricted signs would change the inverse task.

For lack of a uniform precision margin, use stars with fixed
diagonal $1/2$ and positive edge weight $\varepsilon\in\mathbb Q$.
Their first cross-leaf arrival is $\varepsilon^2$, which tends to
zero with $\varepsilon$. Thus the exact zero/nonzero decision
of Lemma 2.1 has no class-wide positive error margin. An exact
digital zero test is not a noisy physical threshold theorem.

Finally, the numerical proofs take fixedness, the roster, binding,
exact scaling, Reset, Hold and rights as inputs. The inverse makes
no inference establishing those hypotheses. Theorem 8.1 already
supplies a concrete false
complete-roster interpretation with identical full visible service.
A numerical record also lacks a callable reference or permission
unless it is actually retained. These facts are not installed by
arithmetic inversion. $\square$

## 9. Suppliers, conditional correspondence and retained scope

**Mathematical citation 9.1 (inverse-graph correspondence).** Blåsten,
Isozaki, Lassas and Lu,
[*Inverse problems for discrete heat equations and random walks for
a class of graphs*, arXiv:2107.00494v2](https://arxiv.org/abs/2107.00494v2),
Definition 1.2, Theorems 1.3, 1.7 and 1.8, supply geometric inverse
and unique-continuation/observability results. Their graph vertex
measure can be set to $\mu_v=1$, edge weights to $g_{uv}=T_{uv}$,
and potential to

$$
q_v=1-T_{vv}-\sum_{u\sim v}T_{uv}.
\tag{9.1}
$$

Then their discrete heat step $\mathbf1+\Delta-q$ is exactly this
$T$, and their Schrödinger operator $-\Delta+q$ is $\mathbf1-T$.
There is no row-stochastic assumption on the present law. Their
random-walk Theorems 1.5–1.6 therefore are not invoked as an exact
finite-sampling theorem for it. Their Theorem 1.8 uses full
source-to-solution data and known boundary measure; it does not
give these paid finite trials as a port.

Their Two-Points Condition holds for the present complete leaf set.
For any subset with at least two vertices, its minimal spanning
subtree has at least two endpoints, each belonging to the subset.
From either endpoint, a path leaving that subtree extends to an
original leaf; if the endpoint is already an original leaf, use
that leaf itself. All paths from this leaf to the other subset
vertices pass through the chosen endpoint. That endpoint is
therefore the unique nearest subset vertex. The two endpoints
give the required two extreme points. Hence the constant-measure
clause of their Theorem 1.3 applies with $\mu=1$, once its full
interior spectral data have been supplied.

For the hypothesis in their observability Theorem 1.7, an
eigenvector vanishing at all leaves vanishes successively along
the forcing sequence: at a marked zero vertex with one unmarked
neighbor, its eigen-equation forces that neighbor to zero because
the link is nonzero. Lemma 3.2 then makes the eigenvector zero.
This verifies the no-invisible-eigenfunction condition, even at
repeated eigenvalues. The finite window and polynomial inverse
proved in §§3–5 are the explicit realization used here; neither
spectral data nor the entire source-to-solution map is assumed
acquired first. This credits the mature inverse-graph conclusion
while locating the finite chronological acquisition and native
coordinate correspondence.

**Mathematical citation 9.2 (repository and pinned algebraic suppliers).**
Repository source references in this item mean the public snapshot
`31f5535ef5004881de99c70024fd85678d99baa5`.
[Main §§125–126](RECURSIVE_RELATIONAL_OBSERVATION.md) supply
target-observability factorization, finite realization algebra,
the moment-Gram pairing and its effective-space boundary. [P,
§§36–43](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md)
supplies unknown positive-contraction Jacobi-path acquisition,
native path coordinates, a sharp path tick horizon, its restricted
passive phase and retained common adaptive use. The present source
has branching, arbitrary rational diagonal, an authentic zero
start, all-leaf Reset/Add/Read trials and an earned topology. Its
phase is the retained trial chronology; P's strictly decreasing
positive-contraction phase mark is not assumed.

[NCR, §§1–2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md)
and its supplier
`D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer`
already acquire an unknown finite ordered $\alpha/\beta$ tree by
literal address readings. That producer's private traversal and
stationarity lemmas preserve the source and give one reading per
actual node. Neither a literal internal address nor an ordered
binary constructor is a port of Definition 1.2. NCR's clocked
continuation fixes its supplied $H,J$, substitution and controller;
those restrictions are not transferred to the present weighted
branching law.

[PVC, Assumption 1.2 and Definitions 1.3–1.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md)
starts with one acquired fixed-$H$ ordered-tree entrance, the
unused-verifier-lane premise and a once-installed authorized
converter. Its four arrows concern sealed historical observations,
with actual copies, calls and completed return.
[The callable Atlas, §§1–2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md)
likewise retains its particular source interval, canonical
installation, permissions, acquisition fence and all intermediate
historical cuts. [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface)
uses the original fixed-capacity ordered-tree service, Clifford
readout, substitution and guarded grafts. These are substantive
acquisition and callable-memory suppliers in their own domains;
none identifies a literal ordered-tree reading with the scalar
$J^{\mathsf T}T^kJ$ observations used here. Their historical
conversion theorems are not claimed anew for the present
instantaneous Boundary view. [PG, §§1–3](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
supplies the actual-joint-image and complete legality/output/successor
discipline: here it is instantiated by the one actual field, its
serial calls, retained rights and invariant (4.6), rather than by
independently chosen view realizations.

The public/private declarations and owning Blueprint Scribes of
`D5/S3/Observer/Hankel/FiniteHoKalmanBlocks`,
`HankelRankMinimality`, `SequenceHankelRealization`, and
`D5/S3/Observer/Linear/GramianBehaviorQuotientMetric` supply the
corresponding finite-factor, full-tail, rank and behavior-quotient
algebra. In `FiniteHoKalmanBlocks`, use field $\mathbb Q$, state
order $N$, input and output sizes $b$, and sample semantics
$M_k=J^{\mathsf T}T^kJ$. Its nonsingular-minor theorem gives
all-time recovery only against a supplied matching reference
order; its arbitrary-order conclusion is a lower bound. Here
the missing upper-order/native correspondence is earned by
Theorem 2.2 and Lemma 2.3. The full-tail construction takes the
entire sequence as data, not as a finite acquired oracle. The
discounted Gramian theorem requires a chosen
$\beta\in(0,1)$ with $\sqrt\beta\|T\|<1$; that extra discounted
norm condition is unnecessary for, and not inferred by, the
finite identity (4.5). Its private energy lemmas retain those
same summability conditions.

`D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness`
and its owning Scribe supply orthogonal equivalence of two
finite-dimensional real symmetric reachable realizations with
equal moments at every nonnegative degree. The correspondence is
$U=\mathbb R^b$, $E=\mathbb R^V$, $A=T$, $B=J$, with the
Euclidean inner products. Theorem 3.3 supplies its reachability
premise here; the private combination-Gram and combination-kernel
lemmas use the same full moment equality. Orthogonal equivalence
alone does not identify native incidence vertices. The additional
finite native identification is (2.2) and the positive-edge
normalization (3.7), with the earned horizon $2I+1$.

The pinned mathlib version is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Its `Combinatorics/SimpleGraph/Acyclic` contains unique-path and
tree-edge-count results, and `LinearAlgebra/Matrix/PosDef`
contains the ordinary Gram positivity identities. They supply
the standard finite graph and pairing algebra, not an already
installed unknown-tree service. The new synthesis uses those
standard identities at their exact hypotheses.

**Mathematical citation 9.3 (other published domains).**
[Compatible Predictive Waves and Relational Spectra,
§§2, 4, 7, 11–12](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)
uses complex coherent kernels, phase references, complete
instruments, isometries and explicit enlarged resource families.
Its Gram quotient and continuation-preservation principles are
mature suppliers. The present rational tree service exposes
literal scalar fields and linear additive leaf inputs, without
those coherent operations; no quantum phase port or physical
wave geometry is inferred from (3.3).

[STR, Theorem 24.1](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md)
is the fixed calibrated rectangular CPTP-map estimate using
the actual first-label-erased depth-two effects, with full
complex amplified diamond norm and unrestricted output.
Those qutrit/five-mode inputs and effects have no identified
transport to a native tree cell or Reset operation here.
[REPAIR, §9](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_CALIBRATION_OWN_LAW_REPAIR.md)
keeps its two acquired marginal flows and proves upper-tail
concentration with auxiliary finite measures on that complete
descriptor space. It does not turn an incomplete native leaf
list into a complete one. None of their published conclusions
is replaced or claimed unresolved by the present construction.

**Theorem 9.4 (source-relative synthesis and exact residual domain).**
On every source of Definitions 1.1–1.2, one finite controller
earns the native topology and unknown order by $b$ actual
first-arrival trials, earns all native coefficients and the
degree-$I$ coordinates by a further $b$ trials through $2I+1$,
and installs an exact predictor at the actual endpoint of that
same acquisition. The controller supports Theorem 5.1's
arbitrary-current passive window and the complete adaptive
menu thereafter, with the simultaneous attained costs in §7.
Authentic all-leaf coverage is sufficient, and its removal
admits the different-order complete-service countermodels in
§8. The source-relative addition is this conjunction of
unknown branching topology, earned finite native coordinates,
actual current-cut installation and paid continued use; tree
metrics, infection, Gram reconstruction and finite-word
transport remain credited intermediate suppliers.

The theorem concerns precisely this conditional native tree
model. It leaves the fixed-$G_{\rm gc}$/original-$Q$/parked-consumer
and original-initialization obligations in their original domains.
It neither derives a physical geometry nor certifies roster
completeness, calibration or rights, and supplies no universal
$\alpha/\beta$ generator or all-source four-expression inverse.
General controlled-journal inversion is excluded by Proposition
6.2; general incomplete-interface impossibility is excluded
from the quantifier by Corollary 8.2. No sharp all-tree resource
optimum, uniform noisy inverse or unrestricted physical
implementation theorem is asserted.

Proof. Apply Theorem 2.2 and Corollary 2.4 on the initial actual
source, Definition 3.1 and Theorem 3.3 on its subsequent reset
trials, and Theorem 4.3 at their last actual endpoint.
Theorem 5.1 and the unchanged native invariant supply later
current recovery and common adaptive use. Proposition 7.2
counts that same run; Propositions 7.3–7.5 and Definition 7.4
give one simultaneous arithmetic/storage/traffic realization.
Theorem 8.1 and Corollary 8.2 establish the exact failure of
the enlarged incomplete-roster class. The remaining domain
statements follow from the explicit hypotheses and the
counterexamples in §§6 and 8: changing a model or adding a
port cannot discharge a theorem whose original source and
initialization are fixed differently. These are source-relative
proved consequences, without a global priority claim for
their standard intermediate mathematical methods. $\square$

## 追加锚（本行以下为增补区）

## 10. A changed installation: ordered leaf waves on the actual LAB material

**Definition 10.1 (the one source and its concealed entrance).** Use the
birth-typed LAB of [Atomic Generation Acquisition, §§17–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md),
written AA below. An actual finite legal word from its originally allocated
$\alpha$ has produced an unknown current term $t\in\mathcal D$. There are
$L\ge3$ logical leaves. The material source is that very $C(t)$ of AA
Definition 17.3, with AA Definition 20.2's persistent-vertex growth templates.
Thus an $\alpha$ is a terminal material vertex, a $\beta$ is a material
vertex with one left terminal marker, and a branch has two ordered logical
children. A marker is not an additional logical leaf or a permitted logical
growth target. The birth constraint defining $\mathcal D$ is that every
logical leaf at an $L$-ending address is $\beta$. Put $V=V(C(t))$,
$N=|V|$, and let $A_t$ be the symmetric unit adjacency matrix of its
material edges, with zero diagonal.

The installation in this section differs from both AA's seven-request
record service and Definitions 1.1–1.2 above. It equips every actual
material vertex with a rational field cell, initially zero, and installs
exact unit-adjacency field evolution. The same zero-cell initialization
and growth lift of Assumption 10.2 apply during the old preparation,
which uses only its successful $P/S$ word and no field inputs. The
adjacency rule is known; its
matrix, order $N$, original root, logical syntax, internal addresses and
Tag values are not given to the observer. No old generation word, routing
tape, allocation ordinal, clock, internal field read or internal actuator
is exposed. The source is promised reachable from the original $\alpha$;
it is not promised to lie at a common global-substitution epoch.

The observer has one authentic reference to this source service, the
original current addressed $P/S$ authority, and a framed complete
left-to-right roster of its material terminals. There is one terminal for
each logical leaf: the leaf itself for $\alpha$, its marker for $\beta$.
Because $L\ge3$, the logical root is a branch; consequently these terminals
are exactly all degree-one vertices of the unrooted material tree.
The roster provides current ordinal ports $1,\ldots,L$, bound by the
installed dispatcher to those actual terminals in that order. An ordinal
port is not a material address or an internal vertex reference.

**Assumption 10.2 (field service, growth service and complete replies).**
Calls are serialized on this one source. Completed calls leave a settled
cut. A requested Tick is the only field evolution; Hold prevents any
unrequested evolution during finite local work. At a current term $u$ and
field $x\in\mathbb Q^{V(C(u))}$ the full primitive menu is the following.

| Request | Actual effect | Complete reply |
| --- | --- | --- |
| Reset | Replace the field by zero on every current material vertex; retain the source tree | fixed acknowledgement |
| Add$(j,q)$, $1\le j\le L(u)$, $q\in\mathbb Q$ | Add $q$ at the actual current $j$th terminal | fixed acknowledgement |
| Tick | Replace $x$ by $A_u x$ | fixed acknowledgement |
| Read$(j)$, $1\le j\le L(u)$ | Retain the field and tree | the literal rational at that terminal |
| Hold | Retain the field and tree, preventing intervening ticks | fixed acknowledgement |
| $P_p$, $p\in\{L,R\}^*$ | The original logical $\alpha\mapsto\beta$ if enabled | original tagged Growth$(P,p)$, or original tagged refusal |
| $S_p$, $p\in\{L,R\}^*$ | The original logical $\beta\mapsto\langle\beta,\alpha\rangle$ if enabled | original tagged Growth$(S,p)$, or original tagged refusal |

The growth guard first navigates the original logical syntax. An absent
address, a branch target and a wrong leaf type have the distinct refusal
meanings of AA Definition 20.2, and leave the entire source and field
unchanged. In particular navigation cannot pass through a unary marker.
Missing rights disable a call; they are not a leaf-type refusal. An integer
Add/Read ordinal outside the current roster returns a fixed RangeRefusal
without change. Complete finite frames, rational inputs and replies have
actual finite backing and are fully transmitted. Replies contain no timing,
work, meter or resource metadata; allocation exhaustion is not an exposed
branch of this finite-material-supplied service. Growth address and reply framing can be exactly
AA's $A(p)=1^{|p|}0p$, with its kind and refusal tags. Malformed complete
frames return BadFrame without change; a proper incomplete prefix does
not already have a completed reply. No Tag, HasPromotion, HasSplit,
FetchGrowth or Next request is a port of this menu.

The field lift of growth is fixed before observing any responses. For an
enabled $P_p$, retain the old terminal $v$ as the new $\beta$ root, attach
one fresh left marker $m$, and set $x_m=0$. For an enabled $S_p$, retain
its old root $v$ as a branch, reuse its old marker $m$ as the left logical
$\beta$ root, attach a fresh marker $a$ to $m$ and a fresh right $\alpha$
vertex $b$ to $v$, and set $x_a=x_b=0$. Every old vertex keeps its field
value. Edges already present are retained. Equivalently, writing $i$ for
the actual inclusion of old vertices into the new source,

$$
x'_{i(v)}=x_v\quad(v\in V(C(u))),\qquad
x'_z=0\quad(z\text{ fresh}).
\tag{10.1}
$$

The current ordinal roster is rebound by this same material edit: $P$
replaces the target terminal $v$ by $m$, while $S$ replaces the target
terminal $m$ by the consecutive pair $(a,b)$. Other terminal identities
and their relative order persist. This is an installed dispatcher rule,
including its backing and rights over fresh cells, rather than an
inference that a computed name grants access. No allocation names or
extra roster metadata are added to the original growth reply.

Full-field calibration, authentic completeness and order of the roster,
source binding, the original root used by the addressed dispatcher,
exclusive current rights, sufficient finite fresh material, exact rational
arithmetic and complete call/return are hypotheses. The source root is
retained inside that dispatcher but concealed from the observer. Growth
may be realized by finite reserved edits as in AA §20; no field call or
other growth interleaves an unfinished edit. Reset resets the field only,
not LAB's source or its birth history. Costs of the actual installation,
preparation, dispatch and fresh grants are included in §15. These premises
assert an ideal mathematical installation; numerical inversion will not
certify them.

## 11. Ordered leaf waves identify the original root

**Theorem 11.1 (root and ordered-syntax rigidity for reachable LAB).**
Let $t\in\mathcal D$ have at least three logical leaves. Its unrooted
unit material tree together with its complete linear terminal order
determines its original root, every material left/right edge, and its
ordered logical term uniquely. An effective inverse uses no root, Tag,
size bound or generation word as advice.

Proof. A proposed root for a valid presentation with at least three
terminals must be binary, hence have unrooted degree two. After choosing
a proposed root, all edges are oriented away from it. At a binary vertex,
the two child subtrees must have nonempty disjoint intervals of the given
terminal order. Their order is forced by the smaller first terminal.
At a unary vertex its sole child must be terminal, and its edge is the
left marker edge of a $\beta$. A terminal parses as $\alpha$. These rules
leave at most one ordered parse for that root; checking its leaf order
and the condition that no logical $L$-ending leaf is $\alpha$ is finite.
The original root and presentation pass these checks.

For uniqueness let $r$ be the original root and suppose another vertex
$r'\ne r$ passes. In the original material tree, a nonroot branch has
degree three, a terminal has degree one, and every nonroot degree-two
vertex is a logical $\beta$ root. Thus $r'$ is such a $\beta$ root with
its own adjacent terminal marker $m$.

When rooted at $r'$, that terminal becomes a logical $\alpha$ child of
the proposed binary root. It cannot be its left child, by birth typing.
It must therefore be its right child and must be the last terminal of
the entire given linear order. In the original rooting, the last
terminal belongs to the right subtree of $r$, since both original child
subtrees contain terminals. Its adjacent $\beta$ root $r'$ consequently
lies in that right subtree. After rerooting at $r'$, the old root $r$
has one parent along its old right subtree and just one child, namely
its old left child. But this child is not terminal: a logical subtree
at address $L$ cannot be $\alpha$, so it is either $\beta$ with a marker
or a branch. Thus the proposed presentation makes $r$ unary with a
nonterminal child, which is not any $C(u)$. This contradicts validity.
It follows that $r$ is the only possible root.

For the inverse, enumerate the vertices of the finite supplied tree,
test each degree-two candidate by the oriented parsing and interval
checks, and retain the unique success. Decode a unary vertex and its
marker as one logical $\beta$; do not decode its marker as a logical
child. The forced child orders give all original material addresses and
the original logical term. All vertices and candidates come from the
finite tree itself, not from an external order bound. $\square$

**Theorem 11.2 (paid acquisition on the concealed actual source).**
Under Definition 10.1 and Assumption 10.2, one source-independent finite
controller acquires that original root and ordered term using only the
field ports. It uses exactly $L$ actual unit-pulse trials. For

$$
D_j=\max_{k\ne j}d_{C(t)}(\ell_j,\ell_k),\quad
K=\sum_{j=1}^{L}D_j,\quad R=L(K+L),
\tag{11.1}
$$

these trials use $L$ Resets, $L$ Adds, $K$ Ticks, $R$ scalar Reads and
$K+L$ Holds, with one Hold at every sampled epoch. Their last actual
held field is $A_t^{D_L}e_{\ell_L}$. The acquired topology determines
$N$ and $A_t$; no separate coefficient-learning trials are necessary.

Proof. Freeze the source syntax by issuing no growth during acquisition.
For each roster position $j$ issue a real Reset and Add$(j,1)$, then read
all current terminals under Hold initially and after each successive
Tick. Stop this trial exactly when every other terminal has returned a
nonzero value at least once. Lemma 2.1 applies with every link equal to
one and every diagonal zero. Its first nonzero at terminal $k$ occurs
at exactly $d(\ell_j,\ell_k)$ and equals one. Thus Theorem 2.2 supplies
termination, the ordered distance table and precisely these calls,
including every zero reply. Resets act on all the same actual cells;
there are no cloned trials or unrequested waves.

Apply Lemma 2.3 to those distances. Its distance vectors recover every
unit subdivision vertex, not only a reduced tree. The resulting
unrooted graph is leaf-fixing isomorphic to the actual $C(t)$, by
$v\mapsto\delta(v)$. It earns $N$ by counting its vertices. Apply
Theorem 11.1 to identify the original root and ordered material
addresses, and parse the unique logical $t$. Since the evolution rule
was unit zero-diagonal adjacency, the reconstructed graph already
supplies its complete $A_t$. No use of §3's coefficient trials or
infection is being charged as if it had occurred here.

Each new trial reset its predecessor's field. After the last Reset and
Add there were exactly $D_L$ Ticks, so its present field is exactly the
stated power on the same source. During reconstruction it remains held.
All stopping decisions before reconstruction used only earned replies
and growing counters. $\square$

**Definition 11.3 (persistent coordinates and the acquired cut).** Let
$\iota$ be the proved correspondence from the recovered material-address
tree to the actual vertices. It sends its empty material address to the
original root and its ordered terminals to their authentic roster
positions. The observer stores a finite tree code, a field vector and a
current terminal-index table. It can compute the last-trial vector
$\widehat x=A_t^{D_L}e_{\ell_L}$ in those coordinates while Hold remains
in force. Thus it can synchronize already at that nonzero last-trial
cut. For a zero-field entrance, issue one further actual Reset and Hold
and replace the retained vector by zero after the Reset acknowledgement.
This adds precisely one Reset, one Hold and two acknowledgements.

Material addresses, once recovered, are persistent coordinates: $P_p$
adds $pL$ and $S_p$ adds $pLL,pR$, reusing $pL$. Every old material
address survives, though some terminal addresses become internal and
some marker addresses become logical. The acquisition distance vectors
are not used as permanent cell names after the roster changes. In
particular the observer does not move an old value to whichever new
terminal has the old ordinal. The map $\iota$ is a proved correspondence,
not a callable internal-reference cast.

## 12. Original guards and full same-source action correspondence

**Theorem 12.1 (one-step correspondence, including persistent fields).**
Suppose the retained code is the actual current ordered term $u$, its
material-address field satisfies

$$
\widehat x_a=x_{\iota(a)}\quad(a\in V(C(u))),
\tag{12.1}
$$

and its terminal table gives the actual current ordinal roster under
$\iota$. The retained code determines the original four-valued logical
Tag at every finite address without a Tag call. It determines the exact
original $P/S$ guards, refusals and complete growth replies. Each primitive
in Assumption 10.2 has a computable retained successor and complete
predicted reply preserving (12.1) and the roster correspondence.

Proof. Logical navigation in the retained term has exactly the original
meaning: descend only through branches, return absent when a requested
suffix meets a logical leaf, and test its current constructor at an
existing target. AA's original $P/S$ guard is therefore decided at that
same original address, not at a position in a separately rerooted tree.
A blocked or wrong-type request has the same specified refusal and leaves
both configurations unchanged.

For an enabled $P_p$, let $v$ be its actual old terminal. The actual edit
retains $v$ and adds its fresh marker, while the retained vector keeps
coordinate $p$ and adds $pL$ with value zero. The new roster
replaces the old terminal at this position by that new marker; no value
is transferred from $v$ to the marker. For an enabled $S_p$, the old
marker at $pL$ persists, with its old value, as the new left $\beta$
root. The actual edit and its retained representation add the corresponding
zero-valued vertices $pLL,pR$, keep the old root's value at $p$, and keep
every other cell and old edge. Their
rosters replace the old terminal $pL$ by $(pLL,pR)$ in precisely that
order. Extend $\iota$ by the actual two fresh vertices. These are exactly
(10.1) and the original AA material templates, so complete fields,
rosters, actual source guards and Growth replies correspond. Current
rights and fresh material are supplied by Assumption 10.2, rather than
created by extending the mathematical map.

Reset sets every retained and actual cell to zero. Add uses the same
current terminal through the corresponding ordinal table, and its
arbitrary rational operand is added on both sides. For Tick the graph
isomorphism intertwines unit adjacency:

$$
(A_{\rm actual}x)_{\iota(a)}
=\sum_{b\sim a}x_{\iota(b)}
=\sum_{b\sim a}\widehat x_b
=(A_u\widehat x)_a.
\tag{12.2}
$$

Read returns the same literal rational by (12.1), and Hold changes
neither configuration. Acknowledgements and refusal tags are also
identical. The original typed range $1\le j\le L(u)$ for Add and Read
is determined by the same current roster length; an out-of-range integer
ordinal gives the same RangeRefusal and identity successor. Complete
malformed frames give the same BadFrame and identity successor; incomplete frames
have no completed operation on either side. This proves the statement
on the complete declared menu, not only on successful growth. $\square$

**Theorem 12.2 (installed prediction for every finite adaptive continuation).**
At either synchronized cut of Definition 11.3, retain the acquired code,
current field, roster table, finite instruction program, authentic service
reference and current original rights with their backing. For every finite
common adaptive continuation in the full menu of Assumption 10.2, the
predictor has identical complete replies and corresponding actual source,
field and roster successors at every settled cut. Arbitrarily large finite
addresses, rational operands and current roster sizes are admitted. A
common policy may use earlier replies and retained common information for
its next request, operand or stopping decision; a common random tape is
also allowed.

Proof. Theorem 11.2 and Definition 11.3 establish (12.1) at the actual
last-trial endpoint and after the optional paid zeroing. Retained finite
syntax navigation, sparse adjacency addition and finite vector extension
compute each operation of Theorem 12.1. Source calls and retained updates
are serialized; expose the next settled cut only after the corresponding
update and complete output. The original retained entry executes an actual
$P/S$ when requested. Merely calculating a hypothetical successor sends
no source command and produces no physical source change.

Induct on the finite number of completed calls. Equal preceding replies
make a common policy choose the same next complete request. Theorem 12.1
gives equal legality, the entire reply, and the extended invariant. This
also covers a failed growth without changing syntax or field. Fixing a
common random tape gives the same induction for each realized finite
continuation. The maintained matrix can be singular: no inverse of
adjacency is used. A finite program is accompanied by the growing actual
records and operand widths charged in §15. $\square$

**Proposition 12.3 (a current $\rho$ as actual original actions).** After
acquisition, list the current logical leaves of $u$, once, in their
left-to-right order. At each listed original address $p$ issue $P_p$ if
its acquired current leaf is $\alpha$ and $S_p$ if it is $\beta$. Do not
visit a fresh leaf during this pass. This finite macro has the original
source successor $\rho(u)$ of [FARG Definition 3.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md),
on the same physical source, with all old field values retained and only
fresh cells initialized to zero. Its complete output is the ordered list
of those original Growth replies. The predictor of Theorem 12.2 predicts
all its intermediate and final settled configurations. If there are
$a$ current $\alpha$ leaves and $c$ current $\beta$ leaves, this macro
uses exactly $a$ promotions, $c$ splits and $a+2c$ fresh source vertices.

Proof. The original leaves form a logical address antichain. An edit at
one changes no other listed leaf or its original address. Thus every
listed operation remains enabled when reached; each is its genuine
original $P$ or $S$. The final term replaces just these old leaves by
$\beta$ and $\langle\beta,\alpha\rangle$, respectively, and preserves
all old branch constructors. This is exactly FARG's recursive $\rho$,
rather than an assumption that one local event already means global
substitution. Formula (10.1), applied successively, proves the field
claim for every old vertex, including every reused marker. The counts
follow from the one- and two-vertex templates. The macro introduces no
new primitive port, free Tag call or right; all its constituent requests,
outputs, navigations, grants and storage are paid. $\square$

## 13. Four independent expressions at settled zero-field cuts

**Definition 13.1 (domain and independently meaningful observations).**
Fix the installation, its actual source binding and current authority.
The recovery domain $\mathcal Z$ consists of its settled cuts after the
acquired predictor has been installed, with a reachable term having at
least three logical leaves and zero on every material field cell. Requests
and outputs are complete, no edit is pending, and the installed predictor
has completed its matching update.
The following observations are defined by their source meaning, before
using any recovery map.

| Expression | Exposed content on $\mathcal Z$ |
| --- | --- |
| Space | The unrooted unit material tree, its complete linearly ordered terminal set, and its present zero field, modulo terminal-order-preserving isomorphism |
| Time | The labelled causal birth/lifecycle order of the successful original $P/S$ events from the original seed to the present source |
| Boundary | The ordered terminal-to-terminal onset table: the least number of autonomous adjacency Ticks at which a unit terminal impulse first gives a nonzero reading at another terminal, with zero on the diagonal and present terminal field zero |
| Memory | The retained finite recursive constructor record, current zero field vector and ordinal terminal table, with the actual bound callable service entry and its current rights |

Time means AA's actual causal order $E(t)$, not a total event word. Its
labels are original $(P,p)$ and $(S,p)$. Its direct causal relations are
the required local promotion before split and the creating split before
the first event at a child position, followed by transitive closure.
It records neither source-independent Holds nor field Ticks, numerical
input chronology, allocation serials, or an arbitrary linear extension.

Boundary is a finite travel-time observation of the declared field law.
It is not given as an initial oracle; Theorem 11.2 acquires it by the
actual trials. The law's later responses can be computed from recovered
adjacency, but those calculations do not retroactively supply unpaid
wave observations. Memory stores a finite local transition representation
and current field, rather than an old command journal or unrestricted
list of future answers. It is actually installed by §§11–12, and after
continued use its updated contents remain on that same source reference.
The binding and rights are common conditions of the four views. Recovery
of data under those conditions is distinct from installing new bindings.

**Theorem 13.2 (mutual recovery and route agreement on $\mathcal Z$).**
Each expression in Definition 13.1 determines the other three as data on
their actual joint image. All routes agree. The reconstructed original
guards, complete outputs and settled successors agree for every admitted
operation that starts and ends in $\mathcal Z$; the installed predictor
also remains correct on continuations leaving $\mathcal Z$. No chosen
serial source history is needed for these assertions.

Proof. Boundary's onset table is the actual unit leaf distance table,
by Lemma 2.1. Lemma 2.3 recovers its full material tree, and Theorem 11.1
recovers its original root and ordered $t$. Conversely Space directly
computes terminal distances, and the same root theorem parses $t$.
The global vector is known to be zero on the declared domain; it is not
inferred merely from the instantaneous terminal zeros.

AA Theorem 17.2 identifies the actually occurred events precisely as

$$
E(t)=\{S_p:p\text{ is a current logical branch}\}
\ \cup\ \{P_p:p\text{ was born }\alpha\text{ and its current subtree is not }\alpha\}.
\tag{13.1}
$$

Here the root and every $R$-ending position were born $\alpha$, and every
$L$-ending position was born $\beta$. The actual local and creation
precedences are exactly that theorem's causal order. Thus recovered $t$
gives actual Time, not an arbitrarily selected serialization. Conversely
AA's explicit reconstruction from those labelled events recovers $t$:
a split supplies both children, its own position is a branch, and an
unsplit leaf is $\beta$ precisely when born $\beta$ or promoted. This
argument applies to every legal old source word ending at $t$.

Memory's constructor record parses as the same $t$ by its stored meaning;
its terminal table and zero vector are fixed by that record on this
domain. Conversely $t$ constructs these finite data and all predictions
of the declared menu, while the actually retained service entry is the
fixed existing binding. Mathematical construction of these data is not a
new grant of that entry. The paid acquisition and synchronization of
§11 prove that this representation really is installed, and Theorem 12.2
maintains it subsequently.

Every recovery just described factors through this single original $t$
and its zero field. The composition back to any of the four observations
is its identity on the actual image. In particular recovering a third
view through either of two intermediate views gives the same data, with
the same original address interpretation.

A successful $P/S$ extends the actual event set by precisely its new
label and the required lifecycle/creation precedences. Formula (10.1)
preserves a zero field. Field Tick, Read and Hold leave zero and the tree
unchanged. Reset leaves the source and Time unchanged and zeros the
field. Add$(j,0)$ also remains in $\mathcal Z$; a nonzero Add leaves it.
Growth refusals, RangeRefusal and BadFrame preserve the state. Applying any recovery before
or after an operation with both cuts in $\mathcal Z$ therefore yields
the actual view of its same unique successor. For any longer finite
composite returning to zero, the full invariant of Theorem 12.2 gives
that same final correspondence, even if intermediate cuts are outside
$\mathcal Z$. Proposition 12.3 gives the analogous statement for the
current $\rho$ macro. $\square$

**Proposition 13.3 (task kernel and the zero-field restriction).** With
binding and rights fixed, the four data observations on $\mathcal Z$
have exactly the continuation kernel of Assumption 10.2. Outside this
domain the installed predictor still has full field correspondence,
but Time and the onset table alone do not recover a general present
field or a field-control journal.

Proof. Theorem 13.2 identifies each observation exactly with $t$ on
$\mathcal Z$. Equal $t$ and zero field yield the complete continuation
correspondence by Theorem 12.2. Conversely, different roster lengths are
already different exposed interfaces. For equal roster lengths, if the
distance tables agreed, Lemma 2.3 and Theorem 11.1 would make the terms
equal. Thus different terms have different onset data and are separated
by some finite Reset/Add/Tick/Read experiment from §11. A sufficiently
long common finite experiment detects that difference; it need not rely
on choosing different stopping decisions in the two compared sources.
This proves the claimed exact kernel for this declared menu.

For the domain boundary, at any fixed $t$ compare $x=0$ with
$x=e_{\ell_j}$. Time and all onset times agree, whereas Read$(j)$ gives
zero and one. Both fields are actual reachable controls at that source:
use Reset in one run and Reset followed by Add$(j,1)$ in the other.
Even instantaneous terminal zeros cannot certify a global zero field:
a nonterminal unit field restricts to zero at all terminals. The mutual
inverse above is conditional on the actual zero-field domain, not on
such a terminal-only test. The already installed full vector can decide
whether the actual field has returned to zero, since (12.1) remains true.
Reset restores that domain by an actual paid command. Finally an extra
Hold, a Tick at zero, or Add$(j,1)$ followed by Reset changes the control
journal without changing the final zero-field views. No inverse to
those journals or elapsed physical duration follows. $\square$

## 14. Load-bearing order, birth typing and the unrecovered old word

**Theorem 14.1 (terminal order is needed by this wave-to-syntax inverse).**
If the authentic linear terminal order is omitted, complete all-terminal
field service alone need not determine the original ordered LAB syntax
or its original addressed guards, even for reachable terms with three
logical leaves and known unit zero-diagonal adjacency.

Proof. Take

$$
u=\langle\beta,\langle\beta,\alpha\rangle\rangle,
\qquad
v=\langle\langle\beta,\alpha\rangle,\beta\rangle.
\tag{14.1}
$$

Both are in $\mathcal D$ and hence reachable by AA Theorem 17.2. Their
material trees are isomorphic as rooted unordered trees, by exchanging
the two root children and transporting their subtrees. Label their
terminal ports by that isomorphism with a common arbitrary list, rather
than by their different original left-to-right orders. The adjacency
matrices are conjugate by the corresponding permutation, and the input
and output terminal columns are transported by that same permutation.
Starting at zero, equality of full fields under this permutation is
preserved by Reset, arbitrary rational terminal Add, Tick, Read and Hold.
All their complete field-service replies therefore agree, for every
finite common adaptive policy, not just for the first-arrival table.

But $S_L$ is enabled at $u$ and is refused at the branch $L$ of $v$.
Thus the unordered wave data cannot select the correct original logical
syntax or those guards. This removes only the linear-order premise of
the acquisition; it does not claim that the larger active $P/S$ menu
could never be used for a different destructive identification task.
$\square$

**Theorem 14.2 (birth typing is needed even with the linear order).**
If the candidate class is enlarged from reachable LAB terms to arbitrary
ordered $\alpha/\beta$ terms with their $C$ material presentations, the
same complete ordered terminal wave service can have two different
roots and original addressed guards.

Proof. Let

$$
t=\langle\langle\beta,\alpha\rangle,\alpha\rangle,
\qquad
s=\langle\alpha,\langle\alpha,\beta\rangle\rangle.
\tag{14.2}
$$

For $C(t)$ name the root $r$, its left branch child $h$, the left
$\beta$ root of $h$ by $b$, and its marker by $c$. Name the right
$\alpha$ child of $h$ by $d$, and the right $\alpha$ child of $r$ by $e$.
Its complete material edges and terminal order are

$$
\{r,h\},\{r,e\},\{h,b\},\{h,d\},\{b,c\},
\qquad (c,d,e).
\tag{14.3}
$$

Root that very unrooted tree instead at $b$. Its ordered children are
$c$ and $h$; the latter has ordered children $d$ and $r$; the latter is
unary with terminal child $e$. This is precisely $C(s)$, with exactly
the same terminal order $(c,d,e)$. Unit adjacency and all ordered
terminal input/output coordinates are identical. Thus all the field
service, with arbitrary controls and complete replies, is identical
from zero under the identity on these material vertices. Yet the roots
are $r$ and $b$, and $P_L$ is refused at the branch of $t$ but enabled
at the $\alpha$ leaf of $s$.

The first term is reachable LAB; the second has an $L$-ending
$\alpha$ and is not. This is a countermodel for the expressly enlarged
class after removing birth typing, not two reachable sources purporting
to contradict Theorem 11.1. $\square$

**Theorem 14.3 (no recovery of an unretained original serialization).**
The acquisition and full continuation menu of §§10–12 do not recover an
arbitrary actual old generation word. AA's complete promotion-erasure
fibres, including its nonuniform fibres conditional on the old split
word, remain unchanged. No serial-history recovery is implied by naming
Time as causal birth order.

Proof. Fix any $t\in\mathcal D$ and any two legal old generation words
ending at it. Preparation initializes every field cell to zero and
preserves zero through its $P/S$ edits. At attachment the exposed sources
have the same ordered material-address tree, field, roster and declared
rights. Hidden allocation ordinals or old records are not ports of
Assumption 10.2. The proof of Theorem 12.1 then supplies identical entire
replies and corresponding successors for every future field or growth
request. Induction gives this equality for every finite adaptive
acquisition, including the protocol of §11 and any subsequent active
$P/S$. Future choices cannot distinguish which of the two old words
actually occurred.

For a nontrivial same-split-word pair use AA equation (AA.75):

$$
P_\varepsilon S_\varepsilon S_LP_R,
\qquad
P_\varepsilon S_\varepsilon P_RS_L.
\tag{14.4}
$$

Both end at $\langle\langle\beta,\alpha\rangle,\beta\rangle$ and have
split word $(\varepsilon,L)$, but their third generation events differ.
The more general exact ambiguity, conditioned on an already supplied
split chronology, is AA Theorem 18.2's $F_t(\sigma)$; its injectivity
criterion and AA Theorem 18.3's uniform endpoint criterion are not
altered. The present field installation supplies no additional old-word
label, so it does not shrink those fibres. AA's FetchGrowth/Next task
would require the actually retained supplement of AA §§19–22; it is not
implemented by calling the causal order a serial history. Newly retaining
future commands supplies their future suffix only, not the missing old
prefix. $\square$

## 15. One actual resource account, including preparation and continuation

**Definition 15.1 (charged representations).** All counts below refer to
the same actual source and its retained observer. Charge each command,
scalar reply, acknowledgement, complete frame, local comparison and
arithmetic operation at its actual finite operand width. Rational words
use reduced signed numerator and positive denominator with finite framing;
references use their actual encodings and current grants. The actual
program, roster dispatcher, root binding inside that dispatcher, service
reference, permissions and assurance, links, field buffers, source and
observer work, input/output backing, raw readings and retained copies
coexist. A shared object is charged once only when it is actually shared.
No unit-cost arbitrary integer, reference or exact-real wave oracle is
part of the model.

Let $c$ denote the current number of logical $\beta$ leaves before
acquisition. For its actual preparation word $w_0$, let
$D_0=\sum_{e\in w_0}|\operatorname{addr}(e)|$. This is an analysis
parameter, not a supplied or reconstructed old journal. Let $Q$ be
Lemma 2.3's number of candidate distance vectors before deduplication,
so $Q\le {L\choose2}(D+1)$, where $D=\max_jD_j$. All parameters $N,D,Q$
are earned or used only in a posteriori bounds; none is stopping advice.

**Proposition 15.2 (source preparation and actual acquisition work).**
Preparing the actual old source by AA's original seed and templates has
exactly $c$ promotions, $L-1$ splits and

$$
N=2L+c-1
\tag{15.1}
$$

material vertices. With parent/left/right fields initialized as in AA
Proposition 22.1, its located source-field assignments are
$3+4c+8(L-1)$, and there are $N$ initial zero field-cell writes.
Its actual old navigations, requests, replies, finite work, allocation
and grants must be charged in addition; their serial order is not
recovered by the new experiment. If auxiliary historical records are
retained by a chosen preparation, their complete actual backing and
maintenance are additional costs, not free inputs to the observer.

Including the final paid Reset and Hold giving the zero-field entrance,
the acquisition in §§11–12 uses exactly

$$
\begin{array}{c|c}
\text{operation}&\text{actual number}\\ \hline
\mathrm{Reset}&L+1\\
\mathrm{Add}(j,1)&L\\
\mathrm{Tick}&K\\
\mathrm{Read}(j)&R=L(K+L)\\
\mathrm{Hold}&K+L+1
\end{array}
\tag{15.2}
$$

There are $2K+3L+2$ fixed acknowledgements in addition to the $R$ literal
scalar replies. One direct source Tick clears an output buffer of $N$
cells and adds each directed-edge contribution, using exactly $2(N-1)$
rational additions and no scalar multiplications. Acquisition therefore
pays $2K(N-1)+L$ source additions, $(L+1)N$ Reset cell writes and $KN$
Tick-buffer zero writes, besides buffer exchange, dispatch, reads and
serialization. These are source costs in addition to observer work.

Proof. AA's source counts give $P_0=c$, $S_0=L-1$, and
$1+P_0+2S_0=2L+c-1$. The located writes use exactly those same persistent
source templates; the additional rational cell is initialized once at
each actual allocation. Old addresses require their actual navigations,
with total successful-address length $D_0$; no hidden interpretation of
$D_0$ as zero is justified by not knowing its old ordering.

Theorem 11.2 counts all trials, and Definition 11.3 adds the final Reset
and Hold. Reset, Add, Tick and Hold each produce one acknowledgement;
summing their rows gives $2K+3L+2$. A unit tree has $N-1$ undirected
edges. Accumulating its $2(N-1)$ directed contributions into zeroed output
cells gives the displayed attained Tick count. Each unit Add makes one
additional addition. Full-field Reset writes every actual cell, including
all initially concealed ones. $\square$

**Proposition 15.3 (finite earned decoding and simultaneous stores).**
For the acquisition of Proposition 15.2, all field entries and scalar
replies are integers of width $W_0=O(N+1)$. There is an attained local
reconstruction using

$$
O\bigl(LQ^2+LN^2+N^2(N+L)+ND_L\bigr)
\tag{15.3}
$$

integer comparisons, elementary integer operations and additions, at
the actual widths. The first three terms recover and root the graph;
the final term can compute the actual nonzero last-trial field before
zeroing. No coefficient-learning second trials are included. An attained
simultaneous layout has the following charged stores.

| Store | Bound or actual separate charge |
| --- | --- |
| Actual source structure and its two field buffers | $N$ vertices, $N-1$ links, their actual reference words and $O(NW_0)$ field bits |
| Raw acquisition scalar readings, retained separately | $O(RW_0)$ bits, with actual framing and copies |
| Chronological framing and counters | $O((R+K+L)\log(N+1))$ bits for one explicit framed layout |
| Distances, candidate vectors and earned native names | $O((L^2+LQ+LN)\log(N+1))$ bits |
| Root-candidate work and explicit material addresses | $O(NL+N^2+N\log(N+1))$ bits in addition to earned names |
| Retained recursive syntax, field vector and current terminal table | $O(N+NW_0+L\log(N+1))$ bits, plus actual bindings and any separate address copies |
| Program, callable reference, original growth authority, leaf dispatch, Hold/Reset installation and backing | their actual simultaneous representations and resources |
| Input/output, reserved material and other work backing | their actual coexisting encoded lengths |

These rows are added for this chosen layout, including separate raw data
and decoded records; they are not incompatible separately optimal bounds.

Proof. Every material degree is at most three, including the root.
During a unit trial $\|A_t^k e_{\ell_j}\|_\infty\le3^k$ and all entries
are nonnegative integers. Trials stop with $k\le D\le N-1$, so their
scalar widths are $O(N+1)$. This also bounds an explicit computation of
the last-trial vector. Counter and distance values use $O(\log(N+1))$
bits; accumulating the total trial count uses that same order since
$K\le L(N-1)\le N^2$.

Lemma 2.3's explicit enumeration, pairwise deduplication and adjacency
comparison use $O(LQ^2+LN^2)$ elementary integer operations. After that,
for each of at most $N$ root candidates, root the finite graph, accumulate
its descendant terminal sets as $L$-bit vectors, check their intervals,
parse its arities and construct addresses of length at most $N-1$.
Across all candidates a conservative bound is $O(N^2(N+L))$ bit and
integer operations. Keep one candidate's work at a time; its terminal
sets require $O(NL)$ bits and its explicit addresses $O(N^2)$ bits.
Accept the unique valid candidate by Theorem 11.1. Sparse iteration
through $D_L$ steps computes the actual last field in $O(ND_L)$ further
additions. No numerical root extraction or unbounded-precision linear
solve is needed because all coefficients were specified as unit adjacency.
The listed stores describe these very constructions. Actual allocation,
clear/reuse work and complete transmitted words remain additional.
$\square$

**Proposition 15.4 (continued fields, growing operands and actual actions).**
For a finite continuation of $f$ complete commands after acquisition,
write $g_P,g_S$ for its successful growth counts, $h$ for its field Ticks,
and $U$ for the sum of all encoded rational input lengths. Then

$$
N_f=N+g_P+2g_S,\qquad L_f=L+g_S,
\tag{15.4}
$$

and an attained bound on the width of every current field coordinate is

$$
W_f=O\bigl(N+U+h+\log(f+1)+1\bigr).
\tag{15.5}
$$

The $N$ term allows synchronization at the nonzero last-trial cut; at the
paid zero-field entrance it can be omitted from this numerical bound.
There is no fixed bound on $U$, address lengths, roster size, reference
widths, reply lengths or retained memory over all finite continuations.

One source and native predictor Tick together use $4(n-1)$ rational
additions and $2n$ output-buffer zero writes when the current order is
$n$. Reset writes $2n$ zero cells across source and predictor. Add uses
one source and one predictor addition, with actual terminal dispatch.
A successful $P$ allocates one source vertex and $S$ two, with respectively
four and eight located source parent/left/right assignments as in AA's
templates, plus their new zero field cells. Charge corresponding observer
updates as well. A simple attained roster maintenance traverses the entire
current finite material tree after growth; its work, comparisons and
backed indices are included rather than hidden in an ordinal renaming.

Every request pays its complete operation tag and payload, including each
$A(p)$ and rational or current terminal index; every reply pays its entire
rational word, Growth address, refusal or acknowledgement. Actual grants,
references, navigation, reserves, output emission and return remain
charged. Retaining the later journal or copies adds their actual lengths.
The source field buffers and the observer's current field, syntax and
terminal table coexist with whatever old acquired readings are retained.

Proof. Each growth has exactly the physical and roster changes already
proved in Theorem 12.1, giving (15.4). Growth does not amplify an old field
coordinate and inserts only zeros. Between Resets, every Tick has row
sum at most three. A common denominator for all inputs divides the
product of their positive denominators, whose bit length is at most $U$.
The magnitude of a current coordinate is at most $3^h$ times the starting
maximum plus the sum of the propagated input magnitudes. There are at
most $f$ such inputs. Encoding the common denominator, their numerators
and this sum gives (15.5); a Reset can only remove earlier terms. This
argument also bounds intermediate sums in the specified sparse Tick.
It is valid with changing adjacency because the same degree bound holds
at every material stage.

The work counts follow by applying Proposition 15.2's chosen Tick on
both current corresponding graphs, and by the literal $P/S$ templates.
The observer's finite records and indices are maintained at their current
sizes, not by a code-size bound. For a direct witness to arbitrary operand
width at a fixed source, after Reset a single Add$(j,2^m)$ and Read$(j)$
require a numerator with $m+1$ bits, for any finite $m$. This already
precludes a uniform finite numerical-memory or traffic bound for the
full declared menu. Reference and physical-installation prices have no
universal numerical tariff in the assumptions, so their actual costs
remain separate rather than being priced by the scalar-operation count.
$\square$

## 16. Exact suppliers and the remaining mathematical domain

**Definition 16.1 (mathematical correspondence and source-relative content).**
The root rigidity and its actual-action join in §§11–15 are
`repo-derived` consequences for the changed installation of §10. The
following are intermediate suppliers, not claims of new general methods.

| Supplier | Exact use and retained boundary |
| --- | --- |
| This volume, Lemma 2.1, Theorem 2.2 and Lemma 2.3 | Unit adjacency is their special case $T=A_t$ with links one and diagonal zero; the complete ordered terminal set is exactly the actual graph-leaf set since the root is a branch. Their first arrivals and explicit distance-vector tree inverse are reused. They do not themselves mark a concealed original LAB root. |
| This volume, §§4–8 | Same-specimen current synchronization, finite adaptive transport, full-field Reset, Hold and complete-roster calibration are existing disciplines. The present predictor uses known adjacency and an actually changing source; the persistent embeddings and roster updates of Theorem 12.1 supply the additional bridge. The weighted coefficient acquisition and its second trial family are not claimed or charged anew. |
| AA Definitions 17.1 and 17.3, Theorem 17.2, Definition 20.2 and Proposition 22.1 | Reachable terms are exactly $\mathcal D$; $C(t)$ has literal unary markers; $P/S$ have their original guarded meanings and persistent templates. AA already recovers causal order from rooted source syntax and counts its construction. Here syntax and the root are initially concealed and have to be earned from scalar ordered-terminal waves. |
| AA §§18–23 | The exact old-word fibres, actual routing records, original FetchGrowth/Next, task distinctions and serial limitations remain valid. Those serial ports and records are not supplied by the present onset inverse. Theorem 14.3 explicitly preserves their obstruction, including conditioning on a complete split word. |
| FARG §§2–3 | Ordered free syntax and the recursive simultaneous $\rho$ are reused exactly. Proposition 12.3 proves a pass on the acquired current old leaf antichain by actual original local actions; it supplies no inverse global epoch or universal reduction to two generators. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean` and its owning [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `sourceControl`, `initialControl`, `native_source_producer` and private `traverse`, `production_reads`, `stationary` already provide stationary whole-tree acquisition by literal Native address readings with one paid read per actual logical node. Those readings expose constructors directly. They are not assumed available here or implemented by an unproved scalar-to-Tag port. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean` and its owning [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) | `term_at_prim`, `readout_prim`, `substitution_prim` and private `treeView`, `child`, `walkStep`, `walk_exact`, `rootReply`, `readout_walk` supply exact finite navigation, readout and substitution meaning on an already given finite source code. The present original-guard conclusion is applied only after the wave-to-root bridge, with separately retained actual rights. |
| `D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean` and its owning [Scribe](../../../Blueprint/D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.scribe.cs) | Its `Enabled`, `Exec`, `ExtensionList`, `LegalSwap` and `result` concern finite-poset enabled paths and legal adjacent swaps. Use the finite event type $E(t)$ with cuts $\varnothing,E(t)$, as already identified with actual LAB by AA Theorem 17.2. A possible linear extension is not the observed original total chronology. |

The material-tree recovery supplier has a precise literature boundary.
Ilmavirta, Lassas, Lu, Oksanen and Ylinen,
[*Quantum computing algorithms for inverse problems on graphs and an
NP-complete inverse problem*, arXiv:2306.05253v2](https://arxiv.org/html/2306.05253v2),
Theorem 1 and §5.1, compare a complete-leaf tree with connected simple
graphs in $\mathcal G(n,m)$ having the same fixed order $n$ and boundary
size $m$. They expressly credit the classical tree-metric theorem when
the competitor is also known to be a tree. The present tree-only,
unknown-order use is the explicit integer-subdivision construction of
Lemma 2.3. It does not remove fixed $n$ from their stronger all-graph
comparison. Neither their theorem nor the classical tree-metric inverse
identifies an unmarked original LAB root with its birth-typed ordered
syntax and original action semantics. Those extra conclusions are the
content of Theorems 11.1 and 12.1, with load-bearing failures in §14.

The source-relative addition, after subtracting these suppliers, is the
unique original-root inverse for the ordered birth-typed unary-marker
presentation, joined to paid acquisition on its one actual field and the
persistent-vertex original-action correspondence. The four views use the
causal birth order and zero-field domain expressly, and the same-run
charges include preparation and arbitrary later operands. This describes
which conclusion is added to these suppliers, without claiming worldwide
priority for tree metrics, linear prediction, causal orders or finite
adaptive induction.

**Theorem 16.2 (bounded common-source outcome and precise residual scope).**
On the installation of §10, the complete linear terminal order and LAB
birth typing suffice for paid acquisition of its concealed original root
and syntax. The acquired record predicts every finite adaptive continuation
of the entire declared field-and-original-$P/S$ menu, preserving complete
physical field correspondence, retaining every old value during growth,
and assigning the declared fresh zeros. The complete roster, original
guards, entire replies and settled successors also correspond. At settled
zero-field cuts Space, causal Time, Boundary onsets and retained Memory
recover one another with route and dynamics agreement. The resources of
§15 are attained on that same preparation, acquisition and use.

The statement assumes this changed field installation and its authentic
roster, rights and calibration; it proves neither physical installation
nor those assumptions from waves. It supplies no old serial journal,
all-phase inverse, inverse at unknown nonzero fields from Time alone,
sharp total-cost optimum, noisy recovery theorem, or boundary rigidity
against arbitrary unknown-order graphs. Original fixed-$G_{\rm gc}$,
original-$Q$, parked-consumer, unchanged-initialization, terminal and
final-no-Ready obligations keep their original scopes. A current $\rho$
pass is the finite original-action macro of Proposition 12.3, not a
resolution of an original fixed global-substitution acquisition problem.
The general common-process four-expression and parsimony objective remains
beyond this source-specific zero-field recovery domain.

Proof. Theorem 11.2 earns the finite unrooted material tree on the actual
source, and Theorem 11.1 recovers its unique original root and syntax.
Definition 11.3 synchronizes the actual current field and, when desired,
pays to reach zero. Theorem 12.1 establishes the full one-step physical
and logical correspondence, and Theorem 12.2 proves every finite common
adaptive continuation. Theorem 13.2 gives the four mutual inverses and
commutation on their joint image; Proposition 13.3 states their exact
kernel and field-domain boundary. Theorems 14.1–14.3 prove the stated
order, birth-typing and serial limitations. Propositions 15.2–15.4 charge
that same run and continued widths. Every positive conclusion thus has
the same actual source realization; none combines independently chosen
marginal implementations. The remaining boundaries are absent hypotheses
or the proved noninjectivities above, not claims that those larger
problems are impossible. $\square$

## 追加锚（本行以下为增补区）

## 17. A sparse terminal assay on the unchanged ordered installation

**Definition 17.1 (stationary source and selected onsets).** Keep exactly
Definition 10.1 and Assumption 10.2, including their actual preparation,
complete ordered roster, original addressed growth semantics, field lift,
rights, serialization and complete replies. During the assay issue no
growth. Write $A=A_t$, $N=|V(C(t))|$, and let
$\ell_1,\ldots,\ell_L$ be its actual terminals, $L\ge3$. Define the
following boundary quantities by their travel-time meaning:

$$
\begin{aligned}
a_j&=d(\ell_1,\ell_j) &&(2\le j\le L),\\
c_i&=d(\ell_i,\ell_{i+1}) &&(2\le i<L),\\
\sigma(t)&=((a_j)_{j=2}^L,(c_i)_{i=2}^{L-1}).
\end{aligned}
\tag{17.1}
$$

Each distance means the first nonzero terminal response to a unit input
after an actual full Reset. There are $2L-3$ selected onsets. This is a
selection of localized propagation observations; it contains no internal
address, original root, constructor tag, coefficient table or field vector.
The known unit-adjacency rule, rather than an unknown weighted law, is
essential to the construction below.

**Definition 17.2 (the actual sparse assay).** First perform Reset and
Add$(1,1)$, then Hold. Maintain a list of pending terminals
$2,\ldots,L$. At every positive epoch issue Tick, Hold, and one Read
for each still-pending terminal. Delete a terminal from this list when
its reply first becomes nonzero, retaining that epoch. End the trial
when the list is empty. Next, for each $i=2,\ldots,L-1$ in that order,
perform Reset, Add$(i,1)$ and Hold, then repeat Tick, Hold, Read$(i+1)$
until its first nonzero reply. Finally perform Reset and Hold.

All these calls act on the one unchanged specimen. There is no epoch-zero
Read: each sampled terminal differs from its trial's input terminal, so
the actual Reset and Add already specify that zero. The pending list,
trial index, epoch counter, received words and deletion work have retained
finite backing. The next operation depends only on these records and
received replies; no unknown size or distance is a stopping input.

**Theorem 17.3 (earned sparse geometry and direct native reconstruction).**
For every source of Definition 17.1, Definition 17.2 terminates and
physically acquires $\sigma(t)$. Each scalar it reads is either zero or
the first-arrival value one. From these acquired data one can construct
the entire unit material tree, including every degree-two vertex, and
then its original rooted ordered logical term. The final actual field
is zero. The full-menu predictor of Theorem 12.2 can therefore be
installed at that actual cut without a coefficient-learning trial.

Proof. Lemma 2.1, with all edges one and diagonal zero, says precisely
that the first response from one distinct terminal to another is at its
distance and equals one. Each target in Definition 17.2 is read at
every positive epoch up to that first response and never afterwards in
that trial. Finiteness of the actual connected tree proves termination.
This also proves the assertion about every returned scalar, including
the zero replies used to decide when to continue.

Here is an explicit inverse to the acquired geometry. Temporarily root
the actual unrooted tree at $\ell_1$. For every oriented edge, its
component away from $\ell_1$ contains an interval of the terminal list
$\ell_2,\ldots,\ell_L$. To see this, in the original ordered presentation
one side of every edge is a descendant subtree and hence a terminal
interval. If that interval contains the first terminal, it is a prefix
of the full list and its complement is a suffix. Otherwise the interval
itself is the component away from $\ell_1$.

For $2\le i<L$ put

$$
h_i=\frac{a_i+a_{i+1}-c_i}{2}.
\tag{17.2}
$$

The unique-path identity makes $h_i$ the integer depth, from $\ell_1$,
of the intersection endpoint of the paths to $\ell_i,\ell_{i+1}$.
For any $2\le i<j\le L$, their corresponding depth is

$$
g(i,j)=\min_{i\le r<j}h_r,\qquad
d(\ell_i,\ell_j)=a_i+a_j-2g(i,j).
\tag{17.3}
$$

Indeed, if the endpoint paths have common prefix to depth $q$, the
interval property says that every intervening terminal has that prefix.
Thus all their adjacent intersection depths are at least $q$. At their
last common vertex the paths to the two endpoints enter different child
components. The ordered intervening list must cross between such
components at some adjacent pair, whose intersection depth is exactly
$q$. This proves both inequalities in (17.3); no equal leaf-depth or
ultrametric premise has been used.

One need not materialize the complete distance table in (17.3). Make a
unit path of length $a_2$ from a vertex labelled $\ell_1$ to one labelled
$\ell_2$. For each $j=3,\ldots,L$, climb from the preceding terminal
$\ell_{j-1}$ toward $\ell_1$ to depth $h_{j-1}$, and attach a new unit
path of length $a_j-h_{j-1}$ ending at $\ell_j$. Inductively the existing
tree is the union of the actual paths from $\ell_1$ to the first $j-1$
terminals. The deepest meeting of the new actual path with this union
has depth

$$
\max_{2\le i<j}g(i,j)=h_{j-1},
\tag{17.4}
$$

because each minimum in (17.3) is at most its last entry $h_{j-1}$,
with equality for $i=j-1$. Intersections of paths in a tree are
prefixes, so this is the whole overlap, not just one shared vertex.
The construction therefore extends the actual path union exactly.
Every edge separates two nonempty terminal sets and lies on a path
between leaves. Complete terminal coverage makes the final union the
whole actual tree. Creating unit edges, rather than a single weighted
edge per attachment, retains every subdivision.

Apply the existing original-root and syntax inverse of Theorem 11.1.
For an economical implementation of that supplied inverse, every
nonroot degree-two vertex is a $\beta$ root adjacent to its terminal
marker. A degree-two vertex with no terminal neighbor, if present, is
therefore the original root. If none is present, the actual root has
a terminal child. Birth typing forbids a left $\alpha$ child; this is
its right $\alpha$ child and hence the last terminal. Its neighbor is
the root. Orient the tree there, order the two child components by
their smallest terminal ordinal, and parse unary markers and branches.
These are consequences of the same birth-typed rigidity, not a new
root assumption.

The adjacency matrix is now the unit-adjacency matrix of the earned graph.
The last actual Reset made every field coordinate zero; Hold protects
the decoding interval. The recovered term, zero vector, terminal table
and retained original binding establish (12.1). Theorem 12.2 applies to
the entire original menu, including growth, refusals, arbitrary rational
inputs and malformed complete frames, with its existing persistent
coordinates and actual rights. $\square$

The interval principle used inside this proof is classical ordered-tree
mathematics. For example Lambert and Popovic,
[*The coalescent point process of branching trees*,
arXiv:1101.2241v3, §§1 and 2.1](https://arxiv.org/html/1101.2241v3),
DOI 10.1214/11-AAP820, encode the common ancestry of a planar current
generation by consecutive coalescence times, taking the maximum between
the endpoints. Here the depths are measured forward from $\ell_1$,
giving the minimum in (17.3), and leaf depths need not agree. This is
credited intermediate interval geometry. The additional assertion of
Theorem 17.3 is its physically acquired sparse realization on the
declared LAB service and its original-action entrance, rather than a
claim of a new general genealogy encoding.

**Theorem 17.4 (sparse zero-field expressions and their task).** Replace
only the onset-table component of Boundary in Definition 13.1 by
$\sigma(t)$ and the present terminal zeros. On the actual zero-field
image of the assay, Space, causal Time, this sparse Boundary and
retained Memory determine one another as data. They have exactly the
continuation kernel of the complete menu in Assumption 10.2, with
binding and rights fixed. Every recovery route agrees.

Proof. Their independent meanings remain respectively the actual
ordered-terminal material geometry with zero field, the actual labelled
causal order $E(t)$, the selected propagation onsets with zero terminal
field, and the retained constructor/vector/roster record with callable
entry. The domain promises the actual global zero field; terminal zeros
alone do not establish it. Theorem 17.3 recovers the same $t$ from sparse
Boundary that Theorem 13.2 recovers from its full Boundary. Space
computes the selected path lengths. AA Theorem 17.2 and Theorem 13.2
already supply the causal-Time and Memory routes. All these maps
therefore factor through that one $t$ and zero field.

Equal terms give the full continuation correspondence by Theorem 12.2.
Different roster sizes expose different current ranges. For different
terms with the same $L$, Theorem 17.3 implies that some selected onset
differs. The corresponding Reset/Add/Tick/Read experiment, with a
sufficient finite common horizon, distinguishes the two sources.
This proves the reverse implication for the task kernel.

At stationary zero cuts, Tick, Read, Hold, Reset, Add$(j,0)$ and the
declared refusals preserve the acquired onset meanings, and the
existing predictor gives their complete replies and successors.
For zero-preserving growth, the source-semantic value $\sigma(u')$
is computed from the correctly updated term $u'$; the inverse still
commutes with that same successor, by Theorem 13.2. Such computed
values are predictions of a new assay, not a new set of literal
measurements. If Boundary is required to retain physically sampled
current onsets after a topology change, execute Definition 17.2 on
the new source and pay its calls. The original samples remain current
without reacquisition only while the topology is unchanged.
Excursions with nonzero fields use the full predictor; this zero-field
inverse applies again only at an actual zero cut. $\square$

## 18. Attained sparse acquisition resources and a separating family

**Definition 18.1 (charges on one assay).** For the actual tree put

$$
\begin{aligned}
D_1&=\max_{2\le j\le L}a_j,&
C_\Sigma&=\sum_{i=2}^{L-1}c_i,\\
K_\sigma&=D_1+C_\Sigma,&
R_\sigma&=\sum_{j=2}^L a_j+C_\Sigma.
\end{aligned}
\tag{18.1}
$$

These are posterior analysis parameters, not supplied advice. Use
Definition 15.1's literal finite encodings and simultaneous charges:
source material, source and observer fields, pending frames, roster
dispatch, counters, rights, reference words, grants and actual return
all count. An integer operation is charged at its actual operand
width. Outputting a recovered full table or making another copy has
its own work and backing.

**Theorem 18.2 (one simultaneous resource bound and strict schedule
saving).** Including its final actual Reset/Hold, the assay has exactly
the following calls:

$$
\begin{array}{c|ccccc}
 &\mathrm{Reset}&\mathrm{Add}&\mathrm{Tick}&\mathrm{Read}&\mathrm{Hold}\\ \hline
\text{sparse assay}&L&L-1&K_\sigma&R_\sigma&K_\sigma+L .
\end{array}
\tag{18.2}
$$

There are $2K_\sigma+3L-1$ fixed acknowledgements and $R_\sigma$
literal scalar replies. Moreover

$$
a_2+C_\Sigma+a_L=2(N-1),\qquad
K_\sigma\le3(N-1),\qquad
R_\sigma\le(L+1)(N-1).
\tag{18.3}
$$

Let $D_j$ be the actual terminal eccentricities of Theorem 11.2, and
$K_{\rm full}=\sum_jD_j$. On this same source,

$$
K_\sigma\le K_{\rm full}-D_L<K_{\rm full}.
\tag{18.4}
$$

Against Proposition 15.2's full assay through zeroing, the sparse
schedule also uses fewer Reads, Resets, Adds and Holds. These are
comparisons of the specified schedules, not a lower bound on all
admitted acquisition procedures or a comparison of every cost coordinate.

Proof. The anchor trial lasts $D_1$ Ticks. Its pending terminal $j$ is
read exactly $a_j$ times. Each later trial lasts $c_i$ Ticks and has
exactly $c_i$ Reads. There are $L-1$ trials, each with one entrance
Hold and one Hold after each Tick, plus the final Reset/Hold.
This gives (18.2). All calls except Read return acknowledgements;
summing their counts gives the displayed acknowledgement number.

In the cyclic terminal sequence $\ell_1,\ell_2,\ldots,\ell_L,\ell_1$,
each edge cut is crossed exactly twice: the component not containing
$\ell_1$ is one nonempty terminal interval. Summing path lengths counts
each of the $N-1$ edges twice. This proves the equality in (18.3).
Also $D_1\le N-1$, $C_\Sigma\le2(N-1)$, and
$\sum_{j=2}^L a_j\le(L-1)(N-1)$, proving the bounds.

For $2\le i<L$, $c_i\le D_i$. Thus
$D_1+\sum_{i=2}^{L-1}c_i\le\sum_{i=1}^{L-1}D_i$.
Since $D_L>0$, (18.4) follows. Finally
$R_\sigma\le(L-1)D_1+C_\Sigma\le L K_\sigma$, whereas the published
full schedule has $R_{\rm full}=L(K_{\rm full}+L)$ Reads.
Its zero entrance has $L+1$ Resets, $L$ Adds and
$K_{\rm full}+L+1$ Holds. Each comparison is therefore strict.
$\square$

**Theorem 18.3 (source work, direct decoding and coexisting records).**
One attained field realization of this same assay uses

$$
2K_\sigma(N-1)+(L-1)
\quad\text{source additions},\qquad
LN\quad\text{Reset zero writes},\qquad
K_\sigma N\quad\text{Tick-buffer zero writes}.
\tag{18.5}
$$

After receipt of the onsets, the direct decoder in Theorem 17.3 uses
$O(N+L)$ indexed edge and tree-record operations, in addition to
framing, allocation, integer arithmetic at actual widths and source
dispatch. It needs no $L$ by $L$ distance table. A simultaneous attained
layout retains $O(L\log(N+1))$ onset bits and $O(N\log(N+1))$ numerical
tree/index bits, with the following additional coexisting stores:
the actual source links and their reference words; two source field
buffers; pending terminals and counters; the decoding path and tree
records; the retained predictor and its current zero vector; actual
input/output and work backing; and the program, authentic callable
entry, authority and service installation.

During acquisition each source field coordinate can require
$O(N+1)$ bits, despite every sampled scalar being zero or one.
Thus two source buffers have an attained $O(N(N+1))$ numerical-bit
bound. This does not price references or installation backing by
numerical index length.

Proof. Use Proposition 15.2's direct adjacency update, clearing $N$
output cells and adding $2(N-1)$ directed-edge contributions per Tick.
Each actual Add contributes one further source addition and each
Reset writes every current cell. Formula (18.2) gives (18.5).

In direct path gluing, exactly $N-1$ new unit edges are made.
The initial descent and subsequent climbs and descents have total
length $a_2+C_\Sigma=2(N-1)-a_L$, by (18.3).
A stack of the current root path supplies the attachment point by
popping to the specified depth. Each retained vertex and edge is
created once. A scan finds the root by the recognizer in Theorem 17.3;
one traversal orients the tree and computes minimum descendant
terminal ordinals, and another parses its constructors. All have
the claimed indexed-operation count. Parent links let the code retain
original addresses structurally; explicitly copying all address words
instead has its additional total address length. Pending-list scans
and deletions can use $O(R_\sigma+L)$ indexed operations, because a
removed terminal is never scanned again in that trial.

Every trial stops by $N-1$ Ticks, and the maximum material degree is
three. Its nonnegative integer fields obey
$\|A^r e_{\ell_i}\|_\infty\le3^r$, so their widths are $O(N+1)$.
Distances, vertex indices and counters have $O(\log(N+1))$ bits.
The retained onset list and an indexed tree therefore have the stated
numerical sizes. A separate raw sequence of all zero/one samples,
if retained, costs $R_\sigma$ payload bits plus its actual frames;
it is not required by this layout. Discarding a consumed raw word
does not remove the work and traffic of its actual receipt. Likewise
the final predictor's zero vector does not remove the simultaneous
source buffers or its retained code, bindings and workspace.
Proposition 15.4 continues to charge arbitrary later operands and
growth. $\square$

**Theorem 18.4 (an admissible family with an asymptotic attained saving).**
Define $u_0=\beta$ and $u_{m+1}=\langle u_m,\beta\rangle$.
For every integer $m\ge2$, $u_m$ is a reachable LAB term with

$$
L=m+1,\qquad N=3m+2,\qquad
a_j=j+2\ (2\le j\le L),\qquad c_i=5\ (2\le i<L).
\tag{18.6}
$$

The sparse assay on this very source uses

$$
K_\sigma=6m-2,\qquad
R_\sigma=\frac{m^2+17m-10}{2}.
\tag{18.7}
$$

The published full schedule uses $\Theta(m^2)$ Ticks and
$\Theta(m^3)$ Reads, whereas this assay uses $\Theta(m)$ Ticks
and $\Theta(m^2)$ Reads. With the same direct field update, source
adjacency additions decrease from $\Theta(m^3)$ to $\Theta(m^2)$.

Proof. All logical leaves are $\beta$, so the birth condition holds;
AA Theorem 17.2 makes these actual admissible preparations. There
are $m$ branches and $m+1$ marker-bearing leaves, giving the displayed
orders. The two deepest logical leaves form the bottom pair; their
markers are the first two terminals.
The first terminal is at depth $m+1$ from the original root; terminal
$j\ge2$ is at depth $m-j+3$. Their common-path lengths give
$d(\ell_1,\ell_j)=j+2$. Consecutive terminals after the first have
distance five. Hence $D_1=m+3$ and $C_\Sigma=5(m-1)$.
Summing $j+2$ for $2\le j\le m+1$ proves (18.7).

The diameter is $m+3$. Every vertex has eccentricity at least half
the diameter, by the triangle inequality at two diameter endpoints.
Consequently

$$
\frac{(m+1)(m+3)}2\le K_{\rm full}\le(m+1)(m+3).
\tag{18.8}
$$

The exact full Read formula then gives its cubic order. Multiplying
the Tick orders by $2(N-1)$ proves the adjacency-addition comparison.
All trials, source sizes and field updates in these comparisons
belong to the same $u_m$. Merely deleting post-arrival Reads from
every published trial still pays its full $K_{\rm full}$ propagation;
that modification does not attain (18.7)'s Tick count. $\square$

## 19. An actually prepared nonzero passive phase

**Assumption 19.1 (the new origin on the acquired source).** Keep the
same installed tree and acquired law, roster and actual binding.
Execute a real Reset followed by Add$(1,1)$, or use the actual final
Reset of Definition 17.2 followed by that Add. Name the completed
Add the origin $o$. From $o$ to the cuts under consideration there
is no growth, Reset or nonzero Add, and the only field evolution is
the actually requested Tick. Reads and Holds may occur without
changing the field. The source remains the same $C(t)$.

The actual preparation and passive-phase assurance are conditions,
not conclusions of the scalar samples. In particular the late
observer need not have an accessible Tick count or synchronized
vector after an intervening passive prefix. That prefix consists
of finitely many ordinary paid Tick calls with their acknowledgements,
finite input/control backing and actual work. It is not a new
clock port, supplied age, arbitrary unknown initial field or
unreceived sequence of replies. Every choice of a finite prefix
is within the quantifier.

**Definition 19.2 (age, literal samples and the prepared image).**
Put $e=e_{\ell_1}$ and, for integers $r,k\ge0$, write

$$
x_k=A^k e,\qquad m_r=e^{\mathsf T}A^r e,\qquad
s_n=m_{2n},\qquad
p_k=(m_{k-1},m_k)\quad(k\ge1).
\tag{19.1}
$$

Age $k$ is the length of the actual Tick chain since $o$; it
does not count old growth events, Reads, Holds, input/output work
or physical duration. A sampled cut of age $k$ additionally has
two actually received Read$(1)$ values at consecutive passive
epochs $k-1,k$, with no Tick after the second. They have the
numerical content $p_k$. Arbitrary repeated Reads at one epoch
do not supply this pair. The sampled recovery domain in §§19–22
has $k\ge2$.

**Theorem 19.3 (native passive age from two consecutive samples or the
full present field).** On every source of Assumption 19.1,

$$
m_{2n+1}=0,\qquad s_0=s_1=1,\qquad
s_{n+1}>s_n\quad(n\ge1).
\tag{19.2}
$$

The map $k\mapsto p_k$ is injective for all integer ages $k\ge2$.
With the earned $A$, its inverse terminates on its promised actual
image. The full current field $x_k$ also effectively determines
$k$ on this domain. No invertibility of $A$ and no cyclicity of
the single terminal $e$ is required. The trailing-pair threshold
cannot be extended to all positive ages, since $p_1=p_3=(1,0)$.

Proof. A power entry of unit adjacency counts ordinary walks.
The tree is bipartite, so a closed walk has even length, proving
the first assertion. The terminal $e$ has one neighbor $v$,
so the sole closed length-two walk is $e,v,e$. As $L\ge3$,
$v$ has a neighbor $w\ne e$.

Append the backtrack $e,v,e$ to every closed length-$2n$ walk
at $e$. Deleting its final two edges recovers the old walk, so
this is an injection into the closed walks of length $2n+2$.
For every $n\ge1$ there is the additional walk consisting of
$n-1$ backtracks $e,v,e$, followed by $e,v,w,v,e$.
Its last three vertices are $w,v,e$, so it is outside that
injection, whose walks end $e,v,e$. This proves strict increase
in (19.2), including the initial comparison $s_2>s_1$.

For $n\ge1$ the pair at age $2n$ is $(0,s_n)$ and the pair at
age $2n+1$ is $(s_n,0)$. The location of the positive entry fixes
the parity, and strict increase of $(s_n)_{n\ge1}$ fixes $n$.
Enumerating integer powers of the already acquired $A$ therefore
finds the unique pair on the declared image after finitely many
steps. There is no termination claim for arbitrary off-image
input pairs, and no bound in $N$ alone.

From the full present field compute locally

$$
(e^{\mathsf T}x_k,e^{\mathsf T}A x_k)
=(m_k,m_{k+1})=p_{k+1}.
\tag{19.3}
$$

The same inverse yields $k+1$ and hence $k$. The second entry
is computed from the current field at $v$; this is not a source
Tick or a claimed future measurement. Finally $m_0=m_2=1$ and
$m_1=m_3=0$, giving the stated early collision. $\square$

The walk interpretation used in this proof is the standard one.
At the pinned mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679,
[SimpleGraph.adjMatrix_pow_apply_eq_card_walk](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean)
states it for finite vertex sets over a semiring. Here use the actual
finite material graph and rational or natural unit adjacency.
[IsTree.existsUnique_path](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean)
supplies the corresponding unique-path substrate. These are
intermediate suppliers, not installed sampling or age-acquisition
procedures.

## 20. The exact condition for instantaneous terminal recovery

**Definition 20.1 (instantaneous terminal frame).** At passive age $k$
let

$$
y_k=\bigl((A^k e)_{\ell_j}\bigr)_{j=1}^L.
\tag{20.1}
$$

It exposes only the simultaneous present terminal field and the
already earned $\sigma(t)$. A literal acquisition of the frame
means Hold and $L$ individual Reads before the next Tick.
The finite tuple is not a newly installed vector-Read primitive.
Its comparison with a two-epoch record concerns the present
field observation, with the prepared-phase premise held fixed.

**Theorem 20.2 (terminal-parity criterion on the whole tail).** For
each acquired tree, with $D_1$ as in (18.1), the map

$$
k\longmapsto y_k,\qquad k\in\mathbb Z,\quad k\ge D_1,
\tag{20.2}
$$

is injective if and only if the terminal set meets both
bipartition classes of $C(t)$, equivalently some terminal
has odd distance from $\ell_1$. Under this condition its
inverse is effective on its actual image. If the condition
fails, infinitely many distinct ages on this tail have the
identical zero terminal frame although their full fields
are distinct. This is an instantaneous-frame obstruction,
not an obstruction to the two-read protocol or to future
boundary experiments.

Proof. Since $\ell_1$ is itself a terminal, failure of the
condition says that every terminal is at even distance from
$e$. At every odd age all terminal entries then vanish by
bipartiteness. There are infinitely many such ages beyond
$D_1$, and their full fields are distinct by (19.3) and
Theorem 19.3.

For sufficiency choose a terminal $f$ at odd distance $d$
from $e$. Distinct leaves cannot be adjacent in this tree,
so $d\ge3$. Let $v_f$ be the neighbor of $f$ on their path,
and $w_f$ its preceding vertex toward $e$. For $r\ge0$ put

$$
b_r=(A^{d+2r})_{f,e}.
\tag{20.3}
$$

There is one shortest path, so $b_0=1$. Appending
$f,v_f,f$ injects the length-$d+2r$ walks from $e$ to $f$
into those of length $d+2r+2$. A further walk consists of
$r$ initial backtracks $e,v,e$, then the shortest path
from $e$ to $v_f$, then $v_f,w_f,v_f,f$.
Its total length is $2r+(d-1)+3=d+2r+2$.
Its final three vertices are $w_f,v_f,f$, not $f,v_f,f$;
thus it is outside the injection. Consequently
$b_{r+1}>b_r$ for every $r\ge0$.

The anchor coordinate of $y_k$ is positive at even ages
and zero at odd ages. At even $k\ge D_1\ge2$ it is
$s_{k/2}$ and distinguishes even ages by (19.2).
At odd $k\ge D_1\ge d$ the $f$ coordinate is the positive
strictly increasing value $b_{(k-d)/2}$ and distinguishes
odd ages. The anchor separates the two parities.
These facts prove injectivity. Enumerating $A^k e$
from $e$ and comparing the terminal frames for
$k\ge D_1$ gives the asserted inverse. The true finite
age is reached; off-image recognition is not asserted.
$\square$

**Theorem 20.3 (both terminal-parity cases occur on actual LAB).**
There are reachable ordered LAB sources with $L=3$ satisfying
each alternative in Theorem 20.2. The trees

$$
t_-=\langle\langle\beta,\beta\rangle,\alpha\rangle,
\qquad
t_+=\langle\beta,\langle\beta,\alpha\rangle\rangle
\tag{20.4}
$$

have, respectively, material terminal depths $(3,3,1)$
and $(2,3,2)$ from their original roots.

Proof. Both terms obey the condition that no logical
$L$-ending leaf is $\alpha$, so AA Theorem 17.2 supplies
actual legal preparations from the original seed.
A $\beta$ contributes its terminal marker one edge
beyond its logical depth; an $\alpha$ is already terminal.
This gives the displayed depths. The parity of the distance
between two vertices in a rooted tree is the parity of
the sum of their depths. Thus all terminals of $t_-$
lie in one bipartition class, while those of $t_+$
meet both. $\square$

## 追加锚（本行以下为增补区）

## 21. Independent expressions on the sampled nonzero image

**Definition 21.1 (four prepared-phase observations).** Fix the actual
installation, source binding, current rights and authentic origin of
Assumption 19.1. Let $\mathcal P_2$ be its settled sampled cuts of
Definition 19.2 with $k\ge2$, unchanged topology, valid acquired
$\sigma(t)$ and a synchronized retained predictor. Define the
following observations by what they expose:

| Expression | Independent exposed content on $\mathcal P_2$ |
| --- | --- |
| Space $\mathsf S$ | The actual unrooted unit material tree with its linearly ordered terminals, and the full present field, modulo terminal-order-preserving isomorphism |
| Time $\mathsf T$ | The actual labelled LAB birth/lifecycle order $E(t)$, followed by the order type of the actual $k$-Tick chain from the named origin |
| Boundary $\mathsf B$ | The earned selected terminal onsets $\sigma(t)$ and the two literal consecutive terminal-$1$ samples ending at the present cut |
| Memory $\mathsf M$ | The actually retained recursive term, current full predictive vector and current ordinal terminal table, on the bound callable entry with its rights |

The Tick chain in Time consists of the field updates since $o$, not
an old successful-growth word or a list of all controller events.
It may be represented by its finite chain order type; a fully
materialized event list has separate backing. Boundary has no age
label or full vector. Space has a present spatial distribution,
and Memory has a local transition representation rather than an
old command archive or a table of all possible future answers.
The sampled domain promises genuine consecutive measurements:
the two scalars are not defined by a chosen inverse.

The binding, installed law, authentic phase assurance and rights
are common conditions of these observations. They are not
recovered permissions or source references hidden in numerical
data. Mathematical conversion preserves these already fixed
conditions; it does not grant another service entry.

**Theorem 21.2 (mutual recovery and agreement on the actual sampled
domain).** Each observation in Definition 21.1 determines precisely
the same $(t,k,x_k)$ as data. Each determines the other three
observations on their joint image, and every route agrees.
These assertions include every admitted $t$, every authentic
old LAB preparation ending at it, and every finite passive
prefix with $k\ge2$ satisfying the sampling conditions.

Proof. From Space, Theorem 11.1 gives the original term and its
terminal coordinates; the full field supplies (19.3). Theorem 19.3
then gives the unique age. From Time, AA Theorem 17.2 recovers
the same term from $E(t)$, and the length of its actual Tick chain
gives $k$. Its field is computed as $A_t^k e$ by the authentic
preparation and passivity. This does not reconstruct a linear
extension of $E(t)$.

Boundary recovers $t$ by Theorem 17.3. Its literal trailing
pair is $p_k$, so Theorem 19.3 gives $k$ and then $A_t^k e$.
Memory already has $t$ and the actual present vector under
(12.1). Computing its forward pair (19.3) yields the same $k$,
without requiring any retained counter. Thus no view obtains
age from an unrestricted copy of a journal.

The recovered triple computes its present geometry and vector,
its causal order and finite Tick-chain order type, its selected
distances and pair of scalar values, and its finite predictive
record. On the specified joint image these are the original
data of each view, since preparation, passivity and actual
sampling are conditions of that image. If $V_i$ denotes one
of these observations and $D_i$ its recovery of the triple,
then $D_iV_i$ is the identity there. Every conversion has the
form $V_jD_i$, so composing it through another view gives
the same $V_lD_i$. This proves agreement for all routes.

Regenerating a pair of equal numbers is data recovery. It
does not execute two new Reads or restore lost raw measurement
provenance, and computing a chain of length $k$ does not
construct the old physical events again. The paid sampling
and synchronization that make this image nonempty are given
by §22 and the same-source concatenation in §23. $\square$

**Theorem 21.3 (continuation kernel and actual sampled dynamics).**
With the common binding and rights fixed, equality of any one
of the four observations on $\mathcal P_2$ has exactly the
continuation kernel of Assumption 10.2. At a sampled passive
cut, the actual macro

$$
\mathrm{Tick};\ \mathrm{Read}(1);\ \mathrm{Hold}
\tag{21.1}
$$

advances all four expressions compatibly. Its complete replies
are the Tick acknowledgement, the literal $m_{k+1}$, and the
Hold acknowledgement. It retains the trailing pair
$(m_k,m_{k+1})$ at the actual successor of age $k+1$.
The inherited full predictor remains correct for arbitrary
finite adaptive continuations outside this passive domain.

Proof. Equal recovered triples yield equal complete replies
and corresponding successors for every such continuation by
Theorem 12.2. Conversely, differing terms are distinguished
after a Reset by a finite selected-onset experiment, as in
Theorem 17.4. If the term is the same and $k\ne l$ with
$k,l\ge2$, the forward pairs
$(m_k,m_{k+1})$ and $(m_l,m_{l+1})$ differ by Theorem 19.3.
Read$(1)$, Tick, Read$(1)$ therefore distinguish the sources
within this complete menu: either the first replies differ,
or the second ones do. Thus task-equivalent cuts have the
same term and age. This proves the kernel statement without
equating a semantic field with an exposed direct internal
read port.

In (21.1), Tick sends the actual field to $Ax_k=x_{k+1}$.
Time gains one actual Tick in its post-origin chain and its
birth/lifecycle order stays fixed. The new Read is made at
that actual next epoch, so Boundary shifts its existing last
sample into the first slot and uses this new scalar in its
second slot. Memory performs the adjacency update of
Theorem 12.1 before exposing the settled matching cut.
All four successors consequently recover
$(t,k+1,A^{k+1}e)$ by Theorem 21.2. Hold protects the
subsequent finite local work.

Read, Hold and Add$(j,0)$ alone preserve the age and field.
Refusals with identity effect also preserve them. A nonzero
Add, Reset or successful growth breaks Assumption 19.1's
declared phase since $o$; the sampled inverse is not asserted
after it. The complete field and original-action invariant
of Theorem 12.2 still holds and continues to predict those
operations, including the persistent old values and fresh
zeros under growth. A forecast scalar alone does not perform
the Read in (21.1); without that Read the numerical state may
be predicted, but a new literal Boundary sample has not
been acquired. $\square$

## 22. Paid late synchronization at the true advanced cut

**Theorem 22.1 (two actual Reads, one actual Tick and synchronized
retained use).** Suppose the tree, law and valid selected onsets
have been acquired, and the actual source is at an unknown
authentic passive age $k\ge2$ of Assumption 19.1. No accessible
age counter, old passive transcript or current vector is an
input. The serial protocol

$$
\mathrm{Read}(1);\ \mathrm{Tick};\ \mathrm{Read}(1);\
\mathrm{Hold}
\tag{22.1}
$$

uses exactly two scalar Reads, one Tick and one Hold. It
recovers the actual advanced age $h=k+1$ and installs the
full predictor with the true field $A^h e$ at that advanced
cut. It also acquires the literal trailing pair $p_h$.
The entire finite future-menu conclusion of Theorem 12.2
then holds from this synchronized cut.

Proof. The complete received word consists of $m_k$, the
Tick acknowledgement, $m_{k+1}$ and the Hold acknowledgement.
Tick is acknowledgement-only in this installation; its
unreturned scalar cannot substitute for the second Read.
The pair of received scalars is
$(m_k,m_{k+1})=p_h$. Theorem 19.3 identifies $h$ uniquely
on $h\ge2$, and the actual $h=k+1\ge3$ belongs to that image.

For a direct decoder, start a local vector at $e$ and
successively apply the earned sparse unit adjacency.
At local candidate age $r\ge2$, compare the terminal-$1$
coordinates of the preceding and current candidates
with the actual received pair. The true finite candidate
$r=h$ is reached, and uniqueness makes it the sole match.
The current candidate vector at that match is already
$A^h e$, so no inverse of $A$, hypothetical source reset,
second source or response-table oracle is used.

Hold protects the actual source while this finite calculation
completes. Store the vector in the earned persistent
coordinates and retain the same current ordinal table,
service reference and original authority. This establishes
(12.1) at the actual final cut. Theorems 12.1–12.2 supply
all complete replies, guards, lawful source calls, field
updates and successors thereafter. In particular installing
$A^k e$ instead would describe the earlier cut and would
not be the synchronized installation claimed here.
$\square$

**Theorem 22.2 (instantaneous-frame alternative and its exact
domain).** If the earned tree meets both terminal bipartition
classes and the actual unknown passive age satisfies
$k\ge D_1$, then Hold followed by all $L$ terminal Reads
synchronizes at that same age, with no source Tick.
On the actual frame-sampled domain, replacing Boundary
in Definition 21.1 by $(\sigma(t),y_k)$ gives the same
mutual recovery, route agreement and continuation kernel.
Its sampled successor is Tick, Hold and all $L$ Reads.
Without the bipartition condition the instantaneous
frame alone has no age inverse on the whole tail.

Proof. Hold and the $L$ nonchanging Reads acquire exactly
(20.1) at one actual epoch. Theorem 20.2 recovers the unique
age by enumeration of the acquired law, with current vector
$A^k e$. Store it under the same correspondence to obtain
the full predictor invariant. The other three view inverses
in Theorem 21.2 do not depend on how Boundary samples were
chosen. The new Boundary inverse instead uses Theorem 20.2;
all still factor through the same triple. The kernel proof
in Theorem 21.3 applies unchanged to that triple. The
displayed successor actually samples the complete new
frame at age $k+1\ge D_1$, so the same argument proves
dynamics compatibility. The infinite zero-frame fibre
of Theorem 20.2 proves necessity on the entire tail.
It does not prevent advancing to acquire another epoch
or using the two-sample construction. $\square$

**Theorem 22.3 (a smaller phase-only procedure does not acquire a
missing pair).** Under Theorem 22.1's premises, if only the
current passive age and synchronized vector are requested,
one can stop after Read$(1)$ and Hold whenever the first
scalar is positive. If it is zero, one Tick, another
Read$(1)$ and Hold suffice. This does not assert that one
scalar uniformly determines the whole phase image or
provides a literal past/current Boundary record.

Proof. A positive first scalar occurs precisely at even
ages $k=2n$ on this domain. It equals $s_n$ with $n\ge1$,
which strictly increases by Theorem 19.3. Enumeration
therefore recovers $k$ without source advance. A zero
first scalar occurs at odd ages; one Tick reaches the
even age $k+1$, and its actual next Read is positive
and identifies that advanced age by the same argument.
There are infinitely many odd ages with scalar zero,
so one scalar has no uniform inverse. In the positive
branch no sample at the preceding epoch has been
received. Computing its numerical value from the
recovered phase does not make it a literal sampled
pair. $\square$

## 23. One realized sparse-entrance and passive-recovery run

**Definition 23.1 (the concatenation and its resources).** On one
actual source execute the sparse assay of Definition 17.2
through its final Reset/Hold. Apply one Add$(1,1)$ to make
the actual origin $o$. Execute any actual finite prefix of
$k\ge2$ Tick calls, with no intervening evolution or growth,
and then execute (22.1). The late record retains the
acquired tree, onsets, reference and rights; it has no
accessible count or synchronized vector for that prefix
until (22.1) finishes. The former zero-field predictor
can be suspended while the prefix runs and resynchronized
by Theorem 22.1.

The finite prefix is a real producer/input execution with
paid Tick acknowledgements and finite control, dispatch
and request backing. Its count is an analysis variable,
not an age supplied to the late decoder. An archive
retained by any chosen producer is charged separately
and is not a premise of this decoder. This describes
one possible execution, rather than requiring every
continuation to discard an already available counter.

**Theorem 23.2 (simultaneous lifetime calls and source work).**
The exact calls of Definition 23.1, from the beginning of
the sparse assay to the final advanced synchronized cut,
are

$$
\begin{array}{c|ccccc}
 &\mathrm{Reset}&\mathrm{Add}&\mathrm{Tick}&\mathrm{Read}&\mathrm{Hold}\\ \hline
\text{concatenation}&L&L&K_\sigma+k+1&R_\sigma+2&K_\sigma+L+1.
\end{array}
\tag{23.1}
$$

They produce $2K_\sigma+3L+k+2$ fixed acknowledgements
and $R_\sigma+2$ scalar replies. For the direct field
realization in §18 their source costs are

$$
\begin{aligned}
&2(K_\sigma+k+1)(N-1)+L
&&\text{field additions},\\
&LN&&\text{Reset zero writes},\\
&(K_\sigma+k+1)N&&\text{Tick-buffer zero writes}.
\end{aligned}
\tag{23.2}
$$

These counts precede any further continued use. They
add neither a second zeroing nor a preparation from
another separately optimized run.

Proof. Formula (18.2) already includes the actual
zero-producing Reset and Hold. The new origin adds
one Add. The passive prefix adds $k$ actual Ticks,
and (22.1) adds one Tick, two Reads and one Hold.
This gives (23.1). Summing its non-Read columns gives
the acknowledgement count. Apply the same per-Tick,
per-Add and per-Reset implementation as in (18.5)
to these actual totals to obtain (23.2).
No growth occurs between these phases, so their
common $N$, tree, roster and original binding are
unchanged throughout. $\square$

**Theorem 23.3 (actual preparation, local decoding and unbounded
exact widths).** Include in this same run the actual old LAB
preparation of Definition 10.1. If $c$ is its final number
of logical $\beta$ leaves, it has the source counts
$c$ promotions, $L-1$ splits and $N=2L+c-1$ of
Proposition 15.2, with its actual address traversals,
allocation, replies, field initialization and grants.
The sparse and passive phases do not erase these costs.

Writing $h=k+1$ for the final synchronized age, the late
decoder of Theorem 22.1 can use at most $h$ sparse
adjacency iterations, hence $2h(N-1)$ integer additions
and $hN$ local output-buffer zero writes, besides
counter operations, at most $h-1$ pair comparisons,
framing, assignment and work-backing costs.
One attained simultaneous numerical width bound
through the whole concatenation is

$$
W=O(N+h+1)
\tag{23.3}
$$

bits per field or sample integer. Source buffers,
the local candidate buffers and retained predictive
vector, onsets, tree and roster indices, received pair,
counters and pending words coexist with their actual
bindings, authority and communication backing.
There is no uniform finite bound on exact field width
even at a fixed admitted tree.

Proof. The old preparation statement is precisely
Proposition 15.2 applied to this actual source, not
an inferred old serialization. Its initially zero
field and zero insertion at growth remain the same
installed law. Old input/output work, address lengths,
fresh material and backing are actual charges even
when their chronology is unavailable to the entrant.

The late enumeration starts at $e$, retains two
successive candidate vectors and stops at $h$.
Each local iteration is the same unit-adjacency
calculation as a source Tick, with no source call.
Only candidates $r=2,\ldots,h$ need comparison.
The current candidate at the match becomes the
retained predictive vector; separate copies cost
their actual lengths. Since
$\|A^r e\|_\infty\le3^r$, its entries through $h$
have $O(h+1)$ bits. The source fields during the
earlier acquisition have $O(N+1)$ bits by
Theorem 18.3. This proves (23.3). Integer comparison
and addition are charged at these widths, rather
than priced as unit-time arbitrary arithmetic.

The source's two numerical buffers, the two local
candidate buffers and any separately retained
predictor copy have total $O(NW)$ numerical bits.
Sparse onsets use $O(L\log(N+1))$ bits; indexed
tree and roster data use $O(N\log(N+1))$ bits,
plus actual link/reference words; the age counter
uses $O(\log(h+1))$ bits. Pending request/reply
buffers, actual frames, copies, programs and
authority/backing are additional simultaneous
stores. Exporting Time as a list pays for all its
event entries and labels; it is not an obligatory
archive in each other view.

For a fixed-tree witness to growing width, retain
$v,w$ from Theorem 19.3. There are two distinct
four-edge closed walks at $e$:
$e,v,e,v,e$ and $e,v,w,v,e$.
Concatenating any sequence of $r$ such walks gives
$2^r$ distinct closed walks of length $4r$.
Hence $m_{4r}\ge2^r$ and the exact anchor scalar
alone has at least $r+1$ bits along this subsequence.
Finite source order and a finite program therefore
give no fixed lifetime numerical-memory bound.

After synchronization, each further sampled passive
step (21.1) pays one Tick, one Read and one Hold,
the literal scalar and two acknowledgements, and
the retained adjacency update. General future
rational controls or growth have the complete
actual-width and material costs of Proposition
15.4. No uniform later-input, reference-size or
exact-lifetime storage bound follows from (23.3).
$\square$

## 24. Supplier subtraction and the remaining recovery domain

**Definition 24.1 (precise mathematical correspondence).** The
additional conclusions in §§17–23 are repo-derived
source-relative inferences with the following suppliers.
The listed ingredients are used at their original
hypotheses and are not asserted as new generic results.

| Supplier | Correspondence and excluded substitution |
| --- | --- |
| This volume, Lemma 2.1 and §§10–16 | $T=A_t$ has unit positive edges and zero diagonal. First arrival equals unit distance; the original-root/birth-type inverse, persistent field lift, full predictor, zero-domain views and old-history noninjectivity are reused. The additional stationary entrance acquires only the selected $2L-3$ onsets and pays the attained schedule of §18. |
| AA Definitions 17.1 and 17.3, Theorem 17.2 and §§20–23 | The actual source is the same $C(t)$ and its actual old causal order is $E(t)$. The original guarded $P/S$ and their material templates, source counts and serial-word limitations keep their meanings. The new Tick chain is only the authentically prepared field phase, not a replacement chronology for those old events. |
| Lambert–Popovic, arXiv:1101.2241v3, §§1 and 2.1 | Literature-attested adjacent-ancestor information for planar genealogy is an intermediate supplier. The proof in Theorem 17.3 spells out the forward-depth minimum identity and unit subdivisions for these unequal-depth terminals. No stochastic branching or equal-generation premise is imported as an unearned source fact. |
| Ilmavirta et al., arXiv:2306.05253v2, Theorem 1 and §5.1, as delimited in Definition 16.1 | Classical complete-leaf tree-metric recovery is credited. Fixed-order comparison with arbitrary connected graphs is not changed into unknown-order graph rigidity. The sparse assay still assumes the actual source is the declared tree. |
| NativeFullSourceProducer and NativeUniformTree, with the owning Scribes cited in Definition 16.1 | Their stationary literal-address traversal, including private traversal/stationarity helpers, and finite code navigation are supplied results. A scalar terminal onset is not such a literal constructor reply. The bridge here earns the actual code before using original guards or native finite prediction. |
| [NativeAncestorUniqueness](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.scribe.cs) | The complete ordered labelled leaf word and inorder ancestor-area products determine a native full binary tree. Its actual coordinates are products of child leaf counts; they are not the measured travel times or depths in (17.1)–(17.3). Its uniqueness and internal interval arguments do not pay the sparse wave assay or supply its one-run call counts. |
| [Signed Passive Clock, Theorems 2.1, 4.2 and 5.1](RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_PASSIVE_CLOCK.md) | The two-consecutive-output idea, actual-image enumeration and advanced-cut discipline are supplied there for a selfadjoint contraction. That contraction premise fails for the present unit adjacency. Theorems 19.3 and 20.2 supply the walk-growth and exact terminal-parity replacement on this actual law. Its returning Tick also differs from the acknowledgement-only Tick here. |
| [Recovery Geometry II, §§36–41 and 52–58](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md) | Native positive-contraction Jacobi acquisition, actual unit preparation, all-field prediction and the no-retained-length integer pulse-history theorem remain supplied results. The present field has bipartite zero-diagonal unit evolution on LAB; its recovered age is a passive Tick count, not an integer pulse word. |
| Pinned mathlib, SimpleGraph/AdjMatrix and SimpleGraph/Acyclic | The finite walk-count and unique-path identities cited after Theorem 19.3 apply to the actual finite graph. Their elementary algebra does not constitute an operational installation or an acquisition of a missing age record. |

The contraction distinction can be checked without a spectral
inference. At the first terminal and its neighbor $v$,
$Ae=e_v$, and $A^2e=Ae_v$ has one unit entry per neighbor
of $v$. Thus

$$
\|Ae\|^2=1,\qquad \|A^2e\|^2=\deg(v)\ge2,\qquad
\|A\|>1.
\tag{24.1}
$$

Accordingly the strict-contraction phase arguments of P,
or the closed-contraction premise of Signed Passive Clock,
cannot simply be instantiated by $A$. No renormalization
of the actual installed Tick is made here.

The full source/action disciplines of NCR, PVC, PR57,
the callable Atlas and PG retain the correspondence
and limitations described in §§9 and 16. The sparse
entrance improves this volume's own stationary wave
acquisition rather than reauthoring their supplied
acquisition/conversion theorems. The nonzero addition
is recovery of a genuinely prepared passive phase on
this same process, with the exact instantaneous-frame
condition; it does not identify those distinct
installations or their historical tasks.

**Theorem 24.2 (the bounded gain and exact unclaimed extensions).**
On the unchanged ordered LAB field installation, a physically
acquired sparse boundary suffices for native source recovery,
an installed full predictor and the inherited zero-field
four-expression data, with the strict attained schedule
savings of §18. On that same source, an actual unit preparation
admits passive nonzero four-expression recovery at the sampled
ages $k\ge2$. Instantaneous terminal-frame recovery on
$k\ge D_1$ is available exactly under mixed terminal parity.
The sparse-entrance and late-synchronization construction
has the one actual run and costs of §23.

The claimed phase is not an arbitrary field or controlled
history. It supplies neither the old LAB serialization,
unrecorded Read/Hold chronology, an absolute duration,
physical authentication, nor recovery after violating the
phase premise. Complete roster/order, birth typing, exact
unit evolution, Reset/Hold calibration, authentic origin,
source binding, rights and backing remain conditions.
The unchanged original fixed-$G_{\rm gc}$, original-$Q$,
parked-consumer, original-initialization, terminal and
final-no-Ready obligations remain in their original scopes.
There is no global resource optimum, general-graph
rigidity, universal $\alpha/\beta$ reduction or full
common-process four-expression theorem here.

Proof. Theorem 17.3 earns the source from literal sparse
measurements and synchronizes its zero field; Theorem
17.4 identifies its four-view and task domain.
Theorems 18.2–18.4 give the same-source strict saving
and its family witness. Theorems 19.3 and 20.2 prove
the nonzero phase inverse and its exact frame condition,
with actual LAB instances in Theorem 20.3.
Theorems 21.2–21.3 prove agreement and complete
continuation semantics. Theorem 22.1 installs the
predictor at its actual advanced cut; Theorem 22.2
gives the frame alternative. The concatenation and
simultaneous counts in §23 use that very preparation,
source and endpoint.

The early pair collision, infinite zero-frame fibre
and existing §§13–14 field/history noninjectivities
exclude the indicated extensions at their exact
domains. The difference between retained timekeeping
and age recovery is also explicit: an accessible
counter or synchronized vector can be updated
directly, whereas the late theorem recovers age
when that record is not an input. The simpler
phase-only alternative in Theorem 22.3 and the
classical intermediate suppliers are not denied.
Changing a phase, source law, actuator, initialization
or task cannot resolve an older assertion with
different fixed hypotheses. The remaining general
programme is therefore not concluded by these
conditional source-relative results. $\square$

## 追加锚（本行以下为增补区）

## 25. A stationary unit tree with exactly one inaccessible leaf

**Definition 25.1 (the incomplete-boundary installation).** Let $G=(V,E)$
be any finite connected simple tree. Its actual field is $x\in\mathbb Q^V$,
and its installed update $A$ is exactly its zero-diagonal unit adjacency
matrix. An authenticated ordered roster $B=(\ell_1,\ldots,\ell_b)$, with
$b\ge2$, consists of all degree-one vertices except exactly one vertex
$h$. The order labels the accessible ports; it is not a planar order.
Write $J=[e_{\ell_1},\ldots,e_{\ell_b}]$. Neither $G$, $N=|V|$, $h$,
its attachment, a distance bound nor the entry field is receiver advice.

The receiver has the fixed class description and finite controller, this
actual roster and source binding, and the current rights to the following
stationary service. The actual entry field can be arbitrary.

| Request | Actual field successor | Semantic output |
| --- | --- | --- |
| Reset | $0$ on every actual vertex | ACK |
| Add$(j,q)$, $1\le j\le b$, $q\in\mathbb Q$ | $x+q e_{\ell_j}$ | ACK |
| Tick | $Ax$ | ACK |
| Read$(j)$, $1\le j\le b$ | $x$ | the literal rational $x_{\ell_j}$ |
| Hold | $x$, held for finite local work | ACK |

There is no growth, internal field port, hidden-leaf port, coefficient
query, constructor Read, supplied transfer table or physical inverse Tick.
Only a requested Tick evolves the field. Reset zeros the whole actual
field, including the cells not yet described to the receiver. Exact unit
adjacency, the finite-tree promise, exact-one omission, authentic distinct
leaf bindings, full Reset calibration, exclusive serialization and exact
rational arithmetic are installation hypotheses. Observations made under
these hypotheses do not certify an unknown instrument into this class.

**Definition 25.2 (completed calls and their other branches).** Fix a
source-independent finite serialization. A request consists of its kind,
self-delimiting operands and End. A complete syntactically valid Add or
Read with integer index outside $1,\ldots,b$ returns RangeRefusal and has
identity graph and field successor. A complete malformed frame, including
an unsupported request kind or a noncanonical rational encoding, returns
BadFrame and has identity source successor. A proper incomplete prefix
is retained by the parser; it has no completed semantic output and applies
no source operation. Each complete response has its semantic payload and
output End. The holder consumes the entire response, commits its matching
local record, sends one fixed LocalACK and completes one fixed Return
before exposing the next Ready cut. LocalACK is distinct from ACK. These
fixed lifecycle tokens contain no source information. In particular Tick
has no scalar output: a subsequent value requires a separate Read.

Missing or revoked rights, wrong phase and insufficient granted backing
disable execution; they are not RangeRefusal, BadFrame or successful ACK.
A disabled attempted primitive makes no source transition. An interruption
of a partially completed exchange is not a successful acquisition or a
new settled predictive cut. No rollback of a previously executed source
step is asserted. Acquisition starts at a settled Ready cut with an empty
request parser, no unconsumed response and no in-flight mutation. This is
a control-phase premise, not a restriction on the arbitrary entry field
or a procedure for clearing an unknown interrupted exchange.
The runs quantified below supply all finite backing,
current rights, complete delivery and local commits they actually need,
with no intervening writer, autonomous evolution or revocation. A finite
reserve is not assumed to suffice for every source size or every future
length. Any reserve, replenishment, provider support or surviving archive
is part of the same process and its resource account.

Write $c$ for the common binding roles, ordered roster, codec, rights and
source-independent controller conventions. It contains no concealed
geometry, size, field, earlier journal or response function. Resource
availability, timing, allocator identities and private archives are not
additional outputs of this task. If they are exposed to a future selector,
they must instead be included in the compared state and resource account.

**Theorem 25.3 (the part not determined by the visible metric).** Let $H$
be the minimal connected subtree containing $B$. Its leaves are exactly
$B$, and there are a unique $v\in V(H)\setminus B$ and integer $\ell\ge1$
such that $G$ is $H$ with one pendant unit path of length $\ell$ at $v$.
In particular $N=|V(H)|+\ell$. For fixed $H$ and internal $v$, changing
$\ell$ between two different positive integers preserves all pairwise
visible distances and changes the actual geometry and vertex count.

Proof. A leaf of a minimal spanning subtree must be a specified terminal,
since otherwise removing it preserves connectedness and the specified
vertices. Conversely each member of $B$ has degree one even in $G$, and
is a leaf of $H$ because $b\ge2$. The omitted leaf $h$ is not on a path
between two other vertices, so is outside $H$.

A component of $G-V(H)$ attaches to $H$ at exactly one vertex: connectedness
gives an attachment, and two distinct attachment edges would produce a
cycle. Root that component away from its attachment. A furthest vertex is
a leaf of $G$ outside $B$. Thus there is exactly one such component. No
vertex in it can have two children away from $H$, since extending the two
child paths would give two different omitted leaves. It is therefore a
nonempty path. Its attachment $v$ cannot lie in $B$, whose vertices have
actual degree one. This proves all structural assertions. The path
between two visible leaves stays in $H$, independently of $\ell$; the
last assertion follows. $\square$

**Definition 25.4 (the measured metric prefix).** For each
$a=1,\ldots,b-1$ in that order, actually execute Reset; Add$(a,1)$; Hold.
Read all $b$ ports in ascending order at epoch zero, then repeatedly
execute Tick; Hold and read all $b$ ports in that order. Retain every
reply and the first nonzero epoch at each $j\ne a$. End this metric
phase when all those epochs have been found. Before moving to the next
$a$, retain the acquired records; its initial Reset terminates the
preceding pulse. After $a_*=b-1$, keep this last pulse and its complete
sample prefix; do not yet Reset it.

**Theorem 25.5 (earned hull without size advice).** Every metric phase
terminates at

$$
D_a=\max_{j\ne a}d_G(\ell_a,\ell_j).
\tag{25.1}
$$

The actual first nonzero reply at $j\ne a$ is one, at its distance from
$\ell_a$. Symmetry supplies the complete matrix $d_{ij}$. Finite local
calculation from that acquired matrix recovers the entire subdivided
unit tree $H$, with its visible labels, even when $b=2$.

Proof. At epoch $k$ of a trial the actual field is $A^k e_{\ell_a}$,
by the executed Reset, Add and exactly $k$ Ticks. The matrix entry
$(A^k)_{\ell_j,\ell_a}$ counts length-$k$ walks. Before the distance
there is no such walk; at the distance there is precisely the unique
simple path. This is Lemma 2.1 at unit weights and zero diagonal.
Finiteness and connectedness give (25.1) without providing it to the
stopping controller. Trials $1,\ldots,b-1$ include one end of every
unordered pair, so their observations and symmetry earn all $d_{ij}$.
These are also distances in $H$ by Theorem 25.3.

Apply the classical leaf-metric construction of Lemma 2.3 to $H$, rather
than to $G$. Explicitly, for $i<j$ and integer $0\le r\le d_{ij}$ form

$$
\begin{aligned}
t_k&=(d_{ik}+d_{ij}-d_{jk})/2,\\
h_k&=(d_{ik}+d_{jk}-d_{ij})/2,\\
q(i,j,r)_k&=h_k+|r-t_k|\quad(1\le k\le b).
\end{aligned}
\tag{25.2}
$$

The three-path median in the actual tree gives exactly the distance
vector of the vertex at position $r$ on $[\ell_i,\ell_j]$. Every vertex
of $H$ lies on such a path, because $H$ has exactly the leaves $B$.
For distinct $u,w\in H$, extend their connecting path past $w$ to a leaf
of $H$; its distance coordinate attains $d_H(u,w)$. The triangle
inequality bounds every coordinate difference by this number. Hence

$$
\delta_H(u)=(d_H(u,\ell_j))_{j=1}^b,
\qquad \|\delta_H(u)-\delta_H(w)\|_\infty=d_H(u,w).
\tag{25.3}
$$

Deduplicate (25.2) and join two vectors at sup distance one. This produces
exactly $H$, including degree-two vertices. The argument includes the
case of two visible leaves, when $H$ is their full unit path. Each
labelled leaf is located by its zero coordinate. Lexicographic ordering
of these integer vectors fixes a canonical local enumeration.

This step is credited complete-leaf tree-metric reconstruction on the
hull. Ilmavirta et al., [arXiv:2306.05253v2, Theorem 1 and §5.1](https://arxiv.org/abs/2306.05253v2),
explicitly distinguish that classical tree-only theorem from their
fixed-order comparison with arbitrary graphs. No fixed order is used
as input here. Theorem 25.3 proves why this supplier alone cannot recover
$G$ from the incomplete roster. $\square$

## 26. The same pulse identifies the inaccessible attachment

**Definition 26.1 (the comparison measurements).** Keep the last actual
trial of Definition 25.4 at $a_*=b-1$. Its literal port values and the
locally computed hull values are, respectively,

$$
m_j(k)=(A_G^k)_{\ell_j,\ell_{a_*}},\qquad
h_j(k)=(A_H^k)_{\ell_j,\ell_{a_*}}.
\tag{26.1}
$$

Only $m_j(k)$ is a source measurement. Calculate the finite hull walk
vectors successively by its earned adjacency. Scan the retained last-trial
samples for the first epoch with $m_j(k)>h_j(k)$ at each $j$, including
$j=a_*$. Continue that same actual pulse by Tick; Hold and all-port
Reads until each first excess is found. This uses only earned $H$ and
actual received replies. No value of $v$ or $\ell$ is a stopping input.

**Theorem 26.2 (first-excess attachment inverse).** Write
$d_*=d_H(\ell_{a_*},v)$ and $d_j=d_H(v,\ell_j)$ for the actual attachment
of Theorem 25.3. For every $j$ the first excess in (26.1) occurs at

$$
K_j=d_*+d_j+2,
\qquad m_j(K_j)-h_j(K_j)=1.
\tag{26.2}
$$

The all-port comparison terminates at $R=\max_jK_j$, and earns

$$
d_*=(K_{a_*}-2)/2,\qquad d_j=K_j-d_*-2.
\tag{26.3}
$$

The vector $(d_j)_j$ locates $v$ uniquely in the already earned $H$.
Moreover $R\ge D_{a_*}+2$ and $R\le2|V(H)|$.

Proof. The walks in $H$ form a subset of those in $G$, with identical
unit contributions. Any remaining walk must visit the first hidden
vertex, call it $t_1$. Reaching it from $\ell_{a_*}$ takes at least
$d_*+1$ steps, and reaching $\ell_j$ from it takes at least $d_j+1$.
Thus its length is at least $K_j$. At equality both pieces must be their
unique shortest paths. They concatenate to exactly one walk, consisting
of the route to $v$, the excursion $v,t_1,v$, and the route to $\ell_j$.
This argument allows repeated hull vertices in the concatenation; it
counts a walk, not a claimed new simple path. It excludes any additional
stay, detour or deeper tail visit at that length. Unit weights make its
contribution exactly one. This proves (26.2), including its diagonal
case, and then (26.3).

The actual tree is finite, so all these epochs exist. The controller scans
already received samples and then receives every subsequent epoch at every
port until the last first excess. It therefore ends at exactly $R$.
Equation (25.3) identifies the unique hull vertex with the vector (26.3).
No physical interior reference is produced by that coordinate calculation.

For every $j$, the triangle inequality gives
$d_G(\ell_{a_*},\ell_j)\le d_*+d_j$. Maximizing proves
$R\ge D_{a_*}+2$, so the metric prefix and comparison really do compose
on the same pulse. Both $d_*,d_j\le |V(H)|-1$, whence
$K_j\le2|V(H)|$. These bounds are deductions about the completed run,
not size advice to the stopping algorithm. $\square$

## 27. A finite ray comparison earns the tail and the returned zero

**Definition 27.1 (local ray counts).** After earning $v$, let
$H_\infty$ denote $H$ with a formal unit ray $v,t_1,t_2,\ldots$.
Its diagonal walk count at the input leaf is denoted $r(k)$. This is
finite data at every queried $k$: calculate it on the finite tree
$H^{[k]}$ containing just the first $k$ ray vertices. A length-$k$ walk
from $\ell_{a_*}$ cannot reach an omitted vertex of this finite tree,
so that calculation gives exactly $r(k)$. No infinite array or physical
ray is installed.

In increasing $k$, compare $r(k)$ with the actual diagonal samples
$m_{a_*}(k)$ already retained through $R$. If a first strict inequality
has occurred, retain its first epoch. Otherwise keep the same pulse,
executing Tick; Hold; Read$(a_*)$ at successive epochs and comparing
each new reply, until the first inequality. Once the tail has been
decoded, actually execute Reset; Hold. All local computations and the
final predictor installation are protected by Hold.

**Theorem 27.2 (unknown tail length and actual endpoint).** The first
strict inequality in Definition 27.1 is

$$
K_\infty=2(d_*+\ell+1),\qquad
r(K_\infty)-m_{a_*}(K_\infty)=1.
\tag{27.1}
$$

Thus the actual measurements earn

$$
\ell=K_\infty/2-d_*-1,\qquad
Z=\max\{R,K_\infty\},\qquad N=|V(H)|+\ell.
\tag{27.2}
$$

The pulse is at $A_G^Ze_{\ell_{a_*}}$ immediately before the final
Reset. The returned actual source after Reset; Hold is exactly $(G,0)$.
The complete visible-labelled unit geometry, attachment and tail length
have been acquired without any initially supplied size. Its coordinates
are the vectors of (25.3) and disjoint tail labels $t_1,\ldots,t_\ell$.
There is a unique isomorphism from this graph to the actual specimen
fixing all visible labels. The posterior bound is $Z\le2N$.

Proof. Identify the actual hidden path with the first $\ell$ vertices
of the formal ray. Its walks are a subset of the ray's walks. An extra
closed walk must visit $t_{\ell+1}$, which is at distance
$d_*+\ell+1$ from the input leaf. Its length is therefore at least
$K_\infty$. At that length there is exactly one: the shortest path to
that vertex followed by the reverse shortest path. It contributes one.
Before that epoch the two counts agree. This proves (27.1) and the
length formula. In particular the first ray deficit can precede $R$;
scanning the archive, rather than starting a new stopping clock at $R$,
is necessary to obtain its first epoch.

If the first deficit was already sampled, there are no extra source
Ticks in this phase. Otherwise the continued diagonal measurements
receive every epoch up to $K_\infty$. The actual last pulse epoch is
therefore exactly $Z$. All local ray calculations use finite graphs
and finite integer walk recurrences. Each comparison and every call
terminates under the stated per-run backing premises. The structural
finite $\ell$ gives eventual stopping, without a supplied bound.

The hull map is fixed uniquely by its visible distance vectors. The only
remaining vertices are the unique pendant path at the earned $v$, and
their depths from $v$ fix their correspondence uniquely. This yields the
claimed full graph isomorphism, while supplying no additional callable
port. Actual pulse initialization and the counted Ticks give its
pre-Reset field. Reset then zeros every one of those actual cells; it
does not restore the arbitrary entry. The final Hold retains this zero
while its predictor and any finite output are constructed.

Put $n_H=|V(H)|$. Theorem 26.2 gives $R\le2n_H\le2N$, and
$d_*\le n_H-1$ gives $K_\infty\le2(n_H+\ell)=2N$.
This proves the posterior bound. $\square$

**Corollary 27.3 (one acquired state and retained callable entry).** One
fixed finite controller, independent of $N$, terminates on every
installation of Definitions 25.1–25.2 and returns the complete acquired
visible-labelled geometry with actual current field zero. Retaining the
genuine roster/service binding and rights, the earned graph and a zero
predictive vector installs the current five-command service on that same
specimen. Geometry, numerical coordinates and transfer data do not create
new references or grants.

Proof. Concatenate Definitions 25.4, 26.1 and 27.1 without an intervening
Reset of their last pulse. Theorems 25.5, 26.2 and 27.2 prove all stopping
conditions and the common actual endpoint. They use only received
samples, earned finite objects and source-independent arithmetic and
control. At that endpoint, the stored zero vector equals the physical
field under the earned isomorphism. The retained real service entry,
rather than a numerical vertex name, is what permits the subsequent
calls proved in §28. $\square$

## 28. Full current service after the destructive calibration

**Theorem 28.1 (all-but-one forcing and a paid later window).** On an
earned tree of Definition 25.1 the visible set $B$ zero-forces every
vertex. Put $I=N-b$. One can compute integer vector polynomials

$$
p_w(z)=\sum_{r=0}^{I}z^r p_{w,r},\quad p_{w,r}\in\mathbb Z^b,
\qquad e_w=\sum_{r=0}^{I}A^rJp_{w,r}\quad(w\in V).
\tag{28.1}
$$

Consequently, for every later actual rational field $x$, the passive
window $y_r=J^{\mathsf T}A^rx$, $0\le r\le I$, recovers its starting
field by

$$
x_w=\sum_{r=0}^{I}p_{w,r}^{\mathsf T}y_r.
\tag{28.2}
$$

Actually acquiring that window means Hold; all-port Read, followed by
$I$ repetitions of Tick; Hold; all-port Read. It costs $I$ Ticks,
$I+1$ Holds and $b(I+1)$ scalar Reads. It returns the actual field
$A^Ix$, at which the full predictor is initialized, rather than
physically restoring $x$.

Proof. Mark $B$. If marking stalls with an unmarked vertex, keep all
unmarked vertices, their marked neighbors, and exactly the edges with
at least one unmarked end. This is a finite forest with an edge, since
every unmarked vertex retains its full original positive degree. Each
retained marked vertex has at least two unmarked neighbors, or it could
force. The unmarked vertices retain their original degrees, and at most
one has degree one: the omitted leaf. Thus this forest has at most one
degree-one vertex. Every finite forest with an edge has at least two
such vertices, a contradiction. For example take the two endpoints of
a maximal path in a nontrivial component. Marking therefore finishes
in $I$ forces. Choose the first eligible ordered pair in the canonical
finite enumeration earned in §27; this is an acquired-data selector.

Start with $p_{\ell_j}$ equal to the constant $j$th input unit vector.
When $u$ forces $w$, all its other neighbors are already marked, so set

$$
p_w(z)=z p_u(z)-\sum_{t\sim u,\ t\ne w}p_t(z).
\tag{28.3}
$$

Since $Ae_u=\sum_{t\sim u}e_t$, induction proves (28.1); at the
$s$th force its degree is at most $s$. All coefficients are integers.
Transposing (28.1), using $A^{\mathsf T}=A$, and applying it to $x$
gives (28.2). This instantiates the infection/polynomial-coordinate
supplier of §§3–5 with one omitted leaf; it does not require a new
coefficient-learning experiment for the already known unit law.

The stipulated actual window uses no Reset or Add. Its literal samples
are exactly the displayed $y_r$; its $I$ requested Ticks give endpoint
$A^Ix$. Compute that vector from the recovered start and synchronize
there. Singular adjacency causes no problem, since no inverse of $A$
is invoked. The window and its coefficient construction are separate
paid work if actually requested after calibration. $\square$

**Theorem 28.2 (complete retained callable prediction).** From the final
zero of Corollary 27.3, retain the earned graph, visible-coordinate map,
a full predictive field $\widehat x=0$, the actual service binding and
current rights, and matching parser/transport control. Every finite
sufficiently backed common adaptive continuation of Definition 25.2 has
identical complete outputs and corresponding actual/predictive successors
at every settled cut. This includes arbitrary rational Add inputs,
Reset, all declared refusals and the parser/disabled branches. The field
invariant is

$$
\widehat x_w=x_{\phi(w)}\quad(w\in V(\widehat G)),
\tag{28.4}
$$

where $\phi$ is the earned visible-label-fixing actual isomorphism.

Proof. The final Reset establishes (28.4) on every actual cell. Forward
every enabled real request through the retained entry, consume its whole
output and completed return, and commit the matching update before the
next Ready cut. Before forwarding, reserve the actual request, response,
predictor-update and commit backing and check the common rights and phase.
If the local reservation fails, the controller does not invoke the source;
if the source execution guard fails, neither a successful real call nor a
predictive state update occurs. Matching resource guards are part of this
joint installation, rather than a consequence of equality of field vectors.
For Reset replace the local vector by zero. For
Add$(j,q)$ add $q$ at its earned visible coordinate. For Tick multiply
by the earned unit adjacency, using a separate buffer. For Read return
the predicted visible coordinate and compare/consume the literal reply;
Hold leaves the vector fixed. The graph is stationary in every case.
The table in Definition 25.1 and the graph isomorphism prove each
successor identity and every semantic ACK or scalar identity.

An out-of-range index changes neither vector and produces the same
RangeRefusal. A complete malformed frame changes neither source and
produces the same BadFrame. On each incomplete input prefix both parsers
retain the same bytes and wait, applying no field transition. Once End
completes a valid frame, the corresponding table branch applies exactly
once. Lifecycle phase, output End, LocalACK and Return have the same
fixed transitions; none secretly applies Tick. Missing authority, wrong
phase or unavailable backing leaves the attempted primitive disabled on
both sides; the predictor does not replace it by a source refusal. The
successful-run theorem assumes delivery and commit resources; interruption
after a real mutation supplies no stronger rollback or completion claim.

These one-step statements induct over all exchanges and their byte/phase
prefixes. At settled cuts, equal preceding acquired records and outputs
make a common selector choose the same next finite frame and operands.
Fixing a common random tape gives the same proof for each realized finite
randomized continuation. Selectors may use the earned geometry, current
predictor and actually received finite inputs; no source-dependent selector
or response oracle is supplied for free. If the optional window of
Theorem 28.1 is used for late reattachment, its actual advanced endpoint
establishes the same invariant anew. This proves full continuing use,
including nonzero fields outside the calibration-view domain below.
$\square$

**Corollary 28.3 (the exact declared continuation kernel).** Fix $c$,
settled parser/transport phase and the accessible selector interface,
with no unequal archive, timing, allocation or capacity channel. Among
all trees of Definition 25.1 with arbitrary current rational fields,
equality of complete replies for every finite common continuation is
equivalent to a visible-label-fixing graph isomorphism preserving the
current field.

Proof. Such an isomorphism respects every source, parser, refusal and
fixed-return rule, so suffices by the induction in Theorem 28.2.
Conversely identical future service includes executing the deterministic
Reset-based calibration of §§25–27. The same received prefixes give
the same decisions and finite stop, so its proved inverse gives the same
geometry. This argument identifies geometry independently of the old
field because it begins with Reset. On that common geometry, identical
future service also includes the separate passive starting-field window
of Theorem 28.1. Equation (28.2) makes the two current fields equal.
These are alternative distinguishing continuations from the compared
cut, not two experiments simultaneously preserving one pre-Reset field.
Their cost vectors cannot be combined into one cheaper physical run.
$\square$

## 29. Independent expressions on the final-zero calibration image

**Definition 29.1 (the jointly realized image and four meanings).** Fix
$c$ and the deterministic acquisition above: trial and port orders,
canonical integer-vector enumeration, increasing-epoch archive scans,
fixed request/reply serialization and the final Reset; Hold. A designated
calibration interval starts with its first Reset and ends with that final
Hold. Its command and semantic/lifecycle output journal has no wall times,
local instruction timings, old entry field or earlier history. Consider
only actual successful completed intervals on the promised class, at
which the whole actual field is zero. Later cuts may retain this same
designated interval, rather than treating a new total journal as Time.
On this image the four data have the following independent meanings.

| Expression | Exposed mathematical data, in common context $c$ |
| --- | --- |
| Space | The actual unrooted unit tree with its visible labels and whole present field zero, modulo visible-label-fixing isomorphism |
| Time | The actual finite ordered request/reply journal of the designated canonical calibration interval |
| Boundary | The visible linear response law $F_G(z)=J^{\mathsf T}(z\mathbf1-A_G)^{-1}J$, together with current visible output zero |
| Memory | A finite reachable rational symmetric local predictor $(S,C,0)$, modulo rational orthogonal coordinate changes preserving its input columns |

For an installed Time exposure the controller actually records the
designated exchanges, including their requests, complete replies and
lifecycle words, as they complete. Its finite archive is retained and
charged separately from the predictor; no earlier journal or history port
is assumed. A literal Boundary exposure likewise requires actually
constructing and storing or transmitting its finite rational-function
representation from the earned graph. These finite local constructions
can finish under the final Hold on the same actual zero field. The four
mathematical expressions do not make those records, computations or
exports free.

Here $S\in\mathbb Q^{n\times n}$ is symmetric,
$C\in\mathbb Q^{n\times b}$, and reachability means
$\operatorname{span}_{\mathbb Q}\{S^rCa:r\ge0,\ a\in\mathbb Q^b\}
=\mathbb Q^n$. Its local meanings are update $\xi\mapsto S\xi$,
visible Add $\xi\mapsto\xi+qCe_j$ and output $C^{\mathsf T}\xi$.
Equivalent predictors have a rational orthogonal isomorphism $Q$ with
$QS=S'Q$ and $QC=C'$. The installed earned representative is $(A_G,J,0)$,
not an unrestricted copy of the calibration archive. Any actual journal
archive is a distinct store and remains charged.

Boundary is a finite rational matrix function with an input/output
meaning: from zero, for any subsequent pulse sequence its Laurent
coefficients give the visible convolution responses. It is calculated
from the earned graph after the real measurements, rather than supplied
as an initial full-response oracle or purportedly read as an infinite
table. The matrix-function calculation, representation and any export
are paid local work. The same genuine source entry and rights are
retained in $c$; none of these numerical data produces physical access.

**Theorem 29.2 (all recovery routes and their agreement).** On exactly
the image of Definition 29.1, each of the four data determines the other
three as mathematical data. The routes recover one and the same actual
visible-labelled geometry and zero current field; all twelve directed
conversions, their round trips and every intermediate route agree.
They do not certify off-image numerical data as physical observations or
recover erased entry history.

Proof. Space gives the unit adjacency and the visible injection. Finite
polynomial matrix arithmetic computes $F_G$ by adjugate and determinant.
It also gives the reachable predictor $(A_G,J,0)$, reachability following
from (28.1). Finally run the deterministic calibration locally on this
earned graph: after each simulated Reset/Add/Tick its scalar and fixed
outputs are determined. Its stopping tests terminate by §§25–27. This
computes exactly the numerical contents of the actual designated Time
journal on the stipulated image, including every zero, ACK, End and fixed
return. It does not execute that journal again.

Time contains the actual trial labels, epoch counts and scalar replies.
The first arrivals, hull construction, first hull excesses and first ray
deficit in §§25–27 reconstruct $H,v,\ell$ and hence $G$. The final
Reset; Hold is part of this actual interval and gives current zero.
Neither an old arbitrary input field nor a native growth history occurs
among these decoded data.

Boundary gives every moment by formal expansion at infinity:

$$
F_G(z)=\sum_{k\ge0}M_kz^{-k-1},\qquad M_k=J^{\mathsf T}A_G^kJ.
\tag{29.1}
$$

Each requested coefficient is obtained by finite rational polynomial
recursion on the supplied finite function, not by storing all coefficients.
Use the appropriate columns of $M_k$ to simulate the calibration's
successive finite trials and its same-last-pulse comparisons. The
termination theorem holds on this promised response image, so this earns
the same $G$ in finite local work. A purported arbitrary rational function
is not promised a terminating class-recognition procedure by this argument.
Conversely Space already computes this same $F_G$.

Memory computes its transfer $C^{\mathsf T}(z\mathbf1-S)^{-1}C$, so takes
the Boundary route to $G$. It remains to check that returning through the
earned $(A_G,J,0)$ returns exactly the original Memory equivalence class.
This is the minimal symmetric-realization supplier, with its hypotheses
verified here, as follows. For any two finite reachable symmetric rational
pairs $(S,C)$ and $(S',C')$ with equal transfer, (29.1) gives all equal
moments. For finitely supported rational coefficient lists $a_r,b_s$,
symmetry gives

$$
\left\langle\sum_rS^rCa_r,\sum_sS^sCb_s\right\rangle
=\sum_{r,s}a_r^{\mathsf T}C^{\mathsf T}S^{r+s}Cb_s.
\tag{29.2}
$$

The same Gram pairing holds in the second realization. Thus sending the
first finite sum to the corresponding second finite sum is well-defined:
a zero first sum has zero squared norm, so the second sum is also zero.
It is isometric by the mixed pairing, and is onto by reachability of the
second pair. Reachability of the first makes its domain the full first
space. Increasing every power by one proves $QS=S'Q$; power zero proves
$QC=C'$. Choosing a basis from rational input iterates writes its matrix
as $VU^{-1}$ for rational basis matrices $U,V$, so $Q$ is rational and
orthogonal. The intertwiner is unique because those iterates span. The
converse follows directly by conjugating the resolvent. This checks both
symmetry assumptions, all-moment equality and both reachability assumptions;
no unobservable extra state is silently allowed.

For clarity about all directions, let $E_i(G)$ denote the four just-defined
data of this canonical interval, with Memory understood as its equivalence
class. Let $D_i$ be the recovery of $G$ from each datum proved in the
preceding paragraphs. Then

$$
D_iE_i(G)=G,\qquad E_iD_i(V_i)=V_i,
\qquad \rho_{ij}=E_jD_i\quad(i\ne j).
\tag{29.3}
$$

The second identity uses the actual-image restriction for Time, (29.1)
for Boundary and (29.2) for Memory. It is not a definition of those views
by desired inverses. For every pair $i,j$, (29.3) proves both inverse
round trips, and for any third view $k$ it gives
$\rho_{jk}\rho_{ij}=\rho_{ik}$ wherever interpreted, with identity maps
when indices coincide. Thus all routes, including Time-to-Memory,
Memory-to-Space and Boundary-to-Time, recover the same actual $G$ and
zero field. Computation recovers numerical contents, not a new literal
measurement, historical physical occurrence, service binding or grant.
$\square$

**Theorem 29.3 (the task kernel, zero-domain dynamics and full service).**
On Definition 29.1's image, equality of any one of the four data is
exactly equality for the complete current continuation task of Corollary
28.3. Tick, Hold, Read, Reset, Add$(j,0)$ and the declared field-preserving
refusals transport compatibly within this zero-domain convention. Nonzero
Add leaves this four-view domain; the full predictor remains correct for
it and all subsequent finite legal continuations.

Proof. By Theorem 29.2 each datum determines precisely $G$ and current
zero. Corollary 28.3 gives both implications for the full service kernel.
Every listed zero-preserving completed operation retains $G,0$, so it
retains Space, transfer, zero predictor and the designated calibration
interval. It returns zero for a valid Read and its exact stipulated ACK
or refusal otherwise. This is compatible with each conversion in (29.3).
Additional later calls do not append to the designated Time interval;
the total event journal is a different datum. Proper prefixes and disabled
attempts are handled by the same common parser/phase, not mistaken for
new completed view cuts.

For any rational orthogonally equivalent predictor with $QA_G=SQ$ and
$QJ=C$, initialize $\xi=0$ and maintain $\xi=Qx$. Its local Tick, Add,
Read and Reset rules give respectively $S\xi$, $\xi+qCe_j$,
$e_j^{\mathsf T}C^{\mathsf T}\xi$ and zero, exactly the source values
because $Q^{\mathsf T}Q=\mathbf1$. The same real calls, parser branches
and lifecycle rules are still used. This is coordinate transport of a
retained callable service, not installation by a matrix. The earned
representative uses $Q=\mathbf1$ and Theorem 28.2 directly. After a
nonzero Add, Memory for full prediction has a nonzero current vector,
while the old calibration Time and $F_G$ remain fixed. Consequently the
zero-domain inverse is not an inverse of arbitrary controlled histories.
$\square$

## 30. Calls, literal traffic and coexisting material on one run

**Definition 30.1 (one concrete finite representation).** Let
$s(n)=\max\{1,\lfloor\log_2 n\rfloor+1\}$ for $n>0$, with $s(0)=1$.
Encode a nonnegative integer by $1^{s(n)}0$ followed by its $s(n)$ binary
digits; its length is $\lambda(n)=2s(n)+1$. A signed integer has its
sign bit followed by this word, with positive sign for zero; write
$\sigma(j)=1+\lambda(|j|)$. Encode reduced $p/q$, $q>0$, by the sign of
$p$, the word for $|p|$ and the word for $q$, with the canonical zero
$0/1$. Its exact length is

$$
\rho(p/q)=2s(|p|)+2s(q)+3.
\tag{30.1}
$$

This is also a permissible variable-width rational-cell representation.
It permits growing finite widths; it does not assume unit-cost rational
arithmetic.

For an explicit realization of Definition 25.2, use request kinds
000, 001, 010, 011, 100 for Reset, Add, Tick, Read, Hold respectively;
101, 110, 111 are unsupported kinds with no operands.
Add carries the signed index word and rational word; Read carries the
signed index word. Use semantic response kinds 00, 01, 10, 11 for ACK,
Scalar, RangeRefusal, BadFrame respectively; Scalar also carries its
rational word. Request End and response End are each 1, LocalACK is 0
and Return is 1, in their prescribed protocol positions.

The request parser first consumes three kind bits, then the operand
shape fixed by that kind, then one End bit. In each numeric word it
counts the unary run up to its terminating zero and consumes exactly
that many digit bits, even if the resulting encoding is noncanonical.
An empty unary run, a leading-zero padded word, negative zero, denominator
zero, a nonreduced fraction, an unsupported kind or an incorrect End bit
marks the completed request BadFrame. Otherwise an out-of-range integer
selector marks RangeRefusal. BadFrame takes precedence when both tests
fail. Thus every finite input prefix has a definite next parsing phase;
absence of the remaining operand or End bits stays pending, and a
recognized complete malformed request has no field effect. Extra bits
belong to the next frame and cannot change the completed one. This is a
framed serialized service, not an assertion of error correction against
arbitrary transport corruption. The successful runs deliver each fixed
response and handshake token correctly; interrupted responses retain
their actual phase without an asserted rollback.

Prefix lengths determine the payload boundary, so the fixed tokens
carry no measurement. There are exactly nine nonoperand/nonvalue bits
per completed source call.
An incomplete request or response retains its actual prefix and phase,
and is not charged as a fictitiously completed call. All its transmitted
bits and backing still count if such prefixes are considered.

Let $\mathcal I$ be the actual list of triples $(a,k,j)$ at which the
calibration reads port $j$ in trial $a$. It contains all ports for
epochs $0,\ldots,D_a$ when $a<b-1$, all ports for $0,\ldots,R$ in
trial $a_*$, and just $j=a_*$ for $R<k\le Z$ in that trial.

**Theorem 30.2 (exact successful calibration calls and wire words).** Put

$$
S_0=\sum_{a=1}^{b-2}D_a,
\tag{30.2}
$$

with empty sum zero when $b=2$. For the one calibration through its
actual final Reset; Hold, the source calls are exactly

$$
\begin{aligned}
\mathcal Z&=\#\mathrm{Reset}=b,\\
\mathcal A&=\#\mathrm{Add}=b-1,\\
\mathcal T&=\#\mathrm{Tick}=S_0+Z,\\
\mathcal R&=\#\mathrm{Read}
=b\sum_{a=1}^{b-2}(D_a+1)+b(R+1)+(Z-R),\\
\mathcal H&=\#\mathrm{Hold}
=\sum_{a=1}^{b-2}(D_a+1)+Z+2.
\end{aligned}
\tag{30.3}
$$

It has $2(S_0+Z)+3b-1$ semantic ACKs and $\mathcal R$ literal scalar
replies, including every zero. Write
$C_{\rm cal}=\mathcal Z+\mathcal A+\mathcal T+\mathcal R+\mathcal H$.
With Definition 30.1's codec its exact source-channel traffic is

$$
\begin{aligned}
\beta_{\rm cal}={}&9C_{\rm cal}+(b-1)\rho(1)
+\sum_{a=1}^{b-1}\sigma(a)\\
&+\sum_{(a,k,j)\in\mathcal I}
\bigl(\sigma(j)+\rho(m_j^{(a)}(k))\bigr).
\end{aligned}
\tag{30.4}
$$

Installation, earlier preparation and entry storage, roster/reference/right
supply, report delivery, provider support, local copies and later use
contribute their own actual words on this same run in addition to (30.4).

Proof. Each of the $b-1$ trials has one Reset, Add and initial Hold.
The first $b-2$ have $D_a$ Tick/Hold pairs and $b(D_a+1)$ Reads.
The retained last trial has $Z$ Tick/Hold pairs, all-port Reads through
$R$ and diagonal-only Reads thereafter. The final Reset; Hold adds one
to each of those two operations. This gives (30.3), including the
$b=2$ case with just the single retained pulse. Every non-Read operation
has one ACK; their sum is $2(S_0+Z)+3b-1$. Every Read has one rational
reply and has been counted individually.

The five request kinds and two-bit response kind, plus the two Ends,
LocalACK and Return, give nine bits per call. The only Add operands are
the $b-1$ unit rationals and their displayed actual selectors. Each Read
has its selector and exactly its literal rational reply. Summing gives
(30.4), with no discarded acknowledgement or unused scalar made free.
The other listed channels are not source calls in (30.3), but their
actual transmission/copy/allocation costs remain part of the process.
$\square$

**Definition 30.3 (retained output and full accounting).** A finite
geometry report may consist of $b,n_H,\ell,N$, the attachment's index in
the canonical hull enumeration, its $n_H$ ordered distance vectors, the
sorted $n_H-1$ hull edges as pairs of those indices, and a current-Zero
tag. The tail edges and visible locations then follow uniquely.
Encoding each nonnegative integer in this report by $\lambda$, with a
two-bit report tag 10, a one-bit Zero tag 0, output End 1, LocalACK 0
and Return 1, gives the finite exported report length

$$
\begin{aligned}
\beta_{\rm report}={}&6+\lambda(b)+\lambda(n_H)+\lambda(\ell)
+\lambda(N)+\lambda(i_v)\\
&+\sum_{u\in V(H)}\sum_{j=1}^{b}\lambda(d_H(u,\ell_j))\\
&+\sum_{\{u,w\}\in E(H)}\bigl(\lambda(i_u)+\lambda(i_w)\bigr).
\end{aligned}
\tag{30.4a}
$$

Here $i_u\in\{1,\ldots,n_H\}$ is the canonical hull index, and edges
are sorted pairs with the smaller index first. Counts in the header
determine every subsequent list length. This is a separate output
channel; any request that initiates it and any transferred actual binding
have their own literal traffic. A retained callable
entry is the already held actual binding and grants; numerical report
bytes are not a substitute for their actual backing or an authorized
handoff. If the report is internal, its actual allocated words still
count; if exported, every transmitted copy and return counts.

For a run $\omega$, let $\mathcal R_t$ be its actual simultaneously
live rational cells, $\mathcal U_t$ its other live integer words, and
$\beta_{\rm rest}(t)$ the code, graph/index, parser, reference, grant,
provider, journal, transport, pending and output bits not already counted
in those sets. A concrete encoded-store account is

$$
\operatorname{Store}_{\omega}(t)
=\sum_{q\in\mathcal R_t}\rho(q)
+\sum_{u\in\mathcal U_t}\operatorname{len}(u)
+\beta_{\rm rest}(t),\qquad
\operatorname{Peak}_{\omega}=\max_t\operatorname{Store}_{\omega}(t).
\tag{30.5}
$$

The first sums range over cell occurrences, so equal numbers in different
cells are distinct stores. Shared backing is counted once; distinct
source, predictor, archive or caller copies are counted separately.
Memory-management and access metadata not encoded by (30.1) belong to
$\beta_{\rm rest}$. Total literal traffic is the sum of actual wire and
copy word lengths over all these channels, including (30.4), report,
installation/preparation and every subsequent completed call or prefix.
Local word operations, rational normalization and allocation/clearing
work are separate computation coordinates. These are simultaneous
per-run quantities; no minimum from another run is substituted.

For example a separately materialized Time archive can store the complete
ordered source-channel bitstream of length $\beta_{\rm cal}$, prefixed
by its $\lambda(\beta_{\rm cal})$-bit length word. This costs their sum
in numerical bits, in addition to the actual container/reference backing
and the work and copy traffic of recording it. Protocol phase and the
canonical controller parse the stream in its fixed directions. Retaining
the separately indexed rational sample arrays as well pays for both
copies. Exposing Time requires this actual record or an actually shared
equivalent store, rather than assuming a surviving free transcript.

**Proposition 30.4 (finite local computation with actual widths).** One
direct implementation has finite work and storage on every admitted
calibration, with the following explicit realization. Put

$$
Q=\sum_{i<j}(d_{ij}+1),\qquad n_H=|V(H)|,
\qquad \Delta=\max_{w\in V}\deg_G(w).
\tag{30.6}
$$

Form at most $Q$ candidate vectors of $b$ integers in (25.2). Naive
construction, pairwise deduplication, canonical ordering and adjacency
cost $O(Qb+Q^2b)$ integer operations/comparisons. The final-pulse hull
walk comparison can use $O(Rn_H)$ integer additions and its actual
sample comparisons. Recomputing each ray comparison at epoch $k$ by
$k$ sparse walk updates on $H^{[k]}$ costs in total

$$
O\!\left(\sum_{k=0}^{Z}k(n_H+k)\right)
=O\bigl(Z^2(n_H+Z)\bigr)
\tag{30.7}
$$

integer additions/initializations, besides archive handling. Only two
walk vectors and the finite graph for the current comparison are needed
at once. Throughout this run $n_H+Z\le3N$. All displayed operation counts
pay their actual word widths and bit operations.

Proof. There are exactly the indicated pair/position candidates. Each
has $b$ coordinates computable with integer addition, division by two
and absolute value; on this image the divisions are exact. Direct
comparison of every pair of candidates or retained vectors costs at most
$b$ coordinate operations per pair. Adjacency and canonical ordering can
be obtained within the same quadratic bound.

A tree walk update initializes one number per vertex and adds once for
each directed edge. The hull has $n_H-1$ edges. Propagating its input
through every needed epoch, retaining current vectors and the actual
read archive, proves the hull bound. The finite ray graph at epoch $k$
has $n_H+k$ vertices and $n_H+k-1$ edges. Starting its input vector and
performing $k$ such updates computes exactly the diagonal in Definition
27.1. Summing gives (30.7). This deliberately simple implementation
recomputes each finite comparison; it needs no infinite-ray state or
unproved reuse of a changing truncation. Theorem 27.2 gives $Z\le2N$,
hence the stated posterior storage bound. No runtime stopping decision
consults that inequality.

For any actual epoch-$k$ impulse, each nonnegative walk count is at most
$\Delta^k$: there are at most $\Delta$ choices at every step. The finite
comparison trees have maximum degree at most $\Delta$ as well, because
adding the ray increases only the earned attachment degree to its actual
value and gives the new ray vertices degree at most two. Their nonzero
count magnitudes through epoch $k$ therefore need at most
$1+\lceil k\log_2\max\{2,\Delta\}\rceil$ bits. Exact counters, indices,
intermediate products, rational-function coefficients if constructed,
and every operand/output use their actual widths too. This bound on
impulse integers places no bound on the arbitrary rational entry field
before the first Reset or on later arbitrary rational controls.
$\square$

**Proposition 30.5 (source, predictor, archives and continued use coexist).**
A simultaneous realization of the preceding bounds may retain all
acquisition arrays through the returned zero cut. It charges all the
following live backing wherever present: the actual $N$ field cells and
its separate synchronous Tick buffer; actual source incidence and service
support; a distinct $N$-cell predictor and its Tick buffer after allocation;
the earned hull and full graph, visible map and tail coordinates; up to
$Qb$ candidate-coordinate words and deduplication records; the distance
table, two finite ray/hull work vectors, samples/onset flags/counters and
finite controller; the complete actual calibration journal if retained;
all input/output, parser/pending, report and arithmetic scratch; genuine
references, grants and their provider backing; and every coexisting
preparation, supplier, caller or archived copy. Optional forcing
polynomials or exported transfer data add their actual construction,
coefficient and output stores. A finite program supplies no uniform
bound on this material or on its lifetime traffic.

Proof. The algorithms above use exactly finite lists, integer/rational
words and sparse graphs, so the listed layout supplies their work and
retained outputs without an oracle. In (30.5) the source and predictor
cells are different occurrences even when their values agree. One
synchronous adjacency update in either array uses $N$ zero initializations
and $2(N-1)$ directed-neighbor additions, plus actual copying or buffer
exchange; performing both updates pays both bills. Each Reset writes
$N$ zero fields. A valid Add performs its rational addition and dispatch;
Read copies/transmits the exact rational; Hold and every refusal still
use their control, framing and return operations. Decoder comparisons,
list scans, selectors, report construction and source/predictor dispatch
are local paid work, not hidden source transitions.

After calibration, a continuation contributes its own actual counts for
Reset, Add, Tick, Read, Hold and refusals, and each valid Add operand and
Read value contributes its own $\rho$ word. The nine-bit completed-call
overhead and selector words remain as in Definition 30.1. A later passive
window in Theorem 28.1 adds exactly its stated calls and $2I+1$ semantic
ACKs, every scalar/selector/frame, polynomial construction, reconstruction
and advanced-vector work. It is not included in (30.3). Building (28.3)
by direct coefficient arrays uses at most $Nb(I+1)$ integer slots, with
actual signed coefficients, and its graph scans and arithmetic are paid.

If Boundary's rational function is materialized, the already earned
finite $A,J$ allow polynomial determinant/adjugate construction, for
example by the finite permutation expansion and finite polynomial
arithmetic. Its possibly expensive coefficient growth and every export
are additional work and backing, not a free all-response port. A
non-native symmetric Memory representative similarly pays for its actual
matrices, basis conversion and vector operations. All such choices are
charged only when made on the run in question.

There are sources of unbounded $\ell$ already for a fixed visible hull,
and all have $N=n_H+\ell$ actual field cells. The acquired length/output,
walk arrays and exact widths can grow too. Earlier provider records need
not disappear because an observer's field was Reset; any surviving
record is still counted, with actual isolation or clearing work if used.
Thus the fixed instruction description and pointwise finite termination
give no constant-space, constant-precision, polynomial bit-cost or
lifetime-material theorem. The exact account is (30.5) and the sum of
actual operations and traffic, with the displayed finite bounds for this
chosen implementation. No global optimum or coordinatewise superiority
over a different installation has been deduced. $\square$

## 31. Exact exclusions and the source-relative gain

**Proposition 31.1 (what the recovered data cannot distinguish).** The
calibration inverse has the following exact boundaries.

For the same promised $G$, different arbitrary entry fields give the same
calibration journal after its first Reset and the same four final-zero
data. A present visible snapshot need not determine a nonzero current
interior field. If two leaves instead of exactly one may be omitted,
even unit trees admit distinct current fields with identical complete
visible five-command service. Reachability is necessary for the Memory
uniqueness assertion as stated. None of these is a counterexample to
Theorems 27.2 or 29.2 on their declared domains.

Proof. Reset maps all entry fields to zero. From that moment the fixed
calibration executes identical calls on the same $G$ and receives
identical replies. It consequently cannot recover the erased entry or
its preceding controls. More generally, from a zero cut the journals
Reset; Hold and Add$(1,1)$; Reset; Hold have the same endpoint $G,0$ but
different commands and outputs. Inserted zero-field Reads, Holds or Ticks
supply further collisions for unrestricted historical Time. Their
journals are outside the designated canonical interval convention.

For an internal vertex $w$, zero and $e_w$ have the same current visible
restriction. Such a vertex exists in the present class, which has at
least three leaves. Theorem 28.1 separates these fields by a paid window,
but no instantaneous snapshot inverse follows.

For the two-omission claim, use a unit star with $b\ge2$ visible leaves
and two hidden leaves $h_1,h_2$. Put $z=e_{h_1}-e_{h_2}$. Then
$J^{\mathsf T}z=0$ and $Az=0$. Starting from $x$ and $x+z$, common
visible Adds preserve this invisible difference, the first Tick kills
it, and Reset also kills it; every preceding or subsequent visible Read
agrees. Hold, refusals, parser and fixed outputs agree too. Induction
therefore gives identical complete common adaptive service from distinct
current fields. This violates the arbitrary-field kernel conclusion on
that enlarged class. It does not assert a geometry collision inside the
exact-one/unit class. The weighted different-order collision of Theorem
8.1 remains a separate positive result with its own different weights
and omission counts.

Finally append an uncoupled rational symmetric scalar mode to any
reachable predictor: $(S\oplus[\alpha],\binom C0,0)$. Its visible
transfer is unchanged but its dimension is larger. It is not reachable
and cannot be orthogonally equivalent to the original full realization.
Thus equality of transfer without both reachability premises cannot
justify the Memory inverse used in Theorem 29.2. $\square$

**Theorem 31.2 (supplier correspondence and bounded acquisition gain).**
The source-relative addition in §§25–30 is acquisition of the omitted
attachment and its unknown positive length from physically performed
unit-tree trials with one absent leaf port, including finite stopping,
actual final zero and retained full current service. Its four-expression
consequence is restricted to the final-zero canonical calibration image.
It uses the following supplied mathematics at its actual hypotheses,
rather than claiming a new general metric, forcing, realization or
four-view principle.

Proof. In this volume §§1–5, the native law can have positive rational
links and arbitrary rational diagonal, and the supplied roster contains
all leaves. Lemma 2.3 supplies precisely the hull reconstruction used
in (25.2)–(25.3). The polynomial infection, advanced passive window,
current predictor and continuation-kernel arguments of §§3–5 supply
the algebraic consumers in §28. Their complete-roster premise does not
supply the path outside $H$ in Theorem 25.3. Sections 17–24 reduce
selected measurements on a complete ordered LAB roster and identify
its original birth-typed root; sparse observations there do not mean
that a leaf port is absent. Here the roster is incomplete, no planar
order or birth type is given, and only unrooted visible-labelled unit
geometry is recovered. The metric counterpair in Theorem 25.3 shows
the genuine missing information; the two same-pulse defects in §§26–27
supply it. The lower number of supplied leaf ports is obtained under
stronger unit/exact-one/Reset hypotheses, with the costs in §30, not as
a total dominance theorem over full-leaf weighted acquisition.

The infection residual is literature-attested. [Burgarth and Maruyama,
*Indirect Hamiltonian Identification through a small gateway*,
arXiv:0903.0612v1, §II, DOI 10.1088/1367-2630/11/10/103019](https://arxiv.org/abs/0903.0612v1)
uses a known graph, a unique healthy neighbor and its Hamiltonian
spectral/preparation/tomography data. Only that one-neighbor linear
identity is consumed in (28.3). Its Hamiltonian access and tomography
are not installed scalar field ports here. The primary tree-metric
reference and its fixed-order distinction are given in Theorem 25.5.

Blåsten, Isozaki, Lassas and Lu, [*Inverse problems for discrete heat
equations and random walks for a class of graphs*, arXiv:2107.00494v2,
Definitions 1.1–1.2 and Theorems 1.3, 1.7–1.8](https://arxiv.org/abs/2107.00494v2),
supply the inverse-spectral/source-to-solution and unique-continuation
framework already credited in §9.1. Their direct graph-rigidity theorem
requires the Two-Points Condition. It fails for the present incomplete
roster: in the two-vertex set $\{v,t_1\}$, every visible leaf is strictly
nearer to $v$ than to $t_1$, so only $v$ is extreme. Their full response
map is not a finite acquired port, either. The forcing proof does verify
absence of an invisible eigenfunction. More explicitly, choose their
vertex measure and edge weights both one and their potential
$q(w)=-\deg_G(w)$. Their Laplacian is
$\Delta=A_G-\operatorname{diag}(\deg_G)$, so
$-\Delta+q=-A_G$. An eigenvector of this operator vanishing on $B$
vanishes everywhere by (28.1). This meets their no-invisible-eigenfunction
premise, with known boundary measure one, for the corresponding
spectral/source-to-solution equivalence. It does not identify their
discrete heat update $\mathbf1+A_G$ with the installed Tick $A_G$, or
install their full response map as a literal read. The particular
missing-tail geometry and finite stopping are proved here, not obtained
by dropping the Two-Points premise or changing the actual clock.

The [Finite Observability Equivalence source](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs)
concern arbitrary supplied finite real inner-product update/readout
maps. Their present correspondence is update $A_G$, output $J^{\mathsf T}$,
state $\mathbb R^N$, output $\mathbb R^b$ and horizon $I+1$.
Equation (28.2) supplies the rational left inverse, and that identity
persists over the reals, meeting its kernel/full-rank/Gram criteria.
The theorem itself grants no Read or Reset. The [Minimal Symmetric
Realization Uniqueness source](../../../D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.lean)
with its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.scribe.cs)
supplies the real Euclidean orthogonal intertwiner. Its private
combination, Gram and kernel helpers use exactly the equal-all-moments
and both symmetric/reachable hypotheses checked in (29.2). The rational
basis argument there supplies the rational coordinate refinement. The
owning Scribe attributes the mature symmetry theory to Willems; this
application is not a new generic minimal-realization theorem.

[Native Full Source Producer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean)
with its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs)
has a literal constructor/address Read, growing stacks and a retained
chronology. Its private traversal, exact-read and stationarity proofs
do not turn a scalar field response into that Read or bound its workspace.
[Native Material Root Recognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean)
with its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs)
uses original birth typing, at least three logical leaves, full adjacency
and the complete linear terminal list. Its finite compatibility test,
private catalog/coordinate/uniqueness helpers and effective inverse
retain those inputs. The present visible hull and omitted tail supply
neither complete terminal order nor birth typing, so that result is not
an inverse to an original ordered alpha/beta source here.

The pinned mathlib [adjacency source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean)
provides `adjMatrix_pow_apply_eq_card_walk` for a finite simple graph,
decidable vertex equality and semiring coefficients. Use the actual
finite $G$ and coefficients $\mathbb Q$; it counts exactly the unit
walks used above. It does not supply a full response oracle or stopping
bound as input. This correspondence and the inspected D5 declarations
are source-level suppliers, not a newly compiled application.

The distinct public constructions also retain their actual conditions.
[NLBA II §§45–50](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md#45-an-earned-root-read-installation-with-a-cleared-rational-preparation)
already recovers prepared signed rational amplitudes by an installed
original-root Read, known constructed geometry/roster, cleared handoff
and successful asymmetric growth. Its [§§51–54](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md#51-one-growth-separation-through-the-original-first-terminal)
separate owned field pairs using selected original-terminal experiments
with growth and the selected advanced endpoint. Neither is the present
unknown stationary geometry/incomplete-roster task. [AA II §§84–92](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#84-growing-native-fields-with-two-declared-clock-phases)
already recovers successful growing histories from a known-alpha nonzero
seed under its installed positive-diagonal invertible laws and explicit
clock phases. Unit adjacency, erased entry and a canonical stationary
calibration are different premises. [Recovery Geometry II §§96–103](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md#96-persistent-local-calibration-on-the-native-material)
already acquires unknown ordered native support from genuine zero under
persistent address-dependent calibrated coefficients and a returning
root Tick. Its root binding, address calibration and preparation do not
come from the present incomplete leaf roster, and no such calibration
is assumed for the unit adjacency here. These are positive supplied
results, not absent or unresolved predecessors.

The actual-source, rights, retained-use and historical-service conditions
of NCR, PVC, PR57, the callable Atlas and Process Geometry remain those
delimited in §§9 and 16. Their installed original tasks are not renamed
as this five-command stationary service. The new correspondence is
Corollary 27.3 and the invariant (28.4); the new geometry information is
(26.2) and (27.1). Thus the credited ingredients are used as intermediate
suppliers of a repository-derived source-specific synthesis, with no
claim of worldwide priority or impossibility from a search absence.
$\square$

**Corollary 31.3 (the retained domain and precise residual obligations).**
On the finite stationary unit-tree/exact-one-missing-leaf class, with
$b\ge2$ authenticated visible leaves and the installed actual
Reset/Add/Tick/Read/Hold service, the complete acquired geometry and
zero-current callable predictor exist by this finite procedure without
supplied size. Independently meaningful four-view numerical recovery
holds on the final-zero canonical calibration image, with the same
source, bindings, current rights and costs. It proves neither erased
entry/history recovery, original ordered alpha/beta root/birth recovery,
a generic incomplete weighted-tree inverse, a finite-noise guarantee,
nor a global optimum. The unchanged fixed-$G_{\rm gc}$, original-$Q$,
parked-consumer, original-initialization and other original-model
obligations retain their original statements.

Proof. Theorems 25.5–27.2 give actual measurements, finite stopping and
the complete current endpoint. Theorems 28.1–28.2 give the optional
advanced window and every continued service branch; Theorems 29.2–29.3
give all view routes, kernels and their exact dynamics domain. Section
30 charges this one acquisition and its actual later use, rather than
mixing different specimens or interfaces. Theorem 25.3 and Proposition
31.1 give exact counterevidence to metric-only, erased-history and
indiscriminately enlarged view claims. The remaining exclusions follow
from the explicit domain: a coordinate or numerical image test is not
physical provenance, a right or a missing native structural input;
exact integer comparisons are not a noisy instrument theorem; a finite
algorithm is not a material optimum. A common actual process identifying
this stationary installation with original alpha/beta, rational-path or
quantum preparations, complete actions and outputs has not been supplied
by these results. Establishing such a correspondence, or any of the
excluded original tasks, requires its own hypotheses and proof. $\square$

## 追加锚（本行以下为增补区）
