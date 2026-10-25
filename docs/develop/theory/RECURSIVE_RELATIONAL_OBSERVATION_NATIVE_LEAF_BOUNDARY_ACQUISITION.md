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
