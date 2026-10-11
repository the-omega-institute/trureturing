# Actually acquired mixed-epoch relations and complete original recuts

## 1. Original sources, retained relations and the unchanged target

**Definition 1.1 (source and original row).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{ARH.1.1}
$$

These are nonempty finite free ordered trees; brackets, order and repeated
occurrences are part of the source. Addresses are finite words over
$\{L,R\}$, with root $\varepsilon$. The reply $r_t(p)$ lies in
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
A subtree $t|_p$ is defined only when $p\in\operatorname{Pos}(t)$.

For a finite prefix-free set $A$ of **original** addresses, use the complete
row $R_A(t)$ of [SLH, Definition 59.1][SLH]. Its reached holes are exactly
$A\cap\operatorname{Pos}(t)$, ordered lexicographically. Its concrete
outside context is obtained by replacing those whole subtrees by numbered
holes. Its partition equates two holes exactly when their complete ordered
subtrees are equal. An absent cut address supplies no hole. Empty cuts,
the root cut and cuts containing absent addresses are allowed.

Fix arbitrary such $P,Q$ and an actually acquired old row $R=(C,\pi)$ at
$P$. Let $\mathcal B$ be its set of classes. The old source correspondence from
[SLH, Theorem 59.4][SLH] is used without weakening:

$$
u=C[(z_{[i]})_i],\qquad z_b\in\mathcal T,
\qquad z_b\ne z_c\quad(b\ne c).
\tag{ARH.1.2}
$$

The occurrence list, every repeated class, every cross-class disequality,
the concrete outside and the old absent-address guards are retained.
Classes outside the new task still participate in (ARH.1.2).

**Definition 1.2 (signed, guarded relation history).** A literal record is
$(a,s,c)$ with certified epoch $a\ge0$, address $s$, and reply $c\in\mathcal A$.
A relation record is $e=(a,s,b,t,\bowtie)$, where $\bowtie$ is either
$=$ or $\ne$. Its predicate on an original source is

$$
\begin{aligned}
\operatorname{Rel}_e(u)\quad\Longleftrightarrow\quad&
 s\in\operatorname{Pos}(\rho^a u)\ \land\
 t\in\operatorname{Pos}(\rho^b u)\ \land\\
& (\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t.
\end{aligned}
\tag{ARH.1.3}
$$

In particular, an absent endpoint makes either signed predicate false;
absence is not a disequality certificate. The compared objects are entire
trees, not their root replies. Endpoints can have different epochs and
can be absent originally but born before their recorded epochs.

For finite lists $H_0,H_{\rm rel}$, retaining repetitions, set

$$
\begin{aligned}
U=\mathcal U_R(H_0,H_{\rm rel})
 :=\{u\in\mathcal T:;&R_P(u)=R,\\
&r_{\rho^a u}(s)=c\quad((a,s,c)\in H_0),\\
&\operatorname{Rel}_e(u)\quad(e\in H_{\rm rel})\}.
\end{aligned}
\tag{ARH.1.4}
$$

All constraints refer to this same $u$. Throughout the service statements,
$U\ne\varnothing$ and the task is the **entire** $R_Q(u)$: its concrete
outside, reached original holes and complete equality partition. No past
raw event is requested.

**Assumption 1.3 (paid acquisition, complete cut and service).** The retained
records were acquired by legal finite paid raw acquisition and comparison
before a complete access cut. The same physical register, with the same
original root and source, has actually reached a certified
$N\ge\max(\{0\}\cup\operatorname{epochs}(H_0,H_{\rm rel}))$.
The entire accessible initial state is a fixed function of the stated
records and common parameters, and recovers them. Its original-source
fiber is exactly (ARH.1.4). A source-dependent choice of records or of
control state must satisfy this correspondence too.

Every still accessible source-bearing cache, address, count, length,
program position, timing field, output, archive, permission or handle is
included in the complete retained input. No forgotten traversal or acquired
tree description is available. This is an access assumption, not a claim
of physical erasure. Source continuity and epoch certification do not
supply a source identity label. If these conditions fail, the appropriate
fiber must include the extra state; it is not (ARH.1.4).

A service is deterministic, effective and terminates correctly for every
$u\in U$. The allowed operations are paid $\mathsf{Read}(p)$ at any finite
physical address, including absent addresses, and real serial
$\mathsf{ApplyRho}$ on that register. A static service makes no further
updates. There is no reset, reroot, clone, unknown whole-tree, unknown
subtree equality, source-membership or identity port. Local computation
uses common input and acquired replies only. Updates reveal no additional
source-dependent timing or implementation information.

A uniform finite new-read budget means a single $K\in\mathbb N$, depending
on common retained input and task, bounds new raw calls on **all** $u\in U$.
Physical address generation and length, local work, installation, memory,
retention, entry, version evidence, updates, archives and output are charged
separately. A finite per-source pre-cut cost is not required to have a
uniform bound. A new entry after an absorbing halt must be supplied and
paid separately. These are the same operation and access conditions as
[SLH, §§1, 59, 62 and 74][SLH], with the additional acquired predicates
(ARH.1.3).

## 2. Acquisition correspondence and the inherited existence bridge

**Proposition 2.1 (an actual producer for the full signed input).** Fix a
finite public list of literal coordinates, a finite public list of endpoint
pairs, $P$, and a final epoch $N$ at least their epochs. There is a
deterministic source-total pre-cut acquisition procedure whose successful
retained outputs have exactly the fibers (ARH.1.4), conditional on the
complete cut in Assumption 1.3. An unreachable endpoint produces a distinct
invalid-record outcome, not a successful signed record.

Proof. Use the paid full traversal of [SLH, §§53 and 59][SLH] at epoch zero
to compute $R_P(u)$, including all old comparisons. Process the public
epochs in increasing order, executing each intervening update on the same
register. Perform every requested literal read. For each endpoint $(a,s)$,
read $s$ at epoch $a$. If reached, acquire its complete finite subtree by
the same traversal, prefixing every relative request by $s$ and requesting
children only after their parent reports branch. Keep these paid finite
descriptions until both endpoints of each comparison have been obtained.
Finite syntactic tree comparison then determines its sign. A comparison
can be computed after the earlier endpoint's epoch without accessing that
old physical version: its paid description was still available before
the cut. These descriptions are not physical register clones.

Continue to $N$ and retain the canonical old row, stipulated literal
replies, endpoint coordinates and signs, $N$, and common code, permissions
and ready control. Apply the stipulated complete cut to the descriptions
and all other source-dependent acquisition fields. On any source the
successful retained output reports exactly the predicates in Definition
1.2. Conversely, any finite source satisfying a fixed successful output
executes the same public coordinate schedule, gives its stated replies and
signs, and reaches that same retained state. Its forgotten traversal length
can differ. These two directions prove the fiber equality, not merely
soundness of each record separately.

For a non-sharing traversal, successful pre-cut raw cost is

$$
|\operatorname{Pos}(u)|+|H_0|
 +\sum_{(a,s)\in E}|\operatorname{Pos}((\rho^a u)|_s)|,
\tag{ARH.2.1}
$$

where $E$ lists endpoint occurrences with repetitions; their root reads
are already counted in their traversals. Every physical request includes
its actual prefix. Comparisons, descriptions, updates, certification and
the access cut have their separate costs. All are finite on each source;
none is refunded by the short retained sign. The procedure computes both
sign outcomes, so fixing either actual outcome is legitimate. An adaptive
producer requires its own full control/state correspondence; legality
alone does not make its selection rule disappear. $\square$

**Definition 2.2 (finite original-prefix determination).** For the entire
fiber (ARH.1.4), write $\operatorname{PrefDet}(U,Q,h)$ for

$$
\forall u,v\in U,\quad
\bigl[\forall s, |s|\le h\Longrightarrow r_u(s)=r_v(s)\bigr]
\Longrightarrow R_Q(u)=R_Q(v).
\tag{ARH.2.2}
$$

The following correspondence is an application of the operational part
of [SLH, Theorem 74.4, proof (iii), and (SLH.74.7)][SLH], not a new
literal-history algorithm:

$$
\begin{aligned}
&\text{uniform-finite-read serial service on }U\\
\Longleftrightarrow\;&\text{uniform-finite-read static service on }U\\
\Longleftrightarrow\;&\exists h\ge0\ \operatorname{PrefDet}(U,Q,h).
\end{aligned}
\tag{ARH.2.3}
$$

Here is the precise change of domain needed to use that supplier. Its
serial-to-prefix direction uses a common complete initial state,
source-totality, four-valued replies and physical-address locality. Those
hypotheses hold in Assumption 1.3 independently of the form of $U$.
The supplier compresses each deterministic computation/update segment
between replies and obtains a finite reply tree under a uniform $K$.
Its finitely many submitted addresses have a finite maximum length.
(SLH.74.7) turns that length into an $h$ satisfying (ARH.2.2), including
all born and absent-address cases. It also gives at most $4^K$ terminal
outputs. No prior uniform bound on local work or update count is added.

For the converse the old literal-only feasibility routine is replaced
as follows. Membership of a *given concrete finite candidate* in (ARH.1.4)
is decidable by computing its old row, finite iterates, literal replies,
endpoint guards and complete signed comparisons. Given a valid $h$, use
[SLH, Theorem 2.2][SLH] at the actual static epoch $N$ to recover all original
replies of length at most $h$. This costs at most
$2(2^{h+1}-1)$ new reads, with address length at most $h+\lceil N/2\rceil$.
Enumerate all finite original trees by size and encoding until one belongs
to $U$ and agrees with the recovered prefix. The actual source is an
enumerated witness, so this local search terminates on every actual run.
Output its complete $R_Q$. Equation (ARH.2.2) proves that output is common
to the actual conditioned fiber. No claim that the witness is the real
source is needed. The newly acquired evidence is the actual $N$-epoch
reply tuple, not fictitious epoch-zero events. Static inclusion gives
the remaining direction of (ARH.2.3).

This constructs a service **given** a suitable $h$. It does not decide
whether an $h$ exists for arbitrary $H_{\rm rel}$, extract it from arbitrary
source-total code, or decide emptiness of arbitrary coupled morphic
constraints. It proves equality of the two existence predicates, not
equality of their minimum budgets. These distinctions remain part of the
full question in §9.

## 3. Guarded morphic cells and exact paid reuse

**Definition 3.1 (residual terms).** Use [SLH, Definition 74.2][SLH] with

$$
d=1+\max\bigl(\{0\}\cup\{|q|:q\in Q\}
 \cup\{|s|:(a,s,c)\in H_0\}
 \cup\{|s|,|t|:(a,s,b,t,\bowtie)\in H_{\rm rel}\}\bigr).
\tag{ARH.3.1}
$$

For each old class choose its original depth-$d$ prefix pattern $t_b$,
using one variable at each reached depth-$d$ frontier position, different
variables for different classes and positions, and the same pattern at
every occurrence of a repeated class. Put

$$
W_\eta=C[(t_{[i]})_i],\qquad
\Delta_\eta=\{t_b\ne t_c:b<c\}.
\tag{ARH.3.2}
$$

The finite pattern list and the literal checks are exactly the existing
construction, including all old disequalities. A residual term is a finite
ordinary term over $\alpha,\beta,\langle\ ,\ \rangle$ and these variables.
A morphic expression $\rho^a(A)$ means the actual iterate applied **after**
a finite-tree valuation of $A$; $\rho$ is not a free new constructor.

**Proposition 3.2 (full-domain guarded representation).** There is an
effective finite list of disjoint original prefix cells such that the
entire $U$ is their union under $v\mapsto W_\eta[v]$. Each cell retains
$\Delta_\eta$, its literal conditions, and a finite conjunction of signed
relations between morphic residual terms or concrete trees. Empty cells
may remain in the list. The construction does not require a general
emptiness algorithm. It also computes the full target maps on each cell.

Proof. A residual occurrence has depth $|p_i|+d$, strictly beyond every
named endpoint, literal and new cut address. Thus navigation to an endpoint
$s$ either reaches an original subterm $A$ of $W_\eta$, in which case the
whole endpoint at epoch $a$ is $\rho^a(A[v])$, or meets a known original
leaf $\lambda_b$ at a strict prefix $c$ of $s$. Here
$\lambda_0=\alpha$, $\lambda_1=\beta$. In the latter case write $s=cz$.
The supplied leaf-sector formula [SLH, Definition 29.1][SLH] gives the guard

$$
a+b\ge w(z^-)+2,
\qquad w(z)=\#_L(z)+2\#_R(z),
\tag{ARH.3.3}
$$

and, when it holds, the complete endpoint is
$T_{a+b-w(z)}$, where $T_j=\rho^j\alpha$. If the guard fails, reject the cell
for this relation record, for either sign. In the original-node case the
endpoint is always reached. Concrete computations cover ground $A$ too.
Apply this to both endpoints of every relation and retain the stated sign
between the resulting **whole** expressions. Literal checks use the
already supplied guarded reply formula, including repetitions and absent
replies.

Each concrete old class value has a unique pattern and a unique valuation
by its original frontier subtrees. The inverse to filling is recovered at
old representative holes and then at their pattern frontiers. [SLH,
Theorems 59.4 and 60.2][SLH] supply exactly the old-row correspondence.
The endpoint analysis proves each newly attached predicate equivalent to
(ARH.1.3) under that same valuation. Therefore the disjoint union of all
satisfying valuations is bijective with (ARH.1.4). No product relaxation,
separate marginal feasibility or chosen representative is involved.

The target construction of [SLH, (SLH.74.9)][SLH] still applies: navigation
to $Q$ gives a fixed reached set $J_\eta$, a symbolic outside context
$E_\eta$ and subterms $A_{\eta,q}$, satisfying

$$
\begin{aligned}
I_Q(W_\eta[v])&=J_\eta,\qquad C_Q(W_\eta[v])=E_\eta[v],\\
q\sim r&\Longleftrightarrow
 A_{\eta,q}[v]=A_{\eta,r}[v]\quad(q,r\in J_\eta).
\end{aligned}
\tag{ARH.3.4}
$$

The outside can contain residual variables which must be output as complete
concrete trees. Equation (ARH.3.4) keeps that obligation.

For clarity about the algebraic boundary, when $a\le b$, injectivity from
[TRANSPORT, (RA.2207)][TRANSPORT] gives

$$
\rho^a(A[v])=\rho^b(B[v])
\Longleftrightarrow A[v]=\rho^{b-a}(B[v]),
\tag{ARH.3.5}
$$

and the same equivalence for disequality. Only the common iterate cancels.
If one endpoint is a known concrete $g$, its finite partial image inverse
$\delta$ from the same supplier tests whether $g\in\rho^a[\mathcal T]$.
When so, $\rho^a(A[v])=g$ is exactly $A[v]=\delta^a(g)$; otherwise it is
always false. The corresponding reached disequality is its complement.
Equal epochs therefore give ordinary signed term constraints; a known
endpoint does too. Unequal live epochs generally leave a morphic relation.
For instance $\rho(x)=\langle y,z\rangle$ has
$(x,y,z)=(\beta,\beta,\alpha)$ as a solution. Treating $\rho$ as a free
constructor would reject it. The original source
$u=\langle\beta,\alpha\rangle$ satisfies $(0,L,1,R,=)$ although its
original children differ. $\square$

The following paid reductions identify existing supply used by this
representation and by later consumers; they are not new solvers.

If a record compares two reached old holes at the **same** epoch, [SLH,
Theorem 60.2][SLH] determines its sign from the complete old partition.
A consistent record is redundant; an inconsistent one violates the
nonempty-input promise. All other old classes and their disequalities stay.
Here [SLH, Theorem 74.4][SLH] applies directly when no other nonredundant
relation remains. [SLH, Theorem 69.4][SLH] applies to its own finite VALUE
tasks, with its static contract and exact minimax conclusion unchanged.

For records whose cell expressions have a concrete endpoint, acquire the
finite original prefix needed to select a cell using [SLH, Theorem 2.2][SLH].
The actual current reply tuple entails that prefix on all old-row/literal
sources. For each remaining nonconstant predicate $u|_a=g$, the selected
cell guarantees that $a$ is originally reached; use the paid delayed
whole-template certificate [SLH, Theorem 55.3][SLH] under the physical prefix
$a$. Its complete actual reply tuple decides both equality and disequality
against $g$, on every originally reached finite subtree, without a shape
promise. Templates are computed from common data and the selected cell.
They are not unknown-source descriptions.

To verify the exact interface, let $H'$ contain $H_0$ and all those actual
current replies. On a reached branch of this converter, every source in
$\mathcal U_R(H')$ has the selected original prefix and the same template
test outcomes, hence satisfies every incoming relation. Conversely any
incoming source giving the tuple belongs to $\mathcal U_R(H')$. The new
full branch fiber is therefore exactly that basic old-row/literal fiber.
A rejected template is represented by its actual mismatching tuple, not
an invented historical event. There are finitely many cells and finite
template supports. Their union provides a uniform finite read bound;
all branch feasibility and subsequent full-row decisions can now use
[SLH, §§61 and 74][SLH]. Incoming bounded solvability restricts to every
branch, and bounded branch services combine with the paid converter using
a finite maximum. Thus this is also an exact existence reduction for this
case. It adds no new mathematical criterion to the predecessor.

A second direct interface is a fully acquired row at another known original
frontier $A$: retained literals determine its entire outside context and
reach guards, and same-epoch records determine its complete partition.
It can be computed from already paid data. To replace the old input by
this row and literal history, **both** full source-fiber inclusions must
hold; the old row and every remaining record must be consequences of the
new input, and conversely. Under that condition only a paid local encoding
change is needed. Dropping old off-task disequalities would violate it.
An ordinary same-epoch equation without such a correspondence does not
by itself constitute an acquired row input.

An unselected finite union of basic fibers is not this paid interface.
For example, the union of the equal-child and unequal-child two-hole
rows is the whole set of original pairs; knowing the separate row on
each part would already decide the unbounded child-equality task. On the
union, pairs $\langle z,z\rangle$ and $\langle z,z'\rangle$, with $z,z'$
agreeing arbitrarily deeply but unequal, obstruct finite-prefix determination
of the two-hole row. The caller has no free branch selector. The stronger
nonreduction statements in §8 concern exact entire fibers.

## 4. Root-to-descendant certificates and the supplied atomic orbit

**Definition 4.1 (root-certificate fragment and orbit suppliers).** A retained
input is in the fragment when it contains a positive record

$$
e=(n,\varepsilon,m,p,=),\qquad p\ne\varepsilon,
\tag{ARH.4.1}
$$

possibly written with its endpoints exchanged. All other old data and
finite signed mixed histories remain arbitrary. Recognition means finding
such a record; it does not require proving that every equivalent presentation
has one.

Use the existing atomic recurrence and transport clock:

$$
\begin{gathered}
T_0=\alpha,\quad T_1=\beta,\quad
T_{j+2}=\langle T_{j+1},T_j\rangle,\qquad \rho^aT_j=T_{j+a},\\
\kappa(\alpha)=0,\quad\kappa(\beta)=1,\quad
\kappa(\langle x,y\rangle)=2+\kappa(y),\quad
\kappa(\rho^a u)=\kappa(u)+a.
\end{gathered}
\tag{ARH.4.2}
$$

These are [TRANSPORT, §§23–24][TRANSPORT] and the atomic supply used by
[SLH, §§2 and 29][SLH]. In particular $\kappa(T_j)=j$, so the $T_j$ are
pairwise distinct. Their reached-subtree formula is

$$
\begin{aligned}
s\ne\varepsilon:\quad
s\in\operatorname{Pos}(T_j)&\Longleftrightarrow j\ge w(s^-)+2,\\
T_j|_s&=T_{j-w(s)}\quad\text{when reached};
\end{aligned}
\tag{ARH.4.3}
$$

at the root the guard is automatic. Nonnegative $j-w(s)$ alone is not
a reach test, as $s=LL,j=2$ shows.

The exact previously established orbit classification used here is the
first conjunct of [SourceTransportCentralizer,
`source_transport_centralizer`][CENTRALIZER]:

$$
\operatorname{Stab}(v):=
[\rho^2v=\langle\rho v,v\rangle]
\quad\Longleftrightarrow\quad
\exists j\ge0, v=T_j.
\tag{ARH.4.4}
$$

Its `Source = FreeMagma Bool` identifies `.of true` with $\alpha$,
`.of false` with $\beta$, and `FreeMagma.mul` with ordered pairing;
`GenealogicalFiberTransport.substitution` is exactly (ARH.1.1).
The classification itself is supply, not a new theorem of this volume.

**Theorem 4.2 (exact acquired root-certificate fiber).** For arbitrary
$n,m\ge0$ and nonempty $p$, the guarded record (ARH.4.1) has a source if
and only if $m=n+w(p)$. More precisely, its entire fiber before intersection
with other retained conditions is empty unless this equality holds, and
otherwise is

$$
\{T_k:k\ge e\},\qquad
 e=\begin{cases}1,&n=0\text{ and the last letter of }p\text{ is }L,\\
                 0,&\text{otherwise}.
   \end{cases}
\tag{ARH.4.5}
$$

This is a consequence of an acquired predicate on all finite original
trees; membership in an orbit is not an additional source promise.

Proof. If $m\le n$, each application of $\rho$ weakly increases node count,
as follows immediately from its two leaf images and distribution over a
pair. But the reached nonroot subtree of $\rho^m u$ has strictly fewer
nodes than $\rho^m u$. It cannot equal $\rho^n u$. This rules out these
epoch orders and agrees with $w(p)>0$.

Suppose $m>n$ and put $d=m-n$. We first establish the interface to
(ARH.4.4). For any finite $v$, if $p$ is reached in $\rho^d v$ and
$v=(\rho^d v)|_p$, then $\operatorname{Stab}(v)$. Use strong induction on
the node count of $v$, keeping $d,p$ fixed. If $p$ is an original reached
address of $v$, let $z=v|_p$, a strict subtree. Original-address transport
[TRANSPORT, (RA.2205)–(RA.2206)][TRANSPORT] gives $v=\rho^d z$.
Consequently $z=(\rho^d z)|_p$: indeed $\rho^d z=v$ and $v|_p=z$.
The induction hypothesis yields $\operatorname{Stab}(z)$. Apply $\rho^d$
to its equation and distribute over pairing to obtain
$\operatorname{Stab}(\rho^d z)=\operatorname{Stab}(v)$.

If $p$ is not an original address of $v$, a known original leaf
$\lambda_b$ blocks it at a strict prefix $a$, so $p=as$ with $s\ne\varepsilon$.
Its reached later endpoint belongs to that leaf sector. By (ARH.4.3) and
the reach guard it is $T_{d+b-w(s)}$ with a nonnegative index. It equals
$v$ by hypothesis. The reverse implication of the supplied (ARH.4.4)
gives $\operatorname{Stab}(v)$. This includes the case that $v$ is a leaf.
The only recursive call was on the strictly smaller $z$, completing the
induction. We have proved a certificate-to-stability bridge, without
reproving the supplied stability classification.

Apply the bridge and (ARH.4.4) to the mathematical tree $v=\rho^n u$.
This changes no physical register. Thus $v=T_j$ for some $j$. By (ARH.4.3),
its record is now exactly

$$
T_j=T_{j+d-w(p)},\qquad j+d\ge w(p^-)+2.
\tag{ARH.4.6}
$$

Index injectivity gives $d=w(p)$. Under this equality the reach condition
is $j\ge2-w(a)$, where $a$ is the last letter of $p$.
The clock gives $j=\kappa(u)+n\ge n$. Injectivity of $\rho^n$ and
$T_j=\rho^nT_{j-n}$ imply $u=T_{j-n}$. Writing $k=j-n$, the two lower
bounds are exactly $k\ge e$ in (ARH.4.5): the last-letter requirement is
one for $L$ and zero for $R$, and a positive $n$ already supplies the one.
Conversely every listed $T_k$ satisfies both the reach guard and equality
in (ARH.4.6). Proposition 2.1 acquires that record by paid traversal at its
two epochs. Every and only these sources produce its positive outcome;
no retained index, size or traversal count is needed. $\square$

The instance $(a,\varepsilon,a+2,R,=)$ selects the entire orbit for every
$a\ge0$. The instance $(0,\varepsilon,1,L,=)$ selects $k\ge1$.
In the first instance the descendant can be born after epoch zero even
when $u$ is a leaf. These are uses of the same guarded statement.

## 5. Effective finite/cofinite indices for the entire retained input

**Definition 5.1 (complete cut and row height).** A finite prefix-free
address set $A$ is complete when every infinite $L/R$ path has a prefix
in $A$. This is decidable from its finite trie: every node before a cut
leaf must have both children in the trie. The empty cut is incomplete;
$\{\varepsilon\}$ is complete. Let $\operatorname{ht}(C)$ be the ordinary
finite height of a context with holes treated as leaves.

For an incomplete $A$ one can compute an address $r$ incomparable with
every member of $A$. For $A=\varnothing$ take $r=\varepsilon$; otherwise
follow a missing branch of its finite trie and extend past the maximum
cut depth. Thus no cut removes or enters any part of the cone at $r$.

**Theorem 5.2 (exact index compiler with all old constraints).** Suppose the
input contains a record from Definition 4.1. There is an effective procedure
which either detects its incompatible epoch/weight condition, or computes
an integer $B\ge e$, a finite $S_0\subseteq\{e,\ldots,B-1\}$ and
$\tau\in\{0,1\}$ such that

$$
U=\{T_k:k\in S\},\qquad
S=S_0\ \cup\ \begin{cases}\{k:k\ge B\},&\tau=1,\\
                              \varnothing,&\tau=0.
             \end{cases}
\tag{ARH.5.1}
$$

Here $P,R,H_0$ and **every** additional finite signed mixed-epoch relation
are arbitrary. All predicates are checked jointly on the same $T_k$.
The procedure detects emptiness too; under the nonempty promise it is
excluded. An infinite tail in (ARH.5.1) denotes all its indices.

Proof. An incompatible designated record gives emptiness by Theorem 4.2.
Otherwise that theorem first restricts all and only possible sources to
$T_k$, $k\ge e$. We give explicit eventual thresholds for every remaining
condition and evaluate the finite part exactly.

For a literal $(a,s,c)$, at

$$
k\ge B_{a,s}:=\max(0,w(s)+2-a)
\tag{ARH.5.2}
$$

its reply on $T_k$ is branch. This inequality guarantees the reach guard
as well as index at least two; for the root it still suffices.
Consequently the eventual truth of that literal is exactly
$c=\mathsf{branch}$. Small indices use the guarded formula of [SLH,
Definition 29.1][SLH]. In particular, absent and repeated replies are
not discarded.

For an endpoint $(a,s)$ define

$$
G_{a,s}=\begin{cases}
0,&s=\varepsilon,\\
\max(0,w(s^-)+2-a),&s\ne\varepsilon.
\end{cases}
\tag{ARH.5.3}
$$

Above $\max(G_{a,s},G_{b,t})$ both endpoints of a relation are reached.
Their whole values are $T_{k+a-w(s)}$ and $T_{k+b-w(t)}$. They are equal
if and only if

$$
a-w(s)=b-w(t).
\tag{ARH.5.4}
$$

For a disequality use the opposite comparison of these integers.
This computes its eventual truth for arbitrary epochs and original or
born endpoints. Below the threshold test both reach guards before either
sign. A negative index is never substituted into $T$.

The old row needs a whole-context check. If $P$ is complete, put

$$
B_P=\max\bigl(\{0\}\cup
        \{w(p^-)+2:p\in P,\ p\ne\varepsilon\}\bigr).
\tag{ARH.5.5}
$$

For every $k\ge B_P$ all cuts are reached. Completeness says their trie
is the entire outside context, with branch nodes at proper prefixes and
holes at $P$. The old hole values are $T_{k-w(p)}$; their complete
partition identifies precisely equal weights $w(p)$. Thus the entire
old row is one effectively constructed constant row on this tail.
Compare it with all of $R$, including its context and complete partition,
to decide the old row's eventual truth. This also covers the root cut.

If $P$ is incomplete, compute an incomparable $r$ as in Definition 5.1.
For

$$
k\ge B_P:=w(r)+\operatorname{ht}(C)+2,
\tag{ARH.5.6}
$$

$r$ is reached in $T_k$ and its entire subtree $T_{k-w(r)}$ survives in
the old outside. The recurrence (ARH.4.2) gives
$\operatorname{ht}(T_j)=j-1$ for $j\ge1$ by induction, with
$\operatorname{ht}(T_0)=0$. This surviving subtree has height greater
than $\operatorname{ht}(C)$, so the old context cannot equal $C$.
The eventual old-row truth is therefore false. For empty $P$, $r$ is
root and this is simply the finite height obstruction for a fully
concrete old row.

Take $B$ at least $e$, $B_P$, all thresholds (ARH.5.2), and all endpoint
thresholds (ARH.5.3). Let $\tau$ be the conjunction of the eventual old-row,
literal and signed relation truth values. For each $e\le k<B$, directly
compute the finite row $R_P(T_k)$ and all literal and guarded signed
predicates; include $k$ in $S_0$ exactly when the entire conjunction holds.
These are finite computations on known candidate trees, not source queries.

Theorem 4.2 excludes every non-orbit source. The finite checks are exact
below $B$, and the displayed thresholds prove constant truth at **every**
$k\ge B$. This proves both inclusions in (ARH.5.1), including all old
repetitions and off-task inequalities. It also proves emptiness exactly
when $S_0=\varnothing$ and $\tau=0$. The finite initial list is not a
finite proxy for the infinite tail. $\square$

## 6. An effective complete-row decision and paid consumer on this fragment

**Theorem 6.1 (full original recut criterion).** Under Assumption 1.3 and
Definition 4.1, let $(S_0,B,\tau)$ be the exact nonempty description from
Theorem 5.2. For every allowed $N$, the following are equivalent:

1. A deterministic effective source-total serial service recovers the
   entire original $R_Q$ with a uniform finite new-read budget.
2. Such a static service exists at $N$.
3. $\tau=0$ or $Q$ is complete.

The third condition is effectively decidable from the common input and
$Q$. In the positive cases one can construct a static consumer and a
finite read bound independent of $N$, with addresses depending on $N$.
In the negative case the obstruction holds on the entire given fiber,
including all additional retained constraints.

Proof. On the whole orbit $\kappa(T_k)=k$. The supplied right-spine reply
formula in [SLH, §2][SLH] gives, at physical epoch $N$,

$$
\begin{array}{c|cccc}
r_{T_{N+k}}(R^a)&\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\
\hline
N+k&<2a&2a&2a+1&\ge2a+2.
\end{array}
\tag{ARH.6.1}
$$

For a known candidate $j$, one paid read at
$R^{\lfloor(N+j)/2\rfloor}$ tests $k=j$: accept just the leaf reply
$\alpha$ if $N+j$ is even, or $\beta$ if it is odd. Equation (ARH.6.1)
proves both directions **on the entire orbit fiber**. This is a use of
the supplied clock, not a new unknown-tree equality port; outside the
orbit, a clock match would not identify a tree.

If $\tau=0$, $S=S_0$ is finite and nonempty. Test candidates in a fixed
order except the last. On a match compute and output the complete
$R_Q(T_j)$; on no match use the last candidate. The exact fiber formula
proves source-total correctness. A sufficient budget is
$|S_0|-1$, including zero for a singleton. All missing original $Q$
addresses and their concrete outside portions are computed from the
identified original tree. No current recut is substituted for it.

Suppose $\tau=1$ and $Q$ is complete. Define

$$
B_Q=\max\bigl(\{0\}\cup\{w(q^-)+2:q\in Q,\ q\ne\varepsilon\}\bigr),
\quad D=\max(B,B_Q),\quad A=S\cap\{0,\ldots,D-1\}.
\tag{ARH.6.2}
$$

The finite $A$ is effectively obtained from (ARH.5.1). For every $k\ge D$
all $Q$ addresses are originally reached. The entire outside is the
complete finite trie of $Q$, with its leaves replaced by the numbered
holes. Its complete partition is

$$
q\sim r\quad\Longleftrightarrow\quad w(q)=w(r).
\tag{ARH.6.3}
$$

Indeed the full hole values are $T_{k-w(q)}$ and $T_{k-w(r)}$ and their
indices are injective. Thus (ARH.6.3) and the trie give one **complete row**
for every source in the allowed tail, even though their unknown hole values
are unbounded.

Test every $j\in A$ by (ARH.6.1). A match selects its exact finite-tree
row; if all reject, the exact source characterization implies $k\ge D$,
so output the complete tail row. The read budget is at most $|A|$.
There is no read in the tail branch beyond those finitely many tests and
no new update. If $Q=\{\varepsilon\}$, its single-hole row is constant
on all sources and can instead be returned with zero reads. Either
consumer handles the boundary, without a minimum-budget claim.

For comparison with the existing template interface, the same positive
construction may test each finite candidate by the delayed whole-tree
certificate of [SLH, Theorem 55.3][SLH]. Summing its $\ell(T_j)$ costs
gives another sufficient bound valid even against arbitrary finite
non-orbit competitors. The smaller displayed bounds here use the actually
retained orbit consequence. Both methods pay their real raw requests.
They are consumers of Theorem 5.2, not replacements for its entire-fiber
proof.

For necessity suppose $\tau=1$ and $Q$ is incomplete. Choose $r$
incomparable with every $q\in Q$. For all sufficiently large allowed
$k\ge B$, $r$ is reached, and the whole subtree $T_{k-w(r)}$ is part of
the **concrete outside** of $R_Q(T_k)$. No $Q$ hole meets that cone. As
$k$ varies through this tail those subtrees are pairwise distinct, giving
infinitely many complete target rows on this very $U$. The inherited
finite-transcript argument in §2 permits at most $4^K$ terminal outputs
for any uniform $K$-read serial service. Such a service cannot output
this infinite image.

There is also a direct full-fiber witness to failure of (ARH.2.2).
For any proposed $h$, choose distinct allowed $k,l$ sufficiently large
that $k,l\ge2h+2$ and the preceding $r$ is reached. At every original
address of length at most $h$, both sources reply branch by (ARH.4.3).
Their full outside subtrees at $r$ differ. They satisfy all retained
conditions because both belong to the exact tail of (ARH.5.1), yet their
complete $Q$ rows differ. This witness excludes static and real serial
services by (ARH.2.3). It does not discard any old disequality.

We have proved $3\Rightarrow2\Rightarrow1\Rightarrow3$. All finite
candidate construction, row computation and integer/trie work terminate.
The tests use the same register at $N$. A test for $j$ has physical address
length $\lfloor(N+j)/2\rfloor$; the length sum is the sum over actual
tests. Template alternatives have exactly the separately stated address
costs in [SLH, §55][SLH]. Computation, stored descriptions, installation,
entry, certification, archives and complete output are additional costs.
These statements bound new raw calls only, and make no general minimax
or joint-resource optimality assertion. $\square$

Outputting the row does not create a new access cut that forgets
$R,H_0,H_{\rm rel}$ or the new actual replies. Subsequent source fibers
still include every accessible field, as in [SLH, Proposition 68.3 and
(SLH.72.5)][SLH]. In particular, the positive tail branch is justified by
the retained relation, not by a fabricated acquisition of its unknown
whole trees.

## 7. A native four-hole complete-row consumer

**Proposition 7.1 (one read on an entire acquired relation fiber).** Take

$$
\begin{gathered}
P=\{L,R\},\quad C=\langle\square_1,\square_2\rangle,
\quad \pi=\{\{1\},\{2\}\},\quad H_0=\varnothing,\\
H_{\rm rel}=\{(0,\varepsilon,1,L,=)\},\quad
Q=\{LL,LR,RL,RR\},\qquad N\ge1.
\end{gathered}
\tag{ARH.7.1}
$$

The entire input fiber is $U_\star=\{T_j:j\ge2\}$. Its complete original
$Q$ row is one of the following three rows:

$$
\begin{array}{c|c|c|c}
j&\text{reached original cuts}&\text{outside context}&\text{partition}\\
\hline
2&\varnothing&\langle\beta,\alpha\rangle&\varnothing\\
3&LL,LR&\langle\langle\square_1,\square_2\rangle,\beta\rangle
 &\{\{1\},\{2\}\}\\
\ge4&LL,LR,RL,RR
 &\langle\langle\square_1,\square_2\rangle,
                 \langle\square_3,\square_4\rangle\rangle
 &\{\{1\},\{2,3\},\{4\}\}.
\end{array}
\tag{ARH.7.2}
$$

For each allowed $N$, both static and serial minimum new-read budgets
for this particular complete-row task are exactly one. Removing the
relation record, while keeping the same old row and same $Q$, leaves
no uniform finite-read service.

Proof. Theorem 4.2 gives $j\ge1$ before the old-row intersection.
$T_1$ is a leaf and fails that old row; for every $j\ge2$, the root
children are $T_{j-1},T_{j-2}$, which are distinct. Thus exactly
$j\ge2$ remain. In particular the old disequality has been enforced,
not dropped. Proposition 2.1 gives a legal paid acquisition: retain the
acquired epoch-zero root description until after one real update, acquire
the whole current subtree at $L$, compare the two descriptions, and
then perform the stipulated full cut. Continuing to $N$ adds actual paid
updates. Neither $j$ nor either tree description is retained.

For $j=2$, both original children are leaves, so every $Q$ address is
absent. For $j=3$, only the original left child is a pair and the right
child is $T_1=\beta$. For $j\ge4$ all four cuts are reached, and their
whole values in the displayed order are

$$
T_{j-2},\quad T_{j-3},\quad T_{j-3},\quad T_{j-4}.
\tag{ARH.7.3}
$$

Index injectivity gives the full partition in (ARH.7.2), including the
cross-parent repeated class. This proves the three complete rows.

At the actual current tree $T_{N+j}$, read just

$$
R^{\lceil(N+2)/2\rceil}.
\tag{ARH.7.4}
$$

If $N$ is even, replies $\alpha,\beta,\mathsf{branch}$ select,
respectively, the first, second and third rows of (ARH.7.2); absent is
unreachable. If $N$ is odd, absent selects the first, $\alpha$ the
second, and $\beta$ or branch the third. This table is the direct
substitution of the address exponent into (ARH.6.1), so it is valid for
all $j\ge2$, not just the first few sources. The actual read selects a
whole row, not merely an equality bit. Its address length and all local
row construction/output work remain paid.

Zero new reads leave the same deterministic control on $T_2$ and $T_3$,
even if real updates are executed without observations. Their required
complete rows differ, excluding zero reads in both service classes.
Together with (ARH.7.4) this proves the asserted example-specific minimum.

Finally remove the relation. For any $h$, choose distinct finite trees
$z,z'$ with the same original replies through depth $h$. Such a pair is
obtained by a full binary tree with leaves deeper than $h$ and a change
of one deepest label. The two original sources

$$
u=\langle\langle z,z\rangle,\alpha\rangle,
\qquad v=\langle\langle z,z'\rangle,\alpha\rangle
\tag{ARH.7.5}
$$

have that same two-hole old row: the original left child is a pair and
therefore differs from the right leaf. They agree through original depth
$h$. Their only reached $Q$ cuts are $LL,LR$; these are equal in $u$
and unequal in $v$, with the same concrete right outside $\alpha$.
Thus their complete rows differ. [SLH, Theorem 74.4][SLH], or its inherited
prefix obstruction in §2, excludes a uniform finite serial budget on
this whole basic fiber. Its full target image is nevertheless finite: each
original root child is either one of two concrete leaves or a pair whose
two children are holes; there are finitely many such contexts and
partitions of at most four holes. Thus finite target image alone does not
suffice. The change in solvability comes from the actually retained
relation while the full-row task is unchanged. $\square$

## 8. Limits of exact compilation to ordinary old inputs

**Definition 8.1 (ordinary coordinate-preserving cell).** An ordinary cell
in tree coordinates $(x,y)$ is a relation defined by

$$
\exists z_1,\ldots,z_s\in\mathcal T\quad
 \bigwedge_i A_i(x,y,\mathbf z)=B_i(x,y,\mathbf z)
 \ \land\ \bigwedge_j C_j(x,y,\mathbf z)\ne D_j(x,y,\mathbf z),
\tag{ARH.8.1}
$$

where every expression is a finite free term over the original two
leaves and ordered pair. Finite ground tree parameters are allowed.
There is no interpreted $\rho$ or encoded replacement of the source
coordinates. Arbitrary existential auxiliary finite-tree variables are
allowed. Finite unions of these cells are the compilation class below.

**Theorem 8.2 (an acquired morphism graph has no finite ordinary compilation).**
The relation

$$
\mathcal G=\{(x,y)\in\mathcal T^2:x=\rho(y)\}
\tag{ARH.8.2}
$$

is not a finite union of ordinary cells. Adding finite literal-history
conditions at fixed epochs to those cells does not change the conclusion.
It follows that a coordinate-preserving finite ordinary-cell normalization
cannot handle every actually acquired mixed-epoch input of Definition 1.2.
This is a representation obstruction, not an undecidability assertion.

Proof. Suppose a finite union equals $\mathcal G$. Every nonempty disjunct
is then contained in $\mathcal G$. Apply the ordinary finite-term
unification supplied in [SLH, Theorem 74.4, proof (ii)][SLH] to that
disjunct's equations. This application involves only free terms, so
occurs-check and the full solved-substitution correspondence apply.
Discard inconsistent disjuncts. In a nonempty one, the solved substitution
expresses

$$
x=A(\mathbf z),\qquad y=B(\mathbf z)
\tag{ARH.8.3}
$$

in the remaining free variables, subject only to finitely many residual
ordinary disequalities. This includes originally existential variables
and any free coordinate left by the substitution.

Fix a satisfying assignment. Suppose a variable $z$ occurs in $B$.
Hold all other variables at their assigned finite trees. By the
one-variable fact in [SLH, Theorem 74.4, proof (ii)][SLH], each remaining
disequality, being true at the fixed assignment, excludes at most one
replacement value for $z$. Thus all but finitely many finite trees can
replace $z$ while staying in this same disjunct.

Let $a\ge0,b>0$ count occurrences of $z$ in $A,B$. Let $w_j$ be any fixed
choice of a tree with exactly $j$ leaves all labeled $\alpha$, for each
$j\ge1$. Infinitely many of these pairwise distinct trees avoid the
finite excluded set. With all other variables fixed, write $c_\alpha,
c_\beta,d_\alpha,d_\beta$ for their constant contributions to the two
leaf counts. Then

$$
\begin{aligned}
\#_\alpha A(w_j)&=aj+c_\alpha,&
\#_\beta A(w_j)&=c_\beta,\\
\#_\alpha\rho(B(w_j))&=d_\beta,&
\#_\beta\rho(B(w_j))&=bj+d_\alpha+d_\beta.
\end{aligned}
\tag{ARH.8.4}
$$

The second line uses exactly the actual images of $\alpha,\beta$ in
(ARH.1.1). Containment in $\mathcal G$ requires equality of both counts
for unbounded $j$. The alpha equality forces $a=0$; the beta equality
then, and in fact already, contradicts $b>0$. Hence $B$ contains no free
variable. This disjunct fixes one $y$, and containment in $\mathcal G$
fixes $x=\rho(y)$ as well. Each nonempty disjunct contains just one pair,
whereas $\mathcal G$ has infinitely many. This is the contradiction.

For the literal extension, physical-address locality (SLH.74.7) makes
every fixed finite history depend on a finite original prefix in its
source coordinates. Enumerate the finitely many such prefix patterns.
Each is described by ordinary equations with fresh frontier variables;
the literal outcomes are constant on a pattern. Distribute this finite
disjunction into (ARH.8.1). The result is still a finite union of ordinary
cells, already excluded. A fixed old row likewise has the ordinary
context-filling equations and all its class disequalities (ARH.1.2).

To exhibit the graph as an actual input, take

$$
P=\{L,R\},\quad C=\langle\square_1,\square_2\rangle,
\quad\pi=\{\{1\},\{2\}\},\quad H_0=\varnothing,
\quad H_{\rm rel}=\{(0,L,1,R,=)\}.
\tag{ARH.8.5}
$$

Writing the original tree $\langle x,y\rangle$, this record says exactly
$x=\rho(y)$. The old inequality adds no restriction, since
$\kappa(\rho(y))=\kappa(y)+1$ implies $\rho(y)\ne y$. Both endpoints
are original and reached. Proposition 2.1 acquires them by paid traversal,
one actual update, finite comparison and the complete cut. Its entire
fiber is therefore $\{\langle\rho(y),y\rangle:y\in\mathcal T\}$.
An ordinary description of this original-source fiber would give an
ordinary description of $\mathcal G$ by substituting
$u=\langle x,y\rangle$. It is impossible by the preceding proof. $\square$

The theorem rules out a route that simply turns all morphic constraints
into finitely many ordinary cells and then invokes the unchanged ground
binding test of [SLH, §74][SLH]. It does not exclude a finite description
which retains $\rho$, a richer automaton with a proved correspondence,
or another effective representation. It says nothing against a particular
constant recut on (ARH.8.5); for instance its $Q=P$ row is already retained.

**Theorem 8.3 (infinite orbit fibers cannot be exact finite old-input unions).**
Let $\mathcal O=\{T_k:k\ge0\}$. Every basic old-row/literal-history fiber
$\mathcal U_{R'}(H')$ contained in $\mathcal O$ is finite, allowing its
own arbitrary finite original cut $P'$. Hence no infinite fiber in
Theorem 5.2 with $\tau=1$ is a finite union of such basic fibers.

Proof. Use the exact finite prefix decomposition [SLH, Definition 74.2
and (SLH.74.8)][SLH] for $R',H'$. If this basic fiber were infinite,
some nonempty cell would have a residual variable $x$ occurring in its
source term $W$. Otherwise each of finitely many ground cells would give
only one source. The only remaining constraints in a cell are its full
finite old disequality list $\Delta$; its literal replies are already
fixed by the prefix.

Fix one feasible valuation and every variable except $x$. The supplied
one-variable free-term fact again says that each true disequality excludes
at most one new value of $x$. Let $F$ be their finite union of excluded
values. Choose an integer $M\ge2$ with $2^M>|F|+1$, fix a full binary
shape with $M$ leaves, and vary its two leaf labels. At least two distinct
such trees $z,z'$ avoid $F$. Their substitutions into $W$ yield different
original sources: at an occurrence of $x$ their entire subtrees differ.
Both substitutions preserve the old row, every old inequality and all
literal replies. Their total leaf counts are the same,

$$
A+cM\ge2,
\tag{ARH.8.6}
$$

where $c\ge1$ is the number of occurrences of $x$ in $W$ and $A\ge0$
is the fixed contribution from the rest of $W$.

By (ARH.4.2), the leaf counts of $T_0,T_1$ are one, and
$\ell(T_{j+2})=\ell(T_{j+1})+\ell(T_j)$. They are strictly increasing
from $T_2$ onward. There is at most one orbit tree of each leaf count
at least two. The two distinct legal substitutions with (ARH.8.6) cannot
both lie in $\mathcal O$, contradicting containment. Thus every such
basic fiber is finite, and a finite union cannot equal an infinite
subset of $\mathcal O$. $\square$

Both representation obstructions have a paid-interface consequence.
Suppose a deterministic source-total converter with a common $K$ new
reads outputs only an ordinary finite description in the same original
coordinates, or only a basic old-row/literal input, and promises that each
terminal description's full semantic fiber over **all** $\mathcal T$
is exactly its incoming branch fiber. Assume no relation, morphic domain
promise or other source-bearing information survives outside that
description. The finite reply-tree supply in §2 gives only finitely many
terminal descriptions, even with serial updates. Their fibers cover the
incoming domain and are contained in it. For (ARH.8.5) this contradicts
Theorem 8.2; for an infinite orbit fiber and basic outputs it contradicts
Theorem 8.3.

The requirement “over all $\mathcal T$” is essential. Describing a branch
as a basic fiber *intersected with the retained morphic promise* is a
richer representation, not the forbidden conversion. Unbounded paid
acquisition of the actual tree and task-specific output of a constant
row are also not excluded. Theorem 8.3 shows why the infinite-tail
consumer of Theorem 6.1 is not merely a finite exact selection of already
solved literal-history inputs.

## 9. Mathematical scope, suppliers and remaining obligations

**Definition 9.1 (the unresolved unrestricted decision).** For arbitrary
finite $R,H_0,H_{\rm rel},Q$ satisfying Assumption 1.3, the unrestricted
question remains an effective exact decision of
$\exists h\,\operatorname{PrefDet}(U,Q,h)$, together with a paid
source-total full-row consumer in the positive case, or an exact negative
theorem covering the proposed unrestricted input class. In the guarded
representation of Proposition 3.2 this requires reasoning about all
joint finite-tree solutions of the coupled signed morphic equations,
including concrete outside variation and every target subtree comparison.

Decidable membership of a single concrete tree, ordinary unification of
the same-epoch part, an emptiness result for another constraint language,
or a search that terminates only after a suitable prefix bound is supplied
does not settle this question. Theorem 8.2 rules out one finite ordinary
compilation; it does not prove the unrestricted question undecidable.
Theorem 6.1 decides the recognized root-certificate fragment with arbitrary
additional histories, without claiming that the fragment exhausts all
solvable inputs. Equation (ARH.2.3) already establishes static/serial
**existence** equivalence under the stated contract; general minimum raw
budgets and equality of those minima remain unresolved. Proposition 7.1
settles its own one-read example only.

The source-relative additions are the paid signed-history and guarded
endpoint correspondences, the root-certificate interface to the supplied
stability classification, the exact finite/cofinite full retained fiber,
its complete-row decision and consumer, and the two precise representation
obstructions. These are `repo-derived` ordinary mathematical deductions.
The atomic orbit classification, historical decoder, template certificates,
Hall matching, finite-term unification and finite-transcript method are
reused suppliers. No global priority claim is made.

The relevant supplier boundaries are as follows, attached to the
correspondences they support.

- [SLH, §§59–62][SLH] supply actual old-row acquisition, full class
  inequalities, local transport and complete-state continuation. [SLH,
  §§29, 55, 69 and 74–75][SLH] supply guarded literal semantics, delayed
  templates, finite historical VALUE minimax, and the general literal-only
  full-row criterion. [SLH, §§70–73][SLH] keep their exact multi-hole
  ancestor and joint-extension conditions. None is replaced by a renamed
  ground-binding algorithm here.
- [CENTRALIZER][CENTRALIZER] supplies (ARH.4.4), with the exact source
  identification in Definition 4.1. [TRANSPORT][TRANSPORT] supplies the
  actual image parser, injectivity, original-address transport, clock and
  guarded atomic subtree formulas. Their uses here are ordinary theorem
  applications; they do not by themselves supply an acquired mixed-history
  decision or certify a physical cut.
- [ActualTreeReadoutAcquisition][ACQUISITION], `source_foundation` and
  `acquisition_foundation`, supplies the existing leaf-rigidity and finite
  traversal correspondence consumed through [SLH, §§53, 55 and 59][SLH].
  Its original static Boolean policy is not a serial full-row service.
  The finite-record/counting and realized-image factor suppliers named in
  [SLH, §75][SLH] likewise retain their own hypotheses; finite image alone
  does not ensure bounded observation, as Proposition 7.1 without its
  relation demonstrates.
- Finite free-term unification is `literature-attested` by
  [Martelli–Montanari, *An Efficient Unification Algorithm*, ACM TOPLAS
  4(2), 258–282][MM]. The exact finite occurs-check and solved-substitution
  argument used here is already supplied in [SLH, §74, proof (ii)][SLH].
  It is applied only to ordinary free terms in Theorems 8.2–8.3.
- [Hall, *On Representatives of Subsets*][HALL] and the pinned mathlib
  [`Finset.all_card_le_biUnion_card_iff_existsInjective'`][MATHHALL]
  supply the finite matching step used by [SLH, §61][SLH]. Its finite
  index set is the old class set, and values are finite trees with
  decidable equality. [Pinned `FirstOrder.Language.Term` and
  `Term.subst`][SYNTAX] supply syntax and substitution, not a solver
  for interpreted $\rho$ constraints. These library statements do not
  establish an unproved mixed-epoch correspondence.
- [Comon et al., *Tree Automata Techniques and Applications*, §1.4][TATA]
  is the `literature-attested` tree-homomorphism background: (ARH.1.1)
  is a fixed nondeleting linear ranked homomorphism. Injectivity here
  comes from the specific parser, not from linearity. Ordinary image
  or preimage language closure does not compare two coupled unknown
  mixed-epoch endpoint trees.
- [Barguñó–Creus–Godoy–Jacquemard–Vacher, *Decidable Classes of Tree
  Automata Mixing Local and Global Constraints Modulo Flat Theories*,
  LMCS 9(2:1)][TABG] supplies decidable emptiness in its stated automaton
  language. Its fixed old-hole use is already supplied in [SLH, §61][SLH].
  No representation of arbitrary coupled $\rho$ constraints in that
  language, nor a decision of (ARH.2.2), follows merely from this citation.
- [Marshall–Meadows–Narendran, *On Unification Modulo One-Sided
  Distributivity: Algorithms, Variants and Asymmetry*, LMCS 11(2:11)][OSD]
  studies a different specified equational theory. Its homomorphism
  methods are a possible comparison, but no transfer to the fixed two
  leaf images, finite original ground sources, signed guards and full-row
  boundedness problem is asserted. No complexity claim is imported.

**Definition 9.2 (retained stochastic and further deterministic questions).**
The original fixed-prior stochastic $j_c$ zero/positive alternative,
joint full-law calibration, finite exact stochastic optimum, and
effective charged stochastic attainment keep their original standards.
[Fixed full-residual null, Theorem 4.1 and Corollary 5.2][NULL] excludes
the specified 155-coefficient separator family. Its full-marginal and
omitted-residual distinctions prevent either $j_c=0$ or $j_c>0$ from
following. None of the deterministic rows in this volume supplies a
compatible full-law pair, a stochastic optimum, or an exact paid sampler.
The finite/cofinite orbit index description is not a stochastic
finite-law replacement.

For the unrestricted deterministic question, epoch-potential methods for
coupled records and the separate full three-hole root-record family remain
candidate increments. No classification of either is assumed here and
neither substitutes for Definition 9.1. A partial solution on the present
recognized fragment does not complete the persistent self-calibration
programme.

[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[TRANSPORT]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[CENTRALIZER]: ../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[ACQUISITION]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[MM]: https://doi.org/10.1145/357162.357169
[HALL]: https://doi.org/10.1112/jlms/s1-10.37.26
[MATHHALL]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean
[SYNTAX]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/ModelTheory/Syntax.lean
[TATA]: https://inria.hal.science/hal-03367725/document
[TABG]: https://arxiv.org/abs/1302.6960v2
[OSD]: https://arxiv.org/abs/1503.06687v2
[NULL]: RECURSIVE_RELATIONAL_OBSERVATION_FIXED_FULL_RESIDUAL_NULL.md

## 追加锚（本行以下为增补区）
