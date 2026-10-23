# Native response phases and unrestricted prescribed-state synthesis

## 1. The original acquired task and its supplied interfaces

**Assumption 1.1 (the entire CAR task).** Fix a finite acquired input of
[CAR, Assumption 1.1 and Definition 3.1][CAR], with nonempty cycle-covered
fiber $D$, authenticated common entry epoch $N$, and original target cut
$Q$. The native sources are nonempty finite ordered free binary trees
over $\alpha,\beta$. Their one forward operation is

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{NPS.1}
$$

The fiber consists of **all** original sources with the specified complete
old row, literal history and signed relation history. A signed relation
between subtrees at two recorded epoch/address pairs requires both
addresses to be reached, for either equality or disequality. Repeated
old classes, distinct-class inequalities, and records outside the target
remain constraints on the same source. No further rank, size, parity or
finite-support promise is part of this assumption.

The required output is $R_Q(u)$ at the original epoch: its whole concrete
marked exterior, its reached original holes with their canonical
numbering, and the complete equality partition of their whole subtrees.
An absent original target address is not turned into a hole by subsequent
growth. The retained input was acquired with its original payment,
permissions, authentication, retention and complete-access-cut hypotheses.
In particular, the accessible common input contains no further
source-dependent cache, pointer, timing information or selector.

The controller is exactly [CAR, Definition 11.1][CAR], the native instance
of [Continuation II, Definitions 26.1–26.2][CII]. It has a nonempty finite
state set $E$, common initial state $e_*$, and one fixed instruction at
each state. A read state contains one finite literal word over $\{L,R\}$
and four fixed response successors; an update state has one successor
and applies $\rho$ once to the same physical register; a halt contains
one concrete complete row. Reads leave the register unchanged. Absent
reads are legal and counted. Halts are absorbing. All online program
positions, retained replies, mutable selectors and output distinctions
belong to $E$. The plant register is not an additional readable control
state, and the epoch is not a clock available to the controller.

The operations have the stipulated synchronous whole-word and whole-row
semantics. The size of fixed words, fixed output rows and retained common
input is charged as installation separately from $|E|$. There is no
bound on reads, updates, address lengths or installation in this volume's
prescribed-$K$ question. Each installed word and row is nevertheless
finite, and every admitted source must actually halt.

**Definition 1.2 (the arithmetic interface being reused).** Use the finite
chart family and bijection of [CAR, Theorem 3.2][CAR]:

$$
\coprod_{\eta\in\mathcal A}
 \{\mathbf n\in\mathbb N^{d_\eta}:
                  \operatorname{Adm}_\eta(\mathbf n)\}
 \xrightarrow[\text{bijection}]{\ \Theta\ }D,
\qquad
(\eta,\mathbf n)\longmapsto\Theta_\eta(\mathbf n).
\tag{NPS.2}
$$

Here $\mathbb N$ includes zero; $d_\eta=0$ is permitted. The predicates
$\operatorname{Adm}_\eta$ and
$\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)$ are those of
[CAR, Lemma 4.1][CAR]. The latter means precisely

$$
R_Q(\Theta_\eta(\mathbf n))
 =R_Q(\Theta_\theta(\mathbf m)).
\tag{NPS.3}
$$

Both predicates are effective first-order Presburger formulas. Admission
retains the entire acquired input, including both endpoint guards of
every signed record. The chart inverse is effective on a supplied
concrete source; no chart selector or source tuple is thereby installed
as an observation.

Use the physical descriptors of [CAR, Definition 6.1 and Theorem 6.2][CAR].
For the common finite skeleton depth $H$, their types are the finitely
many literal words of length at most $H$, and the finitely many choices
$(z,b)$ with $|z|=H$ and $b\in\{L,R\}$. A descriptor of the latter
type has unbounded natural parameters $(t,l)$ satisfying

$$
l\ge1,\qquad
l-1\le t-\omega(b)\le2(l-1),
\qquad \omega(L)=1,\quad\omega(R)=2.
\tag{NPS.4}
$$

This notation denotes ordinary integer inequalities, equivalently
addition inequalities over naturals. A long descriptor describes a word
$zs$ with suffix length $l$, suffix weight $t$ and last letter $b$.
Write $\operatorname{Valid}(\delta)$ for its supplied validity formula;
a short literal descriptor is automatically valid. Every finite word
has a descriptor, and every valid descriptor has an effectively
constructible single literal realization $p(\delta)$. For the four-reply
alphabet $\mathcal C=\{\mathsf{absent},\alpha,\beta,\mathsf{branch}\}$,
the supplied predicates satisfy

$$
\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta)
\quad\Longleftrightarrow\quad
r_{\rho^j\Theta_\eta(\mathbf n)}(p)=c
\quad\text{for every realization }p\text{ of }\delta.
\tag{NPS.5}
$$

This equivalence holds on every admitted chart tuple, at every natural
epoch, with the **same physical word** on the whole chart union. It
includes actual absence and the endpoint condition for a suffix ending
in $L$. Its formulas are Presburger jointly in source coordinates,
epoch and descriptor parameters. These are supplied interfaces; their
chart, normalization and word-realization proofs remain in CAR.

**Definition 1.3 (the local decision).** For $K\in\mathbb N$, let
$\mathsf{Native}_K(D,N,Q)$ assert existence of a table under Assumption
1.1 with $|E|\le K$ that, from $(\rho^N u,e_*)$, halts with the
complete row $R_Q(u)$ for every $u\in D$. All quantification over tables
allows arbitrary finite installation. The native-control supplier
[CAR §§11–14][CAR] is cited at immutable revision
`ac159239a7c999bf163bd244eb18ba0a49c0de81`, the separately published
[PR15494][CAR-PR] source. Its per-installed-table bound and its bounded
synthesis theorems are used only at their own scopes. The question here
is the unrestricted prescribed-state regime identified in its
Definition 14.2.

## 2. Describing the unchanged instruction graph

**Definition 2.1 (finite design choices).** For $1\le s\le K$, a graph
$G$ consists of $E=\{0,\ldots,s-1\}$, $e_*\in E$, a partition into
read states $E_R$, update states $E_U$ and halt states $E_H$, and the
successors required by Assumption 1.1. At this point words and halt rows
are unspecified. There are finitely many such graphs, including graphs
with unreachable states and graphs with no halt. Put $r=|E_R|$.

Choose one descriptor type for each $e\in E_R$. Write
$\boldsymbol\delta=(\delta_e)_{e\in E_R}$ for the resulting tuple of
numeric parameters and fixed types, and
$V_G(\boldsymbol\delta)=\bigwedge_{e\in E_R}
\operatorname{Valid}(\delta_e)$. The graph, all types and all numeric
parameters are common design data, chosen before source quantification.
Distinct read states may contain identical words; descriptors need not
be distinct. There is only one descriptor for every visit to a given
state.

**Definition 2.2 (fixed-response paths).** For a vector
$v\in\mathcal C^{E_R}$, form the partial function $F_v$ on $E$ by
selecting the $v(e)$ successor at a read state and the sole successor
at an update state. Give its edge weight zero or one, respectively.
There is no outgoing edge at a halt: this graph describes actions up to
first halt, rather than an absorbing self-loop after termination.

Let $P_v(x,y,d)$ mean that a finite path of this partial function starts
at $x$, ends at $y$, and contains exactly $d$ update edges. Its edges
are all nonhalt actions. The empty path is included when $x=y,d=0$.
This is an exact endpoint-and-update-count relation, not a sum of
independently selected cycles.

Its effective arithmetic description is the standard unary regular-path
specialization: read edges are epsilon transitions and update edges
consume one unary letter; see [To, §§1–2][TO]. For this functional graph
one can obtain the formula directly from its unique orbit. Iterate from
$x$ until halt or the first repeated vertex. Before a repetition, each
occurrence of $y$ gives a fixed update count $a$. If $y$ occurs on the
resulting simple cycle, let $a$ be its first update count and let $b$ be
the number of update edges on that cycle. Its later occurrences give
exactly

$$
d=a+bz,\qquad z\in\mathbb N.
\tag{NPS.6}
$$

Take the finite disjunction of these singleton and progression formulas;
if $y$ never occurs the formula is false. This is the usual finite
orbit construction, with the native edge weights specified. Every $a,b$
is a computed integer of $G,v,x,y$, and $0\le b\le s$. In particular
$b$ is not a source, descriptor or epoch variable. A zero-update cycle
contributes the singleton $d=a$, with no division by zero and no exit
from that cycle. A target halt can only occur on the finite terminating
orbit, since it has no successor. Formula (NPS.6) therefore constructs
$P_v$ effectively in Presburger arithmetic, without invoking a general
parametric-counter reachability decision.

**Definition 2.3 (crossing by a real final update).** Write
$\operatorname{succ}_U(q)$ for an update successor and put

$$
X_v(x,y,d)\ \Longleftrightarrow\
\bigvee_{\substack{q\in E_U\\\operatorname{succ}_U(q)=y}}
 \exists c\in\mathbb N\,
       \bigl(d=c+1\ \land\ P_v(x,q,c)\bigr).
\tag{NPS.7}
$$

Thus $X_v$ describes a path with positive update count whose **last
action is an actual update**. Suppose its starting epoch is $a$ and
$a+d=b>a$. Before its final edge the accumulated update count is at
most $d-1$, because every edge weight is nonnegative and the final edge
still contributes one. All preceding actions, including that last
update at epoch $b-1$, therefore start in $[a,b)$. The endpoint is at
epoch $b$. This is exactly the endpoint convention needed when a reply
vector changes at $b$; no read at $b$ may still use the old vector.

The relation counts updates, not elapsed instructions. Its path can
contain arbitrarily many actual reads. Those actions remain in the
finite path witness and in the native execution it describes.

## 3. Exact unbounded halting support

**Definition 3.1 (phase guards and terminal support).** With the fixed
design of §2, define the interval guard

$$
\begin{aligned}
G_{\eta,v}(\mathbf n,\boldsymbol\delta;a,b)
\ \Longleftrightarrow\
\forall j\in\mathbb N\quad
 a\le j<b\ \Longrightarrow\
 \bigwedge_{e\in E_R}
       \operatorname{Reply}_{\eta,v(e)}(\mathbf n,j,\delta_e).
\end{aligned}
\tag{NPS.8}
$$

All read states occur in this mathematical guard, even if a particular
execution never visits them. No additional physical reads are implied.
One original tuple $\mathbf n$ supplies every conjunct and every epoch.

For $h\in E_H$ define
$\mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta)$ as follows. Take a
finite disjunction over

$$
1\le m\le3r+1,\qquad
v_0,\ldots,v_{m-1}\in\mathcal C^{E_R},\qquad
x_1,\ldots,x_{m-1}\in E,
\tag{NPS.9}
$$

and put $x_0=e_*$. Within each disjunct existentially quantify natural
$t_0,\ldots,t_m,d_0,\ldots,d_{m-1}$ and impose

$$
\begin{gathered}
N=t_0<t_1<\cdots<t_m=J+1,\\
\bigwedge_{i=0}^{m-1}
       G_{\eta,v_i}(\mathbf n,\boldsymbol\delta;t_i,t_{i+1}),\\
\bigwedge_{i=0}^{m-2}
 \bigl(t_i+d_i=t_{i+1}\ \land\
       X_{v_i}(x_i,x_{i+1},d_i)\bigr),\\
t_{m-1}+d_{m-1}=J\ \land\
       P_{v_{m-1}}(x_{m-1},h,d_{m-1}).
\end{gathered}
\tag{NPS.10}
$$

The conjunction with upper index $m-2$ is empty when $m=1$.
Define the eventual support

$$
H_{\eta,h}(\mathbf n;\boldsymbol\delta)
 \ \Longleftrightarrow\
 \exists J\in\mathbb N\,
       \mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta).
\tag{NPS.11}
$$

The delimiter $J+1$ makes the terminal epoch part of the last guarded
interval. It is not an executed update beyond halt. These formulas
allow arbitrary phase lengths. They need not require adjacent vectors
to be distinct or phases to be maximal; the exact guards suffice.

**Theorem 3.2 (native execution and phase description in both directions).**
For every fixed finite graph and descriptor-type choice, the formulas
(NPS.10)–(NPS.11) are effectively Presburger. For every valid common
descriptor valuation, every admitted $(\eta,\mathbf n)$, every halt
$h$ and every $J\in\mathbb N$,

$$
\begin{aligned}
\mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta)
\quad\Longleftrightarrow\quad
&\text{the unchanged literal graph on }
u=\Theta_\eta(\mathbf n)\text{ from epoch }N\\
&\text{first halts at state }h\text{ at actual epoch }J.
\end{aligned}
\tag{NPS.12}
$$

Any realizing word may be installed once at each read state. Halt rows
do not enter this arrival statement. The correspondence preserves every
actual control visit, response and unit update. In particular
$H_{\eta,h}$ is exact finite-halting support, with no action horizon.

Proof. First establish the finite number of relevant phases on an
arbitrary finite native source, without an atomic-source assumption.
Reuse reached-subtree transport
[NativeDepthPatterns, `original_present_transport`][TRANSPORT]. Applied
to the actual tree $\rho^j u$ at any epoch where $p$ is reached, it gives

$$
(\rho^{j+a}u)|_p=\rho^a((\rho^j u)|_p),
\qquad a\in\mathbb N,
\tag{NPS.13}
$$

and persistence of that reached address. This application is made only
after reach; it does not transport an absent original subtree. The
root transition of a reached subtree, from (NPS.1), follows
$\alpha\to\beta\to\mathsf{branch}\to\mathsf{branch}$ or a suffix of
that chain. Before first reach the reply is absent. Consequently
$j\mapsto r_{\rho^j u}(p)$ is nondecreasing for the order

$$
\mathsf{absent}<\alpha<\beta<\mathsf{branch}.
\tag{NPS.14}
$$

It changes at most three times. Give these four values ranks $0,1,2,3$.
For the $r$ fixed installed words, the sum of reply ranks increases
whenever the vector changes and can increase by at most $3r$. Thus on
any integer interval $[N,J]$ the vector has at most $3r+1$ maximal
nonempty constant intervals. Simultaneous changes count once; duplicate
words do not invalidate this bound. This bounds the number of intervals,
not their durations or the number of actions in them.

For the forward implication from actual execution to description, take
its finite trace ending at $h,J$. Every integer epoch from $N$ to $J$
is visited, because updates increment by exactly one and reads do not
change the epoch. Partition that whole interval by the vector just
described. Set the last right endpoint to $J+1$. At each internal
boundary $t_{i+1}$ cut the trace immediately after the actual update
that first enters that epoch. Let $x_{i+1}$ be its destination state.
Every action before this cut within the segment uses vector $v_i$.
Its path is a path of $F_{v_i}$, its update count is $d_i$ with
$t_i+d_i=t_{i+1}$, and its final action is the crossing update. Hence
it satisfies $X_{v_i}$. The last segment ends at $h$ with update count
$d_{m-1}$ and $t_{m-1}+d_{m-1}=J$, so satisfies $P_{v_{m-1}}$.
Equation (NPS.5) gives every interval guard. There are at most the
number of segments allowed by (NPS.9). This supplies all witnesses in
(NPS.10), on the same original source throughout.

Conversely suppose (NPS.10) holds. By the exact path construction of
§2, each $X$ witness expands to a finite $F_{v_i}$ path ending in its
specified update; the last $P$ witness expands to a finite path ending
at $h$. Concatenate them at the shared states $x_i$. On an internal
segment the argument after (NPS.7) places every action's starting epoch
in $[t_i,t_{i+1})$. On the final segment nonnegative edge weights and
total update count $d_{m-1}$ place all action-start epochs between
$t_{m-1}$ and $J$, inclusive. The final guard extends through $J$.

Induct on the actions of this finite concatenation. At its start the
register is $\rho^N u$ and control is $e_*$. At a read, (NPS.8) and
(NPS.5) supply exactly the real literal reply on that register, so the
installed response successor is the one used by the path. At an update,
the unique installed action changes $\rho^j u$ to $\rho^{j+1}u$ and
uses its fixed successor. These facts preserve the actual register,
state and epoch at each step. No segment can continue through an earlier
halt, because $F_v$ has no outgoing halt edge. An intermediate segment
ending at a halt cannot be followed by a positive crossing from that
halt; the only compatible final segment there is the empty path to
that same halt. Thus the concatenation is the actual first-halting
execution, at $h,J$. Determinism supplies no additional choices to the
controller merely because the description used existential witnesses.

For effectiveness, (NPS.9) is finite after $G$ is fixed. Each $P_v$
is the finite formula of §2; (NPS.7) uses a finite disjunction over
update states. Formula (NPS.8) is a first-order quantified CAR reply
formula. The remaining conditions are addition, order, conjunction
and first-order quantification over natural numbers. All coefficients
in (NPS.6) are numerals. Neither source ranks nor word parameters are
cycle weights, and no product of two quantified variables occurs.
Thus (NPS.10) and its existential projection (NPS.11) are effectively
Presburger, proving the theorem. $\square$

**Definition 3.3 (boundary conventions in the correspondence).** For
$r=0$ use the unique empty response vector and $m=1$. If the initial
state is a halt $h$, its empty path gives $J=N$; there is no need for a
read or update. If the final crossing update enters a halt at a vector
change, the final segment is empty at that new epoch. Singleton
$\alpha$ or $\beta$ phases are ordinary one-epoch intervals. A change
while control is at an update state is included even though that state
does not read the changing word.

Pure-read cycles cannot use a later hypothetical epoch to escape: their
update weight is zero and they have no path to a crossing update or an
external halt under the current vector. Update-containing cycles can
cross arbitrarily distant boundaries by their actual unit updates;
their terminal positions, including a boundary in the middle of a
cycle, are retained by $P_v$ and $X_v$. An update-only cycle with no
exit to a halt has no terminal $P_v$ path in any phase. These are cases
of (NPS.12), not extra termination assumptions. Empty halt sets make
the disjunction of eventual halt supports false.

## 4. Decision, exact rejection and positive literal extraction

**Definition 4.1 (one common design sentence).** For a graph $G$ and
descriptor types as in §2, put

$$
\begin{aligned}
\operatorname{Total}_G(\boldsymbol\delta)
={}&\bigwedge_{\eta\in\mathcal A}\ \forall\mathbf n\quad
 \operatorname{Adm}_\eta(\mathbf n)
 \Longrightarrow\bigvee_{h\in E_H}
                     H_{\eta,h}(\mathbf n;\boldsymbol\delta),\\
\operatorname{Shared}_G(\boldsymbol\delta)
={}&\bigwedge_{\eta,\theta\in\mathcal A,\ h\in E_H}
 \forall\mathbf n\,\forall\mathbf m\quad
 \left[
 \begin{array}{l}
 \operatorname{Adm}_\eta(\mathbf n)\land
 \operatorname{Adm}_\theta(\mathbf m)\land\\
 H_{\eta,h}(\mathbf n;\boldsymbol\delta)\land
 H_{\theta,h}(\mathbf m;\boldsymbol\delta)
 \end{array}
 \right]
 \Longrightarrow\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m),\\
\Phi_G={}&\exists\boldsymbol\delta\quad
 V_G(\boldsymbol\delta)\land
 \operatorname{Total}_G(\boldsymbol\delta)\land
 \operatorname{Shared}_G(\boldsymbol\delta).
\end{aligned}
\tag{NPS.15}
$$

The implications in the first two lines are within their respective
universal quantifiers. The tuple dimensions are those of their charts.
Descriptor types have already been selected by a finite outer choice;
all numeric descriptor variables in the third line precede every source
quantifier. Phase cuts, path counts and terminal epochs occur only
inside $H$. This uses the whole-domain and shared-halt construction of
[CAR, Theorem 12.1][CAR], with exact unbounded support replacing its
finite-horizon path formula.

**Theorem 4.2 (unrestricted prescribed-$K$ native-table synthesis).**
For every input of Assumption 1.1 and every prescribed $K\in\mathbb N$,
$\mathsf{Native}_K(D,N,Q)$ is decidable. More precisely it is equivalent
to the finite disjunction of (NPS.15) over all graphs with
$1\le |E|\le K$ and all descriptor-type choices. For $K=0$ that
disjunction is false. A true answer effectively constructs an original
literal table with at most $K$ complete states. A false answer excludes
every such table on the entire original fiber, irrespective of its
finite word lengths, finite output sizes and terminating run durations.

No read, update, address-length or literal-installation upper bound is
an input, an auxiliary cutoff or an existence premise of this decision.

Proof. CAR supplies the exact finite chart and predicate data of
Definition 1.2 from the cycle-covered input. Theorem 3.2 supplies the
finite formulas $H$ for each of the finitely enumerated designs.
Consequently each (NPS.15) is a first-order Presburger sentence over
nonnegative integers. Apply [Ginsburg–Spanier, Theorem 1.2][GS] to
decide them. Arbitrary first-order quantifier alternation, including
the interval guards inside source-universal clauses, is allowed.
Both true and false decisions terminate. This is not enumeration of
successively larger action horizons or literal installations.

For necessity take any successful original table $C$ with $s\le K$
states and relabel its states in the enumerated format. Retain its
initial state, instruction types and every successor. Give each read
state the descriptor of its actual installed word, once for all visits.
Theorem 6.2 of CAR gives that word's responses on every source at every
epoch, including absent responses. Each source has exactly one admitted
tuple by (NPS.2), and its finite actual trace yields $H$ by (NPS.12).
This proves $\operatorname{Total}_G$. Two sources reaching the same
halt have that halt's one installed complete row, hence satisfy
(NPS.3). This proves $\operatorname{Shared}_G$ across all charts and
terminal epochs. Thus $C$ makes one disjunct true. If every disjunct
is false, no successful original table of the requested size exists;
this proves the exact negative direction.

For sufficiency take a true disjunct. Extract one common satisfying
descriptor tuple. For example, after its existential truth is decided,
enumerate tuples of naturals by increasing total sum and decide the
remaining formula for each tuple. Existence ensures that this extraction
terminates; the preceding negative decision did not depend on that
enumeration. Realize every descriptor once as a literal word by CAR
Theorem 6.2 and keep the selected graph and initial state.

For each halt decide the support-nonemptiness sentence

$$
\operatorname{Reach}_h(\boldsymbol\delta)
\ \Longleftrightarrow\
\bigvee_{\eta\in\mathcal A}\exists\mathbf n\quad
 \operatorname{Adm}_\eta(\mathbf n)\land
 H_{\eta,h}(\mathbf n;\boldsymbol\delta).
\tag{NPS.16}
$$

When it is true, extract one such tuple, construct the actual finite
source $u_h=\Theta_\eta(\mathbf n)$ and compute its **entire original**
$Q$ row. This computation is effective on a finite tree: navigate the
fixed original cut, keep the complete remaining marked tree and compare
the finitely many reached whole subtrees. Install that concrete row
$Y_h=R_Q(u_h)$ at $h$. By $\operatorname{Shared}_G$, every other
admitted source reaching this halt has exactly $Y_h$, including sources
in other charts and sources reaching it at other epochs. At an
unreachable halt install the row of any witness to nonempty $D$, found
using $\operatorname{Adm}$ and (NPS.2).

Now fix an arbitrary original $u\in D$. Its unique admitted tuple
satisfies $\operatorname{Total}_G$, so (NPS.12) forces its actual
execution with the installed words to reach some halt in finite time.
That halt is reachable, and the preceding equality shows its installed
row is $R_Q(u)$. This holds for every original source. The implementation
is the selected $s$-state graph itself: no $x_i,t_i,d_i,J,v_i$, source
witness, chart tag, descriptor evaluator or output decoder becomes a
runtime input or an additional state. Witness sources are used only to
construct literal rows before execution. All words and rows are finite,
so installation is finite, with no prescribed bound. This proves the
reverse direction and positive extraction. $\square$

**Definition 4.3 (what the sentence excludes).** The one tuple in every
$G$ guard prevents mixing replies realizable only on different original
sources. The common descriptor tuple and (NPS.5) prevent chart-specific
words that no one physical request realizes. The fixed graph retains
the same instruction and reply successors at every visit, including
visits at different epochs. The pair of complete source tuples in
$\operatorname{Shared}_G$ compares the entire support of one installed
halt, rather than separate leaves of a trace expansion. Equal vectors,
equal chart tags or individually constant trace leaves do not replace
the required full-row equality. Quantifier order permits each source
its own proof of termination, but permits only one installed design.

## 5. An exact unbounded design ray on an original infinite fiber

**Definition 5.1 (the supplied source family and a literal design parameter).**
Fix $m\ge6$. Use exactly the acquired input and original target of
[CAR, Definition 13.1 and Proposition 13.2][CAR], with

$$
N_m=2m+1,\qquad B_m=m(2m+2),\qquad D_m=B_m+1.
\tag{NPS.17}
$$

The supplied two-way recognition identifies its entire fiber as

$$
\mathcal D_m=
\left\{U_{D_m}(T_n,T_{n\bmod2},T_h):
           2\le n\le2m+1,\quad h\ge2m+2\right\},
\tag{NPS.18}
$$

where $T_j=\rho^j\alpha$, $G_0(v)=v$,
$G_{i+1}(v)=\langle\alpha,G_i(v)\rangle$, and
$U_D(x,z,w)=\langle x,G_{D-1}(\langle z,w\rangle)\rangle$.
This displayed parametrization is the cited conclusion about the
acquired fiber, not a new promise made by its observer. The retained
literals, signed relations and old three-class row are exactly CAR's
input. Its target cut is $Q_m=\{L,R^{D_m}R\}$. Its two complete rows
$Y_0\ne Y_1$ have the full fixed marked comb exterior, concrete
$T_e$ at $R^{D_m}L$, and the reached unequal holes at $L,R^{D_m}R$.
The unbounded $h$ coordinate is retained in the source domain.

Consider the five-state graph with initial read state $r$, update
states $v_1,v_2$ and halts $h_0,h_1$. Its read successors for
$(\mathsf{absent},\alpha,\beta,\mathsf{branch})$ are
$(v_1,h_0,h_1,h_0)$, and its update edges are
$v_1\to v_2\to r$. For each integer $t\ge1$ install the single word

$$
p_t=LLR^t.
\tag{NPS.19}
$$

Leave the halt rows unspecified when asking whether this design is
successful. The parameter $t$ is literal installation data, not an
online repetition counter. The case $t=2m$ is the table supplied by
[CAR, Theorem 13.3][CAR]; the question here concerns **every** $t\ge1$
with no read or update bound.

**Theorem 5.2 (exact supports and successful installation ray).** On
the entire original $\mathcal D_m$, the eventual supports of this
graph, in the coordinates (NPS.18), are

$$
\begin{aligned}
H_{h_1}(n,h;t)
 &\ \Longleftrightarrow\
 n\text{ is odd}\ \land\ n+2m\le2t+1,\\
H_{h_0}(n,h;t)
 &\ \Longleftrightarrow\
 n\text{ is even}\ \lor\
       \bigl(n\text{ is odd}\ \land\ n+2m>2t+1\bigr).
\end{aligned}
\tag{NPS.20}
$$

These are the pullbacks of (NPS.11) along the supplied source
identification. In particular the graph halts on every source for
every $t\ge1$. There exist shared complete halt rows making it
successful if and only if

$$
t\ge2m.
\tag{NPS.21}
$$

For every such $t$, extraction in Theorem 4.2 installs $Y_0$ at $h_0$
and $Y_1$ at $h_1$. Writing $n=2j$ or $2j+1$ with $1\le j\le m$,
the actual successful table has

$$
q(n,h;t)=t-m-j+1,\qquad
a(n,h;t)=2(t-m-j).
\tag{NPS.22}
$$

Thus, even with $m$ fixed, five complete states on this fixed infinite
nonconstant target task admit successful installations of arbitrarily
large action duration. This does not assert that the shortest successful
table for the task has a large duration.

Proof. Compute the exact supports through Theorem 3.2. At a visit to
$r$ after $a$ actual updates, the first $L$ of (NPS.19) enters the
original $T_n$ coordinate. The remaining suffix $LR^t$ has weight
$1+2t$ and last letter $R$. The supplied all-epoch atomic reply formula
[CAR (CAR.23)][CAR] therefore has residual

$$
n+N_m+a-(1+2t)=n+2m-2t+a.
\tag{NPS.23}
$$

Negative residual means actual absence, zero gives $\alpha$, one
gives $\beta$, and at least two gives branch. A return from $r$ to
$r$ while absence holds follows the actual three-edge path
$r\to v_1\to v_2\to r$ and contributes exactly two updates. In the
fixed-absence graph, the $P$ relation to successive read visits thus
has update progression $2z$, and $X$ cuts that path at each intervening
unit update. The phase description retains an intermediate reply
change even when control then lies at $v_2$; it cannot read the
intermediate reply there. By (NPS.12), expanding these paths and guards
is exactly the actual polling trace, with no source-dependent loop
choice.

Write $n=2j+e$, $e\in\{0,1\}$, and put $L=t-m-j$. At the $z$th
read visit the residual is $e+2(z-L)$. If $L\ge0$, it is negative
precisely at the visits $0,\ldots,L-1$; at visit $L$ it is $e$.
The resulting finite phase-path witness ends at $h_e$, after $L$
two-update cycles, at epoch $N_m+2L$. If $L<0$, the first residual is
at least two and the first read goes directly to $h_0$ at epoch $N_m$.
These cases exhaust all admitted sources and all $t\ge1$.
Theorem 3.2 gives both inclusions in (NPS.20): each displayed finite
path is a satisfying halting-support witness, and its exactness excludes
any other halt of the deterministic run. No value of $h$ was fixed or
discarded in this calculation. For odd $n$, the condition $L\ge0$ is
equivalent to $n+2m\le2t+1$, giving exactly (NPS.20).

Now apply (NPS.15), with these exact unbounded supports, to the original
joint source and full-row predicates. Totality holds for every $t$.
Every even $n$ reaches $h_0$ and has full row $Y_0$; every source
reaching $h_1$ has full row $Y_1$. The shared-halt clause at $h_0$
therefore holds precisely when no odd $n$ in $[2,2m+1]$ satisfies
$n+2m>2t+1$. Since the largest admitted odd value is $2m+1$, this
is precisely (NPS.21).

For a concrete negative witness when $t<2m$, the two actual original
sources with $(n,h)=(2,2m+2)$ and $(2m+1,2m+2)$ both reach $h_0$
by (NPS.20), but their complete rows are $Y_0$ and $Y_1$. They
falsify $\operatorname{Shared}_G$, whatever literal row is installed
there. These two witnesses reject a design on the entire infinite
fiber; they do not replace the fiber by a sample. For $t\ge2m$ both
parity supports are nonempty, and the positive extraction of Theorem
4.2 gives exactly their complete rows. It uses the same five states
and no parity buffer.

The parameter family is expressible in the descriptor language used by
that theorem. Split off the finitely many short words relative to the
CAR common depth $H$. For the remaining $p_t$, their length-$H$ prefix
is fixed once $t$ is sufficiently large, their last letter is $R$, and
their suffix length and weight are affine functions of $t$. Hence this
restriction is a finite union of Presburger descriptor conditions with
$t$ a common design variable. Fixing $t$, or leaving it existential,
uses exactly the decision sentence of §4; there is no cutoff on $t$.
The calculation above evaluates its entire successful parameter set as
the ray (NPS.21), rather than reporting a finite solver sample.

For $t\ge2m$ all $L=t-m-j$ are nonnegative. There are $L$ absent
reads followed by one terminal read and $2L$ updates, proving
(NPS.22). The maximum of $q+a$ on this same original fiber is
$3(t-m-1)+1$, attained at $n=2$ or $3$ with any admitted $h$.
It tends to infinity with $t$ at fixed $m$ and fixed five-state graph.
All words and both complete rows retain their separate installation
cost. $\square$

## 6. Applicability and arithmetic limits

**Definition 6.1 (the scope of the inference).** The phase count in the
proof of Theorem 3.2 holds for every finite native source. Effective
synthesis additionally uses the cycle-covered whole-fiber bijection,
joint admission, full-row equality and uniform physical-word predicates
of Definition 1.2. For general signed fibers with unforced non-atomic
skeletons, those uniform predicates have not been supplied by this
argument. A bijection with arbitrary native normal codes does not
supply their decision theory; no ambient normal-domain or
canonicalization solver is assumed.

The bound $3r+1$ counts constant-response intervals. The positive
integers $t_{i+1}-t_i$ and the repetitions in (NPS.6) are unbounded.
Theorem 5.2 shows why those durations cannot be replaced by a bound
depending only on $K$ over all successful installations. Once a
particular literal table has been constructed, [CAR, Theorem 11.2][CAR]
supplies its word-dependent uniform stopping bound on all sources.
That result is compatible with the present proof, but is not used as
a uniform search horizon for unknown words.

The arithmetic statement is a feasibility decision. Multiplying a
fixed cycle update count $b$ by a repetition variable $z$ is linear.
Multiplying an unbounded visit count by an unbounded symbolic word
length would be a different expression, with two variable factors.
No such product occurs in (NPS.15), and no arbitrary unbounded
word-length-weighted optimum follows from its decidability. After
literal extraction, costs of that one table may instead be analyzed
under the existing per-table and bounded-path contracts. Installation
minimization and any additional symbolic price objective require their
own arguments.

The complete-state convention is the native atomic-operation convention
of CAR. Bitwise word emission, output serialization, physical timing,
acquisition, erasure and authenticated access are not constructed by
this mathematical synthesis. The result concerns original complete-row
recovery on the given fiber, not complete future-law recovery or a
uniform-depth or stochastic-law conclusion. No complexity or efficient
implementation bound is asserted.

## 7. Mathematical sources and correspondence

**Mathematical citation 7.1 (owners and literature).** The external
arithmetic and automata facts below are `literature-attested` at the
specified scope. The consumed native phase correspondence, its
unrestricted prescribed-$K$ synthesis consequence and the source-specific
ray calculation are `repo-derived` ordinary mathematical deductions.
They make no global novelty claim.

| Source | Exact use in this volume |
| --- | --- |
| [CAR §§1, 3–4][CAR] | Original acquired input, cycle recognition, both directions of the entire-source coordinate bijection, all retained joint constraints, and original complete-row equality in (NPS.2)–(NPS.3). |
| [CAR §§6–7][CAR] | One globally realized word for each descriptor and its all-chart, all-epoch reply predicates; common design quantifiers and whole-row extraction. No resource cap is invoked as a state-preserving transformation. |
| [CAR §§11–12, 14][CAR], [PR15494][CAR-PR] | Complete native instructions and state accounting; the per-installed-table stopping bridge; bounded synthesis's shared-instruction/shared-output construction. The new relation (NPS.11) supplies the unrestricted support needed by that consumer. |
| [CAR §13][CAR] | Both acquired-domain directions and the complete rows for the infinite family in §5. Its particular $t=2m$ controller and its length-constrained static lower bound retain their scopes; neither is claimed as a new result here. |
| [Continuation II §§26–30][CII] | Complete observable state, fixed instructions and output distinctions, and proof-only support/rank. No finite-plant synthesis theorem is applied to the infinite native register. |
| [NativeDepthPatterns, `original_present_transport`][TRANSPORT] | Reached-subtree transport, applied at the actual epoch of reach in (NPS.13). This is not a transport assertion for an absent subtree. |
| [Ginsburg–Spanier, Theorems 1.2–1.3][GS] | Theorem 1.2 decides the explicit first-order natural-addition sentences. Theorem 1.3 supplies the mature effective semilinear/Presburger correspondence; no arbitrary-tree decision is inferred. |
| [To, §§1–2][TO] | Unary regular paths and finite unions of arithmetic progressions. Here the fixed-response graph is functional with weights $0,1$, so its actual orbit gives the constants in (NPS.6). No bound for general counter machines, independent mixing of cycles, or automata complexity claim is imported. |

Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas,
and Languages*, Pacific Journal of Mathematics **16**(2), 285–296,
Theorems 1.2–1.3, supplies the decision theorem after the native
interpretation, not the interpretation itself. Anthony Widjaja To,
*Unary finite automata vs. arithmetic progressions*, arXiv:0812.1291v1,
§§1–2, supplies the mature automata context for the finite path arithmetic.
Its warning about dependencies between cycles is respected by using the
unique orbit of $F_v$ with its specified entry and endpoint.

The proofs here are ordinary mathematical proofs. They assert no new
Lean compilation, kernel certification, executed synthesis solver or
physical realization. The effective algorithm in Theorem 4.2 is
justified by the displayed reduction and the cited decision theorem.

[CAR]: https://github.com/the-omega-institute/trureturing/blob/ac159239a7c999bf163bd244eb18ba0a49c0de81/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[CAR-PR]: https://github.com/the-omega-institute/trureturing/pull/15494
[CII]: https://github.com/the-omega-institute/trureturing/blob/230f7df3faef1932c21cac2f5dad58f5d9eb9e2a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md
[TRANSPORT]: https://github.com/the-omega-institute/trureturing/blob/906b8a1d479e36f432622e868d871503dec19fde/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[TO]: https://arxiv.org/pdf/0812.1291v1

## 追加锚（本行以下为增补区）
