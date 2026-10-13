# Uniform descriptor boundaries for finite relational sources

## 1. Task, source coordinates and exact literal descriptors

**Definition 1.1 (ordinary-theory scope).** This volume concerns finite
relational objects, their prescribed read and transport operations, and
recovery of one complete target row of the original object. A source is
finite; the family of sources, coordinate values, literal lengths and
execution lengths need not be bounded. The new bridge separates arithmetic
controller synthesis from dynamic sufficiency of a boundary representation.
Its deductions are `repo-derived` ordinary mathematics. The arithmetic
decision fact used inside the deductions is `literature-attested`
[Ginsburg–Spanier, Theorems 1.2–1.3][GS]. These statements are not assertions
of Lean or kernel verification, physical realization or literature novelty.
The append-only convention is that subsequent additions follow the final
append anchor and use new numbers.

**Definition 1.2 (an effectively presented original-source task).** Let
$\mathbb N=\{0,1,2,\ldots\}$. Supply an effectively encoded class $\mathcal S$
of finite relational objects, a family $D\subseteq\mathcal S$ of original
sources, a deterministic effective transport $U:\mathcal S\to\mathcal S$,
and a common entry epoch $N\in\mathbb N$. Transport need not preserve $D$.
Supply a finite alphabet $\Sigma$ of address letters and the permitted
literal address set $\mathcal W\subseteq\Sigma^*$, with effective membership.
The actual read at $p\in\mathcal W$ on $z\in\mathcal S$ has deterministic
reply $r_z(p)$ in a fixed nonempty finite ordered alphabet $\mathcal C$. A read
leaves $z$ unchanged; an update replaces $z$ by $U(z)$ once. Every permitted
read, including an absent reply, and every update is legal. A more
restrictive legality convention requires additional exact legality
predicates; it is not inferred from an absent reply.

Supply an effective map $R:D\to\mathcal Y$ into finite encodings of
**complete target rows**, with decidable literal equality on $\mathcal Y$.
For a cut task, completeness means the entire concrete marked exterior,
the ordered reached original holes and their complete whole-subobject
equality partition. For another relational task, all fields of its
declared target belong to $R$; a mask, rank or selected coordinate is not
silently substituted. Supply one effective default row $Y_*\in\mathcal Y$.
The task starts on $U^N u$ and must output $R(u)$, for every $u\in D$.
The target is attached to the original source, not to the transported
register at the stopping epoch.

**Assumption 1.3 (finite disjoint charts and whole-row equality).** Supply a
finite chart index set $\mathcal A$, dimensions $d_\eta\in\mathbb N$, effective
Presburger formulas $\operatorname{Adm}_\eta(\mathbf n)$, and effective
maps

$$
\Theta_\eta:\{\mathbf n\in\mathbb N^{d_\eta}:
                     \operatorname{Adm}_\eta(\mathbf n)\}\longrightarrow D
$$

such that the disjoint-union map

$$
\Theta:\coprod_{\eta\in\mathcal A}\operatorname{Adm}_\eta
           \longrightarrow D,
\qquad (\eta,\mathbf n)\longmapsto\Theta_\eta(\mathbf n)
\tag{UDB.1}
$$

is a bijection. Thus no original source is omitted, and one coordinate
tuple is not an independently refillable phase source. A zero-dimensional
chart contains at most its unique empty tuple. Empty charts and $D=\varnothing$
are allowed. Chart parameters can encode relations between components;
admission is jointly Presburger in the entire tuple, not merely in each
marginal coordinate.

For each $\eta,\theta\in\mathcal A$, supply an effective Presburger formula
$\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)$, jointly in both
whole tuples, satisfying

$$
\begin{aligned}
\forall\mathbf n\in\mathbb N^{d_\eta}\;
\forall\mathbf m\in\mathbb N^{d_\theta}\quad
&\operatorname{Adm}_\eta(\mathbf n)\land
 \operatorname{Adm}_\theta(\mathbf m)\ \Longrightarrow\\
&\left(\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)
\ \Longleftrightarrow\
R(\Theta_\eta(\mathbf n))=R(\Theta_\theta(\mathbf m))\right).
\end{aligned}
\tag{UDB.2}
$$

Effective construction of $\Theta_\eta(\mathbf n)$ and of its complete row
is part of the assumption. Decidability of row equality alone would not
provide output literals. A chart tag or coordinate is mathematical source
context; the controller receives no chart-selector or unknown-coordinate
port.

**Assumption 1.4 (finite descriptor types, unbounded parameters).** Supply a
finite type set $\mathcal B$. A descriptor of type $b$ is
$\delta=(b,\mathbf t)$ with $\mathbf t\in\mathbb N^{k_b}$, where $k_b$ is a
fixed natural number. There is an effective Presburger validity formula
$\operatorname{Valid}_b(\mathbf t)$ and a nonempty set
$\operatorname{Real}(\delta)\subseteq\mathcal W$ for every valid descriptor.
Supply an effective choice of **one literal realization**

$$
p(\delta)\in\operatorname{Real}(\delta).
\tag{UDB.3}
$$

It is chosen without a source, chart, epoch or future reply. Supply an
effective descriptor $\delta$ for every $p\in\mathcal W$ such that

$$
\operatorname{Valid}(\delta)\land p\in\operatorname{Real}(\delta).
$$

Thus the descriptor language covers every permitted finite installation with
a valid descriptor and a realization containing that installed literal.
There are finitely many types, not finitely many descriptors. Different
descriptors may share a realization, and different states may install
the same literal. A singleton realization set is permitted.

For every $\eta\in\mathcal A$, $c\in\mathcal C$ and descriptor type, supply
an effective Presburger relation
$\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta)$ jointly in the source
coordinates, epoch and descriptor parameters. Its exactness requirement
has the following quantifier order:

$$
\begin{aligned}
\forall\mathbf n\;\forall j\in\mathbb N\;\forall\delta\quad
&\operatorname{Adm}_\eta(\mathbf n)\land\operatorname{Valid}(\delta)
\ \Longrightarrow\\
&\forall p\in\operatorname{Real}(\delta)\;\forall c\in\mathcal C\quad
\left(\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta)
\ \Longleftrightarrow\ r_{U^j\Theta_\eta(\mathbf n)}(p)=c\right).
\end{aligned}
\tag{UDB.4}
$$

The quantifier over descriptor types is a finite conjunction. On admitted,
valid arguments exactly one reply predicate holds. No independently
chosen chart-specific words can witness (UDB.4): every realization is
exact simultaneously on the entire chart union and at all epochs.
The formulas themselves are finite arithmetic data; deciding whether
arbitrary proposed formulas really satisfy these semantic assumptions is
not part of the synthesis problem.

**Assumption 1.5 (reached-address transport and rank).** Fix a rank map
$\operatorname{rk}:\mathcal C\to\{0,\ldots,q\}$ that strictly preserves the
given order, where $q\in\mathbb N$ is a fixed maximum rank. The absent
reply, if present, is the least rank, zero; in that case define
$\operatorname{Reached}(z,p)$ by $r_z(p)\ne\mathsf{absent}$. If no absent
symbol is supplied, every permitted address is reached. For each $p$
supply a content set $\mathcal L_p$, a map $\chi_p$ from reached register
objects into $\mathcal L_p$, and a reply map $g_p:\mathcal L_p\to\mathcal C$
which gives $r_z(p)=g_p(\chi_p(z))$ on reached objects. For every admitted
$u$, every $p\in\mathcal W$ and every $j,a\in\mathbb N$, reaching $p$ on
$U^ju$ implies reaching it on $U^{j+a}u$. Thus absence can precede first
reach, but cannot recur after it.

Supply the reached-address transport law in the following explicit form.
At a reached epoch set $w_{u,p,j}=\chi_p(U^ju)$. There are maps
$L_{p,a}:\mathcal L_p\to\mathcal L_p$ with $L_{p,0}=\operatorname{id}$ and
$L_{p,a+b}=L_{p,b}\circ L_{p,a}$ such that, for every $u\in D$, every
$p\in\mathcal W$, every reached epoch $j$ and every $a\in\mathbb N$,

$$
\begin{gathered}
w_{u,p,j+a}=L_{p,a}(w_{u,p,j}),\qquad
r_{U^{j+a}u}(p)=g_p(L_{p,a}(w_{u,p,j})),\\
\operatorname{rk}(g_p(w_{u,p,j}))
 \le \operatorname{rk}(g_p(L_{p,a}(w_{u,p,j}))).
\end{gathered}
\tag{UDB.5}
$$

Before first reach the reply is the least element; first reach cannot
decrease rank. If all reads are always reached, the absence clause is
vacuous. Only reached content is transported: no nonexistent original
subobject is assigned an image. These hypotheses imply, with all source
and address quantifiers shared,

$$
\forall u\in D\;\forall p\in\mathcal W\;\forall j,k\in\mathbb N\quad
j\le k\ \Longrightarrow\
\operatorname{rk}(r_{U^ju}(p))\le\operatorname{rk}(r_{U^ku}(p)).
\tag{UDB.6}
$$

The subsequent arithmetic proof uses (UDB.6); (UDB.5) specifies the
original-address interpretation supplying it. Here rank $q$ means at
most $q$ strict rank increases, allowing $q+1$ ordered replies. If instead
an alphabet is described as having $q$ symbols, use maximum rank $q-1$;
the sharper bound $(q-1)r+1$ then also implies the requested $qr+1$ bound.
For the four replies in [NPS][NPS], maximum rank is three.

## 2. Finite controllers and the phase bound

**Definition 2.1 (complete finite instruction table).** A controller has a
nonempty finite set $E$, a common initial state $e_*$ and a partition
$E=E_R\sqcup E_U\sqcup E_H$. A read state $e\in E_R$ installs one fixed
literal $p_e\in\mathcal W$ and one successor $s_R(e,c)\in E$ for each
$c\in\mathcal C$. An update state $e\in E_U$ has one successor
$s_U(e)\in E$. A halt $h\in E_H$ installs one literal row $Y_h\in\mathcal Y$
and is absorbing. The source register and epoch are respectively $U^ju$
and $j$; they are not extra readable controller storage.

All mutable reply retention, program positions, finite selectors and
output distinctions are counted in $E$. A prescribed finite-valued
accumulator can be incorporated by taking its product with control and
counting the resulting states. Unbounded writable storage is not part of
this controller class. Whole-literal reads and whole-row halt output have
the declared primitive semantics. The cardinality $|E|$ does not charge
their installation lengths or serialization work.

For $K\in\mathbb N$, write $\mathsf{Solve}_K$ for existence of such a table
with $|E|\le K$ which, on every original $u\in D$ from $(e_*,U^Nu)$, first
halts after finitely many instructions with output $R(u)$. This is one
table for the entire family, not one table for each source.

**Definition 2.2 (one common symbolic graph).** Before selecting literals,
fix a labeled graph $G$ on $E=\{0,\ldots,s-1\}$, its initial state,
instruction partition and successors. Choose one descriptor type for
each read state, and let $\boldsymbol\delta=(\delta_e)_{e\in E_R}$ contain
their numeric parameters. Set $r=|E_R|$. All choices in this definition
are common design data. For a valid tuple, an admitted $u$ and an epoch
$j$, define

$$
V_u(j)=(r_{U^ju}(p(\delta_e)))_{e\in E_R}\in\mathcal C^{E_R}.
\tag{UDB.7}
$$

This vector lists the replies to all installed addresses, including
states not visited on the run. It is a mathematical response field;
forming it in the proof does not execute $r$ extra reads or grant the
controller a simultaneous-response port.

**Theorem 2.3 (finite response-phase bound).** Under Assumptions 1.4–1.5,
for every valid common descriptor tuple, every $u\in D$ and every
$J\ge N$, the integer interval $[N,J]$ has at most $qr+1$ maximal nonempty
intervals on which $V_u$ is constant. The same bound applies to the
entire half-line starting at $N$. When $r=0$ there is one empty response
vector and one phase. An initial halt has the one-epoch interval $[N,N]$.

Proof 2.3. Exactness gives the same literal at every epoch on this same
source. By (UDB.6), every coordinate of $V_u(j)$ is nondecreasing in rank.
The potential

$$
B_u(j)=\sum_{e\in E_R}\operatorname{rk}(V_u(j)(e))
\tag{UDB.8}
$$

is nondecreasing, lies in $[0,qr]$ and increases by at least one whenever
the vector changes. There can therefore be at most $qr$ change epochs.
Their cuts yield at most $qr+1$ nonempty constant intervals. The proof
also works on the half-line: an infinite list of changes would force
the bounded integer potential to exceed $qr$. An empty sum is zero and
$\mathcal C^{\varnothing}$ has its unique empty vector. Duplicate
addresses and simultaneous changes only reduce the count. $\square$

This bounds **phase count**. It bounds neither phase duration, instruction
count, number of updates or reads, word length, output size nor installation
cost. A pure-read loop can perform infinitely many instructions at one
epoch; a phase can contain an arbitrarily long update-containing loop.
Monotonicity is not itself a termination theorem.

## 3. Fixed-response paths and exact eventual halt support

**Definition 3.1 (endpoint-exact paths).** For $v\in\mathcal C^{E_R}$, let
$F_v$ be the partial function on $E$ that takes $s_R(e,v(e))$ at a read
state and $s_U(e)$ at an update state, and is undefined at a halt. Give a
read edge weight zero and an update edge weight one. Let $P_v(x,y,d)$
mean that a finite path of this partial function starts at $x$, ends at
$y$ and has total update weight $d\in\mathbb N$. Include the empty path
exactly for $x=y,d=0$. Its edges are nonhalt instructions; an absorbing
halt self-loop is deliberately excluded from this first-arrival graph.

The effective Presburger formula for $P_v$ is obtained from the unique
orbit of $x$. Follow it until halt or first vertex repetition. A transient
occurrence of $y$ gives the singleton $d=a$, where $a$ is its computed
update count. If $y$ occurs on the eventual simple cycle, its first count
is $a$ and the cycle has computed update weight $b$. Its possible counts
are exactly

$$
\exists z\in\mathbb N\quad d=a+bz.
\tag{UDB.9}
$$

Take the finite disjunction of the applicable singleton and progression
formulas. The numerals $a,b$ depend on the fixed graph and fixed vector,
not on source, descriptor or epoch variables. For $b=0$ the progression
is just $d=a$. An orbit trapped in a zero-weight cycle cannot reach an
external vertex merely by choosing a positive $z$. The orbit construction
retains entry and endpoint; it does not combine cycles that no single
path traverses. This is the functional-path construction used within
[NPS, Definition 2.2][NPS].

**Definition 3.2 (crossing by the final unit update).** Define

$$
X_v(x,y,d)\ \Longleftrightarrow\
\bigvee_{\substack{e\in E_U\\s_U(e)=y}}
\exists c\in\mathbb N\quad d=c+1\ \land\ P_v(x,e,c).
\tag{UDB.10}
$$

This is exactly a finite path whose final edge is a real update and whose
positive total update count is $d$. If its starting epoch is $a$ and
$a+d=b$, every action starts before epoch $b$: the last unit edge remains
to be executed before the endpoint. Thus every read along the path uses
epochs in $[a,b)$, even if many zero-weight reads occur between updates.

**Definition 3.3 (shared-source guards and halt formulas).** For one fixed
chart tuple, define

$$
\begin{aligned}
\Gamma_{\eta,v}(\mathbf n,\boldsymbol\delta;a,b)
\ \Longleftrightarrow\
\forall j\in\mathbb N\quad
a\le j<b\ \Longrightarrow\
\bigwedge_{e\in E_R}\operatorname{Reply}_{\eta,v(e)}(\mathbf n,j,\delta_e).
\end{aligned}
\tag{UDB.11}
$$

For $h\in E_H$, form $\mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta)$
by a finite disjunction over

$$
1\le m\le qr+1,\qquad
v_0,\ldots,v_{m-1}\in\mathcal C^{E_R},\qquad
x_1,\ldots,x_{m-1}\in E,
\tag{UDB.12}
$$

with $x_0=e_*$. Each disjunct existentially quantifies
$t_0,\ldots,t_m,d_0,\ldots,d_{m-1}\in\mathbb N$ and imposes

$$
\begin{gathered}
N=t_0<t_1<\cdots<t_m=J+1,\\
\bigwedge_{i=0}^{m-1}
\Gamma_{\eta,v_i}(\mathbf n,\boldsymbol\delta;t_i,t_{i+1}),\\
\bigwedge_{i=0}^{m-2}
\left(t_i+d_i=t_{i+1}\ \land\ X_{v_i}(x_i,x_{i+1},d_i)\right),\\
t_{m-1}+d_{m-1}=J\ \land\ P_{v_{m-1}}(x_{m-1},h,d_{m-1}).
\end{gathered}
\tag{UDB.13}
$$

Put

$$
H_{\eta,h}(\mathbf n;\boldsymbol\delta)
\ \Longleftrightarrow\ \exists J\in\mathbb N\;
\mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta).
\tag{UDB.14}
$$

Adjacent phase vectors need not be distinct or intervals maximal. The
guard includes epoch $J$ by the delimiter $J+1$; that delimiter is not an
update after halt. For $m=1$ the crossing conjunction is empty. For $r=0$
one may use just $m=1$ and the empty vector. Most importantly, every
occurrence of $\mathbf n$ in every phase is the **same free source tuple**.
The quantifier order is a common $\boldsymbol\delta$, then one source,
then that source's $J$ and phase witnesses. It is not
$\exists\mathbf n_0\cdots\exists\mathbf n_{m-1}$.

**Theorem 3.4 (both directions on the same original source).** Under
Assumptions 1.3–1.5, for every fixed graph and descriptor-type choice,
$\mathcal H_{\eta,h}$ and $H_{\eta,h}$ are effective Presburger formulas,
jointly in their displayed numeric arguments. For every valid common
$\boldsymbol\delta$, every admitted $(\eta,\mathbf n)$, every $h\in E_H$
and every $J\in\mathbb N$,

$$
\begin{aligned}
\mathcal H_{\eta,h}(\mathbf n,J;\boldsymbol\delta)
\ \Longleftrightarrow\
&\text{the installed literal graph on the original }u=\Theta_\eta(\mathbf n)\\
&\text{from }(e_*,U^Nu)\text{ first reaches halt }h
  \text{ at epoch }J.
\end{aligned}
\tag{UDB.15}
$$

Consequently $H_{\eta,h}$ is equivalent to eventual first halt at $h$ on
that source. Arrival says nothing yet about the correctness of $Y_h$.

Proof 3.4. Suppose first that the actual execution first halts at $h,J$.
Its trace is finite, and $J\ge N$. Every integer epoch from $N$ to $J$
is visited, since the only epoch-changing action increments by one.
Partition $[N,J]$ into its maximal constant response-vector intervals.
Theorem 2.3 supplies at most $qr+1$ intervals. Give the last interval right
endpoint $J+1$. Cut the trace at every internal interval boundary
immediately after the update that first enters its new epoch. The state
at that cut is the shared $x_i$.

Each internal segment uses its old vector $v_i$, has update count $d_i$
with $t_i+d_i=t_{i+1}$ and ends in an update. It therefore satisfies
$X_{v_i}$. The last segment is an $F_{v_{m-1}}$ path to $h$ with total
weight $J-t_{m-1}$ and satisfies the final $P$. Exact Reply gives each
$\Gamma$ on the one original source. These are all witnesses in
(UDB.13), proving this direction without choosing new phase sources.

Conversely, suppose (UDB.13) holds. Every $P$ assertion expands to an
actual finite path of its specified $F_v$, by Definition 3.1. Every $X$
assertion expands to such a path followed by its stipulated final update.
Concatenate these paths at the same states $x_i$. Every action in an
internal segment starts in $[t_i,t_{i+1})$ by Definition 3.2. Nonnegative
weights place all starts in the final segment in $[t_{m-1},J]$. The final
guard includes that last epoch.

Induct through this finite concatenation with original register $U^Nu$.
At a read, (UDB.11) and (UDB.4) give exactly the actual literal reply on
$U^ju$, and hence the actual response successor. At an update the register
becomes $U^{j+1}u$ and control takes its sole successor. The register,
control and epoch therefore agree with the actual execution throughout.
No path can continue through an earlier halt: $F_v$ has no outgoing halt
edge. If the final crossing itself enters $h$, the remaining segment must
be the empty path at that same epoch. A different earlier halt cannot
have a path to $h$. The resulting trace is exactly first halt at $h,J$.

For arithmetic effectiveness, (UDB.12) is a finite outer enumeration.
$P_v$ uses singleton and fixed-coefficient progression formulas; $X_v$
uses a finite disjunction and a natural existential. Each $\Gamma$ is a
first-order quantified supplied Reply formula. The remaining operations
are conjunction, disjunction, order, addition and first-order natural
quantification. The same closure gives the projection (UDB.14).
Presburger closure and decision are used at their established scope
[GS, §1][GS]. $\square$

**Definition 3.5 (degenerate and cyclic cases).** If the initial state is
halt $h$, the empty path proves $J=N$. If $E_H=\varnothing$, every eventual
halt disjunction is empty. A pure-read cycle has zero update weight and
cannot escape by positing a later phase: no crossing path exists. An
update-containing cycle may cross a distant boundary, but $P$ and $X$
retain the actual endpoint, including a cut inside a cycle. An update-only
cycle with no route to halt has no halt support. These follow from the
path definitions and are not extra assumptions of termination.

## 4. Uniform design, output extraction and representation independence

**Definition 4.1 (the common design sentence).** For a fixed graph and
descriptor types, define

$$
\begin{aligned}
\operatorname{Valid}_G(\boldsymbol\delta)
={}&\bigwedge_{e\in E_R}\operatorname{Valid}(\delta_e),\\
\operatorname{Total}_G(\boldsymbol\delta)
={}&\bigwedge_{\eta\in\mathcal A}\forall\mathbf n\in\mathbb N^{d_\eta}\quad
\operatorname{Adm}_\eta(\mathbf n)\ \Longrightarrow\
\bigvee_{h\in E_H}H_{\eta,h}(\mathbf n;\boldsymbol\delta),\\
\operatorname{Shared}_G(\boldsymbol\delta)
={}&\bigwedge_{\eta,\theta\in\mathcal A}\ \bigwedge_{h\in E_H}
\forall\mathbf n\in\mathbb N^{d_\eta}\ \forall\mathbf m\in\mathbb N^{d_\theta}\quad\\
&\left(\operatorname{Adm}_\eta(\mathbf n)\land
\operatorname{Adm}_\theta(\mathbf m)\land
H_{\eta,h}(\mathbf n;\boldsymbol\delta)\land
H_{\theta,h}(\mathbf m;\boldsymbol\delta)\right)
\ \Longrightarrow\ \operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m),\\
\Phi_{G,\mathbf b}
={}&\exists\boldsymbol\delta\quad
\operatorname{Total}_G(\boldsymbol\delta)\land
\operatorname{Shared}_G(\boldsymbol\delta)\land
\operatorname{Valid}_G(\boldsymbol\delta).
\end{aligned}
\tag{UDB.16}
$$

Each displayed implication is inside its displayed source quantifiers.
The finite type tuple $\mathbf b$ is selected before this sentence.
**All numeric descriptor variables precede all source variables.**
Inside $H$ each source may have its own terminal epoch, phase lengths and
path witnesses. Shared compares any two sources reaching the same halt,
even in different charts and at different epochs; it is equality of the
complete original row. A constant row on each separately chosen trace
leaf would not suffice to install one row at a shared halt.

**Theorem 4.2 (Uniform Descriptor Boundary Theorem).** For every effectively
presented task satisfying Definitions 1.2 and Assumptions 1.3–1.5, and for
every $K\in\mathbb N$,

$$
\mathsf{Solve}_K\ \Longleftrightarrow\
\bigvee_{\substack{G\text{ a labeled instruction graph}\\1\le|E|\le K}}
\ \bigvee_{\mathbf b\in\mathcal B^{E_R}}
\Phi_{G,\mathbf b}.
\tag{UDB.17}
$$

The right side is a finite effective Presburger sentence. Its truth is
decidable. If true, one can extract a single finite literal table and
observer interface with at most $K$ complete controller states. If false,
one obtains a finite arithmetic rejection of all graphs and all valid
descriptor valuations in (UDB.17). This is an exact criterion within the
declared instruction class, without a bound on finite word installation
or terminating action durations.

Proof 4.2. For each $1\le s\le K$, there are finitely many partitions of
$\{0,\ldots,s-1\}$ into three instruction classes, finitely many initial
states, $s^{|\mathcal C|}$ successor choices at each read, and $s$ at each
update. Enumerate them all, including unreachable states and graphs
without halts. For each graph, enumerate the finitely many descriptor-type
tuples. Their dimensions are then fixed. No literal length is enumerated
as a bounded cutoff: unbounded numeric descriptor values remain the
existential variables in (UDB.16).

Theorem 3.4 and supplied admission and Same formulas make (UDB.16)
Presburger. Boolean closure, existential projection and universal
quantification are all allowed, including quantifier alternation within
the phase guards. Apply the decision theorem [GS, Theorem 1.2][GS] to
the finite disjunction. Every cycle expression has form $a+bz$ with fixed
numeral $b$. Graph size, alphabet rank and phase count are fixed before
arithmetic quantification. Products of a descriptor length with a variable
visit count, of two source coordinates, or of a source coordinate with
an epoch are never introduced by this construction. Reply, Same and
admission are required to be jointly Presburger already. Consequently no
product of two unbounded quantified variables is hidden in a cycle weight
or resource objective.

For necessity, take a successful literal table with $s\le K$ states.
Relabel its states, preserving instructions and successors, to one
enumerated graph. Descriptor completeness supplies, for each installed word
$p_e$, a descriptor $\delta_e$ satisfying
$\operatorname{Valid}(\delta_e)\land p_e\in\operatorname{Real}(\delta_e)$;
its type contributes to the enumerated tuple $\mathbf b$. All visits to that
state retain that word. By (UDB.4), the installed word and the chosen
$p(\delta_e)$ give identical
replies on every admitted source at every epoch. Induction on instructions
therefore preserves the table's execution when that chosen realization
is used. Every original source has its unique admitted tuple and actually
halts. Theorem 3.4 proves Total. If two sources reach one halt, correctness says both
complete rows equal its single installed $Y_h$. Exact Same proves Shared.
Thus this table makes one disjunct of (UDB.17) true.

For sufficiency, take a true graph/type disjunct and extract a satisfying
numeric tuple. One effective extraction is to enumerate natural tuples by
increasing coordinate sum and decide the remaining Presburger formula
after substitution; existential truth guarantees termination of this
positive extraction. Realize each descriptor **once** by $p(\delta_e)$.
All-chart, all-epoch exactness makes these the same literals whose halt
supports were computed.

For each halt, decide

$$
\operatorname{Reach}_h\ \Longleftrightarrow\
\bigvee_{\eta\in\mathcal A}\exists\mathbf n\quad
\operatorname{Adm}_\eta(\mathbf n)\land H_{\eta,h}(\mathbf n;\boldsymbol\delta).
\tag{UDB.18}
$$

If true, extract one admitted witness tuple, construct the finite original
source $u_h=\Theta_\eta(\mathbf n)$ and its entire row $R(u_h)$, and install
that literal at $h$. Shared and (UDB.2) ensure that every other source
reaching $h$ has that very row. If false, install $Y_*$ there. Now fix any
$u\in D$. Total and Theorem 3.4 force its actual finite first halt; that
halt is reachable, and its installed row equals $R(u)$. All choices of
witness sources are offline output construction, not new online source
access. The extracted controller is the selected graph itself. Phase
vectors, epochs, chart tags, cut witnesses and descriptor evaluators do
not become extra readable states or instructions.

For rejection, effective Presburger reduction may eliminate the descriptor
and source quantifiers, using congruences with fixed moduli if needed, to
closed arithmetic truth values. A negative answer consists of the finite
graph/type list and finite arithmetic reductions showing that each
$\Phi_{G,\mathbf b}$ is false. Equivalently, its definable good-descriptor
set is empty for each listed graph/type. This rejects unbounded parameter
domains symbolically; it need not be one fixed finite collection of sources
that defeats every installation. It is a mathematical finite rejection,
not a claim that a particular certified solver has been run.

If $K=0$, the graph disjunction is empty and false because controller
states are nonempty. If $D=\varnothing$ and $K\ge1$, a one-state initial
halt with row $Y_*$ succeeds vacuously. For a nonempty family, an initial
halt succeeds exactly when its one output equals every complete target
row. These conventions also agree with (UDB.16). $\square$

**Theorem 4.3 (independence from a particular source representation).**
Suppose two effective presentations satisfy the hypotheses for the same
original-source family, physical permitted literals, transport, entry
epoch, actual replies and complete target $R$. Their arithmetic sentences
(UDB.17) have the same truth value for every $K$, and each extracted
literal table works on the common original task. No Presburger coordinate
change between their charts is required. The conclusion also holds for a
second task $(D',U',r',R')$ under a supplied effective bijection
$\psi:D\to D'$ with the same permitted literals and entry epoch, satisfying

$$
\forall u\in D\;\forall j\in\mathbb N\;\forall p\in\mathcal W\quad
r'_{U'^j\psi(u)}(p)=r_{U^ju}(p),\qquad R'(\psi(u))=R(u).
$$

An intertwining map on the full register carriers which restricts to
$\psi$ supplies the displayed reply correspondence when it also
preserves literal reads. The formula does not apply $\psi$ to a
transported register outside its original-source domain.

Proof 4.3. A successful table is defined by its literal instructions and
actual executions on original sources. Theorem 4.2 identifies each
presentation's sentence with existence of exactly such a table. Thus
both truth values coincide. In the bijective version, induction on
instructions transports the same replies, successors, epochs and output
rows. The admission and reply formulas remain obligations of each
presentation: merely re-encoding arbitrary relations does not make those
formulas Presburger. $\square$

For a prescribed graph rather than a state budget, its finite type
disjunction gives the same decision with that graph fixed. For an observer
which never updates, restrict enumeration to $E_U=\varnothing$. The
full result concerns existence and extraction, not optimal installation
size, efficient computation or a universal physical stopping bound.

## 5. Boundary factorization and the exact source-removal condition

**Definition 5.1 (boundary of an admitted execution history).** Fix one
installed table from a graph and valid common descriptor tuple, with
$p(\delta_e)$ at each read state. Any other realization has the same
replies by (UDB.4). Let $\mathcal X$ be its finite execution histories from
the common start on sources $u\in D$, including first halt. A history $s$
has immutable original-source coordinate
$\lambda(s)=(\eta,\mathbf n)$, control $e(s)$ and update epoch $j(s)$.
The action labels are $\mathsf{Read}_e$ for $e\in E_R$,
$\mathsf{Update}_e$ for $e\in E_U$, and $\mathsf{Stop}$. A state-indexed
action is enabled exactly at its named state; $T_a$ appends that actual
instruction and its actual response to the history. Stop is enabled at a
halt and acts as identity, so the history space need not include
additional post-termination instructions.
Define the retained row accumulator

$$
A(s)=\begin{cases}
\mathsf{Pending},&e(s)\notin E_H,\\
\mathsf{Done}(Y_{e(s)}),&e(s)\in E_H.
\end{cases}
\tag{UDB.19}
$$

The tags distinguish a pending empty row from a completed empty row.
Here the accumulator is finite-valued and determined by the complete
control state. It can equally be stored in that state. This notation
does not grant a free unbounded memory register. For a flattened
finite-accumulator table, use its actual finite accumulator value instead.

The **observable boundary form** is

$$
b(s)=\bigl(e(s),j(s),V_{\Theta(\lambda(s))}(j(s)),A(s)\bigr).
\tag{UDB.20}
$$

The response-vector component is the finite phase value, not just its
ordinal position in a list of phases. The mathematical exact interface
with source context retained is

$$
\mathfrak e(s)=\bigl(\lambda(s),b(s)\bigr).
\tag{UDB.21}
$$

Its observable portion has exactly the four fields in (UDB.20). Its
source coordinate is immutable semantic context, not an observation
available to the installed controller. A family-indexed transition on
the observable portion is different from a single autonomous transition
that has discarded that context. This distinction is necessary even
when all replies are monotone. Here observable refers to the declared
response and output semantics of the external execution model; it does
not mean the controller has measured every vector component or can read
its epoch.

For a valid descriptor tuple, call the installed halt outputs
**reachable-witness-installed** when

$$
\begin{aligned}
\forall\eta\in\mathcal A\;\forall\mathbf n\in\mathbb N^{d_\eta}\;\forall h\in E_H\quad
&\left(\operatorname{Adm}_\eta(\mathbf n)\land
H_{\eta,h}(\mathbf n;\boldsymbol\delta)\right)\\
&\Longrightarrow Y_h=R(\Theta_\eta(\mathbf n)).
\end{aligned}
\tag{UDB.22a}
$$

The reachable-witness construction in Theorem 4.2 installs halt rows with
this property: it chooses a complete row from one admitted witness for every
reachable halt, while **Shared** and (UDB.2) show that every source reaching
that halt has the same row. An unreachable halt receives $Y_*$. **Total** and
**Shared** alone do not impose (UDB.22a) on an arbitrary
preinstalled $Y_h$.

**Theorem 5.2 (boundary factorization and task correctness).** Under the
interface hypotheses, the source-context interface $\mathfrak e$ is
dynamically sufficient on admitted execution histories. For every
prescribed instruction action $a$, including absorbing stop, there is
a well-defined boundary transition satisfying

$$
\mathfrak e(T_a(s))=\overline T_a(\mathfrak e(s))
\tag{UDB.22}
$$

whenever that instruction is enabled. Equivalently, for each fixed
original coordinate $\lambda$, the four-field observable boundary satisfies
$b(T_a(s))=\overline T_{a,\lambda}(b(s))$. For a table satisfying Total and
Shared, whose halt outputs are reachable-witness-installed in the sense of
(UDB.22a), the decoder $\mathsf{Done}(Y)\mapsto Y$ returns the complete
$R(u)$ on every terminal admitted history.

The observable form $b$ alone admits a single autonomous factorization
$bT_a=\overline T_a b$ across all original sources **if and only if** it
has the following successor-consistency property:

$$
\begin{aligned}
\forall s,t\in\mathcal X\quad b(s)=b(t),\ e(s)\in E_U
\ \Longrightarrow\
V_{\Theta(\lambda(s))}(j(s)+1)
=V_{\Theta(\lambda(t))}(j(t)+1).
\end{aligned}
\tag{UDB.23}
$$

This iff is for the instruction and accumulator convention in Definitions
2.1 and 5.1. If additional actions have source-dependent permission or
effects, their enable predicates, declared response observations and
successor boundaries must also be constant on $b$-fibers. That is the
exact additional condition, rather than a claim that all summaries work.

Proof 5.2. With $\lambda$ fixed, Reply determines the vector at every
epoch. A read at $e$ uses $v(e)$, takes $s_R(e,v(e))$, leaves $j$ and $v$
unchanged, and sets the accumulator to its new state's value. An update
takes $s_U(e)$, increments $j$ by one, uses the same $\lambda$ to determine
the new vector by exact Reply, and sets the new accumulator. An absorbing
stop leaves all fields fixed. The same boundary and coordinate therefore
have the same enabled instruction, response and successor. These rules
define $\overline T_a$ and prove (UDB.22) on the actual image of
$\mathfrak e$. They remove the full history and transported register
representation; they keep the source dependency of future responses.

If $b(s)=b(t)$ without requiring equal source coordinates, reads still
have the same current vector and successor, and absorbing stops still
agree. At an update all successor fields other than the new vector are
already determined by the common old fields and table. Hence (UDB.23)
is sufficient for equality of complete successor boundaries. Define
$\overline T_a(b(s))=b(T_a(s))$; that equality makes the definition
independent of representative. Conversely, any such autonomous map forces
equality of successor boundaries and therefore of their new vector
components, proving (UDB.23). Induction on a common enabled continuation
then preserves all subsequent boundary observations.

For a partial-action extension, the same construction requires enable
predicates to agree on each fiber before a successor is defined, and
requires declared observations and successor images to agree there.
Necessity follows by taking one action; sufficiency follows by defining
on representatives and inducting on action words. This is the operational
fiber criterion used in [Context Geometry, §3][CG], here with exact
same-source arithmetic response and output data. Finally Theorem 3.4 gives
actual termination from Total. The factorization claims use no
installed-output condition. For terminal decoding, (UDB.22a) applied to the
actual first halt gives $Y_h=R(u)$; in the extracted tables of Theorem 4.2,
the reachable-witness construction establishes this condition. Shared and
exact Same by themselves only identify the rows of sources that reach one
halt with one another; they do not identify an arbitrary preinstalled $Y_h$
with that common row. $\square$

**Definition 5.3 (arithmetic reachable-boundary predicate).** Let
$\mathcal B_{\eta,e}(\mathbf n,J;\boldsymbol\delta)$ be the formula
(UDB.12)–(UDB.13) with final $P_{v_{m-1}}(x_{m-1},e,d_{m-1})$ in place
of its halt endpoint. Its meaning is finite arrival at state $e$, epoch
$J$, before any earlier halt, or first arrival at a halt if $e$ is one.
The proof of Theorem 3.4 applies without requiring the endpoint to halt:
a finite actual prefix supplies cuts, and a guarded concatenation
supplies that prefix. Thus $\mathcal B$ is effective Presburger and exact.
For fixed $v$, put

$$
\mathcal V_{\eta,v}(\mathbf n,j;\boldsymbol\delta)
=\bigwedge_{e\in E_R}\operatorname{Reply}_{\eta,v(e)}(\mathbf n,j,\delta_e).
\tag{UDB.24}
$$

**Theorem 5.4 (effective test for autonomous boundary sufficiency).** For
each fixed graph/type choice and valid descriptor tuple, condition
(UDB.23) is an effective Presburger property of that tuple. More
precisely, it is equivalent to absence of witnesses in the following
finite disjunction, where the outer choices are
$\eta,\theta\in\mathcal A$, $e\in E_U$ and $v,w,z\in\mathcal C^{E_R}$ with
$w\ne z$:

$$
\begin{aligned}
\exists\mathbf n\;\exists\mathbf m\;\exists j\in\mathbb N\quad
&\operatorname{Adm}_\eta(\mathbf n)\land
\operatorname{Adm}_\theta(\mathbf m)\land\\
&\mathcal B_{\eta,e}(\mathbf n,j;\boldsymbol\delta)\land
\mathcal B_{\theta,e}(\mathbf m,j;\boldsymbol\delta)\land\\
&\mathcal V_{\eta,v}(\mathbf n,j;\boldsymbol\delta)\land
\mathcal V_{\theta,v}(\mathbf m,j;\boldsymbol\delta)\land\\
&\mathcal V_{\eta,w}(\mathbf n,j+1;\boldsymbol\delta)\land
\mathcal V_{\theta,z}(\mathbf m,j+1;\boldsymbol\delta).
\end{aligned}
\tag{UDB.25}
$$

Writing $\operatorname{PC}_G$ for its negation, existence of a successful
at-most-$K$ table whose bare observable form is autonomously sufficient
is also decidable: add $\operatorname{PC}_G(\boldsymbol\delta)$ within
the existential scope of (UDB.16), and use the same finite enumeration.
This additional demand is not imposed on $\mathsf{Solve}_K$ itself.

Proof 5.4. Equal bare boundaries at an update have the same $e,j,v$.
Their accumulators agree automatically under (UDB.19). Exact finite-prefix
arrival supplies the two $\mathcal B$ predicates. Failure of successor
consistency supplies distinct $w,z$; exact Reply supplies all four vector
predicates. Conversely each witness reconstructs two admitted histories
with those shared boundary fields and distinct next vectors. This proves
the equivalence. Every part of (UDB.25) is Presburger, and all vector,
state and chart choices are finite. Negation and the outer descriptor
existential preserve that property. Theorem 4.2 supplies the rest of the
successful-table equivalence and extraction. $\square$

Thus a successful finite controller and an autonomous predictive boundary
are different requirements. The source-context interface always provides
the exact factorization; its source-free version does so precisely when
the additional arithmetic test passes. Neither adds a clock, source
coordinate port or response-vector port to the actual controller.

## 6. Paired histories, essential distinctions and redundant fields

**Theorem 6.1 (a phase value cannot generally be deleted from a source-free
boundary).** There is a two-source finite relational task satisfying all
the interface hypotheses and (UDB.23), with a successful three-state
table, for which deleting the phase vector from $b$ merges two histories
with different immediate responses and outputs.

Proof 6.1. Let $D=\{u_0,u_1\}$ be finite one-port records. Their target
rows are distinct $Y_0,Y_1$. Use one chart with $\operatorname{Adm}(n)$
equal to $n=0\lor n=1$, and $\operatorname{Same}(n,m)$ equal to $n=m$.
Let $U$ be identity. There is one permitted literal $p$, one parameterless
valid descriptor realizing it, and ordered replies $c_0<c_1$ with ranks
zero and one. Here $c_0=\mathsf{absent}$ and $c_1$ reports the single
reached content. Source $u_n$ replies $c_n$ at every epoch. Take $N=0$.
The port is absent forever for $u_0$ and reached forever for $u_1$;
reached transport is identity. Reply is the exact formula $n=i$ for $c_i$.

The initial state $e$ reads $p$ and sends $c_i$ to halt $h_i$ with row
$Y_i$. The two initial histories have the same $e,j=0,A=\mathsf{Pending}$,
but phase vectors $(c_0)$ and $(c_1)$. Their next replies and halts differ.
There are no update states, so (UDB.23) holds vacuously; the full bare
boundary is sufficient, but its phase-deleted projection is not. All
sources, ports and table states in the example are finite. $\square$

If the exact source coordinate and epoch are retained, deleting the phase
vector is harmless: (UDB.4) reconstructs it. For a source-free projection,
the exact additional hypothesis is that its fibers have identical declared
current responses, enabled actions and projected successors. One cannot
prove that a redundant vector is indispensable merely by counting its
coordinates.

**Theorem 6.2 (current phase does not replace predictive source context).**
There is a two-source finite relational task satisfying every interface
hypothesis, with a successful four-state table, such that identical
$(e,j,v,A)$ histories have different successor response vectors. Hence
deleting the source chart coordinate from $\mathfrak e$ fails, and
monotone bounded-rank replies do not imply (UDB.23).

Proof 6.2. Take finite records $u_n$ with threshold $n\in\{1,2\}$ and a
single port $p$. The plant stores a progress value $k\in\{0,1,2\}$, starts
at zero and updates to $\min(k+1,2)$. The port is reached precisely when
$k\ge n$, and its ordered reply is $c_0=\mathsf{absent}$ before reach and
$c_1$ after. Use ranks zero and one and entry epoch $N=0$.
Reached content has identity transport and persists. Consequently at
epoch $j$ its exact reply is $c_1$ iff $j\ge n$. Use the chart
$\operatorname{Adm}(n)\equiv n=1\lor n=2$, exact Same $n=m$, a single
parameterless descriptor and distinct target rows $Y_1,Y_2$.

The initial state $a$ updates to read state $e$. That read sends $c_1$ to
halt $h_1$ with row $Y_1$ and $c_0$ to halt $h_2$ with row $Y_2$. This
four-state table correctly halts for both sources at epoch one. At their
initial histories the bare boundaries are both
$(a,0,(c_0),\mathsf{Pending})$. After the update their vectors are
respectively $(c_1)$ and $(c_0)$. The immutable chart coordinates separated
these histories; their present phases did not. All numeric relations are
the stated Presburger inequalities and finite admission conditions.
$\square$

The exact additional hypothesis for deleting that coordinate is (UDB.23),
together with the corresponding legality and observation conditions if
more actions are admitted. It can hold for some families and fail for
others; source-independent future schedules determined by the current
bare boundary are a sufficient condition. The example also shows why
source coordinates in phase guards cannot be independently replaced by
coordinates producing the desired answer in each phase.

**Theorem 6.3 (terminal output distinctions must survive terminal merging).**
There is a two-source finite relational task and a successful finite table
whose terminal histories have the same epoch and phase vector but distinct
correct complete rows. In their source-free boundaries $b$, identifying
their halt controls as one generic halt and deleting the retained row
makes correct decoding impossible.

Proof 6.3. Take $D=\{u_0,u_1\}$ and rows $Y_0\ne Y_1$. At its single
port, $u_0$ replies $c_0$ at epoch zero and $c_1$ at all epochs $j\ge1$;
$u_1$ replies $c_1$ at all epochs. This is implemented by a finite plant
with a one-step persistent reached flag. The chart is $n\in\{0,1\}$,
Same is $n=m$, and the exact $c_1$ formula is $n=1\lor j\ge1$. The one
descriptor, reached transport and monotonicity are as in the preceding
examples.

The initial read sends reply $c_i$ to update state $a_i$, and $a_i$ sends
its one update to halt $h_i$ with installed row $Y_i$. At both terminal
histories $j=1$ and $v=(c_1)$. The histories have respective pairs
$(h_i,\mathsf{Done}(Y_i))$. Replacing these pairs by a single unlabelled
terminal symbol gives equal projected boundaries. Any decoder on that
projection has one output there, and cannot equal both distinct required
rows. $\square$

Deleting $A$ alone while retaining the distinct complete halt states is
safe, since $A$ is recoverable from $h$. Retaining $A$ allows the halt
controls to be merged only when all remaining successor and legality
requirements also descend. Deleting **both** forms of output distinction
is safe exactly when the complete target row is constant on each merged
terminal fiber. Equal masks or equality of only one row field do not
establish that condition. Likewise, the pending/complete tag can be
deleted only if another retained field still determines whether output
has completed. These are conditions on information retained by the
projection, not assertions that every listed field is separately minimal.
If exact source coordinates are instead available to a decoder, it can
compute $R(\Theta(\lambda))$ independently. The terminal counterexample
concerns the source-free retained interface; it does not install that
source-coordinate port in the controller.

## 7. Spatial readout, temporal transport and exact relation recovery

**Definition 7.1 (a supplied spatial and temporal correspondence).** Let
$\mathcal Z$ be the declared spatial interface addresses. Supply an
effective assignment $z\mapsto\delta(z)$ to valid descriptors, with the
same chosen literal $p(\delta(z))$ at every source. If the spatial task is
finite, its required addresses form a supplied finite set. Supply a
temporal correspondence $\tau:\mathbb N\to\mathcal T$ and physical or
abstract configuration maps $\iota_j$ satisfying, on the same admitted
original source,

$$
\iota_{j+1}(u)=U(\iota_j(u)),\qquad \iota_j(u)=U^ju,
\qquad \text{progress after }d\text{ actual updates is }\tau(N+d).
\tag{UDB.26}
$$

If a different carrier is used, replace the middle equality by a supplied
representation map intertwining its actual update with $U$. The declared
spatial reply at $(z,\tau(j))$ must equal
$r_{U^ju}(p(\delta(z)))$. The temporal map need not be injective; recovering
$j$ from its temporal label additionally requires an inverse on the
relevant image. Neither a descriptor nor $\tau$ supplies a wall clock.

**Theorem 7.2 (spatial/temporal recovery corollary and its converse boundary).**
Under Definition 7.1 and the exact interface hypotheses, the same
source-context boundary recovers all declared spatial replies by Reply
and recovers temporal progress by its epoch and $\tau$. It recovers the
complete original target row on termination for every extracted successful
table. If the spatial probes are the table's installed probes, their
current readout is exactly its boundary phase vector. For additional
declared probes, use their supplied descriptors with the same original
coordinate. For a finite enlargement of the probe list, under the
successor-consistency condition for that enlarged finite response vector,
the source-free boundary also transports those readouts autonomously.

Conversely, if Reply or Same is replaced by a weakened predicate, soundness
and completeness require separate conditions. With the other hypotheses
retained, positive extraction (soundness) of a reachable-witness-installed
table is guaranteed if weakened Reply implies the actual literal reply on
every admitted source, valid descriptor and realization at every epoch,
and weakened Same implies actual complete-row equality on all admitted
pairs. These implications suffice on the task's domain; no claim about
arguments outside that domain is required.

For completeness, the reverse implication from actual Reply to weakened
Reply supplies inclusion of actual traces only. If weakened Reply enlarges
halt support, Shared is evaluated on the enlarged support and can reject a
previously successful table. With the other hypotheses retained and actual
complete-row equality implying weakened Same, completeness is guaranteed
if Reply is exact, or if the weakened halt supports equal the actual halt
supports for each represented successful table, or if actual supports are
included and another supplied condition preserves Shared on every enlarged
support. Equality of halt supports here concerns the represented literals;
it includes the chosen realizations used in extraction. Thus task-specific
exactness may survive weaker global predicates. A weakening alone does not
show that exact recovery fails; without the appropriate task-level
guarantees, arithmetic consistency of a coarse summary establishes only an
approximation, and postprocessing cannot supply a missing distinction.

Proof 7.2. For $u=\Theta_\eta(\mathbf n)$, substitute the common
$\delta(z)$ and actual epoch $j$ in (UDB.4). Definition 7.1 identifies the
resulting literal reply with the declared spatial one. The number of
updates increments $j$ by exactly one, so (UDB.26) identifies its temporal
progress. Theorem 5.2 transports the joint same-source state, and Theorem
4.2 supplies the complete terminal row. Enlarging the vector requires
applying the same successor-fiber criterion to that enlarged interface;
unrecorded probes are not automatically determined by the old vector.

For positive extraction under the stated one-way implications, each
weakened phase guard still supplies the actual reply at every read of its
witnessed path. The concatenation in Proof 3.4 is therefore an actual finite
first-halt trace, so weakened halt support is contained in actual halt
support. Weakened Total supplies such a trace for every admitted source.
Install one witness's complete row at each supported halt as in Proof 4.2.
Weakened Shared and the implication from weakened Same to actual complete-row
equality make that row correct for every source in that support. Determinism
and Total ensure that every actual run reaches its witnessed halt; defaults
at unsupported halts are never used. This proves positive extraction without
requiring the converse implications.

For completeness, actual Reply implying weakened Reply keeps each actual
trace and its bounded phase partition as witnesses, hence preserves Total.
Actual complete-row equality implying weakened Same establishes Shared on
the actual supports, but not necessarily on added supports. For an explicit
counterexample, take two finite one-port sources $u_0,u_1$ with permanent
replies $c_0,c_1$, identity transport, entry epoch zero and distinct complete
rows $Y_0\ne Y_1$. Use one singleton literal descriptor and exact Same. A
three-state table reads the port and sends $c_i$ to halt $h_i$ with row
$Y_i$; it succeeds on both sources. Replace both reply predicates by true.
Actual Reply implies weakened Reply, but each weakened halt support now
contains both sources. Shared with exact Same is false at each halt because
the two complete rows differ. The successful table is rejected by the
weakened arithmetic criterion. This is a completeness failure, not a claim
that every weakening fails.

Under exact Reply the supports stay exact as in Proof 3.4, and the stated
row-equality implication supplies Shared for every successful table.
Exact halt support is enough for the same argument even when Reply is
globally weaker. More generally, trace inclusion supplies Total and a
condition preserving Shared on all enlarged supports supplies the remaining
clause. These are sufficient replacements for completeness; they do not
assert that global semantic biconditionals are necessary for every task.

For the negative boundary, take two finite one-port records with identical
summary but replies $c_0\ne c_1$. A single reply value selected from that
summary is wrong for one of them; a set containing both is an approximation,
not an exact deterministic reply. Likewise take two sources with identical
coarse row mask but distinct whole-subobject equality partitions. If
$\widetilde{\operatorname{Same}}$ declares them equal on their mask, a
shared halt may be arithmetically accepted although no one complete row
fits both. These illustrate particular missing soundness implications,
not failure of every weakening. An under-approximate Same can instead
reject a genuinely common row, and an under-approximate Reply can omit a real
trace; those are completeness
failures. Other weakened predicates may remain exact on a restricted task, or
may have their missing direction restored by another supplied relation. A
function of identical summary values cannot separate either pair. $\square$

This corollary is relation-level recovery under a supplied correspondence.
It provides no physical timing, distance, metric, simultaneity, acquisition
procedure, authenticated handoff or installation mechanism. Extra probes
require their actual permitted access. The epoch in the proof counts
updates, not elapsed read or serialization time. No statement here turns
an ordinary mathematical proof into Lean verification or gives arbitrary
signed-fiber coverage.

## 8. Consumers, suppliers and the remaining general-fiber gap

**Definition 8.1 (supplier correspondence).** The following existing
results supply concrete parts of the abstract contract. Their conclusions
retain their original scopes.

| Supplier | Exact consumption and limit |
| --- | --- |
| [NPS, Definitions 1.2 and 2.2–2.3; Theorems 3.2 and 4.2][NPS] | Supplies the native cycle-covered instance of exact all-epoch literal descriptors, reached-address rank phases, fixed-response paths and common-descriptor/shared-halt synthesis. Sections 1–4 abstract its interface; Sections 5–6 add the exact autonomous-boundary test and source-context obstruction. The native phase bound specializes to $3r+1$. |
| [CAR, Theorem 3.2, Lemma 4.1 and Theorem 6.2][CAR] | Supplies finite whole-source charts, joint admission, full-row equality and common physical-word realization for cycle-covered recognition. Those are hypotheses here, not consequences for every signed fiber. |
| [NIC, Theorems 3.2–3.3 and 4.3][NIC] | Supplies complete positive image normalization, original-native signed pullback and whole original-source row strata, retaining shared occurrences and both signed endpoint guards. An image cover with residual variables or native restrictions is not automatically a finite disjoint Presburger chart union. |
| [SLP, Lemma 2.1, Theorem 3.1 and Corollary 3.2][SLP] | Supplies simultaneous finite signed prefix witnesses at a fixed feasible scalar tuple and the precise scalar-support closure criterion on its declared Cartesian grammar. It does not supply all-depth uniform literal Reply or whole-row Same for arbitrary residual fibers. |
| [Context Geometry, §3][CG] | Supplies the operational principle that observations and allowed successors must descend on boundary fibers. Theorems 5.2–5.4 instantiate it with explicit reachable arithmetic supports and distinguish immutable source context from autonomous boundary dynamics. |
| [Ginsburg–Spanier, §1, Theorems 1.2–1.3][GS] | Supplies decidability of natural Presburger sentences and the effective semilinear correspondence, used only after the displayed exact interface reductions. It supplies no decision theorem for arbitrary finite relational structures or native trees. |

**Definition 8.2 (explicit consumer and unresolved interface problem).**
The consumer is a prescribed finite-state observer or read/update/halt
controller recovering a complete original relation row over an entire
source family. It consumes finite chart and descriptor data, exact joint
predicates and a reached-address monotonicity law. It can be a native
controller, a finite relational register controller or another effectively
presented task with these same interfaces. Its synthesis decision and
positive literal extraction are independent of which qualifying chart
presentation supplied them.

The remaining project gap is to prove these interface hypotheses for
**general signed fibers outside cycle-covered recognition**, including
unforced non-atomic skeletons and jointly constrained residual coordinates.
In particular, one needs a complete finite arithmetic representation of
the same original sources, exact whole-row Same, descriptor coverage by
common literals and all-source/all-epoch exact Reply. A finite image cover,
a feasible fixed-rank witness or a bounded-prefix lifting result by itself
does not supply those relations. This volume proves what follows if they
are supplied; it does not solve that missing interface problem.

No result here establishes minimality of the native $\alpha/\beta$ alphabet,
native undecidability, a complete solver for arbitrary signed residual
fibers, physical spacetime, cost-optimal installation, or Lean/kernel
verification. In particular, failure to verify an interface is not a
negative instance of (UDB.17), and failure of a source-free boundary is
not failure of the original finite-controller task.

**Definition 8.3 (primary arithmetic source).** Seymour Ginsburg and Edwin
H. Spanier, *Semigroups, Presburger Formulas, and Languages*, Pacific
Journal of Mathematics **16**(2), 285–296, DOI
[10.2140/pjm.1966.16.285][GS-PAGE], §1, Theorems 1.2–1.3, is the primary
literature used here. Theorem 1.2 states decidability of natural-number
Presburger sentences; Theorem 1.3 states effective equivalence with
semilinear descriptions. The finite functional-orbit calculation is given
explicitly in Definition 3.1 rather than importing a general
counter-machine reachability theorem. The new ordinary deductions make
no claim that their abstract packaging or boundary test is an externally
unprecedented result.

[NPS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PHASE_SYNTHESIS.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[CG]: RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[GS-PAGE]: https://msp.org/pjm/1966/16-2/p09.xhtml

## 追加锚（本行以下为增补区）
