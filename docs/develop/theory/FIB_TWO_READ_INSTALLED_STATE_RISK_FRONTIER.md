# FIB two reads: the exact installed-state classification-risk frontier

For the original stationary biased XOR source, the best correct mass
with almost-sure return within two paid calls and at most $m$ installed
complete-controller rows is

$$
C_m=
\begin{cases}
a/2,&m=1,2,\\
a/2+a\eta,&m=3,\\
a/2+a\eta(1+c),&m=4,5,\\
a/2+a\eta+a^2\eta,&m\ge6,
\end{cases}
\qquad
\eta=ab,\quad c=a^2+b^2,
$$

where $a=\max(p,1-p)$ and $b=\min(p,1-p)$ for a fixed biased
interior parameter. All these values are attained on the same original
source, for either original endpoint and every unchanged independent
seed law. The minimum classification error is $R_m=1-C_m$.
In particular the exact error penalty at four or five rows relative
to six is $\eta^2(a-b)>0$.

This volume presents the supplied ordinary installed-state frontier
derivations with complete proofs. The additional content relative to
the three preceding theory sources is the quantitative four/five-row
plateau, the bounds on all installed tables, and the exact positive
penalty. The unrestricted one- and two-read optima, their attainers,
and their attainment rigidity and minimum three/six-row costs retain
their ownership in Original, Risk and Endpoint as specified in §11.
These are ordinary mathematical arguments, without a formal-kernel,
physical-memory, empirical-learning or worldwide-priority claim.

## 1. The original stationary law and its actual endpoint

**Definition 1.1 (Source and parameter range).** Fix $0<p<1$ with
$p\ne1/2$. Let $\varphi$ be uniform on $\{0,1\}$ and independent of
iid Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. The four
symbols in $\mathcal A=\{a_0,a_1,b_0,b_1\}$ are distinct. On the
original integer clock put

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Denote this joint law by $J_p$. It is Original, Proposition 2.1 and
(2.2). To check its clock and stationarity directly, write
$\pi_0=1-p$, $\pi_1=p$. An active transition takes $a_s$ to $b_t$
with probability $\pi_t$ and emits $s\oplus t$; the next transition
takes $b_t$ to $a_t$ and emits zero. The proposed stationary mass
$\pi_s/2$ at each $a_s,b_s$ is preserved: the incoming mass at $b_t$
is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and the copying transition gives
the same mass at $a_t$. The independent uniform phase in (1.1)
realizes this stationary integer-clock law. Consecutive visible ones
are impossible. Separator positions remain actual coordinates.

Fix one $j\in\{0,1\}$ before any acquisition. The target is the
actual hidden state $H_j$, with the following identification:

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{1.2}
$$

For this fixed endpoint define

$$
\begin{aligned}
h_0(s)&=\begin{cases}a_s&j=0,\\b_s&j=1,\end{cases}&v_0&=j,\\
h_1(s)&=\begin{cases}b_s&j=0,\\a_s&j=1,\end{cases}&v_1&=0.
\end{aligned}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.3}
$$

The two phase-label sets are disjoint. A single returned state cannot
be correct in both phases. The representation gives no access to
$\varphi$ or an unobserved spin.

**Definition 1.2 (Majority notation).** Set

$$
a=\max(p,1-p),\quad b=\min(p,1-p),\quad
\eta=ab,\quad c=a^2+b^2=1-2\eta,
\qquad
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2.\end{cases}
\tag{1.4}
$$

Thus $S_\ell=\sigma$ has probability $a$, and

$$
\begin{gathered}
a+b=1,\quad 0<b<1/2<a<1,\quad 0<\eta<1/4,\quad 1/2<c<a<1,\\
a-c=b(a-b)>0,\qquad 2a^2-c=a^2-b^2>0.
\end{gathered}
\tag{1.5}
$$

For example $c>1/2$ follows from $a\ne b$, and the displayed
identity for $a-c$ proves $c<a$. These strict inequalities will keep
all parameter comparisons on the entire stipulated range.

## 2. Paid acquisition and literal installed state

**Definition 2.1 (Full original protocol class).** Let
$(\mathsf U,\mathcal U,\nu)$ be any probability space independent of
the whole $J_p$ source, with its law unchanged. All random public data
and internal randomness belong to the same auxiliary variable $u$;
fixed public data are constants. An acquired record is a finite ordered
list $r=((t_1,x_1),\ldots,(t_n,x_n))$ of integer addresses and binary
replies. A measurable next-event rule, using only $u$, the fixed public
data and $r$, requests an integer address, returns a label in
$\mathcal A$, or continues internally forever without another read or
return. Finite events can follow internal waiting, whose finite
duration and occurrence depend measurably only on the same data.

Every requested address returns the actual $X_t$ of (1.1), and every
actual request costs one call. Repetitions, ignored replies,
separators, negative coordinates, disconnected sets and arbitrary
distances are all charged. The return time is $\tau$, with
$\tau=\infty$ on nonreturn, and $N$ counts all actual calls, allowing
$N=\infty$. The full class allows internal nonreturn after any finite
number of calls, including zero, and infinite-read nonreturn. A finite
return has finite $N$, and its label and time are measurable functions
of the available data and terminal record. Zero-read returns and
wrong-phase labels are permitted. Measurable completions on null sets
are allowed.

There is no hidden-state, half-line or tail read, source-dependent seed
or timing, reset, law switch, endpoint movement, or erased-coordinate
substitution. This is the contract of Original, Definition 9.1, also
given in Risk, Definition 1.2 and Endpoint, Definition 1.2. Write
$\mathbb P_p=J_p\otimes\nu$.

**Definition 2.2 (Complete installed controller).** An installed table
is $(K,\lambda,\delta,c_{\rm init})$, where $K$ is nonempty and finite,

$$
\begin{aligned}
\lambda &:K\longrightarrow
\{\operatorname{Read}(t):t\in\mathbb Z\}
\sqcup\{\operatorname{Halt}(h):h\in\mathcal A\},\\
\delta &:K_{\rm R}\times\{0,1\}\longrightarrow K,
&c_{\rm init}&:\mathsf U\longrightarrow K
\end{aligned}
\tag{2.1}
$$

and $c_{\rm init}$ is measurable for discrete $K$.
The sets $K_{\rm R},K_{\rm H}$ are the read and halt rows. Initialize
the current row to $c_{\rm init}(u)$. At a read row with literal
address $t$, make one paid call to $X_t$ and set the current row to
$\delta(r,X_t)$. At a halt row return its fixed label and end.
Each instruction takes finite duration; there are no silent
instructions. An execution that does not reach a halt makes charged
reads forever.

The current row is the entire runtime state after initialization.
There is no extra program position, counter, phase bit, clock port,
archive, stack, output latch, saved last reply, runtime address
computation or seed reaccess. A reply is available only for its
immediate transition. Durations provide no observation or additional
branching. All installed rows count in $|K|$, including duplicate
instructions, unused rows and rows on null paths. The fixed public
$p,j$ can determine the table and its integer literals.

This is Endpoint, Definition 8.1, literally. Such a table is a legal
protocol of Definition 2.1. It is a specified subclass; the original
protocol class is larger. Cycles and arbitrarily long formal paths
are allowed in the installed class.

**Definition 2.3 (The frontier).** With $A$ the returned label, for
$k\in\{1,2\}$ put

$$
E_k=\{\tau<\infty,N\le k\},\qquad
q_k=\mathbb P_p(E_k),\qquad
L_k=\mathbb P_p(A\ne H_j,E_k).
\tag{2.2}
$$

For $m\ge1$ define, over precisely the tables of Definition 2.2,

$$
\begin{aligned}
C_m(p,j,\nu)&=\sup\{q_2-L_2:|K|\le m,\ q_2=1\},\\
R_m(p,j,\nu)&=\inf\{L_2:|K|\le m,\ q_2=1\}.
\end{aligned}
\tag{2.3}
$$

The admissible sets are nonempty because an immediate halt is legal.
The condition $q_2=1$ is almost sure: source-null nonreturns or paths
with more calls remain in the comparison class. It is not an all-input
hard cap. Since $E_2$ has mass one, $R_m=1-C_m$, and classification
error is unconditional up to a null extension of $A$. Classification
of the four-valued hidden endpoint differs from squared loss for an
erased visible bit.

## 3. Source sections and initialization cells

**lemma 3.1 (Finite acquired sections).** For a measurable next-event
representative at a fixed seed, a consistent finite acquired record
has source section exactly

$$
C(r)=\bigcap_{i=1}^n\{X_{t_i}=x_i\}.
\tag{3.1}
$$

An inconsistent sequence of prescribed choices has empty section.
An output after a consistent terminal record is fixed on its section.
These assertions also hold for reachable prefixes.

Proof. The empty record imposes no condition. At a fixed seed and
prefix, the next action and internal waiting are fixed. Requesting
$t$ and receiving $x$ intersects the preceding section with
$\{X_t=x\}$. A finite return imposes no new source condition;
indefinite internal waiting gives the same nonreturn on the entire
section. Induction proves the claim, including adaptive requests and
contradictory repeated replies. Completed-product versions agree with
representatives on source sections for almost every seed, up to source
null sets, by Tonelli; thus they give the same integrated masses.
This is the elementary finite-section
interface in Original, Theorems 9.2–10.1. $\square$

For any source event $C$ write

$$
M(C)=\max_{h\in\mathcal A}J_p(C,H_j=h).
\tag{3.2}
$$

This is a maximum of four joint masses. It bounds the correctness of
every label, including minority and wrong-phase choices. On a leaf
compatible with two phases the maximum is over their disjoint label
sets, rather than a sum of their separate maxima.

**lemma 3.2 (Finite averaging over actual initialized rows).** For a
fixed installed table, let
$w_r=\nu(c_{\rm init}^{-1}\{r\})$, and let $q(r),C(r)$ be its source
masses of return and correct return within two calls when started
deterministically at $r$. Then

$$
q_2=\sum_{r\in K}w_rq(r),\qquad
q_2-L_2=\sum_{r\in K}w_rC(r),\qquad
\sum_{r\in K}w_r=1.
\tag{3.3}
$$

If $q_2=1$, then $q(r)=1$ for every $w_r>0$. Any uniform bound
on these deterministic-start correct masses bounds the original
table under its given seed law.

Proof. After initialization the seed has no role. Independence gives
the product mass on each of the finitely many initialization cells,
proving (3.3). The equality $q_2=1$ forces
$\sum_rw_r(1-q(r))=0$; every summand is nonnegative. This proves the
claim and the averaging assertion. No regular conditional law on
$\mathsf U$, atomlessness, new gate, or additional random coin is
needed. Zero-weight cells contribute zero regardless of their
behavior. $\square$

**lemma 3.3 (Positive short executions of an actual table).** Consider
a deterministic start with $q(r)=1$. If the initial row $R$ reads
at $t$, both first replies have positive masses $1-\eta,\eta$.
Every positive section immediately after two calls must have a halt
as its current row. Neither first successor can equal $R$.

Proof. Each integer $t$ is active in exactly one phase, with
conditional probability $2ab$ of reply one; this gives the two stated
masses. A read after two calls incurs a third call before any return
on the entire section. If that section has positive mass, it
contradicts $q(r)=1$. If $\delta(R,x)=R$, then on first reply $x$
the controller rereads the same static coordinate, gets the same
reply, and repeats this transition forever. That first-reply section
is positive and cannot return. Thus this equality is impossible.
Other cycles and all instructions confined to source-null sections
remain allowed. These statements concern the actual table and do
not replace it by a tree. $\square$

## 4. The finite products for arbitrary integer addresses

An address $2\ell+\alpha$ is active in phase $\alpha$ and reads
the spin-line edge $e=\{\ell,\ell+1\}$ there. In the other phase it
is a separator. Two distinct active edges either share one vertex
or have disjoint vertex sets. Together with repetition, this is the
complete incidence list, for arbitrary signs, distances and order
of acquisition.

**lemma 4.1 (One edge and complementary triples).** Conditional on a
specified phase, the two target-spin masses for one active edge are
as follows. The first entry denotes the majority spin when entries
differ.

| Target position | XOR zero | XOR one |
| --- | --- | --- |
| In the edge | $(a^2,b^2)$ | $(\eta,\eta)$ |
| Outside the edge | $(ac,bc)$ | $(2a\eta,2b\eta)$ |

The sum of maximal target-spin masses after one active XOR with
phase known is $a$. For distinct adjacent edges, each label pair
$01,10,11$ has conditional probability $\eta$ and maximal
target-spin mass $a\eta$, for every target position. The pair $00$
has its two constant-triple assignments of masses $a^3,b^3$.
Every phase-specific full-law mass includes a factor $1/2$.

Proof. Zero XOR permits two constant pairs, of masses $a^2,b^2$;
one XOR permits two opposite pairs, each of mass $ab$. For an
exterior target, multiply by its independent spin probability.
The two sums are $a^2+\eta=a$ and $ac+2a\eta=a$.

Two adjacent labels determine a triple up to simultaneous spin
complementation. Unless both labels are zero, the two assignments
are mixed, with masses $a^2b=a\eta$ and $ab^2=b\eta$.
Their total probability is $\eta$. A target in that triple takes
opposite spins on the two assignments, so its maximum is $a\eta$.
An exterior target has independent majority factor $a$, giving
$a\eta$ as well. Both-zero labels force a constant triple. The
argument covers both orientations of adjacent edges. Disjoint
edges use independent spin sets in this same realization. $\square$

These are the products already used in Original, Lemma 3.1, and
Endpoint, Lemmas 3.1–3.2. In particular every nonempty finite
consistent spin assignment has positive probability for the stipulated
$p$. Impossible parity or repeated-label constraints have mass zero.

## 5. Bounds on actual first-reply subtrees

Fix a deterministic execution that returns within two calls almost
surely and starts by reading $t=2\ell+\alpha$. Write
$\beta=1-\alpha$, $e=\{\ell,\ell+1\}$ and $v=v_\alpha$.
Let $D_x$ be its actual correct mass on first reply $x$, including
an early return or all subsequent terminal leaves. At a fixed seed,
any second address on that branch is fixed. Lemma 3.1 allows us to
bound each terminal output by (3.2); there is no assumption that the
leaf maxima are simultaneously attainable with a given row budget.
When the branch makes a second call at $t_x$, write
$C_{xy}=\{X_t=x,X_{t_x}=y\}$ for its acquired-cylinder section.

**lemma 5.1 (Every first-one branch).** For every second instruction,
including an early halt,

$$
D_1\le a\eta.
\tag{5.1}
$$

Proof. First reply one certifies phase $\alpha$. An early halt, a
separator second call, or repetition adds no information. The best
correct mass is $\eta/2$ if $v\in e$, and $a\eta$ otherwise.
For a distinct adjacent second edge both leaves are mixed triples;
each has maximum $a\eta/2$ by Lemma 4.1.

For a vertex-disjoint second edge $f$, if $v\in e$, the first-one
condition leaves equal target masses and independence makes the sum
over second replies
$\tfrac12\eta(c+2\eta)=\eta/2$.
If $v\in f$, the independent first-one factor $2\eta$ multiplied
by the one-edge total $a$ gives $a\eta$ after the phase factor.
If $v$ is in neither edge, its independent majority probability
multiplies the first-one mass to give $a\eta$. These are all
incidences. Thus the full list is

| Second call in phase $\alpha$ | Target position | Sum of leaf maxima |
| --- | --- | --- |
| Separator or repeat | In $e$ | $\eta/2$ |
| Separator or repeat | Outside $e$ | $a\eta$ |
| Distinct adjacent edge | Anywhere | $a\eta$ |
| Disjoint edge $f$ | In $e$ | $\eta/2$ |
| Disjoint edge $f$ | In $f$ or outside both | $a\eta$ |

Since $a>1/2$, every entry gives (5.1). Null leaves contribute zero.
$\square$

**lemma 5.2 (Every first-zero branch).** An early halt gives
$D_0\le a/2$. A same-parity second call satisfies

$$
D_0\le
\begin{cases}
a/2+a^2\eta,&v\in e,\\
a/2+ac\eta,&v\notin e.
\end{cases}
\tag{5.2}
$$

An opposite-parity second call satisfies

$$
D_0\le a^2/2+a\eta.
\tag{5.3}
$$

Proof. With no second call the phase-$\beta$ majority state has
mass $a/2$ on the first-zero section, while no state exceeds its
prior $a/2$.

If the second address has parity $\alpha$, both calls are separators
in phase $\beta$. Consequently the $00$ leaf has maximum exactly
$a/2$. On the $01$ leaf only phase $\alpha$ remains, with edge
constraints $e=0,f=1$. The exhaustive maxima are

| Relation of $f$ to $e$ | Target position | $M(C_{01})$ |
| --- | --- | --- |
| Repeat | Anywhere | $0$ |
| Distinct adjacent edges | Anywhere | $a\eta/2$ |
| Disjoint edges | In $e$ | $a^2\eta$ |
| Disjoint edges | In $f$ | $c\eta/2$ |
| Disjoint edges | Outside both | $ac\eta$ |

For the disjoint entries, the respective products are
$\tfrac12a^2(2\eta)$, $\tfrac12c\eta$, and
$\tfrac12ac(2\eta)$. The adjacent entry is Lemma 4.1.
If $v\in e$, all applicable entries are at most $a^2\eta$,
using $a/2<a^2$. If $v\notin e$, they are at most $ac\eta$:
$c>1/2$ controls adjacency, and $a>1/2$ controls the target-in-$f$
entry. Adding the $00$ maximum proves (5.2).

If instead the second address has parity $\beta$, the $00$ leaf
imposes only $e=0$ in phase $\alpha$ and only the second active
edge $f=0$ in phase $\beta$. For either phase's own target vertex,
Lemma 4.1 gives largest full-law state mass $a^2/2$ when incident
and $ac/2<a^2/2$ when exterior. Taking the maximum over the two
disjoint phase-label sets gives $M(C_{00})\le a^2/2$.
The $01$ leaf certifies phase $\beta$, where the first call was
a separator; its largest mass is $\eta/2$ or $a\eta$, according
to incidence with that phase's actual target $v_\beta$. This proves
(5.3). The two phase targets were never identified with each other.
$\square$

**proposition 5.3 (Inherited unrestricted bounds, with the full
almost-sure competitor domain).** Every protocol of Definition 2.1
with $q_2=1$ has correct mass at most

$$
S_2=\frac a2+a\eta+a^2\eta.
\tag{5.4}
$$

Every such protocol returning within one call almost surely has
correct mass at most

$$
S_1=\frac a2+a\eta.
\tag{5.5}
$$

Proof. First work at a seed for which return within two calls has
source mass one. An initial return has correctness at most $a/2$.
Initial indefinite internal continuation is excluded by that mass-one
property. Otherwise the first event is a call, and both first-reply
sections are positive. On each positive
section the rule must either return after finite waiting or make
its next call, and every positive two-call section must return after
finite waiting. Any indefinite continuation or third call there
would exclude that section from $E_2$. Thus Lemmas 5.1–5.2 apply
directly, including early returns and arbitrary second addresses.
Their largest zero-branch bound is $a/2+a^2\eta$, since $c<a$ and

$$
\left(\frac a2+a^2\eta\right)
-\left(\frac{a^2}{2}+a\eta\right)
=\frac{\eta c}{2}>0.
\tag{5.6}
$$

Adding (5.1) gives (5.4). For a one-call rule, the zero maximum
is $a/2$, and the one maximum is at most $a\eta$, proving (5.5).
This reasoning bounds finite reply trees solely for their masses;
it asserts no installed-state preservation.

For the arbitrary independent seed space, Tonelli applied to
$\mathbf1_{E_2^c}$ gives a full-measure set of seeds with the source
property just used. Lemma 3.1 justifies their acquired-cylinder
sections and fixed terminal outputs. Apply the uniform bound at
each such seed and integrate the measurable original correctness
event. There is no need for a measurable choice of maximizing leaf
labels, a regular conditional distribution on the seed space, or
any assumption about its atoms. Source-null branches and the
exceptional null set of seeds contribute zero. Completed versions
give the same statement by choosing measurable representatives and
applying Tonelli to their product-null differences. The identical
argument applies to $E_1$. $\square$

The values (5.4) and (5.5) are the inherited results of Endpoint,
Theorem 6.1, and Original, Theorem 11.4 / Risk, Theorem 4.1.
Their explicit attaining tables appear in §9. The proof above
supplies the mass estimates needed below without replacing the
original almost-sure comparison by pathwise stopping.

## 6. The quantitative bound for two installed read rows

**theorem 6.1 (At most two read instructions).** Any table of
Definition 2.2 with $|K_{\rm R}|\le2$ and $q_2=1$ has correct mass
at most

$$
T=\frac a2+a\eta(1+c),
\tag{6.1}
$$

with no restriction on the number or choice of its halt rows.

Proof. By Lemma 3.2 it suffices to examine any actual deterministic
start with $q(r)=1$, retaining the whole installed table for counting.
An initial halt gives at most $a/2$. Otherwise let the root row $R$
carry $\operatorname{Read}(t)$, with $\alpha,\beta,e,v$ as in §5.
By Lemma 3.3 neither first successor equals $R$.

If both first successors halt, correctness is at most $S_1$.
If both read, the two-read-row hypothesis forces both to be the
same other installed row $S$. Every source sample then reaches $S$.
For each of the two replies to its fixed address, its positive
marginal section must lead to a halt: it is a union of the
corresponding two-call sections, and any positive one requires a
halt by Lemma 3.3. Thus the output depends only on the reply at
$S$'s address. The first history has been forgotten when both
branches enter the same row; neither it nor the last reply is
available beside that row. This actual output function has the
same correctness as a one-call rule at $S$'s address, hence at most
$S_1$. This includes distinct read rows with identical addresses.
It is an identity of output functions, not an assertion that the
original first call was free.

Exactly one first branch remains to read in all other cases.
If zero halts and one reads, Lemmas 5.1–5.2 give at most $S_1$.
If zero reads and one halts, the early-one correct mass is
$\eta/2$ for $v\in e$, or $a\eta$ for $v\notin e$.
For a same-parity second call, (5.2) therefore gives respectively

$$
A_*:=\frac a2+\eta\left(a^2+\frac12\right)
\quad\hbox{or}\quad T.
\tag{6.2}
$$

For an opposite-parity second call, (5.3) and the uniform early-one
bound give

$$
B_*:=\frac{a^2}{2}+2a\eta.
\tag{6.3}
$$

These cases include every successor type, repeated address, parity,
edge incidence and target placement. They used individual-state
maxima, so minority and wrong-phase outputs are included.
The comparisons on the entire parameter range are

$$
\begin{aligned}
T-S_1&=ac\eta>0,\\
T-A_*&=\eta\left(a-\frac12\right)c>0,\\
T-B_*&=\eta\left(\frac12-2a\eta\right)>0.
\end{aligned}
\tag{6.4}
$$

For the middle identity use $c=2a^2-2a+1$; for the last use
$c=1-2\eta$ and $a-a^2=\eta$. Its strict sign follows from
$\eta<1/4$ and $a<1$. Thus all cases are bounded by $T$.
Averaging the actual starts with Lemma 3.2 proves the theorem.
Unused read rows are included in its hypothesis, and null-path
instructions never supplied an additional positive leaf. $\square$

## 7. The restriction imposed by outputs in one phase

**lemma 7.1 (One-phase output bound).** If all installed halt labels
belong to one of the two target phases, every deterministic start
with $q(r)=1$ has correct mass at most

$$
\frac U2<T,\qquad
U=a^2+2a\eta=a+\eta(a-b).
\tag{7.1}
$$

Proof. Let $\gamma$ be that phase. Correctness is zero in the other
phase. Because its prior is positive, $q(r)=1$ still implies return
within two calls almost surely conditional on $\gamma$. To bound
this execution we allow every terminal leaf its best spin label,
and allow the two second addresses to differ. This enlarges a
numerical upper bound; it does not construct a new state-preserving
or phase-observing controller.

An initial halt gives conditional spin correctness at most $a$.
A first separator gives no information and leaves at most one
active-edge observation, whose total spin correctness is at most
$a$ by Lemma 4.1. Now suppose the first call reads active edge $e$.

If its target lies in $e$, the first-zero subtree has conditional
correct mass at most $a^2$. A separator or repeat leaves this mass
unchanged. A disjoint second edge partitions the independent
target masses $a^2,b^2$, so the sum is still $a^2$. An adjacent
second edge gives maxima $a^3$ on $00$ and $a^2b$ on $01$, summing
to $a^2$. On first one a separator, repeat or disjoint second edge
leaves total maximum $\eta$, whereas an adjacent edge gives two
mixed-leaf maxima $a\eta$, totaling $2a\eta$.

If the target is outside $e$, the first-zero subtree gives $ac$
for a separator or repeat. A disjoint second edge also gives $ac$:
if it contains the target, multiply the first-zero probability $c$
by the one-XOR total $a$; otherwise the target is independent of
both constraints. For an adjacent second edge, a target at its
new vertex lies in the triple; its leaf maxima are $a^3$ and
$a^2b$, totaling $a^2$. If the target is exterior to the triple,
its independent factor gives total $ac$. Hence every first-zero
case is at most $a^2$, using $c<a$.

For this exterior first target, first reply one gives $2a\eta$
for a separator or repeat. A disjoint second edge gives the same
total: either its one-XOR spin total is $a$ independently of the
first-one event of probability $2\eta$, or the target remains
independent of both. An adjacent second edge gives $a\eta$ on
each mixed leaf, whether or not the target lies in the triple.
Thus every first-one case is at most $2a\eta$.

Early halts obey the respective first-zero and first-one bounds
in all these cases. We have exhausted both first parities, all
second-address incidences, and every target position. The total
conditional spin correctness is at most $U=a^2+2a\eta$.
The initial-halt and first-separator cases also satisfy this bound
because $U-a=\eta(a-b)>0$. Multiplication by the original phase
prior $1/2$ gives (7.1), and

$$
T-\frac U2=\eta\left(\frac12+ac\right)>0.
\tag{7.2}
$$

The bound includes any fixed subset of the two phase-$\gamma$
labels. Null sections do not affect these conditional masses.
$\square$

## 8. A bound on every five-row table

**theorem 8.1 (Universal five-installed-row bound).** Every table of
Definition 2.2 with $|K|\le5$ and $q_2=1$ has correct mass at most
$T$ in (6.1).

Proof. Apply Lemma 3.2 and fix an eligible deterministic initial row.
If there are at most two installed read rows, Theorem 6.1 applies.
Otherwise at least three rows read, leaving at most two halt rows.
No halt row makes $q(r)=1$ impossible. If there is only one
distinct halt label, every successful return has that fixed label,
so its correct mass is at most its prior $a/2$. Duplicate halt rows
do not change this conclusion. If the two distinct labels belong
to the same phase, Lemma 7.1 gives a strict bound below $T$.

It remains to treat two labels in opposite phases. An initial halt
again gives at most $a/2$. For a reading start $R$ of parity
$\alpha$, call the two existing halt rows $Z_\alpha,Z_\beta$,
with $\lambda(Z_\gamma)=\operatorname{Halt}(d_\gamma)$ for
$\gamma\in\{\alpha,\beta\}$, where $d_\gamma$ is a label in phase
$\gamma$. Their spin values can be arbitrary. First reply one
certifies phase $\alpha$. Every original success on that section
must therefore have $H_j=d_\alpha$. Sending the first-one
transition directly to $Z_\alpha$ realizes the whole event
$\{X_t=1,H_j=d_\alpha\}$, and cannot decrease correctness.
This assertion does not assume that the label is the majority spin.

For precision, construct the following fresh comparison table for
this deterministic start. Retain the root $R$, both halt rows, and
its original zero successor $S$ if that successor reads. If the zero
successor halts there is no $S$. Lemma 3.3 gives $S\ne R$ when it
exists. Keep the retained address literals and halt labels. Set
$\delta(R,1)=Z_\alpha$ and keep $\delta(R,0)$ as originally
specified. For $S$, keep its transition on each positive zero-branch
second-call section; its destination is already one of the two halt
rows by Lemma 3.3. On each null such section set the destination
to either retained halt row. This specifies both transitions of
every retained read row. Initialize constantly at $R$.

There are at most two read and two halt rows in this complete
comparison table. It returns within two calls, preserves correctness
on the zero section, and weakly improves it on the one section.
No output latch, hidden branch index, seed access, extra phase
observation or address operation has been added. The original
table's rows are all still counted in the original cost; the
comparison is a separate legal table with its own explicit cost
at most four. Theorem 6.1 bounds its correctness by $T$, and hence
also bounds that of the original deterministic start.

These alternatives exhaust every Read/Halt split with at most
five installed rows, including unused rows and arbitrary label
choices. History merging was retained in the argument, positive
cycles were excluded only where $q(r)=1$ forces their exclusion,
and null destinations were changed only in the explicitly
constructed comparison. Average over the original initialization
cells to conclude the theorem. $\square$

## 9. Complete tables and simultaneous actual-source masses

Each construction below is an alternative complete controller.
Only its displayed rows are installed; every read transition is
specified. A dash denotes the absence of a transition at a halt.
Initialization is constant at the named initial row, and every
instruction may have duration one. The seed law is left unchanged
and is never accessed subsequently. Phase notation in the proofs
describes source events and gives no runtime memory port.

**proposition 9.1 (One-row and three-row attainers).** One installed
row attains correct mass $a/2$, and three installed rows attain
$S_1$ under $q_2=1$.

Proof. For the first value initialize at the sole row

| Row | Instruction | Reply zero | Reply one |
| --- | --- | --- | --- |
| $Z$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

It makes zero calls and has the prior correctness $a/2$.

For $S_1$, initialize at $R$ and install

| Row | Instruction | Reply zero | Reply one |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $Z$ | $P$ |
| $Z$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

In phase zero the read is $S_{j+2}\oplus S_{j+3}$, independent
of the actual target $S_j$. In phase one it is a separator and the
target is $S_0$. The full-source terminal masses are

| Record | Output | Source mass | Correct mass |
| --- | --- | --- | --- |
| $0$ | $h_1(\sigma)$ | $(1+c)/2$ | $a/2$ |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ |

On zero, success is exactly the phase-one majority-target event.
On one, the actual phase-zero target is independent of the
certifying edge, giving $\tfrac12(2\eta)a=a\eta$.
Every input returns after one charged call. This is the inherited
one-read attainer of Original and Endpoint, with all halt rows
included in the installed cost. $\square$

**proposition 9.2 (The simultaneous four-row plateau attainer).** Four
installed rows attain $T=a/2+a\eta(1+c)$ with $q_2=1$.

Proof. Initialize at $R$ and install precisely

| Row | Instruction | Reply zero | Reply one |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $R_0$ | $P$ |
| $R_0$ | $\operatorname{Read}(2(j+4))$ | $Z$ | $P$ |
| $Z$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

In phase zero the two possible calls use the disjoint spin pairs
$\{j+2,j+3\}$ and $\{j+4,j+5\}$, both disjoint from the actual
target $S_j$. In phase one both addresses are separators. The
terminal sections, all from this one table on this one source, are

| Record | Output | Source mass | Correct mass |
| --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $ac\eta$ |
| $00$ | $h_1(\sigma)$ | $(1+c^2)/2$ | $a/2$ |

Indeed the first line has phase-zero mass $\tfrac12(2\eta)$,
and multiplying by the independent target-majority factor gives
its correct mass. The second line has phase-zero mass
$\tfrac12c(2\eta)$, again with independent target factor $a$.
The last line contains all of phase one, and the phase-zero event
of two disjoint zero edges, giving $(1+c^2)/2$. Its output is
correct exactly in phase one with $S_0=\sigma$, of mass $a/2$;
phase-zero realizations on the same leaf are errors.

The source masses sum to one:
$\eta+c\eta+(1+c^2)/2=1$ by $2\eta=1-c$.
The correct masses sum to $T$. Every formal binary input path
halts after one or two paid calls. Both read instructions and
both fixed output distinctions are included in the four rows.
Thus the bound is attained simultaneously, rather than by adding
best masses from incompatible hypothetical policies. The same
four-row table is legal at budget five because the constraint is
$|K|\le m$. $\square$

**proposition 9.3 (Inherited six-row unrestricted attainer).** Six
installed rows attain $S_2$ with exactly two paid calls on every
input.

Proof. Initialize at $R$ and use Endpoint, (8.10), namely

| Row | Instruction | Reply zero | Reply one |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2j)$ | $R_0$ | $R_1$ |
| $R_0$ | $\operatorname{Read}(2(j+2))$ | $Z$ | $P$ |
| $R_1$ | $\operatorname{Read}(2(j+1))$ | $Q$ | $P$ |
| $Z$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

In phase zero the first edge is $\{j,j+1\}$ and the target is
$S_j$. After zero, the second edge $\{j+2,j+3\}$ is disjoint
from it. After one, the second edge $\{j+1,j+2\}$ is adjacent.
In phase one all actual calls in the table are separators, and
the target is $S_0$. The terminal masses are

| Record | Output | Source mass | Correct mass |
| --- | --- | --- | --- |
| $00$ | $h_1(\sigma)$ | $(1+c^2)/2$ | $a/2$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $a^2\eta$ |
| $10$ | $h_0(1-\sigma)$ | $\eta/2$ | $a\eta/2$ |
| $11$ | $h_0(\sigma)$ | $\eta/2$ | $a\eta/2$ |

For $00$, all phase-one samples give the two zero replies, and
success is their target-majority event. Its additional phase-zero
mass is $c^2/2$ and is incorrect for that phase-one output.
For $01$, correct phase-zero samples have
$S_j=S_{j+1}=\sigma$ and $S_{j+2}\ne S_{j+3}$, giving the
joint mass $\tfrac12a^2(2\eta)=a^2\eta$.
On $10$ the larger complementary completion of the actual triple
$(S_j,S_{j+1},S_{j+2})$ is
$(1-\sigma,\sigma,\sigma)$; on $11$ it is
$(\sigma,1-\sigma,\sigma)$. Each has conditional mass $a^2b$,
with complement mass $ab^2$, so each correct full-law mass is
$a\eta/2$. The corresponding whole mixed leaf has mass
$(a^2b+ab^2)/2=\eta/2$.

All source masses are positive and sum to one. The correct masses
sum to $a/2+a^2\eta+a\eta=S_2$. The target identification remains
valid for $j=1$, where the phase-zero label is $b_{S_1}$; no target
has moved. Every transition and output is in the displayed six
rows, and every binary input path halts after exactly two calls.
$\square$

The constructions work for both bias directions and either fixed
endpoint, for every given independent seed space. They require
neither an event of prescribed seed mass nor a source-dependent
initialization. At any larger allowed installed budget the same
table remains admissible; no uncounted rows are needed.

## 10. The exact frontier and its positive sixth-row gain

**theorem 10.1 (All positive integer installed budgets).** Under
Definitions 1.1–2.3, for each fixed allowed $p,j,\nu$, all extrema
are attained and

| Installed budget | $C_m$ | $R_m$ | $R_m-R_6$ |
| --- | --- | --- | --- |
| $m=1,2$ | $a/2$ | $1-a/2$ | $a\eta(1+a)$ |
| $m=3$ | $S_1=a/2+a\eta$ | $1-a/2-a\eta$ | $a^2\eta$ |
| $m=4,5$ | $T=a/2+a\eta(1+c)$ | $1-a/2-a\eta(1+c)$ | $\eta^2(a-b)$ |
| $m\ge6$ | $S_2=a/2+a\eta+a^2\eta$ | $1-a/2-a\eta-a^2\eta$ | $0$ |

Proof. With at most two installed rows, a table containing a read
has at most one halt row, hence one fixed returned label and correct
mass at most $a/2$. If it has no reads, every initialized row halts
with a fixed label of prior at most $a/2$; Lemma 3.2 gives the same
bound. The one-row construction in Proposition 9.1 attains it.

With at most three rows, two or more read rows leave at most one
halt label, again bounding correctness by $a/2$. With at most one
read row, a deterministic reading start cannot return to that row
on either positive first-reply section, by Lemma 3.3. Both successors
therefore halt, and the one-read bound gives at most $S_1$.
Initial halts and their finite initialization averages also obey
this bound. Proposition 9.1 attains $S_1$ with three rows.

For four or five rows, Theorem 8.1 gives the bound $T$ for every
installed table, and Proposition 9.2 attains it with four rows.
For all $m\ge6$, Proposition 5.3 bounds every table by $S_2$
even in the larger unrestricted protocol class, while
Proposition 9.3 attains it with six rows. Thus all suprema are
maxima and, because $q_2=1$, the risk infima are the complementary
attained minima.

Subtracting the correct masses from $S_2$ gives the last column.
In particular

$$
\begin{aligned}
S_1-a/2&=a\eta>0,\\
T-S_1&=ac\eta>0,\\
C_5-C_4&=0,\\
S_2-T&=a\eta(a-c)
=a\eta b(a-b)=\eta^2(a-b)>0.
\end{aligned}
\tag{10.1}
$$

Also $S_2-S_1=a^2\eta$ and $S_2-a/2=a\eta(1+a)$.
All factors giving the strict signs are positive throughout the
specified biased interior range. There is no interior threshold
or omitted equality case. The positive penalty comes from a
universal quantitative bound matched by a complete attainer;
nonattainment at five rows alone would not have proved it.
$\square$

## 11. Inherited rigidity, mathematical ownership and source boundaries

**proposition 11.1 (The inherited equality geometries and costs).** In
the literal complete-controller model, the minimum installed costs
for attaining the unrestricted $S_1$ under $q_1=1$, and $S_2$ under
$q_2=1$, are respectively three and six. For every positive
initialization cell, their equality geometries and labels are
exactly the following.

For $S_1$, the first active edge in its parity must be exterior
to that phase's actual target. Both successors halt, with
$h_\beta(\sigma)$ on zero and $h_\alpha(\sigma)$ on one.

For $S_2$, the root edge $e$ contains $v_\alpha$. The zero-branch
second call has parity $\alpha$ and an edge $f$ vertex-disjoint
from $e$. The one-branch second call has parity $\alpha$ and an
edge $g$ sharing one vertex with $e$. The unique maximizing labels
are

$$
\begin{array}{c|c}
00&h_\beta(\sigma)\\
01&h_\alpha(\sigma)\\
10&h_\alpha(s_0)\\
11&h_\alpha(s_1)
\end{array}
\qquad
(s_0,s_1)=
\begin{cases}
(\sigma,1-\sigma),&v_\alpha\in e\cap g,\\
(1-\sigma,\sigma),&v_\alpha\in e\setminus g.
\end{cases}
\tag{11.1}
$$

These are inherited from Endpoint, Propositions 8.3–8.4 and
Theorem 8.5.

Proof. For a deterministic $q_1=1$ start, an initial halt is below
$S_1$. Both first replies have positive mass, so both successors
must halt. The zero leaf has unique maximizing label
$h_\beta(\sigma)$: its mass $a/2$ exceeds the other same-phase
spin mass $b/2$ and the phase-$\alpha$ masses bounded by
$a^2/2$ or $ac/2$. The one leaf has maximum $\eta/2$ for an
incident target, strictly below $a\eta$. For an exterior target
the unique maximum is $a\eta$ with label $h_\alpha(\sigma)$.
This proves the one-read characterization, forcing one read row
and two distinct halt labels.

For $S_2$, the zero branch cannot halt, since then total correctness
is at most $S_1<S_2$. Equality in Proposition 5.3 forces equality
in both branch bounds and every positive leaf maximum. Opposite
parity on the zero branch loses the positive quantity in (5.6).
For the same parity, the $01$ maxima in Lemma 5.2 are strictly
below $a^2\eta$ except for a disjoint second edge with target in
$e$: a repeat contributes zero, adjacency contributes
$a\eta/2<a^2\eta$, a target in the disjoint new edge gives
$c\eta/2<a^2\eta$, and a target outside both gives
$ac\eta<a^2\eta$. Thus the first edge is incident to the target
and the zero second edge is disjoint at the same parity.

With that incident first edge, an early first-one halt, separator,
repeat, or disjoint second edge gives only $\eta/2<a\eta$.
Lemma 5.1 forces an adjacent active second edge. The four leaf
source masses are then, in order $00,01,10,11$,

$$
\frac{1+c^2}{2},\qquad c\eta,\qquad
\frac\eta2,\qquad\frac\eta2,
\tag{11.2}
$$

all positive. On $00$ the phase-$\beta$ majority mass $a/2$
strictly exceeds $b/2$ and the phase-$\alpha$ maximum
$a^2c/2$. On $01$ the two phase-$\alpha$ target masses are
$a^2\eta,b^2\eta$. These give the first two unique labels
in (11.1). On $10$, the two spins of the zero second edge are
majority in the larger mixed triple, and the remaining vertex
is minority. On $11$, the shared vertex is minority and the two
outer vertices are majority. The target belongs to $e$, so these
give exactly the two label alternatives in (11.1), uniquely
because $a^2b>ab^2$. Conversely these geometries and labels give
correct masses $a/2,a^2\eta,a\eta/2,a\eta/2$ and attain $S_2$.

The three required edge addresses are distinct, so they require
three distinct fixed Read rows. The outputs include
$h_\beta(\sigma),h_\alpha(\sigma),h_\alpha(1-\sigma)$,
requiring three distinct Halt rows, separate from the Read rows.
All are reached on positive sections. At an attaining randomized
initialization, (3.3) and the uniform unrestricted bound force
every positive cell to attain the same bound, so the necessity
persists under any seed law. For $q_1$ the identical averaging
argument uses its one-read coordinates. Propositions 9.1 and 9.3
give the matching installed costs. This recovers the inherited
three/six-row minima with their original hypotheses. $\square$

**Attribution 11.2 (Exact source-relative increment).** The preceding
theory sources have the following ownership.

| Source | Inherited content used here |
| --- | --- |
| Original, *FIB harmonic-edge load: fixed-state tail nonuniformity and an erasure-risk jump*, Proposition 2.1 and (2.2) | The stationary four-state source on the original integer clock. |
| Original, Definition 9.1, (9.4), Theorems 9.2–10.1 | The arbitrary-address paid acquisition contract, actual endpoint indices, finite sections and complementary-product mechanism. |
| Original, Theorem 11.4; Risk, *FIB paid reads: return mass and hidden-endpoint classification risk*, Theorem 4.1 | The unrestricted one-read optimum $S_1$ and its deterministic actual-source attainer. Risk additionally owns its selective one-read curve and equality gate. |
| Endpoint, *FIB two paid reads: exact almost-sure-return endpoint risk*, §§3–6, especially Theorem 6.1 and Definition 5.1 / Proposition 5.2 | The unrestricted $q_2=1$ value $S_2$, its full-address subtree bounds and simultaneous two-call actual-source policy. |
| Endpoint, Definition 8.1, Lemma 8.2, Propositions 8.3–8.4 and Theorem 8.5 | The literal complete-controller convention, initialization averaging, equality rigidity, and minimum costs three/six for attaining the inherited optima. |

Original is
[FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md](FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md).
Risk is
[FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md](FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md).
Endpoint is identified above by its full title and numbered sections.
Endpoint's own attribution retains the fuller two-read geometry in
its named FixedSeed source; no additional result from that nested
source is required here.

The installed-state frontier derivations supplied for this volume
provide the two-read-row argument, the output-label dichotomy,
the explicitly costed opposite-phase dominance, and the four-row
attainer. This exposition supplies their ordinary proofs in §§6–10.
Relative to Original, Risk and Endpoint, the substantive addition
is the quantitative bound $T$ for every five-row table, its
simultaneous attainment, and the resulting exact positive risk
penalty. Their ownership is not transferred to an approval or
checking verdict. The products, source sections, one-read value,
two-read value and qualitative attainment minima remain inherited.
No exhaustive literature-absence or global-originality assertion
is made.

## 12. Scope of the mathematical conclusion

Theorem 10.1 evaluates all positive integer installed budgets only
for the fixed original biased interior parameter, the actual fixed
$H_j$, the literal interface in Definition 2.2, and $q_2=1$.
Its lower bounds include almost-sure stopping with exceptional
null paths; its attainers additionally halt on every binary input.
The distinction is preserved throughout the proof. Source-null
records have zero contribution, not an extra source observation
or an uncharged instruction.

The exact frontier at $q_2<1$ is not determined here. Seed-event
availability and selective returns can matter there. Quantitative
frontiers for larger read budgets, joint expected-read constraints,
and other runtime memory ports also remain outside this result.
In particular the proof does not transfer to an interface with
an external program counter, saved reply, output latch, clock,
computed addresses or later seed access. The fair parameter
$p=1/2$ and endpoints $p=0,1$ are excluded; strictness is asserted
only for each fixed parameter in the stated range, without a
uniform positive gap at its degenerate limits.

Installed rows are an abstract resource defined by the complete
instruction convention. Their number supplies no physical-bit,
write, energy, code-size, timing or learning guarantee. Every
actual call remains charged even if it is repeated or returns a
separator zero. Hidden-state classification here supplies no
visible-bit Brier theorem. Original, Open Problem 6.4, concerning
arbitrary-finite attainment/separation for the whole harmonic/Brier
domain, remains unresolved by this volume. No completion of that
problem or any research-wide goal follows.

The evidence is the ordinary proofs in this source. No mathematical
execution, numerical enumeration, experiment, new test, Lean
compilation or kernel certification is asserted.

## 追加锚（本行以下为增补区）
