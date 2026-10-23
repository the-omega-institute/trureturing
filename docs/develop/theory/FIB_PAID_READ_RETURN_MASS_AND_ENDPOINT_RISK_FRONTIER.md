# FIB paid reads: return mass and hidden-endpoint classification risk

## 1. One original law and its paid acquisition contract

**Assumption 1.1 (Original stationary XOR law and fixed endpoint).** Fix
$0<p<1$, $p\ne1/2$, and a single endpoint index $j\in\{0,1\}$. The hidden
state alphabet is $\mathcal A=\{a_0,a_1,b_0,b_1\}$. Let $\varphi$ be uniform
on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$. On the original integer clock set

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell:=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this one joint hidden-visible law. This is exactly the
realization in [Original, Proposition 2.1 and (2.2)][Original], with the
four stationary state masses $(1-p,p,1-p,p)/2$. An active transition goes
from $a_s$ to $b_t$ with probability $\pi_t$, where $\pi_0=1-p$ and
$\pi_1=p$, and emits $s\oplus t$; the following transition goes from
$b_t$ to $a_t$ and emits zero. Thus the phase mixture uses the original
stationary emitted-bit clock, including its separator positions. In
particular $X_tX_{t+1}=0$ at every integer $t$. No rescaled or replacement
source is used.

The target is the actual $H_j$ in this same realization. The endpoint
identification is exactly [Original, (9.4)][Original]:

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{1.2}
$$

For a fixed endpoint, each phase corresponds to two states distinguished
by the displayed spin. Knowing a representation of $J_p$ does not grant
access to that spin or to $\varphi$. In particular the complete-half-line
measurability in [Original, Lemma 8.1][Original] grants no free acquisition
operation in the following definition.

**Definition 1.2 (Admissible protocol, unchanged from Original Definition
9.1).** Choose an arbitrary probability space
$(\mathsf U,\mathcal U,\nu)$ independent of the entire $J_p$ source, and
keep its law $\nu$ unchanged. Constant public data may be included in
$\mathsf U$; all random public data and all internal randomness are part
of this same source-independent auxiliary variable $u$. A finite acquired
record is an ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.3}
$$

A protocol is a measurable next-event rule based only on the fixed public
data, $u$, and this acquired record. Its next event is either a read at an
integer address $t_{n+1}$, a return of a state $A\in\mathcal A$, or
indefinite internal continuation with no further read and no return.
Finite events may follow internal waiting. Their occurrence, kind,
address or output, and their finite waiting time are measurable functions
only of those same available data. Thus adaptive addresses are allowed,
but no extra information can enter through a waiting time.

The reply to a requested address is precisely the actual $X_{t_{n+1}}$
of the same stationary source. Every actual call costs one read. This
includes repeated addresses, separator zeros, negative and positive
addresses, disconnected sets, and arbitrarily distant addresses. Ignoring
a call in a later likelihood calculation does not refund its cost.

Let $\tau$ be the return time and let
$N\in\mathbb N_0\cup\{\infty\}$ count all actual reads. These are separate
random variables. Every nonreturn has $\tau=\infty$. Internal continuation
forever after finitely many reads is allowed, including $N=0$; infinite
read paths are allowed as well. A return has finite $N$, and its output
and return time depend measurably only on the public data, $u$, and the
terminal acquired record, denoted $\mathsf R$.

No hidden-state read, half-line read, tail read, source-dependent seed or
timing, reset, law switch, moving endpoint, or erased-coordinate
substitution is permitted. A protocol may return without reading and may
choose a state from the wrong phase. Null records and versions completed
by null sets are included using the usual measurable completion. These
are exactly the operations and allowances of [Original, Definition
9.1][Original], rather than a restriction to consecutive, connected, or
always-returning protocols. Put

$$
\mathbb P_p=J_p\otimes\nu.
\tag{1.4}
$$

In particular all public and auxiliary randomness is independent of both
the original endpoint and every visible coordinate.

**Definition 1.3 (Return mass, classification risk, and parameters).** Write

$$
\begin{gathered}
T=\{\tau<\infty\},\qquad E_k=\{\tau<\infty,\ N\le k\},\\
q_k=\mathbb P_p(E_k),\qquad
L_k=\mathbb P_p(A\ne H_j,\ E_k),\qquad k\in\mathbb N_0,\\
a=\max(p,1-p),\qquad b=\min(p,1-p),\qquad R=a/b,\\
\eta=ab,\qquad c=a^2+b^2=1-2ab,\qquad
e_0=1-a/2,\qquad e_k=\frac{1}{1+R^k}\quad(k\ge1).
\end{gathered}
\tag{1.5}
$$

Here $0<b<1/2<a<1$, $R>1$, and $1/2<c<1$. Set
$x_+=\max(x,0)$. The quantity $L_k$ is joint classification error on the
budgeted return event, not total return mass and not conditional error.
For $q_k>0$, conditional error on $E_k$ is $L_k/q_k$; it is not defined
here when $q_k=0$. The total finite-return probability is
$\mathbb P_p(T)$ and need not equal $q_k$: paths outside $E_k$ may return
after more calls. They may also continue internally forever after any
finite read count or make infinitely many reads.

The loss is the indicator of an incorrect four-state endpoint, rather
than the squared loss for an erased visible bit or a posterior variance.
In particular the Brier quantities in [Original, Lemma 3.1 and
§§3--5][Original] are distinct from $L_k$.

## 2. The existing finite-record interface

**Definition 2.1 (Terminal masses and the reused count-only estimate).**
For a fixed seed $u$, a finite ordered record $r$ of length $n$ either
agrees with the protocol's successive choices and finite return, or it
does not. In the former case its terminal source section is exactly

$$
C(r)=\{X_{t_i}=x_i:1\le i\le n\};
\tag{2.1}
$$

in the latter case the terminal section is empty. The output on a
consistent section is fixed by $u$ and $r$. This is the finite-section
reduction in [Original, Theorems 9.2--10.1][Original]. Internal waits add
no source condition: the same seed and acquired replies give the same
finite events and delays, or the same internal nonreturn. The assertion
therefore includes adaptive addresses.

For a consistent section and its chosen output $h$, use the notation

$$
w_h=J_p(C(r),H_j=h),\qquad W=J_p(C(r)),\qquad L=W-w_h.
\tag{2.2}
$$

These are source-section masses, with no regular conditional probability
on $\mathsf U$ assumed. In a specified phase, distinct active addresses
give edges $\{\ell,\ell+1\}$ of the integer spin line. Repetitions repeat
an edge; separators impose their required zero reply. A component with
specified XOR labels has two complementary spin assignments if it is
consistent. For the component containing the endpoint spin, with $v$
vertices, the two same-phase endpoint masses have a common factor from
the phase and every other component, times complementary products of
$v$ Bernoulli factors. Their ratio in either direction is at most $R^v$.
This is the product comparison of [Original, Lemma 3.1, (9.5), and the
proof of Theorem 10.1][Original]. Components outside the endpoint
component remain in the common factor; they are not discarded from the
source law.

We use, without introducing a new count-only theorem, the sharper
conclusion of [Original, Theorem 10.1][Original]: for every output on a
terminal section of length $n$,

$$
L\ge e_nW.
\tag{2.3}
$$

This includes $n=0$, where the largest state prior is $a/2$. The sequence
$(e_n)_{n\ge0}$ is nonincreasing and $e_1=b$. Summing the supplied
recordwise bound gives $L_0\ge e_0q_0$ and $L_k\ge e_kq_k$ for $k\ge1$,
as well as its random-count version. There are only countably many
finite integer-address/reply records. Their source sections can be
summed at a fixed seed and then integrated against the unchanged $\nu$.
Measurable representatives outside completed-product null sets suffice;
completion does not change any integrated mass below.

For each integer $n\ge1$, the existing sharpness witness in [Original,
Theorem 10.1, (10.4)][Original] makes $n-1$ local even-address reads
$2(j+i)$, $0\le i\le n-2$, and the
distant even-address read $2(j+n)$, paying for all $n$ calls. It returns
the majority-spin phase-zero state only when every local reply is zero
and the distant reply is one, and otherwise continues internally forever
without more reads. Its already established masses are

$$
\mathbb P_p(T)=ab(a^n+b^n),\qquad
\mathbb P_p(A\ne H_j,T)=ab\,b^n,\qquad
\mathbb P_p(A\ne H_j\mid T)=e_n.
\tag{2.4}
$$

For $n=1$ the local list is empty, and the distant spin pair is disjoint
from the unobserved target spin. For $n=0$, immediate return of a largest
prior state has error $e_0$. Neither these coefficients nor this selective
witness are new claims of this volume. [Original, Theorem 9.2][Original]
also retains its weaker coefficient $1/(1+R^{k+1})$ and its consequence
that positive-probability finite return always has positive joint error.
Selective sharpness does not itself determine risk at prescribed return
mass or at almost-sure return.

## 3. A return-mass correction for every finite budget

**Theorem 3.1 (Forced zero-return sections).** Under Assumption 1.1 and
Definition 1.2, let $k\ge1$ be an integer and put

$$
\begin{aligned}
z_k&=\frac{c^{\lfloor k/2\rfloor}+c^{\lceil k/2\rceil}}{2},\\
d_k&=\frac{(1-e_k)c^k}{2},\\
F_k(q)&=e_kq+\frac{d_k}{z_k}(q+z_k-1)_+,
\qquad 0\le q\le1.
\end{aligned}
\tag{3.1}
$$

Every admissible protocol, for every arbitrary unchanged independent
auxiliary law, satisfies

$$
L_k\ge F_k(q_k).
\tag{3.2}
$$

The improvement over $e_kq_k$ is strict when $q_k>1-z_k$. No condition is
imposed on paths outside $E_k$; no almost-sure return or moment assumption
is required. For $q_k>0$, the conditional error on $E_k$ is at least
$F_k(q_k)/q_k$; no such conditional quantity is asserted at $q_k=0$.
If every returning path uses at most $k$ reads, $q_k$ equals
the total return probability. If $\mathbb P_p(T)=1$ and $N\le k$ almost
surely, the unconditional classification error is at least $e_k+d_k$.
These general-budget constants are not asserted optimal.

Proof. First consider any finite list of at most $k$ actual addresses and
its all-zero reply cylinder $C$. In phase $\phi$, let $m_\phi$ be the
number of distinct active edges in this list. The active-edge graph is a
disjoint union of finite paths. A component with $\ell\ge1$ edges has
$\ell+1$ spins; its all-zero XOR constraint says precisely that those
spins are constant. Its conditional mass is therefore
$a^{\ell+1}+b^{\ell+1}$. Convexity of $t\mapsto t^\ell$, with weights
$a,b$ summing to one, gives

$$
a^{\ell+1}+b^{\ell+1}
=a\,a^\ell+b\,b^\ell
\ge(a\,a+b\,b)^\ell=c^\ell.
\tag{3.3}
$$

The different components use disjoint iid spins, so their masses
multiply. Separator reads impose no further constraint, and repeated
zero labels impose no new edge constraint. Thus

$$
J_p(C,\varphi=\phi)\ge\frac{c^{m_\phi}}2.
\tag{3.4}
$$

With no active edge, the conditional mass is one and the same formula
holds. Each distinct integer address is active in exactly one of the two
phases; hence $m_0+m_1\le k$, with repetitions still counted as actual
paid calls in the budget.

For $0<c<1$, the minimum of $c^x+c^y$ over nonnegative integers with
$x+y\le k$ uses sum $k$ and balanced exponents. Increasing an exponent
decreases its power. If $x\ge y+2$, the change upon replacing $(x,y)$ by
$(x-1,y+1)$ is

$$
(1-c)(c^{x-1}-c^y)\le0.
\tag{3.5}
$$

Repeated balancing proves the assertion. Consequently

$$
J_p(C)\ge z_k,
\qquad J_p(C,\varphi=\phi)\ge c^k/2\quad(\phi=0,1).
\tag{3.6}
$$

Every endpoint state has positive mass on $C$: in either phase the
finite path constraints admit a constant assignment of either spin value
on the endpoint component, and $a,b$ are positive. These arguments apply
equally to negative, distant, and disconnected addresses and to the
empty list.

Next fix a seed whose hypothetical all-zero decision path returns after
$n\le k$ reads, and let $C$ be its zero terminal cylinder. If its output
is $h$, let $\bar h$ be the complementary-spin state of the same endpoint
phase, and write

$$
w=J_p(C,H_j=h),\qquad \bar w=J_p(C,H_j=\bar h),\qquad
O=J_p(C,\text{opposite phase}),
\qquad W=w+\bar w+O,\quad L=\bar w+O.
\tag{3.7}
$$

Here the phase associated with $h$ is determined by the fixed $j$ and
(1.2), even when that output is a wrong-phase state on some actual
sources. Let $v$ be the number of vertices in its endpoint component,
adjoining the endpoint as a singleton if needed. The comparison in
Definition 2.1 gives $w\le R^v\bar w$.

If $v\le k$, use (3.6) for the entire opposite-phase mass to obtain

$$
\begin{aligned}
L-e_kW
&=\frac{R^kL-w}{1+R^k}\\
&\ge\frac{R^kO}{1+R^k}
=(1-e_k)O\ge d_k.
\end{aligned}
\tag{3.8}
$$

If $v=k+1$, the endpoint component already needs $k$ distinct edges.
Since $n\le k$, necessarily $n=k$ and every call is a distinct active
edge in that component. There are no other components with edges, no
separator calls, and no repeats in this case. All its replies are zero,
so the component is constant. In the opposite phase all these calls are
separators, giving $O=1/2$. The two same-phase state masses are
$a^{k+1}/2$ and $b^{k+1}/2$. For their fixed total, $L-e_kW$ is minimized
by choosing the state of larger mass. At that choice,

$$
L-e_kW
=\frac{1-e_k}{2}\bigl[1-(a-b)b^k\bigr].
\tag{3.9}
$$

For $k\ge1$, $b^k\le b$ and
$1-(a-b)b=c+b\ge c\ge c^k$. Thus (3.9) is at least $d_k$ as well;
choosing the smaller state only increases the error. The earlier case
$v=1\le k$ also includes return with no reads. We have proved the
absolute excess bound $L-e_kW\ge d_k$ for every such zero terminal
section and every output.

It remains to show how many seeds must have such a section. Let $B$ be
the set of seeds for which the hypothetical all-zero path returns
within $k$ reads. This is measurable: it is a countable union over finite
ordered integer-address zero records of the measurable conditions that
the rule follows that record and then returns in finite time. Following
zero replies is an analysis of the existing rule, not a new observation
available to a protocol.

For a seed outside $B$, follow zero replies until the rule either
continues internally forever or will make call $k+1$. The already
acquired zero prefix has at most $k$ calls. On its cylinder, $E_k$ is
impossible. Internal nonreturn before the first read uses the empty
cylinder; internal nonreturn after any finite prefix is included. A path
that takes this $(k+1)$st call cannot return in at most $k$ calls, regardless
of its later behavior. By (3.6) this excluded cylinder has mass at least
$z_k$. The $E_k$ source-section mass is therefore at most $1-z_k$ off
$B$ and at most one on $B$. Integration gives

$$
q_k\le1-z_k+z_k\nu(B),
\qquad
\nu(B)\ge\frac{(q_k+z_k-1)_+}{z_k}.
\tag{3.10}
$$

At each seed, every other terminal section with at most $k$ reads obeys
the reused inequality $L\ge e_nW\ge e_kW$, including $n=0$. Terminal
sections are disjoint at a fixed seed. For a seed in $B$, its particular
zero terminal section has the additional excess at least $d_k$ from
(3.8)--(3.9). Sum these nonnegative excesses over the countable finite
terminal records, and integrate the source sections against $\nu$.
Tonelli's theorem, or finite sums followed by monotone convergence,
yields

$$
L_k-e_kq_k\ge d_k\nu(B)
\ge\frac{d_k}{z_k}(q_k+z_k-1)_+.
\tag{3.11}
$$

No disintegration of the auxiliary space was used. Null sections and
measurable completions do not alter these integrated identities.
All-zero records, both phase alternatives, wrong outputs, repetitions,
all finite address configurations, and internal or infinite-read
nonreturn remain in the competitor class. Since $d_k,z_k>0$, the strict
improvement and the assertions at total or almost-sure return follow.
$\square$

The reused ingredients in this theorem are the original law and endpoint
identification, the finite-section reduction of [Original, Theorems
9.2--10.1][Original], the component products of its Lemma 3.1, and its
count-only estimate. The additional quantitative bridge is the zero
cylinder mass $z_k$, its absolute excess $d_k$, and the forced seed mass
in (3.10). Convexity and finite-product likelihood comparison retain
their usual elementary meaning; the displayed return-mass statement is
repo-derived, without a literature-priority assertion.

## 4. The exact universal one-read envelope and its equality gate

**Theorem 4.1 (One-read risk and exact seed-event availability).** Retain
the full protocol class and write $q=q_1$, $L=L_1$. Put

$$
z=1-\eta,\qquad
\rho=1-\frac{a}{2z},\qquad
f(q)=bq+\frac{ac}{2z}(q-\eta)_+.
\tag{4.1}
$$

Every admissible protocol under every unchanged independent auxiliary
law satisfies

$$
L\ge f(q)
=\begin{cases}
bq,&0\le q\le\eta,\\
b\eta+\rho(q-\eta),&\eta\le q\le1.
\end{cases}
\tag{4.2}
$$

The slope difference is $\rho-b=ac/(2z)>0$, so this is strictly stronger
than the one-read count-only bound when $q>\eta$.

For a specified unchanged auxiliary space, there exists an admissible
protocol with $\mathbb P_p(E_1)=q$ and $L_1=f(q)$ if and only if that
space has a measurable event $G$ of measure

$$
\nu(G)=
\begin{cases}
q/\eta,&0\le q\le\eta,\\
(q-\eta)/(1-\eta),&\eta<q\le1.
\end{cases}
\tag{4.3}
$$

At $q=\eta$ the lower formula asks for an event of measure one, while the
upper construction may equivalently use an empty event. In particular
$q=0,\eta,1$ are equality points under every auxiliary law, without
using its randomness. Across auxiliary spaces the entire curve is
attained; an atomless uniform auxiliary variable supplies every gate in
(4.3). For a fixed atomic law, neither attainability of every $q$ nor
equality at every attainable $q$ is asserted.

Among all almost-surely returning protocols with $N\le1$ almost surely,
the exact minimum unconditional classification error, for either
original endpoint and every auxiliary law, is

$$
f(1)=1-a/2-a^2b.
\tag{4.4}
$$

A deterministic protocol using exactly one paid read attains it.

Proof. In Theorem 3.1, $z_1=(1+c)/2=z$, $e_1=b$, and $d_1=ac/2$.
Consequently its lower bound is (4.2). To obtain necessity of the gate,
we also give the branchwise lower argument.

For any one original address $t$, exactly one phase is active there, so
the one reply has mass $\eta=(1/2)2ab$. In that phase its active edge
either is disjoint from the endpoint spin or touches it. In the disjoint
case the target keeps its original Bernoulli law independently of the
edge, and the largest joint mass of a state and that reply is $a\eta$.
In the touching case the two assignments on an XOR-one edge each have
conditional spin mass $ab$. Their joint masses including the phase are
$ab/2=\eta/2\le a\eta$. The other phase cannot produce the one reply.
Thus every output has joint error at least $b\eta$ on the one branch.
The distinction between touching and disjoint edges covers every
integer address, including negative and arbitrarily distant ones.

The zero reply has mass $z$. Its joint mass with any particular endpoint
state is bounded by that state's prior, hence by $a/2$. Every output
therefore has joint error at least $z-a/2=\rho z$ on the zero branch.
This bound is attained by the majority-spin state of the phase in which
the address is a separator. A zero-read return has error at least
$e_0=1-a/2$.

At a fixed seed, before reading, the first finite event is either a
return or a read at an address determined by that seed; internal
nonreturn is the remaining possibility. After a first read, whether a
reply branch lies in $E_1$ depends only on the seed and that reply.
Making a second read excludes the branch from $E_1$, as does internal
nonreturn, without any restriction on later returns. Define measurable
seed events $G_1,G_0,G_I$ by, respectively, first making a read and
returning within one call on its one branch, doing so on its zero
branch, and returning before reading. The events $G_1,G_0$ may overlap,
but each is disjoint from $G_I$. Measurability follows from the next-event
rule, or from the countable union over possible first integer addresses
and terminal records. Write

$$
\alpha=\nu(G_1),\qquad \lambda=\nu(G_0),\qquad
\gamma=\nu(G_I).
\tag{4.5}
$$

Every original address has the same one/zero reply masses $\eta,z$.
Independence of the source and seed, and the branch estimates just
proved, give

$$
\begin{aligned}
q&=\eta\alpha+z\lambda+\gamma,\\
L&\ge b\eta\alpha+\rho z\lambda+e_0\gamma.
\end{aligned}
\tag{4.6}
$$

Let $d=ac/2=(\rho-b)z$. Subtract $bq$ and use $e_0-b=a/2$:

$$
L-bq\ge d\lambda+\frac a2\gamma.
\tag{4.7}
$$

Also $\alpha\le1-\gamma$, because $G_1$ and $G_I$ are disjoint. Thus

$$
q\le\eta+z(\lambda+\gamma).
\tag{4.8}
$$

Since $0<c<1$, we have $0<d<a/2$. If $q\ge\eta$, (4.7)--(4.8) yield

$$
L-bq\ge d\lambda+\frac a2\gamma
\ge d(\lambda+\gamma)
\ge\frac d z(q-\eta).
\tag{4.9}
$$

If $q\le\eta$, the nonnegative right side of (4.7) gives $L\ge bq$.
This proves the lower envelope directly and retains zero-read returns,
finite-read internal nonreturn, and all later-return paths.

For attainability, let $\sigma=1$ if $p>1/2$ and $\sigma=0$ otherwise.
Use the one predetermined original even address

$$
t=2(j+1).
\tag{4.10}
$$

In phase zero it gives $S_{j+1}\oplus S_{j+2}$, whose spin pair is
disjoint from the target $S_j$. In phase one it is a separator. On a one
reply return $a_\sigma$ for $j=0$, or $b_\sigma$ for $j=1$. This is the
majority-spin phase-zero state; the branch has mass $\eta$ and
conditional error $b$. On a zero reply return $b_\sigma$ for $j=0$, or
$a_\sigma$ for $j=1$, if that branch is to return. This is the
majority-spin phase-one state. Its correct joint mass on the zero branch
is $a/2$, since that reply is automatic in phase one. The branch has
mass $z$ and conditional error $\rho$.

For $0\le q\le\eta$, make this paid read on every path. Return only on
the one reply with $u\in G$, where the already existing event $G$ has
measure $q/\eta$. On every other record continue internally forever
without more reads. The return mass is $q$, and its joint error is
$bq$. For $\eta<q\le1$, always return on the one reply, and return on
the zero reply exactly when $u\in G$, where
$\nu(G)=(q-\eta)/z$. Continue internally forever on the remaining zero
records. These choices give

$$
\mathbb P_p(T)=\eta+z\nu(G)=q,
\qquad
\mathbb P_p(A\ne H_j,T)=b\eta+\rho z\nu(G)=f(q).
\tag{4.11}
$$

Each construction keeps $\nu$ unchanged and has $N=1$ on every path;
nonreturn is internal. At $q=0$ never return, at $q=\eta$ return only on
one, and at $q=1$ return on both replies. These three choices ignore the
seed. The point $q=\eta$ is the existing $n=1$ selective point in (2.4).
The additional zero-branch rule supplies the continuation to larger
return mass. Always returning gives

$$
b\eta+\rho z=b\eta+z-a/2
=1-a/2-a\eta=1-a/2-a^2b.
\tag{4.12}
$$

For an almost-sure return with $N\le1$, $E_1$ has probability one, so
the universal lower bound and this deterministic protocol prove (4.4).

Finally suppose an arbitrary admissible protocol attains $L=f(q)$.
If $q\le\eta$, (4.7) forces $\lambda=\gamma=0$, since both coefficients
are positive. Equation (4.6) then implies
$\alpha=q/\eta$; the measurable seed event $G_1$ supplies the required
gate. This includes $q=\eta$ and $q=0$. If $q>\eta$, equality in (4.9)
forces $\gamma=0$ because $a/2>d$, and forces
$\lambda=(q-\eta)/z$. The event $G_0$ is then the required gate
(and (4.6) also gives $\alpha=1$). These are events of the original
auxiliary space, not added randomness. Necessity together with the
explicit gated constructions proves (4.3) in both directions.
$\square$

For $q>0$, the same theorem gives conditional error at least $f(q)/q$.
There is no conditional-risk assertion at $q=0$. Equality on the lower
curve and the optimum above that curve are distinct questions for a
specified atomic $\nu$; the absence of a gate does not determine the
latter. The one-read mass constraint, equality condition, and
almost-sure-return optimum are repo-derived relative to the source's
count-only theorem, using elementary likelihood comparison and convex
branch accounting, without an external priority claim.

## 5. A finite paid-probe and local-block family

**Theorem 5.1 (Exact return, risk, and paid-cost formulas).** Under the
same law and acquisition contract, fix integers $s\ge1$ and $m\ge0$.
Set $M=m+1$ and

$$
\beta=2\sqrt{ab},\qquad
r_M=\frac12\sum_{r=0}^M\binom Mr
\min\bigl(a^{M-r}b^r,\ a^rb^{M-r}\bigr).
\tag{5.1}
$$

For either fixed original endpoint and every unchanged auxiliary law,
there is a deterministic admissible protocol, ignoring that auxiliary
variable, with

$$
\begin{aligned}
\mathbb P_p(T)&=1,\\
\mathbb P_p(A\ne H_j)
&=c^se_0+(1-c^s)r_{m+1},\\
N&\le2s+m,\\
\mathbb E_pN&=2s+m(1-c^s).
\end{aligned}
\tag{5.2}
$$

If $m>0$, its exact read-count distribution is

$$
\mathbb P_p(N=2s)=c^s,
\qquad
\mathbb P_p(N=2s+m)=1-c^s.
\tag{5.3}
$$

The maximum actual read count is exactly $2s+m$. For $m=0$, $N=2s$ on
every path and $r_1=b$. Moreover

$$
r_M\le\frac{\beta^M}{2},\qquad
\mathbb P_p(A\ne H_j)
\le c^se_0+(1-c^s)\frac{\beta^{m+1}}2.
\tag{5.4}
$$

For each fixed biased interior parameter and each $\varepsilon>0$, a
choice of finite $s,m$ makes the error smaller than $\varepsilon$ with a
deterministic finite maximum actual read cost. This is an attained upper
family, without an optimality assertion or a zero-error finite-return
claim.

Proof. Put $D=m+3$. First make all $2s$ actual reads, in the indicated
pair order,

$$
4(D+r),\quad 4(D+r)+1,
\qquad 0\le r<s.
\tag{5.5}
$$

All these calls are made and paid before any output or local-block
branch, even when an early reply is one. In phase zero the even member
of each pair is active; in phase one the odd member is active. In
either case its active reply is

$$
Y_{2(D+r)}=S_{2(D+r)}\oplus S_{2(D+r)+1},
\tag{5.6}
$$

and the other reply is a separator zero. The spin pairs in (5.6) are
mutually disjoint. Their XORs are independent and each is zero with
probability $c=a^2+b^2$. Let $Z$ be the event that every probe reply is
zero. Then

$$
\mathbb P_p(Z)=c^s.
\tag{5.7}
$$

The event $Z$ is the same event of these distant spin pairs in either
phase. It is therefore independent of the uniform phase. The smallest
probe spin index is $2m+6$, whereas every local block used below has
largest index at most $m+1$. Thus all probe spins are also disjoint from
every such local block. Independence here concerns spin supports in the
same $J_p$ realization, not an independently spliced source.

On $Z$, return a fixed majority-spin state in one fixed phase; for
example use $a_\sigma$ for $j=0$ and $b_\sigma$ for $j=1$, with
$\sigma$ as in Theorem 4.1. Conditional on $Z$, the phase remains
uniform and the endpoint spin keeps its original Bernoulli law.
The correct conditional probability is $a/2$, hence the conditional
classification error is $e_0$. Exactly $2s$ reads have been made.

On $Z^c$, at least one paid reply is one. Its original address parity
identifies the actual phase $\phi$. Only after completing all probes,
make the following $m$ actual local reads:

$$
\begin{array}{c|c|c|c}
\text{certified phase}&\text{addresses},\ 0\le i<m
&\text{active XORs}&\text{spin block}\\ \hline
0&2(j+i)&Y_j,\ldots,Y_{j+m-1}&S_j,\ldots,S_{j+m}\\
1&1+2i&Y_0,\ldots,Y_{m-1}&S_0,\ldots,S_m
\end{array}
\tag{5.8}
$$

Every local reply is read and paid for. The first spin in each row is
exactly the original endpoint spin in (1.2), for both $j=0$ and $j=1$.
For $m=0$, both local lists are empty and the phase-certified endpoint
spin is still unobserved. There is no endpoint reset or movement.

The local $m$-XOR word determines its $M=m+1$ spins up to simultaneous
complementation. For each of its two completions compute its Bernoulli
product mass, choose a larger-mass completion, and return its first spin
in the certified original phase, using (1.2). A fixed deterministic
choice resolves every likelihood tie. This is the maximum a posteriori
choice of endpoint spin for that word: the two completions have opposite
first spins.

For an unordered complementary pair with product masses $u,v$, the
weighted error is $\min(u,v)$, including a tie. Sum over unordered pairs.
Equivalently sum over all spin words and divide by two, because
complementation has no fixed word for $M\ge1$. If a word has $r$ minority
spins, its mass is $a^{M-r}b^r$ and its complement has mass
$a^rb^{M-r}$. Grouping by $r$ gives exactly $r_M$ in (5.1). This is a
classification-error identity. The related complementary-pair mechanism
in [Original, Lemma 3.1][Original] instead weights a pair by
$uv/(u+v)$ for posterior variance; that Brier expression is not being
substituted here.

For every pair $uv=(ab)^M$. The elementary estimate
$\min(u,v)\le\sqrt{uv}$ and the binomial identity
$\sum_{r=0}^M\binom Mr=2^M$ imply

$$
r_M\le 2^{M-1}(ab)^{M/2}=\frac{\beta^M}{2}.
\tag{5.9}
$$

When $m=0$, (5.1) reads $r_1=b$, as required for an unobserved
Bernoulli spin after phase certification. All possible local likelihood
ties are covered by the fixed tie rule and leave the minimum-mass
formula unchanged.

Given either phase, the local spin block is independent of the probe
spins and of $Z^c$. Hence the local error on probe success is exactly
$r_{m+1}$ in each phase. Combining success with (5.7) and the error on
$Z$ proves the exact risk in (5.2). On $Z$ the count is $2s$; on $Z^c$
it is $2s+m$. If $m>0$ these are distinct and give (5.3). If $m=0$ they
coincide, so the count is always $2s$. In both cases the expectation is
$2s+m(1-c^s)$. Since $0<c^s<1$, the success branch has positive mass,
so the maximum count is exactly $2s+m$, also when $m=0$.
The entire construction consists of fixed finite lists
and a finite decision on their replies, with finite internal waits
chosen, so it returns almost surely. Impossible records can receive
any fixed output to make the rule total and measurable.

For the stated parameter range, $0<c<1$ and $0<\beta<1$. Choose $s$
large enough that $c^se_0<\varepsilon/2$, and then $m$ large enough
that $\beta^{m+1}/2<\varepsilon/2$. Equation (5.4) gives error below
$\varepsilon$ and maximum paid count $2s+m$. At every finite $s$, the
error remains positive because $c^se_0>0$.

The parameter restriction is material: at $p=1/2$ the geometric factor
$\beta$ is one, while at $p=0,1$ the positive-mass hypotheses fail,
$c=1$, and $R$ is not defined. Neither these boundary parameters nor a
uniform cost bound as they are approached are part of the theorem.
$\square$

The complement-pair likelihood, maximum a posteriori rule, and geometric
mean estimate are reused elementary mechanisms. The repo-derived
content is the finite paid phase probing on the original separator
clock, the local addresses for the unchanged endpoint in both phases,
and the simultaneous exact return, classification-risk, maximum-cost,
read-distribution, and expected-cost formulas. Complete-half-line phase
or spin identification is not a free step in this construction.

## 6. Frontier questions and resource boundaries

**Definition 6.1 (Attainable regions and unresolved optima).** For the
fixed $p,j$ and unchanged auxiliary law $\nu$, the budget-$k$ attainable
region consists of all pairs $(q_k,L_k)$ from Definition 1.2. Its lower
risk at a specified attainable mass $q$ is

$$
\mathcal L_{k,\nu}(q)
=\inf\{L_k:\text{an admissible protocol has }q_k=q\}.
\tag{6.1}
$$

Theorem 3.1 supplies a universal lower bound. For $k=1$, Theorem 4.1
gives a sharp universal envelope and characterizes exactly when a
protocol reaches that envelope under the given seed law. It does not
settle the attainable region or the value of (6.1) above $f$ at attainable
masses whose equality gate is absent in a specified atomic space. For
$k\ge2$, the optimal return-mass frontier and sharpness of $F_k$ remain
unsettled. Theorem 5.1 supplies an explicit upper family; it does not
determine minimum expected paid cost, optimal adaptive stopping, or the
complete larger-budget attainable region.

The budget in these statements is the number of actual visible reads.
Return time, internal computation, address size, persistent state, and
physical storage are different resources and receive no complexity or
bounded-memory conclusion here. In particular small error with a finite
paid budget is not zero error on a positive finite-return event; the
existing positivity result of Original Theorem 9.2 still applies. The
joint, unconditional, and return-conditioned classification risks in
Theorem 5.1 coincide because its return probability is one, not because
classification risk equals Brier risk.

The original arbitrary-finite attainment/separation question in
[Original, Open Problem 6.4][Original] remains unchanged and unsettled.
No conclusion about neural training, generalization, empirical learning,
or the whole-domain attainment problem follows from these acquisition
bounds. The attribution throughout is relative to the exact original
source and its stated finite-product mechanisms, with no claim of
global originality.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md

## 追加锚（本行以下为增补区）
