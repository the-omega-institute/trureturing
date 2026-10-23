# FIB two paid reads: fixed-seed frontiers and a strict support-invisible optimum

For the original biased stationary XOR law, this volume determines every
feasible return mass and the attained minimum endpoint-classification risk
with a budget of two actual reads, for each specified independent auxiliary
probability space. The auxiliary law is kept unchanged. Its positive-measure
atoms may be nonpoints, and their number may be countably infinite.

The classification starts with two explicit tables of deterministic
subtree optima. Their combinations form at most eighty indexed paid
policies. Every original protocol has a measurable selection of these
policies with the same return mass and no greater risk. This is a
classification of feasible masses and the lower risk frontier; it does
not purport to list every attainable pair with higher risk.

At the smallest positive deterministic mass, $q_*=2\eta^2$, the
constant-seed optimum is attained but is strictly worse than a feasible
competitor for every real supporting objective $C-\lambda q$. An
atomless seed attains a strictly smaller risk at that same mass. Thus a
complete universal support curve does not recover a fixed-law frontier.

The law, finite-record interface and count-only and zero-record bounds
belong to [Original][Original] and [Risk][Risk]. The complete universal
two-read support curve and its four-part equality face belong to
[Universal Support][Support]; the $q_2=1$ optimum belongs to [Slice][Slice].
Those results retain their ownership. All arguments needed for the
fixed-law classification and comparisons below are ordinary,
self-contained probability proofs.

## 1. The original law and the full acquisition contract

**Definition 1.1 (One stationary law and one fixed endpoint).** Fix
$0<p<1$, $p\ne1/2$, and $j\in\{0,1\}$. The four states in
$\mathcal A=\{a_0,a_1,b_0,b_1\}$ are distinct. Let $\varphi$ be
uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$. On the original integer clock define

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell:=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this joint hidden-visible law. It is the law of
Original, Proposition 2.1 and (2.2). In the state order
$(a_0,a_1,b_0,b_1)$ the stationary masses are
$(1-p,p,1-p,p)/2$. Indeed an active transition chooses $b_t$ from
$a_s$ with probability $\pi_t$, where $\pi_0=1-p$, $\pi_1=p$,
and emits $s\oplus t$; the following transition copies $b_t$ to
$a_t$ and emits zero. Incoming mass at each $b_t$ is $\pi_t/2$,
and copying gives the same mass at $a_t$. Formula (1.1) uses this
stationary emitted-bit clock, including the separator positions.
In particular $X_tX_{t+1}=0$ for every integer $t$.

The target is the actual $H_j$, with the original endpoint indices

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{1.2}
$$

from Original, (9.4). For this fixed $j$, put

$$
\begin{aligned}
h_0(s)&=\begin{cases}a_s&j=0,\\b_s&j=1,\end{cases}&v_0&=j,\\
h_1(s)&=\begin{cases}b_s&j=0,\\a_s&j=1,\end{cases}&v_1&=0.
\end{aligned}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.3}
$$

The two phase state pairs are disjoint. Correct masses for different
phases cannot be added as though a single output could be correct in
both. The representation grants no observation of $\varphi$ or any
unread spin.

**Definition 1.2 (Unchanged paid arbitrary-address protocol).** Let
$(\mathsf U,\mathcal U,\nu)$ be any probability space independent of
the entire $J_p$ source. Keep this space and its law unchanged. Fixed
public data may be included as constants; all random public data and
all internal randomness are part of the same source-independent
auxiliary variable $u$.

An acquired record is a finite ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,\qquad n\in\mathbb N_0.
\tag{1.4}
$$

A measurable next-event rule, based only on these public data, $u$
and $r$, either requests an integer address, returns a state
$A\in\mathcal A$, or continues internally forever without a further
read or return. Finite events may follow internal waiting. Their
occurrence, kind, address or output, and finite waiting time are
measurable functions of exactly those available data. Waiting adds
no source information.

Each requested address $t$ replies with the actual $X_t$ of (1.1),
and every actual call costs one read. This includes repeated calls,
separator zeros, negative and positive addresses, disconnected sets,
and arbitrarily distant addresses. Ignoring a reply does not refund
its call. The next address may depend on all acquired replies.

Let $\tau$ be return time, with $\tau=\infty$ on every nonreturn,
and let $N\in\mathbb N_0\cup\{\infty\}$ count all actual reads.
Internal nonreturn after finitely many reads, including zero, and
infinite-read paths are both permitted. A return has finite $N$;
its output and time depend measurably only on the available data and
the terminal acquired record. Zero-read returns, one-read early
returns, and wrong-phase outputs are allowed. Null records and
versions completed by null sets are included through the usual
measurable completion.

There is no hidden-state, half-line or tail read, source-dependent
seed or timing, reset, law switch, endpoint movement, or substitution
of an erased coordinate. This is Original, Definition 9.1, and Risk,
Definition 1.2. The contract imposes neither effective computability
nor a storage bound. All constructions below use only this contract.

**Definition 1.3 (Budgeted return and joint error).** Under
$\mathbb P_p=J_p\otimes\nu$, set

$$
\begin{gathered}
T=\{\tau<\infty\},\qquad E_2=\{\tau<\infty,\ N\le2\},\\
q=\mathbb P_p(E_2),\qquad
L=\mathbb P_p(A\ne H_j,E_2),\qquad C=q-L,\\
\mathcal L_{2,\nu}(q)
=\inf\{L:\text{a protocol of Definition 1.2 has return mass }q\}.
\end{gathered}
\tag{1.5}
$$

The infimum of an empty constraint set is $+\infty$. No condition
is imposed on behavior outside $E_2$: such paths may return after
more reads, continue internally forever after any finite count, or
make infinitely many calls. The representatives constructed here
preserve $q$ and weakly reduce $L$; they need not preserve the
pointwise return event, exterior behavior, or other resource costs.
For $q>0$, the conditional error on $E_2$ is $L/q$; no conditional
error is assigned at $q=0$. This four-state classification loss is
different from squared loss for an erased visible bit.

**Convention 1.4 (Bias notation).** Throughout let

$$
\begin{gathered}
a=\max(p,1-p),\qquad b=\min(p,1-p),\qquad
\eta=ab,\qquad c=a^2+b^2=1-2\eta,\\
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2,\end{cases}\qquad
z=1-\eta,\qquad w=1-\frac{3\eta}{2},\qquad
v=\frac{1+c^2}{2}.
\end{gathered}
\tag{1.6}
$$

Thus $\sigma$ is the majority spin, $a+b=1$,
$0<b<1/2<a<1$, $0<\eta<1/4$, and $1/2<c<1$.
Useful strict identities are

$$
a-c=b(a-b)>0,\qquad c-b=a(a-b)>0.
\tag{1.7}
$$

The letter $v$ in (1.6) is a mass; $v_0,v_1$ in (1.3) are spin
indices.

## 2. Finite source sections and exhaustive two-read geometry

**Lemma 2.1 (Source sections and paid padding).** Fix a seed value
$u$. A consistent finite acquired record has source section exactly

$$
C(r)=\{X_{t_i}=x_i:1\le i\le n\}.
\tag{2.1}
$$

An inconsistent record has empty section. On a terminal section its
output is fixed. For the purpose of $(q,L)$, a fixed-seed protocol
that starts with a read can be represented by a depth-two binary tree
with a first address $t$, second addresses $t_0,t_1$, and an
accept/reject decision and an output at each leaf. This representation
preserves its return and error masses before optimizing outputs.

Proof. At a fixed seed and prefix, every next event and finite delay
is determined. A requested address and its reply intersect the old
section with $\{X_t=x\}$. A finite return imposes no extra source
condition; internal divergence is the same behavior on the entire
prefix section. Induction proves (2.1), including adaptive choices.
Contradictory repeated replies give an empty cylinder.

If after a second call the next event is a third read or internal
nonreturn, reject that branch for this calculation. A later return
after a third read is outside $E_2$. If a one-read branch returns,
make an actual paid repeat of that address, ignore its necessarily
repeated reply, and then return the same state. The branch still
returns within two calls with exactly the same source and error
masses. A short rejected branch can likewise be padded by a paid
repeat and internal nonreturn. This yields the asserted tree.

Before any read, internal nonreturn gives $(q,L)=(0,0)$. A zero-read
return gives $q=1$ and correct mass at most $a/2$. These cases will
receive explicit representatives in Theorem 4.3. All later behavior
discarded from the calculation remains allowed in the original
competitor class. The section argument is the interface of Original,
Theorems 9.2–10.1, here proved directly. $\square$

**Definition 2.2 (Leaf masses and first-address types).** For a leaf
source cylinder $D$, write

$$
W(D)=J_p(D),\qquad M(D)=\max_{h\in\mathcal A}J_p(D,H_j=h).
\tag{2.2}
$$

An accepted leaf has correct mass at most $M(D)$, attained by a fixed
maximizing state. A root address $t$ has active phase
$\alpha=t\bmod2\in\{0,1\}$; put $\beta=1-\alpha$.
In phase $\alpha$, its active edge is $e=\{\ell,\ell+1\}$
when $t=2\ell+\alpha$. Call the root type $I$ if
$v_\alpha\in e$ and type $D$ otherwise. The first-one source
mass is $\eta$, and it certifies $\alpha$. The first-zero mass
is $z=(1+c)/2$.

All $W,M$ below include the prior phase factor $1/2$. Where one
phase is certified, an entry is a joint mass in that phase, rather
than a conditional probability on the auxiliary space.

**Lemma 2.3 (The elementary spin products).** Conditional on a fixed
phase, one active edge has the following joint target-spin masses:

| Target position | Edge zero | Edge one |
| --- | --- | --- |
| In the edge | $a^2,b^2$ | $\eta,\eta$ |
| Outside the edge | $ac,bc$ | $2a\eta,2b\eta$ |

For two distinct active edges, the only possibilities are one shared
vertex or disjoint vertex sets. For shared-vertex edges, each
specified one-containing label pair $\xi\in\{01,10,11\}$ has
phase-conditional mass $\eta$ and maximal full-law state mass
$a\eta/2$, for any target position. The union of those three label
events has phase-conditional mass $3\eta$. Their all-zero label pair
has phase-conditional mass $1-3\eta$.
Constraints on vertex-disjoint edges multiply within that same phase.

Proof. A zero edge has equal endpoint spins, with products $a^2,b^2$.
A one edge has the two complementary products $ab,ab$. An exterior
target contributes its independent factor $a$ or $b$, proving the
table.

Two edges of the integer line can only coincide, be adjacent, or
have disjoint vertex sets. For adjacent edges write their union in
left-to-right spin order. The larger-mass completions of the three
one-containing label pairs are

$$
\begin{array}{c|c}
\text{left/right edge labels}&\text{larger-mass spin triple}\\ \hline
01&(\sigma,\sigma,1-\sigma)\\
10&(1-\sigma,\sigma,\sigma)\\
11&(\sigma,1-\sigma,\sigma).
\end{array}
\tag{2.3}
$$

Each has product $a^2b=a\eta$; its complement has product
$ab^2=b\eta$. If the target belongs to the triple, its two
values distinguish these two products. If outside, the triple event
has mass $\eta$, and multiplication by the majority prior gives
$a\eta$. In either case the phase factor gives $a\eta/2$.
The zero pair instead forces three equal spins, of total mass
$a^3+b^3=1-3ab$. Disjoint edges use disjoint iid spins, proving
the product assertion. These incidences exhaust all integer addresses,
including negative and arbitrarily distant ones. Repetition repeats
a constraint but retains its paid call. $\square$

**Lemma 2.4 (All first-one leaves).** Given a first reply one, the
complete leaf table for the second address is as follows. The two
reply symbols refer to the order of calls.

| Second call and target placement | Leaf | $W$ | $M$ |
| --- | --- | --- | --- |
| Repeat or a phase-$\alpha$ separator; type $I$ | Only possible leaf | $\eta$ | $\eta/2$ |
| Repeat or a phase-$\alpha$ separator; type $D$ | Only possible leaf | $\eta$ | $a\eta$ |
| Same-parity adjacent edge; either type | $10$ | $\eta/2$ | $a\eta/2$ |
| Same-parity adjacent edge; either type | $11$ | $\eta/2$ | $a\eta/2$ |
| Disjoint edge; type $I$ | $10$ | $\eta c$ | $\eta c/2$ |
| Disjoint edge; type $I$ | $11$ | $2\eta^2$ | $\eta^2$ |
| Disjoint edge meeting the target; type $D$ | $10$ | $\eta c$ | $a^2\eta$ |
| Disjoint edge meeting the target; type $D$ | $11$ | $2\eta^2$ | $\eta^2$ |
| Disjoint edge avoiding the target; type $D$ | $10$ | $\eta c$ | $a\eta c$ |
| Disjoint edge avoiding the target; type $D$ | $11$ | $2\eta^2$ | $2a\eta^2$ |

Proof. A first one excludes phase $\beta$. Repetition or a separator
does not split its source mass; the one-edge table of Lemma 2.3 gives
the first two rows. Adjacency gives the next two rows by its triple
calculation. For disjoint edges, the first-one probability $2\eta$
multiplies the second-zero probability $c$ or the second-one
probability $2\eta$, followed by the phase factor.

For type $I$, the target is in the first one edge, with equal
target masses, and is independent of the second edge. For type $D$
with target in the second edge, its zero and one target masses are
$a^2$ and $\eta$, multiplied by the independent first-one factor
$2\eta$ and by $1/2$. If the target avoids both, multiply each
leaf probability by $a$. This proves every entry. A second address
of the opposite parity is precisely a separator in the certified
phase, so no address case is missing. $\square$

**Lemma 2.5 (All first-zero leaves).** Given a first reply zero, the
complete leaf table is the following. In the last two rows, $f$
denotes the active edge of the second call in phase $\beta$.

| Second-call geometry | Leaf | $W$ | $M$ |
| --- | --- | --- | --- |
| Same-parity repeat | $00$ | $z$ | $a/2$ |
| Same-parity adjacent | $00$ | $w$ | $a/2$ |
| Same-parity adjacent | $01$ | $\eta/2$ | $a\eta/2$ |
| Same-parity disjoint; either type | $00$ | $v$ | $a/2$ |
| Same-parity disjoint; type $I$ | $01$ | $\eta c$ | $a^2\eta$ |
| Same-parity disjoint; type $D$, second edge meets target | $01$ | $\eta c$ | $\eta c/2$ |
| Same-parity disjoint; type $D$, second edge avoids target | $01$ | $\eta c$ | $a\eta c$ |
| Opposite parity | $00$ | $c$ | $a^2/2$ if $e$ meets $v_\alpha$ or $f$ meets $v_\beta$; otherwise $ac/2$ |
| Opposite parity | $01$ | $\eta$ | $\eta/2$ if $f$ meets $v_\beta$; otherwise $a\eta$ |

Proof. For two same-parity calls, phase $\beta$ sees two separators.
Thus its entire majority-state mass $a/2$ lies on $00$. No particular
state has prior larger than $a/2$, so this is exactly $M(00)$.
The phase-$\alpha$ zero-constraint probabilities for a repeat,
adjacent edges and disjoint edges are $c$, $1-3\eta$ and $c^2$.
Adding the opposite-phase mass and dividing by two gives $z,w,v$.

The adjacent $01$ leaf follows from Lemma 2.3. For disjoint $01$,
the first zero edge contributes $a^2$ if it contains the majority
target, while the second one contributes $2\eta$; the full-law
maximum for type $I$ is therefore $a^2\eta$. If only the second
edge contains the target, multiply its one-state mass $\eta$ by
the first-zero factor $c$ and $1/2$. If neither contains it,
multiply the leaf mass $\eta c$ by the majority prior $a$.

For opposite parities, each phase has exactly one active edge on
$00$. Each contributes total mass $c/2$. Its largest individual
state mass is $a^2/2$ when that phase's active edge touches its
actual target, or $ac/2$ when it does not. Since the phase state
pairs are disjoint, take their maximum, not their sum. Identity
$a>c$ gives the stated alternative. On $01$ only phase $\beta$
remains; its one-edge calculation gives the last row. These are
mutually exclusive phase sections of one source. They are not
independently spliced observations. $\square$

## 3. Two complete fixed-mass subtree tables

**Definition 3.1 (Candidate subtree masses).** Put

$$
\begin{aligned}
\mathcal R&=\{0,2\eta^2,\eta/2,\eta c,\eta\},\\
\mathcal S&=\{0,\eta/2,\eta c,\eta,c,v,w,z\}.
\end{aligned}
\tag{3.1}
$$

For root type $\rho\in\{I,D\}$, let $U_\rho(r)$ be the
largest correct mass available from its first-one subtree when that
subtree returns source mass $r$. Define $V_\rho(s)$ analogously
on first zero. The upper bounds apply to every root of the stated
type. Section 4 realizes all their entries at a common specified
root of that type.

**Theorem 3.2 (Complete first-one table).** The possible first-one
return masses are exactly $\mathcal R$, and their optimal correct
masses are

| $r$ | $U_I(r)$ | $U_D(r)$ |
| --- | --- | --- |
| $0$ | $0$ | $0$ |
| $2\eta^2$ | $\eta^2$ | $2a\eta^2$ |
| $\eta/2$ | $a\eta/2$ | $a\eta/2$ |
| $\eta c$ | $\eta c/2$ | $a^2\eta$ |
| $\eta$ | $a\eta$ | $a\eta$ |

Proof. In Lemma 2.4 each subtree has at most two nonempty leaves.
An accepted subset is empty, a single leaf, or the whole subtree.
Repeats and separators give masses $0,\eta$; adjacency gives
$0,\eta/2,\eta$; disjoint edges give
$0,2\eta^2,\eta c,\eta$. This proves coverage of the mass list.

Mass $2\eta^2$ requires the disjoint $11$ leaf. Its type-$I$
maximum is $\eta^2$. For type $D$, avoiding the target gives
$2a\eta^2>\eta^2$. Mass $\eta/2$ is an adjacent single leaf,
with maximum $a\eta/2$ for both types. Mass $\eta c$ is the
disjoint $10$ leaf; for type $D$, putting the target in the second
zero edge gives $a^2\eta>a\eta c$, since $a>c$.

Mass $\eta$ requires accepting the whole subtree. For type $I$,
adjacency gives $a\eta$, exceeding the $\eta/2$ available from
repetition, separators or disjoint edges. For type $D$, repeats,
separators and adjacency each give $a\eta$. The disjoint sums are
also at most that value: when the second edge contains the target,
$a^2\eta+\eta^2=a\eta$; when it does not,
$a\eta c+2a\eta^2=a\eta$. The zero row is immediate.
Section 4 gives paid realizations of every chosen maximum. $\square$

**Theorem 3.3 (Complete first-zero table).** The possible first-zero
return masses are exactly $\mathcal S$, and their optimal correct
masses are

| $s$ | $V_I(s)$ | $V_D(s)$ |
| --- | --- | --- |
| $0$ | $0$ | $0$ |
| $\eta/2$ | $a\eta/2$ | $a\eta/2$ |
| $\eta c$ | $a^2\eta$ | $a\eta c$ |
| $\eta$ | $a\eta$ | $a\eta$ |
| $c$ | $a^2/2$ | $a^2/2$ |
| $v$ | $a/2$ | $a/2$ |
| $w$ | $a/2$ | $a/2$ |
| $z$ | $a/2+a^2\eta$ | $a/2+a\eta c$ |

Proof. Accepting subsets in the four geometries of Lemma 2.5 gives
respectively

$$
\{0,z\},\quad \{0,\eta/2,w,z\},\quad
\{0,\eta c,v,z\},\quad \{0,\eta,c,z\}.
\tag{3.2}
$$

Their union is $\mathcal S$. The strict ordering

$$
0<2\eta^2<\eta/2<\eta c<\eta<c<v<w<z
\tag{3.3}
$$

shows which single-leaf cases can supply each nonzero proper mass.
Here $v-c=(1-c)^2/2>0$,
$w-v=\eta(1/2-2\eta)>0$, and $z-w=\eta/2>0$;
the earlier inequalities follow from $0<\eta<1/4$ and $c>1/2$.

An adjacent single $01$ gives $a\eta/2$ at $s=\eta/2$.
The disjoint $01$ gives $a^2\eta$ for type $I$ and, for type
$D$, the larger choice $a\eta c>\eta c/2$ when the second edge
avoids the target. An opposite-parity $01$ avoiding the phase-$\beta$
target gives $a\eta$ at $s=\eta$. Its $00$ maximum at $s=c$
is $a^2/2$: type $I$ already touches the phase-$\alpha$ target;
type $D$ can make the second edge touch the phase-$\beta$ target.
The same-parity $00$ leaves give $a/2$ at $v,w$.

For $s=z$, the entire first-zero subtree must be accepted. For type
$I$, the best sums from repeat, adjacency, disjointness and opposite
parity are bounded respectively by

$$
\frac a2,\quad \frac a2+\frac{a\eta}{2},\quad
\frac a2+a^2\eta,\quad \frac{a^2}{2}+a\eta.
\tag{3.4}
$$

The disjoint sum exceeds the adjacent sum by
$a\eta(a-1/2)>0$ and the opposite-parity bound by
$\eta(1/2-\eta)>0$. It also exceeds the repeat sum.
If the opposite-parity second edge touches its target, the sum is
only $a^2/2+\eta/2=a/2$, already covered.

For type $D$, the four geometry maxima are

$$
\frac a2,\quad \frac a2+\frac{a\eta}{2},\quad
\frac a2+a\eta c,\quad \frac a2.
\tag{3.5}
$$

In the disjoint case a target-touching second edge instead gives
$a/2+\eta c/2$, smaller than the avoiding choice. In the
opposite-parity case, touching gives $a^2/2+\eta/2=a/2$,
while avoiding gives $ac/2+a\eta=a/2$. Since $c>1/2$,
the third sum in (3.5) is largest. Section 4 realizes these maxima
and the other rows. $\square$

The two tables retain the small mass $2\eta^2$ even though it
will never optimize a real support objective. No pruning by support
values has been performed.

## 4. Canonical paid policies and deterministic completeness

**Definition 4.1 (Common roots and actual second addresses).** Use
root parity zero. For $\rho=I$ choose $t=2j$; for $\rho=D$
choose $t=2(j+4)$. For either root put

$$
f=2(j+8),\qquad g=t+2,\qquad
o=2(j+8)+1,\qquad i=1.
\tag{4.1}
$$

In phase zero, $f$ is vertex-disjoint from the root edge and avoids
$S_j$; $g$ is its right adjacent edge. In phase one, $o$ avoids
the target $S_0$, while $i$ reads its incident edge
$S_0\oplus S_1$. For a type-$D$ root, address $2j$ reads a
target-touching edge disjoint from the root. These assertions hold
for both $j=0$ and $j=1$ using the actual indices in (1.2).

After a first reply one, use the following second actual call and
acceptance rule. Every accepted leaf outputs $h_0(\sigma)$,
except the specified $10$ leaf.

| Required $r$ | Second address | Accepted second replies | Output exception |
| --- | --- | --- | --- |
| $0$ | $t$ | None | None |
| $2\eta^2$ | $f$ | $1$ | None |
| $\eta/2$ | $g$ | $1$ | None |
| $\eta c$ | $f$ for $I$; $2j$ for $D$ | $0$ | None |
| $\eta$ | $g$ | $0,1$ | For type $I$, $10$ outputs $h_0(1-\sigma)$ |

After a first reply zero, use this second actual call and rule:

| Required $s$ | Second address | Accepted second replies | Accepted output |
| --- | --- | --- | --- |
| $0$ | $t$ | None | None |
| $\eta/2$ | $g$ | $1$ | $h_0(\sigma)$ |
| $\eta c$ | $f$ | $1$ | $h_0(\sigma)$ |
| $\eta$ | $o$ | $1$ | $h_1(\sigma)$ |
| $c$ | $i$ | $0$ | $h_1(\sigma)$ |
| $v$ | $f$ | $0$ | $h_1(\sigma)$ |
| $w$ | $g$ | $0$ | $h_1(\sigma)$ |
| $z$ | $f$ | $0,1$ | $00$: $h_1(\sigma)$; $01$: $h_0(\sigma)$ |

Every rejected leaf continues internally forever after its second
call, with no further reads. Choose finite internal waits for all
calls and accepted returns. Thus every path makes exactly two actual
paid calls, including paths rejected by a repeated call.

**Proposition 4.2 (Simultaneous attainment at the same root).** For
each $\rho\in\{I,D\}$ and every
$(r,s)\in\mathcal R\times\mathcal S$, Definition 4.1 is one
admissible deterministic policy with

$$
q=r+s,\qquad C=U_\rho(r)+V_\rho(s).
\tag{4.2}
$$

Proof. The addresses have the incidences stated after (4.1), so the
leaf masses are those of Lemmas 2.4–2.5. On an isolated one edge
containing the target, the target masses tie, and the fixed output
$h_0(\sigma)$ is maximizing. On a zero edge containing the target,
the majority choice maximizes its state mass. When the target avoids
all queried spin supports in a certified phase, the same output
uses its unchanged majority prior.

For the type-$I$ adjacent edge $g$, the larger triples for $10$,
$11$ and $01$ are respectively
$(1-\sigma,\sigma,\sigma)$, $(\sigma,1-\sigma,\sigma)$ and
$(\sigma,\sigma,1-\sigma)$, as in (2.3).
Their target is the leftmost spin $S_j$. Hence their
maximizing outputs are respectively $h_0(1-\sigma)$,
$h_0(\sigma)$ and $h_0(\sigma)$, exactly as specified. For a
type-$D$ root and $g$, the target is outside the entire triple;
$h_0(\sigma)$ has maximal mass there.

On any same-parity $00$ leaf, $h_1(\sigma)$ has correct mass
$a/2$. On the opposite-parity $00$ leaf using $i$, its phase-one
edge touches $S_0$, so $h_1(\sigma)$ has mass $a^2/2$.
On $01$ using $o$, phase one is certified and its target is
independent of the distant edge, giving correct mass $a\eta$.
These checks give every output and every table maximum in Section 3.

The second-call rules on first zero and first one are choices on
mutually exclusive branches of a single tree, with the same first
address. Therefore any $r$ row and any $s$ row of the same root
type are simultaneously realizable. Their masses add because they
are disjoint source sections. This proves (4.2), without combining
incompatible marginal extrema or adding a random coin. $\square$

**Theorem 4.3 (All deterministic masses and their minimum risks).**
Let the finite index set and its associated pairs be

$$
\begin{gathered}
K=\{I,D\}\times\mathcal R\times\mathcal S,\\
q_k=r+s,\qquad
\ell_k=r+s-U_\rho(r)-V_\rho(s),\qquad k=(\rho,r,s).
\end{gathered}
\tag{4.3}
$$

There are at most $2\cdot5\cdot8=80$ indexed policies. Numerical
duplicates may be retained. The deterministic feasible masses are
exactly

$$
\mathcal Q_{\rm det}=\mathcal R+\mathcal S,
\tag{4.4}
$$

and for each such $q$ the attained minimum risk is

$$
\mathcal L_{\rm det}(q)
=q-\max_{\substack{\rho\in\{I,D\},\ r\in\mathcal R,\ s\in\mathcal S\\r+s=q}}
\bigl[U_\rho(r)+V_\rho(s)\bigr].
\tag{4.5}
$$

Every deterministic original protocol has a $K$ policy of the same
mass and weakly smaller risk. Formula (4.5) maximizes over all
decompositions, including collisions of different $r+s$ as $p$
varies.

Proof. For a protocol starting with a read, Lemma 2.1 reduces the
calculation to a depth-two tree. Its root has one of the two types.
Theorems 3.2–3.3 give $r\in\mathcal R$, $s\in\mathcal S$,
and $C\le U_\rho(r)+V_\rho(s)$. Proposition 4.2 supplies
a same-mass representative achieving that upper bound.

Initial internal nonreturn is represented by $r=s=0$. Initial
zero-read return has $q=1$ and $C\le a/2$. The type-$I$ policy
$r=\eta$, $s=z$ has $q=1$ and

$$
C=\frac a2+a\eta+a^2\eta>\frac a2,
\tag{4.6}
$$

so it dominates this case too. Thus no mass has been lost by treating
early returns, and each claimed representative is actually paid.
Conversely every pair in (4.3) is realized by Proposition 4.2.
The finite maximum therefore gives (4.4)–(4.5) and is attained.
The strict inequalities inside (3.3) do not imply that different
total sums $r+s$ are distinct. Retaining the indices in (4.5)
handles every such equality without a generic-parameter assumption.
$\square$

## 5. Measurable finite-policy representation on the original seed space

**Theorem 5.1 (Same-mass domination by a measurable $K$ partition).**
For every protocol on a specified space
$(\mathsf U,\mathcal U,\nu)$ there is a measurable partition
$(G_k)_{k\in K}$ of that same space such that

$$
q=\sum_{k\in K}\nu(G_k)q_k,\qquad
L\ge\sum_{k\in K}\nu(G_k)\ell_k.
\tag{5.1}
$$

Conversely every such partition, followed by the corresponding
policies of Definition 4.1, attains both sums in (5.1). The seed
law, source and target remain unchanged. No regular conditional
distribution on $\mathsf U$ is required, and the statement includes
noncomplete spaces under the completed-version convention.

Proof. First take a measurable next-event representative of the
protocol. Ignore the numerical values of its finite waiting times;
only whether the next event is finite, its kind, and its address or
output are relevant. At the root and the two possible first replies,
and after each possible second reply, the truncated choices consist
of finitely many integers, finite-valued action types and finite-valued
outputs. Padding and rejection are as in Lemma 2.1. Thus the possible
truncated behavior codes form a countable set.

For each code its inverse image in $\mathsf U$ is measurable. It
is described by finitely many measurable next-event conditions at
specified finite records; the possible address values are countable.
The first-zero and first-one subtree masses and root type of that
code determine a $K$ label through Theorem 4.3. Use its fixed
representative also for the two initial cases. The resulting label
map is measurable, since each label inverse image is a countable
union of code inverse images. Write that finite partition as $G_k$.

For each fixed seed the source-section return mass is preserved,
and the source-section risk is no larger. The section masses are
ordinary $J_p$ masses of finite cylinders. Summing over the
countably many terminal records and integrating with respect to
$\nu$ gives (5.1), by Tonelli or monotone convergence. This uses
independence and product sections, not conditioning on a singleton
seed or assuming that the seed space is standard Borel.

In the reverse direction, a measurable finite partition chooses a
specific deterministic policy using only the original seed. The
chosen policy then makes its two actual calls on the same $J_p$.
Independence gives the two equalities for its masses. No extra
randomness has been appended to $\mathsf U$.

For completed versions, take measurable representatives first. There
are only countably many records and relevant next-event categories;
the union of their exceptional null sets is still null. A finite
partition in the completion of $\mathcal U$ has representatives
in $\mathcal U$ with the same measures. Remove overlaps successively
and assign the remaining set to one label to obtain a genuine
$\mathcal U$ partition. All masses are unchanged. Similarly,
completed-product modifications agree with measurable representatives
outside a product-null set, whose sections are null for almost every
seed by Tonelli. No pointwise assertion on the exceptional sections
is needed. This neither assumes that every subset of a null set was
originally measurable nor permits a completed partition to split a
positive-measure atom into positive parts. $\square$

Theorem 5.1 is stronger than agreement of support maxima: it retains
the exact mass of each protocol. Its representative set can omit
high-risk attainable pairs while still determining feasibility and
the whole lower frontier.

## 6. Measure atoms and exact division of the atomless remainder

**Lemma 6.1 (Decomposition of an arbitrary auxiliary probability
space).** A positive-measure atom means a measurable set $A$ of
positive measure such that every measurable subset of $A$ has
measure either zero or $\nu(A)$. It need not be a singleton.
All such atoms, modulo null equality, admit an empty, finite or
countable list of disjoint measurable representatives $A_n$ with
weights $\lambda_n=\nu(A_n)>0$. The measurable remainder

$$
\mathsf U_0=\mathsf U\setminus\bigcup_n A_n,\qquad
d=\nu(\mathsf U_0)=1-\sum_n\lambda_n
\tag{6.1}
$$

is atomless.

Proof. If two atoms have intersection of positive measure, that
intersection has full measure in each, so they agree modulo null
sets. Otherwise their intersection is null. Distinct atom classes
of measure at least $1/m$ number at most $m$: the measures of
any finite collection add after removal of null intersections and
have sum at most one. Every positive measure exceeds $1/m$ for
some positive integer $m$. Taking the union of these finite sets
shows that the atom classes are at most countable.

Choose representatives and remove from each the preceding
representatives. This removes only null intersections, preserves
its positive weight, and gives disjoint measurable atoms. Their
complement is measurable. A positive-measure atom in that complement
would be an additional atom class absent from the list, a
contradiction. Countable unions and differences suffice; no
completeness assumption was used. $\square$

**Lemma 6.2 (Exact measurable cutting without a new random source).**
If $E$ is an atomless measurable set of finite measure, then for
each $t\in[0,\nu(E)]$ it has a measurable subset of measure
exactly $t$. Consequently $\mathsf U_0$ can be partitioned into
any prescribed finite vector of nonnegative masses summing to $d$.

Proof. First, every positive-measure atomless set contains a
measurable subset with measure in $(0,\varepsilon]$ for each
$\varepsilon>0$. If its measure is too large, split it into two
positive-measure measurable pieces and choose a smaller piece.
It has at most half the old measure and is still atomless. Repeating
finitely many times yields the required small piece.

The cases $t=0,\nu(E)$ are immediate. Otherwise build disjoint
increments inside the remaining part of $E$, keeping their total
measure at most $t$. At a step with positive remaining gap, let
$s$ be the supremum of the measures of measurable subsets of the
remainder with measure at most that gap. The small-piece property
gives $s>0$. Choose an increment of measure greater than $s/2$
and at most the gap. Stop if the gap becomes zero. If this process
is infinite, its increasing union has measure $l\le t$.

Suppose $l<t$. Its final complement in $E$ has positive measure,
so contains a fixed measurable piece $B$ with
$0<\delta:=\nu(B)\le t-l$. This $B$ was available at every
step: it is disjoint from all chosen increments and its measure is
at most every remaining gap. Every step's supremum was therefore
at least $\delta$, forcing each increment to have measure greater
than $\delta/2$. Their sum cannot be bounded by $t$, a
contradiction. Hence $l=t$, proving exact cutting.

Apply this fact successively to obtain the desired finite masses;
take the last piece to be the remainder. Every piece belongs to
the original sigma-algebra. No uniform variable, point measurability,
countable generation, or completion of the space was needed.
$\square$

**Proposition 6.3 (All finite-policy weight vectors).** A finite
measurable $K$ partition of the specified seed space has precisely
the possible vectors

$$
(\nu(G_k))_{k\in K}
=\sum_n\lambda_n e_{k_n}+d(t_k)_{k\in K},\qquad
k_n\in K,\quad t_k\ge0,\quad\sum_{k\in K}t_k=1,
\tag{6.2}
$$

where $e_k$ is the $k$th unit vector. Every vector in (6.2) is
realized by a partition in the original $\mathcal U$.

Proof. The intersections of a finite partition with an atom have
measures either zero or the whole atom weight. Exactly one label
has the latter measure. Denote it by $k_n$. The remaining partition
weights come from $\mathsf U_0$ and sum to $d$, giving (6.2).
If $d=0$, the choice of $t$ is immaterial.

Conversely assign each whole $A_n$ to its specified label $k_n$,
and use Lemma 6.2 to partition $\mathsf U_0$ into masses $dt_k$.
The union of the atoms assigned to one label is a countable
measurable union. Adding its remainder piece yields the desired
partition. This proves both directions, including nonpoint atoms
and noncomplete spaces. $\square$

## 7. Exact feasible masses, fixed-law risks and attained minima

**Definition 7.1 (The finite convex function and representative
set).** Using the actual pairs in (4.3), define

$$
F(x)=\min\left\{\sum_{k\in K}t_k\ell_k:
t_k\ge0,\ \sum_kt_k=1,\ \sum_kt_kq_k=x\right\},
\qquad 0\le x\le1.
\tag{7.1}
$$

For the fixed auxiliary space and its decomposition (6.1), put

$$
\mathcal B_\nu=\left\{
\sum_n\lambda_n(q_{k_n},\ell_{k_n})
+d\sum_{k\in K}t_k(q_k,\ell_k):
k_n\in K,\ t_k\ge0,\ \sum_kt_k=1\right\}.
\tag{7.2}
$$

For an assignment $\kappa=(k_n)_n$, abbreviate

$$
Q_\kappa=\sum_n\lambda_nq_{k_n},\qquad
B_\kappa=\sum_n\lambda_n\ell_{k_n}.
\tag{7.3}
$$

All sums converge absolutely, because the pair coordinates belong
to $[0,1]$ and $\sum_n\lambda_n\le1$. With no atoms the
assignment is the single empty assignment and both sums are zero.

**Lemma 7.2 (Finite convex minima and two-policy remainder
realizations).** The minimum in (7.1) exists for every
$x\in[0,1]$. A minimizing vector can be chosen with at most two
positive entries. For $d>0$, the corresponding combination is
realized by cutting the original $\mathsf U_0$ into at most two
parts, without changing its law.

Proof. The set $K$ contains policies of masses zero and one, so
the constraint set in (7.1) is nonempty for every $x$. It is a
closed subset of the finite simplex, hence compact. Its continuous
linear objective attains a minimum.

If a minimizing vector has at least three positive entries, their
vectors $(1,q_k)$ are linearly dependent. There is a nonzero
direction $h$ supported on those entries with
$\sum_kh_k=\sum_kh_kq_k=0$. Both sufficiently small positive
and negative movements along $h$ preserve nonnegativity and the
constraints. Optimality forces $\sum_kh_k\ell_k=0$; otherwise
one of these two movements lowers the objective. Move until a
positive entry first becomes zero. The vector is still minimizing
and has smaller support. Finitely many repetitions leave at most
two positive entries. Lemma 6.2 cuts masses $dt_k$ inside the
original remainder, and Theorem 5.1 gives the paid realization.
$\square$

**Lemma 7.3 (Compactness with countably many atoms).** The set
$\mathcal B_\nu$ is compact. Every one of its points is attained
by a protocol on the original seed space. Every original protocol
has a point in $\mathcal B_\nu$ of the same return mass and no
larger risk.

Proof. Attainment follows from Proposition 6.3 and the converse in
Theorem 5.1. The domination assertion follows from the forward
direction of the same two results.

For compactness, take any sequence of points of $\mathcal B_\nu$
and choose their representations in (7.2). Pass to a subsequence
whose finite simplex vectors $t^{(m)}$ converge to a vector $t$.
For the first atom pass to a further subsequence on which its label
is constant, then do so for the second atom, and so on. A diagonal
subsequence has a label $k_n$ eventually constant for each fixed
$n$, while retaining convergence of the simplex vectors. A finite
or empty atom list only shortens this argument.

For any $N$, the first $N$ atomic summands eventually coincide
with those of the proposed limit. In either coordinate the
remaining difference is at most

$$
\sum_{n>N}\lambda_n,
\tag{7.4}
$$

since each label coordinate is in $[0,1]$. This tail tends to zero.
The finite remainder sum converges with $t^{(m)}$. Hence the
subsequence converges to the point represented by $(k_n)_n,t$,
which is in $\mathcal B_\nu$. This proves sequential compactness
in the Euclidean plane and thus compactness. It also covers $d=0$.
No continuity of a hypothetical optimizer on the infinite assignment
space, or exchange of an infimum with a limit, has been assumed.
$\square$

**Theorem 7.4 (Complete classification for each fixed auxiliary
law).** For every specified independent probability space of
Definition 1.2, all feasible masses are exactly the compact set

$$
\mathcal Q_\nu=\bigcup_\kappa[Q_\kappa,Q_\kappa+d].
\tag{7.5}
$$

It contains zero and one. At every $q\in\mathcal Q_\nu$ the
infimum in (1.5) is an actually attained minimum. Explicitly, if
$d>0$ it is

$$
\mathcal L_{2,\nu}(q)=
\min_{\substack{\kappa:\ Q_\kappa\le q\le Q_\kappa+d}}
\left[B_\kappa+dF\left(\frac{q-Q_\kappa}{d}\right)\right],
\tag{7.6}
$$

and if $d=0$ it is

$$
\mathcal L_{2,\nu}(q)=\min_{\kappa:\ Q_\kappa=q}B_\kappa.
\tag{7.7}
$$

Outside $\mathcal Q_\nu$, no original protocol has that exact
return mass and $\mathcal L_{2,\nu}(q)=+\infty$.

Proof. By Lemma 7.3 the feasible mass set of the original class is
exactly the first-coordinate projection of $\mathcal B_\nu$.
For each atomic assignment the remainder's mass projection is
$[0,d]$: all $q_k$ are in $[0,1]$, and the zero and one policies
already supply every convex mass between those endpoints. This
proves (7.5) in both directions. Compactness follows by projection
of the compact set in Lemma 7.3. Assigning all parts to a zero or
one policy proves inclusion of zero and one.

Fix a feasible $q$. The section of $\mathcal B_\nu$ with first
coordinate $q$ is nonempty and compact, so its second coordinate
has a minimum $l$. Every original protocol with mass $q$ has risk
at least $l$, by same-mass domination. The minimizing point itself
is attained on the original space by Lemma 7.3. Hence $l$ is
exactly $\mathcal L_{2,\nu}(q)$, with actual attainment even for
countably infinitely many atoms.

For a fixed atomic assignment and $d>0$, the remainder must have
normalized mass $(q-Q_\kappa)/d$. Its feasibility is equivalent
to the inequalities under the minimum in (7.6), and its smallest
risk is the attained value $dF((q-Q_\kappa)/d)$. For $d=0$,
the mass constraint is precisely $Q_\kappa=q$, with risk
$B_\kappa$. These observations give the displayed formulae.
To justify their outer minimum signs, take the already attained
minimizing point of the compact section and any representation of
it in (7.2). Its remainder must minimize (7.1); replacing a
nonoptimal remainder would contradict minimality. Its atomic
assignment therefore attains the outer expression. The $d=0$
case is immediate from that representation. If $q$ is outside the
projection there is no feasible protocol, proving the last clause.
$\square$

**Corollary 7.5 (The exact role of the fixed law).** A single
positive-measure atom of weight one gives (4.4)–(4.5), including
the constant-seed space. An atomless probability space gives
$\mathcal Q_\nu=[0,1]$ and
$\mathcal L_{2,\nu}=F$. For any fixed space and feasible mass,

$$
\mathcal L_{2,\nu}(q)\ge F(q).
\tag{7.8}
$$

If equality is unavailable at a feasible mass, the difference is
strictly positive between attained values, rather than a finite
unattained infimum.

Proof. The first two assertions substitute $d=0,\lambda_1=1$
and $d=1$ respectively into Theorem 7.4. Every point of
$\mathcal B_\nu$ is a convex combination of the finite pairs,
with total weight $\sum_n\lambda_n+d=1$. It therefore has
risk at least $F$ at its mass. If a fixed-law minimum equalled
$F(q)$, its actual attainer from Theorem 7.4 would attain that
value. Unavailability of equality thus forces a strict gap.
$\square$

For finitely many atoms, (7.6)–(7.7) involve finitely many atomic
assignments and a finite linear optimization. With countably many
atoms they are exact infinite weighted formulae and an existence
theorem. They are not a uniform finite algorithm on arbitrary
unencoded laws. Measurable selection of the optimal atom labels
here means a partition of the original space; it makes no claim of
an effective membership procedure or bounded-state implementation.

## 8. The strict support-invisible fixed-mass optimum

**Lemma 8.1 (The inherited two-read error coefficient, proved from
the leaf products).** Every original protocol satisfies

$$
L\ge\frac{b^2}{c}q.
\tag{8.1}
$$

The coefficient and its selective equality witness are Original,
Theorem 10.1 and (10.4), reused in Risk, §2.

Proof. First bound the largest correct proportion of each leaf by
$a^2/c$. A one-containing leaf certifies one phase. Inspection
of Lemmas 2.4–2.5 shows its possible maximal proportions are
$1/2$, $a$, or $a^2/c$. The latter exceeds $a$ because $a>c$.
A same-parity all-zero leaf has $M=a/2$ and $W\ge1/2$, so its
proportion is at most $a$. An opposite-parity $00$ leaf has
$W=c$, $M\le a^2/2$, hence proportion at most $a^2/(2c)$.
These cases include repetitions and impossible leaves of zero
mass. A zero-read return has correct proportion at most $a/2$;
a one-read return may either be padded as in Lemma 2.1 or bounded
directly by its one/zero branch proportions at most $a$.

Summing $M\le(a^2/c)W$ over accepted sections and integrating
gives $C\le(a^2/c)q$. Since $a^2+b^2=c$, this is (8.1).
The argument is recordwise and puts no restriction outside $E_2$.
$\square$

**Theorem 8.2 (Two attained minima with a strict seed-law gap).**
Let

$$
q_*=2\eta^2.
\tag{8.2}
$$

For a constant seed, or any auxiliary space consisting modulo null
sets of one measure atom, $q_*$ is the smallest positive feasible
mass and

$$
\mathcal L_{2,\mathrm{constant}}(q_*)=bq_*.
\tag{8.3}
$$

For every atomless auxiliary probability space,

$$
\mathcal L_{2,\nu}(q_*)=\frac{b^2}{c}q_*.
\tag{8.4}
$$

Both values are attained by lawful paid policies. Their difference is

$$
\Delta=\left(b-\frac{b^2}{c}\right)q_*>0.
\tag{8.5}
$$

Proof. By (3.3), the smallest positive entry of $\mathcal R$ is
$2\eta^2$, whereas the smallest positive entry of $\mathcal S$
is $\eta/2>2\eta^2$. Thus in (4.4) the smallest positive
mass is $q_*$, and its only decomposition is $r=q_*,s=0$.
The type-$D$ entry gives correct mass $2a\eta^2=aq_*$,
strictly exceeding the type-$I$ entry $\eta^2$. The deterministic
minimum is therefore $q_*-aq_*=bq_*$.

A direct attainer makes both predetermined actual calls

$$
2(j+4),\qquad 2(j+8),
\tag{8.6}
$$

and returns $h_0(\sigma)$ only on $11$. Otherwise it continues
internally forever after those two paid calls. That record certifies
phase zero. Its two spin pairs are disjoint from one another and
from $S_j$, so in the same original source

$$
q=\frac12(2\eta)^2=q_*,\qquad C=aq_*,\qquad L=bq_*.
\tag{8.7}
$$

For the atomless attainer, use the inherited selective anchor: read
the two predetermined actual addresses

$$
2j,\qquad 2(j+2),
\tag{8.8}
$$

and accept only $01$, with output $h_0(\sigma)$. In phase zero
the first zero edge contains $S_j$ and the disjoint second edge
is one. The phase-one replies would both be zero. Hence this
anchor has

$$
q_H=\eta c,\qquad C_H=a^2\eta,\qquad L_H=b^2\eta.
\tag{8.9}
$$

These are exactly the $n=2$ masses of Original, (10.4), not a new
selective anchor. By Lemma 6.2 the original atomless seed space
contains an event $G$ with

$$
\nu(G)=\frac{2\eta}{c}\in(0,1),
\tag{8.10}
$$

where $2\eta<c$ follows from $\eta<1/4$. Still make both
calls (8.8) on every path, but return only on $G$ and $01$.
All other paths internally do not return after the second call.
Independence gives

$$
q=\nu(G)\eta c=q_*,\qquad
L=\nu(G)\eta b^2=\frac{b^2}{c}q_*.
\tag{8.11}
$$

Lemma 8.1 proves its optimality over the full original class.
Finally $c-b=a(a-b)>0$, so $b-b^2/c>0$, proving (8.5).
Thus the two distinct minima are both actual values. The
atomless construction also permits every $0<q<q_*$ by a smaller
gate; all such masses are infeasible for the constant seed.
$\square$

**Theorem 8.3 (Strict suboptimality for every real support
objective).** The constant-seed fixed-mass optimal point

$$
P_*=(q_*,C_*)=(q_*,aq_*)
\tag{8.12}
$$

is strictly suboptimal for $C-\lambda q$ for every real
$\lambda$, among actual feasible deterministic policies of the
same original source and endpoint.

Proof. Three lawful deterministic competitors suffice. Complete
internal nonreturn gives $O=(0,0)$ in $(q,C)$ coordinates. A
single actual distant even read, for example $2(j+4)$, returning
$h_0(\sigma)$ only on one gives
$B=(\eta,a\eta)$. Its phase-zero spin pair avoids the target;
it may also be padded with a paid repeat. The two-read anchor
(8.8) gives $D=(\eta c,a^2\eta)$. These policies ignore the
seed, so all three are feasible under every fixed auxiliary law.

If $\lambda<a$, the objective gain of $B$ over $P_*$ is

$$
(a-\lambda)(\eta-q_*)>0.
\tag{8.13}
$$

If $\lambda>a$, the gain of $O$ over $P_*$ is
$(\lambda-a)q_*>0$. If $\lambda=a$, the objective of $P_*$
is zero, whereas the anchor has value

$$
a^2\eta-a\eta c
=a\eta(a-c)=(a-b)\eta^2>0.
\tag{8.14}
$$

This covers all real $\lambda$ by strict inequalities, proving
the assertion. $\square$

The example is not merely a tied or nonexposed point: for every
support objective a feasible point is strictly better. It is also
not an unreachable mass or a nonattained infimum. Its mass is
feasible, its constant-seed minimum is attained, and the smaller
atomless minimum is attained with a positive gap. These distinctions
are precisely what a classification of supporting values alone
does not retain.

## 9. The inherited universal curve, equality face and full-return slice

**Proposition 9.1 (Universal convex envelope and support values;
inherited comparison).** The function $F$ in (7.1) is the attained
minimum risk when the independent auxiliary probability space may
be chosen. If

$$
\mathscr B(\lambda)=\max_{k\in K}
\bigl[(1-\lambda)q_k-\ell_k\bigr],\qquad \lambda\in\mathbb R,
\tag{9.1}
$$

then it is the maximum of $C-\lambda q$ under every specified
auxiliary law, attained by a deterministic paid policy, and

$$
F(q)=\sup_{\lambda\in\mathbb R}
\bigl[(1-\lambda)q-\mathscr B(\lambda)\bigr].
\tag{9.2}
$$

This complete universal support curve is the result of
[Universal Support][Support]; the formula here expresses it through
the mass-preserving tables.

Proof. Theorem 5.1 bounds any supporting objective by the maximum
over its finite representatives, and a maximizing $K$ policy
attains it without using the seed. For any protocol at mass $q$,
its dominating pair is a convex combination of $K$ pairs, and so
has risk at least $F(q)$. An atomless space realizes a minimizing
combination by Lemmas 6.2 and 7.2, proving attained universal
optimality.

For completeness of the support representation, the convex hull
of the finitely many $(q_k,\ell_k)$ is a compact polygon. Its
lower section is $F$, defined at every $q\in[0,1]$. Each of
its lower edges has an affine supporting line; at an endpoint a
finite slope beyond the slopes of the finitely many edges suffices.
A lower vertex also admits such a slope. A line of slope
$1-\lambda$ below all the vertices has intercept at most
$-\mathscr B(\lambda)$. A supporting line at each lower point
attains that intercept, proving (9.2). This uses finite convex
geometry, with the actual paid realizations already established.
$\square$

**Proposition 9.2 (The inherited four-part face).** Put
$\delta=a-b$, $D=\delta\eta^2$ and $q_H=\eta c$.
The universal curve satisfies

$$
F(q)=bq-D,\qquad q_H\le q\le\eta(1+c).
\tag{9.3}
$$

For each specified unchanged auxiliary space, equality
$L=bq-D$ holds if and only if it admits a measurable four-part
partition $G_0,G_h,G_c,G_1$ such that

$$
q=q_H+\frac\eta2\nu(G_h)
+\eta c\nu(G_c)+\eta\nu(G_1).
\tag{9.4}
$$

The four deterministic equality masses are
$q_H$, $q_H+\eta/2$, $2\eta c$, and $\eta(1+c)$.
This face and its exact four-part criterion belong to Universal
Support, rather than being an additional fixed-law result claimed
here.

Proof. Consider $C-aq$ at a fixed seed. By the raw leaf tables,
every all-zero leaf has correct proportion strictly below $a$;
every ordinary one-containing leaf has proportion $a$ or $1/2$.
The only leaf with proportion greater than $a$ has a zero edge
touching the target and a disjoint one edge certifying the same
phase. Its masses are $(W,M)=(\eta c,a^2\eta)$ and its
excess is $D$ by (8.14). At most one such leaf occurs in any
depth-two tree: for type $I$ it is on first zero, and for type
$D$ on first one. Consequently $C-aq\le D$ at every seed,
including initial returns and nonreturns, and hence $L\ge bq-D$
after integration.

If equality holds at a seed, that unique exceptional leaf must
be accepted with a maximizing state. Every other accepted leaf
must have proportion exactly $a$. For type $I$, the first-zero
subtree is consumed by the exceptional leaf; on first one only
adjacency supplies such leaves, each of mass $\eta/2$.
The optional total is $0,\eta/2$, or $\eta$. For type $D$,
the exceptional first-one subtree uses a disjoint target-touching
zero edge; its other leaf has proportion $1/2<a$. On first zero,
the permitted proportion-$a$ leaves have mass $\eta/2$ from
adjacency, $\eta c$ from a disjoint avoiding edge, or $\eta$
from an opposite-parity edge avoiding its phase's target. Repeats
give no such leaf. Thus every equality seed has mass

$$
q(u)=q_H+d(u),\qquad d(u)\in\{0,\eta/2,\eta c,\eta\}.
\tag{9.5}
$$

Early returns do not add cases: zero-read and first-zero returns
have proportion below $a$; a type-$I$ first-one early return
has proportion $1/2$; a type-$D$ first-one early return has
proportion $a$ but prevents its exceptional descendant.

If integrated equality holds, the nonnegative deficit
$D-[C(u)-aq(u)]$ has integral zero. It vanishes almost everywhere,
so (9.5) holds almost everywhere. Its four distinct values define
the measurable partition in (9.4) by Theorem 5.1's countable-code
argument, with null sets treated as there. This proves necessity
without a regular conditional distribution.

For sufficiency all four policies occur explicitly in Section 4:
use type $D$, $(r,s)=(\eta c,0)$;
type $I$, $(r,s)=(\eta/2,\eta c)$;
type $D$, $(r,s)=(\eta c,\eta c)$; and
type $D$, $(r,s)=(\eta c,\eta)$, respectively.
Each has correct mass $aq+D$, by the tables, and each pays for
both actual calls on all paths. Running these policies on the
four parts gives exactly (9.4) with equality risk. On an atomless
space, mixing the first and last fills the entire interval in
(9.3), proving its universal attainment and the stated face.
No single adjustable gate has been assumed necessary: (9.4)
is the full partition condition. $\square$

**Proposition 9.3 (The inherited almost-sure-return slice).** For
every fixed auxiliary law,

$$
\mathcal L_{2,\nu}(1)
=1-\frac a2-a\eta-a^2\eta
=1-\frac a2-a^2b(1+a).
\tag{9.6}
$$

This is Slice, Theorem 6.1. Original, Theorem 11.4, and Risk,
Theorem 4.1, supply the one-read value
$1-a/2-a^2b$; it is also inherited.

Proof. The only total mass one in (4.3) uses $r=\eta,s=z$.
Its type-$I$ correct mass is (4.6), and its type-$D$ correct
mass is $a/2+a\eta+a\eta c$, smaller by
$a\eta(a-c)=D>0$. A convex combination of masses in $[0,1]$
can have mass one only by using mass-one policies almost
everywhere. Thus Theorem 5.1 bounds the correctness of any
full-return competitor by (4.6). Definition 4.1 with type $I$,
$r=\eta,s=z$ attains it, paying exactly twice and returning
on every path. Its disjoint first-zero second edge $f$ may be
replaced by $2(j+2)$, the attainer used in Slice; the leaf
products are the same. Since $a\eta=a^2b$, (9.6) follows.
$\square$

These comparisons identify the overlap: universal support and
its face classify convex envelope values and certain equality
partitions; the full-return slice supplies one mass independent
of seed availability. Theorem 7.4 additionally determines every
feasible mass and the minimum above the envelope when the
specified law cannot attain it. The point in Theorem 8.3 is a
strict witness to information lost by retaining only supporting
values.

## 10. Provenance and exact limits

**Attribution 10.1 (Mathematical ownership).** The following are
the owning repository sources. The inherited arguments used here
have also been proved directly above in the required two-read scope.

| Owning source | Inherited content and boundary |
| --- | --- |
| [Original][Original], Proposition 2.1, Lemma 3.1, §8, Definition 9.1 and Theorems 9.2–10.1 | The original law and endpoint, complementary-spin products, complete-half-line recovery as a measurability statement, full paid protocol, terminal source sections, count-only error and selective anchors. Complete-half-line recovery supplies no free read. |
| Original, Theorems 11.1–11.4 | The sharp all-zero record envelope and its paid witnesses, integrated record-type estimate, forced zero-record mass, and the exact one-read guaranteed-return optimum. None is new here. |
| Original, Theorems 12.2–12.3 | The finite $p$-independent representative family for arbitrary-address protocols under a hard total budget, preserving the full joint $Z=(H_j,O,D,N)$ target/output/return/count law and its measurable same-seed representation and converse. This hard-cap result is distinct from the unrestricted two-coordinate projection below. |
| Original, Theorem 13.2 and Boundary 13.3 | The classical finite partition-range and compactness result, its atomless simplex/convex-hull specialization, and the atomic/atomless partition-weight formula. These govern seed partition availability and do not add a randomizer or alter the given seed. |
| Original, Theorem 14.1 | The unrestricted budgeted-return projection onto $(q_k,L_k)$, with compactness and an attained minimum at every feasible mass. Its truncation preserves this two-coordinate projection only; it does not preserve the full hard-cap $Z$ law or unrestricted paid cost. |
| [Risk][Risk], §§1–2 and Theorem 3.1 | The same contract and recordwise estimates, with a general-budget return-mass correction not asserted optimal for every budget. |
| Risk, Theorem 4.1 | The exact universal one-read curve, its seed-event equality gate, and the overlapping one-read full-return optimum. |
| Risk, Theorem 5.1 and §6 | The finite paid-probe/local-block upper family and its exact return, risk and paid-cost formulae; its larger frontier and cost questions retain their boundaries. |
| [Universal Support][Support] | The complete all-real-support two-read curve, the attained universal envelope, and the explicit face with its four deterministic equality masses and four-part fixed-law criterion. These are comparisons in Section 9, not new universal-envelope results. |
| [Slice][Slice], Theorem 6.1 | The exact attained $q_2=1$ two-read minimum, restated in Proposition 9.3. |

The additional content of this volume is the full mass-preserving
$U_I/U_D$ and $V_I/V_D$ classification, its simultaneous paid
realizations and measurable finite-policy domination; the exact
fixed-law atomic-weight formulae and actual minimum at every
nonempty mass constraint; and the strict support-invisible
constant-seed optimum with the attained atomless risk separation.
These are source-specific, repo-derived results relative to the
named volumes. Atom decomposition, exact atomless cutting,
finite convex optimization and diagonal compactness retain their
usual general mathematical roles. No worldwide priority claim is
made.

**Boundary 10.2 (What completeness does and does not specify).**
Completeness here means the exact feasible return masses and the
lower risk frontier in the two-paid-read problem for every
specified auxiliary law. The set $\mathcal B_\nu$ is attainable
and provides a same-mass risk-dominating representative for every
original protocol. It is not asserted to be the entire attainable
region, including all higher-risk pairs. The infinite atomic
formulae give existence and exact constraints, not a uniform finite
algorithm for arbitrary probability laws without an effective
description. No simplified list of every bias-dependent total-mass
collision is needed or asserted; the indexed finite maximum
retains all of them.

**Boundary 10.3 (Resources and parameters).** The statements fix
$0<p<1$, $p\ne1/2$, and either original $j=0$ or $j=1$.
They do not extend to the fair or endpoint parameters, to budgets
$k>2$, to minimum expected paid cost, or to optimal stopping for
another resource. The paid representatives may replace exterior
behavior with internal nonreturn, so they do not optimize total
finite-return probability or preserve the distribution of all
costs. Every actual call of each constructed policy is nevertheless
charged. Internal computation, finite waiting, address size, program
length, counters, persistent state and physical storage receive no
complexity or bounded-memory conclusion. The measurable protocol
contract does not silently acquire an effectiveness restriction.

**Boundary 10.4 (Evidence and the original open problem).** These
are ordinary mathematical proofs. They supply no Lean-kernel
certification, numerical or experimental evidence, exhaustive
literature absence, or global originality assertion. The original
arbitrary-finite attainment/separation problem for the whole-domain
harmonic/Brier objective, Original, Open Problem 6.4, remains
unresolved by these endpoint-classification results. No neural
training, generalization, empirical-learning, physical realization
or whole-goal completion follows.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[Risk]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md
[Slice]: FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md
[Support]: FIB_TWO_PAID_READ_SELECTIVE_RISK_AND_SEED_AVAILABILITY.md

## 追加锚（本行以下为增补区）
