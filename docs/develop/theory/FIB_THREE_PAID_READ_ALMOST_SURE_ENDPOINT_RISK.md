# FIB three paid reads: exact almost-sure-return endpoint risk

For the original stationary biased XOR source, the attained minimum
four-state endpoint classification error with almost-sure finite return
and at most three actual paid reads is

$$
\varepsilon_3=1-\frac a2-3a^2\eta-2\eta^3,
\qquad a=\max(p,1-p),\quad b=\min(p,1-p),\quad\eta=ab.
$$

The ordinary probability proof below bounds every original measurable
adaptive arbitrary-integer-address protocol and gives one deterministic
policy attaining equality on the same source. Its two first-reply
subtree bounds are attained simultaneously. The model and acquisition
contract, zero-record results and exact one-read optimum are inherited
from [Original][Original] and [Risk][Risk]. The exact two-read optimum
belongs to [Two Read][TwoRead]. The additional result here is the exact
$q_3=1$ optimum, including its universal comparisons and fully paid
attainer.

## 1. Original law, fixed endpoint and full acquisition contract

**Definition 1.1 (Stationary biased XOR law).** Fix $0<p<1$ with
$p\ne1/2$. The alphabet $\mathcal A=\{a_0,a_1,b_0,b_1\}$ consists of
four distinct states. Let $\varphi$ be uniform on $\{0,1\}$, independently
of iid Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. On the
original integer clock set

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell:=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this joint hidden-visible law. This is Original,
Proposition 2.1 and (2.2). To identify its transition and emission clock,
put $\pi_0=1-p$ and $\pi_1=p$. From $a_s$ the next state is $b_t$
with probability $\pi_t$, emitting $s\oplus t$; from $b_t$ the next
state is $a_t$, emitting zero. The stationary state masses are
$(1-p,p,1-p,p)/2$: incoming mass at $b_t$ is
$\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and the copying transition gives the
same mass at $a_t$. Formula (1.1) therefore retains the actual emitted-bit
clock and separator positions. In particular $X_tX_{t+1}=0$ for every
integer $t$.

Fix one original endpoint index $j\in\{0,1\}$. Its actual hidden state
is

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{1.2}
$$

For this fixed $j$, define

$$
\begin{aligned}
h_0(s)&=\begin{cases}a_s&j=0,\\b_s&j=1,\end{cases}&v_0&=j,\\
h_1(s)&=\begin{cases}b_s&j=0,\\a_s&j=1,\end{cases}&v_1&=0.
\end{aligned}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.3}
$$

The answer sets $\{h_0(0),h_0(1)\}$ and $\{h_1(0),h_1(1)\}$ are
disjoint. Correctly guessing a spin in one phase does not also give a
correct state in the other phase. Representation (1.1) itself supplies
no observation of the phase or spins.

**Definition 1.2 (Original measurable paid protocol).** Let
$(\mathsf U,\mathcal U,\nu)$ be any probability space independent of
the entire $J_p$ source. Its law $\nu$ stays unchanged. Fixed public data
are constants; all random public data and all internal randomness belong
to this same auxiliary variable $u$. A finite acquired record is an
ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.4}
$$

Given only the public constants, $u$ and $r$, a measurable next-event
rule requests an integer address, returns a state $A\in\mathcal A$, or
continues internally indefinitely with neither another read nor a return.
A finite event may follow internal waiting. Its occurrence, kind,
address or output and finite waiting time are measurable functions of
exactly those available data. Waiting supplies no additional source
information. Addresses may depend on all earlier acquired replies.

A call at $t$ replies with precisely the actual $X_t$ in (1.1). Every
actual call costs one read, including repeats, ignored replies, separator
zeros, negative or positive addresses, disconnected configurations and
arbitrarily distant addresses. No later calculation refunds a call.

Let $\tau$ be the return time, with $\tau=\infty$ on every nonreturn,
and let $N\in\mathbb N_0\cup\{\infty\}$ count all actual calls. These
are separate variables. Internal nonreturn after any finite number of
calls, including zero, and infinite-read paths are admitted. A return
has finite $N$; its output and return time depend measurably only on the
public constants, $u$ and its terminal acquired record. A rule may return
before reading, or choose a wrong-phase state. Null records and versions
completed by null sets are included through the usual measurable
completion.

There is no hidden-state, half-line or tail read, source-dependent seed
or timing, reset, law switch, endpoint movement, or erased-coordinate
substitution. No additional coin is supplied. All ordinary measurable
rules satisfying this interface remain admitted; no effective
computability or bounded-storage condition is added. This is the
contract of Original, Definition 9.1, and Risk, Definition 1.2. Put
$\mathbb P_p=J_p\otimes\nu$.

**Definition 1.3 (Budgeted return and error).** Write

$$
\begin{gathered}
T=\{\tau<\infty\},\qquad
E_k=\{\tau<\infty,\ N\le k\},\\
q_k=\mathbb P_p(E_k),\qquad
L_k=\mathbb P_p(A\ne H_j,\ E_k),\\
a=\max(p,1-p),\quad b=\min(p,1-p),\quad
\eta=ab,\quad c=a^2+b^2=1-2\eta,\\
\delta=a-b>0,\quad R=a/b>1,\qquad
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2.\end{cases}
\end{gathered}
\tag{1.5}
$$

Thus $a+b=1$, $0<b<1/2<a<1$, and
$\mathbb P_p(S_\ell=\sigma)=a$. The condition studied here is exactly

$$
q_3=\mathbb P_p(\tau<\infty,\ N\le3)=1.
\tag{1.6}
$$

The contract imposes no restrictions on behavior outside $E_3$: there
may be later finite returns, internal nonreturn after finitely many calls,
or infinitely many calls. Under (1.6) these exceptional paths have mass
zero. Finite stopping on every possible source input is not a competitor
requirement. The risk $L_3$ is then the unconditional four-state
classification error, with the output extendible arbitrarily on null
nonreturns. It is distinct from a squared-loss prediction of an erased
visible bit.

## 2. Finite sections for every almost-sure competitor

**Lemma 2.1 (Acquired-record source sections).** At a fixed auxiliary
value $u$, a finite record compatible with the successive next-event
choices has source section

$$
C(r)=\bigcap_{i=1}^n\{X_{t_i}=x_i\}.
\tag{2.1}
$$

A record incompatible with those choices has empty section. On a
compatible return section the output is fixed.

Proof. The empty record imposes no source condition. At a fixed seed and
prefix, the next action and its waiting time are fixed. A read at $t$
with reply $x$ intersects the old section with $\{X_t=x\}$. A finite
return imposes no further source condition. Indefinite internal
continuation occurs on that whole prefix section. Induction proves
(2.1), including adaptive addresses and contradictory repeated replies,
the latter giving empty cylinders. $\square$

For any source event $C$ define

$$
m(C)=\max_{h\in\mathcal A}J_p(C,H_j=h).
\tag{2.2}
$$

Every single output on that section has correct mass at most $m(C)$.
This is a maximum of four joint masses. It never adds different-phase
answers on the same leaf.

**Lemma 2.2 (Reduction to unrestricted depth-three trees).** A uniform
upper bound for

$$
\sum_{x,y,z\in\{0,1\}}m(C_{xyz}),\qquad
C_{xyz}=\{X_t=x,\ X_{t_x}=y,\ X_{t_{xy}}=z\},
\tag{2.3}
$$

over every integer $t,t_0,t_1,t_{00},t_{01},t_{10},t_{11}$ bounds the
correct probability of every protocol satisfying (1.6), under every
unchanged independent auxiliary probability space.

Proof. Tonelli applied to the nonnegative indicator of $E_3^c$ gives
$J_p(E_3^c\text{ at }u)=0$ for almost every $u$. These are sections of
the independent product; no regular conditional law on $\mathsf U$ is
required.

Fix such a seed. By Lemma 2.1 a positive-mass reachable prefix is its
entire reply cylinder. Internal nonreturn there would exclude that
positive-mass cylinder from $E_3$. A fourth call before returning would
do the same, irrespective of all subsequent behavior. After three calls
a positive-mass branch must therefore return after finite waiting.

Pad each earlier return, including zero-, one- and two-read returns, to
three calls by predetermined calls, for example repetitions of address
zero. Keep its already chosen output on every resulting subleaf. The
subleaf cylinders partition its old return cylinder, so their correct
masses sum to exactly its old correct mass. This constructs a comparison
tree; it does not retroactively charge the original early return for
extra calls. Fill source-null or inconsistent branches with arbitrary
finite actions and outputs. Further intersections of a null cylinder
stay null.

The resulting tree has arbitrary first address, a second address
depending on the first reply, and a third depending on both earlier
replies, exactly as in (2.3). Its correct probability equals that of the
fixed-seed protocol and is at most the displayed sum. In particular this
reduction imposes no connectedness, address size, sign or parity
restriction.

For completed versions, take measurable representatives outside the
product-null exceptional sets. There are countably many finite
integer-address/reply records, so the relevant exceptional sets can be
combined into a product-null set. Tonelli makes its sections null for
almost every seed as well. Thus completion alters none of the integrated
masses or the preceding comparison. Integrate the uniform bound against
the original measurable correctness event. There is no need to choose
the padded trees or their maximizing outputs measurably as functions of
$u$. Neither an atomic nor a nonatomic auxiliary law needs any additional
property. $\square$

## 3. Complementary components and final-query comparisons

In a specified phase $\phi$, an active address $2\ell+\phi$ reads the
edge $\{\ell,\ell+1\}$ of the integer spin line. The other parity is a
separator. Conditional on that phase, distinct active queried edges form
disjoint finite paths. Specified XOR labels determine each path up to
complementation, so it has two assignment weights, each a product of
$a$ and $b$. Vertex-disjoint components are independent. Their full
probability factors must all be multiplied, including components outside
the target component. An unqueried target is adjoined as a singleton
with weights $a,b$. Passing from a phase-conditional mass to its full-law
mass introduces the factor $1/2$.

The analytic comparisons used below follow from

$$
\begin{gathered}
\frac12<c<a,\qquad c<2a^2,\qquad c>b,\qquad a>\frac12,\\
a-c=b\delta,\qquad 2a^2-c=\delta,\qquad c-b=a\delta,\\
t_*:=a^3+b^3\le a^2,\qquad a^2-t_*=b\delta.
\end{gathered}
\tag{3.1}
$$

For example $c-1/2=\delta^2/2>0$; the other identities use
$a+b=1$. Thus all comparisons hold throughout both biased parameter
ranges, without a sampled parameter comparison.

**Lemma 3.1 (Orientation identity and geometry).** Suppose the target
component has complementary weights $U\ge V>0$ and an independent
component has complementary weights $A\ge B>0$. After a new joining
edge, the sum over its two replies of the best target-spin mass is

$$
\begin{aligned}
\max(UA,VB)+\max(UB,VA)
&=UA+\max(UB,VA)\\
&=\max\bigl(U(A+B),A(U+V)\bigr).
\end{aligned}
\tag{3.2}
$$

All other components contribute their common multiplicative factors.
Either attachment orientation gives the same sum.

Proof. The two labels specify the two possible relative orientations of
the components. In one case the two target-spin weights are $UA,VB$;
in the other they are $UB,VA$. The displayed maxima follow, with
$UA\ge VB$. Reversing an attachment or the label order only interchanges
the two cases.

A fresh vertex has weights $a,b$. If $U/V\ge R$, (3.2) gives summed
best mass $U$; the preferred old orientation remains a maximizer for
each reply. If $U=V$, it gives $2aU$. A query wholly outside the target
component only partitions independent factors and leaves their summed
contribution unchanged.

On the line, a new edge repeats an old edge, extends one component by a
new vertex, joins two existing components, or is disjoint from them.
There is no additional edge inside a connected path, and one edge cannot
join three components. If a newly reached vertex is the target, treat
it as the already adjoined target singleton, making that operation a
join. Repeats and separators add no information. This exhausts all
target incidences and all integer addresses, including negative and
distant ones. Allowing a join comparison where the particular line
geometry prevents a join only enlarges an upper bound. $\square$

The next lemmas bound joint masses summed over a possible final reply.
They do not optimize incompatible normalized posteriors separately.

**Lemma 3.2 (One edge).** Conditional on a specified phase, the two
target-spin joint masses on a single active edge are

| Target position | Zero label | One label |
| --- | --- | --- |
| In the edge | $a^2,b^2$ | $\eta,\eta$ |
| Outside the edge | $ac,bc$ | $2a\eta,2b\eta$ |

Consequently a zero-edge prefix has maximal full-law state mass at most
$a^2/2$. A one-edge prefix with at most one further query has summed
full-law correct mass at most $a\eta$.

Proof. A zero edge has two constant assignments of weights $a^2,b^2$;
a one edge has two opposite assignments of weights $\eta,\eta$. An
external target contributes its independent factor $a$ or $b$, proving
the table. Since $ac<a^2$, the zero bound follows.

For an internal target after a one edge, an extension by a fresh vertex
gives phase-conditional best sum $2a\eta$ by (3.2). No other operation
can do better: a disjoint query leaves the tie unchanged, and repeats or
separators are uninformative. For an external target the singleton has
odds $R$. Joining the tie component gives
$\max(2a\eta,\eta)=2a\eta$. Joining a fresh vertex also leaves its
average majority probability $a$ unchanged; a nontarget query only
partitions the probability $2\eta$ of the first one edge. Thus in every
case the phase-conditional sum is at most $2a\eta$. Multiply by $1/2$.
$\square$

**Lemma 3.3 (Adjacent mixed triple).** Two distinct adjacent active
edges with at least one one label have complementary assignment weights
$a^2b=a\eta$ and $ab^2=b\eta$, total $\eta$. With at most one
additional query their summed full-law correct mass is at most
$a\eta/2$, for every target position and either acquisition order.

Proof. For left and right labels $01,10,11$, the larger assignments are,
respectively,

$$
(\sigma,\sigma,1-\sigma),\quad
(1-\sigma,\sigma,\sigma),\quad
(\sigma,1-\sigma,\sigma).
\tag{3.3}
$$

Each has weight $a^2b$; its complement has weight $ab^2$. Reversing
the acquisition order changes no weights. For an internal target the
component odds are $R$, so a fresh-vertex extension gives no summed
improvement by Lemma 3.1. A disjoint query, repeat or separator also
gives no improvement. For an exterior target, joining its singleton to
the triple gives
$\max(a\eta,(a\eta)(a+b))=a\eta$ before the phase factor, by
(3.2). A fresh-vertex query at the singleton leaves its majority
probability $a$ unchanged, while a query among nontarget vertices only
partitions the prefix probability $\eta$. These cases exhaust the last
query and prove the bound. $\square$

**Lemma 3.4 (Disjoint zero and one edges).** Two vertex-disjoint active
edges with labels zero and one, in either acquisition order, have summed
full-law correct mass at most $a^2\eta$ after at most one further query.

Proof. Their component weights are $(a^2,b^2)$ and $(\eta,\eta)$.
If the target is in the zero pair, its odds are $R^2$. An extension by
one fresh vertex cannot improve the best sum. Joining the tie pair
gives $2a^2\eta$ by (3.2); a nontarget query only partitions the
other factor. Thus $2a^2\eta$ is an upper bound before the phase prior.

If the target is in the one pair, an extension gives $2a\eta$ times
the zero-pair probability $c$, namely $2ac\eta$. Joining the zero
pair gives $2a^2\eta$. The latter dominates because $c<a$.
Queries not touching the target component, repeats and separators
give at most its original best mass $c\eta$.

If the target is outside both pairs, joining its singleton to the zero
pair gives $a^2$ times $2\eta$, because
$\max(ac,a^2)=a^2$. Joining the tie pair, adding a fresh vertex at
the singleton, or making a nontarget query gives at most
$2ac\eta\le2a^2\eta$. This includes a query joining the two
nontarget components: their labels are summed and the target remains
independent. All other components retain their probability factors.
Multiply the common bound $2a^2\eta$ by $1/2$. $\square$

**Lemma 3.5 (Two disjoint one edges).** After two vertex-disjoint active
edges labelled one, at most one further query gives summed full-law
correct mass at most $2a\eta^2$.

Proof. The phase-conditional prefix probability is $4\eta^2$. If the
target lies in either tie component, extending it by one fresh vertex
gives average correctness $a$. Joining the other tie component leaves
correctness $1/2$ by (3.2). A repeat, separator or nontarget query
leaves correctness $1/2$. For an external target its singleton has
odds $R$; joining a tie component or a fresh vertex leaves its average
correctness $a$, and a nontarget query cannot improve it. Hence every
case has correctness at most $a$ times the prefix probability. Including
the phase factor gives $\tfrac12(4\eta^2)a=2a\eta^2$. $\square$

**Corollary 3.6 (A fixed zero/one leaf).** With no further query, a
specified active zero edge and active one edge have maximal full-law
state mass at most $a^2\eta$.

Proof. A repeated edge with opposite labels is contradictory. Adjacent
edges give $a\eta/2\le a^2\eta$ by Lemma 3.3. For disjoint edges,
the masses according as the target is in the zero pair, in the one pair,
or outside both are

$$
a^2\eta,\qquad \frac{c\eta}{2},\qquad ac\eta.
\tag{3.4}
$$

They follow directly from the component products. The last two are at
most $a^2\eta$ by $c\le2a^2$ and $c\le a$. $\square$

## 4. A final one after two active zero edges

**Lemma 4.1 (Adjacent zero edges).** For two distinct adjacent active
edges $e,f$ and any third active edge $g$, the maximal full-law state
mass on

$$
e=0,\qquad f=0,\qquad g=1
\tag{4.1}
$$

is at most $a^3\eta$, for every target position.

Proof. The first two zero edges force their three spins to be constant,
with weights $a^3,b^3$ and total $t_*=a^3+b^3\le a^2$.
If $g$ repeats either edge, its one label is impossible. If $g$ is
vertex-disjoint from that triple, the full-law maximal masses are

| Target position | Maximal state mass |
| --- | --- |
| In the zero triple | $a^3\eta$ |
| In the one edge $g$ | $t_*\eta/2$ |
| Outside both | $at_*\eta$ |

These products include both assignments of the nontarget component.
Since $t_*\le a^2$ and $a\ge1/2$, all three are at most
$a^3\eta$.

The remaining possibility is that $g$ extends the zero triple. Its one
label gives weights $a^3b,ab^3$ on the four-spin component. An internal
target, including the new vertex, gives full-law mass
$a^3b/2=a^2\eta/2$. An exterior target gives
$a(a^3b+ab^3)/2=ac\eta/2\le a^2\eta/2$. Finally
$a^2\eta/2\le a^3\eta$. A single line edge has no further incidence
with this connected triple. $\square$

**Lemma 4.2 (Disjoint zero edges).** If $e,f$ are vertex-disjoint
active zero edges, the maximal full-law state mass on (4.1), for every
third active edge and target position, is at most $a^2c\eta$.

Proof. Each zero pair has weights $a^2,b^2$ and probability $c$.
Repeated $g$ is contradictory. A $g$ disjoint from both zero pairs gives

| Target position | Maximal state mass |
| --- | --- |
| In either zero pair | $a^2c\eta$ |
| In $g$ | $c^2\eta/2$ |
| Outside all three pairs | $ac^2\eta$ |

The last two are at most $a^2c\eta$ by $c\le2a^2$ and $c\le a$.

If $g$ extends one zero pair, that mixed triple has weights
$a^2b=a\eta,ab^2=b\eta$, total $\eta$. The untouched zero pair
still contributes its full factor. Thus

| Target position | Maximal state mass |
| --- | --- |
| In the mixed triple | $ac\eta/2$ |
| In the untouched zero pair | $a^2\eta/2$ |
| Outside both components | $ac\eta/2$ |

These are at most $a^2c\eta$ because $a\ge1/2$ and $c\ge1/2$.
The first row includes a target at the newly introduced vertex.

If $g$ joins the two zero pairs, its one label forces their constant
spins to be opposite. The two four-spin assignments each have weight
$\eta^2$. An internal target gives full-law mass $\eta^2/2$ and an
exterior target gives $a\eta^2$. Since $a\ge1/2$, the latter bounds
both; and

$$
a\eta^2\le a^2c\eta,
\qquad \eta\le ac\ \Longleftrightarrow\ b\le c.
\tag{4.2}
$$

This is (3.1). Repeat, extension, join and disjointness exhaust the
third edge, proving the result. A separator could not give its required
one reply either. $\square$

## 5. Uniform bounds for both first-reply subtrees

Fix an arbitrary depth-three tree of Lemma 2.2. Let $\alpha$ be the
parity of its first address and $\beta=1-\alpha$. Its active first
edge in phase $\alpha$ is $e$. The first reply one certifies phase
$\alpha$. Define the actual sums of maximal terminal state masses

$$
B_1=\sum_{y,z}m(C_{1yz}),\qquad
B_0=\sum_{y,z}m(C_{0yz}).
\tag{5.1}
$$

**Lemma 5.1 (Every first-one subtree).** Uniformly over the first
address and all adaptive later addresses,

$$
B_1\le D:=a^2\eta+2a\eta^2
=a\eta+\delta\eta^2.
\tag{5.2}
$$

Proof. Work in the certified phase $\alpha$, keeping its actual target
vertex $v_\alpha$. If the second call is a separator or repeats $e$,
there is at most one additional informative call. Lemma 3.2 bounds
$B_1$ by $a\eta$.

If the second call is a distinct adjacent active edge, each second
reply leaves a mixed triple because the first label is one. Lemma 3.3
bounds each remaining subtree by $a\eta/2$, so again
$B_1\le a\eta$.

If the second active edge is vertex-disjoint from $e$, its zero branch
is bounded by Lemma 3.4 by $a^2\eta$, and its one branch is bounded
by Lemma 3.5 by $2a\eta^2$. Each branch may choose its own third
address. Their sum gives $D$. Finally

$$
D-a\eta
=a\eta(a-1+2\eta)
=\eta^2(2a-1)=\delta\eta^2>0.
\tag{5.3}
$$

Thus $D$ also bounds the preceding cases. Both first parities, every
second-call parity, all target incidences and every final-query geometry
have been included. $\square$

**Lemma 5.2 (Every first-zero subtree).** Uniformly over all addresses
and adaptive choices,

$$
B_0\le Z:=\frac a2+a^2\eta(1+c).
\tag{5.4}
$$

Proof. Introduce the comparison quantity

$$
Q=\frac{a^2}{2}+a\eta+a^2\eta.
\tag{5.5}
$$

First suppose the second call after the first zero has parity
$\alpha$, with active edge $f$ in that phase. Its second reply one
certifies $\alpha$ and imposes $e=0,f=1$. If $f=e$ this continuation
is null. For adjacent $e,f$, Lemma 3.3 bounds the summed final
continuation by $a\eta/2$. For disjoint $e,f$, Lemma 3.4 bounds it
by $a^2\eta$. In all cases $a^2\eta$ is a valid upper bound.
These comparisons allow either parity and any address for that branch's
third call.

Consider the second-zero prefix. If its third call has parity
$\alpha$, the final-zero leaf contains all of phase $\beta$:
every call on this leaf is a separator there. The phase-$\beta$
majority state therefore has mass $a/2$. Every individual state has
prior at most $a/2$, so this leaf's maximum is exactly $a/2$.
Its final-one leaf imposes $e=0,f=0,g=1$ in phase $\alpha$.

When $f=e$, that last leaf has a single zero edge and one one edge.
If $g$ is adjacent to $e$, Lemma 3.3 bounds it by
$a\eta/2\le a^2\eta$. If $g$ is disjoint, Corollary 3.6, or the
disjoint comparison of Lemma 3.4 without a further query, bounds it by
$a^2\eta$. If $g=e$, its required one contradicts the zero prefix.
The second-one branch is null in this repeated-prefix case. Hence

$$
B_0\le\frac a2+a^2\eta\qquad(f=e).
\tag{5.6}
$$

This explicitly treats the adjacent, disjoint and repeated final edges
separately.

For distinct adjacent $e,f$, Lemma 4.1 bounds the final-one leaf by
$a^3\eta$, while Lemma 3.3 bounds the second-one continuation by
$a\eta/2$. For disjoint $e,f$, Lemma 4.2 bounds the final-one leaf
by $a^2c\eta$, while Lemma 3.4 bounds the second-one continuation
by $a^2\eta$. Thus

$$
\begin{array}{c|c}
\text{incidence of }e,f&\text{upper bound for }B_0\\ \hline
\text{adjacent}&a/2+a^3\eta+a\eta/2\\
\text{vertex-disjoint}&a/2+a^2c\eta+a^2\eta=Z
\end{array}
\tag{5.7}
$$

The repeated bound in (5.6) is smaller than $Z$ by $a^2c\eta>0$.
The adjacent bound is also smaller, since

$$
Z-\left(\frac a2+a^3\eta+\frac{a\eta}{2}\right)
=\frac{a\eta\delta c}{2}>0.
\tag{5.8}
$$

Still with the second call of parity $\alpha$, suppose instead that
the third call on the second-zero prefix has parity $\beta$. The final
all-zero leaf then has at least one active zero edge in each phase.
Lemma 3.2 bounds each individual state's mass by $a^2/2$; imposing
further constraints cannot increase that state's joint mass. Its
final-one leaf certifies $\beta$. In this phase both earlier calls
were separators, so the sole active constraint is this last one edge.
Its maximal full-law state mass is at most $a\eta$ by Lemma 3.2.
Adding the at-most-$a^2\eta$ second-one continuation proves
$B_0\le Q$ in this case, including repeats or adjacency among the
earlier active edges in the other phase.

Now suppose the second call after the first zero has parity $\beta$.
Its second reply one certifies $\beta$ and leaves one active one edge
with one query remaining, so Lemma 3.2 bounds that continuation by
$a\eta$. On its second-zero prefix each phase has one active zero
edge. Whatever parity the third call has, the final all-zero leaf has
maximal individual state mass at most $a^2/2$. A final one certifies
the phase of the third address and leaves a zero edge and one edge
there. Corollary 3.6 bounds that leaf by $a^2\eta$: repeated edges
are contradictory, adjacent edges use Lemma 3.3, and disjoint edges
use their full products. This again gives $B_0\le Q$.

Finally, using $a+b=1$ and $\delta=a-b$,

$$
\begin{aligned}
Z-Q
&=\eta\left(\frac12-a+a^2c\right)\\
&=\frac\eta2\left(b^2+a^2\delta^2\right)>0.
\end{aligned}
\tag{5.9}
$$

Every case therefore gives $B_0\le Z$. Both second-call parities,
both third-call parities on the zero-zero prefix and independently
chosen third calls on the other prefix have been allowed. The bounds
are uniform in target location and component orientation. On every
mixed-phase leaf we took a single state's maximum, not a sum of
different-phase answers. $\square$

**Proposition 5.3 (Universal depth-three bound).** Every tree in (2.3)
satisfies

$$
\sum_{x,y,z}m(C_{xyz})\le S_3,
\qquad S_3=\frac a2+3a^2\eta+2\eta^3.
\tag{5.10}
$$

Proof. The actual two subtrees satisfy $B_0\le Z$ and $B_1\le D$.
Their sum is

$$
\begin{aligned}
Z+D
&=\frac a2+a^2\eta(2+c)+2a\eta^2\\
&=\frac a2+3a^2\eta+2a(1-a)\eta^2\\
&=\frac a2+3a^2\eta+2\eta^3,
\end{aligned}
\tag{5.11}
$$

because $c=1-2\eta$ and $a(1-a)=ab=\eta$. This proves the
inequality uniformly over every address tree. Equality still requires
one policy attaining both subtree bounds with the same first call and
source. $\square$

## 6. One original-source policy attaining both bounds

**Definition 6.1 (Three actual paid calls).** Ignore $u$, leaving its
law unchanged. First call the original address $2j$, then call
$2(j+2)$ regardless of the first reply. Denote these replies by $x,y$.
Make the third actual call and return according to this table, where
$z$ is the third reply:

| First replies $x,y$ | Third actual integer address | Output for $z=0$ | Output for $z=1$ |
| --- | --- | --- | --- |
| $0,0$ | $2(j+4)$ | $h_1(\sigma)$ | $h_0(\sigma)$ |
| $0,1$ | $2j$ | $h_0(\sigma)$ | $h_0(\sigma)$ |
| $1,0$ | $2(j+1)$ | $h_0(1-\sigma)$ | $h_0(\sigma)$ |
| $1,1$ | $2(j-1)$ | $h_0(\sigma)$ | $h_0(1-\sigma)$ |

Choose zero internal delays. Every call is made and charged, including
the deliberate repeat on prefix $01$. When $j=0$, prefix $11$ uses
the legal negative address $-2$. The rule is a total measurable finite
table, including its output on the inconsistent reply triple $011$.
It has exactly $N=3$ and finite return on every path.

All its addresses are even. In phase zero they are the displayed active
edges $Y_\ell$. In phase one all are actual separator calls, and only
triple $000$ is reached. These are properties of the paid observations
under (1.1); the policy acquires no phase observation before its calls.

**Proposition 6.2 (Eight full-law correct masses).** For Definition 6.1,
the full-law correct-state masses are

$$
\begin{array}{c|c|c}
(x,y,z)&\text{output}&\mathbb P_p(x,y,z,A=H_j)\\ \hline
000&h_1(\sigma)&a/2\\
001&h_0(\sigma)&a^2c\eta\\
010&h_0(\sigma)&a^2\eta\\
011&h_0(\sigma)&0\\
100&h_0(1-\sigma)&a^2\eta/2\\
101&h_0(\sigma)&a^2\eta/2\\
110&h_0(\sigma)&a\eta^2\\
111&h_0(1-\sigma)&a\eta^2
\end{array}
\tag{6.1}
$$

The first-zero masses sum to $Z$, and the first-one masses sum to $D$,
simultaneously for this one policy and realization, for either $j$ and
every unchanged independent auxiliary law.

Proof. On $000$ the output is a phase-one state. Success there is
exactly $\varphi=1,S_0=\sigma$, with mass $a/2$, since in that
phase every paid call is a separator. Phase-zero realizations on the
same leaf are errors for this output: the phase-specific state sets
are disjoint. The target spin is $S_0$ in phase one for both choices
of $j$, as (1.2) requires.

On $001$, the third paid one certifies phase zero. Its three edge
constraints concern the disjoint pairs

$$
(S_j,S_{j+1}),\quad(S_{j+2},S_{j+3}),\quad
(S_{j+4},S_{j+5}).
\tag{6.2}
$$

For the declared output to be correct, the first pair must be both
$\sigma$, of probability $a^2$. The second pair agrees, of
probability $c$, and the third disagrees, of probability $2\eta$.
Independence of these spin pairs in the same source gives
$\tfrac12 a^2c(2\eta)=a^2c\eta$.

On $010$, the second one again certifies phase zero. The first pair
must be both $\sigma$ and the second disjoint pair must disagree.
The third actual call repeats the first address, so it replies zero.
The correct mass is $\tfrac12 a^2(2\eta)=a^2\eta$. Triple $011$
contradicts this actual repeat and has mass zero, although its output
is specified.

On $100$ and $101$, the actual phase-zero edges are $Y_j,Y_{j+2}$
and then the joining edge $Y_{j+1}$. The corresponding larger-mass
four-spin completions are

$$
\begin{array}{c|c|c}
(x,y,z)&(S_j,S_{j+1},S_{j+2},S_{j+3})&\text{spin weight}\\ \hline
100&(1-\sigma,\sigma,\sigma,\sigma)&a^3b\\
101&(\sigma,1-\sigma,\sigma,\sigma)&a^3b
\end{array}
\tag{6.3}
$$

Each complementary completion has weight $ab^3<a^3b$ and the
opposite target spin. The declared output uses the actual $S_j$ of
the displayed completion. Multiplying by the phase factor yields
$a^3b/2=a^2\eta/2$ on each leaf.

On $110$ and $111$, the third actual edge is $Y_{j-1}$. The local
preferred completions are

$$
\begin{array}{c|c|c}
(x,y,z)&(S_{j-1},S_j,S_{j+1})&\text{spin weight}\\ \hline
110&(\sigma,\sigma,1-\sigma)&a^2b\\
111&(\sigma,1-\sigma,\sigma)&a^2b
\end{array}
\tag{6.4}
$$

Their complements have weight $ab^2<a^2b$. The already paid edge
$Y_{j+2}=1$ uses the separate pair $(S_{j+2},S_{j+3})$, of
probability $2\eta$ in that same realization. The output uses the
middle spin $S_j$ in (6.4). Each leaf therefore has correct mass
$\tfrac12(a^2b)(2\eta)=a\eta^2$.

These calculations verify both endpoint indices, not just their labels:
in phase zero the spin is $S_j$, giving $a_{S_0}$ for $j=0$ and
$b_{S_1}$ for $j=1$; in phase one it is $S_0$, giving $b_{S_0}$ or
$a_{S_0}$ respectively. In particular the $j=1$ calculation does not
replace its phase-zero target by $S_0$. When $p>1/2$, $\sigma=1$;
when $p<1/2$, $\sigma=0$. Every product and output above uses this
same majority convention, so both bias directions are covered.

Finally the first-zero rows of (6.1) give

$$
\frac a2+a^2c\eta+a^2\eta=Z,
\tag{6.5}
$$

and the first-one rows give

$$
\frac{a^2\eta}{2}+\frac{a^2\eta}{2}
+a\eta^2+a\eta^2=D.
\tag{6.6}
$$

Thus one original source and policy attain both bounds with the same
first two calls. No separately optimized incompatible sources, phases
or first queries are combined. Ignoring $u$ makes the result independent
of any event availability or atomlessness of its unchanged law.
$\square$

## 7. The exact minimum and the inherited two-read comparison

**Theorem 7.1 (Exact attained almost-sure three-read optimum).** For
every $0<p<1$ with $p\ne1/2$, either fixed original endpoint
$j\in\{0,1\}$ and every specified unchanged independent auxiliary
probability space, the minimum over all protocols of Definition 1.2
satisfying $q_3=1$ is

$$
\begin{aligned}
\min L_3
&=1-\frac a2-3a^2\eta-2\eta^3\\
&=1-\frac a2-3a^3b-2a^3b^3.
\end{aligned}
\tag{7.1}
$$

Definition 6.1 attains this minimum with three actual calls and finite
return on every path. The lower bound holds for the complete
almost-sure competitor class, including its null exceptional paths.

Proof. For any competitor, Lemma 2.2 reduces its correct probability,
at almost every seed, to at most the sum (2.3). Proposition 5.3 bounds
that sum by $S_3$ uniformly in all address choices and outputs.
Integrating against the unchanged $\nu$ therefore gives

$$
\mathbb P_p(A=H_j,T)\le S_3.
\tag{7.2}
$$

The integration uses the original measurable correctness event;
completed versions and exceptional seed sections have zero effect.
No regular conditional probability, measurable optimizer selection or
all-input stopping restriction enters the argument. Since $E_3$ has
mass one, correct and incorrect state masses sum to one, giving
$L_3\ge1-S_3$.

Definition 6.1 is admissible for every specified auxiliary law and has
$q_3=1$. Proposition 6.2 gives its correct probability $Z+D=S_3$.
This proves equality and attainment, rather than only an infimum or
an improved construction. The second form of (7.1) uses $\eta=ab$.
$\square$

**Comparison 7.2 (Strict gain at the unchanged task and resource).**
The inherited exact result of Two Read, Theorem 6.1, is

$$
S_2=\frac a2+a\eta+a^2\eta,
\qquad \varepsilon_2=1-S_2.
\tag{7.3}
$$

With the same original source, endpoint, classification loss and
actual-call budget convention, Theorem 7.1 implies

$$
\begin{aligned}
\varepsilon_2-\varepsilon_3
&=S_3-S_2\\
&=a^2c\eta+\delta\eta^2>0.
\end{aligned}
\tag{7.4}
$$

Indeed $S_3=Z+D$, $Z-(a/2+a^2\eta)=a^2c\eta$, and
$D-a\eta=\delta\eta^2$ by (5.3). Both displayed increments are
strictly positive. The gain is conditional on retaining this exact task
and paid-read resource; it makes no comparison of other losses or
resources.

## 8. Mathematical ownership and exact boundaries

**Attribution 8.1 (Inherited content and added result).** The owning
repository sources and their roles are

| Source | Inherited content |
| --- | --- |
| `FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md`, Proposition 2.1 and (2.2) | The original stationary four-state law, iid spins, independent uniform phase and separator clock. |
| Original, Lemma 3.1, Definition 9.1, Theorems 9.2–10.1 and (9.4)–(9.5) | Complementary products, full paid arbitrary-address contract, actual endpoint indices and finite source-section likelihood method. |
| Original, Theorems 11.1–11.3 | Zero-record envelope, integrated record-type bound and zero-record mass forced by a return budget. |
| Original, Theorem 11.4 | The exact almost-sure-return one-read minimum $1-a/2-a^2b$. |
| `FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md`, §§1–4 | The same law and contract, finite-record interface, zero-return correction and exact one-read envelope, including the overlapping one-read minimum. |
| `FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md`, Theorem 6.1 | The exact attained almost-sure two-read minimum (7.3), with its complete-competitor reduction and simultaneous two-subtree attainer. |

Both Original §11 and Risk receive credit for the zero-record and
one-read results. Their selective count-only sharpness is distinct from
an almost-sure-return optimum. The exact two-read result is inherited,
not an additional discovery of this volume. The finite-section method
and elementary complementary-product mechanism are also inherited;
they are proved here where needed for a self-contained argument.

The added content is precisely the full $q_3=1$ bound, the one-query
mixed-component and two-zero-prefix comparisons required for it, and
simultaneous equality in one actually paid three-call policy. Equation
(7.4) is a consequence of this result and the inherited two-read value.
The attribution is relative to the supplied source results; it asserts
no exhaustive literature comparison.

**Boundary 8.2 (Unsettled return and budget frontiers).** Theorem 7.1
settles only $q_3=1$. It does not determine the frontier at $q_3<1$,
an optimum at a larger budget, an expected-paid-cost optimum, or a
general stopping theorem. Selectively omitting leaves changes the
subtree accounting. The auxiliary law remains specified and unchanged;
ignoring it in the attainer does not settle selective event-availability
questions for other return masses. Behavior outside $E_3$ remains
unrestricted by the acquisition contract.

**Boundary 8.3 (Other objectives and resources).** The result concerns
four-state endpoint classification and actual visible calls only.
Original, Open Problem 6.4, and the whole-domain harmonic/Brier
attainment and separation problem remain outside its conclusion.
The budget supplies no bound on internal computation, waiting time,
address size, persistent state or physical storage. It gives no neural
training, generalization or empirical learning result. All proofs here
are ordinary mathematical arguments. The fair parameter $p=1/2$ and
the endpoints $p=0,1$ are excluded from Theorem 7.1. Finite return on
every path is a property of the displayed attainer, while the universal
lower bound retains the larger almost-sure class of Definition 1.2.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[Risk]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md
[TwoRead]: FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md

## 追加锚（本行以下为增补区）
