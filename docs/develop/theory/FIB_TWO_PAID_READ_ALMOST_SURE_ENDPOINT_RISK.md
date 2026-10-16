# FIB two paid reads: exact almost-sure-return endpoint risk

For the original biased XOR source, the attained minimum four-state
endpoint classification error with almost-sure finite return and at most
two actual paid reads is

$$
1-\frac a2-a^2b(1+a),\qquad
a=\max(p,1-p),\quad b=\min(p,1-p).
$$

This volume proves the bound for all original arbitrary-address adaptive
protocols and gives a deterministic attainer on that same source. The
new result is the exact slice with return mass $q_2=1$. The source law,
endpoint identification, finite-record interface, selective count-only
bounds, zero-record bounds and one-read optimum belong to
[Original][Original] and [Risk][Risk]. In particular the DEV text of
Original, §11, already includes zero-record return-budget bounds and the
exact one-read minimum; the latter is also in Risk, Theorem 4.1. Neither
is claimed as new here.

## 1. The unchanged source, endpoint and acquisition contract

**Definition 1.1 (Original stationary biased XOR source).** Fix a real
parameter $0<p<1$, $p\ne1/2$. The alphabet
$\mathcal A=\{a_0,a_1,b_0,b_1\}$ has four distinct states. Let
$\varphi$ be uniform on $\{0,1\}$ and independent of the iid
Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. Define, on the
original integer clock,

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell:=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this joint hidden-visible law. This is the realization
in Original, Proposition 2.1 and (2.2). With
$\pi_0=1-p$ and $\pi_1=p$, its active transition takes $a_s$ to $b_t$
with probability $\pi_t$ and emits $s\oplus t$; its next transition
takes $b_t$ to $a_t$ and emits zero. The stationary masses of
$(a_0,a_1,b_0,b_1)$ are $(1-p,p,1-p,p)/2$: incoming mass at $b_t$ is
$\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and the copying transition supplies
the same mass at $a_t$. Thus (1.1) retains the stationary emitted-bit
clock and its separator positions. It also gives $X_tX_{t+1}=0$ at
every integer $t$.

Fix one endpoint index $j\in\{0,1\}$. The target is the actual $H_j$
of (1.1), with the phase-specific identification

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{1.2}
$$

as in Original, (9.4). For this fixed $j$, define state labels and target
spin indices by

$$
\begin{aligned}
h_0(s)&=\begin{cases}a_s&j=0,\\b_s&j=1,\end{cases}&
v_0&=j,\\
h_1(s)&=\begin{cases}b_s&j=0,\\a_s&j=1,\end{cases}&
v_1&=0.
\end{aligned}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.3}
$$

The two sets $\{h_0(0),h_0(1)\}$ and
$\{h_1(0),h_1(1)\}$ are disjoint. An observation compatible with both
phases does not merge these states into a single correct answer.
Representation (1.1) supplies no access to an unobserved spin or phase.

**Definition 1.2 (Original paid arbitrary-address protocol).** Take any
probability space $(\mathsf U,\mathcal U,\nu)$ independent of the whole
$J_p$ source, keeping $\nu$ unchanged. Fixed public data can be included
as constants; all random public data and all internal randomness belong
to this same auxiliary variable $u$. The acquired record is a finite
ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.4}
$$

Based only on those public data, $u$ and $r$, a measurable next-event
rule either requests an integer address, returns a state in $\mathcal A$,
or continues internally forever without another read or return. Finite
events may follow internal waiting. Whether such an event occurs, its
kind, address or output, and its finite waiting time are measurable
functions of exactly those available data. In particular waiting
conveys no additional source information.

A requested address $t$ returns exactly the actual $X_t$ in (1.1).
Every actual call costs one read. Repeated addresses, separator zeros,
negative addresses, disconnected sets and arbitrarily distant addresses
are all charged. An ignored reply still costs its call. Addresses may
depend on all previously acquired replies.

Let $\tau$ be the return time, setting $\tau=\infty$ on every nonreturn,
and let $N\in\mathbb N_0\cup\{\infty\}$ count all actual calls. Internal
nonreturn after any finite number of calls, including zero, is allowed;
so are infinite-read paths. A return has finite $N$, and its output and
return time depend measurably only on the available data and its
terminal acquired record. A return before reading and a wrong-phase
output are permitted. Null records and versions completed by null sets
are included through the usual measurable completion.

No hidden-state, half-line or tail read, source-dependent auxiliary
variable or timing, reset, law switch, moving endpoint, or replacement of
an erased coordinate is available. This is the full contract of
Original, Definition 9.1, also restated in Risk, Definition 1.2. Put
$\mathbb P_p=J_p\otimes\nu$.

**Definition 1.3 (Risk and parameters).** Write

$$
\begin{gathered}
T=\{\tau<\infty\},\qquad
E_k=\{\tau<\infty,\ N\le k\},\\
q_k=\mathbb P_p(E_k),\qquad
L_k=\mathbb P_p(A\ne H_j,\ E_k),\\
a=\max(p,1-p),\qquad b=\min(p,1-p),\qquad
\eta=ab,\qquad c=a^2+b^2,\\
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2.\end{cases}
\end{gathered}
\tag{1.5}
$$

Thus $a+b=1$, $0<b<1/2<a<1$, and the majority spin $\sigma$ has
probability $a$. The competitor condition in this volume is

$$
q_2=\mathbb P_p(\tau<\infty,\ N\le2)=1.
\tag{1.6}
$$

Under (1.6), $L_2$ is the unconditional four-state classification error.
One may extend $A$ arbitrarily on the null nonreturn event without
changing it. The loss is an incorrect hidden endpoint state, distinct
from squared loss for an erased visible bit. Condition (1.6) allows
exceptional nonreturn or excess-read paths of probability zero; it is
not a requirement of finite stopping on every possible input.

## 2. Finite source sections and the complete competitor reduction

**Lemma 2.1 (Fixed-seed cylinder sections).** Fix an auxiliary value $u$.
If a finite ordered address/reply record $r$ agrees with the successive
next-event choices, its source section is the cylinder

$$
C(r)=\{X_{t_i}=x_i:1\le i\le n\}.
\tag{2.1}
$$

If the choices disagree, the section is empty. When the rule returns
after this record, its output is fixed on that section. The same
assertion applies to a reachable prefix before a return.

Proof. The empty record imposes no condition. At a fixed seed and
prefix, the rule's next action and its internal delay are fixed. If it
requests $t$, adjoining reply $x$ intersects the previous cylinder with
$\{X_t=x\}$. A finite return adds no source restriction, and indefinite
internal continuation is the same behavior on that entire prefix
section. Induction on the number of calls proves the assertion, also
for adaptive choices. Contradictory repeated replies give empty
cylinders. This is the finite-section interface of Original, Theorems
9.2–10.1, proved here directly from Definition 1.2. $\square$

For a source event $C$ define its best possible correct-state mass by

$$
m(C)=\max_{h\in\mathcal A}J_p(C,H_j=h).
\tag{2.2}
$$

This is a maximum of four ordinary joint masses. On a terminal section,
every specified output has correct mass at most $m(C)$. We never sum
the best state in each phase as if both could be output on one leaf.

**Lemma 2.2 (Almost-sure protocols reduce to depth-two trees).** To bound
the correct probability of every protocol satisfying (1.6), it suffices
to bound, uniformly over all integer choices $t,t_0,t_1$, the sum

$$
\sum_{x,y\in\{0,1\}}m(C_{xy}),\qquad
C_{xy}=\{X_t=x,\ X_{t_x}=y\}.
\tag{2.3}
$$

The first address is $t$ and the second address is $t_x$ after first
reply $x$. Repeated and otherwise arbitrary addresses remain allowed.

Proof. Apply Tonelli's theorem to the nonnegative indicator of
$E_2^c$ on the independent product $J_p\otimes\nu$. Equation (1.6)
gives a set of auxiliary values of full $\nu$-measure for which the
source section of $E_2$ has $J_p$-mass one. This statement uses product
sections, without requiring a regular conditional probability on
$\mathsf U$.

Fix such a value $u$. By Lemma 2.1, every positive-mass reachable
prefix has exactly its acquired-reply cylinder as section. Indefinite
internal continuation there, or a third call before returning, would
exclude a positive-mass source section from $E_2$. Neither can occur
on a positive-mass branch of this fixed-seed rule. At two calls a
positive-mass branch must therefore return after finite internal
waiting.

If the rule returns with zero or one call, pad that return with enough
predetermined actual calls to make two, keeping its already selected
output on every resulting subbranch and ignoring the added replies.
For example each padding call can use address zero. The new cylinders
partition the old terminal cylinder, so their correct masses for that
unchanged output sum to exactly its old correct mass. Padding here is
an analysis of the bound, not an assertion that the original protocol
already paid those calls. On zero-mass or inconsistent branches choose
any finite actions and outputs. A source-null branch stays null under
further intersections.

The resulting fixed-seed tree has a first address $t$, second addresses
$t_0,t_1$, and an output at each of four leaves. It has the same correct
probability as the original fixed-seed protocol, and that probability
is bounded by (2.3). Exceptional source sections and the excluded null
set of seeds contribute no integrated mass. For completed versions,
measurable representatives agree outside product-null sets; Tonelli
again makes their sections agree almost everywhere. A measurable
choice of the completed trees or of maximizing leaf outputs is
unnecessary: the desired uniform bound is applied at each eligible
seed, and the original correctness event is measurable. $\square$

## 3. The elementary masses on the integer spin line

In phase $\phi$, an active address $2\ell+\phi$ reads the edge
$e=\{\ell,\ell+1\}$ with label $S_\ell\oplus S_{\ell+1}$; an address
of the other parity reads a separator. The actual target vertex in
this phase is $v_\phi$ from (1.3). Distinct active edges of this
integer line either share one vertex or have disjoint vertex sets.
There are no other incidences for two distinct edges, regardless of
their distance, sign or order of acquisition.

**Lemma 3.1 (One active edge).** Conditional on a specified phase, an
active edge has zero-reply probability $c$ and one-reply probability
$2\eta$. Its two joint target-spin masses are as follows, with the
majority-spin mass listed first when it differs from the other mass.

| Position of the target vertex | Reply zero | Reply one |
| --- | --- | --- |
| In the edge | $a^2,\ b^2$ | $\eta,\ \eta$ |
| Outside the edge | $ac,\ bc$ | $2a\eta,\ 2b\eta$ |

All entries in this table are conditional on that phase. A full-law
mass with this phase specified has an additional factor $1/2$. The
total best target correctness after one XOR with phase known is $a$,
whether or not its edge meets the target.

Proof. A zero XOR says the two spins agree, giving the assignments
$(\sigma,\sigma)$ and $(1-\sigma,1-\sigma)$ with masses $a^2,b^2$.
A one XOR has the two assignments
$(\sigma,1-\sigma)$ and $(1-\sigma,\sigma)$, each of mass $ab=\eta$.
If the target is outside the pair, its independent spin factor is
$a$ or $b$. This proves the table. For an incident edge the sum of the
two maximal branch masses is $a^2+\eta=a$; for an exterior target it
is $ac+2a\eta=a$, since $c+2\eta=1$. $\square$

The comparisons used below are

$$
a>\frac12,\qquad
a-c=b(a-b)>0,\qquad
2a^2-c=a^2-b^2>0.
\tag{3.1}
$$

**Lemma 3.2 (Two adjacent active edges with a one).** Suppose two
distinct active edges share a vertex and at least one of their labels
is one. For either orientation of the edges, the constraints leave two
complementary three-spin assignments. Their masses conditional on the
phase are $a^2b$ and $ab^2$. For every target position, the maximal
joint endpoint-state mass on this constrained phase section is
$a\eta/2$ under the full law.

Proof. Write the ordered triple on the union as $(s_0,s_1,s_2)$.
Its two successive XOR labels determine the triple once $s_0$ is
given, leaving exactly the triple and its complement. A label one
excludes constant triples. For clarity, the three possible label pairs
on the left and right edges have these majority-mass assignments:

$$
\begin{array}{c|c|c}
\text{left label}&\text{right label}&(s_0,s_1,s_2)\\ \hline
0&1&(\sigma,\sigma,1-\sigma)\\
1&0&(1-\sigma,\sigma,\sigma)\\
1&1&(\sigma,1-\sigma,\sigma)
\end{array}
\tag{3.2}
$$

Each displayed assignment has mass $a^2b$, and its complement has
mass $ab^2<a^2b$. Reversing which edge was read first only changes
which row applies. For a target in the triple, these complementary
assignments give opposite target spins, so the maximal full-law state
mass is $a^2b/2=a\eta/2$. For a target outside the triple, the
constraint has phase-conditional probability
$a^2b+ab^2=ab=\eta$. Multiplication by the independent majority
target factor $a$ and the phase factor $1/2$ gives the same answer.
$\square$

## 4. Universal bounds for both subtrees

Fix any tree from Lemma 2.2. Let $\alpha\in\{0,1\}$ be the parity
of its first address $t$, and put $\beta=1-\alpha$. Let $e$ be the
first address's active edge in phase $\alpha$. The first reply one
certifies phase $\alpha$ and has full-law mass $\eta$. The first
reply zero retains both phase alternatives. Define

$$
B_1=m(C_{10})+m(C_{11}),\qquad
B_0=m(C_{00})+m(C_{01}).
\tag{4.1}
$$

**Lemma 4.1 (Every first-one subtree).** For every second address $t_1$,

$$
B_1\le a\eta.
\tag{4.2}
$$

Proof. Only phase $\alpha$ remains, so its target is the fixed vertex
$v_\alpha$. If $t_1$ is a separator in that phase or repeats the
first address, it adds no information. In the separator case its
reply is necessarily zero; in the repeated case it is necessarily
one. By Lemma 3.1 the maximal correct mass is $\eta/2$ if the target
belongs to $e$, and $a\eta$ otherwise. Both are at most $a\eta$.

Otherwise the second call is a distinct active edge $f$. If $e,f$
share a vertex, each second-reply value imposes a mixed triple of
Lemma 3.2. Each leaf then has maximal correct mass $a\eta/2$,
including an exterior target, so their sum is $a\eta$.

If the two edges have disjoint vertex sets, consider all three target
placements. For a target in $e$, the first-one condition gives equal
target-spin masses $\eta$ before the phase factor, independently of
$f$. Summing the maximal masses over the two labels of $f$ gives

$$
\frac{\eta}{2}(c+2\eta)=\frac{\eta}{2}.
\tag{4.3}
$$

For a target in $f$, the first constraint has probability $2\eta$
and is independent of the edge and target calculation at $f$.
Lemma 3.1 therefore gives total correct mass
$\tfrac12(2\eta)a=a\eta$. For a target in neither edge, it remains
independent of both constraints, so the first-one mass $\eta$
multiplied by its majority probability $a$ gives $a\eta$.

These exhaustive possibilities can be summarized by their total
subtree correct masses:

| Second call in the certified phase | Target placement | $B_1$ |
| --- | --- | --- |
| Separator or repeated edge | In $e$ | $\eta/2$ |
| Separator or repeated edge | Outside $e$ | $a\eta$ |
| Distinct edge sharing a vertex with $e$ | Anywhere | $a\eta$ |
| Edge vertex-disjoint from $e$ | In $e$ | $\eta/2$ |
| Edge vertex-disjoint from $e$ | In $f$ or in neither edge | $a\eta$ |

Since $a>1/2$, every row proves (4.2). The table includes null leaves
with mass zero in its summed values. $\square$

**Lemma 4.2 (First-zero subtree, same-parity second call).** If $t_0$
has parity $\alpha$, then

$$
B_0\le\frac a2+a^2\eta.
\tag{4.4}
$$

Proof. In phase $\beta$ both calls are separators. Thus $C_{00}$
contains that entire phase, and the state $h_\beta(\sigma)$ has
joint mass $a/2$ on it. Every particular endpoint state's prior is
at most $a/2$, so

$$
m(C_{00})=\frac a2.
\tag{4.5}
$$

This maximum is over individual four-state answers. It does not add
an optimal phase-$\alpha$ state to an optimal phase-$\beta$ state.

The leaf $C_{01}$ certifies phase $\alpha$ and imposes $e=0,f=1$,
where $f$ is the active edge at $t_0$. Repetition $f=e$ makes it
impossible. If the two distinct edges share a vertex, Lemma 3.2
gives maximal state mass $a\eta/2$, for either orientation and any
target position.

For vertex-disjoint edges, independence and Lemma 3.1 give the
following full-law maxima:

$$
\begin{array}{c|c|c}
\text{target placement}&\text{product giving the maximum}&m(C_{01})\\ \hline
v_\alpha\in e&\tfrac12 a^2(2\eta)&a^2\eta\\
v_\alpha\in f&\tfrac12 c\eta&c\eta/2\\
v_\alpha\notin e\cup f&\tfrac12 ac(2\eta)&ac\eta
\end{array}
\tag{4.6}
$$

The middle row uses the equal target-spin masses on a one edge;
the last row uses the independent target factor. In particular it
retains the full probability of the disjoint zero constraint.

All nonzero cases are at most $a^2\eta$: for the adjacent case use
$a/2\le a^2$, for the middle row of (4.6) use $c\le2a^2$, and for
the last row use $c\le a$, as in (3.1). Repetition, adjacency and
vertex-disjointness exhaust the possible edges. Adding (4.5) proves
(4.4). $\square$

**Lemma 4.3 (First-zero subtree, opposite-parity second call).** If
$t_0$ has parity $\beta$, then

$$
B_0\le\frac{a^2}{2}+a\eta
<\frac a2+a^2\eta.
\tag{4.7}
$$

Proof. The second address is a separator in phase $\alpha$ and an
active edge $f$ in phase $\beta$. On $C_{00}$ the phase-$\alpha$
section imposes only $e=0$, whereas the phase-$\beta$ section imposes
only $f=0$. Apply Lemma 3.1 to each phase using its actual target
vertex $v_\alpha$ or $v_\beta$. In a phase whose edge meets its
target the largest full-law state mass is $a^2/2$; otherwise it is
$ac/2<a^2/2$. The phase state sets are disjoint, so the largest
state mass over their union is a maximum over these alternatives.
It follows that

$$
m(C_{00})\le\frac{a^2}{2}.
\tag{4.8}
$$

The leaf $C_{01}$ certifies phase $\beta$ and imposes just $f=1$;
the first read was its automatic separator. Its maximal state mass
is $\eta/2$ if $f$ meets $v_\beta$, and $a\eta$ otherwise. Hence
$m(C_{01})\le a\eta$, proving the first inequality in (4.7).

The difference between the same-parity bound and this bound is

$$
\begin{aligned}
\left(\frac a2+a^2\eta\right)
-\left(\frac{a^2}{2}+a\eta\right)
&=\frac\eta2-\eta^2\\
&=\frac{\eta c}{2}>0,
\end{aligned}
\tag{4.9}
$$

using $a(1-a)=ab=\eta$ and $c=1-2\eta$. No relation between
two hypothetical target locations was assumed: each mass was
computed inside its own phase section of the one original law.
$\square$

**Proposition 4.4 (Universal depth-two correct-mass bound).** Every tree
in (2.3) satisfies

$$
\sum_{x,y}m(C_{xy})\le S_2,
\qquad S_2=\frac a2+a\eta+a^2\eta.
\tag{4.10}
$$

Proof. Lemma 4.1 bounds $B_1$ by $a\eta$. Lemmas 4.2 and 4.3
bound $B_0$ by $a/2+a^2\eta$ for either possible parity of $t_0$.
Their sum gives (4.10). The second addresses on the two first-reply
branches were allowed to differ. Every integer address, both first
parities, both orientations of adjacency, repeated edges, disjoint
edges and every target incidence have been included. $\square$

## 5. A single fully paid policy attaining both subtree bounds

**Definition 5.1 (Deterministic two-call rule).** Ignore $u$, without
changing its law. First request the actual original address $2j$.
After reply $x$, make the second actual call and then return according
to this table, where $y$ is the second reply:

| First reply $x$ | Second actual address | Output if $y=0$ | Output if $y=1$ |
| --- | --- | --- | --- |
| $0$ | $2(j+2)$ | $h_1(\sigma)$ | $h_0(\sigma)$ |
| $1$ | $2(j+1)$ | $h_0(1-\sigma)$ | $h_0(\sigma)$ |

There is no search for a phase before the first call and no extra
observation between these two calls. Choose finite internal delays,
for example zero. The table specifies an output for every binary
reply pair, including impossible ones. Thus the rule is measurable,
returns in finite time on every input, and has

$$
N=2\quad\text{on every path}.
\tag{5.1}
$$

In phase zero its first paid reply is $Y_j$. Its second paid reply
is $Y_{j+2}$ on the zero branch and $Y_{j+1}$ on the one branch.
In phase one every address in the table is a separator. These
statements describe the actual replies under (1.1); they grant no
free phase observation.

**Proposition 5.2 (Same-source leaf masses and simultaneous equality).**
For the rule in Definition 5.1 the four correct masses are

$$
\begin{array}{c|c|c}
(x,y)&\text{output}&\mathbb P_p(x,y,A=H_j)\\ \hline
(0,0)&h_1(\sigma)&a/2\\
(0,1)&h_0(\sigma)&a^2\eta\\
(1,0)&h_0(1-\sigma)&a\eta/2\\
(1,1)&h_0(\sigma)&a\eta/2
\end{array}
\tag{5.2}
$$

Consequently its correct probability is $S_2$ for either fixed
endpoint $j$ and every unchanged independent auxiliary law.

Proof. For the leaf $00$, the output is a phase-one state. In phase
one both paid replies are automatically zero, and by (1.3) the actual
target spin is $S_0$ for both choices of $j$. Success on this leaf is
exactly the phase-one event $S_0=\sigma$, of mass $a/2$. Any phase-zero
sources reaching the same leaf give a different endpoint state and
are errors for this output.

For $01$, the second paid reply one certifies phase zero. The
constraints are

$$
S_j\oplus S_{j+1}=0,\qquad
S_{j+2}\oplus S_{j+3}=1.
\tag{5.3}
$$

These two pairs of spins are disjoint in the same realization.
The actual phase-zero target is $S_j$, also when $j=1$, where its
state label is $b_{S_1}$. The prescribed output is correct exactly
when $S_j=S_{j+1}=\sigma$. Therefore its correct mass is

$$
\frac12 a^2(2ab)=a^2\eta.
\tag{5.4}
$$

For the first-one branch phase zero has been certified by that paid
reply. The two actual edges are $Y_j$ and $Y_{j+1}$. On $10$ their
larger-mass completion is

$$
(S_j,S_{j+1},S_{j+2})=(1-\sigma,\sigma,\sigma),
\tag{5.5}
$$

whose target is exactly the output $h_0(1-\sigma)$ and whose spin
mass is $a^2b$. The other completion has mass $ab^2$ and the opposite
target spin. On $11$ the larger completion is

$$
(S_j,S_{j+1},S_{j+2})=(\sigma,1-\sigma,\sigma),
\tag{5.6}
$$

whose target gives $h_0(\sigma)$ and whose mass is again $a^2b$.
The complementary completion again has mass $ab^2$. Multiplying by
the phase factor makes each correct leaf mass $a^2b/2=a\eta/2$.
This proves every row of (5.2).

The first-zero branch thus attains $a/2+a^2\eta$, while the
first-one branch attains $a\eta$, using the same first address and
the same original source. Their extremal masses are simultaneously
realized by one admissible policy. The rule ignores $u$, so the
calculation applies without any atomlessness, event availability or
additional random coin on the auxiliary space. $\square$

## 6. The exact almost-sure-return minimum

**Theorem 6.1 (Attained two-paid-read endpoint optimum).** For every
$0<p<1$, $p\ne1/2$, either fixed endpoint $j\in\{0,1\}$, and every
arbitrary unchanged independent auxiliary probability space, the
minimum over all protocols of Definition 1.2 satisfying $q_2=1$ is

$$
\begin{aligned}
\min L_2
&=1-S_2\\
&=1-\frac a2-a^2b(1+a).
\end{aligned}
\tag{6.1}
$$

The minimum is attained by Definition 5.1, with exactly two paid calls
and finite return on every path. The lower bound holds in the larger
almost-sure class (1.6), including its null exceptional paths.

Proof. Fix an arbitrary competitor satisfying (1.6). Lemma 2.2 gives,
for almost every seed, a depth-two source-section tree with unchanged
correct probability. Proposition 4.4 bounds that probability by $S_2$
uniformly over its addresses and outputs. Integrate this inequality
against the original $\nu$. Tonelli's theorem on the measurable
original correctness event gives

$$
\mathbb P_p(A=H_j,T)\le S_2.
\tag{6.2}
$$

Source-null sections and the null exceptional seed set do not change
the integral. No regular conditional probability on the auxiliary
space, measurable selection of optimizing trees, all-input stopping
assumption or restriction on the possible integer addresses was used.
Since $E_2$ has mass one, correct and incorrect classification masses
sum to one, giving $L_2\ge1-S_2$.

Definition 5.1 is a competitor for every auxiliary law, and
Proposition 5.2 gives correct probability $S_2$. Hence equality is
attained. Finally $a\eta+a^2\eta=a^2b+a^3b=a^2b(1+a)$, proving
the displayed form. $\square$

**Comparison 6.2 (Consequence of the inherited one-read optimum).**
Original, Theorem 11.4, and Risk, Theorem 4.1, already establish the
attained one-read minimum

$$
\varepsilon_1=1-\frac a2-a^2b.
\tag{6.3}
$$

Writing $\varepsilon_2$ for (6.1), subtraction gives

$$
\varepsilon_1-\varepsilon_2=a^3b>0.
\tag{6.4}
$$

This strict improvement is a consequence of the new two-read value
and the inherited one-read value, rather than an independent
one-read discovery or a separate optimization problem solved here.

## 7. Provenance and unresolved boundaries

**Attribution 7.1 (Supplier results and the precise increment).** The
mathematical source identities are the following two existing volumes.
The ordinary finite-product and decision-tree proof above is
self-contained within their original law and protocol.

| Source and section | Inherited content and role |
| --- | --- |
| `FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md`, Proposition 2.1 and (2.2) | The stationary four-state hidden-visible law, its independent uniform phase, iid spins and original separator clock. |
| Original, Lemma 3.1 and §8 | Complementary-spin product mechanism and complete-half-line endpoint recovery. The latter grants no paid-read operation here. |
| Original, Definition 9.1, Theorem 9.2 and (9.4)–(9.5) | The full protocol contract, unchanged endpoint indices, finite source-section interface and finite-product likelihood comparison. |
| Original, Theorem 10.1 and (10.4) | Sharp selective count-only coefficients and fully paid selective witnesses. In particular $e_2=b^2/(a^2+b^2)$ is inherited. |
| Original, Theorems 11.1–11.3 | Sharp all-zero terminal-record envelope, its integrated record-type bound and forced zero-record mass under a return budget. |
| Original, Theorem 11.4 | The exact almost-sure-return one-read minimum (6.3), with a deterministic one-paid-call attainer. |
| `FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md`, §§1–2 | The same law, endpoint table, contract, return/risk notation and existing finite-record estimates. |
| Risk, Theorem 3.1 | A universal return-mass correction for finite budgets, without a general optimality assertion. |
| Risk, Theorem 4.1 | The exact universal one-read return-mass envelope, its seed-event equality criterion and the same almost-sure-return one-read minimum (6.3). |
| Risk, Theorem 5.1 and §6 | A finite paid-probe/local-block upper family and its exact cost formulas, together with the unresolved larger frontier questions. |

Original's §11 and Risk's one-read result overlap on (6.3); both receive
credit. Selective coefficient sharpness in Original, Theorem 10.1,
does not give an almost-sure-return optimum, because its witnesses
may reject records. The additional result here is precisely (6.1):
the universal sum of both subtree correct masses, with their
simultaneous equality under one two-paid-call policy. The one-edge
products, complementary triples and maximum-state classification
rule retain their elementary meanings. The claimed increment is
relative to these supplied texts, with no worldwide priority claim.

**Boundary 7.2 (Return mass and auxiliary-law frontiers).** Theorem 6.1
settles $q_2=1$. It does not determine the complete lower frontier at
a prescribed $q_2<1$. Selectively omitting leaves changes the
accounting in (4.1)–(4.10). No complete selective equality criterion,
supporting-objective family, or optimal mixing construction is
established here. Under a specified atomic auxiliary law, measurable
gate availability remains a real constraint; ignoring the seed in
the $q_2=1$ attainer does not resolve those selective frontiers.
Risk's exact one-read equality gate is inherited, while optima above
that universal envelope at attainable masses without such a gate
remain outside this result.

**Boundary 7.3 (Other budgets and original attainment problem).** No
larger-budget optimum, expected-paid-cost optimum, or general optimal
stopping theorem follows from (6.1). Expected paid cost would count
every actual call on returning and nonreturning paths; a mean
restricted to returns is a different resource. The finite upper
family in Risk, Theorem 5.1, retains its existing scope. The original
arbitrary-finite attainment/separation question for the whole-domain
harmonic/Brier objective, Original, Open Problem 6.4, remains
unestablished by this endpoint-classification volume.

The budget here measures actual visible calls. Internal computation,
address size, return time, program length, counters, persistent state
and physical storage receive no complexity or bounded-memory
conclusion. No neural learning, training, generalization or empirical
learning conclusion is supplied. The fair parameter $p=1/2$ and the
endpoint parameters $p=0,1$ are outside the theorem. The deterministic
attainer's all-input finite stopping strengthens its own construction;
it does not narrow the lower-bound competitor class or settle any
overall research goal.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[Risk]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md

## 追加锚（本行以下为增补区）

## 8. Equality rigidity and minimum installed complete-controller states

**Definition 8.1 (Closed finite controller and endpoint state cost).**
Keep exactly Definitions 1.1--1.3: one fixed $0<p<1$, $p\ne1/2$,
one original endpoint $j\in\{0,1\}$ fixed before acquisition, the
actual four-state target $H_j$, and the given independent probability
space $(\mathsf U,\mathcal U,\nu)$ with its unchanged law. A closed
finite controller is a tuple $(K,\lambda,\delta,c_{\rm init})$, where
$K$ is a nonempty finite set, its instruction map is

$$
\lambda:K\longrightarrow
\{\operatorname{Read}(t):t\in\mathbb Z\}
\sqcup\{\operatorname{Halt}(h):h\in\mathcal A\},
\tag{8.1}
$$

$K_{\rm R}$ and $K_{\rm H}$ are the inverse images of the two
instruction types, and

$$
\delta:K_{\rm R}\times\{0,1\}\longrightarrow K,
\qquad c_{\rm init}:\mathsf U\longrightarrow K
\tag{8.2}
$$

has a measurable initialization map, with $K$ discrete. Initialization
sets the current state to $c_{\rm init}(u)$. In state $r$ with
$\lambda(r)=\operatorname{Read}(t)$, the controller makes one actual
call at that fixed integer address, receives exactly $X_t$, and changes
state to $\delta(r,X_t)$. In a halt state it returns the fixed label
$h$ and ends. Each instruction has finite duration. There is no silent
instruction. An execution that never reaches a halt has $\tau=\infty$
and makes infinitely many charged reads.

After initialization the current element of $K$ contains every runtime
distinction that can affect an action, a successor or a returned label.
The seed is not read again. There is no separate phase, counter, clock,
archive, stack, output latch, program position or other runtime port.
In particular the last reply is used only in (8.2), and is not available
beside the resulting state at the next instruction. All installed rows
count: the state cost is $|K|$, including rows never initialized or
visited. The table and its integer literals may depend on the fixed
public $p,j$. This objective does not minimize static address lengths,
code size, the initialization mechanism, physical bits or writes, time,
energy, or expected reads.

This is the complete-state instruction convention of
[Relational II, Definitions 26.1--26.2](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md),
specialized to the original actual-coordinate observations and fixed
halt labels. General finite-memory action and update maps also occur in
Junges et al., *Permissive Finite-State Controllers of POMDPs using
Parameter Synthesis*, [Definition 7](https://arxiv.org/html/1710.10294v2).
That background does not supply the endpoint-specific minima below.

Every such table is a legal protocol of Definition 1.2; it is a specified
subclass, not a representation theorem for every original protocol.
The original unrestricted class, including internal nonreturn after
finitely many calls, retains its original meaning. A table may have
cycles and arbitrarily long read paths. Its benchmark is still the
almost-sure statistic $q_k=1$, not an all-input hard cap. Repeated,
separator and remote calls are charged exactly as in Definition 1.2.

Write

$$
\begin{aligned}
S_1&=\frac a2+a\eta,&
S_2&=\frac a2+a\eta+a^2\eta,\\
M_k(p,j,\nu)&=\min\bigl\{|K|:
q_k=1,\ L_k=1-S_k\text{ for a controller of (8.1)--(8.2)}\bigr\},
&&k\in\{1,2\}.
\end{aligned}
\tag{8.3}
$$

The minimum of an empty set is $+\infty$. The values $S_1,S_2$ are
the inherited unrestricted correctness optima: Original, Theorem 11.4,
and Risk, Theorem 4.1, supply $S_1$; Theorem 6.1 supplies $S_2$.
The optimization in (8.3) asks for the least installed state cost among
tables attaining those values on the same source and seed law.

**Lemma 8.2 (Equality on every positive initialization cell).**
For a table of Definition 8.1 let
$\omega_r=\nu(c_{\rm init}^{-1}\{r\})$. If it satisfies
$q_k=1$ and $L_k=1-S_k$, then every $r$ with $\omega_r>0$, used as
a deterministic initial state, has $q_k(r)=1$ and correct mass $S_k$.

Proof. Let $q_k(r)$ and $C_k(r)$ be the $J_p$ masses of return within
$k$ reads and of correct return within $k$ reads when the initial
state is $r$. Independence and the fact that the seed has no later
runtime role give the finite sums

$$
q_k=\sum_{r\in K}\omega_r q_k(r),\qquad
q_k-L_k=\sum_{r\in K}\omega_r C_k(r),\qquad
\sum_{r\in K}\omega_r=1.
\tag{8.4}
$$

Since $0\le q_k(r)\le1$, the first equality forces $q_k(r)=1$
whenever $\omega_r>0$. For each such deterministic start the
inherited unrestricted bound applies, so $C_k(r)\le S_k$.
The second equality, whose left side is $S_k$, forces equality in
each positive-weight term. This uses only a finite measurable
partition of the given seed space, with no atomlessness or extra
randomness premise. $\square$

**Proposition 8.3 (All one-read attaining starts).** Fix any installed
table and deterministic initial state $r$ with $q_1(r)=1$. Its correct
mass is $S_1$ if and only if it starts with $\operatorname{Read}(t)$
whose active phase $\alpha=t\bmod2$ and active edge
$e=\{\ell,\ell+1\}$, $t=2\ell+\alpha$, satisfy
$v_\alpha\notin e$, and its reply-zero and reply-one successors
halt with labels $h_{1-\alpha}(\sigma)$ and $h_\alpha(\sigma)$,
respectively. Both successors have positive source probability.
Consequently every such start visits at least one read state and two
distinct halt states with positive source probability.

Proof. An initial halt has correct mass at most $a/2<S_1$.
For every integer first address both reply sections are positive:
their masses are $1-\eta$ and $\eta$. Thus $q_1(r)=1$ forces
each successor to be a halt; a further read would exclude that entire
positive section from $E_1$.

Put $\beta=1-\alpha$. On reply zero the phase-$\beta$ majority
state has mass $a/2$. The largest phase-$\alpha$ state mass is
$a^2/2$ if $v_\alpha\in e$, and $ac/2$ otherwise, by Lemma 3.1.
Both are strictly below $a/2$. Since $b<a$, the unique maximizing
zero-reply label is $h_\beta(\sigma)$.
On reply one only phase $\alpha$ remains. Its maximal state mass is
$\eta/2$ if $v_\alpha\in e$ and $a\eta$ otherwise.
The former is strictly smaller because $a>1/2$; in the latter case
the unique maximizer is $h_\alpha(\sigma)$, since $a>b$.
Hence equality at $S_1$ holds exactly as asserted. The two phase
label sets are disjoint, so their halt states differ from one another
and from the read state. $\square$

**Proposition 8.4 (All two-read attaining starts and their forced labels).**
Fix any installed table and deterministic initial state $r$ with
$q_2(r)=1$. Its correct mass is $S_2$ if and only if its execution
from $r$ has the following form. It reads $t=2\ell+\alpha$ first,
then reads $t_0$ or $t_1$ according to the first reply, and then halts.
Writing $\beta=1-\alpha$ and $e=\{\ell,\ell+1\}$, the exact
geometric conditions are:

1. $v_\alpha\in e$.
2. $t_0$ has parity $\alpha$ and its active edge $f$ is
   vertex-disjoint from $e$.
3. $t_1$ has parity $\alpha$ and its active edge $g$ shares exactly
   one vertex with $e$.

The required terminal labels, with replies in acquisition order, are

$$
\begin{array}{c|c}
\text{reply pair}&\text{unique maximizing label}\\ \hline
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
\tag{8.5}
$$

Every leaf has positive source probability. The three read states
have distinct actual addresses, and the terminal labels include the
three distinct states $h_\beta(\sigma)$, $h_\alpha(\sigma)$ and
$h_\alpha(1-\sigma)$. Thus every attaining start visits at least
three read states and three halt states with positive source probability.

Proof. We analyze the actual instructions from $r$, without replacing
them by padded or risk-dominating representatives. An initial halt has
correct mass at most $a/2<S_2$. The first instruction must therefore
read some actual integer $t$. Both first-reply sections have positive
mass. On either section, a successor is either a halt or a second
read. After a second read, every positive-mass leaf must have a halt
successor, since any third read there violates $q_2(r)=1$.

Let $D_x$ be the actual correct mass on first reply $x$, including
all its subsequent returning leaves. For a second read after reply
one, Lemma 4.1 gives $D_1\le a\eta$; if it instead halts,
Lemma 3.1 gives the same bound. If the zero successor halts then
$D_0\le a/2$, by the zero-section calculation in Proposition 8.3.
It would follow that $D_0+D_1\le S_1<S_2$. Hence the zero
successor must read $t_0$.

For this actual zero subtree, Lemmas 4.2--4.3 give

$$
D_0\le B_0\le \frac a2+a^2\eta,
\qquad D_1\le a\eta.
\tag{8.6}
$$

Equality of the total at $S_2$ forces equality in both bounds and
in every intervening leaf maximum. Opposite parity for $t_0$ loses
at least $\eta c/2>0$, by (4.9). At the same parity the $00$
maximum is $a/2$, and the possibilities for the $01$ maximum in
Lemma 4.2 are exhaustive. A repeat gives zero; an adjacent edge
gives $a\eta/2<a^2\eta$. For disjoint edges with the target in
$f$, the maximum is $c\eta/2<a^2\eta$, since $c<2a^2$.
If the target is in neither edge it is $ac\eta<a^2\eta$,
since $c<a$. Therefore $D_0=a/2+a^2\eta$ forces precisely
conditions 1 and 2, using the strict inequalities of (3.1).

Now the first edge contains $v_\alpha$. Halting on first reply
one gives at most $\eta/2<a\eta$, so that successor must read
$t_1$. The exhaustive table in Lemma 4.1 shows that a separator,
a repeated first edge, or a vertex-disjoint edge gives only
$\eta/2$ on this subtree. Thus $D_1=a\eta$ forces exactly
condition 3. This argument allows every integer address and either
first parity. The fuller tables in
[FixedSeed, Lemmas 2.4--2.5 and Theorems 3.2--3.3](FIB_TWO_PAID_READ_FIXED_SEED_FRONTIER_AND_SUPPORT_INVISIBILITY.md)
give the same source geometry; their representative policies are not
being used as state-preserving transformations.

It remains to identify the outputs and check sufficiency on that same
source. Under conditions 1--3 the leaf source masses and best correct
masses are

$$
\begin{array}{c|c|c}
\text{reply pair}&J_p(C_{xy})&m(C_{xy})\\ \hline
00&(1+c^2)/2&a/2\\
01&\eta c&a^2\eta\\
10&\eta/2&a\eta/2\\
11&\eta/2&a\eta/2
\end{array}
\tag{8.7}
$$

Indeed $00$ contains all of phase $\beta$ and, in phase $\alpha$,
two disjoint zero edges. The phase-$\alpha$ largest target-state
mass there is $a^2c/2<a/2$, whereas the phase-$\beta$ majority
state has mass $a/2>b/2$. Thus its unique maximizer is
$h_\beta(\sigma)$. The $01$ leaf certifies phase $\alpha$;
its two target-state masses are $a^2\eta$ and $b^2\eta$, so
its unique maximizer is $h_\alpha(\sigma)$. These statements use
the actual target $S_{v_\alpha}$, not a target transported from the
other phase.

For $10$ and $11$, the two adjacent edge constraints leave the
complementary three-spin assignments of (3.2), whose masses are
$a^2b$ and $ab^2$. Their majority assignments give exactly
$(s_0,s_1)$ in (8.5), whether $g$ is left or right of $e$.
To see the distinction directly, on $10$ the two spins of the
zero edge $g$ are the majority spin and the remaining vertex is
the minority spin. On $11$ the shared vertex is the minority spin
and the two outer vertices are the majority spin. Since the target
belongs to $e$, its two maximizing values are opposite. The phase
factor $1/2$ proves the last two rows of (8.7); $a>b$ makes each
maximizer unique. All four source masses are positive.

Consequently (8.5) is necessary for equality. Conversely, conditions
1--3 with those labels give correct mass equal to the sum of the
last column of (8.7), namely $S_2$, and return after exactly two
reads. Finally $e,f,g$ are pairwise different: $f$ is disjoint from
$e$, while $g$ is adjacent to $e$. Thus $t,t_0,t_1$ are three
distinct address literals. A fixed instruction state cannot carry
two of these literals. The three distinct output labels require
three distinct halt states, disjoint from the read states by (8.1).
Each required state is reached on a positive source section.
$\square$

**Theorem 8.5 (Exact installed state costs for the inherited optima).**
For every original $0<p<1$, $p\ne1/2$, either fixed original
$j\in\{0,1\}$ and every given unchanged independent seed law,
the minima of Definition 8.1 are

$$
M_1(p,j,\nu)=3,\qquad M_2(p,j,\nu)=6.
\tag{8.8}
$$

The lower bounds hold over every attaining table of Definition 8.1,
including tables with cycles, unused rows, early-return options and
arbitrary measurable seed initialization. They require, respectively,
at least one read and two halt states, and at least three read and
three halt states. The matching tables below attain the original
unrestricted optima, with one and two actual reads on every path.

Proof. There is at least one initialization cell of positive measure.
For every such cell, Lemma 8.2 and Propositions 8.3--8.4 give the
stated numbers of distinct states in the installed $K$. Counting
unused rows cannot reduce those lower bounds. In particular this
argument bounds every attainer, rather than counting only a chosen
construction or a representative of its risk.

For the one-read upper bound take three distinct states
$R,Z,P$, initialize constantly at $R$, and install

$$
\begin{array}{c|c|cc}
\text{state}&\text{instruction}&\delta(\cdot,0)&\delta(\cdot,1)\\ \hline
R&\operatorname{Read}(2(j+2))&Z&P\\
Z&\operatorname{Halt}(h_1(\sigma))&-&-\\
P&\operatorname{Halt}(h_0(\sigma))&-&-
\end{array}
\tag{8.9}
$$

The dash means that no successor is used at a halt. This is exactly
Original, Theorem 11.4's one-call attainer, with its halting labels
included in $K$. Its actual zero/one correct masses are $a/2$ and
$a\eta$, so it attains $S_1$. The address is a phase-zero edge
disjoint from $S_j$ for either allowed $j$; in phase one it is a
charged separator.

For the two-read upper bound take six distinct states
$R,R_0,R_1,Z,P,Q$, initialize constantly at $R$, and install

$$
\begin{array}{c|c|cc}
\text{state}&\text{instruction}&\delta(\cdot,0)&\delta(\cdot,1)\\ \hline
R&\operatorname{Read}(2j)&R_0&R_1\\
R_0&\operatorname{Read}(2(j+2))&Z&P\\
R_1&\operatorname{Read}(2(j+1))&Q&P\\
Z&\operatorname{Halt}(h_1(\sigma))&-&-\\
P&\operatorname{Halt}(h_0(\sigma))&-&-\\
Q&\operatorname{Halt}(h_0(1-\sigma))&-&-
\end{array}
\tag{8.10}
$$

These are the actual calls and outputs of Definition 5.1, with all
runtime phases and output distinctions included in the six rows.
Proposition 5.2 gives their correct masses $a/2,a^2\eta,
a\eta/2,a\eta/2$ under the original $J_p$, hence correctness
$S_2$. Neither table uses the seed after its constant initialization,
so both constructions work on every given auxiliary space without
changing its law. They need no phase observation or other acquisition
beside their charged calls. Every binary reply path ends at a halt.
This proves both upper bounds and (8.8).

The source-relative additional conclusions are the equality rigidity
of Propositions 8.3--8.4 and the all-attainers installed-state minimum
(8.8), derived here from the owning endpoint bounds. The unrestricted
risk values and the actual-source attainers retain their ownership in
Original, Risk and Sections 5--6; the fuller two-read geometry remains
credited to FixedSeed, Sections 2--4. Generic complete-state semantics
and finite-memory controller background retain the citations in
Definition 8.1. These are `repo-derived` endpoint-memory conclusions,
with no global-priority claim. Finite representative existence and
[address compression, Sections 4--6](FIB_FINITE_PAID_READ_ADDRESS_COMPRESSION_AND_SIGNATURE_RADIUS.md)
are not state-minimality premises. The result compares a legal subclass
attaining an inherited unrestricted optimum; it does not replace that
unrestricted protocol comparison or extend (8.8) to a different runtime
interface. $\square$

## 追加锚（本行以下为增补区）
