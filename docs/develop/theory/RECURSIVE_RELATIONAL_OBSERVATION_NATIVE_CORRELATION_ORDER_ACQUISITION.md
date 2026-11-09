# Native correlation order and optimal mean acquisition

## 1. The stationary native task and its law interface

**Definition 1.1 (one persistent source and globally correct acquisition).**
Use [AAR, Definitions 1.1, 1.3–1.4 and 13.1–13.2][AAR]. A source is a
finite nonempty ordered full binary tree with leaves $\alpha,\beta$.
Its height is zero at a leaf and one plus the maximum child height at
a branch. Fix public $D\ge1$ and a word $p$ beginning with $R$, with
$1\le |p|\le D$. The source family is exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:\operatorname{height}(v)\le D\}.
\tag{NCO.1}
$$

One unknown $t\in\mathcal F_D$ is sampled once from a public law and
remains stationary throughout acquisition. Every finite original-root
word $w$ is a legal Read, returning one of
$\{\alpha,\beta,\mathsf b,\bot\}$: the two leaf labels, branch and
absent. The empty word reads the root; every strict extension of a leaf
is absent. In particular $\bot$ is not an alpha label. There is no
source identity, subtree operation, free navigation or additional port.

An admissible encoder is a deterministic effective procedure with
source-blind initialization, terminating and correct on every member of
the whole family (NCO.1). Its complete accessible source dependence at
handoff, denoted $E_A(t)$, includes any surviving operands, selectors,
reply latches, histories, control and allocation distinctions. One
passive decoder must, without further Reads, satisfy

$$
\mathsf D_A(E_A(t),D,p,k)=\operatorname{Read}_{\rho^k t}(p)
\quad(t\in\mathcal F_D,\ k\in\mathbb N),
\tag{NCO.2}
$$

where the supplied $k$ is authentic for this same source and initial
version, and

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{NCO.3}
$$

Only the number $T_A(t)$ of actual initial Read invocations is optimized;
constant, repeated, absent and off-path invocations all count. Write

$$
V_{D,p}(\mu)=\inf_A\mathbb E_\mu T_A.
\tag{NCO.4}
$$

The competitor class in this infimum is the same for every law on
$\mathcal F_D$. Public laws can inform installation, but installation
reveals no sampled source. Local computation, memory, complete operand
lengths, installation, clearing, validation of stationarity and
authentication and representation of $k$ are separate resources.

Let $p_j$ denote the length-$j$ prefix of $p$. The published boundary
descriptor $d=\partial_p(t)$ is $B$ if $p$ is branch, and otherwise
$(j,e)$ if the first leaf on its path is at $p_j$, with label
$\lambda_e$, where $\lambda_0=\alpha$ and $\lambda_1=\beta$.
This descriptor is a mathematical function, not a supplied input.

**Definition 1.2 (conditional native observation order).** For laws on
the same family and task, write $\mu_0\equiv_r^\partial\mu_1$ when
their $d$ laws agree and, for every attained $d$, every $1\le q\le r$
and every ordered tuple of arbitrary finite words $(w_1,\ldots,w_q)$,

$$
\mathcal L_{\mu_0}\bigl((\operatorname{Read}_t(w_i))_{i=1}^q\mid d\bigr)
=\mathcal L_{\mu_1}\bigl((\operatorname{Read}_t(w_i))_{i=1}^q\mid d\bigr).
\tag{NCO.5}
$$

Repeated and nested words are allowed. Equivalently, the joint laws of
$(d,\operatorname{Read}_t(w_1),\ldots,\operatorname{Read}_t(w_q))$
agree for every $0\le q\le r$, with $q=0$ denoting the boundary law.
Indeed multiplication by the common descriptor mass gives the joint
law, and division by a positive common descriptor mass gives (NCO.5).

**Theorem 1.3 (no uniform finite correlation-order sufficiency).** For
every finite integer $r\ge1$ there exist admissible $D,p$ and rational
laws $\mu_0,\mu_1$, strictly positive on every source in the unchanged
family $\mathcal F_D$, such that

$$
\mu_0\equiv_r^\partial\mu_1,
\qquad V_{D,p}(\mu_0)<V_{D,p}(\mu_1).
\tag{NCO.6}
$$

The construction in §2 and the all-competitor bounds in §3 prove this
statement. Both laws use exactly the same $D,p$, family, four-reply
operation and correctness domain. They can even have the same entire
hint-bank marginal before full-support completion. The asserted price
gap is between optimized infima; no exact optimum is asserted.

Proof. Choose the parameters and laws of Definitions 2.1–2.2 for the
given $r$. Theorem 2.3 realizes them on actual sources of (NCO.1) and
proves the native all-word conditional equalities. Theorem 2.4 with
$\epsilon=1/100$ makes both laws rational and strictly positive on the
entire same family while preserving those equalities. Theorems
3.1–3.3 give an admissible upper strategy and a lower bound uniform
over every admissible competitor, with positive difference (NCO.25).
These are precisely the two assertions of (NCO.6). $\square$

## 2. Finite algebra inside actual native trees

**Definition 2.1 (parameters and the public coset locator).** Fix $r\ge1$
and put

$$
\begin{aligned}
m&=\min\{s\ge1:3^s\ge8r\},& a&=rm,& M&=8r,\\
C&=Mm=8a,& N&=3^{7a},& n&=N+1,\\
D&=n,& p&=R^n,& \ell&=\lceil\log_2 C\rceil.
\end{aligned}
\tag{NCO.7}
$$

In particular $m\ge2$ and $a\ge2$. Take a field $F$ of cardinality
$Q=3^m$, a public ordered $\mathbb F_3$ basis, and distinct public
points $\xi_1,\ldots,\xi_M\in F$. There are enough points since
$Q\ge M$. All choices are finite and effective.

For completeness, the standard finite-field existence argument can
be expressed without a choice of an infinite table. In a splitting
field over $\mathbb F_3$, the roots of $X^{3^m}-X$ are distinct, since
its derivative is $-1$. They are closed under addition, multiplication,
negation and nonzero inversion by the Frobenius identities. They form
a field of exactly $3^m$ elements, hence have $\mathbb F_3$ dimension
$m$. An effective presentation may be found by enumerating addition
and multiplication tables on $3^m$ labelled elements and testing the
finite field axioms and characteristic three; existence makes that
search terminate. A basis is then found by finite linear algebra.
This establishes effectivity, without asserting affordable installation.

For $z\in F^M$, let $I_z$ be the unique polynomial of degree less than
$r$ satisfying $I_z(\xi_i)=z_i$ for $i\le r$, and define

$$
H(z)=\bigl(z_i-I_z(\xi_i)\bigr)_{i=r+1}^{M}\in F^{M-r}.
\tag{NCO.8}
$$

The map $H$ is linear and onto: put the first $r$ entries of $z$ equal
to zero and prescribe its remaining entries. Its kernel consists of
the degree-less-than-$r$ evaluation vectors, and each fiber has $Q^r$
elements. Since

$$
|F^{M-r}|=3^{m(8r-r)}=3^{7a}=N,
\tag{NCO.9}
$$

fix a public bijection $\iota:\{2,\ldots,n\}\to F^{M-r}$. For example,
expand $j-2$ in $7a$ ternary digits and group them according to the
chosen basis.

This interpolation and masking mechanism is classical, as in
[Shamir, §2][SHA] and [Christiani–Pagh, §2.1, Lemma 1][CP], which
credits Joffe and Carter–Wegman. Its coset interpretation is also the
method of [Ozarow–Wyner, §2][OW]. The native geometry and prices below
are additional obligations; a field element is not a native reply.

**Definition 2.2 (native cells, sources and core laws).** Encode one
ternary digit by an actual tree

$$
G(0)=\alpha,\qquad G(1)=\beta,\qquad
G(2)=\langle\alpha,\alpha\rangle.
\tag{NCO.10}
$$

Expand $z\in F^M$ in the public basis into $C$ ternary digits. Build
a complete binary skeleton of depth $\ell$, put these $C$ cells in
the first $C$ bottom slots in lexicographic order, and put alpha in
the remaining slots. Call this tree $\mathsf{Bank}(z)$. A cell-root
Read returns respectively $\alpha,\beta,\mathsf b$. Reading one whole
field coordinate requires $m$ such native calls. There is no tuple
reply or additional symbol.

Define

$$
\mathsf{Comb}_0(u)=u,\qquad
\mathsf{Comb}_{h+1}(u)=\langle\alpha,\mathsf{Comb}_h(u)\rangle,
\tag{NCO.11}
$$

and, for $2\le j\le n$, $e\in\{0,1\}$ and $z\in F^M$, set

$$
t_{j,e,z}=
\left\langle\alpha,
 \left\langle\mathsf{Bank}(z),\mathsf{Comb}_{j-2}(\lambda_e)
 \right\rangle\right\rangle.
\tag{NCO.12}
$$

Thus the bank is at $RL$, and the first leaf on the target ray is at
$R^j$. Define two actual-source laws, zero on other trees, by

$$
P_0(t_{j,e,z})=
\frac{\mathbf1\{H(z)=\iota(j)\}}{2NQ^r},
\qquad
P_1(t_{j,e,z})=\frac1{2NQ^M}.
\tag{NCO.13}
$$

Equivalently, both first choose $j,e$ uniformly. The first chooses $z$
uniformly on $H^{-1}(\iota(j))$; the second chooses $z$ independently
uniformly on $F^M$. These choices prepare a single actual tree. Every
later reply is its deterministic native reply, including replies at
cell descendants and at words not used by the upper strategy.

**Theorem 2.3 (actual-source realization and all-word equality).** The
sources (NCO.12) lie in $\mathcal F_D$, the displayed laws are rational
probability laws, and

$$
\partial_p(t_{j,e,z})=(j,e),\qquad
P_0\equiv_r^\partial P_1.
\tag{NCO.14}
$$

Both core laws also give $z$ the uniform law on $F^M$.

Proof. A bank has height at most $\ell+1$. The right subtree of
(NCO.12) consequently has height at most

$$
\max\{\ell+2,j-1\}\le D.
\tag{NCO.15}
$$

For the last inequality, $\ell\le C-1$ for every integer $C\ge2$,
and $C=8a\le3^{7a}=N$. The latter follows already at $a=1$, and
persists under increment because multiplication by $3^7$ exceeds the
required linear increment. Hence $\ell+2\le C+1\le N+1=D$.
The outer left child is exactly alpha. Along the right ray all proper
ancestors of $R^j$ are branches, and the leaf at $R^j$ is
$\lambda_e$. This proves the descriptor assertion. Distinct triples
$(j,e,z)$ give distinct trees: the descriptor identifies $j,e$ and the
cell-root replies identify all digits of $z$. Each $H$ fiber has $Q^r$
elements, so (NCO.13) has total mass one. Summing $P_0$ over $j,e$
assigns each $z$ mass $1/(NQ^r)=1/Q^M$; the same holds for $P_1$.

Here is the low-order projection argument in its exact finite form.
For any $s\in F^{M-r}$, a uniform element of $H^{-1}(s)$ is

$$
z_i=f(\xi_i)+b_i,
\qquad
b_i=\begin{cases}0,&i\le r,\\s_{i-r},&i>r,\end{cases}
\tag{NCO.16}
$$

where the $r$ coefficients of $f$ are independent uniform field
elements. For any $q\le r$ distinct points, their evaluation map
from these coefficients has rank $q$: its first $q$ columns have
Vandermonde determinant
$\prod_{u<v}(\xi_v-\xi_u)\ne0$.
Every prescribed $q$-tuple therefore has exactly $Q^{r-q}$ coefficient
preimages. Translation by $b$ preserves this uniform distribution.
Thus every at-most-$r$ coordinate projection of each coset is uniform,
just as for uniform $F^M$. In orthogonal-array terminology the coset
table has strength $r$ and index one on $r$ columns. This is the
standard polynomial-array mechanism, used here as an intermediate step.

To lift it to every native word, classify words on (NCO.12) by their
first left edge. The following cases exhaust all finite words:

| Word | Actual reply on $t_{j,e,z}$ |
| --- | --- |
| $\varepsilon$ or $R$ | $\mathsf b$ |
| $L$; $Lu$ with $u\ne\varepsilon$ | respectively $\alpha$; $\bot$ |
| $RLu$ | a fixed skeleton/padding reply, or a function of one bank digit |
| $R^i$, $i\ge2$ | $\mathsf b$ if $i<j$; $\lambda_e$ if $i=j$; $\bot$ if $i>j$ |
| $R^iLu$, $i\ge2$, $u=\varepsilon$ | $\alpha$ if $i<j$; $\bot$ otherwise |
| $R^iLu$, $i\ge2$, $u\ne\varepsilon$ | $\bot$ |

Within the bank, a strict skeleton ancestor is always branch. A padded
slot is alpha and every strict extension is absent. At a variable slot
the root returns its digit's constructor. Either one-edge continuation
returns alpha exactly when that digit is $2$, and otherwise absent;
every continuation of length at least two is absent. A literal follows
one path and cannot visit two incomparable cells. These statements also
cover words longer than the whole tree's height.

Condition on $d=(j,e)$. All nonbank replies in the table are fixed.
Any tuple of $q\le r$ arbitrary words depends on at most $q$ bank
digits, hence on at most $q$ field coordinates. Their joint field
projection is identical under both laws by (NCO.16); taking the
specified deterministic reply functions preserves equality. Multiple
digits from one field coordinate, repeated words, nested words, and
cell-root/child pairs are all included in this pushforward argument.
It uses no independence assertion between repeated coordinates. Both
descriptor laws give mass $1/(2N)$ to each $(j,e)$ in their support,
so (NCO.14) follows. $\square$

**Theorem 2.4 (exact rational full-support completion).** Let $U_D$ be
uniform on the entire family $\mathcal F_D$. For any rational
$0<\epsilon<1$, put

$$
\mu_i^{\epsilon}=(1-\epsilon)P_i+\epsilon U_D
\quad(i=0,1).
\tag{NCO.17}
$$

These are rational full-support laws and
$\mu_0^{\epsilon}\equiv_r^\partial\mu_1^{\epsilon}$, including every
descriptor outside the core support.

Proof. The number $b_h$ of labelled trees of height at most $h$ obeys
$b_0=2$, $b_{h+1}=2+b_h^2$. The two summands distinguish leaves
from ordered pairs of height-at-most-$h$ trees. Thus
$|\mathcal F_D|=b_D<\infty$ and
$\mu_i^{\epsilon}(t)\ge\epsilon/b_D>0$ for every actual source.
All probabilities are rational.

For any fixed word tuple and reply event $G$, Theorem 2.3 gives equality
of the unnormalized probabilities $P_i(d,G)$ and of $P_i(d)$.
Adding the identical $\epsilon U_D$ contribution preserves both
equalities. Division by the resulting common positive descriptor mass
proves conditional equality. Explicitly, if $b=P_0(d)=P_1(d)>0$, then

$$
\mu_i^{\epsilon}(G\mid d)=
\frac{(1-\epsilon)bP_i(G\mid d)+\epsilon U_D(d,G)}
     {(1-\epsilon)b+\epsilon U_D(d)}.
\tag{NCO.18}
$$

If $b=0$, only the common $U_D$ component contributes. This includes
first-position leaves and $B$, as well as all noncore shapes. The
mixture is a law on actual sources sampled once, not a per-query
mixture of replies. $\square$

## 3. Global correctness and separation against every strategy

**Theorem 3.1 (legal locating strategy and uniform fallback).** There
is one encoder $A_*$, admissible on all of $\mathcal F_D$, such that

$$
T_{A_*}=C+1\text{ on the support of }P_0,
\qquad
T_{A_*}\le C+1+h_n\text{ on }\mathcal F_D,
\quad h_n=\lceil\log_2(n+1)\rceil.
\tag{NCO.19}
$$

Proof. Actually Read the $C$ public cell-root words at $RL$ followed
by their skeleton slots, in a fixed order. If any reply is absent, use
the fallback below. Otherwise interpret alpha, beta and branch as
$0,1,2$, assemble $z$, compute $j_*=\iota^{-1}(H(z))$, and actually
Read $R^{j_*}$. Return $(j_*,e)$ only if this Read is a labelled leaf.
If it is branch or absent, use the fallback.

The locating relation alone is never accepted as evidence. On an
arbitrary tree in $\mathcal F_D$, a labelled reply at $R^{j_*}$ proves
that all its strict ancestors are branches and that this is precisely
the first leaf on the target path. Thus every direct return acquires
the genuine descriptor, even if the tree has a different bank shape,
invalid cell descendants, or no relation to either core law.

The fallback is [AAR, Theorem 13.4][AAR]. Search the ordered leaf
positions $[1,n]$ at the lower middle index $i$. A Read of $R^i$ is
a hit if labelled, keeps the earlier positions if absent, and keeps
the later positions if branch. Exhaustion of the leaf candidates can
leave only the branch descriptor $B$. Each nonterminal comparison
leaves at most half the previous leaf candidates, so at most
$h_n$ actual calls suffice. This is a new search on the same stationary
tree; any repeated call from the locating phase still counts. It
terminates correctly on every source of the full family.

For clarity the passive decoder for this all-right target has the
following explicit form. At descriptor $B$ it always returns branch.
At $(j,e)$ put $x=k+e-2(n-j)$, as an integer, and return

$$
\begin{cases}
\bot,&x<0,\\
\alpha,&x=0,\\
\beta,&x=1,\\
\mathsf b,&x\ge2.
\end{cases}
\tag{NCO.20}
$$

This is AAR13.3 specialized to the right ray. In the native source
algebra, an originally present leaf at $R^j$ transports to
$\rho^{k+e}\alpha$ at that same address, by
[`original_present_transport`][NDP]. The existing
[`right_clock_iterate` and `right_clock_readout`][DOR], with
$s=n-j$ and initial clock $e$, give exactly (NCO.20).
An initially present branch persists under the homomorphism.
Transport is used only at an originally present address; it never
turns an initial absent node into an alpha leaf.

One complete handoff includes the acquired descriptor together with
the whole remaining accessible acquisition state. The decoder uses
its descriptor component. Alternatively, separately charged clearing
can leave only a fixed encoding of that descriptor. Neither convention
discards accessible source dependence from the accounting. No further
source Read is needed for any supplied authentic $k$.

On $P_0$, the actual bank gives $H(z)=\iota(j)$ and the validation
Read hits the genuine leaf. There are exactly $C+1$ calls. On any
source there are at most $C$ cell calls, one candidate call and $h_n$
fallback calls. This proves (NCO.19) and full-family correctness.
$\square$

**Theorem 3.2 (persistent-source all-word lower bound).** Every
admissible encoder $A$, with any allowed public installation, satisfies

$$
\mathbb E_{P_1}T_A\ge L_a,
\qquad
L_a=10a-\frac{2^{10a}-1-10a}{N}>10a-1.
\tag{NCO.21}
$$

Proof. First, on each $t_{j,e,z}$ the encoder must actually Read
$R^j$ before stopping. Flip only its leaf label. The resulting tree
is $t_{j,1-e,z}$ in the same full family, with unchanged height,
outer left alpha and every reply except at $R^j$. A deterministic run
omitting that address has identical queries, local decisions,
termination and complete handoff on both trees. At the common
authentic count $k=2(n-j)$, formula (NCO.20) requires respectively
alpha and beta. This contradicts (NCO.2). This is exactly the
bounded-family actual-leaf evidence mechanism of AAR13.5 and
[SLH, Lemma 43.2][SLH]; it remains necessary even when the initial
target reply is absent.

Now condition under $P_1$ on a complete fixed bank vector $z$ and a
label $e$. The position $j$ is still uniform on $N$ possible values.
This is a probability decomposition for the lower proof, not advice
given to the executing encoder. Every reply during each execution
continues to come from its one actual $t_{j,e,z}$.

Consider arbitrary adaptive query histories up to the first Read of
the actual $R^j$. The all-word table in Theorem 2.3 implies that, on
any subset of still-unhit positions, a query has the following form:
a right-prefix word can hit at most one position and leaves at most
two nonhit reply groups; a later left-sibling word has at most two
threshold reply groups and no hit; a bank word or outer constant has
one reply group once $z,e$ are fixed. Arbitrarily long words, nested
words, repeated words and absent replies are included in these cases.

Let $K_q$ be a uniform upper bound on the number of candidate positions
that any such adaptive continuation can first hit within $q$ further
charged calls. A history fixes the next word, because all local state
is determined by that history and the common installation. Cutting
off a position when it is first hit gives

$$
K_0=0,\qquad K_q\le1+2K_{q-1},\qquad K_q\le2^q-1.
\tag{NCO.22}
$$

The recurrence holds on any remaining subset, so no assumption that
the encoder itself maintains intervals is needed. Constant queries
have only one continuation; threshold queries have no added hit.
Halting before a required hit is forbidden by the first paragraph.
Source-free local computation adds no reply group. This proves the
bound for every permitted adaptive word strategy, rather than just
prefix-search strategies.

If $\tau$ is the charged time of the compulsory first hit, then
$T_A\ge\tau$ and, for all $q\ge0$,

$$
\Pr_{P_1}(T_A\le q\mid z,e)
\le\Pr_{P_1}(\tau\le q\mid z,e)
\le\min\left\{1,\frac{2^q-1}{N}\right\}.
\tag{NCO.23}
$$

Since $3^7=2187>1024=2^{10}$, we have $N=3^{7a}>2^{10a}$.
The elementary integer tail sum, truncated at $10a$, yields

$$
\begin{aligned}
\mathbb E_{P_1}(T_A\mid z,e)
&\ge\sum_{q=0}^{10a-1}\left(1-\frac{2^q-1}{N}\right)\\
&=10a-\frac{2^{10a}-1-10a}{N}=L_a>10a-1.
\end{aligned}
\tag{NCO.24}
$$

This bound is uniform in the fixed $z,e$ and in $A$. Averaging over
their actual joint law proves (NCO.21). The lower argument neither
projects the source to a different tree nor draws a fresh bank for a
later query. $\square$

**Theorem 3.3 (optimized gap after common full support).** With the
parameters of §2 and $\mu_i=\mu_i^{1/100}$, the following separated
upper and lower bounds hold:

$$
\begin{aligned}
V_{D,p}(\mu_0)&\le8a+1+\frac{h_n}{100}
                  \le8a+1+\frac{14a}{100},\\
V_{D,p}(\mu_1)&\ge\frac{99}{100}L_a
                  \ge\frac{99}{100}(10a-1),\\
V_{D,p}(\mu_1)-V_{D,p}(\mu_0)
 &\ge\frac{176a-199}{100}\ge\frac{153}{100}>0.
\end{aligned}
\tag{NCO.25}
$$

Proof. The one globally correct strategy of Theorem 3.1 gives
$V(\mu_0)\le C+1+h_n/100$. For every admissible $A$, nonnegativity
of its $U_D$ cost and Theorem 3.2 give
$\mathbb E_{\mu_1}T_A\ge(99/100)L_a$. This bound is uniform before
taking the infimum over the same competitor class.

To bound the fallback, $3^{7a}+2\le2^{14a}$ for $a\ge1$. Indeed
$4^{7a}-3^{7a}\ge4^7-3^7>2$, and that difference increases with
$a$. Hence $h_n=\lceil\log_2(3^{7a}+2)\rceil\le14a$.
Subtracting the upper bound from the lower one gives
$(176a-199)/100$, whose minimum for $a\ge2$ is $153/100$.
Together with Theorem 2.4 this proves Theorem 1.3.

More generally, the same common completion obeys

$$
V(\mu_1^{\epsilon})-V(\mu_0^{\epsilon})
\ge L_a-(C+1)-\epsilon(L_a+h_n).
\tag{NCO.26}
$$

Thus every rational
$0<\epsilon<(L_a-C-1)/(L_a+h_n)$ preserves a strictly positive
gap and all exact conditional equalities. The numerator is positive
because $L_a>10a-1$ and $C+1=8a+1$, with $a\ge2$.
This is stability under the stated common full-support completion,
not under arbitrary separate perturbations of the laws. Neither this
argument nor the displayed bounds identifies either exact optimum.
$\square$

**Proposition 3.4 (the first order is included).** For $r=1$ the
parameters are $m=2$, $a=2$, $M=8$, $C=16$, $N=3^{14}$,
$D=n=3^{14}+1$ and $p=R^n$. One may take
$F=\mathbb F_3[X]/(X^2+1)$. In particular,

$$
V(\mu_0)\le\frac{1728}{100},\qquad
V(\mu_1)\ge\frac{1881}{100}.
\tag{NCO.27}
$$

Proof. The polynomial $X^2+1$ has no root in $\mathbb F_3$ and is
irreducible of degree two. Substitute $a=2$ in (NCO.25).
The bound uses $h_n\le28$ and is not an exact-value computation.
The proof for general $r$ uses the same argument with larger fields
and families; it is not inferred from this first-order case.
$\square$

## 4. Bounded experiments, stopping and fixed-family saturation

**Theorem 4.1 (exact bounded adaptive-history equivalence).** For two
persistent source laws on a common finite native family,
$\mu_0\equiv_r^\partial\mu_1$ implies the following: every fixed common
deterministic installed protocol has identical joint law with $d$ of
its acquisition history through $r$ Reads. This includes earlier
stopping, the final output on an earlier stop, the still-running flag,
next chosen operand and all local state determined by the history.
Equivalently, conditional history laws agree for every attained $d$.

Conversely, equality of these joint bounded-experiment laws for every
common protocol implies $\mu_0\equiv_r^\partial\mu_1$. In particular,
for every fixed admissible encoder $A$,

$$
\Pr_{\mu_0}(T_A\le q)=\Pr_{\mu_1}(T_A\le q)\quad(0\le q\le r),
\qquad
\mathbb E_{\mu_0}\min(T_A,r+1)
=\mathbb E_{\mu_1}\min(T_A,r+1).
\tag{NCO.28}
$$

Proof. Fix a control-consistent history
$h=((w_1,y_1),\ldots,(w_q,y_q))$ with $q\le r$. Once its earlier
replies are specified, the deterministic protocol's words and local
decisions along this path are fixed. Its event is exactly the
single-source cylinder

$$
\bigcap_{i=1}^q\{t:\operatorname{Read}_t(w_i)=y_i\}.
\tag{NCO.29}
$$

Control-inconsistent paths have probability zero under either law.
Each consistent cylinder has equal joint probability with every $d$
by Definition 1.2. There are at most four reply continuations per
Read, hence finitely many paths up to depth $r$, despite the unbounded
word vocabulary. Stopping, the next operand, retained data and any
specified finite source-free processing of a path are deterministic
functions of that path and the common installation. They therefore
have the same joint distributions as well. For admissible encoders,
termination on every source excludes an infinite local computation
on an attained path. A stopped transcript can be padded by a fixed
stop marker to express all these distributions on one carrier.

The converse uses a protocol that nonadaptively Reads any requested
tuple, together with the zero-Read experiment for the $d$ marginal.
Repeated and nested words are allowed in both directions. Finally,
the event $T_A>q$ is decided after the first $q$ replies and subsequent
source-free control, and
$\mathbb E\min(T_A,r+1)=\sum_{q=0}^r\Pr(T_A>q)$.
This proves (NCO.28).

This is the finite cylinder argument for a random function sampled
once, in the language of [Maurer, Definitions 2–3 and Lemma 4][MAU].
The input here is a native word and the output is its deterministic
reply on one tree. No simulator redraws nuisance variables; all
conjuncts in (NCO.29) refer to the same $t$. $\square$

**Proposition 4.2 (what bounded equality does not optimize).** If a
common class of admissible encoders always stops within $r$ Reads,
its optimized mean Read price is the same under
$\mu_0\equiv_r^\partial\mu_1$. Equality also holds for the infimum
of $\mathbb E\min(T_A,r+1)$ over any common class. It need not hold
for the uncapped objective (NCO.4).

Proof. Apply Theorem 4.1 to each fixed encoder, then take the infimum
of the equal quantities over the identical class. Public laws may
lead to different choices of installed encoder, but do not alter this
pointwise-in-program comparison or the common class. For uncapped
cost the omitted tail terms involve cylinders of higher order. In
Theorem 1.3 those tails yield strictly different infima; its useful
locating record has $C+1>r$ Reads. Thus no equality at arbitrary
length follows by optimizing the bounded comparison. $\square$

**Theorem 4.3 (a sufficient saturation order on a fixed family).** Fix
$D,p$. The finite response vector indexed by

$$
W_D=\{Ru:u\text{ is a word with }|u|\le D\},
\qquad |W_D|=2^{D+1}-1,
\tag{NCO.30}
$$

uniquely determines $t\in\mathcal F_D$. Consequently, if
$r\ge2^{D+1}-1$ and $\mu_0\equiv_r^\partial\mu_1$, then
$\mu_0=\mu_1$. All strategy cost distributions and their optimized
means are then equal. The stated order is sufficient, without a
minimality assertion.

Proof. The entries include every possible node of the right subtree
through its height cap, and give every branch, labelled leaf and
absence. Recursively reconstruct $v$ from these replies. The outer
root and left child are fixed, strict descendants of that left leaf
are absent, and all $R$-leading words longer than $D+1$ are absent.
Thus the response map is injective. Apply (NCO.5) to the entire tuple
$W_D$ and combine with the common $d$ law. Equality of its law implies
equality of the law of the uniquely recovered source. The remaining
assertions follow by evaluating each deterministic encoder on that
source. Therefore agreement at every order on one fixed $\mathcal F_D$
cannot give a price gap. Theorem 1.3 varies $D,p$ with $r$ and has a
different quantifier order. $\square$

**Proposition 4.4 (the one-letter target degeneracy).** For every
$D\ge1$ and $p=R$, $V_{D,R}(\mu)=1$ for every source law under the
global-correctness contract.

Proof. Read $R$ once. Its label or branch descriptor suffices for all
supplied counts by AAR13.3. An encoder stopping without any Read
would have the same complete state on every source, since its
initialization and local work are source-blind. The family contains
sources whose initial $R$ replies are alpha and beta, contradicting
correctness at $k=0$. Hence every admissible encoder makes at least
one Read on every source. This includes $D=1$, for which $R$ is the
only admissible target. $\square$

## 5. Recovery content, attribution and mathematical limits

**Proposition 5.1 (passive prediction and acquisition-side choice).**
For the paired laws of Theorem 1.3 the random complete target future
trajectory has the same distribution. Every fixed bounded experiment
through order $r$, including its joint law with that trajectory, has
the same distribution. These equalities coexist with the distinct
optimal acquisition prices in (NCO.25).

Proof. AAR13.3 factors the complete future through $d$; for the present
right-ray task this is (NCO.20). Push forward the common $d$ law for
the first assertion and the joint law in Theorem 4.1 for the second.
The third assertion is Theorem 3.3. The operational difference is that
an acquired higher-order bank relation can select the address of a
subsequent genuine leaf-evidence Read. Under $P_0$, $H(z)$ identifies
$j$; under $P_1$, $j$ remains independent of the whole bank. The
actual target evidence and full-family fallback are required under
both laws. $\square$

**Definition 5.2 (the recovery and resource boundary of this result).**
The recovered quantities are the genuinely acquired descriptor, its
task-specific predictive factor, and the target's replies at authentic
supplied counts. A full response-vector law is sufficient on each
fixed finite family, by Theorem 4.3. Theorem 1.3 excludes a uniform
finite-order substitute for that law across all such families when
the consumer is optimal mean acquisition.

Passive prediction, finite experimental statistics, acquisition-side
action selection and complete accessible memory are distinct
interfaces here. Exploiting $H(z)$ requires acquired joint data and
local computation; it is not furnished by its low-order marginal
tables. The strategy in §3 may retain its whole acquired record.
If only a descriptor is retained, every other accessible distinction
must be cleared with its separate resource cost. No minimum-memory
theorem follows from its Read bound.

The constructed target and some literal operands are extremely long.
No total-efficiency, affordable-installation, short-operand or physical
clock claim follows. The public count $k$ is not recovered from the
record. Recovering physical spacetime, arbitrary undeclared targets,
the complete source, erased history, or all operation permissions is
outside this theorem. The wider programme of mutual recovery between
relations, spatial structure, time, boundaries and memory retains
these additional obligations. Minimal $D$, adjacent-order strictness
on one fixed task, exact $V$, and a minimum sufficient law interface
for a specified task are not identified by the present bounds.

**Mathematical citation 5.3 (supplier correspondence and content status).**
The native correlation-order/acquisition bridge and its cost conclusion
are ordinary `repo-derived` deductions. They are not Lean verification
or a claim of worldwide originality. The load-bearing source
correspondences are:

| Supplier | Exact use and boundary |
| --- | --- |
| [AAR §§12–13][AAR], particularly AAR13.1–13.5 | The unchanged stationary family, complete handoff, descriptor factor, globally correct balanced fallback, and bounded-family actual-label necessity. Retained-alphabet and worst-case results are not mean-price comparisons. |
| AAR14.1–14.2 | The normalization compares $c_B(t)$ with $c_A(\pi_p(t))$, not $c_A(t)$. Pointwise nondomination alone gives no optimized mean gap. The fixed-bank argument (NCO.21) supplies an actual-law lower bound instead. |
| AAR15–16, especially AAR16.2–16.4 | Evidence, full-family canonical completions and joint-menu all-word geometry retain their stated tasks. Their projected-source and worst-resource comparisons do not preserve an arbitrary actual prior. The altered bank-family geometry is proved in Theorem 2.3. |
| [SLH §§35–38 and 43][SLH] | First-leaf future semantics and label-flip evidence. The closure of our bounded family under that flip is checked in Theorem 3.2. |
| [`Source`, `substitution`][GFT]; [`Reply`, `readout`, `flip`, `source_foundation`][READ] and [their Blueprint supplier][READB] | Boolean leaves encode alpha as true and beta as false; address false means $L$, true means $R$. Readout is address-first and has four replies. The formal module's positive-image task and distinct-address `paid` cost differ from (NCO.2) and actual invocation count. Its optimization results are not imported. |
| [`original_present_transport`][NDP] and [its Blueprint supplier][NDPB]; [`right_clock_iterate`, `right_clock_readout`][DOR] and [their Blueprint supplier][DORB] | Same-source transport only at present addresses, and the exact right-ray interval table used in (NCO.20). No subtree oracle or originally absent transport premise is supplied. |
| [Shamir §2][SHA]; [Christiani–Pagh §2.1, Lemma 1][CP]; [Ozarow–Wyner §2][OW] | Classical interpolation privacy, limited independence and coset encoding. Equation (NCO.16) gives the needed finite projection counts directly. Neither a whole field share nor several tree replies become one native call. No asymptotic wiretap bound is used. |
| [Maurer, Definitions 2–3 and Lemma 4][MAU] | Random-function and adaptive-invocation framework; (NCO.29) proves the bounded native correspondence, including stopping, directly. No fresh-source simulation is allowed. |
| [Cicalese–Laber–Saettler, §1][CLS] | Finite objects are sources, classes are target future trajectories, tests are native reply functions, and each invocation has unit cost. Their decision-tree/expected-cost framework is background; its approximation results do not provide the native first-hit bound. |

These source versions are the published repository at
`2cbcc2b15d3ba4b9a5cb4de1bed62edcf6e8849c` and the linked primary
papers. The orthogonal-array interpretation used above follows from
the explicit Vandermonde projection proof. [Bush's original
orthogonal-array paper][BUSH] is a bibliographic antecedent; no
parameter theorem from it is needed. No numerical or asymptotic
wiretap bound is transferred. The cited methods do not themselves establish
native realizability, all-word equality or the global acquisition gap.
Those are supplied here by (NCO.12)–(NCO.26). This identifies the
substantive addition without an exhaustive-literature claim or a claim
that the wider programme is complete.

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[GFT]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[READ]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[READB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs
[NDP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[NDPB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[DORB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.scribe.cs
[SHA]: https://web.mit.edu/6.857/OldStuff/Fall03/ref/Shamir-HowToShareASecret.pdf
[CP]: https://arxiv.org/pdf/1408.2157v1
[OW]: https://link.springer.com/content/pdf/10.1007/3-540-39757-4_5.pdf
[MAU]: https://crypto.ethz.ch/publications/files/Maurer02.pdf
[CLS]: https://proceedings.mlr.press/v32/cicalese14.pdf
[BUSH]: https://doi.org/10.1214/aoms/1177729387

## 追加锚（本行以下为增补区）

## 6. Actual-source normalization on short targets

**Definition 6.1 (prefix cells and conditional continuations).** Keep
exactly Definition 1.1, including the whole family $\mathcal F_D$,
stationarity, every finite original-root word as a legal competing
Read, and correctness for every authentic later $k$. Write $n=|p|$.
A nonterminal prefix history $H$ is a finite truthful history of Reads
of $p_i$, $1\le i\le n$, containing only absent replies and branch
replies at proper prefixes $i<n$. Let

$$
\begin{aligned}
\mathcal C_H&=\{t\in\mathcal F_D:t\text{ gives every reply in }H\},\\
a&=1+\max\bigl(\{i:(p_i,\mathsf b)\in H\}\cup\{0\}\bigr),\\
b&=\min\bigl(\{i:(p_i,\bot)\in H\}\cup\{n+1\}\bigr)-1.
\end{aligned}
\tag{NCO.31}
$$

Only feasible histories, $\mathcal C_H\ne\varnothing$, are considered.
Their unresolved leaf positions are exactly $[a,b]$. The outcome $B$
is possible exactly when $b=n$, equivalently when $H$ has no absent
reply. The cell includes every matching source, even a source with
zero mass under the public law.

A conditional continuation starts from one fixed effective local state
on all of $\mathcal C_H$, terminates on every member, and, together with
its passive decoder, meets (NCO.2) on this entire cell. Its additional
Read count is denoted $R(t)$. In particular, an encoder's continuation
after the complete acquired history $H$ has this form. A fixed state
is not allowed to vary with an unobserved source. The definition also
allows a fixed state obtained by computing an earlier encoder's
response to a reply already forced throughout $\mathcal C_H$.

A prefix continuation searches the remaining ordered keys $a,\ldots,b$.
At key $i$ it actually Reads the full literal $p_i$ on the same $t$.
Either leaf label terminates with $(i,e)$; absence selects the lower
keys; branch selects the upper keys, with branch at $p_n$ terminating
with $B$. Every remaining key occurs once in its ordered binary search
tree. Such a continuation acquires the genuine descriptor. Its existing
passive decoder is [AAR13.3, (AAR.76) and (AAR.59)][AAR], for arbitrary
$R$-leading $p$, including left-ending words.

**Lemma 6.2 (pointwise comparison on an acquired small residual).**
For every $D\ge1$, $R$-leading $p$ with $1\le n\le D$, feasible
nonterminal prefix history $H$ with $1\le b-a+1\le3$, and conditional
continuation as in Definition 6.1, there is a deterministic effective
prefix continuation $S_H$, fixed independently of $t\in\mathcal C_H$,
such that

$$
 R_{S_H}(t)\le R(t)\qquad(t\in\mathcal C_H).
\tag{NCO.32}
$$

The comparison counts actual further invocations only. It requires no
law, no supplied off-path record and no restriction of correctness to
a prior's support.

Proof. First check the cell and the evidence obligation. A branch reply
at $p_i$ says the first leaf lies strictly after $i$, or the outcome is
$B$; absence says the first leaf lies strictly before $i$ and excludes
$B$. Their intersection gives (NCO.31). Every indicated position and
both labels are feasible: make its proper ancestors branches, put the
chosen leaf there, and fill unused siblings with alpha. The outer left
leaf stays alpha. The right subtree then has height at most $n-1$.
When $b=n$, making $p$ branch with two alpha children instead gives a
$B$ completion of right-subtree height $n\le D$. Thus $a\le b$, and
no additional candidate is removed by the height promise or the labels.

The actual-label and branch-certificate argument of AAR13.5 applies on
this whole cell, with the following closure checks. Flip the first leaf
at any unresolved $p_j$. The height, shape, outer alpha and every reply
in $H$ are unchanged; the competitor lies in $\mathcal C_H$. Its replies
at all words except exactly $p_j$ agree with those of the original
source. The two labels have different future trajectories by AAR13.3:
if $j=n$ they differ at count zero; otherwise, writing $p=p_jr$ and
$s(r)=\#_L(r)+2\#_R(r)$, at the common authentic count $s(r)+1$
one gives beta and the other branch.
Consequently every correct continuation must actually Read $p_j$.
Collisions between the predictive factors of different positions,
including the left-ending collision in AAR13.3, do not remove this
within-position necessity.

For a $B$ source, prune its subtree at $p$ to alpha. All of $H$ consists
of proper-prefix branch replies in this case, so pruning preserves $H$
and decreases height. If no further Read returns branch at $p$ or a
nonabsent reply at a strict descendant of $p$, every further reply is
preserved by pruning as well. Determinism from the common fixed state
would yield the same termination and complete decoder input, although
the required replies at count zero are branch and alpha. This is
impossible. Here evidence means the actual chronological calls, even
if their records are subsequently cleared; no persistence of a separate
transcript is assumed.

Neither kind of evidence is in $H$. In particular $R(t)\ge1$ everywhere.
If $w$ is the first further word, a one-call completion is possible
only when $w=p_j$ is the actual unresolved leaf address, when $w=p_n$
returns branch, or when $w$ strictly extends $p$ and returns nonabsent
on a $B$ source. An absent descendant reply is never a branch
certificate. This classification concerns every finite word: a word
outside the target prefixes and strict descendants cannot be either
required witness. Known or repeated prefixes, the root, the left-root
cone, divergent siblings and arbitrarily long absent words are thereby
included. It is not a bound on the competing word vocabulary.

With one position, query it. Its label, or branch at $p_n$ if $B$ is
possible, finishes in one call and meets $R(t)\ge1$.

With two positions $a<c$, inspect $w$. If $w=p_a$, use the order $a,c$.
The later leaf and any $B$ source cannot finish after that first proper
prefix, and the chosen order costs two there. If $w\ne p_a$, use the
order $c,a$. It costs one on the leaf at $c$ and on $B$ when possible,
and two on the leaf at $a$. That last source lacks its required first
call at $p_a$, so $R(t)\ge2$ there. These two orders prove (NCO.32),
including strict-descendant first queries and $B$ sources where such
a query returns absent.

Now let the three positions be $a<c<z$. The middle-first tree queries
$c$, then $a$ on absence and $z$ on branch. Its costs on the three leaf
positions are $(2,1,2)$, and its $B$ cost, when present, is two. It
therefore suffices if $w=p_c$. It also suffices if $w$ cannot give any
one-call completion, since then $R(t)\ge2$ everywhere.

Suppose $w=p_a$. On the sources with later leaves or $B$, this first
reply is the common branch reply. The continuation cannot yet stop;
let $u$ be its fixed next word after this reply and its intervening
local computation. If $u=p_c$, use the order $a,c,z$. Its costs are
$(1,2,3)$, with $B$ cost three. On the sources assigned cost three,
neither $p_z$ nor a branch certificate has appeared in the first two
competing calls, so $R(t)\ge3$. If $u\ne p_c$, use the tree rooted at
$a$, followed by $z$, and then $c$ on absence at $z$. Its leaf costs
are $(1,3,2)$ and its $B$ cost is two. The leaf at $c$, the sole
cost-three outcome, has not been read in the first two competing
calls. Every other noninitial outcome needs at least two. Both choices
therefore dominate pointwise, regardless of what $u$ returns elsewhere.

Suppose $w=p_z$. The sources with leaves at $a,c$ give the common absent
reply. Let $u$ be the next word from that fixed continuation state. Query
$z$ first in the replacement, then $a$ before $c$ if $u=p_a$, and $c$
before $a$ otherwise. The earlier leaf assigned cost three is precisely
one whose compulsory address is missing from the competing first two
calls; the other earlier leaf needs at least two. The leaf at $z$, and
$B$ when possible, cost one in the replacement. This proves the claim
in this case.

The remaining first word capable of one-call completion is a strict
descendant of $p$, with $B$ possible and hence $z=n$. Query $p_z$ first
in the replacement. It terminates in one call on $B$ and on the leaf
at $z$, even on $B$ sources where the competing descendant reply was
absent. On both earlier leaf positions the competing descendant reply
is always absent. Inspect its fixed next word $u$ after that reply and
use exactly the preceding $a$-versus-$c$ rule. The earlier leaf assigned
cost three still lacks its actual address after the two competing
calls. This completes all first-word cases.

Every inspected continuation state occurs on a nonempty full cell or
on the stated common-reply subcell. Totality makes its next Read
computable in finite local time; the evidence obligation forbids an
earlier stop on the subcell used for inspection. Only the resulting
finite query choices are installed. Their selection depends on $H$
and the continuation program, never on a sampled source or off-path
value. Each comparison concerns the same $t$ throughout. Extraction,
local computation, installation and memory are separate costs. $\square$

**Theorem 6.3 (same-source pointwise and two-encoder normalization).**
For every integer $D\ge1$, every $R$-leading $p$ with
$1\le n=|p|\le\min(D,4)$, and every admissible arbitrary-word encoder
$A$ of Definition 1.1, there are two deterministic effective prefix
encoders $S_1,S_2$, admissible on that identical whole family for the
same all-authentic-$k$ passive task, such that

$$
 T_{S_1}(t)+T_{S_2}(t)\le2T_A(t)
 \qquad(t\in\mathcal F_D).
\tag{NCO.33}
$$

They depend on $A,D,p$, not on the sampled $t$ or a sampled-source
identifier. For $n\le3$ they can be identical, giving one deterministic
pointwise dominator. At $n=4$ deterministic pointwise domination in
general is false, as in AAR14.2; (NCO.33) preserves that counterexample.

Proof. For $n\le3$, apply Lemma 6.2 with empty $H$ and the source-blind
initial state of $A$. For $n=4$, $A$ cannot stop before its first Read:
a source-independent zero-call state cannot distinguish the two labels
at the first leaf. Inspect the fixed first word $w$.

If $w=p_i$ is a target prefix, actually Read that same prefix. A leaf
reply acquires its descriptor; branch at $p_4$ acquires $B$. Stop there,
with at most $A$'s call count. Every nonterminal reply defines an actual
prefix history $H$ of one call. Its leaf interval has at most three
positions, and $A$'s continuation state is fixed on all of $\mathcal C_H$.
Attach the prefix continuation of Lemma 6.2 at that reply. This gives
one pointwise prefix dominator on every actual source, so use it twice.

If $w$ strictly extends $p$, actually Read $p=p_4$ instead. Its leaf
or branch reply is terminal evidence in one call. On its absent reply,
the actual cell is

$$
 \mathcal C_{[(p,\bot)]}
 =\{t:\partial_p(t)=(j,e),\ 1\le j\le3\}.
\tag{NCO.34}
$$

The original $\operatorname{Read}_t(w)$ equals absent on every member
of this entire cell. Compute $A$'s fixed continuation state after that
forced reply; no source Read of $w$ is made by the replacement. This
continuation is total and correct on the cell, since it is $A$'s
actual post-first-call state on each of its members. Apply Lemma 6.2
using the genuinely acquired prefix history $[(p,\bot)]$. The total
replacement count is at most $1+(T_A(t)-1)=T_A(t)$ on the cell.
This is a fixed-state reduction on the same actual sources; it does
not apply the lemma to an off-path history or obtain a new receipt
for an unperformed Read. Again take both encoders to be this one.

Every other first word lacks a possible one-call certificate, by the
classification in Lemma 6.2 with empty $H$. Hence $T_A(t)\ge2$ on every
source of $\mathcal F_D$. Take the following two fixed prefix trees:

- $S_1$ queries $p_2$, then $p_1$ on absence or $p_4$ on branch;
  after absence at $p_4$ it queries $p_3$.
- $S_2$ queries $p_3$, then $p_1$ on absence or $p_4$ on branch;
  after branch at $p_1$ it queries $p_2$.

Every leaf reply terminates, and branch at $p_4$ terminates with $B$.
Their costs, independent of label and off-path shape, are

$$
\begin{array}{c|ccccc}
\text{outcome}&j=1&j=2&j=3&j=4&B\\\hline
T_{S_1}&2&1&3&2&2\\
T_{S_2}&2&3&1&2&2\\
(T_{S_1}+T_{S_2})/2&2&2&2&2&2.
\end{array}
\tag{NCO.35}
$$

Thus their average count is at most $T_A(t)$ for each same $t$.
These are two deterministic programs; the average is an inequality,
not an executing coin flip. The preceding cases complete the universal
proof for all finite competing words and all $D\ge n$.

Every replacement actually acquires a labelled first leaf or branch
at $p$. It may retain its whole accessible acquisition record, with
its retention cost, or retain the descriptor or its existing predictive
factor after paying to clear all other accessible source dependence.
AAR13.3 then supplies the one passive decoder for every authentic
same-source, same-initial-version $k$. No $\rho$ action occurs during
acquisition, and no later Read or inferred clock is used. $\square$

## 7. The attained actual-law mean as a consumer

**Theorem 7.1 (exact short-target mean and a sufficient law interface).**
Fix $D\ge1$, $R$-leading $p$, and $1\le n=|p|\le\min(D,4)$ as in
Theorem 6.3. Let $\mathcal S_n$ be the finite family of all ordered
prefix search trees on keys $1,\ldots,n$, with leaf-label termination
and the terminal $B$ outcome. For every probability law $\mu$ on the
whole unchanged $\mathcal F_D$,

$$
 V_{D,p}(\mu)=\min_{S\in\mathcal S_n}\mathbb E_\mu T_S.
\tag{NCO.36}
$$

The infimum in (NCO.4) is attained by an admissible deterministic
encoder. In particular, this remains true for arbitrary zero-prior
worlds, on which the attaining encoder must still be correct.

For an exact expression, put

$$
\begin{aligned}
q_0&=1,&q_i&=\mu\{t:\operatorname{Read}_t(p_i)=\mathsf b\},\\
x_i&=q_{i-1}-q_i\quad(1\le i<n),&x_n&=q_{n-1}.
\end{aligned}
\tag{NCO.37}
$$

These are actual-law probabilities, not observations supplied to the
encoder. Define the finite interval recurrence

$$
\begin{aligned}
F(a,b)&=0&&\text{if }a>b,\\
F(a,b)&=\sum_{j=a}^b x_j+
 \min_{a\le i\le b}\bigl(F(a,i-1)+F(i+1,b)\bigr)
 &&\text{if }a\le b.
\end{aligned}
\tag{NCO.38}
$$

Then the exact value is $V_{D,p}(\mu)=F(1,n)$. Thus the ancestor branch
masses $q_1,\ldots,q_{n-1}$ suffice for the optimized mean; the complete
source law, its leaf-label split and its off-path correlations are not
needed for this value on the stated short tasks. No minimality of this
law interface is asserted.

Proof. Integrate (NCO.33) under the one actual law $\mu$. At least one
of its two deterministic prefix encoders has mean at most that of the
arbitrary admissible $A$. Therefore the finite prefix minimum is at
most every competing mean and hence at most their infimum. Conversely
every member of $\mathcal S_n$ is an admissible whole-family encoder,
by actual descriptor acquisition and AAR13.3. Its finite minimum is
therefore at least the unrestricted infimum. This proves (NCO.36) and
attainment. The argument averages costs, without installing randomness.

The branch events along the prefixes are nested. The first leaf is at
$i$ exactly when $p_{i-1}$ is branch and $p_i$ is not branch; for $i=1$
the root is the known branch. Its mass, summed over both labels, is
$q_{i-1}-q_i$. The mass of $B$ is $q_n$. In every prefix search tree
the last leaf position $n$ and $B$ follow exactly the same strict
ancestor queries and both terminate at $p_n$. Their call costs agree,
so their masses combine to
$(q_{n-1}-q_n)+q_n=q_{n-1}=x_n$. All other keys have masses $x_i$.
In particular $x_i\ge0$ and $\sum_i x_i=1$.

At the root key $i$ of any subtree on $[a,b]$, every outcome in that
interval pays one additional call. The lower and upper intervals
then use disjoint subtrees. Minimizing those finite choices proves
(NCO.38) by induction on interval length. This is the ordinary ordered
search-tree cost calculation, used here only after Theorem 6.3 has
justified its application to the original all-word mean problem.
For example it gives the following short expressions:

$$
\begin{aligned}
n=1:\quad V&=1,\\
n=2:\quad V&=1+\min\{q_1,1-q_1\},\\
n=3:\quad V&=\min\{1+q_1+q_2,\ 1+2q_1-q_2,\ 2-q_1+q_2,\\
 &\hspace{46mm}2+q_1-2q_2,\ 3-q_1-q_2\}.
\end{aligned}
\tag{NCO.39}
$$

For $n=4$, (NCO.38) with
$(x_1,x_2,x_3,x_4)=(1-q_1,q_1-q_2,q_2-q_3,q_3)$ is an exact
four-key expression. These expressions and ancestor-mass sufficiency
are consumers of the new same-source comparison, rather than separate
novel search formulas. The case $n=1$ is also Proposition 4.4.

A finite minimizer exists even for a noncomputable law. Each candidate
is an effective finite installed program, but a uniform effective map
from arbitrary real prior parameters to an optimal program is not
provided. Exact rational input masses permit finite exact comparison;
representation, comparison, extraction and installation costs remain
separate. Sampling a source does not furnish those prior masses.
$\square$

**Corollary 7.2 (the necessary length boundary for a descriptor-law gap).**
For the same $D,p$ and the unchanged correctness family of Definition
1.1, two laws with the same descriptor distribution but different
optimized means must have $|p|\ge5$. This applies in particular to the
common-descriptor-law comparisons of Definition 1.2. It asserts no
existence of a gap at length five and no mean normalization for any
length at least five.

Proof. Equal descriptor laws give equal ancestor masses in (NCO.37).
If $|p|\le4$, Theorem 7.1 gives equal exact means, a contradiction.
Equality only of the compressed future-trajectory law is a different
hypothesis: AAR13.3 permits descriptor collisions, and no conclusion
under that weaker hypothesis is used here. $\square$

**Definition 7.3 (resource and recovery scope of the comparison).**
Only actual initial Read invocation count is dominated in (NCO.32)–
(NCO.36). Every submitted word is the full original-root literal on
one stationary actual source. For each resulting prefix tree there
are at most $n$ calls, peak literal length at most $n$, and total
submitted letters at most $n(n+1)/2$; these are its own bounds, not
pointwise domination of $A$'s letter or peak-address costs.

Operand addresses and letters, reply storage, installed literals and
controller extraction or selection, law representation and arithmetic,
local computation, output and decoder computation remain charged.
The stationarity promise supplies no validation service; any separately
required stationarity validation and the authentication, representation
and validation of the later $k$ retain their costs and hypotheses.
Complete accessible memory includes surviving operands, reply latches,
histories, selectors, control, capacities and allocation distinctions.
Retain each such source dependence at its actual cost or pay to clear
or retract it before a descriptor-only handoff in a fixed output
region. Resident source storage and retained inaccessible or dead
backing remain physical costs even when absent from the exported
interface. No minimum-memory or simultaneous resource optimum follows.

The theorems supply neither source projection nor fresh-source
sampling, rerooting, free navigation, a new randomizer, a pre-acquired
row, a source-identity port, an acquisition or invocation permission,
or recovery of an unknown clock. The acquired descriptor and its
existing native decoder serve the declared target at every authentic
supplied count. Recovering the complete original response $Q$, an
original $S$-to-$C$ or cross-source bridge, undeclared later targets,
full-source structure and the full mutual recovery of structure,
continuation, boundaries and memory remain additional obligations.
Theorems 1.3, 3.3 and 4.3 retain their quantifiers, and AAR14.2 retains
its deterministic pointwise obstruction at length four. Theorem 7.1
resolves the exact-mean boundary in Definition 5.2 only on its stated
short-target slice.

**Mathematical citation 7.4 (source correspondence and evidence).**
Lemma 6.2 and Theorem 6.3 are ordinary `repo-derived` deductions from
the unchanged native family and evidence obligations. AAR13.3 supplies
the existing passive decoder and within-position label separation;
AAR13.5 supplies actual-leaf and branch-certificate necessity, with
conditional-cell closure proved above. AAR13.4 supplies the admissible
prefix-search form. AAR14.1 and AAR16.4 concern projected sources and
worst resources; neither is used as an actual-law comparison.
AAR14.2 is the retained counterexample to stronger pointwise domination.
These owning sources are read at repository base
`92ebb4bf99a02f9804996167f5f07a3fcabd7a2f`.

The finite expected-cost decision-tree framework is mature; see
[Cicalese–Laber–Saettler, §1][CLS]. Its variables are native reply
functions of the same tree, its output class is the target future
trajectory, and each invocation has unit cost here. The elementary
ordered-tree recurrence is an intermediate calculation in the consumer
Theorem 7.1; no approximation theorem of that paper supplies Lemma 6.2
or the two-encoder inequality. No worldwide originality claim is made.
Existing Lean source cited in Mathematical citation 5.3 supplies the
native carrier, four-reply Read and substitution correspondence only.
The new results are ordinary proofs, with no new Lean check or kernel
verification claimed; a bounded finite calculation alone would not
establish their arbitrary-word or arbitrary-$D$ quantifiers.

## 追加锚（本行以下为增补区）
