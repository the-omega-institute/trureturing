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

## 8. Exact classification of descriptor-law acquisition sufficiency

**Definition 8.1 (five weighted positions on any longer target).**
Retain precisely Definition 1.1. Fix any $D\ge n=|p|\ge5$, with $p$
beginning with $R$, and let

$$
a=p_1\overline{p[2]},\qquad
(w_1,w_2,w_3,w_4,w_5)=(5,3,2,3,5).
\tag{NCO.40}
$$

Here $a$ is the length-two sibling of $p_2$, in the same original-root
address system; the bar exchanges $L,R$. Use the canonical context
$C_u[v]$ of AAR13.6: strict ancestors of $u$ are branches, $v$ is
installed at $u$, and every unused sibling is alpha. For $1\le j\le5$
and $e\in\{0,1\}$ define canonical sources
$c_{j,e}=C_{p_j}[\lambda_e]$. Define guided sources $g_{j,e}$ by leaving
$c_{1,e}$ unchanged and, for $j\ge2$, replacing just its existing
subtree at $a$ according to

$$
\begin{array}{c|ccccc}
j&1&2&3&4&5\\\hline
\text{subtree at }a&\text{absent}&\alpha&\alpha&\beta&
                                      \langle\alpha,\alpha\rangle\\
\operatorname{Read}_{g_{j,e}}(a)&\bot&\alpha&\alpha&\beta&\mathsf b.
\end{array}
\tag{NCO.41}
$$

The first entry prescribes no replacement: $R$ is itself a leaf there.
Let $P_{\rm c},P_{\rm g}$ be zero off their respective displayed
ten-source sets, with

$$
P_{\rm c}(c_{j,e})=P_{\rm g}(g_{j,e})=\frac{w_j}{36}.
\tag{NCO.42}
$$

These are rational probability laws on the identical full family
$\mathcal F_D$. Within each set its ten sources are distinct, since
their descriptors are distinct. The two sets may overlap. For every
displayed pair,

$$
\partial_p(c_{j,e})=\partial_p(g_{j,e})=(j,e).
\tag{NCO.43}
$$

Indeed no replacement lies on the target path. The canonical
right-subtree height is $j-1$, and the only new branch subtree is at
the sibling $a$ of depth two. Thus every displayed right-subtree
height is at most $\max\{j-1,2\}\le4\le D$. This verifies the native
realization for every orientation of $p$, including mixed and
left-ending words, without padding or a change of source family.
Both core descriptor laws give $(j,e)$ mass $w_j/36$ for $j\le5$
and all other descriptors mass zero.

**Lemma 8.2 (the weighted canonical lower bound against every word).**
For every admissible encoder $A$ of Definition 1.1, with arbitrary
finite original-root Read words,

$$
\mathbb E_{P_{\rm c}}T_A\ge\frac{20}{9}.
\tag{NCO.44}
$$

The same lower bound holds for every prefix-only encoder under
$P_{\rm g}$.

Proof. AAR14.1 supplies a correct prefix encoder $S$ with
$T_S(t)\le T_A(\pi_p(t))$. Each canonical $c_{j,e}$ is a fixed point
of that projection. Consequently
$T_S(c_{j,e})\le T_A(c_{j,e})$ on exactly the sources being averaged
under $P_{\rm c}$. No such comparison with an unprojected guided
source is asserted.

Use AAR14.1's ordered pruning of prefix encoders. Each retained query
is a key $i$; its two label replies terminate, absence goes to smaller
keys and branch to larger keys, with $B$ terminating at key $n$.
This pruning remains justified for zero-prior positions, because
correctness is on all of $\mathcal F_D$. In particular the actual
label at each first leaf is compulsory by AAR13.5. For arbitrary
orientations, AAR13.3 distinguishes its two labels at a common
authentic supplied count; collisions between different positions'
predictive factors do not remove that necessity.

For the lower calculation, delete keys $6,\ldots,n$ from the ordered
tree. At a deleted key, every retained key in its subtree lies in
its lower subtree. Splice that lower subtree upwards and discard the
upper part, which has no retained key. This leaves an ordered tree on $1,\ldots,5$
without increasing any of their depths. Write $d_j$ for its key
depths, starting at one. Both labels at key $j$ have that same depth.

The elementary weighted ordered-tree recurrence already used in
Theorem 7.1 gives the following exact finite calculation. Let $F(a,b)$
be the minimum unnormalized cost on keys $a,\ldots,b$ with weights
$w_j$, and set $F(a,b)=0$ when $a>b$. Then

$$
F(a,b)=\sum_{j=a}^b w_j+
       \min_{a\le i\le b}\{F(a,i-1)+F(i+1,b)\}.
\tag{NCO.45}
$$

The interval values, listed from left to right at each length, are

$$
\begin{array}{c|l}
\text{interval length}&F\text{ values}\\\hline
1&5,\ 3,\ 2,\ 3,\ 5\\
2&11,\ 7,\ 7,\ 11\\
3&17,\ 14,\ 17\\
4&25,\ 25\\
5&40.
\end{array}
\tag{NCO.46}
$$

For example the final minimization is
$18+\min\{25,5+17,11+11,17+5,25\}=40$.
Thus $\sum_jw_jd_j\ge40$, and averaging the two labels gives
$\mathbb E_{P_{\rm c}}T_A\ge40/18=20/9$.

For the last assertion begin instead with any prefix-only encoder.
Its pruned tree depends only on prefix replies, hence its cost on
$c_{j,e}$ and $g_{j,e}$ is the same. The same calculation therefore
gives its $P_{\rm g}$ mean at least $20/9$. This assertion uses
descriptor equality for prefix programs, not pointwise domination of
arbitrary-word programs on guided sources. $\square$

**Proposition 8.3 (one globally correct guided acquisition).**
For the same arbitrary $D,p$, there is a deterministic effective encoder
$A_{\rm g}$, correct and terminating on every $t\in\mathcal F_D$, with

$$
\begin{aligned}
(T_{A_{\rm g}}(g_{1,e}),\ldots,T_{A_{\rm g}}(g_{5,e}))
   &=(2,2,3,2,2),\\
\mathbb E_{P_{\rm g}}T_{A_{\rm g}}&=\frac{19}{9},\\
T_{A_{\rm g}}(t)&\le h+3,\qquad
h=\lceil\log_2(n+1)\rceil.
\end{aligned}
\tag{NCO.47}
$$

Proof. First actually Read the full literal $a$. Select candidate
prefix queries from its actual reply as follows:

| Acquired reply at $a$ | Candidate query sequence |
| --- | --- |
| $\bot$ | $p_1$ |
| $\alpha$ | $p_2$; if its reply is branch, then $p_3$ |
| $\beta$ | $p_4$ |
| $\mathsf b$ | $p_5$ |

At every candidate query $p_i$, return $(i,e)$ only on an actual
labelled leaf reply $\lambda_e$. Return $B$ only on an actual branch
reply at $p_i=p_n$. If these tests have not returned a descriptor
after the stated sequence, run the balanced prefix encoder of
AAR13.4 on this same stationary source. It uses at most $h$ further
Read invocations and always acquires the genuine descriptor. The
fallback may repeat an earlier query; that invocation still counts.

Each direct return has real evidence independently of the guide's
truthfulness: an actually labelled $p_i$ certifies all its strict
ancestors as branches, and a branch reply at $p_n$ certifies $B$.
A branch at any proper prefix, including a misleading $p_5$ when
$n>5$, is not accepted as a terminal certificate. The reply at $a$
only selects a literal; its label is never substituted for an
unread target-path label. On arbitrary sources even a reply
inconsistent with the core relation therefore either leads to
genuine evidence or to the total full-family fallback.

On $g_{1,e}$ the first reply is absent and the second query hits
$p_1$. On $g_{2,e}$ it is alpha and $p_2$ hits. On $g_{3,e}$ it is
alpha, $p_2$ returns branch and $p_3$ hits. On $g_{4,e}$ it is beta
and $p_4$ hits; on $g_{5,e}$ it is branch and $p_5$ hits.
These are the five costs in (NCO.47), with weighted numerator
$5\cdot2+3\cdot2+2\cdot3+3\cdot2+5\cdot2=38$.
There is one guide call, at most two candidate calls, and at most
$h$ fallback calls on any source, proving the uniform bound.

Retain the actual acquired descriptor together with the complete
remaining accessible acquisition state, or pay separately to clear
everything except a fixed descriptor encoding. AAR13.3 supplies the
single passive decoder for every authentic same-source,
same-initial-version $k$. Its suffix-dependent formula applies to the
original $p$, including when the acquired leaf is a proper prefix
and the initial reply at $p$ is absent. No substitution is performed
during acquisition and no later source call is used. $\square$

**Theorem 8.4 (rational full-support separation for every longer target).**
For every integer $D\ge n\ge5$ and every length-$n$ word $p$ beginning
with $R$, define $P_{\rm c},P_{\rm g}$ by (NCO.40)–(NCO.42). Let $U_D$
be uniform on the entire original $\mathcal F_D$, and put

$$
\epsilon=\frac{1}{2(9h+19)},\qquad
\mu_{\rm c}=(1-\epsilon)P_{\rm c}+\epsilon U_D,\qquad
\mu_{\rm g}=(1-\epsilon)P_{\rm g}+\epsilon U_D.
\tag{NCO.48}
$$

These two explicit rational laws are strictly positive at every source
of that same family and have the same complete descriptor distribution.
Their unrestricted optimized means satisfy

$$
\begin{aligned}
V_{D,p}(\mu_{\rm c})
   &\ge(1-\epsilon)\frac{20}{9}+\epsilon,\\
V_{D,p}(\mu_{\rm g})
   &\le\mathbb E_{\mu_{\rm g}}T_{A_{\rm g}}
     \le(1-\epsilon)\frac{19}{9}+\epsilon(h+3),\\
V_{D,p}(\mu_{\rm c})-V_{D,p}(\mu_{\rm g})
   &\ge\frac1{18}>0.
\end{aligned}
\tag{NCO.49}
$$

Write $V^{\rm pref}_{D,p}(\mu)$ for the infimum over admissible
prefix-only encoders, with precisely the same whole-family correctness
requirement. The guided law also satisfies

$$
V^{\rm pref}_{D,p}(\mu_{\rm g})-V_{D,p}(\mu_{\rm g})
 \ge\frac1{18}.
\tag{NCO.50}
$$

These are separated quantitative bounds; no exact full-support optimum
is asserted.

Proof. The finite counting recurrence from Theorem 2.4 is
$b_0=2$, $b_{d+1}=2+b_d^2$ and $|\mathcal F_D|=b_D$. In particular
$U_D(t)=1/b_D$, and each law in (NCO.48) assigns every source mass
at least $\epsilon/b_D>0$. All numbers are rational and
$0<\epsilon<1$. Equation (NCO.43) gives identical core descriptor
pushforwards; adding the same uniform law preserves exact equality,
including every descriptor outside the five-position support and $B$.
The mixture samples one entire original tree once. It does not mix
or redraw replies during a run.

Every admissible encoder makes at least one Read on every source.
If it terminated before its first Read on any source, determinism and
source-blind initialization would make that same zero-call termination
occur on all sources. The two sources $c_{1,0},c_{1,1}$ require
different trajectories at a common authentic count by AAR13.3, a
contradiction. Thus Lemma 8.2 and the uniform component give, for
every all-word $A$ before taking any infimum,

$$
\mathbb E_{\mu_{\rm c}}T_A
 \ge(1-\epsilon)\frac{20}{9}+\epsilon.
\tag{NCO.51}
$$

Proposition 8.3 gives the displayed upper bound using the one
full-family-correct deterministic $A_{\rm g}$. Subtracting gives

$$
(1-\epsilon)\frac19-\epsilon(h+2)
 =\frac19-\epsilon\frac{9h+19}{9}
 =\frac1{18}.
\tag{NCO.52}
$$

For every prefix-only $S$, the last assertion of Lemma 8.2 and the
same universal one-call bound give
$\mathbb E_{\mu_{\rm g}}T_S\ge(1-\epsilon)20/9+\epsilon$.
Subtract the same upper bound and take the prefix infimum to prove
(NCO.50). This last step never applies the projected-source
comparison to the arbitrary unprojected guided law. $\square$

**Theorem 8.5 (the three equivalent universal cutoff properties).**
Fix any $D\ge1$ and $R$-leading $p$ with $1\le n=|p|\le D$.
The following three properties hold exactly when $n\le4$:

1. For every two probability laws $\mu,\nu$ on the same
   $\mathcal F_D$, equality of their complete descriptor distributions
   implies $V_{D,p}(\mu)=V_{D,p}(\nu)$.
2. For every probability law $\mu$ on that family,
   $V_{D,p}(\mu)=V^{\rm pref}_{D,p}(\mu)$.
3. For every admissible deterministic all-word encoder $A$, there
   exist finitely many admissible deterministic prefix encoders
   $S_1,\ldots,S_m$ and fixed real coefficients
   $\theta_i\ge0$, $\sum_i\theta_i=1$, independent of the sampled
   source, with
   $\sum_i\theta_i T_{S_i}(t)\le T_A(t)$ for every
   $t\in\mathcal F_D$.

The failures in the first two properties already occur for rational
laws strictly positive on every source. In the third property, the
coefficients and encoders may depend on $A,D,p$; even with that
allowance, $n\ge5$ fails. The finite convex combination is a numerical
sourcewise comparison, not an executing randomized encoder.

Proof. For $n\le4$, Theorem 7.1 gives both the descriptor-law dependence
and the exact prefix-only mean. Theorem 6.3 gives the third property
with at most two encoders and coefficients $1/2,1/2$; when $n\le3$
one encoder suffices.

For every $n\ge5$ and every permitted orientation and $D$, Theorem
8.4 supplies the pair refuting the first property and the guided law
refuting the second. To refute the third, take $A=A_{\rm g}$.
Every admissible prefix encoder has $\mu_{\rm g}$ mean at least
$(1-\epsilon)20/9+\epsilon$, whereas $A_{\rm g}$ has mean at most
$(1-\epsilon)19/9+\epsilon(h+3)$. Their difference is at least
$1/18$. Every fixed finite convex combination of those prefix means
obeys the same lower bound. If it dominated $T_{A_{\rm g}}$
sourcewise, integration under this actual law would give the reverse
inequality, a contradiction. Thus some actual source violates each
proposed finite-combination domination. No runtime randomizer is
introduced in either direction. $\square$

## 9. Source correspondence and the classification's resource boundary

**Definition 9.1 (charged acquisition and unresolved recovery).**
The guide query in (NCO.41) is the original-root literal $a$, answered
by the once-sampled original source, including when $a$ is absent.
It costs one chronological invocation and is neither supplied advice
nor a new port. Its acquired reply selects one of the
literal evidence queries of Proposition 8.3, and every return is checked
on that same source. The upper encoder has peak operand length at
most $n$ and total submitted letters at most $7+nh$: its guide has
length two, its candidate phase uses at most five further letters,
and its fallback uses at most $nh$ letters. These are bounds for
this encoder, not simultaneous resource domination of competitors.

The only optimized coordinate is invocation count. Public law
representation, arithmetic, selection and installation, every full
operand and submitted letter, local computation, output construction,
working and retained memory, clearing and validation remain charged.
Complete accessible state includes surviving replies, operands,
selectors, control, histories, capacity and allocation distinctions.
Retain them at their actual cost, or clear or retract every such
distinction before a descriptor-only export in a fixed output region.
Physical resident source storage and inaccessible or dead backing
remain physical costs. The stationarity promise is not a validation
service, and representation, reference, authentication and validation
of the authentic same-source, same-initial-version count $k$ retain
their hypotheses and costs.

The result supplies no source change, new invocation right, source
identifier, fresh sampling, free guide, free clock, subtree operation,
rerooting or cross-source map. Full $Q$, actual $S$-to-$C$ label
assimilation, physical Return, whole-source or undeclared-menu
recovery, and native/diffusion/AURIC correspondence remain unclosed.
Theorem 8.5 completes the local class boundary left necessary-only
by Corollary 7.2; it does not complete the wider mutual-recovery goal.
Equality of complete descriptor laws remains distinct from equality
of their compressed predictive-factor laws, which can collide as in
AAR13.3.

**Mathematical citation 9.2 (reused suppliers and new scope).**
The class-level cutoff and the universal five-position witness are
ordinary mathematical repo-derived results. The positive half is
Theorems 6.3 and 7.1 of this volume, and is cited rather than reproved.
The native realization uses AAR13.6's canonical contexts; AAR13.3
supplies the passive all-authentic-count decoder; AAR13.5 supplies
actual-label evidence, including label-flipped zero-prior worlds;
AAR13.4 supplies the total balanced fallback. AAR16.2–16.4 retain
their acquired-boundary and canonical-completion scope. In particular
their projected-source comparisons are not actual-law domination.
Lemma 8.2 uses AAR14.1 only at its canonical fixed points.

[Prior Acquisition Boundary §§2–3][PAB] already supplies canonical-core
all-competitor lower bounds, common rational full-support completion,
and length-eight and growing examples. Its Definition 4.3 supplies
the prefix-only optimum, and its Theorem 4.4 supplies the separate
persistent independent-forest sufficient condition at arbitrary
length. Those are reused methods and results, not renamed additions.
Here the five weights, actual sibling realization, evidence strategy
and quantitative bounds make the cutoff sharp for every $D,p$ with
$|p|\ge5$. No independent-forest hypothesis is added to Definition 1.1.
No equality of positive conditional observation orders is asserted for
these paired laws; Theorem 1.3's different correlation-order
quantifiers remain unchanged.

The weighted ordered-search recurrence is a mature intermediate tool,
already used in Theorem 7.1 and [PAB]. The decision-tree framework
described in [Cicalese–Laber–Saettler, §1][CLS] has the correspondence
given in Mathematical citation 7.4; no external approximation theorem
or generic decision-tree result supplies the new native witnesses or
their all-length separation. No worldwide originality claim is made.
The existing Lean definitions cited in Mathematical citation 5.3
identify the carrier, four replies, substitution and present-address
transport. In particular the distinct-address cost and positive-image
task in ActualTreeReadoutAcquisition are not the chronological cost
or passive task used here. Reading those sources supplies no new kernel
evidence. These additions contain no new Lean or kernel-verification
claim; finite arithmetic or finite source checks do not replace the
arbitrary-$D$, arbitrary-orientation proofs above.

[PAB]: RECURSIVE_RELATIONAL_OBSERVATION_PRIOR_ACQUISITION_BOUNDARY.md

## 追加锚（本行以下为增补区）

## 10. Uniform finite-source mixtures and an attained Read deadline

**Definition 10.1 (one finite source without a supplied height cap).**
Let $\mathcal T_D$ be the finite nonempty ordered alpha/beta trees of
height at most $D$, and retain the actual sources, four-reply original-root
Read and substitution of Definition 1.1. Thus

$$
b_0=2,\qquad b_{D+1}=2+b_D^2,\qquad
\mathcal F_D=\{\langle\alpha,v\rangle:v\in\mathcal T_D\},
\qquad U_D(t)=\frac1{b_D}\quad(t\in\mathcal F_D).
\tag{NCO.53}
$$

Fix a public $R$-leading word $p$ of length $n\ge1$ and a public integer
Read budget $r\ge1$. The correctness domain is now

$$
\mathcal F_\infty=\bigcup_{D\ge n}\mathcal F_D
 =\{\langle\alpha,v\rangle:v\text{ is a finite nonempty ordered
 alpha/beta tree}\}.
\tag{NCO.54}
$$

Every finite word, of any depth, remains a legal competing Read.
Competitors are deterministic effective encoder/passive-decoder pairs
with common source-blind initialization, terminating and correct on
every member of $\mathcal F_\infty$, including zero-prior worlds.
There is no supplied $D$, sampled-source identifier, unacquired
descriptor, or extra source-correlated advice input. Only the same
initial stationary register is read. The complete accessible handoff
$E_A(t)$ must support

$$
\mathsf D_A(E_A(t),p,k)=\operatorname{Read}_{\rho^k t}(p)
\quad(t\in\mathcal F_\infty,\ k\in\mathbb N),
\tag{NCO.55}
$$

for every supplied authentic same-source, same-initial-version $k$.
All inherited operation permissions, actual acquired records and
service bindings retain their original meanings and costs. This
experiment adds no permission to restart a stopped run, change the
register, or access a later source.

Let $\pi=(\pi_D)_{D\ge n}$ be any probability mass function, with no
computability assumption. Sample one finite integer $D$ with this law,
then one tree with law $U_D$, and keep that one actual tree throughout.
The resulting actual-source law is

$$
\mu_\pi=\sum_{D\ge n}\pi_D U_D,\qquad
\mu_\pi(\langle\alpha,v\rangle)
 =\sum_{D\ge\max\{n,\operatorname{height}(v)\}}\frac{\pi_D}{b_D}.
\tag{NCO.56}
$$

The latent $D$ need not be the actual minimal height. Overlapping
$\mathcal F_D$ are combined by this source marginal; no source is
resampled between queries. Each draw is finite even if the support of
$\pi$ has no finite cap. There is no uniform law on all finite trees
or on infinite trees in (NCO.56). Law membership and stationarity are
hypotheses, not facts authenticated by the replies.

For finite $D\ge n$, put

$$
s_h=1-\frac2{b_h}=\frac{b_{h-1}^2}{b_h}\quad(h\ge1),\qquad
q^D_0=1,\qquad
q^D_i=\prod_{h=D-i+1}^{D}s_h\quad(1\le i\le n).
\tag{NCO.57}
$$

As before, $T_A$ counts chronological initial Read invocations,
including absent, constant, off-path and repeated calls. Local work,
installation, references, storage and count authentication are separate
coordinates.

**Proposition 10.2 (the actual uniform joint completion and its masses).**
For each $D\ge n$, $U_D$ satisfies exactly the persistent joint-completion
condition of [PAB, Definitions 4.1–4.2][PAB]. In its notation the one
completion forest has law

$$
\nu_D=
 \left(\bigotimes_{i=2}^{n}\operatorname{Unif}(\mathcal T_{D+1-i})\right)
 \otimes
 \left(\operatorname{Unif}(\mathcal T_{D-n})
             \otimes\operatorname{Unif}(\mathcal T_{D-n})\right).
\tag{NCO.58}
$$

The first product is empty when $n=1$. If $Q_D$ is the descriptor law,
the actual realization map of PAB4.1 satisfies

$$
U_D=T_*(Q_D\otimes\nu_D),\qquad
Q_D(j,e)=\frac{q^D_{j-1}}{b_{D-j+1}},\qquad Q_D(B)=q^D_n.
\tag{NCO.59}
$$

In particular these are joint laws of complete trees and all their
literal replies, not only single-query marginals. For ordered prefix
search, combine the last leaf position with $B$ into key $n$ and set

$$
x^D_i=q^D_{i-1}-q^D_i\quad(1\le i<n),\qquad
x^D_n=q^D_{n-1}.
\tag{NCO.60}
$$

These weights sum to one and are strictly increasing when $n>1$.
Consequently the largest mass of any at-most-$m$ keys, $1\le m\le n$,
is the suffix mass $q^D_{n-m}$.

Proof. A uniform tree of cap $h\ge1$ is each of the two labelled
leaves with probability $1/b_h$, and is a branch with probability
$s_h$. Conditional on branch, its two ordered children are independent
uniform members of $\mathcal T_{h-1}$: each ordered pair has the same
unconditional mass $1/b_h$, and there are $b_{h-1}^2$ pairs. This is
a statement about the once-chosen actual tree, not a procedure for
redrawing a child when queried.

Follow the specified orientation of $p$ from $p_1=R$, whose subtree
has cap $D$. Conditional on continuing through a branch, the selected
child is uniform with its cap reduced by one, and its sibling is
independent uniform with that same reduced cap. Induction gives
$\Pr_{U_D}(p_i\text{ is branch})=q^D_i$. Stopping at $p_j$ with a
specified label has probability $q^D_{j-1}/b_{D-j+1}$; continuing as
branch through $p_n$ has probability $q^D_n$.

More fully, conditional on descriptor $(j,e)$, the exposed siblings
at $p_{i-1}\overline{p[i]}$, $2\le i\le j$, are jointly independent
uniform trees of caps $D+1-i$. Conditional on $B$, all siblings through
$i=n$ have this product law, and the two children below $p_n$ are
independent uniform $\mathcal T_{D-n}$ trees, independent also of
those siblings. Thus the exposed tuple under each $(j,e)$ is precisely
the corresponding projection of the one conditional-$B$ forest law
(NCO.58), as required by PAB4.2.

One can also check the mass of each entire actual tree directly.
For a fixed tree with descriptor $(j,e)$, its exposed sibling values
are uniquely determined, while the unexposed forest coordinates are
ignored. Its mass under the realization in (NCO.59) is

$$
\frac{q^D_{j-1}}{b_{D-j+1}}
       \prod_{i=2}^{j}\frac1{b_{D+1-i}}
 =\frac1{b_D}.
\tag{NCO.61}
$$

For descriptor $B$ the corresponding mass is

$$
q^D_n\left(\prod_{i=2}^{n}\frac1{b_{D+1-i}}\right)
               \frac1{b_{D-n}^2}
 =\frac1{b_D}.
\tag{NCO.62}
$$

Both equalities telescope using $s_h=b_{h-1}^2/b_h$, including the
empty products at $n=1$. Every source in $\mathcal F_D$ has exactly
one of these descriptions. Hence (NCO.59) holds on complete sources.
Applying any tuple of literal reply functions, including repeated,
nested, off-path and arbitrarily long words, preserves this joint
identity. Adaptive histories likewise refer to that one fixed tree.

Both labels at position $i<n$ have combined mass
$2q^D_{i-1}/b_{D-i+1}=q^D_{i-1}-q^D_i$. The mass of position $n$
together with $B$ is
$(q^D_{n-1}-q^D_n)+q^D_n=q^D_{n-1}$. A prefix search reaches and
terminates at $p_n$ on either of these last outcomes, so this
combination preserves every prefix search's call count. For
$1\le i\le n-2$, and then for the last two keys, the ratios are

$$
\frac{x^D_{i+1}}{x^D_i}=b_{D-i}>1,\qquad
\frac{x^D_n}{x^D_{n-1}}=\frac{b_{D-n+1}^2}{2}>1.
\tag{NCO.63}
$$

Here $D-n+1\ge1$ and $b_1=6$. For $n=1$ there is only weight one.
Positivity, the telescoping sum in (NCO.60), and these ratios show
that the greatest at-most-$m$ mass uses the last $m$ keys, with sum
$q^D_{n-m}$. $\square$

**Theorem 10.3 (one common attainer and the exact mixture deadline).**
Under Definition 10.1, let $m=\min\{n,2^r-1\}$. Then

$$
\boxed{\displaystyle
\sup_A\Pr_{\mu_\pi}(T_A\le r)
   =\sum_{D\ge n}\pi_D\,q^D_{n-m}.}
\tag{NCO.64}
$$

There is one effective attainer $A_{p,r}$, independent of $D$ and
$\pi$, globally correct and terminating on all $\mathcal F_\infty$.
It actually acquires a sufficient descriptor and uses the supplied
AAR13.3 passive decoder. On its single event of completion by $r$
Reads, the same completed handoff serves every authentic $k$
simultaneously: the event is not chosen separately for each $k$.

Proof. First fix $D\ge n$ and any globally admissible $A$. Its
restriction is correct and terminating on the entire $\mathcal F_D$,
regardless of its probabilities under $\pi$. Use the original
fixed-forest prefix simulation in PAB4.4, with its pointwise
inequality (4.9), on the actual realization (NCO.59). For each fixed
finite forest $z$, it produces a correct prefix encoder $B_z$ with

$$
T_{B_z}(b)\le T_A(T(b,z))
\quad\text{for every descriptor }b.
\tag{NCO.65}
$$

Specifically, it answers a simulated prefix by a real prefix Read;
a first-divergence query by a real Read of its path parent and a local
reply in the fixed sibling $z_i$; and a strict extension of $p$ by a
Read of $p$ and the fixed pair $z_*$. Fixed outer words have public
replies. The same $z$ supplies all simulated replies throughout.
This is precisely the supplier's single-source construction and
cost inequality, rather than an inference from its optimized-mean
conclusion. The hypothetical finite installation of $D,z$ is used
only for this conditional bound; it is not given to $A_{p,r}$.

Stop $B_z$ at any genuine acquired path leaf or branch reply at $p$.
The ordered pruning of PAB4.3 and AAR14.1 then gives an ordered
prefix search tree with no larger count on each descriptor. Prefix
queries whose replies are already forced can be omitted. Before a
hit, only absence or branch can continue, selecting the lower or
upper interval. Every unresolved leaf key must eventually be queried:
flipping just its actual label remains within $\mathcal F_D$ and
changes the required future at a common authentic count, by AAR13.3
and AAR13.5. A correct halt cannot skip that evidence even if different
positions have colliding predictive factors or have prior mass zero.
On the all-branch path, the pruned tree reaches $p_n$ and certifies $B$.
Thus this pruning applies to the complete correctness family, not
merely its positive-prior part. Replace $B_z$ by this pruned tree,
keeping its name and inequality (NCO.65).

There are at most $2^r-1$ internal query nodes in the first $r$ levels
of such an ordered tree: their maximal counts satisfy
$K_0=0$, $K_{\ell+1}=1+2K_\ell$. Each queried key contributes its
whole weight $x^D_i$ to completion by $r$, with $B$ sharing exactly
the completion time of key $n$. There are at most $m$ such keys.
Proposition 10.2 therefore bounds the completion probability of every
pruned tree by $q^D_{n-m}$. Taking the indicators of (NCO.65) and
averaging over the actual independent descriptor and forest gives

$$
\begin{aligned}
\Pr_{U_D}(T_A\le r)
&=\sum_z\nu_D(z)\sum_b Q_D(b)
             \mathbf1_{\{T_A(T(b,z))\le r\}}\\
&\le\sum_z\nu_D(z)\sum_b Q_D(b)
             \mathbf1_{\{T_{B_z}(b)\le r\}}\\
&\le q^D_{n-m}.
\end{aligned}
\tag{NCO.66}
$$

This covers every competing finite word and all its chronological
calls. It uses the actual $U_D$ completion law; the projected-source
comparison alone in AAR14.1 or AAR16.4 would not justify (NCO.66).

Construct the one attaining program as follows. If $m=n$, run the
balanced prefix acquisition of AAR13.4 on all keys $[1,n]$. Its bound
$h(n)=\lceil\log_2(n+1)\rceil\le r$ and its correctness proof do not
use a height cap. It terminates by genuine leaf acquisition or branch
at $p_n$ on every finite source.

If $m<n$, necessarily $m=2^r-1$. First search only the last $m$ keys
$[n-m+1,n]$ with the perfect ordered search tree of height $r$.
At interval $[a,b]$ its next key is $\lfloor(a+b)/2\rfloor$; submit
the entire literal $p_i$. A label reply acquires $(i,e)$ and stops;
branch at $p_n$ acquires $B$ and stops. Otherwise absence selects
the lower interval and branch the upper interval. All actual sources
whose first leaf is in this suffix, and all $B$ sources, terminate
within $r$ calls with this actual evidence.

A source with first leaf at $j\le n-m$ instead gives absence at every
query of the suffix tree's leftmost path. That path has exactly $r$
calls. Its last query, $p_{n-m+1}$, certifies that the first leaf is
earlier, but has not acquired its label. Continue on the same stationary
register with balanced prefix search on $[1,n-m]$, until the actual
leaf is read. This is a finite total fallback; it makes at least one
further Read. On any actual source it preserves the unique first-leaf
candidate and acquires its actual label. No $D$, law, off-path answer,
or pre-acquired descriptor is used in either phase.

Consequently, when $m<n$ the one completed-by-$r$ event is exactly

$$
G_{p,r}=
 \{t:\partial_p(t)=B\text{ or }
             \partial_p(t)=(j,e),\ j>n-m\}
 =\{t:\operatorname{Read}_t(p_{n-m})=\mathsf b\}.
\tag{NCO.67}
$$

When $m=n$, let $G_{p,r}=\mathcal F_\infty$. Equation (NCO.57) shows
$\Pr_{U_D}(G_{p,r})=q^D_{n-m}$ for every $D\ge n$. The stopping
decisions are made from actual acquired evidence; the rightmost event
description in (NCO.67) is not an additional free observation.

Every return includes the actual descriptor, and AAR13.3 gives one
decoder satisfying (NCO.55) for every $k$. Its same-source leaf
transport is at the originally present leaf, not at an absent target.
The construction and decoder are independent of $D$, so their
sourcewise correctness extends to the whole union (NCO.54).
In particular,

$$
G_{p,r}\subseteq
 \{t:\forall k\in\mathbb N,\quad
   \mathsf D_{p,r}(E_{p,r}(t),p,k)
                =\operatorname{Read}_{\rho^k t}(p)\}.
\tag{NCO.68}
$$

This is correctness per authentic request using one retained handoff;
it is not a finite execution producing infinitely many outputs.

Finally, for any fixed competitor the countable law (NCO.56) gives

$$
\Pr_{\mu_\pi}(T_A\le r)
 =\sum_{D\ge n}\pi_D\Pr_{U_D}(T_A\le r).
$$

This follows by summing the nonnegative source/latent-depth joint
masses, even when the source supports overlap. Apply (NCO.66) before
taking the supremum. The one constructed $A_{p,r}$ attains equality
in each summand, hence in their sum, proving (NCO.64).
No interchange of a supremum and an integral is assumed, and no
descriptor-independent forest representation of $\mu_\pi$ is needed.
$\square$

**Corollary 10.4 (uniform error certificate without a law oracle).**
For this same attainer and every $\pi$ of Definition 10.1,

$$
\Pr_{\mu_\pi}(T_{A_{p,r}}>r)=
 \sum_{D\ge n}\pi_D(1-q^D_{n-m})
 \le C_{n,r}:=
 \begin{cases}
 \displaystyle\frac2{b_{m+1}-1},&m<n,\\
 0,&m=n.
 \end{cases}
\tag{NCO.69}
$$

For a prescribed budget this rational certificate is finitely
computable from $n,r$. Given any requested rational tolerance
$\varepsilon\ge0$, there is a finite public procedure choosing a
budget and supplying a checkable certificate $C_{n,r}\le\varepsilon$.
Neither procedure uses $\pi$, a sampler, an actual depth, or exact
evaluation of the sum in (NCO.64).

Proof. For $m<n$ the elementary product inequality gives

$$
\begin{aligned}
1-q^D_{n-m}
&\le\sum_{h=D-n+m+1}^{D}\frac2{b_h}\\
&\le2\sum_{h=m+1}^{\infty}\frac1{b_h}.
\end{aligned}
\tag{NCO.70}
$$

The second step uses $D\ge n$; it does not replace the actual tree
by a cap-$n$ tree. Set $M=b_{m+1}$. The recurrence implies
$b_{m+1+j}\ge M^{2^j}$ for every $j\ge0$. Since the powers $2^j$
form a subset of the positive integers,

$$
\sum_{h=m+1}^{\infty}\frac1{b_h}
 \le\sum_{j=0}^{\infty}M^{-2^j}
 \le\sum_{\ell=1}^{\infty}M^{-\ell}
 =\frac1{M-1}.
\tag{NCO.71}
$$

This proves the bound for each actual conditional law, hence for
every mixture. If $m=n$, $q^D_0=1$ and failure is exactly zero.

Write the tolerance as $a/c$ with integers $a\ge0$, $c>0$. Enumerate
$r=1,\ldots,h(n)$. Compute $m$ by saturating the recurrence
$u_0=0$, $u_{i+1}=\min\{n,2u_i+1\}$, stopping at $i=r$ or $u_i=n$.
When $m<n$, compute the finite integer list
$b_0,\ldots,b_{m+1}$ and accept this budget if

$$
2c\le a(b_{m+1}-1).
\tag{NCO.72}
$$

The list, its recurrence equations and this integer comparison form
a finite rational error certificate. When $m=n$, use the exact
zero-failure certificate instead; this always occurs by $r=h(n)$,
including when $a=0$. Thus the procedure terminates without an
oracle. For a fixed supplied $r$, the same calculation returns
$C_{n,r}$ and checks the requested comparison; a failed comparison
means only that this bound does not certify that tolerance at that
budget. It is not a claim about an unknown $\pi$.

All large-integer arithmetic, storage of the recurrence list and
selection of the public budget are local paid work. For example, with
$L=1+\lceil\log_2(b_{m+1}+1)\rceil$ and $K$ the input bit length of
$a,c$, schoolbook arithmetic computes and checks such a list in
$O((m+1)L^2+(K+L)^2)$ bit operations and
$O((m+2)L+K)$ bits if the whole certificate is retained. Repeating
this finite calculation for at most $h(n)$ budgets is still finite;
no efficiency uniform in the numerical tolerance is asserted.
This certificate is conditional on the declared law class, rather
than an acquisition-based test of that class. $\square$

**Proposition 10.5 (finite acquisition resources and a complete handoff).**
Let $h(0)=0$ and $h(u)=\lceil\log_2(u+1)\rceil$ for $u\ge1$. The
attainer can be implemented with sourcewise bounds

$$
H_{n,r}=
 \begin{cases}
 r+h(n-m),&m<n,\\
 h(n),&m=n,
 \end{cases}
\qquad
T\le H_{n,r},\quad
A\le\min\{nH_{n,r},\,n(n+1)/2\},\quad Q\le n,
\tag{NCO.73}
$$

where $A$ is the total number of submitted letters and $Q$ is peak
literal length. These bounds are independent of $\pi,D$ and the
actual source size. They concern the exhibited encoder; optimality
in (NCO.64) concerns chronological Read count at this one public
deadline only.

Proof. In the nonsaturated case the first phase uses at most $r$
calls, and only its all-absent path enters a fallback of at most
$h(n-m)$ calls. In the saturated case AAR13.4 gives $h(n)$ calls.
No key is repeated: each balanced search discards the queried key
from its remaining interval, and the two phases use disjoint
intervals. Every operand is an original-root prefix of $p$ of length
at most $n$. This proves both letter bounds and the peak bound,
without discounting any competitor's repeated or absent call.

Here is a finite local representation sufficient for these bounds.
Install the public literal $p$, the binary budget and a fixed
controller for ordered interval search, together with the existing
passive decoding rule. Store interval endpoints, current key, phase,
reply and descriptor flags in binary. The saturated recurrence in
Corollary 10.4 computes $m$ with at most $h(n)$ iterations and
$O(\log(n+2))$-bit counters; it need not materialize $2^r$ when $r$
has an arbitrarily large binary representation. Read the budget once
and clamp it to $h(n)$ by a binary comparison before those iterations.
Each midpoint is computed by integer addition and division by two. To query $p_i$,
copy its first $i$ letters from the installed word into an actual
literal buffer, then submit that whole word. A local slice or prefix
index is not a source operation. There is no installed table indexed
by the hidden tree, depth or prior.

For example put $\ell=\lceil\log_2(n+2)\rceil$ and let $\ell_r$ be
the binary input length of $r$. With binary schoolbook counters and
explicit copying and recording of literals, the new controller can
use

$$
O\bigl(\ell_r+(n+h(n)+H_{n,r}(n+1))\ell\bigr)
\tag{NCO.74}
$$

local bit operations during installation of these public parameters
and acquisition, excluding the original Read service, external
authentication and reference installation. Scanning $p$ establishes
$n$; interval arithmetic costs $O(\ell)$ per step. Charging
$O(\ell)$ work per copied or scanned symbol is sufficient even for
a direct sequential representation. This deliberately loose bound
also pays for reply recording and final descriptor/factor formation.
No finite expected running cost of the original source service is
inferred from it.

Retain a complete ordered record of every invocation, its full
literal, reply, chronological position and inherited same-version
binding. A common retained root/version reference can be shared by
these entries, with its representation and installation charged.
It is the inherited actual service binding, not an identifier that
discriminates the unknown source. Keeping the whole record, all
surviving operands and reply latches, final interval/control state,
descriptors, length/capacity fields and allocation distinctions gives
an additional accessible memory bound

$$
O\bigl(\ell_r+n+H_{n,r}(n+\ell)\bigr)
\tag{NCO.75}
$$

bits, plus the actual reference/binding representation. Fixed-size
regions sized by the public bound may be used, with their unused
space also charged. Any previously acquired actual rows, chronological
records, permission fields and original service state remain retained
and separately charged in addition to this new allocation. They are
not deleted or replaced by a descriptor. This full-state convention
requires no erasure or retraction assumption: $E$ includes every
surviving accessible source-dependent field. Any alternative
descriptor-only export would have to pay to clear or retract all
those other distinctions; it is not the interface asserted here.

The output supplies the genuinely acquired descriptor and, if desired,
its already supplied factor $\Gamma_p$ in AAR13.3. For $(j,e)$ the
factor is obtained by scanning the suffix $p\setminus p_j$ with weight
one per $L$ and two per $R$, using the endpoint case when $j=n$.
Its branch threshold is at most $2n$, so it takes $O(\ell)$ bits.
For $B$ it is $(0,0)$. The decoder is exactly AAR13.3's guarded
(AAR.59) rule: for factor $(g,c)$, return branch at $k\ge g$, beta
at $g\ge1,\ k=g-1$, alpha at $c=1,\ k=g-2$, and absent otherwise.
The guards retain the left-ending/right-ending distinction. The
same finite formula holds on every source in (NCO.54), since any
such tree belongs to a finite $\mathcal F_D$ with $D\ge n$ and the
formula does not use $D$.

Formation of the descriptor, the optional factor, and the complete
export is paid local output work covered by (NCO.74)–(NCO.75).
For a later authentic binary count of length $\ell_k$, evaluation
from the retained factor costs $O(\ell_k+\ell)$ local bit operations
and $O(\ell_k+\ell)$ extra bits, including the count representation;
forming the factor afresh instead costs an additional
$O(n\ell)$ scan. Validation, count authentication and actual
same-version binding still require their original suppliers and
their separate costs. There is no later source Read, evaluation of
$\rho^k t$, or recovery of an unknown $k$.

Resident original-source storage and inaccessible or dead backing
are still charged at their actual sizes, beyond (NCO.75). They have
no common finite bound on $\mathcal F_\infty$, and arbitrary $\pi$
does not supply a finite expected source size. These physical costs
are not removed by the finite added-controller bounds. $\square$

**Definition 10.6 (the recovered interface and its scope).**
The consumer in (NCO.64) is acquisition, by a declared Read deadline,
of one finite boundary memory sufficient for the original literal
$p$ at every authentic supplied count. The information travels from
actual spatial path evidence to the existing finite predictive factor
and passive future-value decoder. It is not a supplied mathematical
quotient, inverse or completion forest masquerading as an available
port. Original rows, legal domains, references and operation rights
retain their full contracts.

In particular, (NCO.64) neither identifies an arbitrary law from Reads
nor supplies an effective sampler for an arbitrary $\pi$. When $m<n$,
the exact sum can be noncomputable for a noncomputable prior: already
a mixture of two depths gives a nonconstant rational affine function
of their mixing weight. When $m=n$ the value is one. Corollary 10.4
certifies its uniform bound without evaluating the prior-dependent sum. The
single program is common across depths and priors for fixed $p,r$;
there is no claim of one program optimal for all budgets, mean costs,
or other resource coordinates. No descriptor-independent completion
of the mixture is asserted: the shared latent depth can correlate
boundary and off-path data after mixing.

The interface supplies no actual later source access, physical Return,
actual $S$-to-$C$ label assimilation, full response $Q$, whole-source
recovery, or undeclared menu. It supplies no identification of native,
diffusion or AURIC sources. In particular, a frozen-prefix prediction
or a reply for the original version is not a reply at an actual later
Return. The wider mutual-recovery problem for spatial structure,
legal continuation, boundaries and memory retains these missing
interfaces.

Mathematical citations for §10. The source-specific result is
repo-derived: the actual joint uniform completion, its increasing
native search weights, one common effective attainer and its
depth-uniform certificate establish the stated original-source
deadline consumer. Countable nonnegative averaging, uniform finite
tree counting and ordered successful-search capacity are reused
intermediate methods, not separate new content claims. NCO1.1 and
NCO2.4 supply the native cost convention and $b_D$ count; NCO6–9
retain their short-target mean comparisons and sharp universal
all-law cutoff. This restricted uniform-mixture family does not
alter that all-law classification.

[PAB4.1–4.4][PAB] supplies the persistent completion map and the
pointwise fixed-forest comparison used directly in (NCO.65), while
[AAR13.3–13.5 and AAR14.1][AAR] supply the acquired factor/decoder,
balanced acquisition, label evidence and ordered pruning.
AAR16.2–16.4 retains its joint-menu and projected-source scope;
it is not substituted for an actual-law comparison here.
[SLH35–36][SLH] already supplies executable future-code acquisition
and the separate source, entry, reference and full-record costs.
Thus this is not the first native acquisition algorithm.

The existing [Source and substitution][GFT] and
[Reply, readout and flip][READ] identify the same actual carrier
and operations: true labels alpha, false labels beta, false address
letters mean $L$ and true mean $R$. The present-address transport in
[original_present_transport][NDP] and the existing guarded semantics
cited by AAR13.3 apply only with their original hypotheses. The
positive-image task and distinct-address paid cost of [READ] are
different from (NCO.55) and its chronological invocation count.
These citations supply correspondence, not a new Lean verification
of §10.

For the mature ordered-search background, Bruno, De Prisco, De Santis
and Vaccaro, [*Bounds and Algorithms for Alphabetic Codes and Binary
Search Trees*, §§II–III and V, arXiv:2407.16443v1][BDDV], treats
alphabetic codes, successful/unsuccessful ordered search and bounds
on average search cost, with linear-time constructions. Its root-level
convention agrees with counting a first query at depth one. Its
average-cost bounds do not assert this native fixed-deadline optimum.
[Cicalese–Laber–Saettler, *Diagnosis determination: decision trees
optimizing simultaneously worst and expected testing cost*][CLS]
treats finite adaptive function identification with test costs and
simultaneous logarithmic approximation guarantees. Here sources
are objects, native replies are tests, target futures are output
classes and each chronological invocation has unit cost; those
approximation guarantees do not supply (NCO.59) or (NCO.64).
Neither paper identifies the original native operations with a
generic comparison oracle. The native joint correspondence and
evidence-preserving realization are proved above; no worldwide
priority claim is made.

[BDDV]: https://arxiv.org/html/2407.16443v1

## 追加锚（本行以下为增补区）
