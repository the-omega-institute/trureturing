# FIB three reads: the installed-state endpoint-risk partial frontier

For the original stationary biased XOR source, let $C_m$ be the greatest
correct classification mass achievable with at most $m$ installed complete
controller rows and almost-sure return within three paid visible calls.
The exact values established here are

$$
\begin{aligned}
C_1=C_2&=\frac a2,\\
C_3&=\frac a2+a\eta,\\
C_4&=\frac a2+a\eta(1+c),\\
C_5&=\frac a2+a\eta(1+c+c^2),
\end{aligned}
$$

where $a=\max(p,1-p)$, $b=\min(p,1-p)$, $\eta=ab$ and
$c=a^2+b^2$. The inherited unrestricted value is
$S_3=a/2+3a^2\eta+2\eta^3$, attained with nine rows and requiring
at least nine rows. The exact five-row correct-mass deficit is

$$
S_3-C_5=(a-b)\eta^2(3-2\eta)>0.
$$

Complete six-, seven- and eight-row tables below give further attained
lower points, with their source masses, labels and unconditional paid
costs. A finite-menu theorem preserving actual installed rows proves
attainment at every installed budget. Consequently $C_m<S_3$ for every
$m\le8$. The exact values at $m=6,7,8$ remain open here.

**Reference status.** These are ordinary mathematical proofs. This volume
does not assert Lean-kernel verification. It uses the five owning sources
listed in Section 11; their results retain their ownership. The new
source-relative content is the three-read frontier through five installed
rows, its quantitative deficit, the further fully costed attainable
points, and the row-preserving finite-menu theorem. All conclusions fix
each $0<p<1$, $p\ne1/2$, either original endpoint, and the given unchanged
independent seed law. No literature-wide priority claim is made.

## 1. The one source and the actual target

**Definition 1.1 (Original stationary law).** Let $\varphi$ be uniform
on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$, where $0<p<1$ and $p\ne1/2$.
On the original integer clock define

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

The symbols in $\mathcal A=\{a_0,a_1,b_0,b_1\}$ are distinct.
Write $J_p$ for this joint law. This is [Original, Proposition 2.1][O].
Its stationary masses at $a_s,b_s$ are $\pi_s/2$, with
$\pi_0=1-p$, $\pi_1=p$: an active transition chooses $b_t$ with
probability $\pi_t$ and emits $s\oplus t$, and the next transition
copies $b_t$ to $a_t$, emitting zero. Incoming mass at either state
with spin $t$ is $\pi_t/2$. Thus the uniform phase retains the original
stationary emitted-bit clock, with its actual separator coordinates.

Fix $j\in\{0,1\}$ before acquisition. Define

$$
\begin{array}{c|cc|cc}
 &h_0(s)&v_0&h_1(s)&v_1\\ \hline
j=0&a_s&0&b_s&0\\
j=1&b_s&1&a_s&0
\end{array}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.2}
$$

In particular phase zero uses target spin $S_j$, whereas phase one uses
$S_0$ for either endpoint. The two phase-label sets are disjoint. A
single returned state cannot be correct in both phases. Description
(1.1) supplies no observation of an unqueried spin or of $\varphi$.

**Definition 1.2 (Parameters).** Put

$$
\begin{gathered}
a=\max(p,1-p),\quad b=\min(p,1-p),\quad
\eta=ab,\quad c=a^2+b^2=1-2\eta,\quad d=a-b,\\
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2,\end{cases}
\qquad R=a/b.
\end{gathered}
\tag{1.3}
$$

Thus $\mathbb P(S_\ell=\sigma)=a$, and

$$
\begin{gathered}
a+b=1,\quad 0<b<1/2<a<1,\quad 0<\eta<1/4,\quad
1/2<c<a<1,\quad b<c,\\
d=2a-1>0,\quad a-c=bd,\quad c-b=ad.
\end{gathered}
\tag{1.4}
$$

For example $a-c=b(a-b)$ and $c-b=a(a-b)$ prove the comparisons
with $a,b$; $c-1/2=(a-b)^2/2$ proves the remaining strict comparison.
These identities cover the entire stated bias range.

## 2. Paid reads and complete installed rows

**Definition 2.1 (Original protocol and closed controller).** Fix any
probability space $(\mathsf U,\mathcal U,\nu)$ independent of the whole
$J_p$ source, keeping its law unchanged. In the original protocol class
of [Original, Definition 9.1][O], a measurable next-event rule uses only
fixed public data, $u\in\mathsf U$, and the finite ordered acquired
address/reply record. It requests an integer address, returns a state,
or continues internally forever without another call or return. Finite
events may follow internal waits determined by the same data. All random
public data and internal randomness are included in $u$. Each requested
address replies with the actual $X_t$ of (1.1). Every call is charged,
including repeats, ignored replies, separator zeros, negative addresses
and disconnected or arbitrarily distant addresses. Internal nonreturn
after finitely many calls, infinite-read paths, early returns,
wrong-phase outputs and measurable null-set completions are allowed.
Waiting provides no extra source information. There is no hidden-state,
half-line or tail read, source-dependent seed or timing, reset, law switch,
endpoint movement or erased-coordinate substitution.

The installed subclass considered here is exactly [Two Read,
Definition 8.1][E2]. A table has a nonempty finite set $K$ and maps

$$
\begin{aligned}
\lambda &:K\longrightarrow
\{\operatorname{Read}(t):t\in\mathbb Z\}
\sqcup\{\operatorname{Halt}(h):h\in\mathcal A\},\\
\delta &:K_{\rm R}\times\{0,1\}\longrightarrow K,
&c_{\rm init}&:\mathsf U\longrightarrow K,
\end{aligned}
\tag{2.1}
$$

where $K_{\rm R},K_{\rm H}$ are its read and halt rows and
$c_{\rm init}$ is measurable for discrete $K$. Initialization sets the
current row to $c_{\rm init}(u)$. A read row makes its one fixed literal
call and changes the current row to $\delta(r,X_t)$. A halt row returns
its fixed four-state label. Instructions have finite duration and there
are no silent instructions. A nonreturning installed execution therefore
makes infinitely many charged reads.

After initialization the current row contains all runtime memory. The
reply is consumed by its immediate update. There is no separate program
position, clock, counter, phase bit, archive, stack, saved reply, output
latch, computed address, later seed access or online randomizer. The
public fixed $p,j$ may determine the static table. All installed rows
count in $|K|$, including duplicates, unused rows and rows on null paths.
Cycles are allowed. These tables are a subclass of the original protocols;
they do not represent every protocol with internal continuation.

**Definition 2.2 (The three-read installed frontier).** Let $\tau$ be
the return time, with $\tau=\infty$ on nonreturn, and let
$N\in\mathbb N_0\cup\{\infty\}$ count all actual calls. Set

$$
\begin{gathered}
E_3=\{\tau<\infty,N\le3\},\qquad
q_3=(J_p\otimes\nu)(E_3),\\
L_3=(J_p\otimes\nu)(A\ne H_j,E_3),\\
C_m=\sup\{q_3-L_3:|K|\le m,\ q_3=1\},\qquad
R_m=1-C_m,\qquad m\ge1.
\end{gathered}
\tag{2.2}
$$

An immediate halt makes these sets nonempty. The condition $q_3=1$ is
almost sure, allowing exceptional nonreturn and excess-read paths of
probability zero. It does not require an all-input cap. On this slice
$L_3$ is unconditional four-state classification error, up to a null
extension of $A$. It is distinct from visible-bit Brier loss. The total
paid cost is $\mathbb E N$, counting all returning and nonreturning paths.

**Convention 2.3 (Inherited numerical inputs).** We use the following
ordinary results with their stated ownership:

$$
\begin{aligned}
S_1&=\frac a2+a\eta,\qquad
T=\frac a2+a\eta(1+c),\\
Z&=\frac a2+a^2\eta(1+c),\qquad
D=a^2\eta+2a\eta^2,\\
S_3&=Z+D=\frac a2+3a^2\eta+2\eta^3.
\end{aligned}
\tag{2.3}
$$

[Original, Theorem 11.4][O] and [Paid Risk, Theorem 4.1][P] own the
unrestricted almost-sure one-read correct optimum $S_1$. [Two Installed,
Theorem 6.1][I2] bounds every $q_2=1$ table with at most two read rows
by $T$, irrespective of its halt-row count. Here $q_2$ means return
within two calls almost surely. [Three Read, Theorem 7.1][E3] owns the
unrestricted $q_3=1$ optimum $S_3$; its Theorem 12.4 owns the exact
all-attainers minimum $M_3=9$, with at least six read and three halt
rows. Their constructive realizations are inherited as well. None of
these values or minima is counted as a new result of this volume.

## 3. Actual-table reductions and finite source products

**Lemma 3.1 (Initialization and acquired sections).** For a fixed table
let $w_r=\nu(c_{\rm init}^{-1}\{r\})$, and denote by $q_3(r),C_3(r)$
the source masses of return and correct return within three calls from
deterministic initial row $r$. Then

$$
q_3=\sum_rw_rq_3(r),\qquad
q_3-L_3=\sum_rw_rC_3(r),\qquad \sum_rw_r=1.
\tag{3.1}
$$

If $q_3=1$, every positive-weight initial row has $q_3(r)=1$.
At a deterministic start a consistent finite acquired record has exactly
its acquired-reply cylinder as source section.

Proof. After initialization the seed has no runtime role. Independence
therefore gives the finite sums (3.1), without a conditional law on
singleton seeds. Since $\sum_rw_r(1-q_3(r))=0$ has nonnegative summands,
each positive-weight summand vanishes. Uniform deterministic-start upper
bounds consequently apply to the original initialization. Constant
initialization is available on every given seed space.

For the section assertion, the empty record imposes no condition. At
each fixed prefix the row and instruction are fixed. Reading $t$ with
reply $x$ intersects the previous section with $\{X_t=x\}$. A halt
adds no source condition. Induction proves the assertion, including
adaptive paths and contradictory repetitions, which are empty. Finite
instruction durations add no information. Completed versions agree off
product-null sets; Tonelli gives the same section identities for almost
every seed and the same integrated masses. $\square$

**Lemma 3.2 (No returning revisit).** On a fixed source sample, a
returning execution never visits the same read row twice. Consequently
a table with at most two read rows and $q_3=1$ has $q_2=1$ and
correct mass at most $T$. With at most one read row it has $q_1=1$
and correct mass at most $S_1$.

Proof. Once the source sample is fixed, every read row has a static
reply. Its successor is a deterministic function of that row. A repeated
read row therefore repeats the whole subsequent state trajectory. A
first halt could not occur after such a repetition: it would already
have occurred on the first traversal. Thus repetition before return
causes perpetual reading. Every finite return uses at most the number
of installed read rows. On the mass-one return event this proves the
asserted smaller budgets. Apply the inherited bounds in Convention 2.3,
or apply them to the positive initialization cells of Lemma 3.1 and
average. This argument retains the actual table, its row sharing, all
unused rows and every null-path cycle. $\square$

**Lemma 3.3 (Component products and a fixed-label observation).** In
phase $\phi$, a read at $2\ell+\phi$ is the XOR edge
$\{\ell,\ell+1\}$ on the integer spin line; every other read is a
separator. Distinct acquired active edges form finite disjoint paths.
On a consistent labelled path its two spin assignments are complements,
with their actual Bernoulli product weights. A zero-labelled component
with $L$ edges has probability

$$
t_{L+1}=a^{L+1}+b^{L+1}\ge c^L.
\tag{3.2}
$$

Disjoint components multiply. Adjoin the actual target vertex as a
singleton if needed. If its component has $v$ vertices, the ratio of
its two target-spin masses in either direction is at most $R^v$.
If an almost-surely returning table has only one distinct halt label,
its correct mass is at most $a/2$.

Proof. An XOR on an edge fixes the next spin given the preceding spin.
A finite path therefore has exactly its two complementary completions.
For all-zero labels both are constant. For $L\ge1$, convexity gives
$a\,a^L+b\,b^L\ge(a\,a+b\,b)^L=c^L$; the case $L=0$ is equality
one. Independence of the original iid spins gives multiplication on
vertex-disjoint components. Complementation exchanges each factor $a$
with $b$, yielding the ratio bound. Phase-specific full-law masses have
the factor $1/2$. Repeats add charges but no new edge; inconsistent
labels give zero mass. The argument covers all integer locations and
every target incidence. With one distinct halt label $h$, the output
is $h$ almost surely, so correctness is $J_p(H_j=h)\le a/2$.
Duplicate halt rows do not alter this observation. $\square$

## 4. A universal bound for at most two halt labels

**Theorem 4.1 (Two-label three-read bound).** Every installed table
with $q_3=1$ and at most two distinct halt labels, with any number of
read rows, has correct mass at most

$$
F:=\frac a2+a\eta(1+c+c^2)=a\left(1-\frac{c^3}{2}\right).
\tag{4.1}
$$

This includes same-phase labels, opposite-phase labels, majority and
minority spin choices, every address configuration and every allowed
initialization.

Proof. By Lemma 3.1 fix an eligible deterministic start. One distinct
label is covered by Lemma 3.3. Suppose there are two distinct labels.

First suppose both are in one phase $\gamma$. In the other phase
correctness is zero. Conditional on $\gamma$, return within three
calls still has probability one. On a positive terminal cylinder with
$n\le3$ calls the target component has at most $n+1\le4$ vertices.
Lemma 3.3 bounds its two target-spin odds by $R^4$. Whichever spin is
output, its error mass on that conditional cylinder is at least
$b^4/(a^4+b^4)$ times the cylinder mass. All nontarget components
are common factors in this comparison. Summing the disjoint terminal
cylinders conditional on $\gamma$ and restoring its phase prior gives

$$
\text{correct mass}\le
\frac12\left(1-\frac{b^4}{a^4+b^4}\right)
\le H:=\frac{1-b^4}{2},
\tag{4.2}
$$

because $a^4+b^4\le1$. This conditional calculation supplies an upper
bound for the original rule, without granting it a phase observation.

Now suppose the labels are $h_0(s_0)$ and $h_1(s_1)$. Write
$x_\phi=\mathbb P(S=s_\phi)\in\{a,b\}$. Follow the actual table
with all replies specified to be zero. Every finite all-zero cylinder
has positive mass in each phase, by the constant-component products of
Lemma 3.3. Hence this zero branch must halt after some $\ell\le3$
calls. Otherwise, after three zero replies its current row would still
read, excluding that positive cylinder from $E_3$.

Let $C$ be this terminal zero cylinder, let $n_\phi$ count its calls
at parity $\phi$ including repetitions, and put

$$
w_\phi=J_p(C,H_j=h_\phi(s_\phi)),\qquad
n_0+n_1=\ell\le3.
\tag{4.3}
$$

In phase $\phi$, let $k_\phi\le n_\phi$ be its number of distinct
active edges and let $r$ of them belong to its target component. A
majority target in this component contributes $a^{r+1}$; a minority
target contributes $b^{r+1}$. The other components of lengths $L$
contribute $t_{L+1}\ge c^L$. Using $a>c>b$ gives

$$
\begin{array}{ll}
s_\phi=\sigma:
&w_\phi\ge \tfrac12 a\,c^{k_\phi}
\ge \tfrac12 ac^3,\\
s_\phi=1-\sigma:
&w_\phi\ge \tfrac12 b^{k_\phi+1}
\ge \tfrac12 b^4.
\end{array}
\tag{4.4}
$$

The formulas include empty edge sets, singleton targets and disconnected
edges. The phase factor is $1/2$, and repetitions are still paid.

Outside $C$, a path has a first one at a call on this zero branch.
Its parity identifies the actual phase. In phase $\phi$, correctness
outside $C$ is bounded by the entire event with its one available
phase-$\phi$ label outside $C$, of mass $x_\phi/2-w_\phi$.
On $C$ the actual table outputs a single label, with correct mass at
most $\max(w_0,w_1)$. Therefore

$$
\text{correct mass}\le
\frac{x_0+x_1}{2}-\min(w_0,w_1).
\tag{4.5}
$$

No independently chosen continuations are combined in this inequality.
For two majority labels, (4.4)--(4.5) give $a-ac^3/2=F$.
For mixed labels they give at most $H$, since $ac^3>b^4$.
For two minority labels they give at most $b-b^4/2<H$.

It remains to compare (4.2) and the mixed-label bound with $F$ over
the entire bias range. The identity $c-b=ad$ yields

$$
\begin{aligned}
2(F-H)
&=d-ac^3+b^4\\
&=d\bigl[1-c^3-\eta(c^2+cb+b^2)\bigr]\\
&=d\eta\bigl[2(1+c+c^2)-(c^2+cb+b^2)\bigr]>0.
\end{aligned}
\tag{4.6}
$$

Indeed $ac^3-b^4=dc^3+b(c^3-b^3)
=d[c^3+\eta(c^2+cb+b^2)]$, and $1-c=2\eta$ gives the last
line. Since $b<c<1$, its bracket is at least
$2+2c-c^2>0$. This proves every label case. Finally average using
Lemma 3.1. Null paths, unused rows, early halts and cycles have not been
removed from the competitor class. $\square$

## 5. Exact low installed budgets and their complete attainers

**Convention 5.1 (Static literals and table notation).** Each displayed
table is a separate controller, initialized constantly at its first row.
Every listed row is installed. A dash at a halt means it has no update.
Instructions may all have duration one. Expressions $2(j+k)$ in an
instruction mean a single integer literal fixed before runtime. For
clarity, all offsets used in these tables instantiate as follows:

| Offset $k$ | Integer for $j=0$ | Integer for $j=1$ |
| --- | --- | --- |
| $-2$ | $-4$ | $-2$ |
| $-1$ | $-2$ | $0$ |
| $0$ | $0$ | $2$ |
| $1$ | $2$ | $4$ |
| $2$ | $4$ | $6$ |
| $3$ | $6$ | $8$ |
| $4$ | $8$ | $10$ |
| $6$ | $12$ | $14$ |

There is no runtime address arithmetic. Row names such as $P,Q,Z_H$
name actual halt rows; their fixed labels are always displayed. A record
in a mass table is its full sequence of paid replies up to return.
Source masses are full $J_p$ masses, including the uniform phase.

**Proposition 5.2 (One-, three- and four-row realizations).** The values
$a/2,S_1,T$ are attained with one, three and four installed rows,
respectively, under $q_3=1$ on every given seed space.

Proof. For the first value use the sole row

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

It has $N=0$ on every path and correct mass $a/2$.
For $S_1$, use the inherited one-read realization

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

In phase zero the queried pair $\{j+2,j+3\}$ avoids target $j$;
in phase one it is a separator. Its terminal masses are

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $0$ | $h_1(\sigma)$ | $(1+c)/2$ | $a/2$ | $1$ |

A one certifies phase zero and leaves its actual target independent.
A zero succeeds for the displayed output exactly in phase one with
$S_0=\sigma$. The correct sum is $S_1$, with $N=1$ always.

For $T$ use [Two Installed, Proposition 9.2][I2]'s table:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $S$ | $P$ |
| $S$ | $\operatorname{Read}(2(j+4))$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

The two phase-zero pairs are disjoint from one another and target $j$.
Their zero probabilities are $c$, independently within the same spin
law. Phase one has only paid separators. Thus

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $ac\eta$ | $2$ |
| $00$ | $h_1(\sigma)$ | $(1+c^2)/2$ | $a/2$ | $2$ |

The source masses sum to one by $2\eta=1-c$, and the correct masses
sum to $T$. Its exact cost law is
$\mathbb P(N=1)=\eta$, $\mathbb P(N=2)=1-\eta$, so
$\mathbb E N=2-\eta$ and its maximum is two. These tables halt on
every formal input. The constructions and their one/two-read masses are
inherited; the bounds against the three-read installed competitors are
proved below. $\square$

**Proposition 5.3 (Five-row simultaneous attainer).** Five rows attain
$F$ in (4.1), with exactly three read rows and two halt rows.

Proof. Install

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $S$ | $P$ |
| $S$ | $\operatorname{Read}(2(j+4))$ | $U$ | $P$ |
| $U$ | $\operatorname{Read}(2(j+6))$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

In phase zero the three potentially queried pairs are
$\{j+2,j+3\}$, $\{j+4,j+5\}$ and $\{j+6,j+7\}$.
They are mutually disjoint and exterior to actual target $j$. In phase
one all calls are separators, with actual target $0$. Independence of
these pairs in the one source proves the complete terminal accounting:

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $ac\eta$ | $2$ |
| $001$ | $h_0(\sigma)$ | $c^2\eta$ | $ac^2\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+c^3)/2$ | $a/2$ | $3$ |

In the first three rows the first paid one certifies phase zero, while
the target retains its independent majority probability $a$. In the
last row only the phase-one majority-target event is correct. The
additional phase-zero all-zero mass is an error for its fixed output.
Thus no two phase maxima are added on that leaf.

The source masses sum to one because
$\eta(1+c+c^2)=(1-c^3)/2$; their correct masses sum to $F$.
Every formal path halts within three calls, and

$$
\begin{aligned}
\mathbb P(N=1)&=\eta,&\mathbb P(N=2)&=c\eta,\\
\mathbb P(N=3)&=1-\eta(1+c),&
\mathbb E N&=3-\eta(2+c).
\end{aligned}
\tag{5.1}
$$

The maximum is three. All separators are included in these costs.
Constant initialization leaves every given seed law unchanged.
The target labels in (1.2) and the definition of $\sigma$ verify both
endpoints and both bias directions. $\square$

**Theorem 5.4 (Exact frontier at budgets one through five).** For every
fixed allowed $p,j,\nu$, the correct-mass maxima and complementary
error minima are

| Installed budget | $C_m$ | $R_m$ |
| --- | --- | --- |
| $1,2$ | $a/2$ | $1-a/2$ |
| $3$ | $S_1=a/2+a\eta$ | $1-S_1$ |
| $4$ | $T=a/2+a\eta(1+c)$ | $1-T$ |
| $5$ | $F=a/2+a\eta(1+c+c^2)$ | $1-F$ |

Proof. At most two rows either all halt or, if a read is installed,
leave at most one halt label. Lemmas 3.1 and 3.3 give at most $a/2$.
The one-row table attains it.

With at most three rows, two or more read rows leave at most one halt
label. Otherwise at most one read row gives the one-read bound $S_1$
by Lemma 3.2. Proposition 5.2 attains $S_1$ with three rows.

With at most four rows, at most two read rows give the bound $T$ by
Lemma 3.2. Three or more read rows leave at most one halt label, bounded
by $a/2<T$. The four-row table attains $T$.

With at most five rows, at most two read rows again give $T$. Otherwise
at most two halt rows give at most two distinct halt labels, so Theorem
4.1 gives $F$. Since $F-T=ac^2\eta>0$, this bounds every five-row
table by $F$, and Proposition 5.3 attains it. A table with no halt rows
cannot satisfy $q_3=1$. All splits count unused and duplicate rows.
The initialization reduction includes arbitrary measurable initializations
and all exceptional null paths. Since $q_3=1$, each complementary risk
is attained as well. $\square$

**Corollary 5.5 (Exact quantitative five-row penalty).** Relative to
the inherited unrestricted three-read optimum,

$$
S_3-C_5=R_5-(1-S_3)=d\eta^2(3-2\eta)>0.
\tag{5.2}
$$

Also $C_4-C_3=ac\eta>0$ and $C_5-C_4=ac^2\eta>0$.

Proof. Expand $1+c+c^2=3-6\eta+4\eta^2$. Then

$$
\begin{aligned}
S_3-F
&=3a^2\eta+2\eta^3-a\eta(3-6\eta+4\eta^2)\\
&=3(2a-1)\eta^2-2(2a-1)\eta^3\\
&=d\eta^2(3-2\eta).
\end{aligned}
\tag{5.3}
$$

The middle line uses $a^2-a=-\eta$. All factors in (5.2) are
positive by (1.4). The other differences follow directly from the
matched values in Theorem 5.4. This is an exact all-table quantitative
penalty, with one actual attainer, rather than a consequence of
nonattainment alone. $\square$

## 6. A fully costed six-row attained point

**Proposition 6.1 (Three reads and three output rows).** Define

$$
V=\frac a2+a\eta\left(\frac32+a^2\right),\qquad
t=a^3+b^3=1-3\eta.
\tag{6.1}
$$

A complete six-row table attains $V$. Consequently
$C_6\ge\max(F,V)$, without an equality assertion.

Proof. Install the following three read and three halt rows:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+1))$ | $S$ | $P$ |
| $S$ | $\operatorname{Read}(2j)$ | $U$ | $Q$ |
| $U$ | $\operatorname{Read}(2(j+3))$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

In phase zero its root edge $\{j+1,j+2\}$ avoids target $j$.
After zero, edge $\{j,j+1\}$ introduces that target and is adjacent
to the first edge. On $00$ the last pair $\{j+3,j+4\}$ is disjoint
from their triple. In phase one every call is a paid separator. The
terminal masses are

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $01$ | $h_0(1-\sigma)$ | $\eta/2$ | $a\eta/2$ | $2$ |
| $001$ | $h_0(\sigma)$ | $t\eta$ | $a^3\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+tc)/2$ | $a/2$ | $3$ |

For $1$, root and target are independent. On $01$, the larger
three-spin completion in order $j,j+1,j+2$ is
$(1-\sigma,\sigma,\sigma)$, with weight $a^2b=a\eta$;
its complement has weight $ab^2$. Their sum is $\eta$, proving
both the label and the phase-weighted masses. On $001$ the first
triple is constant, of probability $t$, independently of the last
one edge, of probability $2\eta$. Correctness requires its constant
spin to be $\sigma$, of probability $a^3$. On $000$ the output
succeeds precisely in phase one with its majority target, of mass $a/2$.

The source masses normalize: since $\eta+c/2=1/2$,

$$
\eta+\frac\eta2+t\eta+\frac{1+tc}{2}
=\frac{3\eta}{2}+\frac{1+t}{2}=1.
\tag{6.2}
$$

Their correct sum is $V$. Every formal input halts, with exact costs

$$
\mathbb P(N=1)=\eta,\quad
\mathbb P(N=2)=\frac\eta2,\quad
\mathbb P(N=3)=1-\frac{3\eta}{2},\quad
\mathbb E N=3-\frac{5\eta}{2}.
\tag{6.3}
$$

The maximum is three and the error is $1-V$. The five-row table is
also admissible at six rows, proving the stated maximum lower bound.
All computations use the actual targets of (1.2). $\square$

**Corollary 6.2 (Full-range comparison of the two lower points).**

$$
\begin{aligned}
V-F&=\frac{a\eta d}{4}(2-3d-d^3),\\
S_3-V&=d\eta\left(\eta+\frac{ac}{2}\right)>0.
\end{aligned}
\tag{6.4}
$$

In particular $C_6>C_5$ whenever $d^3+3d<2$.

Proof. Direct subtraction gives
$V-F=a\eta(1/2+a^2-c-c^2)$. With
$a=(1+d)/2$ and $c=(1+d^2)/2$, the bracket is
$d(2-3d-d^3)/4$. To obtain the other identity, set
$Z_V=a/2+a\eta/2+a^3\eta$, the actual zero-subtree correctness
above. Then

$$
\begin{aligned}
Z-Z_V
&=a\eta\left[a(1+c)-\frac12-a^2\right]
=\frac{ad\eta c}{2},\\
D-a\eta&=d\eta^2.
\end{aligned}
\tag{6.5}
$$

For the first equality of brackets, use
$a-a^2=\eta$ and $\eta-1/2=-c/2$. Since $V=Z_V+a\eta$
and $S_3=Z+D$, (6.4) follows. The function $d^3+3d$ is strictly
increasing from zero to four as $d$ runs from zero to one: for
$d_2>d_1$, its difference is
$(d_2-d_1)(d_2^2+d_2d_1+d_1^2+3)>0$. Thus the strict-gain
condition describes a nonempty interval without a sampled comparison.
It compares attained points and does not evaluate $C_6$. $\square$

## 7. A fully costed seven-row attained point

**Proposition 7.1 (A disjoint target pair and its paid join).** Seven
installed rows attain

$$
W:=Z+a\eta=S_3-d\eta^2.
\tag{7.1}
$$

Hence $C_7\ge W$. Throughout the entire stipulated range,

$$
W-F=2d\eta^2(1-\eta)>0,\qquad
W-V=\frac{ad\eta c}{2}>0.
\tag{7.2}
$$

Proof. Install these four read and three halt rows:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+2))$ | $S$ | $P$ |
| $S$ | $\operatorname{Read}(2j)$ | $A_0$ | $B$ |
| $A_0$ | $\operatorname{Read}(2(j+4))$ | $Z_H$ | $P$ |
| $B$ | $\operatorname{Read}(2(j+1))$ | $Q$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

In phase zero root $\{j+2,j+3\}$ avoids target $j$. After zero,
the pair $\{j,j+1\}$ contains the target and is disjoint from the
root. On $00$, pair $\{j+4,j+5\}$ is disjoint from both. On
$01$, edge $\{j+1,j+2\}$ joins the first two pairs. Phase one
again sees only paid separators. The full terminal law is

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $000$ | $h_1(\sigma)$ | $(1+c^3)/2$ | $a/2$ | $3$ |
| $001$ | $h_0(\sigma)$ | $c^2\eta$ | $a^2c\eta$ | $3$ |
| $010$ | $h_0(1-\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |
| $011$ | $h_0(\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |

The first record uses independence of root and target. On $001$, the
target pair must be constantly majority, contributing $a^2$; the other
zero pair contributes $c$ and the final one pair contributes $2\eta$,
with phase factor $1/2$. On $000$, success is the phase-one
majority-target event alone.

For the joining leaves $010,011$, the larger completions in order
$j,j+1,j+2,j+3$ are, respectively,

$$
(1-\sigma,\sigma,\sigma,\sigma),\qquad
(\sigma,1-\sigma,\sigma,\sigma).
\tag{7.3}
$$

Each has weight $a^3b$, its complement has weight $ab^3$, and their
sum is $ab(a^2+b^2)=c\eta$. This proves their labels, whole
source masses and correct masses after the phase factor. The source
sum is
$\eta+c\eta+c^2\eta+(1+c^3)/2=1$.
The correct sum is $a/2+a^2c\eta+a^2\eta+a\eta=Z+a\eta=W$.
The identity $D-a\eta=d\eta^2$ from (6.5) gives (7.1).

Every formal path halts after one call on $1$ and three on $0$.
Thus its exact cost law is

$$
\mathbb P(N=1)=\eta,\qquad
\mathbb P(N=3)=1-\eta,\qquad
\mathbb E N=3-2\eta,
\tag{7.4}
$$

with maximum three and error $1-W$. Subtract its deficit $d\eta^2$
from (5.2) and (6.4) to obtain (7.2). Their factors are positive.
This establishes a common-source attained lower point, with every
output distinction paid for in the three halt rows. It supplies no
universal matching seven-row upper bound. $\square$

## 8. A fully costed eight-row attained point

**Proposition 8.1 (A complementary allocation of the last read).**
Eight installed rows attain

$$
X_{\star}:=S_3-\frac{ad\eta c}{2}.
\tag{8.1}
$$

Consequently $C_8\ge\max(W,X_{\star})$. The two attained points compare by

$$
X_{\star}-W=\frac{ad\eta}{2}(1-2a^2).
\tag{8.2}
$$

Thus $X_{\star}>W$ exactly for $a<1/\sqrt2$, with equality at
$a=1/\sqrt2$. This compares constructions, rather than the unknown
optima $C_7,C_8$.

Proof. Install these five read and three halt rows:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2(j+1))$ | $R_0$ | $R_1$ |
| $R_0$ | $\operatorname{Read}(2j)$ | $A_0$ | $Q$ |
| $R_1$ | $\operatorname{Read}(2(j-1))$ | $P$ | $B$ |
| $A_0$ | $\operatorname{Read}(2(j+3))$ | $Z_H$ | $P$ |
| $B$ | $\operatorname{Read}(2(j-2))$ | $Q$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

Its zero subtree uses exactly the actual edge geometry and outputs of
Proposition 6.1. On first one, root pair $\{j+1,j+2\}$ is
disjoint from pair $\{j-1,j\}$, which contains the target. On $11$,
edge $\{j-2,j-1\}$ is a fresh extension of that target pair,
outside the root pair. Every address, including each negative literal,
is an actual charged coordinate. Phase one sees only separators.

With $t=1-3\eta$, the full terminal accounting is

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $01$ | $h_0(1-\sigma)$ | $\eta/2$ | $a\eta/2$ | $2$ |
| $001$ | $h_0(\sigma)$ | $t\eta$ | $a^3\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+tc)/2$ | $a/2$ | $3$ |
| $10$ | $h_0(\sigma)$ | $c\eta$ | $a^2\eta$ | $2$ |
| $110$ | $h_0(1-\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |
| $111$ | $h_0(\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |

The first three rows have the proofs in Proposition 6.1. On $10$,
the disjoint root one has conditional probability $2\eta$ and the
target zero pair has probability $c$; correctness uses its weight
$a^2$. On $110,111$, the larger local triples in order
$j-2,j-1,j$ are, respectively,

$$
(\sigma,\sigma,1-\sigma),\qquad
(\sigma,1-\sigma,\sigma).
\tag{8.3}
$$

Each has weight $a^2b$, its complement has weight $ab^2$, and the
independent root one contributes probability $2\eta$. Each whole leaf
therefore has mass $\tfrac12\eta(2\eta)=\eta^2$ and correct mass
$\tfrac12(a^2b)(2\eta)=a\eta^2$, with the target spins shown.

The first-one source mass is $c\eta+2\eta^2=\eta$ and its
correct mass is $D$. The zero subtree has source mass $1-\eta$
by (6.2) and correct mass $Z_V$. The complete law is therefore
normalized, and its correct sum is $Z_V+D$. Equation (6.5) identifies
this as $X_{\star}$. The seven-row table remains admissible at budget eight,
giving the maximum lower bound.

Every formal path halts after two or three calls. Its exact cost is

$$
\begin{aligned}
\mathbb P(N=2)&=\eta(c+1/2),\\
\mathbb P(N=3)&=1-\eta(c+1/2),\\
\mathbb E N&=3-\eta(c+1/2).
\end{aligned}
\tag{8.4}
$$

The maximum is three and its error is $1-X_{\star}$. Finally,
$X_{\star}-W=d\eta(\eta-ac/2)$, and
$\eta-ac/2=(a/2)(2b-c)=(a/2)(1-2a^2)$, proving (8.2) and
its full-range sign statement. Constant initialization, the actual target
indices, and the same majority convention give both endpoints and bias
directions without any extra runtime distinction. $\square$

## 9. The inherited nine-row tail of the frontier

**Proposition 9.1 (Inherited realization, with its paid costs).** For
every $m\ge9$ one has $C_m=S_3$. The following is [Three Read,
Definition 12.2][E3] with first parity zero:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $\operatorname{Read}(2j)$ | $R_0$ | $R_1$ |
| $R_0$ | $\operatorname{Read}(2(j+2))$ | $A_0$ | $P$ |
| $R_1$ | $\operatorname{Read}(2(j+2))$ | $B$ | $C$ |
| $A_0$ | $\operatorname{Read}(2(j+4))$ | $Z_H$ | $P$ |
| $B$ | $\operatorname{Read}(2(j+1))$ | $Q$ | $P$ |
| $C$ | $\operatorname{Read}(2(j-1))$ | $P$ | $Q$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

Proof. The inherited unrestricted theorem bounds every installed table
by $S_3$. For completeness, the displayed actual attainer's terminal
law and costs are

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $000$ | $h_1(\sigma)$ | $(1+c^3)/2$ | $a/2$ | $3$ |
| $001$ | $h_0(\sigma)$ | $c^2\eta$ | $a^2c\eta$ | $3$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $a^2\eta$ | $2$ |
| $100$ | $h_0(1-\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |
| $101$ | $h_0(\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |
| $110$ | $h_0(\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |
| $111$ | $h_0(1-\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |

In phase zero, $000,001$ use the three disjoint pairs beginning
at $j,j+2,j+4$. On $01$ the target zero pair and distant one pair
are disjoint; the target-majority weight is $a^2$. For $100,101$,
edge $\{j+1,j+2\}$ joins the one pair $\{j,j+1\}$ to the
zero pair $\{j+2,j+3\}$. The two heavier completions have weights
$a^3b$, and complements $ab^3$, with target spins $1-\sigma$
and $\sigma$ respectively. Hence each source mass is $c\eta/2$
and each correct mass $a^2\eta/2$.

On $110,111$, the local triples in order $j-1,j,j+1$ are
$(\sigma,\sigma,1-\sigma)$ and
$(\sigma,1-\sigma,\sigma)$ in their heavier completions. Each
has weight $a^2b$, while the independent one pair beginning at $j+2$
has probability $2\eta$. This proves the last two masses and labels.
In phase one every call is a separator; its only record is $000$,
whose correct contribution is $a/2$. Thus all entries concern one
source with its unchanged target.

The two first-reply source sums are $1-\eta$ and $\eta$; the
correct sums are $Z$ and $D$. They give total correct mass $S_3$.
The table has six distinct read rows and three distinct halt rows.
Rows $R_0,R_1$ share an address literal but have different successors
and remain separate installed states. It halts on every formal input,
with

$$
\mathbb P(N=2)=c\eta,\qquad
\mathbb P(N=3)=1-c\eta,\qquad
\mathbb E N=3-c\eta.
\tag{9.1}
$$

This inherited table attains the upper bound at every $m\ge9$.
Its nine-row minimality is the inherited $M_3=9$ theorem, rather than
a new conclusion of this proposition. $\square$

## 10. A finite menu preserving installed rows and the whole stopped law

**Theorem 10.1 (Row-preserving finite representatives).** For every
finite $m\ge1$ and either fixed endpoint $j$, there is a finite menu
of deterministic-initialized actual installed controllers with at most
$m$ rows, chosen independently of $p$ and $\nu$, with these properties.
Every deterministic start in any table of at most $m$ rows has a menu
representative with the same joint law of the actual $H_j$, output or
nonreturn, finite-return indicator, and exact $N$, including $N=\infty$.
The representation preserves all installed row identities, instruction
types, halt labels and fixed successors; only the integer address
literals may change.

More strongly, for an arbitrarily seed-initialized table there is one
representative table with the same rows and the same initialization
map under the row identification, preserving the joint law with every
measurable seed event. No hard read cap or return assumption is needed
for these preservation assertions. They preserve neither literal address
names nor numerical return times.

Proof. Label a table's $n\le m$ installed rows by $1,\ldots,n$,
keeping all rows, including unused, duplicate and null-path rows.
There are finitely many choices of each row's read/halt type, each
halt's four-state label, and each read's two successors. Fix such a
combinatorial table. Its remaining infinite choices are the integer
read literals $t_r$.

Record the parity $\epsilon_r$ of each read row. For each phase
$\phi$ introduce the finite slot set

$$
\mathcal I_\phi=\{*\}\cup
\{(r,-),(r,+):r\in K_{\rm R},\ \epsilon_r=\phi\}.
\tag{10.1}
$$

An actual address assignment gives these slots the spin indices

$$
\iota_\phi(*)=v_\phi,\quad
\iota_\phi(r,-)=\frac{t_r-\phi}{2},\quad
\iota_\phi(r,+)=\frac{t_r-\phi}{2}+1.
\tag{10.2}
$$

Its signature consists of the labelled combinatorial table, all read
parities and the two equivalence relations of equality of these actual
indices, with each target slot distinguished. There are finitely many
signatures: each slot set is finite and has finitely many partitions.
Retain only signatures realized by one joint assignment of actual
integer literals in both phases with the actual fixed $v_0,v_1$.
For each retained signature choose one such joint realization.
This is a finite selection from nonempty realization sets. It does not
assume that arbitrary pairs of abstract partitions can be embedded in
the integer line. Realizability and the choice involve integer geometry,
$m,j$, not $p$ or the seed law.

Conditional on phase $\phi$, assign one independent Bernoulli$(p)$
spin to each equivalence class of $\mathcal I_\phi$. The target is
$h_\phi$ of the star-class spin. At a read row of parity $\phi$
the static potential reply is the XOR of its two class spins; at every
other read row it is zero. Therefore the signature determines the joint
conditional law of the actual target and all installed read rows'
potential replies, including replies at rows on incompatible paths.
Equal spin indices are identified, and distinct ones use the original
iid law. This is precisely the distribution of (1.1), even for remote
or negative indices. Combine the two phase alternatives with their
original weights $1/2$. The representative uses the same single joint
integer placement that realizes both relations; no independently
optimized phase placements are spliced.

For a fixed potential-reply vector, the installed successor map and
initial row determine the whole state trajectory. Either it reaches a
halt, fixing its output and exact number of calls, or it reads forever.
Repeated visits still incur calls and use the same potential reply.
Thus the joint law of target and the vector determines the entire
stopped law claimed in the theorem. The selected representative retains
the same labelled rows, successor map and halt labels, so it preserves
that law from every possible initial row simultaneously. In particular
it does not unfold a row into separate occurrences, merge equal literal
instructions, delete an unused row, or add a program position.

To state the seed assertion precisely, put $O=A$ on return and
$O=\bot\notin\mathcal A$ on nonreturn, and let
$D_0=\mathbf1_{\{\tau<\infty\}}$. Denote the common deterministic
start law at row $r$ by $v_r$. For every $B\in\mathcal U$ and
every subset $G$ of the countable alphabet of $(H_j,O,D_0,N)$,

$$
\mathbb P\bigl(u\in B,(H_j,O,D_0,N)\in G\bigr)
=\sum_{r\in K}\nu(B\cap c_{\rm init}^{-1}\{r\})v_r(G).
\tag{10.3}
$$

Independence and seed use only at initialization prove this identity.
Keeping the initialization map and all common $v_r$ proves joint
preservation with the original seed. No atomlessness, added coin or
disintegration on singleton seeds is involved. Lastly include each
possible deterministic initial row for each finite selected table in
the menu. It is finite and proves the deterministic assertion as well.
$\square$

**Theorem 10.2 (Bias-independent feasibility and attained finite
maximum).** The $q_3=1$ members of the menu in Theorem 10.1 form a
nonempty finite menu independent of the interior bias $p$. For a
deterministic member $i$ its correct mass $P_i(p)$ is a polynomial
in $p$ of degree at most $2m+1$. For every stated $p,j$ and every
unchanged independent seed law,

$$
C_m(p,j,\nu)=\max_{i\text{ feasible}}P_i(p).
\tag{10.4}
$$

In particular the optimum is attained by constant initialization and
is independent of $\nu$. The finite maximum need not be one polynomial
over the whole parameter range.

Proof. In either phase the number of equivalence classes in (10.1) is
at most $1+2|K_{\rm R}|\le2m+1$. Every assignment to those classes
has strictly positive probability for every $0<p<1$. Hence an actual
fixed deterministic-start representative has $q_3=1$ exactly when
every class-spin assignment in each phase halts within three calls.
A failing assignment would have positive phase-weighted probability;
if none fails, all source possibilities are covered. This support
criterion is independent of $p$. It leaves all impossible reply vectors
and their arbitrary cycles outside the support. An immediate halt shows
that the feasible menu is nonempty.

For a feasible member, sum over those assignments producing a correct
label. An assignment to $s$ classes with $k$ ones has weight
$p^k(1-p)^{s-k}$, with phase factor $1/2$. A finite sum of these
terms in the two phases is a polynomial of degree at most $2m+1$.
The menu has fixed literal labels, so it is independent of $p$ even
when the maximizing member changes with the majority spin.

Now take any original initialized table with $q_3=1$. Lemma 3.1
makes each positive initialization cell a feasible deterministic start.
Theorem 10.1 represents its law by a feasible menu member. Its averaged
correctness cannot exceed the largest such member's correct mass.
Conversely a maximizing member can be initialized constantly on the
given unchanged seed space. This proves (10.4) and attainment. No
convexification of seed weights has been used. The argument is a finite
existence proof; it supplies no executed enumeration, effective address
radius or procedure deciding arbitrary seed events. $\square$

**Corollary 10.3 (Strict separation below nine rows).** For every
fixed $0<p<1$, $p\ne1/2$, either endpoint and each $m\le8$,

$$
C_m<S_3.
\tag{10.5}
$$

Proof. The inherited unrestricted bound gives $C_m\le S_3$.
Theorem 10.2 attains $C_m$ by an actual complete table. Equality
would therefore give an $S_3$ attainer with at most eight installed
rows, contradicting [Three Read, Theorem 12.4][E3]'s $M_3=9$.
Both attainment and the inherited minimum are necessary for this
argument: nonattainment alone does not exclude a supremum equal to
$S_3$. This establishes a strict gap at each fixed stated parameter.
It does not evaluate its size at six, seven or eight rows or give a
uniform positive gap toward excluded parameter limits. $\square$

## 11. Ownership, proved region and exact remaining target

**Attribution 11.1 (Canonical mathematical owners).** The source
relationships used in this volume are as follows.

| Owner | Exact inherited content |
| --- | --- |
| [Original: fixed-state tail nonuniformity and erasure-risk jump][O], Proposition 2.1, (2.2), Definition 9.1 and (9.4) | Original stationary law, separator clock, actual endpoint indices and full arbitrary-address paid protocol. |
| Original, Lemma 3.1 and Sections 8–11 | Complementary finite products, endpoint measurability, terminal-section bounds, zero-record results and the overlapping one-read optimum. Half-line measurability grants no runtime read here. |
| Original, Sections 12–14 | Finite whole-reply-tree signatures and same-seed stopped-law representation for a hard paid-read cap. These do not by themselves preserve an installed row graph. |
| [Paid Risk: return mass and endpoint classification][P], Sections 1–5 | Same source and paid contract, terminal masses, one-read return-mass envelope and its seed-event criterion, one-read optimum, and finite probe/local-block cost family. |
| [Two Read: exact almost-sure endpoint risk][E2], Theorem 6.1 and Section 8 | Unrestricted two-read value, literal complete-controller convention, initialization averaging, equality rigidity and the minimum three/six-row costs for attaining the one/two-read optima. |
| [Two Installed: exact two-read installed frontier][I2], Theorems 6.1 and 10.1, Section 9 | Quantitative at-most-two-read-row bound $T$, the full two-read installed frontier, and its actual three/four/six-row tables. |
| [Three Read: exact almost-sure endpoint risk][E3], Sections 3–7 and 9–12 | Unrestricted $S_3=Z+D$, component and equality comparisons, all optimal-policy sharing obstruction, actual nine-row attainer and exact minimum $M_3=9$. |

The new bounds in Sections 4–5 concern three paid reads under small
installed budgets. In particular the four-row attainer is inherited,
while its optimality against all three-read four-row competitors is a
new conclusion here. The two-label bound and the five-row table provide
a matched new quantitative value. Sections 6–8 supply new common-source
attained points with all runtime states and paid costs. Section 10
changes the signature carrier from reply-tree occurrences to installed
rows, retaining fixed successors and every start law; this is the
additional ingredient proving installed-budget attainment. These results
are `repo-derived` ordinary consequences and proofs relative to the
listed sources. No new literature search or exhaustive originality
claim is asserted. Nested references in those owners supply no additional
premise of this volume.

**Proposition 11.2 (The proved partial frontier).** With
$F,V,W,X_{\star}$ defined in (4.1), (6.1), (7.1), (8.1), the known region
is

| Installed budget | Proved correct-mass conclusion | Evidence for equality or boundary |
| --- | --- | --- |
| $1,2$ | $C_m=a/2$ | Universal row split and immediate halt |
| $3$ | $C_3=S_1$ | Universal row split and three-row table |
| $4$ | $C_4=T$ | Actual-table no-revisit bound and four-row table |
| $5$ | $C_5=F$ | Universal two-label bound and five-row table |
| $6$ | $\max(F,V)\le C_6<S_3$ | Actual lower tables; finite attainment and inherited $M_3=9$ |
| $7$ | $W\le C_7<S_3$ | Actual seven-row table; same strict-separation argument |
| $8$ | $\max(W,X_{\star})\le C_8<S_3$ | Actual lower tables; same strict-separation argument |
| $m\ge9$ | $C_m=S_3$ | Inherited unrestricted bound and nine-row attainer |

All $C_m$ are attained, all $R_m=1-C_m$ are attained minima, and
$C_6\le C_7\le C_8$.

Proof. The equalities are Theorem 5.4 and Proposition 9.1. The actual
lower points are Propositions 6.1, 7.1 and 8.1; (7.2) shows that $W$
already dominates $F,V$. Theorem 10.2 gives attainment and Corollary
10.3 gives the strict upper comparisons. Budget inclusion gives
monotonicity. Complementation on $q_3=1$ gives the risk assertions.
$\square$

**Open Problem 11.3 (The remaining original installed target).**
Determine the exact attained $C_m$ at each $m=6,7,8$ throughout
$0<p<1$, $p\ne1/2$, for both actual original endpoints, the same
arbitrary unchanged independent seed law, and exactly the complete
runtime interface in Definition 2.1. Completion requires quantitative
upper bounds for every actual table at those budgets, matched by
complete actual-source attainers for every winning parameter branch.
The equations

$$
C_6=\max(F,V),\qquad C_7=W,\qquad C_8=\max(W,X_{\star})
\tag{11.1}
$$

are not established here and are not assumed completion criteria. The
finite menu has unevaluated members and does not certify those guesses.

A middle-budget upper proof must retain actual row-indexed successor
closure. Shared rows force the same instruction and both successors at
every reaching positive section. Distinct rows may have identical
address literals, as $R_0,R_1$ do in Section 9. Unrestricted tree
unfolding, address representatives that forget rows, separately optimized
branch maxima, and $M_3=9$ alone do not supply matching quantitative
upper bounds. The finite-menu theorem preserves these constraints but
does not optimize the remaining members.

**Boundary 11.4 (Exact scope and proof status).** The displayed tables
halt on every formal binary input, whereas all universal installed bounds
retain the larger almost-sure competitor class with its exceptional
nonreturn and excess-read paths, null cycles and unused rows. Labels
and rows remain distinct resources: two distinct labels may have many
duplicate halt rows, and a repeated read literal may occupy different
rows with different updates. Every actual call remains paid. The
reported expectations are costs of the displayed tables, without an
expected-cost optimality claim.

This volume does not determine a $q_3<1$ frontier, a larger paid-read
optimum, fair or endpoint parameters, or a frontier with another runtime
memory port. Installed row counts give no physical-storage, code-size,
write, energy, timing or empirical learning conclusion. Four-state
classification supplies no Brier theorem and leaves Original, Open
Problem 6.4, concerning whole-domain harmonic/Brier attainment and
separation, unchanged. Ordinary proofs are the evidence here; no
mathematical execution, numerical enumeration, experiment, test, Lean
verification or digestion result is asserted. The substantive partial
frontier leaves exactly the quantitative installed budgets six, seven
and eight as stated in Open Problem 11.3.

[O]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[P]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md
[E2]: FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md
[I2]: FIB_TWO_READ_INSTALLED_STATE_RISK_FRONTIER.md
[E3]: FIB_THREE_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md

## 追加锚（本行以下为增补区）
