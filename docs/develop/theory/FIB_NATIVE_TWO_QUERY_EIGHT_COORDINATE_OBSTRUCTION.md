# Fibonacci native two-query eight-coordinate obstruction

A complete normalized eight-coordinate $N$ law satisfying all event
rows at $b_i,e\in[0,1]$ can be extended by an ignored ninth input
whose auxiliary amplitude equals the cap. The same law then satisfies
every nine-coordinate row. Applying the existing $Y_{128}$ theorem
gives the eight-coordinate inequality

$$
2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8\le2+117e,
$$

or equivalently $g\le2s$ for the residuals defined below. On the
positive-width family of Theorem 5.1 this yields
$e_a(A)\ge r_0+4\delta/117$ for every original $\mathcal N_2$
and $\mathcal O_2$ competitor, with every positive ordered vanishing
continuation satisfying $a_9\le a_8$. The ninth input in the finite
proof does not replace the original ninth amplitude. The supporting
score is credited to XVIII318.1–318.2; the contribution here is its
complete extension, prefix transport and application.

## 1. Original source, targets and requests

**Definition 1.1 (Arithmetic source and full carrier).**
Let $F_0=0$, $F_1=1$, $F_{k+2}=F_{k+1}+F_k$, and let $p_i$
be the increasing primes. The countable source and its static replies are

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=[p_i\mid N(x)],\qquad
n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
\tag{1.1}
$$

The full carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with
each block a copy of $(0,1)$. There are no blocks indexed by zero.
The unchanged consumer returns unknown on $B_j$ and proposes $j$
on $P_j$, without making prime requests. The distinct marks

$$
\theta_j=(B_1,1/(j+2)),\qquad j\ge0,
$$

all belong to the existing block $B_1$.

Fix an entire sequence $1\ge a_1\ge a_2\ge\cdots>0$ with
$a_n\to0$. The selected marked targets and error are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a).
\tag{1.2}
$$

The original nonatomic targets remain
$\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$:
$h_0\in(0,1)$, $t_x=\sum_{i\ge1}3^{-i}q_i(x)$,
$Z_t=\int_0^1e^{tu}\,du$, $\nu_x$ has density $e^{t_xu}/Z_{t_x}$
on $B_{n(x)}$, $\pi_j$ is uniform on $P_j$, and $\Omega(x)$
counts distinct prime divisors of $N(x)$. They assign zero mass to
every finite set of marks. Thus a finite marked law has TV distance
one from each such nonatomic target. All accuracy conclusions here
concern (1.2). These objects are those of
[XVII297.1 and 309.1, revision `07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d`](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and
[XVIII315.1, revision `24e09b5c`](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md).

**Definition 1.2 (Hard bound on actual requests).**
An original rule has zero advice, one source-independent common seed
and sourcewise almost-sure finite handoff to the unchanged consumer.
Its information about the source consists of its requested replies;
there is no supplied source label, integer $N(x)$, first absence or
extra observation. In $\mathcal N_2$ its entire schedule is
preselected before replies and all scheduled replies are obtained.
In $\mathcal O_2$ an increasing schedule is preselected before
replies and execution stops at its first **queried** zero or
exhaustion. Its second address cannot depend on its first reply.
Both classes permit at most two actual requests, including repeated
requests and ignored replies. Competitors retain arbitrary addresses
and arbitrary Borel outputs in $\Theta$. There is no source
distribution, address bound, runtime bound or mean-request relaxation.
These are the conventions of
[XVII297.2 and 309.1](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and XVIII315.1 at the revisions just specified.

Completing an $O$ schedule on the same source and seed, obtaining
its entire preselected schedule and reconstructing the stopped output,
gives an $N$ rule with identical output laws. Any ignored second
request is counted. No converse transformation preserving an arbitrary
starting $N$ law is assumed.

**Reused source fact 1.3 (Every finite pattern is actual).**
Use the finite-pattern premise expressly supplied in
[XVII297.3 and 309.3](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and
[XVIII315.3](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md),
which credit Proposition 280.1. Its supplied argument works on the
actual source (1.1). Modulo a prime $p$, the invertible Fibonacci
matrix $Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$
has $Q^k$ scalar exactly when $p\mid F_k$. Its projective order
$z(p)\ge3$ therefore gives $p\mid F_k$ iff $z(p)\mid k$.
For finitely many prescribed primes, choose a sufficiently large
prime index $r$ exceeding all their ranks. None of those ranks divides
$r$, so $F_r$ is invertible modulo their product $D$.
Prescribe $g\equiv-F_r^{-1}\pmod p$ at each desired one and
$g\equiv0\pmod p$ at each desired zero. CRT supplies a residue
modulo $D$, and for large $r$ the legal interval for the integer
$g$ contains $D$ consecutive integers. It contains a legal
representative. Hence every finite word, including all multiple-zero
words and positive prefixes, has an actual witness. Each actual
positive integer $N(r,g)$ has finitely many prime divisors, so every
actual first absence is finite. A positive finite prefix denotes later
actual zeros, not an infinite all-positive source.

## 2. Complete finite laws and the credited supporting theorem

**Definition 2.1 (One normalized allocation and all rows).**
For an integer horizon $L\ge0$, let $\mathcal W_L=\{0,1\}^L$,
$+=1^L$, and $\Omega_n=\{w:\min\{i:w_i=0\}=n\}$.
The complete $N$ catalog contains constants, singletons and every
four-cell table $N(i,j;u_{00},u_{01},u_{10},u_{11})$, $1\le i<j\le L$,
with each output independently allowed in $\{0,\ldots,L\}$.
Every earlier or unqueried label remains legal. Reversal permutes
cells; repetition supplies singleton information without refunding an
actual request. At horizon zero there is only the empty input and
label zero.

One normalized allocation is one vector $\lambda_D\ge0$ with
$\sum_D\lambda_D=1$. It determines

$$
p_w(\ell)=\sum_D\lambda_D[D(w)=\ell].
\tag{2.1}
$$

Each complete table has its same mass in every counterfactual cell;
this same $\lambda$ supplies every word. There is no separate
wordwise or cellwise choice of law. At profile $(b_1,\ldots,b_L;e)$,
retain separately every row

$$
\begin{aligned}
p_w(0)&\ge1-b_n-e &&(A_w),\\
p_w(n)&\ge b_n-e &&(C_w),\\
p_w(0)+p_w(n)&\ge1-e &&(P_w),\qquad w\in\Omega_n,\\
p_+(0)&\ge1-e &&(\text{positive row}).
\end{aligned}
\tag{2.2}
$$

The three zero-word events are $\{0\},\{n\},\{0,n\}$.
Every unscored constraint and every negative singleton demand is
retained literally. For $0\le b_n\le1$ their deficits satisfy

$$
\operatorname{TV}(p_w,(1-b_n)e_0+b_ne_n)
 =\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{2.3}
$$

For general real profiles the rows instead define affine feasibility,
without asserting a probability target outside that interval.
The full-row conventions are
[XVII297.4–297.5 and 309.1–309.2](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and
[XVIII315.2](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md).

**Reused theorem 2.2 ($Y_{128}$ at its full affine scope).**
The score, complete support certificate and theorem belong to
[XVIII318.1–318.2, revision `24e09b5c`](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md#318-a-seven-late-lower-certificate-for-an-attained-family).
Its invariants on nine coordinates are

$$
\begin{gathered}
\beta=(0,16,88,104,104,96,88,88,88),\qquad K=1024,\\
W=B_N=B_O=368,\qquad \Delta_N=\Delta_O=0.
\end{gathered}
\tag{2.4}
$$

To specify its broad domain, let $d(b,e)$ be the full demand vector
in (2.2), $z_D$ the full event-incidence vector of a deterministic
table, $R=O(1,2;1,2,0)$, $\alpha=(1,1,0,\ldots,0)$,
$r=z_R=d(\alpha,0)$ and $G_N=(z_D-r)_D$.
Here $O(i,j;u,s,t)$ gives the outputs on stopped cells $0,10,11$,
so $R$ emits 1 when its first reply is zero, 2 after $10$, and 0
after $11$.
For every $L\ge9$, every ordered
$3\le j_1<\cdots<j_7\le L$, every real $(b,e)$ and one
complete feasible allocation

$$
\lambda\ge0,\qquad G_N\lambda\ge d(b,e)-r,\qquad
M=\sum_D\lambda_D<\infty,
$$

the theorem gives

$$
2b_2+11b_{j_1}+13b_{j_2}+13b_{j_3}+12b_{j_4}
 +11b_{j_5}+11b_{j_6}+11b_{j_7}\le2+128e.
\tag{2.5}
$$

The same is true in the complete $O$ catalog. This finite affine
theorem requires neither normalization, order, $b_i\ge e$, an
auxiliary hull, nor the attained-family hypotheses of XVIII321.1.
At mass one its allocation condition is exactly (2.2).

The owning theorem's 46-row score and complete support proof cover
all ten labels in every pair cell, constants, singletons, repeated
and reversed schedules, and every ordered embedding. On the embedded
scored support, outside queries are constant and outside labels earn
zero. All unscored constraints remain. Its nonnegative score pairing
with the same complete allocation gives

$$
Y_{128}(d(b,e)-r)\le M\Delta_N=0;
$$

the left side is eight times the left-minus-right expression in
(2.5). No division by $M$ is made. This is the credited supporting
result used below, with its support certificate retained at its owning
source.

## 3. An inactive ninth coordinate under the same law

**Lemma 3.1 (Complete extension without a new request).**
Let one normalized complete eight-bit $N$ allocation satisfy (2.2),
with $0\le b_i\le1$ and $0\le e\le1$. There is a complete
nine-bit allocation with identical table weights, schedules and old
outputs at profile $(b_1,\ldots,b_8,e;e)$.

**Proof.** For every complete table set

$$
D'(w,v)=D(w),\qquad w\in\{0,1\}^8,\quad v\in\{0,1\}.
\tag{3.1}
$$

Retain its weight $\lambda_D$ and its whole schedule. The law still
has mass one, all outputs lie in $\{0,\ldots,8\}\subseteq\{0,\ldots,9\}$,
and
$p'_{(w,v)}(\ell)=p_w(\ell)$ for $\ell\le8$, while
$p'_{(w,v)}(9)=0$. Put $b'_9=e$ and $b'_i=b_i$ for $i\le8$.
If $w$ already has first zero $n\le8$, either value of $v$
leaves its first zero and target amplitude unchanged. Each old
$A,C,P$ probability and demand is copied exactly, including every
multiple-zero suffix.

For the new first-zero word $1^8 0$, write $q=p_+(0)\ge1-e$.
Its complete row verification is

$$
\begin{array}{c|ccc}
\text{event}&A& C& P\\\hline
\text{probability}&q&0&q\\
\text{demand}&1-2e&0&1-e
\end{array}
\tag{3.2}
$$

Since $e\ge0$, $q\ge1-e\ge1-2e$, so all three rows hold
separately. The positive word $1^9$ retains $q\ge1-e$.
Equivalently the new first-zero TV is $\max\{1-q,e\}\le e$.
The existing positive row supplies the new independent union row;
correct singleton probabilities alone would not supply it.

The auxiliary amplitude $b'_9=e$ is boxed and inactive under the
strict convention $b_i>e$. At $e=0$ the positive row forces $q=1$;
at $e=1$ the new demands are $(-1,0,0)$. Old inactive ties and
negative singleton demands remain unchanged. No condition $b_8\ge e$
or ordering of the extended profile is used.

Input nine is never requested. Constants, singletons and repeated
schedules retain their original requests, and a full pair retains its
same two requests. There is no need to pad a schedule. Selection of
the complete table by the same seed preserves source independence,
zero advice and finite handoff; ignored and repeated requests remain
counted. This is an extension of the same complete law, with no
recoupling of counterfactual cells. It asserts no unchanged-profile
extension for arbitrary conic mass. $\square$

**Theorem 3.2 (The eight-coordinate consequence of $Y_{128}$).**
For every normalized complete eight-bit $N$ allocation satisfying
all rows (2.2), with $b_i,e\in[0,1]$,

$$
2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8\le2+117e.
\tag{3.3}
$$

**Proof.** Apply (2.5) with $L=9$ and consecutive late addresses
to the actual complete extension of Lemma 3.1. Its last amplitude
is $b'_9=e$. Subtracting $11e$ from the right and left sides of
the resulting nine-coordinate inequality gives (3.3).
The extension supplies all rows with one law before the theorem is
applied. $\square$

**Residual form 3.3 (One inequality in two coordinates).**
For the same eight-bit profile define

$$
\begin{aligned}
S&=b_3+b_4+b_5+b_6+b_7+b_8,\\
s&=1+44e-b_2-4b_3-5b_4-5b_5-5b_6-4b_7-4b_8,\\
g&=3S-b_6-29e.
\end{aligned}
\tag{3.4}
$$

Here $g$ is an affine residual, unrelated to the source integer
in (1.1). The existing six-late score $Z_6$ and its support 68 in
[XVII305.1–305.2](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md#305-a-six-late-integer-score-and-the-saturated-head-tail-boundary)
give $s\ge0$. Direct expansion gives

$$
g-2s=2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8-2-117e.
$$

Consequently (3.3) is exactly $g\le2s$, including its face
$s=0\Rightarrow g\le0$. These are formulations of the same
application of $Y_{128}$, rather than separate supporting results.

## 4. Transport from every positive original cap

**Reused correspondence 4.1 (Finite class feasibility).**
Use exactly the closed-cap correspondence and prefix premise stated in
[XVII297.3 and 309.3](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and
[XVIII315.3](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md),
including their expressly cited Theorem 110.2 and Lemma 280.3.
At a met positive closed cap $0<E\le1$, every original $N$ rule
has some normalized complete finite representative on

$$
H=\max(\{i:a_i>E\}\cup\{0\}).
\tag{4.1}
$$

This premise includes arbitrary original addresses and full-carrier
outputs. Its supplied necessity uses countability for one probability-one
seed event of termination at every source, control of the whole
preselected schedule, actual finite witnesses, truncation and
finite-simplex compactness. It supplies class feasibility and does not
preserve an arbitrary starting output law or coupling. Vanishing of
$a$, with no summability requirement, makes $H$ finite.

**Proposition 4.2 (The eight-bit cut at every original error).**
For every entire sequence (1.2) and every original competitor $A$
in either class,

$$
2a_2+11a_3+13a_4+13a_5+12a_6+11a_7+11a_8
 \le2+117e_a(A).
\tag{4.2}
$$

**Proof.** First let an original $N$ rule meet $0<E\le1$ and
take the representative of 4.1. We obtain one complete normalized
eight-bit representative as follows.

If $H>8$, in each table fix every higher represented reply to zero,
project each label above eight to zero, and contract the resulting
constant observations. The same table weights supply the whole
restricted law, with at most two variable observations. On a low
first-zero word $n\le8$, projection leaves its target
$(1-a_n)e_0+a_ne_n$ unchanged, and TV contracts. Thus every
$A,C,P$ row survives, for every suffix. On the positive eight-prefix
the fixed higher bits give first zero nine. Its target projects to
$e_0$, so TV contraction gives $p_+(0)\ge1-E$. This verifies
the positive row regardless of the size of the actual $a_9$.
If $H=8$, use the representative itself.

If $H<8$, ignore the added input bits and retain the old outputs.
All old first-zero rows are unchanged. At each added first zero
$n>H$ its law is the old positive law $p_+$, supported on labels
at most $H$. Since its only possible overlap with the target is
at zero, the exact identity is

$$
\operatorname{TV}(p_+,(1-a_n)e_0+a_ne_n)
 =1-\min\{p_+(0),1-a_n\}
 =\max\{1-p_+(0),a_n\}\le E.
\tag{4.3}
$$

Here $a_n\le E$ and $p_+(0)\ge1-E$. In row terms,
$p_+(0)\ge1-a_n-E$, $p_+(n)=0\ge a_n-E$ and
$p_+(0)+p_+(n)\ge1-E$. These separately verify the base,
correct and independent union events. The positive row persists.
This includes $H=0$, where the old input is empty, as well as
all ties $a_n=E$, negative singleton demands and every multiple-zero
suffix.

These operations prove necessity through finite representations.
They give no free actual observation or law-preserving stopping
replacement to an original rule. After them, apply Lemma 3.1 with
artificial ninth amplitude $b'_9=E$ to the eight-bit representative
at $(a_1,\ldots,a_8;E)$. This auxiliary amplitude is not the actual
$a_9$: the original sequence and all its targets retain their values.
In particular the proof constructs no original competitor that ignores
an actually active ninth coordinate. Theorem 3.2 now gives (4.2)
with $E$ in place of the error.

For caps $E\ge1$ this necessary inequality is immediate: its left
side is at most 73, while $2+117E\ge119$. Thus every positive
met cap is covered. For actual error $r<1$, decrease positive met
caps to $r$. The inequality is affine in the cap and passes to the
limit, including hypothetical $r=0$. Horizons and representatives
may change; no limiting law or coupling is asserted. At $r=1$ the
same direct bound applies. Finally complete an original $O$ schedule
as in Definition 1.2. Its identical output law has the same error
and at most two actual requests, with any ignored second request
counted. The $N$ result therefore proves (4.2) for $O$ too.
$\square$

## 5. The full positive-width family with arbitrary later tails

**Theorem 5.1 (Uniform original lower bound).**
Let

$$
\begin{gathered}
0<\tau\le1/24,\qquad0<\delta\le\tau/11,\\
a_2=1-11\tau,\qquad
(a_3,a_4,a_5,a_6,a_7)=(13,10,9,8,6)\tau,\\
a_2\le a_1\le1-7\tau,\qquad
a_8=5\tau+11\delta,\qquad r_0=5\tau+\delta.
\end{gathered}
\tag{5.1}
$$

Append **any** positive nonincreasing vanishing continuation with
$a_9\le a_8$. On the original source, full carrier and resource
contract of Section 1, using the credited correspondence 4.1, every
$A\in\mathcal N_2\cup\mathcal O_2$ satisfies

$$
e_a(A)\ge R_*:=5\tau+\frac{121}{117}\delta
               =r_0+\frac4{117}\delta>r_0.
\tag{5.2}
$$

No condition $a_9\le r_0$ is imposed. The conclusion is uniform
over both heads and every permitted continuation, including ties and
nonsummable tails.

**Proof.** The entire sequence is valid throughout (5.1).
The scale bound gives $a_2\ge13\tau=a_3>0$; the head interval
is nonempty and below one. The width bound gives
$a_8\le6\tau=a_7$. All prescribed amplitudes are positive and
ordered, and the stipulated tail preserves order, positivity and
vanishing.

In the left side of (4.2) the contributions are

$$
\begin{aligned}
2a_2&=2-22\tau,\\
11a_3+13a_4+13a_5+12a_6+11a_7
 &=(143+130+117+96+66)\tau=552\tau,\\
11a_8&=55\tau+121\delta.
\end{aligned}
$$

Thus (4.2) gives $117e_a(A)\ge585\tau+121\delta$,
which is (5.2). Equivalently, at any met cap $E$ set $t=E-r_0$.
The residuals of (3.4) are

$$
S=51\tau+11\delta,\qquad s=44t,\qquad g=4\delta-29t.
$$

Consequently $g\le2s$ reads $4\delta\le117t$.
The old six-late inequality in XVII305.2–305.3 gives only
$e_a(A)\ge r_0$ on this family; its score and that initial lower
bound remain credited there.

Proposition 4.2 includes every positive closed cap and actual error
zero or one. In particular the endpoint $r=1$ also follows from

$$
R_*<5\tau+2\delta\le19/88<1.
$$

The proof includes $\tau=1/24$ with $a_2=a_3$,
$\delta=\tau/11$ with $a_8=a_7$, both head endpoints
$a_1=a_2$ and $a_1=1-7\tau$, and every later amplitude tie.
No strict order or summability is required. Finite positive prefixes
and multiple-zero words retain their actual witnesses from 1.3.

At the lower threshold,

$$
a_8-R_* =\frac{1166}{117}\delta>0.
$$

The first eight coordinates are therefore active. Higher coordinates
may also be active: exactly eight are active at $R_*$ iff
$a_9\le R_*$. No such restriction is assumed in (5.1)–(5.2).
An actual $a_9>R_*$ changes the finite horizon before the prefix
restriction in Proposition 4.2; it does not obstruct that restriction.
This proves the bound on the entire declared tail family. $\square$

**Boundary 5.2 (Zero width).**
At $\delta=0$ the incremental term in (5.2) vanishes. Then
$a_8=5\tau$ and $a_9\le a_8$, and the declared heads satisfy
both head conditions of
[XVII300.1](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md#300-exact-coupled-head-projection-and-one-common-stopped-law).
Its existing common stopped law and counted $N$ completion attain
both optima $5\tau$ for every such tail. This is that theorem's
attained boundary, with no new attainment assertion at positive width.
The case $\tau=0$ is outside the positive-sequence family (5.1).

## 6. Attribution and remaining scope

For an entire sequence define

$$
R_N(a)=\inf_{N\in\mathcal N_2}e_a(N),\qquad
R_O(a)=\inf_{O\in\mathcal O_2}e_a(O).
$$

Counted completion and Theorem 5.1 give
$R_*\le R_N(a)\le R_O(a)$ on (5.1) with every declared tail.
There is no matching upper law or assertion that $R_*$ is attained,
that $4/117$ is sharp, or that either infimum equals this bound.

The arithmetic source, original objects, exact positive-cap transport,
finite event rows and old six-late bound are reused at their stated
scopes in XVII297, 305, 309 and XVIII315. The complete $Y_{128}$
score and its broad finite supporting theorem are XVIII318 content;
the narrower attained family in XVIII321 is not a premise for the
bridge. The same-law extension, its eight-coordinate formulation
$g\le2s$, and (5.2) with the enlarged tail scope are one application
of that score. They are not independent new supporting-score results.

The literature framework retains the scope stated in
[XVII303.3 and 314](https://github.com/the-omega-institute/trureturing/blob/07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
and
[XVIII323.2](https://github.com/the-omega-institute/trureturing/blob/24e09b5c/docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md#323-target-literature-and-unrestricted-boundaries):
Blackwell's comparison concerns whole attainable loss vectors, while
Kaniewski–Lee–de Wolf's literal-degree characterization concerns
nonnegative scalar expectation. Scalar output rescaling does not
supply normalized vector probabilities or equal counterfactual schedule
masses. Here those requirements are supplied by (2.1) and (3.1).
No exhaustive external-priority or global-originality assertion is made.

The unrestricted whole-allocation comparison of XVII303.1, XVII314.1
and XVIII323.3 remains unresolved. A lower bound against both classes
supplies neither a replacement stopped law for every feasible $N$
profile nor an original $N/O$ separator. These results do not classify
general unequal-tail optima. Their accuracy concerns the selected
marked laws, with the original nonatomic targets and consumer retained.
The arguments are ordinary mathematics; they assert no formal kernel
verification, physical efficiency, general neural-network consequence
or empirical-learning conclusion.

## 追加锚（本行以下为增补区）
