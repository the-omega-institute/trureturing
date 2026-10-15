# Recursive relational observation: a native cyclic entropy lower certificate

> This reference source uses `generic-v1` and GitHub Markdown mathematics.
> Published statements are immutable; corrections and extensions follow the
> terminal append anchor. The mathematics is ordinary mathematics, without a
> claim of Lean kernel verification. Repository suppliers are pinned at
> `87b4c51addc0da5ef8847a9adc723bde11a3f908`.

## 1. The complete stationary native problem and its supplied interfaces

**Definition 1.1 (trees, literal observations and prediction).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
\tag{NCE.1}
$$

Pairing is free and ordered. An address is any finite word over $\{L,R\}$,
including the empty word $\varepsilon$. Every address is a legal literal
query. Its reply $r_t(a)$ belongs to
$\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$: it gives the
constructor at the addressed vertex, or absent if traversal passes a leaf.
Define the substitution

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{NCE.2}
$$

For each public integer $D\ge1$, retain exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},
\qquad W_D=\{q:|q|\le D-1\},
\qquad\mathcal P_D=\{Rq:q\in W_D\}.
\tag{NCE.3}
$$

One actual initial source $t$ remains stationary through preparation and
later acquisition. The trees $\rho^kt$ are prediction targets, rather than
updates to that register. There is no subtree, equality, source-identity,
age, reset, copying, free-navigation or free-advice port.

**Assumption 1.2 (paid preparation and complete late-target export).**
Preparation is one deterministic effective procedure, initialized
source-blind from public $D$ and common installed tables. It does not receive
the later target. It terminates on every $t\in\mathcal F_D$, acquiring
source dependence only through charged literal Reads of that stationary
source. It exports a finite code $E(t)$. Its complete attained alphabet
includes every accessible surviving source distinction: selectors, control,
operands, buffers, lengths, allocation, handles, counters and accessible
timing distinctions. Every other surviving accessible field is a function
of this code and public data. A separately paid handoff and isolation
service makes preparation transcripts and all other acquired material
inaccessible and supplies lawful reader entry.

Only after export is a public source-independent request
$p\in\mathcal P_D$ supplied. A common deterministic effective reader uses
$E(t),D,p$ and the installed tables. It either makes zero Reads, or makes
one fresh Read of the same stationary $t$, at any finite original-root word
chosen from those inputs. It produces a final predictor $Z$. For every
authentic subsequently supplied integer $k\ge0$, with no further Reads,

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0).
\tag{NCE.4}
$$

Neither a supplied $k$ nor a source-dependent request may guide the query.
Define $M_1(D)$ to be the minimum complete attained cardinality
$|E[\mathcal F_D]|$ over these preparations and readers. Only this
cardinality is optimized. Preparation Reads, work and control, temporary
storage, installed tables, post-request workspace, final predictor size,
submitted address length and letters, authentication, entry, isolation,
source continuity and physical time remain separate resources. The paid
services are hypotheses, not physical operations inferred from a proof.

**Convention 1.3 (the exact AAR factor, reused).** For a word $q$ put
$s(q)=\#L(q)+2\#R(q)$, and put $e(\alpha)=0$, $e(\beta)=1$.
Use precisely the factor $\Gamma_q(u)=(b,c)$ of
[AAR, Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR]. It is
$(0,0)$ at an original branch endpoint. Otherwise let $a$ be the first
original leaf on the path toward $q$, with label $\ell$, and write $q=ar$.
Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{NCE.5}
$$

The supplied all-count decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{NCE.6}
$$

On attained factors, $c=1$ implies $b\ge2$. AAR proves that (NCE.6)
equals $r_{\rho^ku}(q)$ for every $k\ge0$. Its temporal calculation
uses $T_j=\rho^j\alpha$, with $T_0=\alpha$, $T_1=\beta$ and
$T_{j+2}=\langle T_{j+1},T_j\rangle$. Traversing $L$ or $R$
subtracts respectively one or two from the index, and an edge can
be traversed only while its preceding index is at least two.
For a nonempty word $r$, these guards have their largest threshold
at its last edge: $j\ge s(r)$ when that edge is $R$, and
$j\ge s(r)+1$ when it is $L$. Once reached, its reply is the
root reply of $T_{j-s(r)}$. Hence an $R$-ending
word is absent for $j<s(r)$, alpha at $s(r)$, beta at $s(r)+1$, and
branch thereafter; an $L$-ending word is also absent at $s(r)$, then
beta at $s(r)+1$ and branch thereafter. The latter word has no alpha
stage. Transport is applied only at the actually present original
blocking leaf. This gives (NCE.5), including initially absent targets.

Conversely, the complete trajectory recovers $b$ as its first branch
count and $c$ as the indicator that an alpha stage occurs. Thus equality
of these factors is exactly equality of trajectories. Distinct blocking
positions can have the same factor; they must not be counted as distinct
target values. At every actually present occurrence $a$ with subtree $u$,
homomorphic substitution gives

$$
r_{\rho^kt}(aq)=r_{\rho^ku}(q),
\qquad
\Gamma_{Rq}(\langle\alpha,v\rangle)=\Gamma_q(v).
\tag{NCE.7}
$$

In the original request family its first branch count satisfies
$b_{Rq}(\langle\alpha,v\rangle)\le s(q)+2\le2D$.
Thus the supplied finite predictor can be the pair $(b,c)$;
its size and the authentic count representation remain separate
from the optimized retained alphabet.

**Definition 1.4 (canonical actual blocks and joint covers).** Following
[FMR, Definitions 2.1 and 6.1][FMR], put

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{NCE.8}
$$

These are actual trees of height at most $d$, not additional source ports.
A nonempty $B\subseteq S_d^n$ is jointly admissible if, for every
coordinate $i$ and target $q\in W_d$, the function $\Gamma_q(x_i)$
on this same $B$ is constant, or is determined by one function
$r_{x_j}(a)$, with $1\le j\le n$ and $a\in W_d$. Equivalently,

$$
r_{x_j}(a)=r_{y_j}(a)
\ \Longrightarrow\ \Gamma_q(x_i)=\Gamma_q(y_i)
\quad(x,y\in B).
\tag{NCE.9}
$$

The chosen $j,a$ may depend on $B,i,q$ and need not lie in the target
coordinate or on its path. No product structure is imposed on $B$.
Let $K_d(n)$ be the least number of jointly admissible sets covering
$S_d^n$. Let $Z_d(n)$ be the fractional cover optimum over that entire
family: coefficients $c_B\ge0$ satisfy
$\sum_{B\ni x}c_B\ge1$ for every $x$, and the objective is
$\sum_Bc_B$. A set $P\subseteq S_d$ is locally admissible when
it satisfies joint admissibility with $n=1$, and locally insufficient
otherwise. For $n=1$ these are the local cover optima.

The following precise supplier facts will be used. FMR Lemma 2.2 shows
that on $S_d$ a length-$d$ word returns alpha exactly when its
length-$(d-1)$ parent is branch, and absent otherwise; every longer
word is absent. Hence arbitrary finite block experiments reduce to
boundary experiments or constants in their original queried block.
FMR Theorem 2.5 and Lemma 6.2 implement covers by paid preparation,
with a first-containing-member code and actual literal witnesses.
The full boundary scan has the sufficient bounds

$$
T_D\le2^D-1,\qquad Q_D\le D,\qquad
A_D\le(D-1)2^D+1,
\tag{NCE.10}
$$

for preparation Reads, maximum submitted length and submitted letters.
It submits every $Rq$, $q\in W_D$, and isolates the acquired table
after computing the complete code. These are credited sufficient
construction bounds, not optimal costs or resources granted to a
lower-bound competitor.

FMR Theorems 3.3, 6.3 and 6.4 supply

$$
\begin{aligned}
\sigma_d&=\lim_{n\to\infty}\frac{\log_2K_d(n)}n
          =\inf_{n\ge1}\frac{\log_2K_d(n)}n,\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D),\qquad
K_d(2^h)\le M_1(d+h),\qquad
2^{-d}\sigma_d\le\lambda.
\end{aligned}
\tag{NCE.11}
$$

The full-family rate exists because the paid native gluing obeys
$M_1(D+1)\le M_1(D)^2+1$: a leaf marker or a pair of acquired child
codes serves every variable shape, with constituent Reads translated
to original-root literals. Thus $2^{-D}\log_2(M_1(D)+1)$ decreases
to the same limit. Joint concatenation gives subadditivity for
$\log_2K_d(n)$. The restriction in (NCE.11) uses actual perfect
scaffolds, not independently optimized child projections. Section 6
below spells out that restriction for the new certificate.

## 2. A heavy-target half-entropy certificate

**Definition 2.1 (finite interfaces and heavy projections).** Let $S$ be
a nonempty finite set, with target functions $g_q$ and experiment
functions $r_a$. Each experiment has at most $m$ attained replies on
$S$, where $m\ge1$. Include a constant experiment, representing zero
observations. On $P\subseteq S$, say that an experiment determines
$g_q$ if equal replies on $P$ imply equal target values there. Say
that $P$ is range-feasible if $|g_q(P)|\le m$ for every target.
For $w:S\to[0,\infty)$ write

$$
w(P)=\sum_{x\in P}w(x),\qquad
A_{q,z}(P)=\sum_{x\in P:\ g_q(x)=z}w(x),\qquad
\Omega_w(B)=\sum_{x\in B}\prod_{i=1}^nw(x_i).
\tag{NCE.12}
$$

Joint admissibility in $S^n$ means that for every $i,q$ the target
$g_q(x_i)$ is determined on $B$ by one experiment $r_a(x_j)$, with
the constant experiment allowed. Its donor $j$ and experiment $a$
can depend on the whole set $B$ and on $i,q$. For a positive real
$C$, a projection is heavy if $w(P)>C$.

**Theorem 2.2 (uniform mass bound with arbitrary cyclic donors).**
Suppose that every range-feasible $P\subseteq S$ with $w(P)>C$
has a target $g_q$ which no own-coordinate experiment determines on
$P$, and for which

$$
\sum_{z\in g_q(P)}A_{q,z}(P)^2\le C^2.
\tag{NCE.13}
$$

Then for every $n\ge1$ and every jointly admissible $B\subseteq S^n$,

$$
\boxed{\Omega_w(B)\le C^n.}
\tag{NCE.14}
$$

In particular the functions
$y_n(x)=C^{-n}\prod_iw(x_i)$ are feasible fractional-cover dual
weights for the entire family of jointly admissible sets, with total
$(w(S)/C)^n$. Every integral joint cover has at least
$\lceil(w(S)/C)^n\rceil$ members.

Proof. Empty $B$, or $\Omega_w(B)=0$, is immediate. Zero-weight states
can be deleted: replace $S$ by $S_+=\{x:w(x)>0\}$ and $B$ by
$B\cap S_+^n$. Joint admissibility and the hypothesis restrict to
these subsets, and neither relevant mass changes. Hence assume
$w>0$ and $B\ne\varnothing$.

Use the single probability law

$$
\Pr[X=x]=\frac{\prod_iw(x_i)}{\Omega_w(B)}\quad(x\in B).
\tag{NCE.15}
$$

Every point of $B$ has positive probability. Its marginal support is
exactly $P_i=\pi_i(B)$: every projected state occurs in at least one
positive-probability tuple. Every $P_i$ is range-feasible. Indeed,
for a fixed target its values on $P_i$ are exactly its values on
$B$, and the witnessing single experiment on $B$ has at most $m$
replies. This argument asserts neither that $P_i$ is locally
admissible nor that the tuple coordinates are independent.

All logarithms in this proof are base two. For a finite random
variable $U$ with law $p$, write $H(U)=H(p)=-\sum_up_u\log_2p_u$.
Conditional entropy is
$H(U\mid V)=\sum_{v:\Pr[V=v]>0}\Pr[V=v]H(U\mid V=v)$.
We record the finite entropy facts used, with their support conditions.
For a distribution
$p$ and a distribution $q$ positive on the support of $p$,

$$
D(p\Vert q)=\sum_{p_z>0}p_z\log_2\frac{p_z}{q_z}\ge0.
\tag{NCE.16}
$$

To see this directly, apply $\ln t\le t-1$ to $t=q_z/p_z$ and
sum: $\sum_{p_z>0}p_z\ln(q_z/p_z)\le
\sum_{p_z>0}q_z-1\le0$. Thus, for positive numbers $a_z$,

$$
H(p)+\sum_zp_z\log_2a_z\le\log_2\sum_za_z.
\tag{NCE.17}
$$

Here (NCE.17) is (NCE.16) with $q_z=a_z/\sum_ua_u$; the
convention $0\log 0=0$ applies throughout. The chain rule follows
by writing a positive joint mass as marginal mass times conditional
mass, and summing its logarithm. Conditioning reduces entropy:

$$
H(U\mid V,Z)\le H(U\mid Z).
\tag{NCE.18}
$$

For each $z$ of positive probability, apply (NCE.16) to the conditional
joint law of $(U,V)$ and the product of its two conditional marginals.
The product is positive wherever that joint law is positive. Expanding
and averaging gives
$H(U\mid Z)-H(U\mid V,Z)\ge0$. Zero-probability conditioning
events make no contribution. This proves (NCE.18), including empty
or constant conditioning variables. It also proves all the following
uses for vector-valued conditioning variables.

Let $I=\{i:w(P_i)>C\}$. For each $i\in I$, choose a target from
the hypothesis and put $Y_i=g_{q_i}(X_i)$. Its joint witness gives
a donor $j_i$ and a function $d_i$ with

$$
Y_i=d_i(r_{a_i}(X_{j_i}))\quad\text{on }B.
\tag{NCE.19}
$$

Such a function exists on attained replies because equal replies have
equal target values; its definition elsewhere is immaterial. A constant
target would have a constant own-coordinate witness, so $Y_i$ is
nonconstant on $P_i$. A donor $j_i=i$ would determine the chosen
target on all of $P_i$: take any two projected states, lift them to
tuples in $B$, and apply the witnessing equality. Both possibilities
contradict its choice. Therefore $j_i\ne i$. Crucially, $Y_i$ is a
deterministic function both of $X_i$ and of $X_{j_i}$ under the
same law (NCE.15).

Let the total correlation under this law be

$$
\mathcal C(X)=\sum_iH(X_i)-H(X_1,\ldots,X_n).
$$

For any ordering $\pi$ of the coordinates, let $A_i^\pi$ be the
tuple of coordinates preceding $i$. The chain rule gives

$$
\mathcal C(X)=\sum_i\bigl(H(X_i)-H(X_i\mid A_i^\pi)\bigr).
\tag{NCE.20}
$$

Every summand is nonnegative by (NCE.18). If $i\in I$ and $j_i$
precedes $i$, then $Y_i$ is a function of $A_i^\pi$, so

$$
\begin{aligned}
H(X_i\mid A_i^\pi)
 &=H(X_i\mid A_i^\pi,Y_i)\le H(X_i\mid Y_i),\\
H(X_i)-H(X_i\mid A_i^\pi)
 &\ge H(X_i)-H(X_i\mid Y_i)=H(Y_i).
\end{aligned}
\tag{NCE.21}
$$

The last equality uses that $Y_i$ is a function of $X_i$ and the
chain rule for $(X_i,Y_i)$. Average (NCE.20)–(NCE.21) over all
$n!$ coordinate orders. For each distinct pair $j_i,i$, swapping
their order shows that $j_i$ precedes $i$ in exactly half the
orders. Consequently

$$
\mathcal C(X)\ge\frac12\sum_{i\in I}H(Y_i).
\tag{NCE.22}
$$

No assertion that all donor edges point backward in one order is
needed. Reciprocal donors and every longer cycle are included in
this averaging. The order is an analytical device, not a sequence
of actual queries or new side information supplied to a reader.

For a light coordinate, (NCE.17) on its exact marginal support gives

$$
H(X_i)+\mathbb E\log_2w(X_i)\le\log_2w(P_i)\le\log_2C.
\tag{NCE.23}
$$

For a heavy coordinate write $p_z=\Pr[Y_i=z]$ and
$A_z=A_{q_i,z}(P_i)$. Each attained cell has $A_z>0$ and $p_z>0$.
The conditional law of $X_i$ given $Y_i=z$ is supported on exactly
that cell, because the marginal law has full support $P_i$. Applying
(NCE.17) within each cell and then the chain rule gives

$$
H(X_i)+\mathbb E\log_2w(X_i)
 \le H(p)+\sum_zp_z\log_2A_z.
$$

Apply (NCE.17) again, this time to the positive numbers $A_z^2$:

$$
\begin{aligned}
H(X_i)+\mathbb E\log_2w(X_i)-\tfrac12H(Y_i)
 &\le\tfrac12H(p)+\sum_zp_z\log_2A_z\\
 &\le\tfrac12\log_2\sum_zA_z^2\le\log_2C.
\end{aligned}
\tag{NCE.24}
$$

Finally (NCE.15) gives the exact weighted Gibbs identity

$$
\log_2\Omega_w(B)=H(X)+\sum_i\mathbb E\log_2w(X_i).
\tag{NCE.25}
$$

Substitute $H(X)=\sum_iH(X_i)-\mathcal C(X)$, apply (NCE.22),
then (NCE.23) and (NCE.24). The result is
$\log_2\Omega_w(B)\le n\log_2C$, proving (NCE.14).
For a fractional cover, sum its pointwise covering inequalities
against $y_n$; each member has mass at most one by (NCE.14),
while the whole product has mass $(w(S)/C)^n$. This proves the
fractional and integral assertions. $\square$

The hypothesis concerns only heavy range-feasible projections.
Light projections can also be locally insufficient. The proof uses
neither an entropy-cone completeness assertion nor an achievability
theorem for arbitrary functional dependencies.

## 3. Exact native distinctions and the child mass bounds

**Convention 3.1 (the depth-two factor table).** Use $A=\alpha$,
$B=\beta$, $C_0=\langle A,A\rangle$, and write
$g_{xy}=\langle x,y\rangle$ for $x,y\in\{A,B,C_0\}$.
Put $\gamma(A)=(2,1)$, $\gamma(B)=(1,0)$,
$\gamma(C_0)=(0,0)$, and let $\kappa$ give the root constructor.
The exact table, also supplied by FMR Theorem 5.1, is

$$
\begin{array}{c|ccc|ccc}
u&r_u(\varepsilon)&r_u(L)&r_u(R)
 &\Gamma_\varepsilon(u)&\Gamma_L(u)&\Gamma_R(u)\\\hline
A&\alpha&\mathsf{absent}&\mathsf{absent}
 &(2,1)&(3,0)&(4,1)\\
B&\beta&\mathsf{absent}&\mathsf{absent}
 &(1,0)&(2,0)&(3,1)\\
g_{xy}&\mathsf{branch}&\kappa(x)&\kappa(y)
 &(0,0)&\gamma(x)&\gamma(y).
\end{array}
\tag{NCE.26}
$$

Formula (NCE.5) gives the root-leaf entries by $s(L)=1$, $s(R)=2$.
For a branch, the target enters its corresponding child, giving
$\gamma(x)$ or $\gamma(y)$. Thus each side column has five
pairwise distinct possible factors: its two root-leaf factors and
the three child-constructor factors. In particular,

$$
\begin{aligned}
\mathcal V_L:=\Gamma_L(S_2)
 &=\{(3,0),(2,0),(2,1),(1,0),(0,0)\},\\
\mathcal V_R:=\Gamma_R(S_2)
 &=\{(4,1),(3,1),(2,1),(1,0),(0,0)\}.
\end{aligned}
\tag{NCE.27}
$$

**Lemma 3.2 (canonical target vectors distinguish actual states).**
For every $d\ge1$, the map
$u\mapsto(\Gamma_q(u))_{q\in W_d}$ is injective on $S_d$.
Consequently any two distinct branches in $S_3$ differ at some
nonempty target $q\in W_3$. For each such nonempty $q$,
$\Gamma_q(A)\ne\Gamma_q(B)$, and $\Gamma_q(A)$ differs
from the factor of every branch in $S_3$.

Proof. At $d=1$, $\Gamma_\varepsilon$ takes the distinct values
$(2,1),(1,0),(0,0)$ on $A,B,C_0$. Inductively the root factor
separates both leaves from every branch. On a branch,
$\Gamma_{Lq}(\langle x,y\rangle)=\Gamma_q(x)$ and
$\Gamma_{Rq}(\langle x,y\rangle)=\Gamma_q(y)$ for
$q\in W_{d-1}$. Equality of the full vectors therefore gives
equality of both children by induction. Distinct branches agree
at the root target, so their distinguishing target is nonempty.

For a nonempty $q$, the first coordinates of the factors on $A,B$
are respectively $s(q)+2$ and $s(q)+1$, hence differ. For any
finite $u$ and word $r$, (NCE.5) gives $b_r(u)\le s(r)+2$:
a branch endpoint has $b=0$, and a blocking leaf contributes at
most the weight of the whole word plus two. Write $q=sr$ with
$s\in\{L,R\}$. On a branch its factor is the factor at $r$
of one child, with first coordinate at most $s(r)+2<s(q)+2$.
It cannot equal the factor on $A$. $\square$

**Lemma 3.3 (weighted child ranges).** On $S_2$, set

$$
v(A)=v(B)=4,\qquad v(g_{xy})=1.
\tag{NCE.28}
$$

If $U\subseteq S_2$ has both side-target ranges at most $k$,
for $k=2,3,4$, then respectively

$$
v(U)\le8,\qquad v(U)\le9,\qquad v(U)\le13.
\tag{NCE.29}
$$

Proof. Let $\ell=|U\cap\{A,B\}|$, and let $c_L,c_R$ count the
distinct child symbols appearing on each side among its branches.
Table (NCE.26) gives $|\Gamma_s(U)|=\ell+c_s$ for $s=L,R$.
The number of branches is at most $c_Lc_R$, so

$$
v(U)\le4\ell+\min\{3,k-\ell\}^2.
$$

The bounds for the three possible leaf counts are

$$
\begin{array}{c|ccc|c}
k&\ell=0&\ell=1&\ell=2&\text{maximum}\\\hline
2&4&5&8&8\\
3&9&8&9&9\\
4&9&13&12&13.
\end{array}
\tag{NCE.30}
$$

The empty set also satisfies every displayed bound. $\square$

## 4. The depth-three heavy-target certificate

**Definition 4.1 (the analytical depth-three weights).** The sets $S_2$
and $S_3$ have respectively $11$ and $123$ states. On $S_3$ put

$$
w(A)=88,\qquad w(B)=52,\qquad
w(\langle x,y\rangle)=v(x)v(y),\qquad C=169.
\tag{NCE.31}
$$

Here $v$ is (NCE.28), so
$v(S_2)=17$ and $w(S_3)=88+52+17^2=429$.
These weights are dual-certificate data. They are neither a source
prior nor retained advice supplied to the native reader.

**Lemma 4.2 (all four root-leaf cases).** Let $P\subseteq S_3$ be
range-feasible for all seven targets $W_3$, with reply capacity four.
Write its branch part as
$T=\{(x,y):\langle x,y\rangle\in P\}\subseteq S_2^2$,
and let $X,Y$ be the two projections of $T$. Then

$$
\begin{array}{c|cc|c}
P\cap\{A,B\}&v(X)\text{ at most}&v(Y)\text{ at most}
 &w(P)\text{ at most}\\\hline
\varnothing&13&13&169\\
\{A\}&9&9&88+81=169\\
\{B\}&13&9&52+117=169\\
\{A,B\}&8&8&88+52+64=204.
\end{array}
\tag{NCE.32}
$$

In the last case, the branch mass alone is at most $64$.

Proof. Positivity and $T\subseteq X\times Y$ give

$$
\sum_{(x,y)\in T}v(x)v(y)\le v(X)v(Y).
\tag{NCE.33}
$$

This only enlarges a nonnegative sum. It does not replace a native
fiber by a product or claim that $X,Y$ are locally admissible.
If $T$ is empty the assertions follow directly. Otherwise both
projections are nonempty.

For the four deeper targets, the exact parent-leaf factors are

$$
\begin{array}{c|cccc}
 &LL&LR&RL&RR\\\hline
A&(4,0)&(5,1)&(5,0)&(6,1)\\
B&(3,0)&(4,1)&(4,0)&(5,1).
\end{array}
\tag{NCE.34}
$$

For a branch, these same four columns give respectively
$\Gamma_L(x),\Gamma_R(x),\Gamma_L(y),\Gamma_R(y)$.
In the $LL$ column the parent $B$ value $(3,0)$ coincides only
with the $x=A$ root-leaf value in $\mathcal V_L$; in $LR$ its
value $(4,1)$ coincides only with the $x=A$ root-leaf value in
$\mathcal V_R$. The parent $A$ values $(4,0),(5,1)$ in these
columns are absent from $\mathcal V_L,\mathcal V_R$ respectively.
In $RL$, both $(5,0)$ and $(4,0)$ are outside $\mathcal V_L$;
in $RR$, both $(6,1)$ and $(5,1)$ are outside $\mathcal V_R$.
The two added values in each right column are distinct. These
are all parent-leaf versus child-factor collisions in (NCE.34).

With neither parent leaf, range feasibility at these four targets
bounds both side ranges of $X,Y$ by four. Lemma 3.3 gives $13,13$.
With $A$ alone, its new value in each column reduces both side
ranges of both projections to at most three, giving $9,9$.
With $B$ alone, both side ranges of $Y$ are at most three, and
both of $X$ are at most four, giving $13,9$. This proves the
first three rows without imposing any restriction on which of
the possible left collisions is actually attained.

Suppose both parent leaves occur. At target $L$ their factors are
$(3,0),(2,0)$; at $R$ they are $(4,1),(3,1)$. In either case
these are two distinct values outside
$\Gamma_\varepsilon(S_2)=\{(2,1),(1,0),(0,0)\}$.
Hence $X$ and $Y$ each have at most two root-constructor types.
At $LL,LR$, removing the new parent $A$ value leaves

$$
|\Gamma_L(X\cup\{A\})|\le3,\qquad
|\Gamma_R(X\cup\{A\})|\le3.
\tag{NCE.35}
$$

At $RL,RR$, the two new parent values give

$$
|\Gamma_L(Y)|\le2,\qquad|\Gamma_R(Y)|\le2.
\tag{NCE.36}
$$

For completeness, the sector bounds implied by these restrictions are

$$
\begin{array}{c|cc}
\text{root leaves in the child projection}&v(X)\text{ at most}
 &v(Y)\text{ at most}\\\hline
\{A,B\}&8&8\\
\{A\}&4+4=8&4+1=5\\
\{B\}&4+1=5&4+1=5\\
\varnothing&4&4.
\end{array}
\tag{NCE.37}
$$

Indeed, two child leaves exhaust the two allowed constructor types,
so exclude every branch. With only $A$ in $X$, (NCE.35) permits
at most two branch child symbols per side, hence four branches.
With only $B$, adjoining $A$ makes two leaf values, leaving only
one branch symbol per side, hence one branch. With no leaves,
adjoining $A$ leaves two symbols per side, hence four branches.
For $Y$, (NCE.36) permits one branch symbol per side alongside
one leaf, and two per side with no leaf. Thus both masses are
at most eight. Equation (NCE.33) bounds the branch mass by $64$
and proves the final row. $\square$

**Theorem 4.3 (native heavy targets satisfy the squared-cell bound).**
For every range-feasible $P\subseteq S_3$ with $w(P)>169$, there
is a nonempty $q\in W_3$ which no own-coordinate native experiment,
at any finite word, determines on $P$, and

$$
\sum_z w(P\cap\Gamma_q^{-1}(z))^2
\le88^2+116^2=21200<28561=169^2.
\tag{NCE.38}
$$

Proof. Lemma 4.2 forces both $A,B$ to belong to $P$. If there
were at most one branch, its weight would be at most $4\cdot4=16$,
so $w(P)\le88+52+16=156$. There are therefore two distinct
branches. Lemma 3.2 supplies a nonempty target $q\in W_3$
distinguishing them.

The root experiment merges these two branches, so does not
determine this target. Every nonempty finite word returns absent
on both $A$ and $B$, whose target factors differ by Lemma 3.2;
thus no such experiment determines it either. A constant experiment
also fails. This exhausts every own-coordinate experiment, including
all off-target and arbitrarily long words.

By Lemma 3.2, $A$ is alone in its target cell: neither $B$ nor
any branch shares its factor. That cell has weight $88$. All
remaining cells together have weight at most $52+64=116$, by
the last row of Lemma 4.2. For nonnegative numbers the sum of
squares is at most the square of their sum, because all cross
products are nonnegative. Applying this to those remaining cells
gives (NCE.38). $\square$

## 5. Necessary examples and the meaning of equality for a weight system

**Proposition 5.1 (range feasibility does not supply the mass cap).**
The actual six-state set

$$
P_0=\{A,B\}\cup
\{\langle x,y\rangle:x,y\in\{A,B\}\}\subset S_3
\tag{NCE.39}
$$

is range-feasible, has $w(P_0)=204>169$, and is locally insufficient
for the native one-Read interface.

Proof. In the order $\varepsilon,L,R,LL,LR,RL,RR$, the target
range sizes are respectively

$$
(3,4,4,3,3,4,4).
\tag{NCE.40}
$$

The root factors are $(2,1),(1,0),(0,0)$. At $L$ the root leaves
give $(3,0),(2,0)$ and the branches give $(2,1),(1,0)$; at $R$
they give $(4,1),(3,1)$ and $(2,1),(1,0)$. At $LL$ the union
is $\{(4,0),(3,0),(2,0)\}$, and at $LR$ it is
$\{(5,1),(4,1),(3,1)\}$. At $RL$ it is
$\{(5,0),(4,0),(3,0),(2,0)\}$, and at $RR$ it is
$\{(6,1),(5,1),(4,1),(3,1)\}$. These are obtained by the
actual formula (NCE.5), so establish every range assertion.

Its weight is $88+52+4\cdot16=204$. The target $L$ differs
on $\langle A,A\rangle$ and $\langle B,A\rangle$, which
the root experiment merges. Every nonempty experiment merges
the two root leaves, whose $L$ factors differ. Thus no own
experiment determines $L$, and a constant experiment cannot do
so. In particular the larger range-feasible class cannot be
bounded by simply multiplying projection masses at cap $169$.
Theorem 2.2 uses the additional joint determination relation to
charge the selected target's entropy.
$\square$

**Proposition 5.2 (a matching mass set has a limited implication).**
Let $H=\{A\}\cup\{g_{xy}:x,y\in S_1\}\subset S_2$ and
$P_H=\{\langle x,y\rangle:x,y\in H\}\subset S_3$.
Then $P_H$ is locally admissible and $w(P_H)=169$. Its products
attain $\Omega_w(P_H^n)=169^n$ for every $n\ge1$.

Proof. The $S_2$ root target is determined by the root reply.
On $H$, a side reply is absent only on $A$, where the side
factor is fixed; on its branches the three child replies determine
the corresponding $\gamma$ value. Thus every target in $W_2$
has an own-coordinate witness on $H$. On $P_H$, the root
target is constant, and each target $sq$ uses the corresponding
child's witness at the literal $sa$. Every target is served by
at most one actual word. Since $v(H)=4+9=13$, its mass is
$13^2=169$. Products use these same witnesses in their target
coordinate, and their product mass is $169^n$. $\square$

This is equality in the mass bound for the chosen weights. It
does not construct a cover saturating all dual constraints, nor
identify $Z_3(n)$, $\sigma_3$ or $\lambda$. A matching mass
example is not a matching fractional cover or rate construction.
The attained cyclic relation of [NCM, Proposition 6.1][NCM] is
credited context for the need to admit locally insufficient
projections. Theorem 2.2 covers it without assuming a locally
admissible donor, and does not use NCM's lower-bound proof.

## 6. All joint lengths and transport to every original depth

**Theorem 6.1 (depth-three all-correlated fractional dual).** For every
$n\ge1$ and every jointly admissible $B\subseteq S_3^n$,

$$
\Omega_w(B)\le169^n.
\tag{NCE.41}
$$

Consequently the explicit rational dual weights

$$
y_n(x)=169^{-n}\prod_{i=1}^nw(x_i)
\tag{NCE.42}
$$

give, for every $n\ge1$,

$$
\boxed{\quad
Z_3(n)\ge\left(\frac{33}{13}\right)^n,\qquad
K_3(n)\ge\left\lceil\left(\frac{33}{13}\right)^n\right\rceil,
\qquad\sigma_3\ge\log_2\frac{33}{13}.
\quad}
\tag{NCE.43}
$$

Proof. Apply Theorem 2.2 with $S=S_3$, $m=4$, the seven
native targets, all boundary native experiments and a constant,
and the weights (NCE.31). Theorem 4.3 verifies its hypothesis;
indeed it verifies nonrecoverability even for the larger menu
of every finite word. This proves (NCE.41).

The total mass of (NCE.42) is
$(429/169)^n=(33/13)^n$, while every legal joint set has mass
at most one. Summing any integral or fractional cover proves
the first two bounds. The bound holds for every joint length,
so division by $n$ and the supplied limit in (NCE.11) gives
the bound on $\sigma_3$. No conclusion is inferred from only
one finite $K_3(n)$. $\square$

**Theorem 6.2 (strict original full-family lower).** Under Assumption 1.2,
for every $D\ge3$,

$$
\boxed{\displaystyle
M_1(D)\ge
\left\lceil\left(\frac{33}{13}\right)^{2^{D-3}}\right\rceil,
\qquad
\lambda\ge\frac18\log_2\frac{33}{13}.}
\tag{NCE.44}
$$

This applies to every original preparation and reader, allowing the
complete variable-shape family, target-dependent off-target queries,
arbitrarily correlated code fibers and all finite original-root words.

Proof. Put $h=D-3$ and $n=2^h$. In the actual right subtree $v$
fix a perfect ordered binary scaffold of height $h$. Its frontier
addresses $a_1,\ldots,a_n$ all have length $h$. For every tuple
$x\in S_3^n$, fill those frontier occurrences with the actual
trees $x_i$, obtaining $v_x$ and
$t_x=\langle\alpha,v_x\rangle$. This is an injective actual
family: taking the mathematically specified subtrees at the fixed
frontier recovers the tuple. Its height is at most $h+3=D$,
so every $t_x$ belongs to the original $\mathcal F_D$.

Restrict any correct original complete code $E$ to these sources;
do not alter its values or project any of its fibers. For every
block target $q\in W_3$, the address $Ra_iq$ is an original
allowed request, since

$$
1\le|Ra_iq|=1+h+|q|\le1+h+2=D.
\tag{NCE.45}
$$

Every block occurrence is actually present on every tree in this
slice. Equation (NCE.7) identifies its complete target trajectory
with that of $\Gamma_q(x_i)$ for every subsequently supplied $k$.

Fix an attained code and such a request. Determinism and access
isolation fix the zero-Read decision or submitted literal before
any reply or supplied $k$. Every possible original-root word has
one of the following meanings on this actual slice. The root is
constant branch; $L$ is constant alpha and its strict extensions
are absent. A right-cone word ending strictly above the block
frontier is constant branch. Every other right-cone word enters
one uniquely specified block $j$, and its remaining suffix $a$
is an arbitrary finite block word. For $|a|\le2$ it is exactly
one boundary experiment. For $|a|=3$ its reply is alpha when its
length-two parent is branch, and absent otherwise. For $|a|>3$
it is constant absent. Thus every arbitrary query is a function
of one allowed boundary reply in its original queried block, or
is a constant. In particular it need not query the target block.

If two tuples in the restricted code fiber give the same boundary
reply in that block, they give the same actual reply and hence
the same final predictor. Correctness for every later $k$ then
gives equality of target trajectories, and Convention 1.3 gives
equality of target factors. A constant query or zero Reads gives
a constant factor on the fiber. Consequently every nonempty
restricted fiber satisfies (NCE.9) on the unchanged tuple.

These fibers partition $S_3^n$, of product weight $429^n$.
Theorem 6.1 bounds each fiber's mass by $169^n$. Their number
is therefore at least $\lceil(429/169)^n\rceil$, and it is no
larger than $|E[\mathcal F_D]|$. This proves the finite bound
against every original competitor. Divide its logarithm by
$2^D=8n$ and use the supplied existence of $\lambda$ to obtain
the rate bound.

This is FMR's actual scaffold restriction with the new all-joint
mass inequality. No artificial root is queried, no subtree is
handed to a reader, and no original source is changed or copied.
All originally allowed targets and off-target choices remain in
the competitor class; only an actual source slice and legal
requests are used to test its mandatory correctness. $\square$

**Corollary 6.3 (exact comparison and retained upper).** The new rate
lower is strictly larger than the credited NCM depth-two lower:

$$
\frac18\log_2\frac{33}{13}
>\frac14\log_2\frac{25}{17},
\qquad
33\cdot17^2=9537>8125=13\cdot25^2.
\tag{NCE.46}
$$

With the unchanged FMR upper construction,

$$
\frac18\log_2\frac{33}{13}
\le\lambda\le L_{\rm seed}<0.216605159,
\qquad
L_{\rm seed}=\lim_{D\to\infty}2^{-D}\log_2x_D,
\quad x_2=\frac{25}{17},\quad x_{D+1}=x_D^2+1.
\tag{NCE.47}
$$

Proof. Strict monotonicity of the logarithm turns the integer
inequality in (NCE.46) into the displayed comparison. FMR
Theorem 5.2 supplies the recurrence construction and its strict
upper. Its native fractional covers, harmonic rounding and paid
boundary acquisition retain their original resources (NCE.10).
The new lower does not introduce an attaining encoder, unpriced
coloring, or a bound on those other resources. $\square$

## 7. Primary mathematical interfaces and the remaining programme

**Convention 7.1 (repository suppliers and source correspondence).**
All repository links below refer to the pinned public revision in
the opening convention. LTR supplies the original task; AAR
supplies the predictive factor, passive fixed-menu quotient and
exact native acquisition interfaces. FMR supplies the canonical
normalization, native cover correspondence, paid constructions,
rate existence and full-family scaffold restriction. The all-cyclic
heavy-target theorem and its weights and strict lower consequence
are repository-derived ordinary deductions here, rather than
renamings of those suppliers. No worldwide novelty claim is made.

NCM supplies ordinary theory.
Its depth-two lower is a credited comparison, and its attained
cycle is credited context. Neither its lower proof nor a review
judgment is a premise of Theorems 2.2, 4.3, 6.1 or 6.2.

The public D5 definitions identify the carriers exactly:
[`GenealogicalFiberTransport.Source` and `substitution`][D5-source]
are `FreeMagma Bool` and the stated homomorphism, with true
for alpha and false for beta.
[`ActualTreeReadoutAcquisition.Address`, `Reply` and `readout`][D5-read]
use Boolean words, false for $L$ and true for $R$, and the four
replies at every finite word. The recognition objective in that
module is a different task. In
[`NativeDepthPatterns`][D5-present], `original_present_transport`
requires an actually present original subtree, exactly as at the
scaffold occurrences used here; `original_prefix_locality` gives
all-count dependence on the original finite boundary. These are
source correspondences, not newly compiled applications.

[NBP, Assumption 14.1 and Theorem 14.4][NBP] supply a paid
common-start, stationary, complete-code handoff discipline on a
different known-row one-image predecessor problem. They do not
give a physical erasure or source-continuity theorem for this task.
[`target_family_minimal_quotient`][D5-quotient] supplies a passive
joint-kernel universal property, not one-Read acquisition geometry.
[`compact_observation_factorization`][D5-compact] assumes a
nonempty compact space, compatible continuous surjective finite
discrete observations forming a fiber basis, and continuous finite
readouts. Its finite action-window clause also assumes a finite
action type and continuous actions. It gives finite-level existence
for bounded words under those hypotheses, not an effective memory
rate, acquisition bound or convergence modulus for this native task.

**Convention 7.2 (primary literature and transfer boundaries).**
The following primary sources attest the surrounding interfaces.
The numerical native certificate is not imported from any of them.

| Primary source | Exact correspondence and absent transfer hypothesis |
| --- | --- |
| Tomasz Gogacz and Szymon Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, [arXiv:1512.01808v1](https://arxiv.org/html/1512.01808v1), Theorem 1 and Corollary 1 | A common relation's functional dependencies give zero conditional entropy. Their fixed-schema exponent uses almost-entropic vectors; the Shannon relaxation gives an upper bound. Here each code fiber, target and joint length can select different donor dependencies. That theorem supplies neither the native squared-cell condition nor an entropy-cone completeness theorem for these varying interfaces. |
| László Csirmaz, *A short proof of the Gács–Körner theorem*, [arXiv:2306.14718v1](https://arxiv.org/html/2306.14718v1), §I and Theorem 2 | A target determined by two coordinates is a deterministic common function under their joint law. The extraction-rate and tension-region results concern correlated memoryless sources and their stated joint extensions. Here only the exact common function under the single Gibbs law is used, with its elementary entropy bound proved in (NCE.21). No extraction rate, independence, or equality of common and mutual information is presumed. |
| Søren Riis, *Graph Entropy, Network Coding and Guessing games*, [arXiv:0711.4175v1](https://arxiv.org/html/0711.4175v1), §§2–3 and 7–8 | Fixed directed-graph guessing strategies allow cyclic deterministic constraints, and graph entropy links them to specified network and index-code interfaces. Here the recovered quantity is a target function, the donor exposes only one constructor reply, and witnesses vary with the fiber and target. No fixed-graph guessing number or network capacity is substituted for native joint admissibility. |
| Anna Blasiak, Robert Kleinberg and Eyal Lubetzky, *Index coding via linear programming*, [arXiv:1004.1379v2](https://arxiv.org/html/1004.1379v2), Theorem 1 and Definition 2.1 | Decoding constraints and information inequalities hold on a common realization. Their broadcast problem has prescribed messages and receiver side information. A native reader instead has the complete code and chooses one source probe after its target; its donor is not a free side-information set. Their LP hierarchy does not supply this native mass bound or an attaining encoder. |
| Anna Gál and Peter Bro Miltersen, *The Cell Probe Complexity of Succinct Data Structures*, [BRICS RS-03-44](https://www.brics.dk/RS/03/44/index.html), systematic-storage model | Preserved input plus retained index corresponds to the stationary reply array plus $E$. Here the boundary array is grammar-constrained, its replies have four symbols, the whole code is available, and only one actual source probe is charged after the request. Their bit-probe input families and query functions do not imply the displayed native constant. |
| Sumegha Garg, Songhua He, Yuanzhi Li, Periklis A. Papakonstantinou and Xin Yang, *Systematic Data Structure Lower Bounds via the Query-with-Sketch Model*, [arXiv:2609.18024v1](https://arxiv.org/html/2609.18024v1), Definition 2.1 and Theorem 1.1 | $E$ corresponds to a sketch and a boundary Read to an input-coordinate probe, with the same acquired sketch serving all late targets. The min-entropy lifting requires quantitative conditional answer bounds after permitted partial input assignments. Those bounds are not assumed here. The single-law proof establishes its own weighted converse directly. |
| Ali Makhdoumi, Shao-Lun Huang, Muriel Médard and Yury Polyanskiy, *On Locally Decodable Source Coding*, [arXiv:1308.5239v2](https://arxiv.org/html/1308.5239v2), Definition 1 | Their decoder probes compressed bits and has a distributional block-error criterion. Here the entire complete retained code is accessible, the one charged probe reads the stationary source, and correctness is simultaneous on all sources and targets. Those locality converses are not native all-source alphabet lower bounds. |
| Nicolas Charpenay, Maël Le Treust and Aline Roumy, *On the Linearization of Optimal Rates for Independent Zero-Error Source and Channel Problems*, [arXiv:2407.02281v2](https://arxiv.org/html/2407.02281v2), §§II–III | Zero-error graph products and independence hypotheses distinguish several regularized rates. Native admissibility requires a whole fiber to admit one chosen experiment for each target; pair compatibility alone does not define it. No graph-product equality or independent-source additivity is used in the scaffold or entropy proof. |

The chain rule, nonnegativity of relative entropy, conditioning
monotonicity and weighted Gibbs inequality are established information
theory, with the needed finite proofs included inside Theorem 2.2.
The repository-derived delta is the heavy-target condition sufficient
for all joint lengths, its explicit asymmetric native depth-three
verification, and the resulting strict original-rate lower.
The literature correspondences do not confer Lean evidence or global
priority on that delta.

**Proposition 7.3 (the precise recovery relation retained).** Under
the original paid handoff, continuity and authentication assumptions,
the existing native cover constructions realize

$$
(E(t),D,p,\text{at most one actual literal reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{NCE.48}
$$

Proof. The first arrow is exactly the supplied reply-to-factor
decoder of a paid native admissible cover, with its experiment
chosen after $p$ and before $k$. The two inverse maps on the
attained factor and trajectory images are (NCE.6) and recovery
of first branch count and alpha-stage presence from Convention 1.3.
The new lower bounds the complete alphabets of every such service;
it does not add another acquisition operation. $\square$

**Open problem 7.4 (sharpness, convergence and the unchanged programme).**
Determine exact $\lambda$, the general finite $M_1(D)$, and matching
native primal constructions or stronger all-correlated converses.
In particular the new bound does not settle $M_1(3)$, exact
$Z_3(n)$ or exact $\sigma_3$. A single dual with an attained
mass cap does not show that arbitrary optimal covers can saturate it.

The supplied FMR structure is retained:

$$
\lambda=\sup_{d\ge1}2^{-d}\sigma_d,\qquad
0\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,
\quad
\phi=\lim_{h\to\infty}2^{-h}\log_2U_h,
\quad U_0=1,\quad U_{h+1}=1+U_h^2.
\tag{NCE.49}
$$

Each $\sigma_d$ is itself an infimum over all joint lengths. This
source gives a uniform lower at $d=3$, rather than effective
lower endpoints converging to $\lambda$. A bound of the form
$\sigma_d\ge n^{-1}\log_2K_d(n)-\eta_d(n)$ with an explicit
uniform $\eta_d(n)\to0$, or a convergent family of sufficient
dual certificates, remains an original missing relation. No
completeness of the heavy-target method is asserted.

The inverse in (NCE.48) recovers the selected temporal factor,
not the whole source, past hidden histories, the complete code,
authenticity of $k$, or physical space and time. The broader
minimal-relations, internal-observer and mutual-recovery programme
still requires explicit object and operation correspondences and
their resource bounds. Preparation, installed tables, workspace,
word length, final predictors, handoff, isolation, authentication
and physical time retain all their original separate charges.
The strict lower leaves these sharp and broader objectives open.

[LTR]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_ONE_READ_MEMORY.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[AAR]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NBP]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[NCM]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[D5-source]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[D5-read]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[D5-present]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5-quotient]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean
[D5-compact]: https://github.com/the-omega-institute/trureturing/blob/87b4c51addc0da5ef8847a9adc723bde11a3f908/D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean

## 追加锚（本行以下为增补区）

## 8. A positive joint depth-three weight law

**Definition 8.1 (joint child-category weights).** Retain exactly the
source, substitution, observations, request menu and paid-export contract
of §1. Write $A=\alpha$, $B=\beta$ and

$$
\mathcal G=\{\langle u,v\rangle:u,v\in S_1\},\qquad
S_2=\{A,B\}\sqcup\mathcal G,\qquad |\mathcal G|=9.
\tag{NCE.50}
$$

Let $c:S_2\to\{A,B,G\}$ send the two leaves to their respective
symbols and every member of $\mathcal G$ to $G$. In this category order
put

$$
M=\begin{pmatrix}
281&1131&271\\
1131&1437&237\\
271&237&53
\end{pmatrix},\qquad
w_{\rm j}(A)=4947,\quad w_{\rm j}(B)=3264,\quad
w_{\rm j}(\langle x,y\rangle)=M_{c(x),c(y)}.
\tag{NCE.51}
$$

This notation is separate from the weights $w$ in (NCE.31). Every state
of $S_3$ has positive $w_{\rm j}$ weight. For $e=(1,1,9)^{\mathsf T}$,

$$
W_{\rm j}:=w_{\rm j}(S_3)=4947+3264+e^{\mathsf T}Me
=8211+17417=25628,\qquad
C_{\rm j}:=9996,\qquad \mu_{\rm j}:=w_{\rm j}/25628.
\tag{NCE.52}
$$

The branch table is a genuine joint child weight: its $A,B$ principal
minor is $281\cdot1437-1131^2=-875364\ne0$. Thus it cannot have the
form $u(c(x))v(c(y))$. Categories and weights are mathematical counting
data. They are not retained descriptors, source observations or inputs to
a reader. An entire original block receives its weight once.

**Lemma 8.2 (five finite child count bounds).** For $U\subseteq S_2$
write

$$
n(U)=(\mathbf1_{A\in U},\mathbf1_{B\in U},|U\cap\mathcal G|),\quad
d_s(U)=|\Gamma_s(U)|\ (s=L,R),\quad
k(U)=|\{r_u(\varepsilon):u\in U\}|.
\tag{NCE.53}
$$

Here $k(U)$ counts attained root constructors, and is zero for empty
$U$. A vector is dominated by a family if it is componentwise at most
one member of that family. The following implications hold, with the
families ordered exactly as displayed:

$$
\begin{aligned}
\mathcal F_4&=((1,0,9),(0,1,9),(1,1,4)),\\
\mathcal F_3&=((0,0,9),(1,0,4),(0,1,4),(1,1,1)),\\
\mathcal F_{4A}&=((1,0,9),(1,1,4)),\\
\mathcal F_X&=((1,1,0),(1,0,4),(0,1,1)),\\
\mathcal F_Y&=((1,1,0),(1,0,1),(0,1,1),(0,0,4)).
\end{aligned}
\tag{NCE.54}
$$

| Hypothesis on the actual set $U$ | A family dominating $n(U)$ |
| --- | --- |
| $d_L(U),d_R(U)\le4$ | $\mathcal F_4$ |
| $d_L(U),d_R(U)\le3$ | $\mathcal F_3$ |
| $d_L(U\cup\{A\}),d_R(U\cup\{A\})\le4$ | $\mathcal F_{4A}$ |
| $k(U)\le2$ and $d_L(U\cup\{A\}),d_R(U\cup\{A\})\le3$ | $\mathcal F_X$ |
| $k(U)\le2$ and $d_L(U),d_R(U)\le2$ | $\mathcal F_Y$ |

Proof. Let $\ell=|U\cap\{A,B\}|$, and let $p_L,p_R$ be the numbers
of distinct symbols from $S_1$ appearing as the two children of members
of $U\cap\mathcal G$. The exact table (NCE.26) gives

$$
d_s(U)=\ell+p_s,\qquad
|U\cap\mathcal G|\le p_Lp_R,\qquad 0\le p_s\le3.
\tag{NCE.55}
$$

For side ranges at most four, zero or one leaf permits at most nine
branches; two leaves permit at most four. The zero-leaf vector is
dominated by $(1,0,9)$. This gives $\mathcal F_4$. At range three,
the branch bounds for zero, one and two leaves are respectively
nine, four and one, giving $\mathcal F_3$.

For the third row, if $B\notin U$, adjoining $A$ leaves at most nine
branches, giving $(1,0,9)$. If $B\in U$, adjoining $A$ gives two
leaves and at most four branches, giving $(1,1,4)$.

For $\mathcal F_X$, if both leaves occur, the root-constructor bound
excludes every branch. With only $A$ present, adjoining $A$ changes
nothing and range three permits four branches. With only $B$ present,
adjoining $A$ leaves only one branch symbol per side, hence one branch.
With no leaves, adjoining $A$ permits four branches, whose count vector
is dominated by $(1,0,4)$. These are all cases. For $\mathcal F_Y$,
two leaves again exclude branches, a single leaf permits one branch,
and no leaves permit four. The empty set satisfies each applicable
bound. No locally admissible projection is assumed. $\square$

**Lemma 8.3 (complete parent-leaf collision classification).** Let
$P\subseteq S_3$ be range-feasible for all $q\in W_3$, with capacity
four, and put

$$
T=\{(x,y):\langle x,y\rangle\in P\},\qquad
X=\pi_L(T),\qquad Y=\pi_R(T).
\tag{NCE.56}
$$

Then the following child count families apply:

| $P\cap\{A,B\}$ | Family for $n(X)$ | Family for $n(Y)$ |
| --- | --- | --- |
| $\varnothing$ | $\mathcal F_4$ | $\mathcal F_4$ |
| $\{A\}$ | $\mathcal F_3$ | $\mathcal F_3$ |
| $\{B\}$ | $\mathcal F_{4A}$ | $\mathcal F_3$ |
| $\{A,B\}$ | $\mathcal F_X$ | $\mathcal F_Y$ |

Proof. At the four deep targets the parent-leaf factors, computed by
(NCE.5), are

$$
\begin{array}{c|cccc}
 &LL&LR&RL&RR\\\hline
A&(4,0)&(5,1)&(5,0)&(6,1)\\
B&(3,0)&(4,1)&(4,0)&(5,1).
\end{array}
\tag{NCE.57}
$$

For a branch these columns are respectively
$\Gamma_L(x),\Gamma_R(x),\Gamma_L(y),\Gamma_R(y)$.
The sets of possible child values are exactly $\mathcal V_L$ and
$\mathcal V_R$ from (NCE.27). In $LL$ the parent $B$ factor equals
$\Gamma_L(A)$ and no other child factor. In $LR$ it equals
$\Gamma_R(A)$ and no other child factor. The parent $A$ values in
these columns lie outside the respective child ranges. In $RL$ and
$RR$, both parent-leaf values lie outside the respective child range,
and they are distinct. This exhausts all parent-leaf versus child-factor
collisions; equal blocking-leaf descriptions are not being substituted
for equal temporal factors.

With neither parent leaf, both side ranges of both projections are
at most four. With only $A$, its extra value in each column reduces
each child range to three. With only $B$, the left restrictions are
exactly

$$
d_L(X\cup\{A\}),d_R(X\cup\{A\})\le4,
\qquad d_L(Y),d_R(Y)\le3.
\tag{NCE.58}
$$

The union with $A$ accounts also for the case in which the collision
is not attained by $X$ itself.

With both parent leaves, target $L$ adds $(3,0),(2,0)$ to
$\Gamma_\varepsilon(X)$ and target $R$ adds $(4,1),(3,1)$ to
$\Gamma_\varepsilon(Y)$. These are two distinct values outside the
child root-factor set $\{(2,1),(1,0),(0,0)\}$. Consequently
$k(X),k(Y)\le2$. At the deeper targets, removing the parent $A$ value
on the left and the two parent values on the right gives

$$
d_L(X\cup\{A\}),d_R(X\cup\{A\})\le3,
\qquad d_L(Y),d_R(Y)\le2.
\tag{NCE.59}
$$

Lemma 8.2 now gives every row, including empty branch parts.
These are necessary range conditions on the actual projections;
there is no replacement of $T$ by an independently encoded pair.
$\square$

**Proposition 8.4 (exact bilinear mass tables).** For the weights
(NCE.51), every range-feasible $P$ missing at least one parent leaf
has $w_{\rm j}(P)\le9996$. If both parent leaves occur, its branch
mass is at most $3980$.

Proof. Because $M$ is entrywise nonnegative,

$$
\sum_{(x,y)\in T}M_{c(x),c(y)}
\le n(X)^{\mathsf T}Mn(Y)
\le u^{\mathsf T}Mv
\tag{NCE.60}
$$

whenever $u,v$ dominate the respective count vectors. The first
inequality enlarges a nonnegative sum to $X\times Y$. It makes no
claim about admissibility of that product. The four complete finite
tables below use the family orders of (NCE.54). Include the indicated
parent-leaf weight in the first three tables:

$$
\left(u^{\mathsf T}Mv\right)_{
 u\in\mathcal F_4,\ v\in\mathcal F_4}
=\begin{pmatrix}
9452&9996&8976\\
9996&9996&9996\\
8976&9996&8892
\end{pmatrix},
\tag{NCE.61}
$$

$$
\left(4947+u^{\mathsf T}Mv\right)_{
 u\in\mathcal F_3,\ v\in\mathcal F_3}
=\begin{pmatrix}
9240&9294&8988&9996\\
9294&8244&8958&8874\\
8988&8958&9128&9996\\
9996&8874&9996&9996
\end{pmatrix},
\tag{NCE.62}
$$

$$
\left(3264+u^{\mathsf T}Mv\right)_{
 u\in\mathcal F_{4A},\ v\in\mathcal F_3}
=\begin{pmatrix}
9996&8976&9520&9996\\
9744&8640&9660&9996
\end{pmatrix},
\tag{NCE.63}
$$

$$
\left(u^{\mathsf T}Mv\right)_{
 u\in\mathcal F_X,\ v\in\mathcal F_Y}
=\begin{pmatrix}
3980&1920&3076&2032\\
3444&1848&2562&1932\\
3076&1692&1964&1160
\end{pmatrix}.
\tag{NCE.64}
$$

Each entry is the displayed integer bilinear expression. Their maxima
are respectively $9996,9996,9996,3980$. Lemma 8.3 and (NCE.60) prove
the assertions for every such $P$. $\square$

## 9. Exact pressure of the joint law at every length

**Theorem 9.1 (heavy targets for the joint law).** Every range-feasible
$P\subseteq S_3$ with $w_{\rm j}(P)>9996$ has a nonempty
$q\in W_3$ which is not determined on $P$ by any own-coordinate
experiment at any finite word, or by a constant experiment, and

$$
\sum_z w_{\rm j}(P\cap\Gamma_q^{-1}(z))^2
\le4947^2+7244^2=76948345<99920016=9996^2.
\tag{NCE.65}
$$

Proof. Proposition 8.4 forces $A,B\in P$. A branch has weight at
most $1437$, the largest entry of $M$. If there were at most one,
then $w_{\rm j}(P)\le4947+3264+1437=9648<9996$. Thus two distinct
branches occur. By Lemma 3.2 some nonempty $q\in W_3$ separates
them. The root experiment merges those branches. Every nonempty
finite experiment merges $A$ and $B$, returning absent on both,
whereas $\Gamma_q(A)\ne\Gamma_q(B)$. A constant experiment fails
as well. This proves nonrecoverability for the entire original
own-coordinate menu, including arbitrarily long off-target words.

Lemma 3.2 also makes $A$ alone in its $\Gamma_q$ cell. That cell
has weight $4947$. The other cells together have mass at most
$3264+3980=7244$, by Proposition 8.4. Nonnegativity gives
$\sum_j a_j^2\le(\sum_j a_j)^2$ for those other cell masses.
This proves (NCE.65). $\square$

**Theorem 9.2 (exact all-length mass and pressure).** For every
$n\ge1$ and every jointly admissible $B_0\subseteq S_3^n$,

$$
\sum_{x\in B_0}\prod_{i=1}^n w_{\rm j}(x_i)\le9996^n.
\tag{NCE.66}
$$

The maximum equals $9996^n$ at every length, including when the
maximum is taken over full solution sets of complete native decoder
templates. In the pressure notation of [NPC, Definition 5.1][NPCj],

$$
A_n(\mu_{\rm j})=\left(\frac{2499}{6407}\right)^n,
\qquad \beta_3(\mu_{\rm j})=\frac{2499}{6407}.
\tag{NCE.67}
$$

Proof of the upper. Apply Theorem 2.2 to the seven targets $W_3$,
all native boundary replies and a constant experiment, with capacity
$m=4$, weight $w_{\rm j}$ and cap $C_{\rm j}$. Theorem 9.1 proves
its entire hypothesis, even for all finite own experiments.

In particular the theorem uses the one Gibbs law proportional to
$\prod_iw_{\rm j}(x_i)$ on this actual $B_0$. A heavy projection has
an own-unrecoverable target determined by a distinct actual donor
under that same law. The permutation average charges half its target
entropy even around arbitrary cycles. Conditional Gibbs domination
then uses exactly (NCE.65). Light projections use their total mass
at most $C_{\rm j}$. No product law on a competing fiber, independent
child code, separately chosen owner law or acyclic donor ordering is
assumed. Every full block weight in (NCE.66) appears once.

Proof of equality. Put

$$
H_B=\{B\}\cup\mathcal G,\qquad
P_B=\{\langle x,y\rangle:x,y\in H_B\}\subset S_3.
\tag{NCE.68}
$$

On $H_B$ the root reply determines its root factor. At side $s$,
an absent reply identifies the known leaf $B$ and its fixed factor
$\Gamma_s(B)$; a present reply on $\mathcal G$ identifies the
constructor of that child and hence its factor among
$(2,1),(1,0),(0,0)$. Thus every $W_2$ target on $H_B$ is determined
by the literal at that same target. On $P_B$ the root factor is
constant branch; at $sq$, $s\in\{L,R\}$, $q\in W_2$, use the
single same-coordinate literal $sq$. These witnesses serve all
seven targets. There are $|P_B|=10^2=100$ states and

$$
w_{\rm j}(P_B)=(0,1,9)M(0,1,9)^{\mathsf T}
=1437+2\cdot9\cdot237+81\cdot53=9996.
\tag{NCE.69}
$$

The products $P_B^n$ retain these own-coordinate witnesses and have
mass $9996^n$. Extending their attained reply decoders arbitrarily
to total tables gives a complete native template whose solution set
contains $P_B^n$. The already proved upper bounds its mass by
$9996^n$, so its mass is exactly that value. Since $w_{\rm j}$ is
positive on every state, it has no additional solutions. This proves
attainment in both families without a separate saturation assumption.
Normalize by $W_{\rm j}^n$ and use
$9996/25628=2499/6407$ to obtain (NCE.67). $\square$

**Corollary 9.3 (the two finite envelopes at this particular law).**
With $J_d$ and the conditional-owner envelope $\Omega_d$ defined in
[COK, Definitions 2.5 and 5.1][COKj],

$$
J_3(\mu_{\rm j})=\Omega_3(\mu_{\rm j})
=\beta_3(\mu_{\rm j})=\frac{2499}{6407}.
\tag{NCE.70}
$$

Proof. Work first with $w_{\rm j}$. For a range-feasible $P$ of
mass at most $9996$, the Euclidean norm of its joint hard-target cell
masses is at most its total mass. For a heavier $P$, its hard vector
contains the target selected in Theorem 9.1. Its joint cells refine
that target's cells; splitting nonnegative masses cannot increase
the sum of their squares. Equation (NCE.65) bounds the joint norm
strictly below $9996$. It follows that $J_3(w_{\rm j})\le9996$.
On $P_B$ all targets are easy, so its hard vector is empty and its
one cell has mass $9996$. Hence $J_3(w_{\rm j})=9996$.
The credited comparison
$\beta_d\le\Omega_d\le J_d$ in COK Theorem 5.2, together with
Theorem 9.2, forces equality for $\Omega_3$ as well. Homogeneity
gives (NCE.70). This is equality at one fixed law, not optimization
over laws or proof of a conditional certificate's boundary attainment.
$\square$

## 10. Strict lower bounds for the original complete attained alphabet

**Theorem 10.1 (every original competitor and every depth).** Under
Assumption 1.2, every jointly correct original preparation and reader
satisfies, for every $D\ge3$,

$$
\boxed{\displaystyle
|E[\mathcal F_D]|\ge
 \left\lceil\left(\frac{6407}{2499}\right)^{2^{D-3}}\right\rceil.}
\tag{NCE.71}
$$

Consequently

$$
\boxed{\displaystyle
M_1(D)\ge
 \left\lceil\left(\frac{6407}{2499}\right)^{2^{D-3}}\right\rceil,
\qquad \sigma_3\ge\log_2\frac{6407}{2499},\qquad
\lambda\ge\frac18\log_2\frac{6407}{2499}.}
\tag{NCE.72}
$$

Proof. This uses the actual-scaffold restriction of Theorem 6.2,
equivalently [NPC, Theorem 7.1][NPCj], with the new cap. Its original
quantifiers can be checked directly. Set $h=D-3$, $n=2^h$, and fix a
perfect ordered height-$h$ scaffold in the right subtree. Insert the
actual $S_3$ trees at its frontier words $a_1,\ldots,a_n$, $|a_i|=h$.
Each tuple gives a distinct actual $t_x=\langle A,v_x\rangle\in
\mathcal F_D$. All these occurrences are present. For $q\in W_3$,

$$
p=Ra_iq\in\mathcal P_D,\qquad |p|=1+h+|q|\le D,
\qquad r_{\rho^kt_x}(p)=\operatorname{Pred}(\Gamma_q(x_i),k).
\tag{NCE.73}
$$

Restrict an arbitrary original complete export $E$ to this slice,
keeping its values and all its fibers unchanged. Fix one attained
name and one such request. The reader's zero-Read choice or entire
query word is fixed before a reply and before every authentic count.
Every finite original-root word is constant in the root/left wrapper
or strictly above the scaffold frontier, or enters one uniquely fixed
actual donor block with an arbitrary finite suffix. In $S_3$, a
suffix of length at most two is a boundary experiment; at length
three its reply is alpha exactly when its length-two parent is
branch and absent otherwise; at greater length it is constant absent.
Thus every query is a function of one boundary reply in that same
donor block, or a constant. It need not query the target block.

Equal selected boundary replies within this unchanged fiber produce
equal actual replies and the same final predictor. Correctness for
all later authentic $k$ makes the complete trajectories, and hence
$\Gamma_q$, equal. Constant queries and zero-Read branches make
that target constant. The restricted fiber is therefore an unrestricted
jointly admissible subset of $S_3^n$ for every target simultaneously.
This conclusion retains arbitrary cross-block correlations, different
donors for different targets, off-target words and cycles.

The mathematical product law $\mu_{\rm j}^{\otimes n}$ on the entire
slice has total mass one. By Theorem 9.2 each restricted code fiber
has mass at most $(2499/6407)^n$. They partition that slice, so
there are at least $\lceil(6407/2499)^n\rceil$ of them, and the
full original attained alphabet is at least this large. This proves
(NCE.71); no rival preparation has been replaced or granted a free
scan. The same mass argument for integral or fractional covers at
every $n\ge1$ gives

$$
Z_3(n)\ge(6407/2499)^n,\qquad
K_3(n)\ge\lceil(6407/2499)^n\rceil.
\tag{NCE.74}
$$

Take the supplied limit for $\sigma_3$, and divide the original
finite lower logarithm by $2^D=8n$ for the supplied limit $\lambda$.
This proves (NCE.72). The product law is an analytical counting
witness, not a source prior, acquired advice, imposed independence
of competing fibers or a source-dependent request. $\square$

**Corollary 10.2 (strict comparison and finite consequences).** The
lower endpoint in (NCE.72) strictly exceeds that of Theorem 6.2:

$$
6407\cdot13-2499\cdot33=824>0,
\qquad
\frac18\log_2\frac{6407}{2499}
>\frac18\log_2\frac{33}{13}.
\tag{NCE.75}
$$

In particular the certified finite ceilings from (NCE.71) are
$3,7,44,1867$ for $D=3,4,5,6$, respectively. The exact values are
not asserted, except for the separately credited $M_1(3)=4$ from
[D3, Theorem 2.3][D3j]. Combining with its paid rate upper
(Theorem 4.1) gives the valid interval

$$
\frac18\log_2\frac{6407}{2499}\le\lambda<\frac3{16}.
\tag{NCE.76}
$$

Proof. Strict monotonicity of the logarithm gives (NCE.75).
For $n=1,2,4,8$, if $m=3,7,44,1867$ respectively, exact integer
powering gives

$$
(m-1)2499^n<6407^n\le m2499^n.
\tag{NCE.77}
$$

These are precisely the four ceiling assertions. D3 supplies its
upper and its finite optimum independently of the chosen dual law.
The numerical display
$\frac18\log_2(6407/2499)\simeq0.16978726113469447$
is explanatory; strictness and all finite conclusions use the exact
rational expressions above. $\square$

## 11. A paid full-family consumer of the pressure-attaining fiber

**Proposition 11.1 (actual acquisition and exactly counted names).**
For every $D=3+h$, $h\ge0$, put $n=2^h$, and let $Q_D\subseteq S_D$
be the scaffold image of $P_B^n$ from (NCE.68) at the fixed perfect
height-$h$ frontier. There is a jointly correct preparation and reader
on the entire original $\mathcal F_D$ with exactly

$$
|E[\mathcal F_D]|=|S_D|-100^n+1
\tag{NCE.78}
$$

attained complete names. Its one merged canonical fiber is precisely
$Q_D$; all other canonical states have singleton names. On every
original source it uses at most

$$
2^D-1\text{ preparation Reads},\qquad
\max|\text{preparation literal}|=D,\qquad
\text{preparation letters}=(D-1)2^D+1.
\tag{NCE.79}
$$

Every late target uses zero Reads or one actual original-root Read
of length at most $D$, chosen before every supplied count. This is
a nonoptimal full-family realization of an equality fiber for the
chosen law; it is not an attaining construction for $M_1(D)$.

Proof. Scaffold parsing is injective and respects the defining
recursion of $S_D$, so $Q_D$ has exactly $100^n$ states. Install a
finite public table that assigns one name to $Q_D$ and a separate
name to every other member of $S_D$. Before receiving any request,
actually submit every literal $Rq$, $q\in W_D$, on the stationary
source, including absent words. These paid replies compute the
canonical state $\pi_D(v)$ of FMR Lemma 2.2. The table then computes
its complete fixed-width name. FMR's canonicalization fixes $S_D$,
so every stated name is attained on an actual source, proving
(NCE.78). The fixed scan has $\sum_{\ell=0}^{D-1}2^\ell=2^D-1$
words and $\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1$
letters, proving (NCE.79). All other accessible acquired dependence
is isolated under Assumption 1.2 after selecting the name.

At a singleton name the canonical state determines every requested
factor, so the late reader uses zero Reads. At the merged name,
write the request $p=Rq$. If $|q|<h$, its endpoint is in the fixed
scaffold and is branch. Otherwise there is a unique decomposition
$q=a_i r$, where $r\in W_3$. If $r=\varepsilon$, its endpoint is
also branch, since every member of $P_B$ is branch. These cases
have constant trajectories. For nonempty $r$, the local decoder in
Theorem 9.2 obtains $\Gamma_r$ from the actual literal at $r$ in
that block. Implement it by the one original-root word $Ra_i r=p$.
The length is at most $D$. This is one fresh Read of the same actual
stationary source; no artificial wrapper or subtree is an input.

On the full inverse image $\pi_D^{-1}(Q_D)$, canonicalization
preserves the selected boundary reply and requested temporal factor.
The same reader therefore serves all original variable shapes
assigned the merged name, including initially absent targets.
(NCE.6) then answers every subsequently supplied authentic $k$.
The fixed scaffold and finite decoder tables are public installed
data. There is no acquired frontier selector, shape tag or joint
weight table supplied as free advice. $\square$

**Convention 11.2 (complete resource and recovery boundary).** The
preparation in Proposition 11.1 is initially source-blind and depends
only on public $D$ and installed tables; the later request is absent.
A complete name includes every accessible surviving control, selector,
buffer, length, allocation and timing distinction. Fixed-width storage
and common finite control can be arranged, while the separately paid
handoff and isolation service removes access to the scanned arrays,
transcripts, intermediate names and other acquired dependence. This is
exactly the service assumption of §1; it is not physical erasure proved
from the tree equations.

Finite table generation and installation, preparation work and temporary
workspace, selection work, post-request workspace, address construction,
final predictor size, authentic-count representation, lawful entry,
isolation, continuity, authentication and physical time are separate
resources. The factor $(b,c)$ alone has $0\le b\le2D$ and
$c\in\{0,1\}$, so at most
$\lceil\log_2(2D+1)\rceil+1$ bits suffice for that factor. No
free total-efficiency conclusion is implied by the alphabet count.

Under those services the boundary observer obtains exactly

$$
(E(t),D,p,\text{zero or one actual literal reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{NCE.80}
$$

The inverse reads the first branch count and whether an alpha stage
occurs. It does not supply an unknown age, source identity, whole hidden
source, free acquired reference, hidden history or physical space-time
recovery. The source and menu remain those of Definition 1.1, with
no reset, copying, navigation or equality action.

## 12. Exact finite readings, attribution and the open bridge

**Convention 12.1 (bounded exact readings).** The finite identities in
§§8–11 admit integer and finite-tree checks without an asymptotic
sample inference. Among all $2^{11}=2048$ subsets of $S_2$, the numbers
satisfying the five hypotheses of Lemma 8.2, in their displayed order,
are $1627,704,1206,193,112$. Their numbers of distinct category-count
vectors are $35,22,30,13,10$. Each such vector is dominated by its
stated family. Equations (NCE.61)–(NCE.64) give all $45$ bilinear
entries, not selected maxima from an unreported search.

For a bounded full-family example, the number of actual trees of
height at most three is $1446$, obtained from
$T_0=2$, $T_{j+1}=2+T_j^2$. Their canonical image is all $123$
states of $S_3$. At $D=3$, Proposition 11.1 has $24$ attained names;
$1369=37^2$ actual right subtrees have the merged name, since the
canonical child lies in $H_B$ exactly when that actual child is not
$A$. The seven own-literal decoder checks on those merged sources
comprise $9583$ source/target pairs. Canonical reply and factor
preservation hold on all $1446\cdot7=10122$ source/target pairs.
Directly iterating the actual substitution for counts $0\le k\le6$
checks $70854$ replies against (NCE.6). These are bounded readings;
the all-count conclusion is supplied by Convention 1.3, and the
all-length assertion is proved by Theorem 2.2 and Theorem 9.1.
No finite template search, empirical convergence or optimality
assertion replaces those proofs.

**Convention 12.2 (credited suppliers and primary boundaries).** All
repository supplier citations with suffix `j` below designate public
revision `91170b89dfe9dd7eadc64d14d86d2157ed14abdf`. The mathematical
content here is ordinary theory, without a claim of Lean certification,
independent review or worldwide originality. The joint weight law,
finite projection bounds, exact pressure for that law and strict
original lower endpoint are `repo-derived` deductions.

Theorem 2.2 owns the all-cyclic half-entropy rule. Lemma 3.2 and tables
(NCE.26)–(NCE.27) own the separating factor and collision suppliers.
AAR owns the exact factor/trajectory equivalence. FMR owns canonical
all-word simulation, paid finite-cover implementation, actual scaffold
restriction and rate existence; NPC owns unrestricted product pressure
and its all-original-competitor consumer. Proposition 11.1 instantiates
that paid mechanism with the explicit $100^n$-state equality fiber.
COK owns the comparison used only in Corollary 9.3. D3 owns the exact
finite value $M_1(3)=4$ and the upper $\lambda<3/16$. None of these
suppliers is counted as a new general theorem here.

| Primary source | Exact mathematical correspondence and transfer limit |
| --- | --- |
| Tomasz Gogacz and Szymon Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, [arXiv:1512.01808v1](https://arxiv.org/html/1512.01808v1), Theorem 1 and Corollary 1 | A native decoder equation makes its target a function of one reply under the same tuple law. Their theorem fixes a schema, query and functional dependencies and optimizes a closed entropic cone; the submodular relaxation is an upper bound. It supplies neither the particular joint law (NCE.51) nor a finite cutoff for varying native lengths and donors. |
| Pascal O. Vontobel, *Counting in Graph Covers: A Combinatorial Characterization of the Bethe Entropy Function*, [arXiv:1012.0065v2](https://arxiv.org/html/1012.0065v2), Definition 32 and Theorem 33 | The degree-$M$ Bethe partition function is the $M$th root of the average Gibbs partition function over covers of one fixed normal factor graph; its limsup is that base graph's Bethe partition function. This is an average over a fixed graph's covers. It gives no universal upper bound for the maximum over all complete native networks, and no optimizer-cofinality is transferred. |

Finite entropy, conditional Gibbs domination and permutation averaging
are the mature machinery already proved in §2. The new numerical law
does not strengthen their epistemic status. No differently scoped
predecessor-row or finite-reader-synthesis theorem is used to infer
an all-length cap or a preparation bound.

**Open problem 12.3 (optimizer-cofinality and global completion).**
The strict endpoint is a universal certificate at one fixed rational
law and depth. It does not identify
$\min_{\mu\in\Delta(S_3)}\beta_3(\mu)$, exact $\sigma_3$, sharp
$\lambda$ or general exact $M_1(D)$. Even exact pressure at a chosen
law, attained at every length, does not give covers attaining its dual
lower bound.

The remaining [COK, Open problem 9.3][COKj] and [GDB, Definition
11.1][GDBj] obligation is a total sound cap verifier with accepted
weight-optimized endpoints cofinal at every depth, or a uniform
effective native length error sufficient for terminating two-sided
approximation. The conditional-owner local-law completion and global
entropy-loss questions remain open. [SCP, §§3–6][SCPj]'s uniform
softening estimates compare semantic all-size quantities and do not
evaluate them effectively. No length modulus, universal global-law
completion, bounded-width or mixing premise follows from (NCE.67).
The minimal-relations/internal-observer/mutual-recovery programme
retains the original sources, operations, all-view recovery objective
and separate resource obligations beyond this strict quantitative
lower consequence.

[NPCj]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[COKj]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[D3j]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[GDBj]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[SCPj]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SOFT_CONSTRAINT_PRESSURE.md

## 追加锚（本行以下为增补区）

## 13. A positive asymmetric law with five permitted heavy rectangle classes

**Convention 13.1 (unchanged task and credited machinery).** Retain
Definitions 1.1–1.4 and Assumption 1.2 in full. In particular the
source is the entire variable-shape
$\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\}$, preparation
is paid and precedes the request, and every permitted late request
must be served by at most one arbitrary finite original-root Read
of that same stationary source, before any authentic count. All
accessible surviving source distinctions count in the export.
The exact factors and their trajectory equivalence are the credited
AAR supplier in Convention 1.3. Theorem 2.2 supplies the all-cyclic
entropy rule; Lemmas 3.2, 8.2 and 8.3 supply separation and necessary
projection counts. They are reused, rather than new general results
of the weight calculation below.

Repository citations with suffix `a` in §§13–19 designate the public
committed source at
`ce2fe4a685b5a195b8b0a380616daf0151f576cb`. The conclusions are
ordinary mathematics, without a Lean-certification claim. The
specific new law permits certain locally insufficient projections
to exceed its cap. Their hard targets, rather than a bound on their
total mass, make the same entropy rule applicable.

**Definition 13.2 (the full asymmetric block law).** Write
$A=\alpha$, $B=\beta$, $C_0=\langle A,A\rangle$, and retain

$$
S_1=\{A,B,C_0\},\qquad
\mathcal G=\{\langle u,v\rangle:u,v\in S_1\},\qquad
S_2=\{A,B\}\sqcup\mathcal G,\qquad
S_3=\{A,B\}\sqcup\{\langle x,y\rangle:x,y\in S_2\}.
\tag{NCE.81}
$$

Thus $|S_2|=11$ and $|S_3|=123$. Let $c(A)=A,c(B)=B$ and
$c(g)=G$ for $g\in\mathcal G$. In category order $A,B,G$, set

$$
M_{\rm a}=\begin{pmatrix}
254586&1024686&251250\\
1024686&1347714&215358\\
250826&214934&48071
\end{pmatrix},\qquad
w_{\rm a}(A)=4481982,\quad w_{\rm a}(B)=2959092,
\tag{NCE.82}
$$

and $w_{\rm a}(\langle x,y\rangle)=(M_{\rm a})_{c(x),c(y)}$.
Every actual state has positive weight. Put

$$
\begin{aligned}
C_{\rm a}&=9114093,& m_{\rm a}&=48071,\\
W_{\rm a}&=w_{\rm a}(S_3)=23377809,&
\mu_{\rm a}(x)&=w_{\rm a}(x)/W_{\rm a},\\
\frac{C_{\rm a}}{W_{\rm a}}&=\frac{3038031}{7792603},&
R_{\rm a}&=\frac{7792603}{3038031}.
\end{aligned}
\tag{NCE.83}
$$

For $e=(1,1,9)^{\mathsf T}$ the exact total is
$4481982+2959092+e^{\mathsf T}M_{\rm a}e
=7441074+15936735=23377809$. The minimum state weight is
$m_{\rm a}$. The table is asymmetric, and its $A,B$ principal
minor is $-706872282192\ne0$; it is not a product of separate
child weights. Each original block receives this whole weight once.
Categories, weights and hard-target choices are mathematical
counting data, never acquired advice supplied to a reader.

**Definition 13.3 (relations, range and pressure).** At depth three
the target menu is exactly
$W_3=\{\varepsilon,L,R,LL,LR,RL,RR\}$. A relation
$H\subseteq S_3^n$ is jointly admissible when, for every $i,q$,
$\Gamma_q(x_i)$ is constant on $H$ or is a function of one
$r_{x_j}(a)$ on that same $H$, with $a$ any finite word.
Different targets may use different donors and words; self donors,
off-target words, arbitrary correlations and cycles are allowed.
The constant experiment represents zero Reads. Canonical all-word
simulation in §1 makes this exactly the credited finite native
family. A projection $P\subseteq S_3$ is range-feasible when
$|\Gamma_q(P)|\le4$ for every $q\in W_3$.

Use [NPC, Definitions 2.2 and 5.1][NPCa]: $A_n(\mu)$ is the
maximum product-$\mu$ mass of a complete native template's full
solution set on $n$ coordinates, and
$\beta_3(\mu)=\sup_{n\ge1}A_n(\mu)^{1/n}$. Every admissible
relation is contained in such a full solution set, with the same
coordinates and nonnegative mass. No factorization of a competitor
is included in these definitions.

## 14. Exhaustive projection masses and the minimum-state charge

**Proposition 14.1 (all four integer projection tables).** For a
range-feasible $P\subseteq S_3$, let
$T=\{(x,y):\langle x,y\rangle\in P\}$ and let $X,Y$ be its
two projections. For $U\subseteq S_2$ write
$n(U)=(\mathbf1_{A\in U},\mathbf1_{B\in U},|U\cap\mathcal G|)$.
Use precisely the ordered families of Lemma 8.2:

$$
\begin{aligned}
\mathcal F_4&=((1,0,9),(0,1,9),(1,1,4)),\\
\mathcal F_3&=((0,0,9),(1,0,4),(0,1,4),(1,1,1)),\\
\mathcal F_{4A}&=((1,0,9),(1,1,4)),\\
\mathcal F_X&=((1,1,0),(1,0,4),(0,1,1)),\\
\mathcal F_Y&=((1,1,0),(1,0,1),(0,1,1),(0,0,4)).
\end{aligned}
\tag{NCE.84}
$$

In their displayed orders the complete tables are

$$
\left(u^{\mathsf T}M_{\rm a}v\right)_{
 u,v\in\mathcal F_4}
=\begin{pmatrix}
8667021&9114093&8206668\\
9114093&9114093&9156228\\
8212604&9162164&8150280
\end{pmatrix},
\tag{NCE.85}
$$

$$
\left(4481982+u^{\mathsf T}M_{\rm a}v\right)_{
 u,v\in\mathcal F_3}
=\begin{pmatrix}
8375733&8469972&8146944&9106461\\
8473788&7514008&8140540&8067828\\
8150760&8140540&8320000&9125064\\
9114093&8070796&9128032&9114093
\end{pmatrix},
\tag{NCE.86}
$$

$$
\left(2959092+u^{\mathsf T}M_{\rm a}v\right)_{
 u\in\mathcal F_{4A},\ v\in\mathcal F_3}
=\begin{pmatrix}
9114093&8206668&8653740&9114093\\
8889120&7877236&8826796&9132696
\end{pmatrix},
\tag{NCE.87}
$$

$$
\left(u^{\mathsf T}M_{\rm a}v\right)_{
 u\in\mathcal F_X,\ v\in\mathcal F_Y}
=\begin{pmatrix}
3651672&1745880&2839008&1866432\\
3142312&1701424&2327956&1774136\\
2838160&1538941&1826077&1053716
\end{pmatrix}.
\tag{NCE.88}
$$

The first three tables bound $w_{\rm a}(P)$ when its parent-leaf
set is respectively empty, $\{A\}$ or $\{B\}$. The fourth
bounds the branch mass when both parent leaves occur. Exactly five
entries in the first three tables exceed $C_{\rm a}$, and their
excesses are respectively $42135,48071,10971,13939,18603$ in
the order of the support classes in Lemma 14.2 below.

Proof. Lemma 8.3 assigns the families, including the asymmetric
parent-$B$ collision. If $u,v$ dominate $n(X),n(Y)$, positivity
gives

$$
\sum_{(x,y)\in T}(M_{\rm a})_{c(x),c(y)}
\le n(X)^{\mathsf T}M_{\rm a}n(Y)
\le u^{\mathsf T}M_{\rm a}v.
\tag{NCE.89}
$$

Adding the actual parent-leaf contribution gives the indicated
table entry. These inequalities enlarge a nonnegative sum; they
do not assert that $T$ is a product or that its full rectangle is
admissible. Each displayed integer is the corresponding three-by-three
bilinear expression. Inspection of all $33$ entries in
(NCE.85)–(NCE.87) gives the five excesses, all at most
$m_{\rm a}$; the maximum of (NCE.88) is $3651672$. $\square$

**Lemma 14.2 (every heavy support missing a parent leaf).** Use
$X\boxdot Y=\{\langle x,y\rangle:x\in X,y\in Y\}$. For
$U,V\subseteq S_1$, $|U|=|V|=2$, and $g\in\mathcal G$, put

$$
Q=\{\langle u,v\rangle:u\in U,v\in V\},\quad
T_Q=\{A,B\}\cup Q,\quad B_Q=\{B\}\cup Q,\quad
H_B=\{B\}\cup\mathcal G,\quad U_g=\{A,B,g\}.
\tag{NCE.90}
$$

Every range-feasible $P$ with $w_{\rm a}(P)>C_{\rm a}$ and
$P\cap\{A,B\}\ne\{A,B\}$ is in exactly one of the following
five classes:

| Class | Actual support $P$ | Number of supports | Mass |
| --- | --- | ---: | ---: |
| I | $H_B\boxdot T_Q$ | $9$ | $9156228$ |
| II | $T_Q\boxdot H_B$ | $9$ | $9162164$ |
| III | $\{A\}\cup(B_Q\boxdot U_g)$ | $81$ | $9125064$ |
| IV | $\{A\}\cup(U_g\boxdot B_Q)$ | $81$ | $9128032$ |
| V | $\{B\}\cup(T_Q\boxdot U_g)$ | $81$ | $9132696$ |

This classification starts with arbitrary correlated supports.

Proof. If $T$ is empty, the mass is at most
$w_{\rm a}(A)+w_{\rm a}(B)<C_{\rm a}$, so assume $T$ is
nonempty. Choose a dominating pair $u,v$ from the applicable
table. If its entry is at most $C_{\rm a}$, (NCE.89) already
excludes heaviness. Thus the entry is one of the five listed
heavy entries, and is at most $C_{\rm a}+m_{\rm a}$.

Enlarge the actual sets $X,Y$ to sets $X',Y'\subseteq S_2$
with counts exactly $u,v$. Such extensions exist: the two leaf
counts are zero or one, and at most nine distinct members of
$\mathcal G$ are requested. If either count domination is
strict, $X'\times Y'$ contains at least one pair outside
$X\times Y$, since both original projections are nonempty.
If $T$ is a proper subset of $X\times Y$, it already omits
a pair. Each omitted actual branch state has weight at least
$m_{\rm a}$. In either event,

$$
w_{\rm a}(P)\le
\text{its dominating entry}-m_{\rm a}\le C_{\rm a}.
\tag{NCE.91}
$$

Consequently heaviness forces both exact count vectors and
$T=X\times Y$.

The five heavy entries have, in order, count pairs

$$
\begin{array}{c|c|c|c}
 &P\cap\{A,B\}&n(X)&n(Y)\\\hline
\mathrm I&\varnothing&(0,1,9)&(1,1,4)\\
\mathrm {II}&\varnothing&(1,1,4)&(0,1,9)\\
\mathrm {III}&\{A\}&(0,1,4)&(1,1,1)\\
\mathrm {IV}&\{A\}&(1,1,1)&(0,1,4)\\
\mathrm V&\{B\}&(1,1,4)&(1,1,1).
\end{array}
\tag{NCE.92}
$$

A four-branch projection in rows I, II or V has both leaves
and side ranges at most four. By (NCE.55), its branch part
has at most two child symbols on each side. A four-branch
projection in rows III or IV has one leaf and side ranges
at most three, with the same consequence. Four distinct pairs
on at most two symbols per side force exactly two symbols on
each side and all four pairs. Thus each such part is an
actual $Q$ of (NCE.90). A one-branch projection is exactly
$U_g$, and a nine-branch projection with only $B$ is $H_B$.
These observations prove the five forms without assuming a
product at the start. There are $\binom32^2=9$ choices of
$Q$ and nine of $g$. Their full rectangles and parent-leaf
sets determine those choices uniquely, giving the counts.
$\square$

## 15. Hardness against every finite word and exact cell bounds

**Lemma 15.1 (all-word hard targets in the five classes).** In
classes I–V of Lemma 14.2, respectively choose
$q=RL,LL,LL,RL,LL$. No own-coordinate experiment at any
finite word determines this target on its support. The constant
experiment also fails. The unordered lists of its four target-cell
masses and their exact squared sums are

$$
\begin{array}{c|c|r}
 &\text{cell masses}&\sum_z A_{q,z}(P)^2\\\hline
\mathrm I&(3282120,3282120,1295994,1295994)&24903824284872\\
\mathrm {II}&(3285936,3285936,1295146,1295146)&24949557114824\\
\mathrm {III}&(4481982,2587758,1027662,1027662)&28896832487376\\
\mathrm {IV}&(4481982,2587334,1029358,1029358)&28901615660208\\
\mathrm V&(4489614,2587758,1027662,1027662)&28965303708048.
\end{array}
\tag{NCE.93}
$$

All five squared sums are strictly below

$$
C_{\rm a}^2=83066691212649.
\tag{NCE.94}
$$

Proof of hardness. In each row write the chosen target as $sL$,
where $s$ is the side of the displayed $Q$. Choose
$u\ne u'$ in $U$ and a fixed $v\in V$. The two child
states $\langle u,v\rangle,\langle u',v\rangle\in Q$
have the same branch root reply, but their $L$ factors are
$\gamma(u)\ne\gamma(u')$, using (NCE.26). In the full
outer rectangle keep the opposite child fixed and use these two
states on side $s$. They give equal replies at the outer root,
at the root of child $s$, and at every word in the opposite
child cone, but different chosen target factors. This proves
failure for all those words, and proves nonconstancy.

Every remaining finite word is $sa$ with $a\ne\varepsilon$.
For classes I and II, the designated child set $T_Q$ contains
both leaves $A,B$. Take those two child states with the other
child fixed. Every such $sa$ returns absent on both, whereas
their target factors are $\Gamma_L(A)=(3,0)$ and
$\Gamma_L(B)=(2,0)$.

For class III, use the parent state $A$ and a branch with its
designated left child $B$. Every $La$, $a\ne\varepsilon$,
is absent on both. Their $LL$ factors are $(4,0)$ and
$(2,0)$. In class IV the parent $A$ and a branch with
designated right child $B$ likewise merge at every proper
right-child word, while their $RL$ factors are $(5,0)$
and $(2,0)$. For class V use the parent $B$ and a branch
with left child $B$. Their $LL$ factors are $(3,0)$ and
$(2,0)$ and again every proper left-child word is absent.
These cases partition the entire finite-word menu. Nonconstancy
also excludes the constant experiment.

Proof of the cell arithmetic. On a branch at target $sL$,
the target value is $\Gamma_L$ of its designated child.
For each $Q=U\times V$ in (NCE.90), its two first-child
symbols give two distinct factors, each occurring in exactly
two members of $Q$. Every member of $\mathcal G$ has the
same category weight in the outer matrix. This makes the
listed masses independent of the particular $U,V,g$.

In class I, designated child $A$ and $B$ have masses
$1024686+9\cdot250826=3282120$ and
$1347714+9\cdot214934=3282120$. Each of its two $Q$
cells has mass $2(215358+9\cdot48071)=1295994$.
Their factors are the two leaf-side factors and two distinct
members of $\{(2,1),(1,0),(0,0)\}$, so these four cells
are distinct. Class II instead uses row sums:
$1024686+9\cdot251250=3285936$,
$1347714+9\cdot215358=3285936$, and
$2(214934+9\cdot48071)=1295146$ twice.

For class III the parent $A$ is its own cell of mass
$4481982$. The designated child $B$ contributes
$1024686+1347714+215358=2587758$. Each $Q$ cell
contributes $2(250826+214934+48071)=1027662$.
For class IV these become the column sums
$1024686+1347714+214934=2587334$ and
$2(251250+215358+48071)=1029358$, with the same
parent cell. The parent factors $(4,0)$ or $(5,0)$
are distinct from every displayed child factor.

In class V the parent $B$ has $LL$ factor $(3,0)$,
which equals the factor from designated child $A$. They
must be combined, giving
$2959092+(254586+1024686+251250)=4489614$.
The designated child $B$ contributes $2587758$, and each
$Q$ cell contributes $1027662$. No other collision occurs
by (NCE.26)–(NCE.27). Squaring and adding gives (NCE.93).
This counts temporal factors, including their actual collisions,
rather than distinct descriptions of blocking positions.
$\square$

**Lemma 15.2 (heavy supports containing both parent leaves).**
Every range-feasible $P$ with $A,B\in P$ and
$w_{\rm a}(P)>C_{\rm a}$ has an own-unrecoverable
nonempty target $q\in W_3$ for the entire finite-word menu,
and for that target

$$
\sum_z A_{q,z}(P)^2
\le4481982^2+6610764^2
=63790363312020<C_{\rm a}^2.
\tag{NCE.95}
$$

Proof. If there is at most one branch, its mass is at most
$4481982+2959092+1347714=8788788<C_{\rm a}$.
Thus choose two distinct branches. Lemma 3.2 gives a
nonempty target $q$ distinguishing them. A root query merges
those branches. Every nonempty query merges the parent leaves,
both of which give absent, although
$\Gamma_q(A)\ne\Gamma_q(B)$. Thus no finite query or
constant experiment determines $q$.

Lemma 3.2 also says that $A$ is alone in its $q$-cell:
its factor differs from that of $B$ and of every branch.
Equation (NCE.88) bounds the total branch mass by $3651672$,
so all other cells together have mass at most
$2959092+3651672=6610764$. For nonnegative cell masses,
their squared sum is at most the square of their total.
Separating the parent-$A$ cell proves (NCE.95). This includes
every number and shape of branches, not just full rectangles.
$\square$

**Theorem 15.3 (complete heavy-target certificate).** Every
range-feasible $P\subseteq S_3$ with
$w_{\rm a}(P)>C_{\rm a}$ has a target which is
unrecoverable by every own finite literal or constant experiment
and whose squared cell-mass sum is at most $C_{\rm a}^2$.

Proof. If a parent leaf is missing, Lemma 14.2 is exhaustive
and Lemma 15.1 proves both required properties in each of its
five classes. If both parent leaves occur, Lemma 15.2 proves
them. These alternatives exhaust all supports. $\square$

## 16. Exact all-length pressure and fixed-law envelope equality

**Theorem 16.1 (exact pressure at the asymmetric law).** For
every $n\ge1$ and every jointly admissible
$H\subseteq S_3^n$,

$$
\sum_{x\in H}\prod_{i=1}^n w_{\rm a}(x_i)
\le C_{\rm a}^n.
\tag{NCE.96}
$$

At every $n$ equality is attained by the full solution set of
an actual complete template. In the notation of Definition 13.3,

$$
\boxed{\displaystyle
A_n(\mu_{\rm a})=\left(\frac{3038031}{7792603}\right)^n,
\qquad \beta_3(\mu_{\rm a})=\frac{3038031}{7792603}.}
\tag{NCE.97}
$$

Proof of the upper. Apply the credited Theorem 2.2 with
$S=S_3$, the seven full temporal targets, all finite literal
experiments and the constant experiment, reply capacity four,
weight $w_{\rm a}$ and cap $C_{\rm a}$. Theorem 15.3
checks its entire hypothesis. Equivalently canonical all-word
simulation reduces the experiments to a finite boundary menu.
The conclusion holds for every correlated admissible relation
and therefore for every full complete-template solution set.
The entropy proof uses its one actual Gibbs law and permits
arbitrary donor cycles. It does not assume a completion oracle
or independent coordinates inside the relation.

Proof of attainment. Use the credited set from (NCE.68),

$$
P_B=H_B\boxdot H_B,\qquad |P_B|=100.
\tag{NCE.98}
$$

Here are its existing literal witnesses. On $H_B$ the root
reply determines the root factor. At side $s$, an absent
reply identifies the known root leaf $B$ and hence
$\Gamma_s(B)$. A present reply comes from a branch
$\langle u,v\rangle\in\mathcal G$ and identifies its
addressed child's constructor, hence the factor among
$(2,1),(1,0),(0,0)$. Thus every target in $W_2$ on
$H_B$ is determined by its own literal. On $P_B$ the
root factor is constant branch, and at $sq$, $q\in W_2$,
the same literal $sq$ determines its target. These serve
all seven targets. Under the new weights its exact mass is

$$
\begin{aligned}
w_{\rm a}(P_B)
&=1347714+9\cdot215358+9\cdot214934+81\cdot48071\\
&=9114093=C_{\rm a}.
\end{aligned}
\tag{NCE.99}
$$

The product $P_B^n$ has those same-coordinate witnesses and
mass $C_{\rm a}^n$. Complete each attained reply decoder
arbitrarily on unused replies, always into its actual target
range. The resulting complete template contains $P_B^n$.
Its mass is at most $C_{\rm a}^n$ by the upper just proved.
Every state weight is positive, so any additional solution
would increase the mass strictly. Its full solution set is
therefore exactly $P_B^n$. Division by $W_{\rm a}^n$
proves (NCE.97). This reuses the known equality fiber and
its paid native meaning; the new input is its exact mass
and the exhaustive upper at this law. $\square$

**Corollary 16.2 (both finite envelopes at this fixed law).**
With the definitions of [COK, Definitions 2.5 and 5.1][COKa],

$$
J_3(\mu_{\rm a})=\Omega_3(\mu_{\rm a})
=\beta_3(\mu_{\rm a})=\frac{3038031}{7792603}.
\tag{NCE.100}
$$

Proof. For clarity, $J_3(w)$ is the maximum, over nonempty
range-feasible $P$, of the Euclidean norm of its cell masses
under the vector of all targets having no own boundary-reply
decoder on $P$, including constants as easy. If
$w_{\rm a}(P)\le C_{\rm a}$, that norm is at most the
total mass. Otherwise Theorem 15.3 supplies one target in
this hard vector. Its joint cells refine that target's
cells, so their squared sum cannot increase: for nonnegative
$a,b$, $a^2+b^2\le(a+b)^2$. Lemmas 15.1–15.2
therefore bound the joint norm by $C_{\rm a}$. Hence
$J_3(w_{\rm a})\le C_{\rm a}$. On $P_B$ every target
is easy, so its hard vector is empty and its sole cell
has mass $C_{\rm a}$. Equality follows for $J_3$.

The conditional-owner envelope $\Omega_3$ is exactly the
maximum of the one-law, full actual-owner-group objectives
in COK Definition 2.5, retaining their joint owner-image
tests. COK Theorem 5.2 gives
$\beta_3\le\Omega_3\le J_3$. Insert Theorem 16.1
and normalize to force (NCE.100). These are equalities
at one specified law; none optimizes over laws or asserts
positive rational kernel acceptance at the boundary cap.
$\square$

## 17. A strict converse for every original complete export

**Theorem 17.1 (all original competitors, all depths).** For
every $D\ge3$ and every jointly correct original preparation
and reader of Assumption 1.2, with its complete attained
export $E$,

$$
\boxed{\displaystyle
|E[\mathcal F_D]|\ge
\left\lceil R_{\rm a}^{\,2^{D-3}}\right\rceil.}
\tag{NCE.101}
$$

Consequently

$$
\boxed{\displaystyle
M_1(D)\ge\left\lceil
\left(\frac{7792603}{3038031}\right)^{2^{D-3}}\right\rceil,
\quad \sigma_3\ge\log_2\frac{7792603}{3038031},
\quad \lambda\ge\frac18\log_2\frac{7792603}{3038031}.}
\tag{NCE.102}
$$

Proof. This is [NPC, Theorem 7.1][NPCa], equivalently the
actual-scaffold argument of Theorem 10.1, applied to the new
cap; its unchanged quantifiers can be spelled out directly.
Put $h=D-3$ and $n=2^h$. Fix a perfect ordered scaffold of
height $h$ in the actual right subtree. At its frontier
words $a_1,\ldots,a_n$, each of length $h$, insert every
tuple $x\in S_3^n$ of actual trees. It gives a distinct
actual $t_x=\langle A,v_x\rangle\in\mathcal F_D$.
All these frontier occurrences are present. For every $i$
and $q\in W_3$ the source-independent request
$p=Ra_iq$ is permitted, with $|p|\le D$, and its full
trajectory has factor $\Gamma_q(x_i)$ by homomorphic
transport at that present occurrence.

Restrict the arbitrary original complete code to this one
mandatory slice, without replacing any of its names or
fibers. At a fixed attained name and request, the choice
of zero Reads or of one entire word is fixed before its
reply and before every authentic count. Every finite
original-root word has one of these forms: it stays in the
fixed wrapper, ends strictly above the scaffold frontier,
or enters one uniquely fixed frontier block. The first
two give constants. In the third case its suffix may
be any finite word. On an actual $S_3$ block a suffix
of length at most two is a boundary experiment; a
length-three reply is alpha exactly when its length-two
parent is branch, and absent otherwise; every longer
reply is absent. Thus it is a function of one boundary
reply in that same actual donor block or is constant.
The donor need not be the target block.

Equal selected boundary replies on this unchanged code
fiber yield equal actual replies and the same final
predictor. Correctness for every subsequently supplied
authentic $k$ gives equal complete target trajectories,
hence equal $\Gamma_q$ by Convention 1.3. Zero-Read
and constant-reply branches make the target constant.
This proves joint admissibility of every nonempty
restricted fiber for every target simultaneously. All
its cross-block correlations, off-target donor choices
and cycles have been retained.

Give the entire slice the analytical product law
$\mu_{\rm a}^{\otimes n}$. Each restricted fiber has
mass at most $(C_{\rm a}/W_{\rm a})^n=R_{\rm a}^{-n}$
by Theorem 16.1, and the fibers partition total mass one.
Their number is therefore at least $\lceil R_{\rm a}^n\rceil$,
and the full attained original alphabet is at least that
large. No competitor has received free preparation data
or been restricted to independently chosen child codes.

At every integer length the same mass witness gives
$Z_3(n)\ge R_{\rm a}^n$ and
$K_3(n)\ge\lceil R_{\rm a}^n\rceil$. The credited
FMR limits give the $\sigma_3$ assertion. Divide the
original finite logarithmic bound by $2^D=8n$ and use
the original rate limit for $\lambda$. The product law
is a counting witness, not a source prior, acquired advice
or independence imposed inside any competitor fiber.
$\square$

**Corollary 17.2 (strict rational comparison and finite consequence).**
The endpoint in (NCE.102) strictly exceeds the credited
endpoint of Theorem 10.1, because

$$
7792603\cdot2499-6407\cdot3038031=9050280>0.
\tag{NCE.103}
$$

In particular

$$
M_1(6)\ge1874.
\tag{NCE.104}
$$

The new finite ceilings in (NCE.102) at $D=3,4,5,6$
are respectively $3,7,44,1874$. These are lower bounds;
the separately credited exact $M_1(3)=4$ is unchanged.
Combining only with the credited [D3, Theorem 4.1][D3a]
gives the valid pair of inequalities

$$
\frac18\log_2\frac{7792603}{3038031}\le\lambda<\frac3{16}.
\tag{NCE.105}
$$

Proof. Equation (NCE.103) compares the positive rational
ratios before taking the strictly increasing logarithm.
For $n=1,2,4,8$ and $m=3,7,44,1874$, respectively,
exact integer arithmetic gives

$$
(m-1)3038031^n<7792603^n\le m3038031^n.
\tag{NCE.106}
$$

For example the three integer values in the $n=8$
comparison, in increasing order, are

$$
\begin{gathered}
1873\cdot3038031^8
=13591750259290010266833908062638819829841612034091638993,\\
7792603^8
=13597542057106223423647696914192787498632375868628456161,\\
1874\cdot3038031^8
=13599006933213816999491053769025706546248361426528420434.
\end{gathered}
\tag{NCE.107}
$$

This proves the ceilings and (NCE.104). The upper is an
independent credited construction, not an inference from
pressure attainment at this law. For orientation only,
the exact lower expression is approximately
$0.1698710909863263$. No assertion that these are the
globally best endpoints is needed. $\square$

## 18. The credited paid equality fiber and recoverable boundary

**Proposition 18.1 (actual acquisition of the pressure-attaining fiber).**
The construction of Proposition 11.1, unchanged, realizes
the equality fiber in Theorem 16.1. Explicitly, for
$D=3+h$, $n=2^h$, merge the canonical scaffold image
of $P_B^n$ and name every other canonical $S_D$ state
separately. Its complete attained alphabet on the entire
original $\mathcal F_D$ is exactly

$$
|S_D|-100^n+1.
\tag{NCE.108}
$$

On every source preparation uses exactly $2^D-1$ Reads,
maximum submitted length $D$ and $(D-1)2^D+1$ letters.
Every late request uses zero Reads or one actual
original-root Read of length at most $D$, before every
supplied count. This is a nonoptimal full-family consumer
of the chosen equality fiber, not equality for $M_1(D)$.

Proof with the paid correspondence. The ordered scaffold
map is injective on $P_B^n$, so its image has $100^n$
canonical states. Before any request, the source-blind
preparer actually submits every $Rq$, $|q|\le D-1$,
in one fixed public order, including absent replies.
The credited FMR canonicalization computes $\pi_D(v)$
from this paid table. A public finite installed lookup
then gives the merged-or-singleton name. Canonicalization
fixes $S_D$, so all those names are attained, proving
(NCE.108). The scan has
$\sum_{\ell=0}^{D-1}2^\ell=2^D-1$ words and
$\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1$
letters. This acquisition depends only on public $D$
and common tables, never on the later request.

At singleton names every factor is fixed, so use zero
Reads. At the merged name, a target above the frontier
ends at a known branch. A target $Ra_iq$ entering a
block has $q\in W_3$; if $q=\varepsilon$ its factor
is also constant branch. Otherwise the own-literal
witness for $P_B$ in Theorem 16.1 is implemented by
the one actual word $Ra_iq=p$, with length at most
$D$. This single reply gives the requested full factor
and (NCE.6) supplies every authentic subsequent count.
The prefix identifies an actually present occurrence;
no subtree or extra root is supplied as an input.

On all original variable shapes assigned that name,
canonicalization preserves both the selected boundary
reply and the full requested factor. Thus the reader
also serves the entire inverse-image fiber, including
initially absent targets. Fixed-width names, public
allocation and a padded finite selection schedule,
together with the declared separately paid isolation
and handoff, leave no additional accessible acquired
distinctions: the scan arrays, transcripts, intermediate
selectors, buffers, lengths, allocation, control and
accessible timing beyond the name are isolated. Those
services are premises of Assumption 1.2. This is exactly
the credited Proposition 11.1 mechanism; it is independent
of which analytical positive law is used to weigh the
same fiber. $\square$

**Convention 18.2 (separate costs and the observer's recovery).**
Common table generation and installation, preparation work,
control and temporary storage, address generation, post-request
workspace, final predictor size, authentic-count representation,
lawful entry, handoff, isolation, source continuity,
authentication and physical time remain separate resources.
No physical erasure theorem or preparation-cost optimum is
inferred. The factor alone still fits in
$\lceil\log_2(2D+1)\rceil+1$ bits, since $0\le b\le2D$
and $c\in\{0,1\}$.

Under those paid services the operational relation is exactly

$$
(E(t),D,p,\text{zero or one actual literal reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{NCE.109}
$$

The inverse reads the first branch count and the existence
of an alpha stage. The converse (NCE.101) lower-bounds
every complete retained alphabet permitting this recovery
with the prescribed timing. It recovers neither an
arbitrary whole source, an unknown age, hidden history,
nor physical space and time. The scan and the late Read
act on the same stationary source without navigation,
reset, copying, equality, source identity or advice ports.

## 19. Exact finite readings, attribution and the unchanged global goal

**Convention 19.1 (material bounded checks and their limits).**
The arithmetic and actual-tree examples admit bounded
in-memory integer checks, without retained experiment
code or data. The following readings corroborate the
displayed proof:

| Finite domain | Exact reading |
| --- | --- |
| All $123$ actual $S_3$ states | Total weight $23377809$, minimum $48071$, and pressure-fiber mass $9114093$ on its $100$ states. |
| All $2048$ subsets of $S_2$ | The five necessary count hypotheses of Lemma 8.2 hold on respectively $1627,704,1206,193,112$ sets, with $35,22,30,13,10$ distinct count vectors; every vector has the stated domination. These are checks of a credited lemma. |
| All $45$ entries of the four projection tables | Exactly the five heavy entries in (NCE.92); all their excesses are at most $48071$; maximum branch mass with both parent leaves $3651672$. |
| All $261$ actual supports in classes I–V | Counts $9,9,81,81,81$; all are range-feasible, have the stated mass and designated hard target, and give exactly the cell lists and squared sums (NCE.93). |
| Every word of length at most four on those supports | No selected hard target factors through its own reply. The proof in Lemma 15.1, rather than this bounded check, covers every finite word. Canonical words longer than three are absent. |
| All seven targets on the $100$-state $P_B$ | Each is constant or factors through that same target's own literal. The existing full-family $D=3$ construction has $24$ attained names, seven preparation Reads, maximum length three and seventeen letters. |
| All $1446$ actual right subtrees of height at most three | The paid seven-Read scan gives all $123$ canonical states and $24$ names, with $1369$ actual sources in the merged name. Reply and factor preservation hold on all $10122$ source/target pairs; $70854$ authentic-count replies for $0\le k\le6$ agree with direct substitution readout. This checks the credited paid construction, not optimal memory. |
| Rational comparison and powers $n=1,2,4,8$ | Cross-difference $9050280$ and ceilings $3,7,44,1874$; the $n=8$ integers are (NCE.107). |

No enumeration of all $2^{123}$ supports or all joint
templates is needed or asserted. Projection domination,
the missing-state charge, and the all-word witnesses
prove completeness of the heavy cases. Theorem 2.2
then proves all joint lengths; finite checks alone
establish no asymptotic convergence or memory optimum.

**Convention 19.2 (credited suppliers and primary attribution).**
The law (NCE.82), the classification of its heavy supports,
the exact fixed-law pressure and the strengthened original
converse are `repo-derived` deductions. Finite entropy,
Gibbs domination, functional dependencies and positive-weight
monotonicity are mature machinery. There is no worldwide
originality, independent-review or Lean-certification claim.

Theorem 2.2 owns the cyclic-donor entropy argument. Lemmas
3.2 and 8.2–8.3 own the separation, count and collision
suppliers. AAR owns the exact temporal factor. [FMR,
Lemma 2.2, Theorems 2.3–2.5, 3.3 and 6.3–6.4][FMRa]
owns canonical all-word simulation, paid cover realization,
native scaffold restriction and rate existence. [NPC,
Definitions 2.2 and 5.1, Theorem 7.1][NPCa] owns the
complete-template pressure formulation and unrestricted
original-competitor transport. Proposition 11.1 already
owns the paid $100^n$ equality-fiber construction used
in §18. [COK, Theorem 5.2][COKa] supplies the finite
envelope sandwich. [D3, Theorems 2.3 and 4.1][D3a]
owns $M_1(3)=4$ and $\lambda<3/16$. The law and
lower endpoint of §§8–12 retain their credited scope;
they are not counted again as new results.

| Primary source | Checked correspondence and transfer boundary |
| --- | --- |
| Gogacz and Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, [arXiv:1512.01808v1](https://arxiv.org/html/1512.01808v1), Theorem 1 and Corollary 1 | Each native decoder gives a functional dependency under the same joint law. Their fixed-schema almost-entropic characterization and submodular upper relaxation do not supply this particular weight law, its finite squared-cell checks, or a native all-length cutoff as the schema size and donor choices vary. The native all-cyclic rule used here remains Theorem 2.2. |
| Vontobel, *Counting in Graph Covers: A Combinatorial Characterization of the Bethe Entropy Function*, [arXiv:1012.0065v2](https://arxiv.org/html/1012.0065v2), Theorems 25 and 33 | Rational local pseudo-marginals are lift-realizable on finite covers, and fixed-base cover-average partition exponents have the stated Bethe interpretation. Changing to a cover and averaging over covers do not give a universal upper bound on every native template. COK §§12–17 supply the exact native specialization and leave its low-charge completion premise explicit. |
| Ruozzi, *The Bethe Partition Function of Log-supermodular Graphical Models*, [arXiv:1202.6035v2](https://arxiv.org/html/1202.6035v2), Theorem 4.1 | The inequality $Z(H)\le Z(G)^k$ for a $k$-cover assumes a binary log-supermodular factorization. Arbitrary native hard compatibility and joint block weights have not been shown to satisfy that premise; no cover-domination theorem is transferred. |
| Atserias and Kolaitis, *Consistency, Acyclicity, and Positive Semirings*, [arXiv:2009.09488v1](https://arxiv.org/html/2009.09488v1), Lemma 12 and Theorems 4–5 | Pairwise-consistent local relations or laws extend on the specified acyclic/join-tree attribute families. Arbitrary cyclic native donor systems are not made acyclic by this proof. No unrestricted global completion theorem is inferred. |

These primary hypotheses support the stated correspondence
boundaries. They do not close the global native gap, and
this bounded assessment is not a nonexistence claim.
No differently scoped predecessor-row, finite-reader code
synthesis or quantum theorem is transferred to the present
stationary-source pressure or preparation problem.

**Open problem 19.3 (what the strict converse leaves unresolved).**
Exact all-length pressure at $\mu_{\rm a}$ does not
identify a globally minimizing law, exact $\sigma_3$,
sharp original $\lambda$, general exact $M_1(D)$,
or covers attaining the displayed memory lower bound.
The fixed-law equality (NCE.100) does not prove

$$
a_d:=\min_{\mu\in\Delta(S_d)}\Omega_d(\mu)
=b_d:=\min_{\mu\in\Delta(S_d)}\beta_d(\mu)
=2^{-\sigma_d}
\quad\text{at general depth}.
\tag{NCE.110}
$$

The finite-envelope real/rational optimization and algebraic
attainment are already settled in [NWO, §§3–7][NWOa].
Their remaining equality is (NCE.110), not density of
rational weights. [COK, Open problems 9.3 and 17.3][COKa]
still lack matching near-optimal owner populations with
small normalized information charge, or a controlled
same-base global completion. Completion on a finite cover
does not select a prescribed Gibbs law on the unlifted
base; the cover average supplies a lower pressure witness,
rather than the universal upper needed for a cap.

The unchanged effective target of [NPC, Definition 8.1][NPCa]
and [GDB, Definition 11.1][GDBa] is a total sound verifier
whose accepted weight-optimized endpoints are cofinal at
every original $\sigma_d$, or a uniform effective native
length error sufficient for terminating two-sided
approximation of $\lambda$. The strictly positive
counting law here does not remove hard template zeros,
give a length cutoff, force small global entropy loss,
or establish optimizer-cofinality. [SCP][SCPa]'s valid
additive all-size softening bounds retain their scope;
its specified relative-gate obstruction and GDB's
specified method obstructions are not enlarged to
impossibility of the effective target.

The new result is a strict all-competitor quantitative
converse inside the original late-target interface.
The minimal-relations/internal-observer programme,
including the original space/time/boundary/memory
mutual-recovery objective and its paid access and
resource obligations, remains open beyond the
requested-factor recovery in (NCE.109).

[NPCa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[COKa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[FMRa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[D3a]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[NWOa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHT_OPTIMIZATION.md
[GDBa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[SCPa]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SOFT_CONSTRAINT_PRESSURE.md

## 追加锚（本行以下为增补区）
