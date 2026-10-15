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
