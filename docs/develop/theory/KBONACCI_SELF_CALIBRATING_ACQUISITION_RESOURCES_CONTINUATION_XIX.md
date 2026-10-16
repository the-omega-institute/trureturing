# Self-calibrating acquisition resources XIX: complete coefficients and the normalized seven-coordinate slice

## 341. The complete preselected coefficient cone

The fixed objects and resource classes are those of
[73.1 and 90.1–90.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions).
Thus $X$ consists of $(r,g)$ with $r$ prime and
$\lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor$,
$N=1+F_rg$, $q_i=[p_i\mid N]$, and $n=\min\{i:q_i=0\}$.
Every finite word is an actual pattern, by Boundaries 35.2;
there is no probability distribution on $X$. The original carrier
is the disjoint-union Borel space of interval blocks $B_j,P_j$.
Its consumer returns unknown on $B_j$ and proposes $j$ on $P_j$.
The distinct marks are $\theta_j=(B_1,1/(j+2))$, $j\ge0$.
For an entire sequence $1\ge a_1\ge a_2\ge\cdots>0$ tending to zero,
the comparison target is the separately selected law
$(1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}$.
The original nonatomic targets remain distinct from these selected laws.

One source-independent common seed fixes an entire schedule and all
its counterfactual outputs before any reply. There is zero advice,
sourcewise almost-sure finite handoff, and a hard bound of two actual
requests, including repeated or ignored requests. Class $N$ acquires
its whole preselected schedule; class $O$ preselects increasing addresses
and stops at the first queried zero or exhaustion. The second address
is never chosen from the first reply. Original competitors retain
arbitrary addresses and full-carrier outputs.

**Definition 341.1 (Mass cone and coefficient data).** Let $L\ge0$,
$J=\{0,\ldots,L\}$, and $M\ge0$ be finite. Write
$m(v)=\sum_{z\in J}v(z)$, with $v_+$ taken coordinatewise.
A mass-$M$ complete $N$ allocation has an empty vector $z\ge0$,
singleton vectors $x_i,y_i\ge0$ of equal mass, and pair vectors
$a_{ij},b_{ij},d_{ij},e_{ij}\ge0$ of a common mass $w_{ij}$,
for every $i<j$. Their cells are $00,01,10,11$ in that order.
The empty mass, singleton masses, and pair masses sum to $M$,
counting each schedule once. Its entire word law is

$$
\begin{aligned}
k(w)={}&z+\sum_i((1-w_i)x_i+w_i y_i)\\
&+\sum_{i<j}\bigl((1-w_i)(1-w_j)a_{ij}
 +(1-w_i)w_j b_{ij}+w_i(1-w_j)d_{ij}+w_iw_j e_{ij}\bigr).
\end{aligned}
\tag{341.1}
$$

This is the mass cone of the complete model in II 140.2, without
separate normalizations for labels, words or cells. We seek an exact
criterion for a prescribed entire multilinear function

$$
k(w)=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j,
\qquad m(c)=M,\quad m(\ell_i)=m(Q_{ij})=0.
\tag{341.2}
$$

For one family of signed vectors $g_{ij}$ with $m(g_{ij})=0$, set

$$
\begin{aligned}
r_{ij}&=(-g_{ij})_+,&s_{ij}&=(-g_{ij}-Q_{ij})_+,\\
t_{ij}&=\max\{m(r_{ij}),m(s_{ij})\},&
D_i&=\ell_i-\sum_{h<i}g_{hi},\\
R_i&=\sum_{j>i}r_{ij},&S_i&=\sum_{j>i}s_{ij},\\
T_i&=\sum_{j>i}t_{ij},&U_i&=\max\{R_i,S_i-D_i\},\qquad u_i=m(U_i).
\end{aligned}
\tag{341.3}
$$

The maximum defining $U_i$ is coordinatewise. All pairs have a
$g_{ij}$ variable, including those with $Q_{ij}=0$.

**Theorem 341.2 (Exact complete $N$ coefficient criterion).** For every
$L,M$ and data (341.2), a mass-$M$ complete $N$ allocation realizes
$k$ on every word if and only if there exists one entire family $g$
as above satisfying both

$$
\boxed{\quad c\ge\sum_iU_i\quad\text{coordinatewise},\qquad
                \sum_i\max\{u_i,T_i\}\le M.\quad}
\tag{341.4}
$$

Nonnegativity of the prescribed word laws is a consequence, rather
than an additional assumption. At $M=1$ the inverse below gives
one common-seed preselected acquisition with at most two actual calls.

Proof. Start with (341.1), and take $g_{ij}=b_{ij}-a_{ij}$.
Equal cell masses give $m(g_{ij})=0$. Comparing pair coefficients gives

$$
Q_{ij}=e_{ij}-d_{ij}-g_{ij},\qquad
b_{ij}=a_{ij}+g_{ij},\quad e_{ij}=d_{ij}+g_{ij}+Q_{ij}.
\tag{341.5}
$$

Consequently $a_{ij}\ge r_{ij}$, $d_{ij}\ge s_{ij}$,
and $w_{ij}\ge t_{ij}$. Define
$A_i=x_i+\sum_{j>i}a_{ij}$ and
$B_i=y_i+\sum_{j>i}d_{ij}$.
The constant and linear coefficients of (341.1) are exactly

$$
c=z+\sum_i A_i,\qquad B_i-A_i=D_i.
\tag{341.6}
$$

Indeed a pair contributes $d_{ij}-a_{ij}$ to its first address
and $b_{ij}-a_{ij}=g_{ij}$ to its second address.
Thus $A_i\ge R_i$, $B_i\ge S_i$, so $A_i\ge U_i$.
Their common mass is the singleton mass plus
$\sum_{j>i}w_{ij}$, hence is at least both $u_i$ and $T_i$.
Summing these masses, and adding $m(z)$, proves both inequalities
of (341.4). This uses the same allocation throughout.

Conversely, fix one family satisfying (341.4). Put

$$
\rho=c-\sum_i U_i,\qquad \delta_i=(T_i-u_i)_+.
\tag{341.7}
$$

Here $\rho\ge0$ and
$\sum_i\delta_i\le M-\sum_i u_i=m(\rho)$.
If $m(\rho)>0$, choose

$$
A_i=U_i+\frac{\delta_i}{m(\rho)}\rho;
\tag{341.8}
$$

if $m(\rho)=0$, every $\delta_i=0$ and choose $A_i=U_i$.
Then $\sum_iA_i\le c$, $A_i\ge R_i$, and
$B_i:=A_i+D_i\ge S_i$. Since $m(D_i)=0$,

$$
m(A_i)=m(B_i)=\max\{u_i,T_i\}=:v_i.
\tag{341.9}
$$

For a fixed $i$ let $P_i=A_i-R_i\ge0$ and
$W_i=B_i-S_i\ge0$. For every $j>i$ define

$$
\begin{aligned}
a_{ij}&=r_{ij}
 +\frac{t_{ij}-m(r_{ij})}{m(P_i)}P_i,\\
d_{ij}&=s_{ij}
 +\frac{t_{ij}-m(s_{ij})}{m(W_i)}W_i.
\end{aligned}
\tag{341.10}
$$

A fraction with zero denominator means a zero added vector.
This convention is forced: the sum of the nonnegative numerators
in the first line is $T_i-m(R_i)\le v_i-m(R_i)=m(P_i)$;
thus $m(P_i)=0$ forces each numerator to vanish. The same
argument with $S_i,W_i$ handles the second line. When a denominator
is positive the sum of its fractions is at most one. It follows that

$$
\sum_{j>i}a_{ij}\le A_i,\qquad
\sum_{j>i}d_{ij}\le B_i,
\qquad m(a_{ij})=m(d_{ij})=t_{ij}.
\tag{341.11}
$$

Use (341.5) to define $b_{ij},e_{ij}$.
The definitions of $r,s$ make both nonnegative, and their masses
are also $t_{ij}$. Set

$$
x_i=A_i-\sum_{j>i}a_{ij},\qquad
y_i=B_i-\sum_{j>i}d_{ij},\qquad z=c-\sum_iA_i.
\tag{341.12}
$$

These are nonnegative, and $x_i,y_i$ have the same mass $v_i-T_i$.
The total schedule mass is
$m(z)+\sum_i(v_i-T_i)+\sum_{i<j}t_{ij}=M$.
Equations (341.5)–(341.6) now recover precisely $c,\ell,Q$.
Uniqueness of the multilinear expansion gives (341.2) on the entire
cube, including all multiple-zero words.

For $L=0$ all indexed sums vanish and $z=c$ is the whole allocation.
For $M=0$, (341.4) gives $c\ge\sum U_i\ge0$ of mass zero,
so $c=U_i=0$ and $T_i=0$. Then $r=s=0$, $g\ge0$ and
$g+Q\ge0$, with zero sums, force $g=Q=0$. Also
$U_i=\max(0,-D_i)=0$ and $m(D_i)=0$ force $D_i=\ell_i=0$.
The inverse is the zero allocation, with no division.

At $M=1$, partition a uniform seed interval into the schedule masses.
Within a positive-mass schedule interval use its rescaled uniform
coordinate for every cell's quantile partition. The intersections of
these finitely many label intervals fix the entire table before replies.
Each cell has exactly its prescribed marginal, without choosing
new randomness after an answer. Acquiring the preselected pair and
using its fixed table realizes (341.1). Every execution is finite
and every record is a measurable finite union of intervals. This is
also the common-table realization of II 140.3. $\square$

The slice $g=0$ has $r=0$, $s=(-Q)_+$ and
$U_i=(\sum_{j>i}(-Q_{ij})_+-\ell_i)_+$.
Its mass dominates $T_i$, because $m(\ell_i)=0$.
Thus it is exactly the stopped criterion of
[109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#109-an-exact-coefficient-criterion-with-one-common-probability-budget),
with its mass scaled from one to $M$; that result is reused.
The additional variables in (341.3) retain the distinct $00,01$ cells.
For fixed $M$ and $|J|=L+1$, the free real coordinates of
$(c,\ell,Q,g)$ number
$L+L^2+2L\binom L2=L^3+L$.
At $L=8$ this is $520$; the complete-cell chart of II 140.2
has $1068$ dimensions after its independent equalities.
These are representation dimensions, not running-time bounds.

**Affine convention 341.3 (Retaining the anchor).** For $L\ge2$ and event rows,
write $d_{w,E}(b,e)=\eta_w(E)-e$ and
$r_{w,E}=R_w(E)$, where $R=O(1,2;1,2,0)$ is the anchor table.
A mass-$M$ affine comparison uses

$$
k_w(E)\ge d_{w,E}(b,e)+(M-1)r_{w,E}.
\tag{341.13}
$$

Dividing (341.13) by $M$ does not keep the original profile demands.
For $M>0$ its normalized profile is
$b'=\alpha+(b-\alpha)/M$, $e'=e/M$, with
$\alpha=(1,1,0,\ldots,0)$. Theorem 341.2 characterizes the
mass cone; it does not remove this affine anchor.

## 342. Why the scalar schedule budget is independent

**Example 342.1 (A probability law outside the normalized $N$ class).**
Let $L=3$, $t=3/4$, and

$$
f(w)=(1-w_1)w_2+w_1w_3,\qquad
k_0=t(1-f),\quad k_1=1-k_0,\quad k_2=k_3=0.
\tag{342.1}
$$

All word laws are probability vectors. Set
$v=(-t,t,0,0)$, $c=(t,1-t,0,0)$,
$\ell_2=v$, $Q_{12}=-v$, $Q_{13}=v$, with other coefficients zero.
For $g_{12}=v$ and other $g=0$, the data of (341.3) give
$U_1=(t,0,0,0)$, $T_1=2t$, and $U_i=T_i=0$ for $i=2,3$.
The coordinate inequality holds, but the scalar inequality fails.
In fact no other $g$ makes both hold.

Proof. Suppose a normalized complete $N$ allocation gave (342.1).
Couple its cells to deterministic tables by II 140.3. Because
$k_0=0$ at every $f=1$ word, every positive-weight deterministic
table must avoid output zero at those four words. Such a table
can output zero on at most one of $001,110$. Here is the full
schedule check. An empty or singleton zero-output cell contains
an $f=1$ word. For pair $(1,2)$, the cell of $110$ also contains
$111$, so it cannot output zero there. For pair $(1,3)$,
the cell of $001$ also contains $011$. For pair $(2,3)$,
the cell of $001$ contains $101$, and the cell of $110$ contains
$010$. These exhaust all distinct sorted pairs. Repeats and
reversals contract or permute the same observations.
Therefore every such table has
$[D(001)=0]+[D(110)=0]\le1$; the shared normalized mixture
has $k_0(001)+k_0(110)\le1$. Formula (342.1) makes this
$2t=3/2$. The contradiction proves nonmembership, and Theorem
341.2 then rules out every alternative $g$. This is a law-realizability
obstruction, without an original amplitude-profile separator. $\square$

## 343. Aggregated ordered stars and whole-vector positivity

**Theorem 343.1 (Coefficient positivity on a common star partition).**
Partition $[L]$ into roots $R$ and leaves $D$. Give each leaf $j$
one parent $\pi(j)\in R$ with $\pi(j)<j$.
Suppose $p(w)=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j$
is a probability-vector kernel on the full cube, and every nonzero
whole-vector $Q_{ij}$ is an edge $i=\pi(j)\to j$.
No $N$ realization of $p$ is assumed. Put

$$
\rho_i(w)=w_i\ (i\in R),\qquad
\rho_j(w)=w_{\pi(j)}w_j\ (j\in D),\qquad q=p\circ\rho.
\tag{343.1}
$$

For $i\in R$, define

$$
A_{ij}=Q_{ij}+\ell_j\quad(\pi(j)=i),\qquad
V_i=\sum_{\pi(j)=i}(-A_{ij})_+,\quad
h_i=(V_i-\ell_i)_+,\quad H=\sum_{i\in R}h_i.
\tag{343.2}
$$

Then $q$ is a stopped kernel. More explicitly,

$$
q(w)=c+\sum_{i\in R}\ell_iw_i
            +\sum_{j\in D}A_{\pi(j),j}w_{\pi(j)}w_j,
\qquad \min_w q_w(z)=c(z)-H(z).
\tag{343.3}
$$

For any real profile parameters $(b,e)$, if $p$ satisfies all base,
correct, independent union and positive rows, so does $q$ at the
same parameters. There is a common-seed stopped realization using
at most $L+1$ positive-mass schedule types.

Proof. Each parent is a root, so substitution gives
$\rho_i\rho_j=w_i^2w_j=w_iw_j$ on the cube; the leaf-linear
term supplies the additional $\ell_j$ in $A_{ij}$.
This proves the polynomial identity in (343.3).
For a fixed label, the contribution of root $i$ and its leaves is
$w_i(\ell_i+\sum_{\pi(j)=i}A_{ij}w_j)$.
Its exact minimum is
$\min(0,\ell_i-\sum(-A_{ij})_+)=-h_i$.
Different stars use disjoint coordinates, so these scalar minima
can be attained simultaneously for that label. This proves the
minimum formula. It does not require one minimizing word for
all labels. Positivity of $p\circ\rho$ implies $c\ge H$.
Each coefficient of $p$ has zero signed label sum; hence so do
$\ell_i,A_{ij}$. Therefore
$m(h_i)\ge m(V_i-\ell_i)=m(V_i)$ and
$\sum_i m(h_i)=m(H)\le m(c)=1$.
The stopped criterion 109.1 applied to the displayed coefficients
now gives one complete stopped allocation, including zero masses.
Its construction has one pair per leaf, at most one singleton per
root, and an empty schedule: at most $|D|+|R|+1=L+1$ types.

If $w$ has first zero $n$, every coordinate before $n$ is one.
A leaf $n$ has an earlier parent, also one, so $\rho_n=0$;
a root $n$ is unchanged. Earlier coordinates remain one.
Thus $\rho$ preserves the first zero and fixes $1^L$.
Every demand at $w$ equals the corresponding demand at $\rho(w)$.
Consequently $q_w(0)$, $q_w(n)$ and $q_w(0)+q_w(n)$ inherit
the three separate inequalities from that one word of $p$;
the positive row is inherited as well. This argument is valid for
negative singleton demands and every multiple-zero word, and uses
no observed reset in an actual acquisition. $\square$

The outward-star acquisition principle and same-cap repair already
belong to [XV 258.3–258.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md#258-signed-event-transfer-actual-slack-and-universal-common-input-maps).
Their common map sets a leaf to one after its root is zero;
(343.1) instead sets the leaf to zero, and absorbs its linear term
explicitly. The additional scope here is the aggregated whole-vector
positivity calculation (343.3), which does not assume $N$ membership.
There is no new star/fork principle or original amplitude region.

For completeness, the $N$-only consequence can already be recovered
from the old result after regrouping one complete allocation.
Aggregate all schedules with the same pair. If its aggregate $Q_{ij}$
is zero, that pair kernel is a nonnegative affine function on its
two-coordinate cube. Its per-label minimum is its constant minus
the two negative linear parts; positivity gives the coordinate
criterion, and their total mass is at most the pair mass.
The scaled construction of 109.1 has zero outgoing pair vectors
when $Q=0$, so replaces this kernel by constants and singletons.
Now absorb every leaf singleton into its parent pair, letting that
pair ignore the parent for this added component. All four cells of
that component have the same singleton schedule mass, so the full
law and global mass are unchanged. Remaining positive pair schedules
are outward stars and no leaf has a singleton. Theorem 258.3 then
applies to their entire tables, and 258.4 gives the same cap.
Thus a chain or two incoming edges in the aggregated nonzero-$Q$
graph is necessary for a genuine $N$-only profile obstruction;
it is not sufficient. This is a consequence with the preceding
attribution, rather than a further claimed novelty.

Example 342.1 has edges $1\to2,1\to3$ and satisfies the
probability premise of 343.1 while failing $N$ membership.
Its reset law has
$q_0=t(1-w_1w_3)$, $q_1=1-q_0$.
This exhibits the scope beyond assumed $N$ realizability without
supplying a new amplitude region.

## 344. The exact seven-coordinate dataset and its finite identities

**Definition 344.1 (Normalized slice and certificate identity).** Use
coordinates $x=(b_1,b_2,b_4,b_5,b_6,b_7,e)$, with $b_3=b_2$.
Let $H_7$ be the compact seven-dimensional polytope

$$
\begin{gathered}
1\ge b_1\ge b_2=b_3\ge b_4\ge b_5\ge b_6\ge b_7\ge e\ge0,\\
0\le b_3+b_4+b_5+b_6+b_7-8e\le1-b_1.
\end{gathered}
\tag{344.1}
$$

The dataset $\mathcal D_7$ is the complete file
`calibration238-complete-n-h7/H7-certificate.json` in
[the-omega-institute/trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments),
schema `research161-H7-complete-normalized-common-allocation-v1`,
with exactly $2{,}579{,}533$ bytes and SHA256
`621bed2ac570875c2bcb96796338e753ba045c544aa30fb8e1af8702cc94581d`.
This content identity specifies the data independently of a mutable
branch. The complete dataset is available at the
[immutable scientific revision](https://github.com/the-omega-institute/trureturing-experiments/blob/1be64035b2fc5d379ba49b52cb0c402010286922/calibration238-complete-n-h7/H7-certificate.json). All rational strings denote exact rationals.
The complete data, rather than a sample or a selected sublist, are
part of the finite mathematical certificate below.

Its matrix fields $A,B$ define $Ax\le B$ with $481$ rows.
Rows $0,\ldots,9$ are exactly (344.1), in the order
$b_1\le1$, $b_2\le b_1$, the successive descending inequalities
through $e\le b_7$, $e\ge0$, the lower excess inequality,
and the upper excess inequality. The remaining $471$ rows are
specified by `cuts`. Call this polytope $P$.
There is no assertion that these inequalities are distinct facets
or form a minimal description.

Words are lexicographic with $w_1$ first. At each of the first
$127$ words list $A,C,P$, and at $1^7$ list $T$; row indices
are $0,\ldots,381$. For first zero $n$, their events and demands are

$$
\begin{array}{c|c|c}
A&\{0\}&1-b_n-e\\
C&\{n\}&b_n-e\\
P&\{0,n\}&1-e\\
T\text{ at }1^7&\{0\}&1-e.
\end{array}
\tag{344.2}
$$

An omitted score weight is zero. For a cut's nonnegative weights $y$,
let $f_y(w,z)=\sum_{r:\,w_r=w,\,z\in E_r}y_r$ and set

$$
\begin{aligned}
\beta_n&=\sum_{w:n(w)=n}(y_{w,C}-y_{w,A}),\\
K&=\sum_r y_r,\qquad C_y=\sum_w(y_{w,A}+y_{w,P})+y_{+,T},\\
M_{ij}^{ab}&=\max_{z\in J}\sum_{w:w_i=a,w_j=b}f_y(w,z),\\
B_N(y)&=\max_{1\le i<j\le7}\sum_{a,b\in\{0,1\}}M_{ij}^{ab}.
\end{aligned}
\tag{344.3}
$$

Every cut record supplies all these quantities and the primitive
positive scaling of

$$
(\beta_1,\beta_2+\beta_3,\beta_4,\beta_5,\beta_6,\beta_7,-K)
                 \cdot x\le B_N-C_y.
\tag{344.4}
$$

A vertex record supplies its seven rational coordinates and the full
set of active row indices. Its matching lift record supplies one
allocation of increasing pairs, with three sparse terminal vectors
in cells $0,10,11$. Every coordinate is a label in $J=\{0,\ldots,7\}$.

**Lemma 344.2 (Complete finite identities of $\mathcal D_7$).** The
following are exact properties of this data. All $471$ score records
satisfy (344.3)–(344.4). The complete vertex list of $P$ consists
of its $1606$ supplied distinct points, each of active-normal rank
seven; their affine hull has dimension seven. The $1606$ matching
lifts satisfy all counterfactual cell budgets, global mass one,
and every row (344.2) on all $128$ words. In total they contain
$22027$ schedule rows and $66081$ terminal vectors, giving
$205568$ word laws and $613492$ separate event inequalities.

Proof. The finite identities have the following exhaustive specification;
no continuous optimization or floating-point tolerance is involved.
For a score, accumulate its weights into the $128\times8$ array
$f_y$. For each of the $21$ ordered pairs and each of its four
cells, sum the entries over the $32$ consistent words, separately
for each of the eight labels, and take their maximum. These are
exactly the four `cell_maxima` entries in that pair's record.
The maximum of their $21$ sums is its `BN`; the independent class
sums and total weight are its `beta`, `const`, and `K`.
After folding the two equal coordinates, multiply (344.4) by the
least common denominator and divide all eight integer entries,
including the right side, by their positive greatest common divisor.
The resulting normal and right side equal row $10+h$ of $A,B$
for cut $h=0,\ldots,470$. This specifies every entry comparison,
including scores with zero components and negative $\beta$.

Here is a complete exact enumeration of the geometry. For the initial
ten domain rows, solve every one of the $\binom{10}{7}=120$
seven-row systems, discarding singular systems and points violating
any of the ten inequalities. Deduplicating gives precisely the
following twelve points, expressed in the unreduced amplitudes:

$$
\begin{aligned}
o&=(0,\ldots,0;0),\qquad p=(1,0,\ldots,0;0),\\
u_k&=(\underbrace{1/(k-1),\ldots,1/(k-1)}_{k},0,\ldots,0;0),\\
v_k&=(\underbrace{1,\ldots,1}_{k},
 \underbrace{(k-2)/(k+1),\ldots,(k-2)/(k+1)}_{7-k};(k-2)/(k+1)),
 \qquad k=3,\ldots,7.
\end{aligned}
\tag{344.5}
$$

At each stage retain full active sets. Insert rows $10,\ldots,480$
in their listed order. Retain all vertices on or inside the new
halfspace. For every strict crossing pair $u,v$ whose common active
normals have rank six, insert

$$
\frac{s(u)v-s(v)u}{s(u)-s(v)},\qquad s(x)=B_h-A_hx,
\tag{344.6}
$$

and deduplicate exact rational coordinates. Its old active set is
exactly the intersection of those at $u,v$; add the new row.
This recurrence has $21337$ strict crossing edges. Its final set is
exactly the $1606$ listed points, with the listed full active sets;
there are $8363$ final edges and $251$ points with exactly seven
active rows. Every listed point satisfies all $481$ inequalities,
and its active normals have rank seven. The differences between
these points have rank seven as well.

To justify completeness of this enumeration, a vertex of a
seven-dimensional polyhedron has seven independent active normals,
so the initial $120$ systems omit no domain vertex. For distinct
vertices $u,v$ the relative interior of their segment has exactly
the constraints common to their active sets. The minimal face
containing that segment therefore has dimension seven minus the
rank of those normals. Rank six is equivalent to their segment
being an edge. A new vertex strictly inside an old face cut by the
new hyperplane can arise only from a one-dimensional old face:
a transverse cut through the relative interior of a face of dimension
$d$ has dimension $d-1$. Hence the complete new list is exactly
old retained vertices and strict intersections with old crossing
edges. Old boundary vertices are already retained. The final
rank-seven affine hull proves that no intermediate polytope lost
full dimension, since every intermediate one contains the final
set. These observations prove the recurrence by induction through
all $471$ cuts, including degeneracies and redundant cuts.
All ranks and intersections here are over the rationals.

Finally, for each lift, compare its vertex index and all seven
coordinates with the corresponding vertex record. In every schedule
$i<j$ the three nonnegative vectors have exactly the recorded
schedule mass; the sum of those masses is one. For every word form

$$
p_w=\sum_{i<j}
 \begin{cases}T_{ij}^{0},&w_i=0,\\
 T_{ij}^{10},&w_i=1,w_j=0,\\
 T_{ij}^{11},&w_i=w_j=1.
 \end{cases}
\tag{344.7}
$$

Each such vector is nonnegative of mass one. Direct rational
substitution into each of (344.2), with $b_3=b_2$, gives its
$381+1$ inequalities. This is $1606(3\cdot127+1)=613492$
inequalities, with no discarded negative demand or multiple-zero
word. The sums of schedule and terminal-vector counts are as stated.
Together with (344.3) and the exhaustive recurrence, these finite
identities prove all the claims of the lemma. $\square$

The geometry principle is mature polyhedral theory: Kaibel,
[*Basic Polyhedral Theory*, arXiv:1001.2161v1](https://arxiv.org/abs/1001.2161v1),
Theorems 8, 13 and 15 and the face description in §1.5, applies to
finite real halfspace systems, with rational data giving rational
vertices. Here boundedness removes recession rays. The particular
$471$ scores and $1606$ simultaneous stopped lifts are additional
finite data; those general theorems do not supply them.

## 345. Classification of the normalized equality slice

**Theorem 345.1 (The complete normalized $H_7$ slice).** Let
$\Pi_{N,7},\Pi_{O,7}$ denote feasibility of the complete mass-one
seven-coordinate models with every row (344.2). Then

$$
\boxed{\qquad \Pi_{N,7}\cap H_7=P=\Pi_{O,7}\cap H_7.\qquad}
\tag{345.1}
$$

The equality holds for all real points, including the closed auxiliary
boundary $e=0$. It is a classification on $b_2=b_3$, without an
unequal-head or arbitrary-mass assertion.

Proof. Consider one nonnegative full score $y$ of the dataset.
For a fixed $N$ pair of schedule mass $m$, its score reward is at
most $m\sum_{ab}M_{ij}^{ab}$: the four terminal vectors each
have that same mass, and each is evaluated against its own full
cell's label rewards. Taking the maximum over pairs gives the
bound $mB_N$. An empty or singleton schedule satisfies this bound
as well. Extend its observed set to a distinct pair; the pair cells
refine its information, and summing the independent cell maxima
can only increase a maximum with a shared label. Reversal permutes
cells and a repeated static address gives a singleton. Thus the
bound covers every complete $N$ schedule and every legal label.
Summing under the one global mass-one budget bounds total reward
by $B_N$. Feasibility bounds it below by
$\beta\cdot b-Ke+C_y$. This proves (344.4) for every $N$
allocation, with all $A,C,P,T$ rows retained independently.
Lemma 344.2 identifies the exact $471$ inequalities, so
$\Pi_{N,7}\cap H_7\subseteq P$.

The domain is bounded; thus $P$ is the convex hull of its complete
vertex list. Write any real point $x\in P$ as
$x=\sum_v\lambda_vv$ with $\lambda_v\ge0$, $\sum_v\lambda_v=1$.
Choose the whole stopped allocation of vertex $v$ with probability
$\lambda_v$. Each counterfactual cell is mixed with exactly the
same weights. Nonnegativity, equal cell masses and global mass one
are preserved. Since every demand in (344.2) is affine in the
profile and cap, the same mixed allocation satisfies all rows at
$x$, proving $P\subseteq\Pi_{O,7}\cap H_7$.
To realize it, one seed first fixes the vertex branch, then its
schedule interval, then all cell quantiles within that schedule.
Everything is fixed before replies, and the selected increasing
schedule makes at most two actual requests. Its $N$ completion
uses the same seed, acquires both replies, reconstructs the stopped
cell, and ignores the extra reply when appropriate. That ignored
request counts. Hence $\Pi_{O,7}\subseteq\Pi_{N,7}$, completing
the equality. No separate best allocation has been chosen for
individual rows or words. $\square$

**Corollary 345.2 (Original full-tail interpretation).** Fix any entire
positive nonincreasing vanishing $a$ and any positive closed cap
$e$ with $a_7>e\ge a_8$. If $(a_1,\ldots,a_7,e)\in H_7$,
original $\mathcal N_2$ feasibility, original $\mathcal O_2$
feasibility, and all $471$ inequalities (344.4) are equivalent.

Proof. The strict active length is exactly seven. Apply the
class-preserving feasibility correspondence
[110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)
and Theorem 345.1. Its necessity uses the countable original source
for a common conull seed event, finite actual pattern witnesses,
truncation of the entire preselected schedule, sourcewise finite
handoff cutoffs and compactness of the finite catalog simplex.
Consequently it allows arbitrary original addresses, repeated calls
and full-carrier outputs, and transports feasibility at the exact
closed cap. It does not preserve an arbitrary original competitor's
individual laws or coupling.
For sufficiency execute the constructed low-prime rule on the actual
source, handing its actual mark to the unchanged consumer.
At $n\le7$ its entire low word obeys all three rows.
At $n>7$ the law is the finite positive-word law, with no label $n$;
its exact original TV error is
$\max\{1-p_{1^7}(0),a_n\}\le e$.
This includes $a_8=e$ and all later ties and tails; no summability
hypothesis is used. $\square$

For $M>1$, the affine normalization of 341.3 sends an equality
$b_2=b_3$ to $b'_2-b'_3=1-1/M$.
It leaves this slice, so (345.1) does not classify the all-mass
problem. Nor does the auxiliary finite $e=0$ boundary assert an
original positive-tail theorem at zero cap.

## 346. A complete original attainer at error fifteen sixty-fourths

**Example 346.1 (One shared fourteen-schedule law and a full-$N$ lower).**
Take the prefix

$$
(a_1,\ldots,a_7)=\frac1{64}(43,34,34,29,27,25,22)
\tag{346.1}
$$

and any entire positive ordered vanishing tail with $a_8\le15/64$.
Both original hard-two classes have attained minimum error $15/64$.
Every positive closed cap is feasible in either class exactly when
it is at least $15/64$.

Here is the whole upper allocation. A row displays integer numerators
over $64$; each of its three terminal vectors sums to its mass $m$.
Write $e_j$ for a label unit vector. All omitted coordinates are zero.

| Pair | $m$ | First-zero vector | Middle vector | Exhaustion vector |
| --- | ---: | --- | --- | --- |
| $(1,2)$ | 17 | $17e_1$ | $17e_2$ | $7e_0+5e_3+5e_4$ |
| $(1,3)$ | 7 | $7e_1$ | $7e_3$ | $7e_0$ |
| $(1,4)$ | 2 | $2e_1$ | $2e_4$ | $2e_0$ |
| $(1,5)$ | 2 | $2e_1$ | $2e_5$ | $2e_0$ |
| $(2,3)$ | 7 | $5e_0+2e_2$ | $7e_3$ | $7e_0$ |
| $(2,4)$ | 2 | $2e_0$ | $2e_4$ | $2e_0$ |
| $(2,5)$ | 2 | $2e_0$ | $2e_5$ | $2e_0$ |
| $(3,4)$ | 5 | $5e_0$ | $5e_4$ | $4e_0+e_7$ |
| $(3,5)$ | 4 | $4e_0$ | $4e_5$ | $4e_0$ |
| $(3,6)$ | 2 | $2e_0$ | $2e_6$ | $2e_0$ |
| $(4,5)$ | 4 | $4e_0$ | $4e_5$ | $4e_0$ |
| $(4,6)$ | 2 | $2e_0$ | $2e_6$ | $2e_0$ |
| $(5,6)$ | 6 | $6e_0$ | $6e_6$ | $2e_0+4e_7$ |
| $(6,7)$ | 2 | $2e_0$ | $2e_7$ | $2e_0$ |

Proof of the upper bound. The masses sum to $64$, so this is
one normalized complete allocation. On a first-zero-$n$ word the
integer correct masses are respectively
$(28,19,19,14,12,10,7)$, independent of its suffix.
For $n=1$ this is $17+7+2+2$ from the four first cells;
for $n=2$ it is $17+2$ from $(1,2)$ and the first cell of
$(2,3)$; for $n=3$ it is $7+7+5$ from $(1,3),(2,3),(1,2)$;
for $n=4$ it is $2+2+5+5$ from $(1,4),(2,4),(3,4),(1,2)$;
for $n=5$ it is $2+2+4+4$ from its incoming middle cells;
for $n=6$ it is $2+2+6$; for $n=7$ it is $1+4+2$.
Earlier bits force the indicated exhaustion cells, and the first
zero forces the indicated middle or first cells. No later cell can
emit the correct label. These counts equal $64a_n-15$.

For an explicit all-suffix bound, let $W_n=64(1-p_w(0)-p_w(n))$.
With $F,G,E$ the integer vectors in the table, its exact expression is

$$
W_n(w)=\sum_{(i,j)}\sum_{z\notin\{0,n\}}
 \bigl((1-w_i)F_{ij}(z)+w_i(1-w_j)G_{ij}(z)
                       +w_iw_j E_{ij}(z)\bigr).
\tag{346.2}
$$

Fix the first $n-1$ bits to one and bit $n$ to zero. Substitution
of every suffix in lexicographic order gives the following complete
lists, of lengths $64,32,16,8,4,2,1$, respectively. Thus these
are all $127$ zero-word evaluations, not only sole-zero words.

| $n$ | Values of $W_n$ in suffix order |
| --- | --- |
| 1 | $2,2,4,2,8,8,8,6,8,8,8,6,10,10,8,6,13,13,13,11,15,15,13,11,15,15,13,11,13,13,9,7,11,11,13,11,15,15,15,13,15,15,15,13,15,15,13,11,15,15,15,13,15,15,13,11,15,15,13,11,11,11,7,5$ |
| 2 | $11,11,13,11,15,15,15,13,15,15,15,13,15,15,13,11,15,15,15,13,15,15,13,11,15,15,13,11,11,11,7,5$ |
| 3 | $13,13,15,13,15,15,15,13,15,15,15,13,13,13,11,9$ |
| 4 | $15,15,15,13,13,13,11,9$ |
| 5 | $15,15,13,11$ |
| 6 | $11,11$ |
| 7 | $10$ |

Their maxima are therefore

$$
\max W_n=(15,15,15,15,15,11,10).
\tag{346.3}
$$

Hence the correct deficit is exactly $15/64$, the union deficit is
at most $15/64$, and the base deficit is
$(W_n-15)/64\le0$. This proves all independent rows on every
suffix. At $1^7$ the law is
$(49e_0+5e_3+5e_4+5e_7)/64$.
Thus its positive-base deficit is $15/64$. Its stopped coefficients
also have $c=H=(34,28,2,0,0,0,0,0)/64$ in 109.1.
The one-seed execution and counted $N$ completion are those of 345.1.
At an actual first absence $n>7$, exact error is
$\max(15/64,a_n)=15/64$, including the tail tie.

For the full-$N$ lower, the following nonzero score weights are
used; all unlisted row weights in the $382$-row system are zero.

| Type | Word | Weight |
| --- | --- | ---: |
| $C$ | 0010111 | 1 |
| $P$ | 0100110 | 1 |
| $P$ | 0101001 | 1 |
| $P$ | 0101100 | 1 |
| $P$ | 0110010 | 1 |
| $P$ | 0110100 | 1 |
| $P$ | 0111000 | 1 |
| $P$ | 1000100 | 1 |
| $P$ | 1000101 | 1 |
| $P$ | 1001000 | 1 |
| $P$ | 1001010 | 1 |
| $P$ | 1010000 | 1 |
| $P$ | 1010001 | 1 |
| $P$ | 1100010 | 1 |
| $C$ | 1101100 | 2 |
| $C$ | 1101110 | 2 |
| $C$ | 1110000 | 1 |
| $C$ | 1110100 | 4 |
| $C$ | 1111000 | 5 |
| $C$ | 1111100 | 5 |
| $C$ | 1111110 | 5 |
| $T$ | 1111111 | 4 |

Its quotient is $\beta=(1,0,4,5,5,5,5)$, $K=42$, $C_y=17$.
The complete $N$ maxima from (344.3) are listed here; the maximum row
sum is $18$, and each maximum ranges over every label $0,\ldots,7$.

| Pair | $00$ | $01$ | $10$ | $11$ |
| --- | ---: | ---: | ---: | ---: |
| 12 | 1 | 6 | 6 | 5 |
| 13 | 3 | 4 | 5 | 6 |
| 14 | 4 | 3 | 5 | 6 |
| 15 | 3 | 4 | 5 | 6 |
| 16 | 4 | 3 | 5 | 6 |
| 17 | 5 | 2 | 5 | 6 |
| 23 | 4 | 2 | 5 | 7 |
| 24 | 4 | 2 | 5 | 7 |
| 25 | 4 | 2 | 5 | 7 |
| 26 | 5 | 1 | 5 | 7 |
| 27 | 4 | 2 | 6 | 5 |
| 34 | 4 | 4 | 5 | 5 |
| 35 | 4 | 4 | 5 | 5 |
| 36 | 5 | 3 | 5 | 5 |
| 37 | 6 | 2 | 5 | 5 |
| 45 | 4 | 4 | 5 | 5 |
| 46 | 5 | 3 | 5 | 5 |
| 47 | 6 | 2 | 5 | 5 |
| 56 | 5 | 3 | 5 | 5 |
| 57 | 6 | 2 | 5 | 5 |
| 67 | 6 | 3 | 5 | 4 |

The same cell-mass argument of 345.1, including constants,
singletons, repeats and reversed schedules, yields

$$
b_1+4b_3+5(b_4+b_5+b_6+b_7)\le1+42e.
\tag{346.4}
$$

For (346.1) the left side is $694/64$.
Thus every normalized finite feasible law has $e\ge15/64$.
To exclude every original competitor at a smaller positive cap,
use the necessity proof of 110.2 retaining the seven selected
coordinates and fixing higher replies to zero on finite actual
witnesses, with all higher output labels projected to zero.
Its common-seed truncations converge in the seven-bit catalog to
a feasible seven-bit allocation with these same seven demands.
The finite positive target is $\delta_{\theta_0}$ after projection,
even if the actual tail amplitude exceeds the smaller cap. No tail assumption
is required for this necessary seven-prefix restriction.
Consequently (346.4) holds at that proposed cap, a contradiction.
An exact zero-error competitor would also be feasible at every
smaller positive cap and is excluded. The upper law then proves
both attained original minima and every stated closed-cap equivalence.
This example is a completely displayed member of the joint
classification, without additional novelty claimed for its isolated
cut or individual allocation. $\square$

## 347. Attribution, comparison and the remaining unrestricted question

The coefficient inverse of 341.2 treats the complete preselected
cone, whereas 109.1 treats its stopped $g=0$ slice. The source and
seed interfaces of Source-Correlated Laws 45.1–45.3, the actual
finite-pattern theorem, II 140.2–140.3, and class-feasibility
transport 110.2 retain their prior roles. Section 343 explicitly
reuses the outward-star principle of XV 258.3–258.4; its extension
is positivity of aggregated whole-vector coefficients without assumed
$N$ realization. Section 345 is a full normalized equality-slice
classification with explicit dependence on $\mathcal D_7$.
It does not claim priority for any individual cut or vertex.

The seven-equal, high-head, unequal-seventh and complementary
seven-coordinate families in XIV 231, 238, 240–247, the weighted
and zero-cost core constructions in XVI 282, 294–295, and the
head strips and attained cones in XVII 300, 306, 313 remain
scoped suppliers. Their particular constructions and restrictions
are not re-proved here. The nine-coordinate and wider-head
families of XVIII 331–339 and its overlap discussion 340 remain
unchanged. This is a comparison of the specified statements and
coordinate ranges, without a claim that every combination in the
library was excluded or that the H7 result was previously
underivable. The name $H_7$ for this geometric slice is unrelated
to the signed row vector also called $H_7$ in XVI 292.8.

The corrected source-family boundary is also retained:
[Unequal Two-tail Frontier 17.1–17.3](FIB_NATIVE_UNEQUAL_TWO_TAIL_ATTAINED_FRONTIER.md#17-the-surviving-slack-identity-and-exact-remaining-obligations)
keeps the nonnegative identity $S=8(117d-11u)$ but refutes the
additional full-class bound $S\ge212d$ with its complete 217 law.
Its fixed-stock obstruction has a narrower premise. Its attained
unequal-tail wedge is the already credited conserved-transfer family
XVIII 324–327 under $t=(u+v)/2$, $\delta=(u-v)/2$, as explained
in XVIII 340.2. Neither statement is used as a new lower plane
or a new attained region here.

David Blackwell, [*Comparison of Experiments* (1951), §§2–3,
Theorem 2](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
uses a finite family of probability measures on a Borel field and
bounded finite-dimensional action/loss sets, reduced to closed convex
sets. One procedure yields an entire loss vector. Supporting
hyperplanes compare these whole attainable sets for every decision
problem. The general garbling converse is not supplied by that
paper's binary converse, and its framework constructs no paid
stopped-query protocol here.
Kaniewski, Lee and de Wolf,
[*Query complexity in expectation*, arXiv:1411.7280v1,
Definitions 6 and 8, Theorem 9](https://arxiv.org/abs/1411.7280v1),
characterize nonnegative scalar expectations by nonnegative literal
degree. Their cost is maximum supported root-to-leaf depth.
Their inverse samples coefficients $\alpha/M$ and outputs $M$
times a literal indicator. That scalar rescaling supplies neither
normalized vector outputs nor equal masses across counterfactual
cells. Those obligations are discharged here by the coefficient
inverse and the complete joint lifts, rather than by that scalar
precedent. Convex hulls, common randomization, finite support
maximization and exact rational polyhedral arithmetic are mature
methods, not new mathematical claims of this volume.

The unresolved original alternative still quantifies over every
finite horizon and every full unit-$O$ score $y\ge0$. It asks
for one unrestricted full $V\ge0$ and the same
$\theta\in[0,1]$ jointly satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\tag{347.1}
$$

The residual remains signed, and a nonzero zero-cost $V$ at
$\theta=1$ is allowed. The strict alternative requires one
actual same-profile full $N$ allocation and a strict uniform
lower bound against all original arbitrary-address, full-carrier
$O$ competitors, with original attainability and the entire tail.
The law obstruction of 342 and the common feasibility of 345
supply neither alternative. No arbitrary original-law preservation
is imposed as a substitute for original class feasibility.

The earlier-label regression remains actual:
$(r,g)=(19,436)$, $F_{19}=4181$, $N=1822917$, with replies
$0100$ at primes $2,3,5,7$. The legal table
$N(3,4;1,0,0,0)$ emits the earlier unqueried label one;
replacing its $00$ output by zero changes mass one, $\ell^1$
defect two, and TV one. This refutes that repair method, not the
existence of an arbitrary same-cap stopped replacement.
In particular neither arbitrary labels nor the independence of
$N$ cells $00,01$ can be discarded.

All constructed outputs have finite Borel support on the actual marks.
Every unchanged original nonatomic target gives that support mass
zero; hence their TV distance from it is one. Their selected-law
accuracy asserts no nonatomic, M1, physical implementation or
universal comparison result. The arguments and finite certificate
are ordinary mathematics, with no claim of current formal-kernel
verification.

## 追加锚（本行以下为增补区）
