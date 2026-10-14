# Recursive relational observation: an all-correlated native memory lower bound

## 1. The stationary task and its credited finite interface

**Convention 1.1 (scope and suppliers).** This is ordinary mathematical
reference theory for the public source at revision
`31da53e2b57cf3b20446f49f62b50858e94157b6`. It carries no Lean kernel
certification or worldwide priority claim. The following abbreviations
refer to the published suppliers:

- [LTR, Late Target One Read Memory](RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_ONE_READ_MEMORY.md), supplied by PR17061;
- [FMR, Late Target Fractional Memory Rate](RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md), supplied by PR17083;
- [AAR, Adaptive Acquired Reference Frontier](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md), especially §§12, 13 and 16;
- [NBP, Native Birth Provenance](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md), especially Assumption 14.1 and Theorem 14.4.

The local fractional seed, canonical simulation, paid cover
correspondence, native scaffold restriction, harmonic rounding, existence
of the rate and its strict upper bound are reused from those sources.
The lower transport proved below concerns all jointly admissible fibers,
including correlated fibers and target-dependent off-coordinate queries.
Published paragraphs are preserved; extensions follow the terminal
append anchor.

**Definition 1.2 (trees, literal replies and substitution).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
$$

Pairing is ordered. Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(w)$ is
alpha or beta at the corresponding leaf, branch at a pair, and absent
beyond a leaf. Define

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{NCM.1}
$$

For every public integer $D\ge1$, the source and request families are
exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{NCM.2}
$$

In one execution one actual initial source $t$ remains stationary
through preparation and later acquisition. The iterates $\rho^kt$ are
prediction targets, not changes to that stationary register. There is
no subtree, equality, source-identity, age, reset, copying, navigation
or free-advice port.

**Assumption 1.3 (paid preparation and complete retained alphabet).**
One deterministic effective preparation starts source-blind, with public
$D$ and common installed tables, and terminates on every
$t\in\mathcal F_D$. It does not receive the later request. Every source
distinction it acquires comes through charged original-root literal
Reads. It exports a finite code $E(t)$ before the request. The code
includes every accessible surviving source distinction: selectors,
control, buffers, operands, lengths, allocation, handles, counters and
accessible timing distinctions. Every other accessible field is a fixed
function of that code and public data. A separately paid handoff and
isolation service makes earlier preparation transcripts and all other
acquired descriptions inaccessible and supplies lawful reader entry.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. A common deterministic effective reader receives $E(t),D,p$
and the installed tables. It makes at most one fresh Read of the same
stationary source, at any finite word chosen from these inputs, and
exports a predictor $Z$. Zero-Read branches are permitted. For every
subsequently supplied authentic $k\ge0$, with no further Reads, it must
satisfy

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0).
\tag{NCM.3}
$$

Neither $k$ nor a source-dependent request is supplied before the query.
Define

$$
M_1(D)=\min |E[\mathcal F_D]|.
\tag{NCM.4}
$$

Only this complete attained alphabet is optimized. Preparation work and
control, temporary storage, installed tables, post-request workspace,
final predictor size, literal length and submitted letters, authentic
count representation, handoff, isolation, entry, authentication, source
continuity and physical time are separate resources. These services
are assumptions, not inferred physical operations.

**Convention 1.4 (the supplied exact temporal factor).** Put
$s(q)=\#L(q)+2\#R(q)$ and $e(\alpha)=0,e(\beta)=1$. Use precisely
the AAR Definition 12.2 and Proposition 13.3 factor $\Gamma_q(u)$.
At an original branch endpoint it is $(0,0)$. If the first original
leaf along $q$ is a leaf $\ell$ at $a$, and $q=ar$, then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{NCM.5}
$$

The supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{NCM.6}
$$

On attained factors $c=1$ implies $b\ge2$. AAR Theorem 12.3 gives
$r_{\rho^ku}(q)=\operatorname{Pred}(\Gamma_q(u),k)$ for every
$k\ge0$. Conversely the trajectory recovers $b$ as its first branch
count and $c$ from the presence of an alpha stage. Equality of factors
is exactly equality of trajectories. It is not equality of first-leaf
descriptors: the distinct blocking positions in AAR Proposition 13.3
can give equal factors. In the actual wrapper,
$\Gamma_{Rq}(\langle\alpha,v\rangle)=\Gamma_q(v)$.

**Definition 1.5 (canonical blocks and unchanged joint fibers).** Set
$C=\langle\alpha,\alpha\rangle$ and

$$
S_1=\{\alpha,\beta,C\},\qquad
S_{d+1}=\{\alpha,\beta\}\ \sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{NCM.7}
$$

These are actual trees of height at most $d$. For integers $d,n\ge1$,
following FMR Definition 6.1, a nonempty $B\subseteq S_d^n$ is jointly admissible
when for every $i\in\{1,\ldots,n\}$ and $q\in W_d$ either
$\Gamma_q(x_i)$ is constant on $B$, or there exist
$j\in\{1,\ldots,n\}$ and $a\in W_d$ such that

$$
\forall x,y\in B,\qquad
r_{x_j}(a)=r_{y_j}(a)
\ \Longrightarrow\ \Gamma_q(x_i)=\Gamma_q(y_i).
\tag{NCM.8}
$$

Both $j$ and $a$ may depend on $B,i,q$; $j=i$ is not required.
The set $B$ need not be a product. A set $P\subseteq S_d$ is locally
admissible when it satisfies this condition with $n=1$. Let $K_d(n)$
be the least number of jointly admissible sets covering $S_d^n$.
Let $Z_d(n)$ be the fractional cover optimum using that same entire
family of joint sets: its nonnegative coefficients $c_B$ satisfy
$\sum_{B\ni x}c_B\ge1$ for every $x\in S_d^n$, and its objective
is $\sum_B c_B$.

FMR Lemma 2.2 and Lemma 6.2 retain every finite native word in this
definition. A word of length $d$ on $S_d$ returns alpha exactly when
its parent at depth $d-1$ is branch, and absent otherwise; every longer
word is absent. Thus one boundary experiment, followed by a public
function of its reply, simulates any longer experiment within its
original block. This neither projects a fiber nor changes the queried
coordinate. FMR proves the paid native cover correspondence and the
limits

$$
\sigma_d=\lim_{n\to\infty}\frac{\log_2 K_d(n)}n,
\qquad
\lambda=\lim_{D\to\infty}2^{-D}\log_2 M_1(D),
\qquad
\lambda\ge2^{-d}\sigma_d.
\tag{NCM.9}
$$

## 2. A sufficient transport relation for finite native interfaces

**Definition 2.1 (finite interface and weights).** Let $S$ be a finite
nonempty set, $Q$ a finite target index set, and $\mathcal A$ a finite
experiment index set. For $q\in Q$ let $g_q:S\to Y_q$; for
$a\in\mathcal A$ let $r_a:S\to V_a$. A constant experiment is
allowed. Fix an integer $m\ge2$ and assume every experiment has at
most $m$ replies. Local and
joint admissibility mean exactly (NCM.8), with $g_q,r_a$ in place of
$\Gamma_q,r_{(-)}(a)$, and arbitrary queried coordinate permitted.

Give each $x\in S$ a positive weight $w(x)$. Write

$$
w(P)=\sum_{x\in P}w(x),\qquad
\Omega(B)=\sum_{x\in B}\prod_{i=1}^n w(x_i).
\tag{NCM.10}
$$

A nonempty $P\subseteq S$ is range feasible if
$|g_q(P)|\le m$ for every $q\in Q$. This is a necessary condition
for a coordinate projection of a jointly admissible set; it is not
asserted sufficient.

**Theorem 2.2 (transport through projections with deficient reply
capacity).** Fix integers $1\le r<m$ and real numbers
$C_0>0$, $0<c_0\le C_0$. Suppose the finite interface satisfies:

1. Every locally admissible $P$ has $w(P)\le C_0$.
2. For every range-feasible locally inadmissible $P$, every experiment
   has at most $r$ replies on $P$, and there is a target $q_P$ such
   that $|g_{q_P}(P)|>r$ and
   $w(P\cap g_{q_P}^{-1}\{v\})\le c_0$ for every value $v$.

For every $n\ge1$ and every jointly admissible nonempty $B\subseteq S^n$,
let $G$ be the set of coordinates with locally admissible projection
$P_i=\pi_i(B)$, and $I$ its complement. Then

$$
\Omega(B)\le C_0^{|G|}c_0^{|I|}\le C_0^n.
\tag{NCM.11}
$$

Consequently any cover of $S^n$ by jointly admissible sets has at least
$\lceil(w(S)/C_0)^n\rceil$ members. The same product weight divided
by $C_0^n$ is feasible for the joint fractional-cover dual.

Proof. For any coordinate $i$ and target $q$, its witness on the
unchanged $B$ has at most $m$ replies. Since $g_q(x_i)$ factors through
that reply, $|g_q(P_i)|\le m$. Thus every $P_i$ is range feasible.

For $i\in I$ choose $q_i=q_{P_i}$. A constant experiment cannot
determine its more than $r$ target values. Nor can an experiment in
any coordinate $j\in I$, because it has at most $r$ replies on $P_j$.
The witnessing experiment must therefore belong to a coordinate
$j(i)\in G$. The factorization in (NCM.8) supplies a function
$d_i$ on its attained replies, so that, on this same $B$,

$$
g_{q_i}(x_i)=d_i(r_{a_i}(x_{j(i)})).
\tag{NCM.12}
$$

Fix a tuple $u$ of all the $G$ coordinates jointly. In its section of
$B$, each right-hand side in (NCM.12) is fixed. Each $I$ coordinate
therefore lies in one target cell of weight at most $c_0$. That section
is contained in the Cartesian product of those cells. Nonnegativity
of the ambient product weights gives

$$
\begin{aligned}
\Omega(B)
&\le c_0^{|I|}
 \sum_{u\in\pi_G(B)}\prod_{j\in G}w(u_j)\\
&\le c_0^{|I|}\prod_{j\in G}w(P_j)
 \le c_0^{|I|}C_0^{|G|}.
\end{aligned}
\tag{NCM.13}
$$

The empty product convention covers $I=\varnothing$. If $G$ were empty
and $I$ nonempty, the required witnesses could not exist, so no such
nonempty $B$ occurs. The proof never asserts that a section is a
product, that its coordinates are independent, or that a bad projection
is locally admissible after conditioning.

The full product has weight $w(S)^n$. Summing the bound $C_0^n$ over
a cover, even an overlapping one, proves its cardinality lower bound.
More generally, for any fractional cover,

$$
\left(\frac{w(S)}{C_0}\right)^n
\le\sum_B c_B\frac{\Omega(B)}{C_0^n}
\le\sum_B c_B.
$$

This proves the dual assertion directly. $\square$

The hypotheses are finite checks on sets, functions and weights; they
are sufficient conditions, without a completeness claim. Fixing $u$
in this proof is an analytical section, not information supplied to a
native reader. Different bad coordinates may have different targets,
experiments and donor coordinates.

## 3. Full depth-two native transport

**Convention 3.1 (the credited depth-two seed and its complete tables).**
Use $A=\alpha$, $B=\beta$, $C=\langle\alpha,\alpha\rangle$ and
$g_{xy}=\langle x,y\rangle$, for $x,y\in\{A,B,C\}$. Then

$$
S_2=\{\alpha,\beta\}\ \sqcup\mathcal G,
\qquad \mathcal G=\{g_{xy}:x,y\in\{A,B,C\}\},
\qquad |S_2|=11.
$$

Let $\gamma(A)=(2,1)$, $\gamma(B)=(1,0)$ and $\gamma(C)=(0,0)$.
Let $\kappa(A)=\alpha$, $\kappa(B)=\beta$ and
$\kappa(C)=\mathsf{branch}$. The complete boundary tables, from FMR
Theorem 5.1 and the literal definition, are

$$
\begin{array}{c|ccc|ccc}
u&r_u(\varepsilon)&r_u(L)&r_u(R)
 &\Gamma_\varepsilon(u)&\Gamma_L(u)&\Gamma_R(u)\\ \hline
\alpha&\alpha&\mathsf{absent}&\mathsf{absent}
 &(2,1)&(3,0)&(4,1)\\
\beta&\beta&\mathsf{absent}&\mathsf{absent}
 &(1,0)&(2,0)&(3,1)\\
g_{xy}&\mathsf{branch}&\kappa(x)&\kappa(y)
 &(0,0)&\gamma(x)&\gamma(y).
\end{array}
\tag{NCM.14}
$$

For either side target, the two root-leaf values and the three child
values are pairwise distinct. The root target is always determined by
the root reply. A length-two query on $S_2$ returns alpha exactly when
the child selected by its first letter is $C$, and absent otherwise;
every longer query is absent. These exhaust all words, including
queries beyond leaves or below a cutoff branch.

FMR Theorem 5.1 supplies the maximal locally admissible sets

$$
H_\alpha=\{\alpha\}\cup\mathcal G,\qquad
H_\beta=\{\beta\}\cup\mathcal G,\qquad
T_{xy}=\{\alpha,\beta,g_{xy}\}.
\tag{NCM.15}
$$

It also supplies the optimal local fractional cover: coefficients
$8/17$ on each of $H_\alpha,H_\beta$ and $1/17$ on each of the nine
$T_{xy}$, with total $25/17$. These are reused local results.
Use its integer-scaled dual weights

$$
w(\alpha)=w(\beta)=8,\qquad w(g_{xy})=1,
\qquad w(S_2)=25.
\tag{NCM.16}
$$

Each maximal set in (NCM.15) has weight $17$.

**Lemma 3.2 (a nonlocal depth-two target requires a locally admissible
donor).** Let $n\ge1$ and $\varnothing\ne B\subseteq S_2^n$ be jointly
admissible. Write $P_i=\pi_i(B)$. If $P_i$ is locally inadmissible,
then every finite native experiment in this coordinate has at most
three replies on $P_i$, while at least one side target has exactly
four values there. Each witnessing experiment for such a target must
query a coordinate whose projection is locally admissible.

Proof. Every target on every projection has at most four values, since
its single witnessing experiment has at most four replies. By the
credited classification, a locally inadmissible $P_i$ contains both
root leaves and at least two distinct branches. For $s=L,R$, let
$A_{i,s}\subseteq\{A,B,C\}$ be the child symbols appearing at that
side among these branches. Table (NCM.14) gives

$$
|\Gamma_s(P_i)|=2+|A_{i,s}|\le4,
\qquad |A_{i,s}|\le2.
\tag{NCM.17}
$$

The root experiment has at most three replies. Each side experiment
has absent on both root leaves and at most two child replies, hence
at most three replies. A length-two experiment is a function of a side
reply and has at most two; a longer experiment is constant absent.

Two distinct branches differ at some side $s_i$, so
$|A_{i,s_i}|\ge2$. Equation (NCM.17) makes it exactly two, giving
four distinct target values. Its witness cannot be constant or query
any locally inadmissible projection, since all such experiments have
at most three replies. Its queried projection must be locally
admissible. This uses a witness separately for each target on the
same $B$; it places no locality requirement on that witness. $\square$

**Theorem 3.3 (sharp product mass against every correlated fiber).**
For every integer $n\ge1$ and every jointly admissible
$B\subseteq S_2^n$, let $g$ and $b$ be the numbers of its locally
admissible and locally inadmissible coordinate projections. Then

$$
\boxed{\quad
\sum_{x\in B}\prod_{i=1}^n w(x_i)
\le17^g8^b\le17^n.
\quad}
\tag{NCM.18}
$$

The bound $17^n$ is attained by $H_\alpha^n$. Equivalently, for the
analytical probability $\mu=w/25$,
$\mu^n(B)\le(17/25)^n$.

Proof. Apply Theorem 2.2 with $m=4$, $r=3$, $C_0=17$, $c_0=8$.
Locally admissible projections have weight at most $17$ by
(NCM.15). The argument in Lemma 3.2 applies to every range-feasible
locally inadmissible subset of $S_2$. It supplies the deficient reply
capacity and a four-valued side target. Each root-leaf cell of that
target has weight $8$. Each branch cell fixes one child and contains
at most three branches of weight $1$, so has weight at most $3$.
Thus every selected target cell has weight at most $8$, as required.
The resulting estimate is (NCM.18). Products of $H_\alpha$ are jointly
admissible by their own-coordinate witnesses and have weight $17^n$.
$\square$

The product measure is a lower-bound witness, not a source prior.
The proof quantifies over every correlated $B$. In particular it does
not replace a fiber by its product of projections, declare its
projections admissible, or assume a common query for distinct targets.
The smaller product sets used to demonstrate equality impose no
restriction on competitors.

## 4. Exact joint fractional value and a uniform depth-two block error

**Theorem 4.1 (joint fractional optimum and regularized depth two).**
For every integer $n\ge1$,

$$
Z_2(n)=\left(\frac{25}{17}\right)^n,
\qquad
\left\lceil\left(\frac{25}{17}\right)^n\right\rceil
\le K_2(n)
\le H_{11^n}\left(\frac{25}{17}\right)^n,
\tag{NCM.19}
$$

where $H_N=\sum_{j=1}^N1/j$. Consequently

$$
\sigma_2=\log_2\frac{25}{17}.
\tag{NCM.20}
$$

For all $n\ge1$, an explicit uniform finite-block error is

$$
\eta_2(n)=\frac{\log_2(1+3n)}n\longrightarrow0,
\qquad
\sigma_2\ge\frac{\log_2 K_2(n)}n-\eta_2(n).
\tag{NCM.21}
$$

Proof. The rational point weights
$y_n(x)=17^{-n}\prod_i w(x_i)$ have mass at most one on every
jointly admissible set by Theorem 3.3. Their total on $S_2^n$ is
$(25/17)^n$. Summing against any fractional cover gives the lower
bound on $Z_2(n)$, and summing over any integral cover gives the
ceiling lower bound on $K_2(n)$.

For the opposite fractional inequality, reuse the local coefficients
in Convention 3.1. Every product of their locally admissible sets is
jointly admissible: the requested coordinate uses its own local
experiment. Assign each product the product of those coefficients.
The total coefficient covering a tuple is the product of its local
coverages, hence one; total coefficient is $(25/17)^n$. This is an
explicit primal cover matching the all-competitor dual. The local
seed is credited to FMR; the feasibility of its dual tensor against
all additional correlated competitors is Theorem 3.3.

FMR Lemma 4.4's finite harmonic rounding, applied to these $11^n$
vertices, gives the integral upper in (NCM.19), with paid attainment
as in FMR Lemma 6.2. Since

$$
H_{11^n}\le1+\ln(11^n)=1+n\ln11<1+3n,
$$

the normalized logarithmic upper and lower differ by at most
$\eta_2(n)$. This tends to zero, proving (NCM.20) and (NCM.21).
The lower bound applies uniformly to every allowed fiber and reader;
the upper supplies one valid code. No value of finite $K_2(n)$ alone
is treated as a lower bound on its limiting rate. $\square$

## 5. The strictly stronger original all-competitor lower

**Theorem 5.1 (unchanged full-family memory lower).** Under the stationary
task and complete export assumptions, for every integer $D\ge2$,

$$
\boxed{\displaystyle
M_1(D)\ge
\left\lceil\left(\frac{25}{17}\right)^{2^{D-2}}\right\rceil,
\qquad
\lambda\ge\frac14\log_2\frac{25}{17}.}
\tag{NCM.22}
$$

In particular the normalized lower is strictly larger than the credited
LTR lower $\frac14\log_2(7/5)$. Together with the unchanged FMR strict
upper it gives

$$
\frac14\log_2\frac{25}{17}\le\lambda<0.216605159.
\tag{NCM.23}
$$

Proof. Set $h=D-2$, $n=2^h$. Use precisely FMR Theorem 6.3's actual
restriction: put a perfect ordered binary scaffold of height $h$ in
$v$, and fill its $n$ frontier occurrences, at words $a_i$ of length
$h$, with all tuples $x\in S_2^n$. These are simultaneous actual
trees of height at most $D$, each giving
$t_x=\langle\alpha,v_x\rangle\in\mathcal F_D$.

For any correct original preparation, restrict its same complete code
$E$ to these sources. For every block target $q\in\{\varepsilon,L,R\}$,
the actual target is $Ra_iq$, of length at most $D$, and its factor
is $\Gamma_q(x_i)$. The occurrence is present in every tree of this
slice, so the supplied present-subtree transport is lawful for every
subsequent $k$.

Every original-root word is accounted for. The root, the left wrapper
cone and words ending strictly above the block frontier give constant
replies. Every other right-cone word enters exactly one actual block
with a finite suffix. On $S_2$ that suffix is either a boundary
experiment, a length-two coarsening of a side experiment, or constant
absent, by (NCM.14). Its queried block may be different from the
target block. This is the native every-word correspondence in the
credited scaffold restriction, without modifying any fiber or
projecting away its correlations.

Fixing a complete code and a target fixes its zero-Read decision or
chosen literal before any reply or supplied $k$. Equal replies must
give the same trajectory, hence the same factor by Convention 1.4.
Thus each nonempty restricted code fiber is jointly admissible in
$S_2^n$. These fibers partition a set of total integer product weight
$25^n$, and each has weight at most $17^n$ by Theorem 3.3. Their
number, and therefore $|E[\mathcal F_D]|$, is at least
$\lceil(25/17)^n\rceil$. This holds for every original competitor,
whatever its paid preparation, correlations or target-specific literal
choices.

Taking the minimum proves the finite bound. Divide its logarithm by
$2^D=4n$ and use the rate existence supplied by FMR Theorem 3.3.
This proves the rate lower. Its strict improvement is the exact
comparison $25\cdot5=125>119=7\cdot17$. FMR Theorem 5.2 supplies
the upper in (NCM.23); it is not rederived or renamed here. $\square$

**Proposition 5.2 (paid meaning of the matching block upper).** Suppose
the depth-two blocks occur at public prefix-free actual addresses
$Ra_i$, with $|a_i|\le H$. The rounded cover used in Theorem 4.1
has a deterministic source-blind preparation using at most

$$
3n\text{ Reads},\qquad
H+2\text{ maximum literal length},\qquad
n(3H+5)\text{ submitted letters}.
\tag{NCM.24}
$$

Its late reader needs at most one original-root Read of length at most
$H+2$. The construction uses one complete retained name and preserves
all targets and all authentic subsequent counts.

Proof. Reuse the finite codebook and witness installation in FMR
Lemma 6.2. Actually submit $Ra_i$, $Ra_iL$, $Ra_iR$ for each block,
including words returning absent. For actual $S_2$ blocks these
replies identify the block exactly; for height-at-most-two blocks
they identify its canonical representative and preserve every selected
factor by FMR Lemma 2.2. Compute the first-containing-cover-member
index from this genuinely acquired tuple, and export only its complete
fixed-width name. The separately paid isolation removes access to all
other acquired data and selectors. The lengths sum to at most
$(H+1)+2(H+2)=3H+5$ per block.

After the request, the installed table chooses one coordinate and one
boundary word, or zero Reads. Submit its full literal $Ra_jw$.
Constant virtual-wrapper probes are computed from public constants;
every source-bearing probe is a charged literal on the same tree.
No constituent subtree or copied source is an operational input.
The reply decoder gives the factor, and (NCM.6) answers every later
$k$. On $S_2^n$ every greedy choice covers a previously uncovered
tuple, so its first-membership index is attained. Thus this is an
acquired alphabet, not an oracle providing a preassigned color.
$\square$

The existing whole-family FMR constructions retain their separate
preparation bounds $2^D-1$ Reads, maximum literal length $D$, and
$(D-1)2^D+1$ submitted letters. Neither those sufficient bounds nor
(NCM.24) optimize acquisition. Codebook generation, cover search,
membership work, temporary buffers and final predictors remain
separate resources. The lower bound assumes none of these costs is
small and does not infer free total efficiency from retained memory.

## 6. A native depth-three cycle marking the transport boundary

**Proposition 6.1 (joint recoverability with no locally admissible
coordinate projection).** Define

$$
\begin{aligned}
A&=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad J=\langle B,A\rangle,\quad Q=\langle C,A\rangle,\\
(u_0,u_1,u_2,u_3,u_4)
&=(\langle A,A\rangle,\langle B,A\rangle,
\langle C,C\rangle,\langle J,J\rangle,\langle A,Q\rangle),\\
P&=\{u_0,u_1,u_2,u_3,u_4\}\subset S_3.
\end{aligned}
\tag{NCM.25}
$$

Let $\tau$ interchange $1$ and $4$ and fix $0,2,3$, and put

$$
B_* =\{(u_s,u_{\tau(s)}):0\le s\le4\}\subset S_3^2.
\tag{NCM.26}
$$

Both coordinate projections of $B_*$ equal the locally inadmissible
$P$, but $B_*$ is jointly admissible for the complete depth-three target
menu with every finite native experiment word allowed. All its targets
have at most four values,
and the experiment $RL$ on $P$ has four replies. Thus the implication
in Lemma 3.2 that an inadmissible projection must obtain its missing
target from an admissible projection fails at depth three.

Proof. All seven boundary experiments on $P$, with columns ordered
$u_0,u_1,u_2,u_3,u_4$, are

$$
\begin{array}{c|ccccc}
\varepsilon&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
L&\alpha&\beta&\mathsf{branch}&\mathsf{branch}&\alpha\\
R&\alpha&\alpha&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
LL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{absent}\\
LR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\mathsf{absent}\\
RL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\
RR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\alpha.
\end{array}
\tag{NCM.27}
$$

The complete corresponding factor table is

$$
\begin{array}{c|ccccc}
\varepsilon&(0,0)&(0,0)&(0,0)&(0,0)&(0,0)\\
L&(2,1)&(1,0)&(0,0)&(0,0)&(2,1)\\
R&(2,1)&(2,1)&(0,0)&(0,0)&(0,0)\\
LL&(3,0)&(2,0)&(2,1)&(1,0)&(3,0)\\
LR&(4,1)&(3,1)&(2,1)&(2,1)&(4,1)\\
RL&(3,0)&(3,0)&(2,1)&(1,0)&(0,0)\\
RR&(4,1)&(4,1)&(2,1)&(2,1)&(2,1).
\end{array}
\tag{NCM.28}
$$

The $LL$ target has four distinct values. Every boundary experiment
except $RL$ has at most three replies. The experiment $RL$ merges
$u_0,u_1$, whose $LL$ factors are different. No boundary experiment
therefore determines this target on $P$. A length-three experiment
returns alpha exactly when its length-two parent is branch, and
absent otherwise; it is a function of that boundary reply. Every
longer experiment is absent. A constant experiment also fails. Hence
$P$ is locally inadmissible for the full arbitrary-word interface.

For either coordinate of $B_*$, recover its $LL$ factor by reading
$RL$ in the other coordinate. The reply decoder is

$$
\mathsf{absent}\mapsto(3,0),\qquad
\alpha\mapsto(2,1),\qquad
\beta\mapsto(1,0),\qquad
\mathsf{branch}\mapsto(2,0).
\tag{NCM.29}
$$

For the first coordinate these replies, in row order $s=0,1,2,3,4$,
are absent, branch, alpha, beta, absent, exactly resolving its four
$LL$ values in (NCM.28). Since $\tau^2$ is the identity, the same
decoder works for the second coordinate.

Every other target has an own-coordinate witness. The full selection
rule is

$$
\begin{array}{c|ccccccc}
\text{target}&\varepsilon&L&R&LL&LR&RL&RR\\ \hline
\text{queried coordinate}&\text{none}&\text{own}&\text{own}&\text{other}&\text{own}&\text{own}&\text{own}\\
\text{word}&\text{constant}&L&R&RL&L&RL&R.
\end{array}
\tag{NCM.30}
$$

The root factor is $(0,0)$. For $L$ and $R$, map constructor replies by
$\gamma\circ\kappa^{-1}$ on the attained replies. For $LR$ with
experiment $L$, use
$\alpha\mapsto(4,1)$, $\beta\mapsto(3,1)$,
$\mathsf{branch}\mapsto(2,1)$. For $RL$ with experiment $RL$,
use absent $\mapsto(3,0)$, alpha $\mapsto(2,1)$,
beta $\mapsto(1,0)$, branch $\mapsto(0,0)$.
For $RR$ with experiment $R$, use alpha $\mapsto(4,1)$ and
branch $\mapsto(2,1)$. These exhaust attained replies; values on
unattained replies are immaterial. Tables (NCM.27)–(NCM.28) verify
every target on both projections. The all-word reduction above
also exhausts arbitrary native experiments. $\square$

**Proposition 6.2 (paid attainment as an exact full-family fiber).**
At $D=4$ there is a preparation and one common reader on all of
$\mathcal F_4$ satisfying Assumption 1.3 such that exactly

$$
t_s=\langle\alpha,\langle u_s,u_{\tau(s)}\rangle\rangle,
\qquad 0\le s\le4,
\tag{NCM.31}
$$

share one attained code; every other source has a singleton code.
Preparation uses $31$ Reads of maximum literal length $5$ and $129$
submitted letters. The complete attained alphabet has $2{,}090{,}914$
values. The common reader uses at most one fresh Read of length at
most $4$ and is correct for every $p\in\mathcal P_4$ and every
subsequent authentic $k\ge0$.

Proof. Each right subtree in (NCM.31) has height at most four, so all
five sources belong to the original family. Before any request,
actually submit every $Rw$ with $|w|\le4$, including absent words.
Since $h(v)\le4$, this complete finite reply table determines all of
$v$, including its terminal labels. It has
$\sum_{j=0}^4 2^j=31$ words, maximum length $5$ and
$\sum_{j=0}^4(j+1)2^j=129$ letters.

Compare this acquired description locally with the five public
representatives. Give those descriptions one common name and each
other acquired tree its distinct name in a fixed public ordering.
These comparisons use paid descriptions, not a source-identity or
equality port. Export just this complete name; all other source
dependence is isolated by the paid service. The full-family counts
are $f_0=2$, $f_{j+1}=2+f_j^2$, so
$f_1=6,f_2=38,f_3=1446,f_4=2{,}090{,}918$. Merging exactly five
sources replaces five names by one, giving the stated attained alphabet.
This large supporting code is not an assertion about optimal memory.

On the common name, $p=R$ has the constant branch trajectory. Every
other permitted target is $p=Rbq$, with $b=L$ or $R$ and $q\in W_3$.
The target belongs to the actual block at $Rb$. Apply (NCM.30): an
own-coordinate experiment $a$ becomes the original-root literal
$Rba$, and an other-coordinate experiment becomes $R\bar b a$,
where $\bar L=R$ and $\bar R=L$. A root block target needs zero
Reads. Every submitted literal has length at most four. In particular
the requests $RLLL$ and $RRLL$ use respectively $RRRL$ and $RLRL$.
The source is never changed, reset or copied. Present-subtree transport
at $RL$ and $RR$, followed by (NCM.6), proves correctness for every
$k$. Singleton names identify their acquired source through common
tables and need zero Reads for any target. Thus one reader works on
the entire variable-shape family, with exactly the fiber claimed.
$\square$

The obstruction is to the stated local-capacity transport relation:
at depth three a range-feasible locally inadmissible projection can
supply four replies and the two projections can provide mutual
off-coordinate assistance. There is then no locally admissible
coordinate to fix in the proof of Theorem 2.2. This is stronger than
the already credited FMR §7 failure of a single child projection to
be admissible: here both projections fail and every native target is
still served. It neither refutes Theorem 3.3 at depth two nor proves
failure of every higher-depth product dual, entropy method or joint
certificate. Proposition 6.2 establishes legal operational attainment
under declared services, without asserting physical realization.

## 7. Primary interfaces, mathematical attribution and open boundaries

**Convention 7.1 (native source correspondence).** In
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
`Source` is `FreeMagma Bool`, alpha is `true`, beta is `false`, and
`substitution` is the homomorphism (NCM.1). In
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
`Address` is a Boolean list, false means $L$, true means $R$, and
`Reply` and `readout` supply all four replies on every finite legal
word. Its recognition objective is different from (NCM.3).
[NativeDepthPatterns](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean)
supplies `original_present_transport` only at actual original
occurrences and `original_prefix_locality` for original-boundary
dependence. AAR §§12, 13 and 16 supply the exact factors, minimal
passive codes and known-menu acquisition results; their menu is fixed
before acquisition. Their full-menu zero-later-Read endpoint is
already covered. None of these interfaces is renamed as the lower
transport theorem here.

NBP Assumption 14.1 and Theorem 14.4 supply a paid common-start
stationary handoff discipline for a known-row predecessor task with
an authenticated one-image family and whole-predecessor output.
Their service assumptions do not construct isolation or authentication
physically. The
[`target_family_minimal_quotient`](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean)
universal property supplies passive joint-kernel factorization, not a
one-native-reply geometry. The
[`compact_observation_factorization`](../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean)
declaration assumes a nonempty compact source, compatible continuous
surjective finite discrete observations forming a fiber basis, and
continuous finite readouts. It gives a sufficient finite observation
level, also for bounded-length action words over a finite action alphabet with continuous actions. It gives
no effective native acquisition depth, memory-rate lower certificate
or convergence modulus. These declaration correspondences confer no
Lean certification on the ordinary proofs here.

**Convention 7.2 (primary literature and limits of transfer).** The
following primary interfaces are credited at their stated scope.

| Primary source | Correspondence and mathematical limit |
| --- | --- |
| Anna Gál and Peter Bro Miltersen, *The Cell Probe Complexity of Succinct Data Structures*, BRICS RS-03-44, introductory systematic model, [primary report](https://www.brics.dk/RS/03/44/BRICS-RS-03-44.pdf) | Systematic storage preserves input and adds an index. Here the stationary native source plays the preserved-input role and $E$ the index role. The native constructor array has grammar-constrained support and four-valued cells; all retained advice is available to the reader. Their bit-probe numerical bounds and query families are not transferred. |
| Sumegha Garg, Songhua He, Yuanzhi Li, Periklis A. Papakonstantinou and Xin Yang, *Systematic Data Structure Lower Bounds via the Query-with-Sketch Model*, [arXiv:2609.18024v1](https://arxiv.org/html/2609.18024v1), Definition 2.1 and Lemma 2.5 | The code corresponds to a sketch supplied before input-coordinate probes. Here every request has its own target, all use the same acquired sketch, and the one probe is a native constructor reply. Their conditional joint min-entropy lemma has additional hypotheses after partial assignments. No such entropy premise or matrix-powering bound is imported. |
| Tomasz Gogacz and Szymon Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, [arXiv:1512.01808v1](https://arxiv.org/html/1512.01808v1), Theorem 1 and Corollary 1 | A fixed schema's functional dependencies become zero conditional-entropy constraints on a common relation; the almost-entropic cone and its Shannon relaxation have distinct roles. Here the witness dependencies vary with the attained code, target and block length. Theorem 2.2 bounds their weighted native relations directly. The database theorem does not provide its reply-capacity hypothesis or a native uniform block error. |
| Ali Makhdoumi, Shao-Lun Huang, Muriel Médard and Yury Polyanskiy, *On Locally Decodable Source Coding*, [arXiv:1308.5239v2](https://arxiv.org/html/1308.5239v2), §II, Definition 1 | Their local decoder reads a bounded subset of a compressed bit string, with distributional block-error criteria. Here the complete retained code is available and the sole later probe reads the original stationary tree, with correctness for every source. Their locality-rate converses are not native converses. |
| Nicolas Charpenay, Maël Le Treust and Aline Roumy, *On the Linearization of Optimal Rates for Independent Zero-Error Source and Channel Problems*, [arXiv:2407.02281v2](https://arxiv.org/html/2407.02281v2), introduction and graph-product discussion | Their pair-confusability graphs, AND products and additivity hypotheses belong to their zero-error source/channel problems. FMR §7 shows that all pairs can be admissible in the native model while a larger fiber is not. No such graph product replaces (NCM.8). |

Finite fractional covering and harmonic rounding are established
methods. The local $25/17$ primal and dual are credited to FMR
Theorem 5.1. Theorems 2.2, 3.3, 4.1 and 5.1 and Propositions 6.1–6.2
give repository-derived ordinary deductions with explicit native
assumptions. They assert no worldwide novelty. The added relation is
the forced ownership of a four-valued missing target by a projection
with sufficient native reply capacity; at depth two such a projection
is locally admissible. The two-target constraints $L$ and $R$ are used
together in (NCM.17). They are never bundled into a demand for one
reply recovering an entire target vector. A ceiling for a scalar
single-target method would therefore be a separate boundary, without
contradicting this multi-target proof.

**Open problem 7.3 (the unchanged sharp rate and a convergent lower
hierarchy).** Determine the exact original $\lambda$, or effective
all-competitor lower endpoints tending to it with a certified gap to
the computable upper endpoints. Theorem 4.1 settles one regularized
depth and supplies $\eta_2(n)\to0$ only at that depth. It does not
prove errors $\eta_d(n)\to0$ for all $d$ or convergence of this
sufficient certificate class. The native cycle in §6 identifies the
missing extension of its local-capacity hypothesis. A positive bridge
at greater depth must bound the weighted masses of the actual joint
fibers even when deficient local recovery is supported by mutually
dependent inadmissible projections. It may use different hypotheses;
the cycle proves no noncomputability or impossibility of that goal.

**Open problem 7.4 (general finite memory and wider recovery).**
Determine $M_1(D)$ for general finite $D$, including the credited
unresolved $M_1(3)\in\{3,4\}$. Exact joint fractional values and
vanishing normalized rounding loss do not determine general finite
integral optima. The selected operational recovery remains

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow
\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{NCM.32}
$$

The inverse arrow recovers that temporal factor, not the full source,
an authentic unknown age, hidden history, or physical space and time.
Additional recovery relations and their legal operations and resources
remain necessary for the original minimal-relations/internal-observer
programme. The strict lower advance does not replace its completion
criterion or resolve the whole programme.

## 追加锚（本行以下为增补区）
