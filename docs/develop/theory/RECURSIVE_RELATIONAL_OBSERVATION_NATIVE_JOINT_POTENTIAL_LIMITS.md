# Recursive relational observation: native joint potential limits

This volume proves two results about whole-block weights in the native
late-target problem. On a fixed scaffold filled with the four-state core,
every admissible relation has a lossless local completion, even when its
weights correlate all modules. On a different, diagonal support, exact
pressure separates owned joint weights from a specified language of finite
nonnegative separable majorants and scalar cap summation. The restricted
core atlas has a sharp optimizer ceiling. The diagonal obstruction is
pointwise and is already handled by the existing full joint rule.

These are ordinary mathematical statements and proofs, not Lean
certifications. This source is reference input; no statement of compilation,
freezing or machine-maintained coverage is made. Its mathematics uses the
GitHub `$...$` and `$$` conventions. Existing text is preserved when this
volume is extended; further material belongs after its final append anchor.

## 1. The unchanged source, observer and pressure

**Definition 1.1 (actual native sources and replies).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,
\qquad
\operatorname{ht}(\langle x,y\rangle)
=1+\max\{\operatorname{ht}(x),\operatorname{ht}(y)\}.
$$

Pairing is free and ordered. Every finite word in $L,R$, including
$\varepsilon$, is an original-root literal. Its reply $r_t(a)$ is alpha
or beta at a leaf, branch at a pair, and absent if traversal has passed a
leaf. Put

$$
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\},
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

For every public integer $D\ge1$ retain exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:
                         \operatorname{ht}(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{JPL.1}
$$

One actual initial source remains stationary throughout preparation and
later acquisition. The iterates $\rho^kt$ are prediction targets.

**Assumption 1.2 (the complete paid-export interface).** Preparation is
one deterministic effective procedure initialized source-blind from $D$
and common source-independent installed tables. It receives no later
request, terminates on every $t\in\mathcal F_D$, and acquires source
dependence only through charged original-root literal Reads. It exports
a finite code $E(t)$ containing every accessible surviving source
distinction, including selectors, control, operands, buffers, lengths,
allocation, handles, counters and accessible timing. Every other accessible
field is a function of this code and public data. A separately paid handoff
and access-isolation service removes access to all other preparation
dependence, including transcripts, and supplies lawful common reader entry.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. A common deterministic effective reader uses $E(t),D,p$ and the
installed tables. It chooses zero Reads or one fresh Read of the same
stationary $t$ at any finite original-root word, before receiving its reply
or any authentic count. Its final predictor $Z$ must satisfy

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0)
\tag{JPL.2}
$$

for every authentic subsequently supplied count, without further Reads.
There is no subtree, equality, source-identity, age, copying, reset,
free-navigation or advice port. Define $M_1(D)$ as the minimum complete
attained cardinality $|E[\mathcal F_D]|$. Preparation Reads, work/control,
temporary storage, installed codebooks, post-request workspace, final
predictor size, submitted literal length and letters, count representation,
authentication, handoff, isolation, entry and physical time are separate
resources. The declared services are assumptions, not inferred physical
operations. This is the interface of [FMR, Assumption 1.3][FMR] and
[NPC, Assumption 1.2][NPC].

**Convention 1.3 (credited temporal factors and canonical trees).** Use
the exact all-count factor $\Gamma_q$ supplied by [AAR, §§12–13][AAR].
For $s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$, its value
is $(0,0)$ at an original branch endpoint. Otherwise let the first
original blocking leaf have label $\ell$ at $a$, with $q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{JPL.3}
$$

On attained factors $(b,c)$ the credited decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{JPL.4}
$$

It equals $r_{\rho^ku}(q)$ for every $k$. Conversely the trajectory
recovers $b$ as its first branch count and $c$ by its alpha stage.
Factors therefore classify complete trajectories, including initially
absent targets, rather than necessarily identifying blocking positions.

Set $C_0=\langle\alpha,\alpha\rangle$ and

$$
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup
                  \{\langle x,y\rangle:x,y\in S_d\}.
\tag{JPL.5}
$$

The FMR completion $\pi_d(v)$ preserves the $W_d$ replies and factors,
fixes $S_d$, and replaces a branch at depth $d-1$ by $C_0$. On $S_d$
a length-$d$ literal is a function of its length-$(d-1)$ parent reply:
alpha if that reply is branch, absent otherwise. Longer literals are
absent. Thus every finite literal reduces to a function of one $W_d$
reply in its original queried block, or to a constant. [FMR, Lemma 2.2
and Theorems 2.3–2.5][FMR] supply this whole-encoder normalization and
its paid realization; it is not an assumption that a competing fiber
factors or has admissible child projections.

**Definition 1.4 (all native joint competitors).** A nonempty
$B\subseteq S_d^n$ is admissible if every $(i,q)\in[n]\times W_d$
has a constant factor on $B$, or has a donor $j$, a literal $a\in W_d$
and a total reply decoder $\delta$ such that

$$
\Gamma_q(x_i)=\delta(r_{x_j}(a))\qquad(x\in B).
\tag{JPL.6}
$$

The donor and decoder can depend on $B,i,q$. Self donors, off-target
queries, cycles and arbitrary correlations are all allowed. Arbitrary
finite donor words give the same class by Convention 1.3. A complete
template selects one such equation for every target; $C_\Theta$ is
its full simultaneous solution set, possibly empty.

For a nonnegative weight $w:S_d\to[0,\infty)$ put

$$
A_n^{(d)}(w)=\max_{B\text{ admissible in }S_d^n}
                    \sum_{x\in B}\prod_{i=1}^n w(x_i),
\qquad
\beta_d(w)=\sup_{n\ge1}A_n^{(d)}(w)^{1/n},\qquad A_0^{(d)}=1.
\tag{JPL.7}
$$

[NDR, Theorem 2.2][NDR] permits the same maxima over complete
templates: every admissible relation is contained in a full solution set
on the same coordinates. Nonnegative weights, including zero weights,
are essential in this containment statement. No competitor is removed.

**Convention 1.5 (credited rates and the unresolved effective premise).**
Let $K_d(n)$ be the minimum admissible cover size of $S_d^n$. Reuse
[FMR, Theorems 3.3 and 6.3–6.4][FMR] and [NPC, Theorems 5.3, 6.1–6.2
and 7.1][NPC]:

$$
\begin{aligned}
\sigma_d&=\inf_{n\ge1}n^{-1}\log_2K_d(n),\qquad
\lambda=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
       =\sup_{d\ge1}2^{-d}\sigma_d,\\
2^{-\sigma_d}&=\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\\
|\beta_d(\mu)-\beta_d(\nu)|
&\le\operatorname{TV}(\mu,\nu),\qquad
\operatorname{TV}(\mu,\nu)=\tfrac12\sum_x|\mu(x)-\nu(x)|,\\
\beta_d(w+e)&\le\beta_d(w)+\sum_xe(x)
                      \quad(w,e\ge0).
\end{aligned}
\tag{JPL.8}
$$

A cap $\beta_d(\mu)\le C$ for a probability gives, against every
original preparation and reader,

$$
M_1(D)\ge\left\lceil C^{-2^{D-d}}\right\rceil\quad(D\ge d),
\qquad \lambda\ge-2^{-d}\log_2C.
\tag{JPL.9}
$$

NPC's semantic minimizing distribution is not an effective verifier.
The still-required optimizer-cofinality is: for every $d$ and rational
$\epsilon>0$, a total sound verifier accepts some rational $(\mu,C)$
with $-\log_2C>\sigma_d-\epsilon$. An accepted cap must bound every
length and complete arbitrary-donor template with the full joint weight.

## 2. Credited motif and actual scaffold correspondence

**Definition 2.1 (the motif and its core).** Keep the actual trees of
[NCM, Proposition 6.1][NCM] and [SRP, Definition 3.1][SRP]:

$$
\begin{aligned}
A&=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad J=\langle B,A\rangle,\quad Q=\langle C,A\rangle,\\
(u_0,u_1,u_2,u_3,u_4)
&=(C,J,\langle C,C\rangle,\langle J,J\rangle,\langle A,Q\rangle),\\
P&=\{u_0,u_1,u_2,u_3,u_4\}\subseteq S_3,
\qquad K=\{u_0,u_1,u_2,u_3\}.
\end{aligned}
\tag{JPL.10}
$$

For $f:P\to[0,\infty)$ define

$$
R(f)=\sum_{s=0}^4 f(u_s)-\min_{0\le s<4}f(u_s).
\tag{JPL.11}
$$

[SRP, Theorems 1.2 and 3.2][SRP] supply the following facts. The only
residual target on $P$ is $LL$; every other target has its own witness.
A subset is locally admissible precisely when it omits a core state.
For arbitrary $n$ and arbitrary nonnegative weights $f_i$ on $P$,
the maximum mass over all admissible subsets of $P^n$ is
$\prod_i R(f_i)$. This includes cyclic and off-coordinate witnesses.
The motif, this inhomogeneous theorem and the motif fractional cover
$(4/3)^n$ are credited suppliers.

The particular core data needed below are

$$
\begin{array}{c|cccc}
 &u_0&u_1&u_2&u_3\\\hline
r_\varepsilon&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
r_L&\alpha&\beta&\mathsf{branch}&\mathsf{branch}\\
r_R&\alpha&\alpha&\mathsf{branch}&\mathsf{branch}\\
r_{LL}&\mathsf{absent}&\mathsf{absent}&\alpha&\beta\\
r_{LR}&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha\\
r_{RL}&\mathsf{absent}&\mathsf{absent}&\alpha&\beta\\
r_{RR}&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha\\\hline
\Gamma_{LL}&(3,0)&(2,0)&(2,1)&(1,0).
\end{array}
\tag{JPL.12}
$$

All longer literals on this core are absent. Every literal thus has
at most three replies on $K$, whereas its $LL$ factor has four values.
If $u_0$ or $u_1$ is omitted, $RL$ determines $LL$; if $u_2$ or $u_3$
is omitted, $L$ determines it. The other targets
$\varepsilon,L,R,LR,RL,RR$ use respectively a constant and the literals
$L,R,L,RL,R$. These are the NCM/SRP witness tables, not new motifs.

**Definition 2.2 (one fixed actual scaffold).** For $h\ge0$ put
$k=2^h$. Define $T_0(x)=x$ and

$$
T_{h+1}(x_1,\ldots,x_{2k})
=\langle T_h(x_1,\ldots,x_k),T_h(x_{k+1},\ldots,x_{2k})\rangle.
\tag{JPL.13}
$$

Its $k$ public frontier addresses $a_1,\ldots,a_k$ all have length
$h$. Its modules are actual present occurrences. Define

$$
U_h=T_h(K^k)\subseteq S_{h+3},\qquad
L_c=T_h\left(\prod_{j=1}^k(K\setminus\{u_{c_j}\})\right)
\quad(c\in\{0,1,2,3\}^k).
\tag{JPL.14}
$$

The scaffold and its word-prefix transport are the suppliers of
[FMR, §6][FMR] and [JTC, Theorem 4.2][JTC]. In particular, for any
$\nu$ on $S_d$, its product lift $\nu^\uparrow$ on $S_{d+r}$,
supported on $T_r(S_d^{2^r})$, has
$\beta_{d+r}(\nu^\uparrow)=\beta_d(\nu)^{2^r}$.

**Lemma 2.3 (same-realization translation at the fixed cut).** The map
from $n$ coarse scaffold trees in $T_h(S_3^k)$ to their $kn$ ordered
actual modules is a bijection onto $S_3^{kn}$. Under this map an
admissible coarse relation gives an admissible fine relation, and an
admissible fine relation gives an admissible coarse relation. This also
holds on any restricted module support; the relation and its correlations
are not replaced by their projections. Every selected single donor
translates to one single donor or a constant.

Proof. The inverse groups consecutive $k$ actual modules and applies
the fixed ordered constructor $T_h$. A coarse target $q\in W_{h+3}$
with $|q|<h$ ends at a scaffold branch, so has constant factor $(0,0)$.
Otherwise it uniquely has the form $a_jb$ with $b\in W_3$, and its
factor equals $\Gamma_b$ in module $j$. Conversely every fine target
has this coarse representative. These equalities hold for every row
and every authentic count by homomorphic substitution at present
occurrences.

A coarse donor word either ends above the cut, giving a constant
branch reply, or enters one unique actual module. The latter reply is
that module's literal reply. If its suffix is outside $W_3$, Convention
1.3 reduces it to a function of one boundary reply in the same module
or to a constant; compose this function with its decoder. Conversely
a fine donor is implemented by prefixing its literal with its own
public module address in the selected coarse coordinate. Constants,
self donors and cycles retain their values on the same rows. These
translations give witness equations in both directions. They assert
no independent realization of repeated module values. $\square$

## 3. Exact pressure for arbitrary joint weights on the core scaffolds

**Theorem 3.1 (lossless completion on $U_h$).** For every $h\ge0$,
$n\ge1$ and nonempty admissible $B\subseteq U_h^n$, there exist
$c_1,\ldots,c_n\in\{0,1,2,3\}^k$ such that

$$
B\subseteq\prod_{i=1}^n L_{c_i}.
\tag{JPL.15}
$$

Every $L_c$ is locally admissible. Neither $B$ nor a weight on a
coarse block is assumed to factor across modules.

Proof. Every finite literal on a member of $U_h$ either stops above
the fixed frontier and is constant, or enters one actual $K$ module.
By (JPL.12) its range on all of $U_h$ has at most three replies.

Fix a coarse coordinate $i$ and one of its modules $j$. Suppose that
its projection over $B$ contains all four core states. The permitted
coarse target $a_jLL$ then has all four distinct factors in (JPL.12).
An admissibility witness would be a constant or the decoding of one
literal on some coarse coordinate of the same $B$. A constant cannot
produce four values; every such donor literal has at most three
attained replies because that coordinate lies in $U_h$. A function of
these replies also has at most three values. This contradiction
applies to every donor location, including self donors and donors in
cycles.

Consequently each module projection omits at least one core state.
Choose one missing index $c_{ij}$. Every row then belongs to
$\prod_iL_{c_i}$, proving the containment. This argument selected
missing values after restricting the same relation; it did not assert
that its projections are independently attainable fibers.

In $L_c$, each module lies in a proper subset of $K$. Its own witnesses
in (JPL.12) serve every fine target. Prefix each witness by that
module's fixed address; targets above the frontier are constants.
Lemma 2.3 therefore makes $L_c$ locally admissible. Products of these
local sets are admissible too. $\square$

**Definition 3.2 (whole-block box functional).** For a nonnegative
weight $w$ on the entire $S_{h+3}$ supported in $U_h$, let

$$
\mathcal R_h(w)=\max_{c\in\{0,1,2,3\}^k}
                           \sum_{x\in L_c}w(x).
\tag{JPL.16}
$$

This is a finite maximum of sums of the original coarse-block weight.
There is no factorization requirement on $w$.

**Theorem 3.3 (exact inhomogeneous whole-joint-weight pressure).** Let
$h\ge0$, $d=h+3$, $n\ge1$, and let $w_i:S_d\to[0,\infty)$ be
arbitrary nonnegative weights supported in $U_h$. Then

$$
\max_{B\text{ admissible in }S_d^n}
          \sum_{x\in B}\prod_{i=1}^n w_i(x_i)
=\prod_{i=1}^n\mathcal R_h(w_i).
\tag{JPL.17}
$$

The same maximum over complete templates has this value. In particular,
for every such $w$ and every $n\ge1$,

$$
A_n^{(d)}(w)=\mathcal R_h(w)^n,
\qquad \beta_d(w)=\mathcal R_h(w).
\tag{JPL.18}
$$

Proof. For any competitor, discard its zero-product-weight rows.
This does not change its mass, and a nonempty remainder is admissible
with its original witnesses. It lies in $U_h^n$, so Theorem 3.1 puts
it in a product of boxes $\prod_i L_{c_i}$. By nonnegativity its mass
is at most

$$
\sum_{x\in\prod_iL_{c_i}}\prod_iw_i(x_i)
=\prod_i\sum_{u\in L_{c_i}}w_i(u)
\le\prod_i\mathcal R_h(w_i).
$$

Only weights on distinct coarse coordinates have been multiplied;
each $w_i$ remains a single function of all its modules and is counted
once. If there are no positive rows, the upper inequality holds with
zero left side.

Choose a maximizing box for each $w_i$. Their product is admissible
by Theorem 3.1 and has exactly the displayed product mass. This also
works when a weight is identically zero. Thus both inequalities hold.
Saturation from Definition 1.4 gives the complete-template equality;
its larger solution set cannot exceed the proved universal upper.
Taking identical weights and then the all-length supremum proves
(JPL.18). $\square$

**Proposition 3.4 (a nonfactor whole-block example).** At $h=1,d=4$,
give $\langle u_s,u_t\rangle$, $0\le s,t<4$, the weight
$1+\mathbf1_{s=t}$, and set every other weight to zero. Its total is
$20$ and $\mathcal R_1(w)=12$. Hence

$$
A_n^{(4)}(w)=12^n,\qquad \beta_4(w/20)=3/5.
\tag{JPL.19}
$$

Proof. A box excludes one row index $c$ and one column index $e$.
It has nine entries and contains three diagonal entries if $c=e$,
two otherwise. Its mass is therefore $12$ or $11$; among the sixteen
boxes there are four of the first kind and twelve of the second.
The $\{0,1\}\times\{0,1\}$ minor of the weight table has determinant
$2\cdot2-1\cdot1=3$, so the table is not a product of two nonnegative
module functions. Apply Theorem 3.3, which does not require that
factorization. $\square$

The donor-range premise is support-specific. In particular NCM's full
five-state motif has a four-reply $RL$ donor and its cyclic relation
has locally inadmissible coordinate projections. Theorem 3.1 is not a
projection theorem for arbitrary native supports or for donors outside
$U_h$. All original competitors in Theorem 3.3 were retained before
the zero-weight restriction.

## 4. A sharp optimizer ceiling for the restricted core atlas

**Theorem 4.1 (optimization over all correlated core weights).** For
every $h\ge0$, with $k=2^h$ and $d=h+3$,

$$
\min_{\substack{\mu\in\Delta(S_d)\\\mu(U_h)=1}}
                   \beta_d(\mu)=(3/4)^k.
\tag{JPL.20}
$$

The uniform probability on $U_h$ attains this minimum. Thus the
largest normalized lower endpoint from any whole-block probability
on any of these supports is exactly

$$
L_{\mathrm{core}}=\frac18\log_2(4/3).
\tag{JPL.21}
$$

Proof. A fixed state $T_h(u_{s_1},\ldots,u_{s_k})$ belongs to exactly
$3^k$ of the $4^k$ boxes $L_c$: in each position the excluded index
may be any of the three other labels. Therefore, for every probability
$\mu$ on $U_h$,

$$
4^{-k}\sum_c\mu(L_c)=(3/4)^k.
$$

Its maximum box mass is at least this average. Theorem 3.3 identifies
that maximum with $\beta_d(\mu)$. Under the uniform probability,
each box has exactly $3^k$ of the $4^k$ states, so every box mass is
$(3/4)^k$. This proves the minimum, including probabilities with zero
coordinates. Finally $2^d=8k$, and
$-2^{-d}\log_2(3/4)^k=\log_2(4/3)/8$. $\square$

**Definition 4.2 (the precise restricted verifier $V_{\mathrm{core}}$).**
A certificate is a finite topologically ordered list of labels
$(d,\mu,C)$, where $\mu$ is a rational probability on the entire
$S_d$ and $C>0$ is rational. Its last label equals its input. A node
has one of the following justifications:

1. A core leaf: $d=h+3$ for some $h\ge0$, $\mu(U_h)=1$, and
   $C\ge\mathcal R_h(\mu)$, checked using all $4^{2^h}$ boxes.
2. A scaffold node referring to an earlier $(d_0,\nu,C_0)$: for
   some $r\ge0$, $d=d_0+r$, $\mu=\nu^\uparrow$ as a full-table
   equality, and $C\ge C_0^{2^r}$.
3. A stability node referring to an earlier $(d,\nu,C_0)$:
   $C\ge C_0+\operatorname{TV}(\mu,\nu)$.

Malformed tables, nonprobabilities and failed comparisons are rejected.
This grammar retains the exact JTC scaffold and probability-stability
rules. Its leaves are precisely the restricted atlas just defined; it
is not the full $V_{\mathrm{rec}}$ of [JTC, Definition 9.1][JTC].

**Theorem 4.3 (soundness and a sharp ceiling after scaffold and stability).**
The predicate $V_{\mathrm{core}}$ is total computable and sound for
every native length and complete template. Every accepted label satisfies

$$
-2^{-d}\log_2C\le L_{\mathrm{core}}.
\tag{JPL.22}
$$

The ceiling is attained at every leaf depth. Even exact joint-weight
optimization over this atlas, followed by arbitrary finite uses of these
two closure rules, is not optimizer-cofinal for the original problem.
Its best original-rate endpoint is more than $1/10$ below the credited
original lower bound.

Proof. All checks involve finite tree tables and rational arithmetic,
so they terminate. Induction over the node list proves soundness:
Theorem 3.3 supplies the leaves, credited exact scaffold transport
supplies the scaffold step, and (JPL.8) supplies stability.

At a leaf, Theorem 4.1 forces $C\ge(3/4)^{2^h}$ and proves
(JPL.22). At a scaffold step, monotonicity of the logarithm gives

$$
-2^{-(d_0+r)}\log_2C
\le-2^{-d_0}\log_2C_0.
$$

At a stability step $C\ge C_0$, so the same-depth endpoint cannot
increase. This proves (JPL.22) for every finite derivation, even when
stability has produced full-support probabilities outside the atlas.
Uniform core probabilities with the exact rational caps in (JPL.20)
are accepted leaves and attain the ceiling.

The credited [NCE, Theorems 6.1–6.2][NCE] give
$\sigma_3\ge\log_2(33/13)$ and
$\lambda\ge\log_2(33/13)/8$. At depth three all accepted block
endpoints are at most $\log_2(4/3)$. Their gap below that credited
lower bound for $\sigma_3$ is

$$
\log_2(33/13)-\log_2(4/3)=\log_2(99/52)>1/2,
$$

since $99^2>2\cdot52^2$. Consequently the cofinality test of
Convention 1.5 already fails with $d=3,\epsilon=1/2$. Across all
depths, the original-rate gap is at least
$\log_2(99/52)/8>1/10$, since $99^5>16\cdot52^5$.
These are exact inequalities. $\square$

This theorem exhausts the specified support atlas, rather than merely
one weight search. It does not constrain the other leaves of
$V_{\mathrm{rec}}$; its credited NCE joint leaf is outside this atlas.
No conclusion about unrestricted $V_{\mathrm{rec}}$ optimizer-cofinality
follows from (JPL.22).

## 5. Exact pressure of an owned diagonal block potential

**Definition 5.1 (the diagonal scaffold support).** For $h\ge1$ set
$k=2^h$, $d=h+3$, and

$$
v_s=T_h(u_s,\ldots,u_s),\qquad
\mathcal Q_h=\{v_s:0\le s<5\}\subseteq S_d.
\tag{JPL.23}
$$

For $a=(a_0,\ldots,a_4)\in[0,\infty)^5$ define the whole-block
weight $w_a(v_s)=a_s$ and $w_a=0$ on every other state of $S_d$.
Write $R(a)=\sum_sa_s-\min_{s<4}a_s$ and
$\mu_0=w_{(1,1,1,1,1)}/5$. All $k$ modules in one state $v_s$
are actual occurrences of the same motif value. This is a joint
support condition, not $k$ independent replicas or observations.

**Theorem 5.2 (exact diagonal pullback at every length).** For every
$h\ge1$, every nonnegative $a$, and every $n\ge1$,

$$
A_n^{(d)}(w_a)=R(a)^n,\qquad \beta_d(w_a)=R(a).
\tag{JPL.24}
$$

In particular $\beta_d(\mu_0)=4/5$ simultaneously against every
correlated complete native template at every length.

Proof. Map each motif tuple $(u_{s_1},\ldots,u_{s_n})$ to
$(v_{s_1},\ldots,v_{s_n})$. This is a bijection onto
$\mathcal Q_h^n$. A coarse target above the frontier is a constant
branch. Every other coarse target is a fine target in one actual
module. On this support its factor is exactly the corresponding
factor of $u_{s_i}$, independently of which occurrence is selected.

Every coarse donor literal is constant above the frontier or enters
one actual module in one donor block. Its reply is then that motif
state's literal reply. Because all modules in that block have the
same value, this is one motif experiment in the same donor coordinate,
not the joint observation of a vector. Arbitrarily long suffixes reduce
within that motif block as in Convention 1.3. Thus pulling back a
coarse admissible relation gives a motif-admissible relation, retaining
its selected donor coordinates and decoders after this translation.

Conversely, for any motif-admissible relation, implement a chosen motif
donor in one fixed public module occurrence of its chosen coarse donor
coordinate. Its original suffix is prefixed by that occurrence's
address. The same motif witness serves each repeated fine target;
above-frontier targets are constants. This proves coarse admissibility
of the image, with every constant, self donor, off-target choice and
cycle allowed. Both maps concern the same row tuple with equality of
its repeated modules preserved.

For a coarse competitor of positive mass, first restrict to its
positive rows in $\mathcal Q_h^n$. The bijection preserves exactly
one factor $a_{s_i}$ per coarse block. The credited inhomogeneous
motif theorem of Definition 2.1 therefore bounds the mass by $R(a)^n$.
Products of a largest local motif set attain this mass; their diagonal
images are admissible by the converse direction. Zero weights and a
zero total obey the same two inequalities. Saturation preserves the
maximum over complete templates, and taking all-length roots gives
(JPL.24). $\square$

## 6. A finite separable-majorant language and its exact obstruction

**Definition 6.1 (the language $V_{\mathrm{sep},h}$).** Fix $h\ge1$
and $d=h+3$. A leaf for a rational probability $\mu$ on the entire
$S_d$ supplies finitely many nonnegative rational functions
$f_{\ell j}:P\to\mathbb Q_{\ge0}$, $1\le j\le k$, and an arbitrary
nonnegative rational remainder $e:S_d\to\mathbb Q_{\ge0}$. The number
of separated terms may be any finite integer, including zero. Define

$$
F_\ell(T_h(x_1,\ldots,x_k))=\prod_{j=1}^k f_{\ell j}(x_j)
\quad(x_j\in P),\qquad
F_\ell=0\text{ off }T_h(P^k).
\tag{JPL.25}
$$

Check the full pointwise table and the scalar charge

$$
\mu(x)\le e(x)+\sum_\ell F_\ell(x)\quad(x\in S_d),\qquad
C\ge L:=\sum_\ell\prod_{j=1}^k R(f_{\ell j})+\sum_{x\in S_d}e(x).
\tag{JPL.26}
$$

A certificate is a finite topologically ordered list of such leaves,
same-depth probability-stability steps
$C\ge C_0+\operatorname{TV}(\mu,\nu)$ from earlier $(\nu,C_0)$,
and cap-enlargement steps at unchanged $\mu$. The last label is the
input $(\mu,C)$, with $C>0$. Invalid rational data, omitted pointwise
entries and unsuccessful inequalities are rejected. There are no other
cap premises in this grammar. In particular this proposed replacement
language is distinct from the existing joint/group/scaffold calculus;
it places no assertion on the rules it does not contain.

**Theorem 6.2 (all-length soundness of the separable rule).** The
predicate $V_{\mathrm{sep},h}$ is total computable. Every acceptance
implies $\beta_d(\mu)\le C$ for every complete native template and
every length.

Proof. Put $g=\sum_\ell F_\ell$. Fix an arbitrary admissible
$B\subseteq S_d^n$ and expand $\prod_i g(x_i)$ by a term choice
$\ell_i$ at each coordinate. For a fixed choice, the nonzero rows
are on $T_h(P^k)^n$. Recut those same rows into their $kn$ actual
modules by Lemma 2.3. The resulting relation is motif-admissible,
with all its old equalities and correlations intact. Apply SRP's
inhomogeneous theorem to the fine weights $f_{\ell_i j}$ to get

$$
\sum_{x\in B}\prod_iF_{\ell_i}(x_i)
\le\prod_{i=1}^n\prod_{j=1}^k R(f_{\ell_i j}).
$$

Sum over all term choices. Finite distributivity yields

$$
A_n^{(d)}(g)\le
\left(\sum_\ell\prod_jR(f_{\ell j})\right)^n.
$$

No source-dependent term selector is given to a reader; this is an
analytical sum. Every coarse potential in a term is expanded exactly
once. The table majorization, monotonicity and the credited nonnegative
remainder inequality in (JPL.8) give $\beta_d(\mu)\le L\le C$.
That remainder inequality uses fixed-value sections of the same native
relation; it makes no projection-independence assumption. Probability
stability and cap enlargement preserve soundness, so induction proves
the assertion for an arbitrary finite derivation.

Each input specifies finite lists on finite tree alphabets. All
enumerations and rational comparisons terminate; malformed inputs
are rejected without consulting any unverified cap. This proves
totality as well as soundness. $\square$

**Lemma 6.3 (a diagonal dual inequality).** For all nonnegative
$f_1,\ldots,f_k$ on $P$, with $k=2^h\ge2$,

$$
\sum_{s=0}^4\prod_{j=1}^k f_j(u_s)
\le\prod_{j=1}^k R(f_j).
\tag{JPL.27}
$$

Proof. First $R(f)\ge\|f\|_2$. To see this, let $m$ be a minimum
core entry, let $a,b,c$ be the other three core entries, and let $t$
be the fifth entry. Then $a,b,c\ge m\ge0$ and
$R(f)=a+b+c+t$, so

$$
R(f)^2-\|f\|_2^2
=2(ab+ac+bc)-m^2+2t(a+b+c)\ge0.
$$

For $k\ge2$, $\|f\|_k\le\|f\|_2$: after scaling the latter to
one, every entry is at most one and its $k$-th power is at most its
square. The zero-vector case is immediate.

The finite power-of-two Hölder inequality gives
$\sum_s\prod_j f_j(u_s)\le\prod_j\|f_j\|_k$.
Here it follows directly by repeated Cauchy–Schwarz: split the $k$
factors into equal halves, apply Cauchy–Schwarz to the two half-products,
and apply the same inequality inductively to their squared factors.
The base case $k=2$ is Cauchy–Schwarz itself. Thus no asymptotic or
factorization assumption is involved. Combine the two norm bounds
with this inequality to obtain (JPL.27). $\square$

**Theorem 6.4 (strict native failure of the stated replacement language).**
Every acceptance $(\mu,C)$ of $V_{\mathrm{sep},h}$ satisfies

$$
C\ge\mu(\mathcal Q_h).
\tag{JPL.28}
$$

For the diagonal uniform law $\mu_0$, the smallest accepted cap is
exactly $1$, whereas the exact native pressure is $4/5$. Thus the
language's best scalar all-length upper envelope exceeds the true
maximum by $(5/4)^n$ at length $n$. A multiplicative correction whose
logarithm is $o(n)$ cannot remove this exponential loss at fixed $h$.

Proof. Sum the pointwise inequalities (JPL.26) on the five actual
states $v_s$. For each separated term, Lemma 6.3 gives

$$
\sum_{s=0}^4F_\ell(v_s)
=\sum_s\prod_jf_{\ell j}(u_s)
\le\prod_j R(f_{\ell j}).
$$

Also $\sum_s e(v_s)\le\sum_xe(x)$. Consequently each leaf has
$\mu(\mathcal Q_h)\le L\le C$, regardless of the number of terms
or the remainder's support. For probabilities on the full alphabet,
$\mu(\mathcal Q_h)\le\nu(\mathcal Q_h)
+\operatorname{TV}(\mu,\nu)$. Hence (JPL.28) survives every
stability step and every cap enlargement. Induction proves it for
all finite derivations.

For $\mu_0$ the right side is one. A cap of one is accepted, for
example by the remainder $e=\mu_0$ with no separated terms. It is
also attained with no remainder: use five diagonal singleton products,
with weight $1/5$ in one module and unit singleton weights in the
others. Each term has charge $1/5$, and their sum is exactly $\mu_0$
on all of $S_d$. Theorem 5.2 gives the true mass $(4/5)^n$, while
the best accepted scalar cap produces $1^n$. Their ratio is
$(5/4)^n$ and has positive logarithmic rate. $\square$

**Corollary 6.5 (a rational strictly positive separation).** At
$h=1,d=4$, let $s=|S_4|=15131$ and let $u$ be uniform on the entire
$S_4$. Put

$$
\mu_+=\frac{99}{100}\mu_0+\frac1{100}u.
\tag{JPL.29}
$$

Every coordinate of $\mu_+$ is strictly positive and

$$
\beta_4(\mu_+)\le\frac{81}{100},\qquad
V_{\mathrm{sep},1}\text{ acceptance implies }
C\ge\frac{99}{100}+\frac1{20s}
 =\frac{748987}{756550}>\frac{99}{100}.
\tag{JPL.30}
$$

Proof. Every coordinate is at least $1/(100s)$. By (JPL.8) and
Theorem 5.2,
$\beta_4(\mu_+)\le4/5+\operatorname{TV}(\mu_+,\mu_0)
\le4/5+1/100=81/100$.
The set $\mathcal Q_1$ has five states, so its $\mu_+$ mass is
$99/100+5/(100s)$. Apply Theorem 6.4 and simplify the exact fraction.
$\square$

## 7. The existing full joint rules handle the diagonal

**Proposition 7.1 (a current joint certificate, with every support checked).**
For every $h\ge1$, [JTC, Corollary 2.3][JTC] accepts
$(d,\mu_0,4/5)$. Its current probability-stability rule therefore
accepts $(4,\mu_+,81/100)$. The diagonal example does not refute
the existing calculus $V_{\mathrm{rec}}$.

Proof. For a support $H\subseteq S_d$, a target is hard when no
own-coordinate reply, including a constant, determines it on $H$.
Let $Y_H$ be the vector of all hard targets. The JTC joint leaf checks
every nonempty range-feasible $H\subseteq\operatorname{supp}(\mu_0)$
and requires

$$
\sum_y\left(\sum_{x\in H:Y_H(x)=y}\mu_0(x)\right)^2
\le(4/5)^2.
\tag{JPL.31}
$$

On $\mathcal Q_h$ every target and literal pulls back to its motif
counterpart or a constant, exactly as in Theorem 5.2. All subsets are
range-feasible, since all motif targets have at most four values.
If a nonempty subset omits a core index, it is locally admissible by
the credited motif classification and this same translation. Its hard
vector is empty, so the left side of (JPL.31) is its total mass
squared, at most $(4/5)^2$.

There are only two other supports. On all five diagonal states, the
hard targets are the $k$ repeated copies of motif $LL$. Their joint
partition has index cells $\{0,4\},\{1\},\{2\},\{3\}$. Its
squared mass is $(2^2+1+1+1)/25=7/25$. On the four core diagonal
states the same repeated hard targets give four singleton cells and
squared mass $4/25$. They remain hard because no literal has the
missing four-way distinguishing power on these sets. Every other
target retains its own witness. Both squared masses are at most
$16/25$, verifying all thirty-one nonempty supports without omitting
smaller supports. Thus the joint leaf accepts.

Finally $\operatorname{TV}(\mu_+,\mu_0)\le1/100$; one existing
stability step from cap $4/5$ accepts cap $81/100$. These are rules
already present in JTC, with no extension or deletion. $\square$

Theorem 4.3 is an optimizer ceiling for $V_{\mathrm{core}}$ only.
Theorem 6.4 is a pointwise gap for $V_{\mathrm{sep},h}$ only; it
does not even assert an optimizer ceiling for that language after
varying its weights and depths. Neither is a counterexample to
unrestricted $V_{\mathrm{rec}}$ optimizer-cofinality. Proposition 7.1
exhibits its concrete bypass of the second obstruction.

## 8. Original competitors, actual read mapping and paid realization

**Corollary 8.1 (consequences against every original complete code).**
For $d=h+3$, $W=\sum_xw(x)>0$, and $w$ supported on $U_h$,

$$
M_1(D)\ge
\left\lceil\left(\frac{W}{\mathcal R_h(w)}\right)^{2^{D-d}}\right\rceil
\quad(D\ge d),\qquad
\lambda\ge2^{-d}\log_2\frac{W}{\mathcal R_h(w)}.
\tag{JPL.32}
$$

For the diagonal law $\mu_0$ the corresponding bound is

$$
M_1(D)\ge\left\lceil(5/4)^{2^{D-d}}\right\rceil
\quad(D\ge d),\qquad
\lambda\ge2^{-d}\log_2(5/4).
\tag{JPL.33}
$$

Proof. Homogeneity and Theorems 3.3 and 5.2 supply the normalized
caps. Apply the credited all-original-competitor transport (JPL.9).
For clarity, that transport restricts an arbitrary original complete
code to an actual perfect right-subtree scaffold of $2^{D-d}$
canonical $S_d$ blocks. It retains the same source, each whole-source
code fiber and every selected late query. A target in a block is
the permitted original request $Ra_iq$. Any original-root query is
an outer constant, a scaffold constant, or a literal in one unique
actual donor block. Convention 1.3 simulates arbitrary long suffixes
in that same donor block. Correctness for all authentic $k$ makes
each restricted fiber admissible, with every off-target or cyclic
witness still allowed.

The analytical law has total mass one on this slice, even if its
one-block coordinates vanish outside the stated support. Each
restricted code fiber has mass at most the cap raised to the number
of actual blocks. Counting the fibers proves (JPL.32) and (JPL.33).
The support is a lower-witness slice, not a restriction on competing
preparations, readers or their complete attained alphabets. $\square$

**Proposition 8.2 (explicit attained full-family fibers).** Let
$d=h+3$. For any core box $L_c$ there is a correct full-family
preparation and reader on $\mathcal F_d$ whose canonical naming
merges exactly $L_c$ and names every other $S_d$ state separately.
Its complete attained alphabet is

$$
|S_d|-3^{2^h}+1.
\tag{JPL.34}
$$

For $h\ge1$ there is likewise a code merging the four diagonal
states $\{v_1,v_2,v_3,v_4\}$ and naming every other canonical state
separately, with complete attained alphabet $|S_d|-3$. In both
constructions, on every actual source,

$$
T_{\rm prep}\le2^d-1,\qquad Q_{\rm prep}\le d,\qquad
A_{\rm prep}\le(d-1)2^d+1.
\tag{JPL.35}
$$

The common late reader makes at most one original-root Read, of
length at most $d$, chosen before any supplied count.

Proof. Before any request, actually submit every $Rq$, $q\in W_d$,
including absent replies. The finite acquired table determines
$\pi_d(v)$. Its first-membership name is the merged name if the
canonical state belongs to the stated set, otherwise that state's
own fixed public name. Export only this fixed-width complete name.
The public scan, allocation and padded finite computation schedule
depend on $d$ alone; the paid isolation service removes every other
source distinction, including the acquired table and membership
workspace. There are $2^d-1$ submitted literals and their lengths
sum to $(d-1)2^d+1$, proving (JPL.35).

A core box has exactly $3^{2^h}$ distinct states. The four diagonal
states are distinct. Every canonical state is an actual right subtree
in $\mathcal F_d$, so all specified names are attained. This proves
the complete cardinalities. The actual merged fibers on variable
shapes are the inverse images under $\pi_d$, not an assertion that
unread terminal labels have been distinguished.

For a singleton canonical name, the tables determine every factor
without a Read. For a core-box name, a permitted target above the
frontier has constant branch factor. Any other target is $Ra_jq$,
$q\in W_3$. Use its proper-core-subset witness from (JPL.12),
implemented at the actual original-root word $Ra_jb$. That length
is at most $1+h+2=d$. These choices require only the name, request
and public tables. Canonicalization preserves the needed replies
and factors on every original source assigned that name.

For the four-state diagonal name, the $RL$ replies on
$(u_1,u_2,u_3,u_4)$ are respectively absent, alpha, beta and branch.
They identify the state on this named fiber. A nonconstant module
target can therefore use $Ra_1RL$ at one fixed actual public module
occurrence, regardless of which module contains the target. Its
length is $d$. The equality of the module values is a proved property
of this fiber, not an equality test or a copied-source port. Targets
above the frontier are constants. The prefix $Ra_1$ is present in
every source in this fiber because $\pi_d$ preserves the scaffold
constructors. Hence all words are actual original-root literals on
the same stationary source.

In either construction the reply decoder produces $\Gamma_p(t)$,
and (JPL.4) then supplies every subsequent authentic $k$ without
Reads. The predictor can use $(b,c)$ with $b\le2d$, requiring at
most $\lceil\log_2(2d+1)\rceil+1$ bits; its size is separate from
the retained alphabet. Installed tables, membership work/control,
temporary storage, post-request workspace, address generation,
authentication and physical services remain separate resources.
$\square$

At $h=1,d=4$ the diagonal construction has exactly $15128$ attained
names, with $15$ preparation Reads, maximum length $4$, and $49$
submitted letters. This is an explicit deliberately nonoptimal code,
not an assertion about $M_1(4)$. Neither (JPL.32) nor (JPL.33)
improves the credited original interval

$$
\frac18\log_2(33/13)\le\lambda<\frac3{16},
\tag{JPL.36}
$$

supplied by [NCE][NCE] and [D3][D3].

## 9. Attribution, transfer boundaries and the remaining bridge

**Convention 9.1 (the exact scope of the deductions).** The core
completion for all correlated whole-block weights, its optimizer
ceiling with closure rules, the diagonal pullback, and the finite
separable-majorant dual obstruction are `repo-derived` ordinary
deductions in this volume. The motif, its constants and witness
tables, its all-weight residual pressure, canonicalization, native
rate transport and fixed-scaffold product identity are credited
suppliers. The elementary norm and Cauchy–Schwarz steps are mature
finite inequalities. No worldwide-priority claim is made.

[CBN, Theorems 2.2, 4.2 and 6.2][CBN] give exact actual constructor
coordinates and native unary/binary compilation with each original
whole-block potential owned once. Their representation does not
assert that the potential factors. The present recuts keep the same
actual modules and all equalities; Theorem 5.2 in particular retains
the diagonal constraint. These results do not recut arbitrary shapes
for free or forget a shared-reference condition. A newly accessible
source-dependent cut, selector or topology would be additional retained
information unless already determined by the complete code.

The finite-natural-join declaration
[`join_covers`][D5J] assumes that both input relations cover the same
full assignment. It gives no automatic existence of such an assignment
or all-size mass estimate. The declarations
[`finite_root_minimax`][D5M] and
[`effective_native_birth_provenance` / `returned_native_reader`][D5E]
concern complete predecessor-row recovery after actual substitution.
The latter requires a prefix-free cut, a complete row with nonempty
`OriginFiber`, $r\ge1$, and compatible acquired image values; its run
source is $\rho(u)$. The minimax chart has its attained three-reply
class-root menu. None is used as an all-length cap verifier here.
Reading those declarations and their Blueprints supplies no new Lean
verification of this volume.

**Convention 9.2 (source-verified primary comparisons).** The following
primary results have their own representation and hypothesis requirements.
No native equivalence satisfying both mass directions and the original
operational resource conditions is assumed for any row.

| Primary source | Exact result and boundary |
| --- | --- |
| Gogacz–Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, Theorem 1 and Corollary 1, [arXiv:1512.01808v1][GT] | A fixed query schema has an almost-entropic characterization and a submodular outer bound. A native witness gives a functional dependence under one common law, but varying native lengths, maps and owned weights do not become a fixed-schema cofinality theorem. |
| Ruozzi, *The Bethe Partition Function of Log-supermodular Graphical Models*, Theorem 4.1, [arXiv:1202.6035v2][R] | Graph-cover domination assumes a binary log-supermodular factorization. Arbitrary native joint weights have no such premise. The current [GCB][GCB] native graph-cover and Bethe boundaries are separate credited results. |
| de Boer–Buys–Zuiddam, *The asymptotic spectrum distance, graph limits, and the Shannon capacity*, Theorem 3.7, [arXiv:2404.16763v2][DBZ] | Fraction graphs approached from above converge uniformly over the specified spectrum. No cardinality-preserving native fraction-graph identification or effective approximation in that distance is established here. |
| Sarantis–Tetali–Zheng, *On Counting Independent Sets in Regular Hypergraphs*, Theorems 1.4–1.5, [arXiv:2609.17468v1][STZ] | The first bound assumes uniform regular hypergraphs with no cross-edges; the second assumes vanishing relative maximum codegree of the twin quotient along growing degree. Arbitrary native donor networks with whole-block weights have neither a proved reduction nor these hypotheses as a general premise. |

These comparisons give no imported effective all-instance cap. The
proofs above instead use explicit native tables, same-realization
maps and finite inequalities. The source references distinguish
verified statements from unproved transfer bridges; inaccessible or
unmatched literature would not establish originality.

**Open problem 9.3 (the unchanged global obligation).** Construct a total
sound verifier whose accepted rational caps are optimizer-cofinal in
every original $\sigma_d$, or prove a uniform effective length-error
bound yielding two-sided approximation of the same $\lambda$. Neither
the exact core atlas nor the separated-majorant grammar supplies that
bridge. The former has the quantified optimizer ceiling of Theorem
4.3. The latter loses the coupled diagonal information, while the full
joint rule already preserves it. Extending beyond these languages
requires a proof of all-template coverage of optimizing weights, not
only pointwise soundness or another fixed-size exact computation.

No noncomputability, universal recut obstruction, or failure of
unrestricted $V_{\mathrm{rec}}$ optimizer-cofinality follows. The
general exact $M_1(D)$, sharp $\lambda$, effective lower convergence,
and the broader minimal-relations and mutual-recovery programme remain
open. The operational recovery established under the paid service
premises stays

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
$$

The reverse map recovers the first branch count and alpha-stage flag.
It does not identify an unknown age, recover the entire hidden source,
or derive a physical space-time realization or authentication service.

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[JTC]: https://github.com/the-omega-institute/trureturing/blob/a8ded6741d47ed07ae4eabe95b27547e73a8407d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[SRP]: https://github.com/the-omega-institute/trureturing/blob/a8ded6741d47ed07ae4eabe95b27547e73a8407d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: https://github.com/the-omega-institute/trureturing/blob/a8ded6741d47ed07ae4eabe95b27547e73a8407d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[D5J]: ../../../D5/S0/Certificates/FiniteNaturalJoin.lean
[D5M]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean
[D5E]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[GT]: https://arxiv.org/html/1512.01808v1
[R]: https://arxiv.org/html/1202.6035v2
[DBZ]: https://arxiv.org/html/2404.16763v2
[STZ]: https://arxiv.org/html/2609.17468v1

## 追加锚（本行以下为增补区）
