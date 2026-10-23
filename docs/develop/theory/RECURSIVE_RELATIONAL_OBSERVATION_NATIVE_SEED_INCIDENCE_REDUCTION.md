# Recursive relational observation: native seed-incidence reduction

## 1. Native task and credited mathematical interfaces

**Definition 1.1 (one stationary original source).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,
\qquad \operatorname{ht}(\langle u,v\rangle)
=1+\max\{\operatorname{ht}(u),\operatorname{ht}(v)\}.
$$

Pairing is free and ordered. Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(a)$
is the addressed constructor, or absent when traversal passes a leaf,
in the alphabet

$$
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}.
$$

The homomorphic substitution and the original source and request families are

$$
\begin{aligned}
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle,\\
\mathcal F_D&=\{\langle\alpha,v\rangle:\operatorname{ht}(v)\le D\},&
W_D&=\{q:|q|\le D-1\},&\mathcal P_D&=\{Rq:q\in W_D\},
\end{aligned}
\tag{SIR.1}
$$

where $D\ge1$ is public. The one actual initial source remains
stationary throughout preparation and late acquisition; $\rho^kt$
specifies the prediction target. There is no subtree, equality,
source-identity, age, reset, copying, navigation or advice port.

**Assumption 1.2 (complete paid export and late timing).** One
deterministic effective preparation starts source-blind from $D$ and
common source-independent tables, receives no later request, and
terminates on every $t\in\mathcal F_D$. It acquires every source
distinction by charged original-root literal Reads. Its finite export
$E(t)$ includes every accessible surviving source distinction:
selectors, control, operands, buffers, lengths, allocation, handles,
counters and accessible timing. Every other accessible field is a
function of this complete code and public data. A separately paid
handoff and access-isolation service makes all other preparation
material, including transcripts, inaccessible and supplies lawful
reader entry. Continuity, isolation, entry and authentication are
declared service premises.

Only after export does a public source-independent $p\in\mathcal P_D$
arrive. A common deterministic effective reader uses $E(t),D,p$ and
installed tables to choose zero Reads or one fresh Read of the same
stationary $t$, at any finite original-root word. This choice precedes
the reply and every supplied count. Its final predictor $Z$ must obey

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,\ p\in\mathcal P_D,
\text{ and subsequently supplied authentic }k\ge0,
\tag{SIR.2}
$$

without further Reads. Let $M_1(D)$ be the minimum complete attained
cardinality $|E[\mathcal F_D]|$. Preparation Reads, work, control and
temporary storage, table generation and installation, post-request
workspace, final predictor size, submitted literal lengths and letters,
count representation, handoff, isolation, authentication, entry and
physical time are separate resources. This is the unchanged task of
[FMR, Assumption 1.3][FMR] and [NPC, Assumption 1.2][NPC].

**Definition 1.3 (credited factors and actual canonical blocks).** Use
[AAR, Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR]. Put
$s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$.
At an original branch endpoint $\Gamma_q(u)=(0,0)$. Otherwise the
first original leaf along $q$ has label $\ell$ at $a$, with $q=ar$,
and

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{SIR.3}
$$

On attained factors the credited decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{SIR.4}
$$

It equals $r_{\rho^ku}(q)$ for every $k\ge0$. Here $c=1$ implies
$b\ge2$. The whole trajectory recovers $b$ as its first branch
count and $c$ by the occurrence of an alpha stage. Initially absent
targets remain included. Write $h(z)=\operatorname{Pred}(z,0)$.

Set

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle x,y\rangle:x,y\in S_d\}.
\tag{SIR.5}
$$

For $\operatorname{ht}(v)\le d$, the credited completion $\pi_d(v)$
retains the constructors on $W_d$ and replaces a branch at depth
$d-1$ by $C_0$. It fixes $S_d$ and preserves all these replies
and factors. On $S_d$, a length-$d$ reply is alpha if its parent
is branch and absent otherwise; longer words are absent. Thus every
finite canonical probe is a function of one boundary reply in its
original queried block, or a constant. These are [FMR, Lemma 2.2
and Theorems 2.3–2.5][FMR]. The factor vector on $W_d$ uniquely
determines a member of $S_d$, as in [CBN, Theorem 2.2][CBN] and
[RRN, Lemma 2.4][RRN].

**Definition 1.4 (complete competitors and their original pressure).**
For $d,n\ge1$, let $V=[n]\times W_d$, $m_d=2^d-1$ and
$G_q=\Gamma_q[S_d]$. A complete native template chooses at every
$v=(i,q)\in V$ a full-factor constant in $G_q$, or an equation

$$
\Gamma_q(x_i)=\delta_v(r_{x_j}(a)),\qquad
(j,a)\in V,\quad \delta_v:\mathcal A\longrightarrow G_q.
\tag{SIR.6}
$$

Its simultaneous solution set is $C_\Theta\subseteq S_d^n$.
Self donors, off-target queries, cycles and all correlations are
allowed. A nonempty relation is admissible when such witnesses
hold on it for every target. [NDR, Theorem 2.2][NDR] embeds every
admissible relation in a complete solution set on the same coordinates.
It preserves integral and fractional cover optima and nonnegative mass
maxima. Denote those cover optima by $K_d(n),Z_d(n)$.

For arbitrary nonnegative whole-block weights $w_i:S_d\to[0,\infty)$
write

$$
\begin{aligned}
A_n^{(d)}(w_1,\ldots,w_n)
 &=\max_\Theta\sum_{x\in C_\Theta}\prod_{i=1}^n w_i(x_i),\\
\beta_d(w)&=\sup_{n\ge1}
 A_n^{(d)}(w,\ldots,w)^{1/n}.
\end{aligned}
\tag{SIR.7}
$$

The analytical product across original blocks imposes no independence
on a competing relation. Each $w_i$ is an arbitrary joint function
of its whole actual block, including all its constructor coordinates.

**Definition 1.5 (credited rates and original-task consumer).** Use
[FMR, Theorems 3.3 and 6.3–6.4][FMR] and [NPC, Theorems 5.3,
6.2 and 7.1][NPC]:

$$
\begin{aligned}
\sigma_d&=\lim_{n\to\infty}\frac{\log_2 K_d(n)}n
 =\inf_{n\ge1}\frac{\log_2 K_d(n)}n,\\
b_d&=2^{-\sigma_d}=\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
 =\sup_{d\ge1}2^{-d}\sigma_d,\\
0&\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,\qquad 0\le\phi\le1,
\end{aligned}
\tag{SIR.8}
$$

where $U_0=1$, $U_{j+1}=1+U_j^2$ and
$\phi=\lim_j2^{-j}\log_2U_j$. A probability cap
$\beta_d(\mu)\le C$, with $C>0$, gives

$$
|E[\mathcal F_D]|\ge\left\lceil C^{-2^{D-d}}\right\rceil
\quad(D\ge d),\qquad
\lambda\ge-2^{-d}\log_2 C
\tag{SIR.9}
$$

against every original preparation and reader. All logarithms are base two.

## 2. Once-owned seed incidence

**Definition 2.1 (the exact owned-seed carrier).** Use exactly
[RRN, Definition 5.1][RRN]. A network $\mathcal N$ has a finite seed
set $J$, domains $T_c\subseteq\mathcal A$, and distinct actual
owner ports $o_c\in V$. A port $v=(i,q)$ is prescribed either a
constant $z_v=\zeta_v\in G_q$ or a value
$z_v=B_v(s_c)$ from one seed, with $B_v:T_c\to G_q$.
The owner $o_c$ is assigned to $c$ and satisfies

$$
h(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{SIR.10}
$$

Repeated occurrences use the same variable. With
$\mathcal S=\prod_{c\in J}T_c$, define

$$
\begin{aligned}
\mathcal X_i(s)&=\{u\in S_d:
          \Gamma_q(u)=z_{(i,q)}(s)\ \text{for all }q\in W_d\},\\
\mathcal S_{\rm real}&=\{s\in\mathcal S:
                         \mathcal X_i(s)\ne\varnothing\ \text{for all }i\},\\
\Phi_i(s)&=\sum_{u\in S_d}w_i(u)
              \prod_{q\in W_d}\mathbf1_{\{\Gamma_q(u)=z_{(i,q)}(s)\}},\\
Z(\mathcal N;w_1,\ldots,w_n)&=\sum_{s\in\mathcal S}\prod_i\Phi_i(s).
\end{aligned}
\tag{SIR.11}
$$

Every $\mathcal X_i(s)$ is empty or a singleton. Let
$C_{\mathcal N}$ be the reconstructed actual tuples for
$s\in\mathcal S_{\rm real}$. Each original $w_i$ occurs once,
in $\Phi_i$. Incompatible seed assignments have zero contribution;
they are never declared jointly realizable.

[RRN, Theorems 4.2 and 5.2][RRN] give both correspondences:
every complete template has exactly the solution set of such a
network, and every such network translates back to a complete
native template on the same $n$ blocks. Actual owner replies
recover the seeds, so both correspondences count each tuple once
and preserve (SIR.7). Domains may be empty, singleton or have four
members. With no seeds, the empty assignment contributes one
constant tuple or none. Analytical seed variables are not acquired
or exported readings.

**Definition 2.2 (incidence and the auxiliary restricted family).** Put

$$
\nu_{\mathcal N}(c)=
 |\{i:\text{at least one port }(i,q)\text{ is assigned to }c\}|.
\tag{SIR.12}
$$

This is prescribed incidence in original blocks. Several occurrences
in one block count once, even for a constant table or a zero potential.
For an integer $L\ge1$, let $\mathfrak N_{d,L}(n)$ be all networks
of Definition 2.1 with $\nu_{\mathcal N}(c)\le L$ for every seed.
All actual-tree compatibility conditions, guards, full block weights,
network lengths, components and correlations remain allowed.

Write $A_{d,L,n}(w_1,\ldots,w_n)$ for the maximum of (SIR.11)
over this class and

$$
\beta_{d,L}(w)=\sup_{n\ge1}A_{d,L,n}(w,\ldots,w)^{1/n}.
\tag{SIR.13}
$$

Let $K_{d,L}(n),Z_{d,L}(n)$ be integral and fractional covers of
$S_d^n$ by its nonempty full solution sets. A solution set belongs
to this family if it has at least one such witness; no assertion
is made about all its possible witnesses. These are auxiliary
quantities, while $\sigma_d,\lambda,M_1(D)$ retain Definition 1.5.

At fixed $d,n$, these maxima and cover optima exist. Distinct owners
give at most $nm_d$ seeds. Up to seed renaming there are finitely
many domain, owner and table choices. Every singleton tuple is a
constant network with no seeds, so the covers are feasible.

## 3. Exact sections at actual owner replies

**Theorem 3.1 (same-coordinate native section identity).** Fix a network
$\mathcal N$ and any $H\subseteq J$. For
$a\in\prod_{c\in H}T_c$, replace every prescription
$B_v(s_c)$ with $c\in H$ by the full-factor constant $B_v(a_c)$,
and delete those seeds and their owner designations. Keep every
other prescription, owner, domain and actual block unchanged.
Denote the resulting network by $\mathcal N_a$. Then

$$
C_{\mathcal N_a}
=\{x\in C_{\mathcal N}:r_{x_{i_c}}(q_c)=a_c\ (c\in H)\},
\qquad o_c=(i_c,q_c),
\tag{SIR.14}
$$

and these full solution sets form a disjoint partition of
$C_{\mathcal N}$. For every nonnegative tuple weight
$W:S_d^n\to[0,\infty)$,

$$
\sum_{x\in C_{\mathcal N}}W(x)
=\sum_{a\in\prod_{c\in H}T_c}\sum_{x\in C_{\mathcal N_a}}W(x).
\tag{SIR.15}
$$

In particular, for all the arbitrary once-owned $w_i$,

$$
Z(\mathcal N;w_1,\ldots,w_n)
=\sum_a Z(\mathcal N_a;w_1,\ldots,w_n).
\tag{SIR.16}
$$

Proof. Every substituted constant belongs to its original $G_q$.
Remaining owners stay distinct and remain assigned to their own
seeds, with (SIR.10) unchanged. Thus each branch is a network of
Definition 2.1, not merely a projected constraint relation.

If $x$ solves the original network, its unique seed vector consists
of its actual owner replies. Fixing its coordinates in $H$ gives
exactly the substituted prescriptions and the same actual compatible
blocks. This proves one inclusion in (SIR.14). Conversely a solution
of the substituted network has, at the former owner of $c\in H$,
factor $B_{o_c}(a_c)$ and therefore reply $a_c$ by (SIR.10).
Adjoining these fixed values to its remaining seed vector satisfies
all original prescriptions. This proves the other inclusion.

Different $a$ differ at an actual owner reply, hence cannot give
the same tuple. Every original tuple has one such vector. The
partition proves (SIR.15), without a product assumption on $W$.
For $W(x)=\prod_iw_i(x_i)$, the credited one-lift identity in RRN
identifies both sides with (SIR.16). In each branch $\Phi_i$ is
the original full $\Phi_i$ with $s_H=a$ substituted; its weight
has neither been split nor repeated.

If a conditioned domain is empty there are no branches, and the
original solution set is empty. An unconditioned empty domain
makes every branch empty. Empty $H$, singleton domains, no seeds,
zero weights and incompatible constant prescriptions obey the same
identity, with the usual empty-product convention. Finite
conditioning and distributivity are the mature ingredients, as in
[Dechter, §§3–4][Dechter]; (SIR.14) supplies the additional native
same-coordinate closure. $\square$

**Theorem 3.2 (counted high-incidence elimination).** For every
$d,n,L\ge1$ and every network $\mathcal N$, put

$$
H_L=\{c:\nu_{\mathcal N}(c)>L\},\qquad
q_{\mathcal N,L}=\prod_{c\in H_L}|T_c|,\qquad
Q_{d,L,n}=4^{\lfloor nm_d/(L+1)\rfloor}.
\tag{SIR.17}
$$

Theorem 3.1 partitions its full actual solution set into at most
$q_{\mathcal N,L}\le Q_{d,L,n}$ nonempty full solution sets from
$\mathfrak N_{d,L}(n)$ on the same $n$ original blocks.

Proof. Each block has $m_d$ ports, each assigned to at most one seed.
Counting distinct block-seed incidences gives

$$
\sum_c\nu_{\mathcal N}(c)
 =\sum_i|\{c:\text{a port in block }i\text{ is assigned to }c\}|
 \le nm_d.
\tag{SIR.18}
$$

Every member of $H_L$ contributes at least $L+1$, so
$|H_L|\le\lfloor nm_d/(L+1)\rfloor$. Each domain has at most
four members. Apply Theorem 3.1 to $H_L$. Every remaining seed
already had incidence at most $L$, and conditioning adds no
occurrence. Discard empty sections. If any domain was empty,
the conclusion is the empty partition of the empty set. $\square$

## 4. Both pressure directions and exact cover refinement

**Theorem 4.1 (all-original-competitor mass and pressure comparison).**
For every $d,n,L\ge1$ and arbitrary nonnegative whole-block weights,

$$
A_{d,L,n}(w_1,\ldots,w_n)
\le A_n^{(d)}(w_1,\ldots,w_n)
\le Q_{d,L,n}A_{d,L,n}(w_1,\ldots,w_n).
\tag{SIR.19}
$$

Consequently, for every nonnegative $w$,

$$
\beta_{d,L}(w)\le\beta_d(w)
\le4^{m_d/(L+1)}\beta_{d,L}(w).
\tag{SIR.20}
$$

At a finite length $n\le L$ the two maxima in (SIR.19) are equal.

Proof. The inverse RRN correspondence makes every restricted network
an original complete template, proving the first inequality. In the
other direction, normalize any original complete template using RRN,
preserving exactly its actual solution set, its $n$ blocks and its
weight. Theorem 3.2 partitions that set into at most $Q_{d,L,n}$
restricted solution sets. Theorem 3.1 preserves their masses exactly;
each is bounded by the restricted maximum. Sum and then maximize.
This covers arbitrary donors, cycles, guard restrictions and original
fiber correlations. The same argument applies to any nonnegative
tuple weight $W$ if both finite maxima are defined using that $W$.

For identical weights, take $n$th roots and use
$Q_{d,L,n}^{1/n}\le4^{m_d/(L+1)}$, then take the supremum over
all $n$. This proves both directions of (SIR.20), including $w=0$.
When $L\ge n$, every seed of every network has incidence at most
$n$, so the classes already coincide. $\square$

**Theorem 4.2 (integral and fractional cover refinement).** For every
$d,n,L\ge1$,

$$
\begin{aligned}
K_d(n)&\le K_{d,L}(n)\le Q_{d,L,n}K_d(n),\\
Z_d(n)&\le Z_{d,L}(n)\le Q_{d,L,n}Z_d(n).
\end{aligned}
\tag{SIR.21}
$$

More precisely, each complete cover member $C_e$ is partitioned
by Theorem 3.2 into disjoint sections $C_{e,a}$, with exactly
the same union $C_e$. For fractional coefficients $\theta_e\ge0$,
assign $\theta_e$ to every nonempty section of $C_e$. At every tuple
the total covering sum is unchanged; the total coefficient is at most
$\sum_e\theta_e q_{e,L}$.

If an arbitrary encoder has disjoint assigned fibers $B_e\subseteq C_e$,
then

$$
B_{e,a}=B_e\cap C_{e,a}
\tag{SIR.22}
$$

is an exact partition of that fiber into assigned subsets of these
restricted full solution sets. Its number of attained refined names is

$$
\sum_e\left|
 \{(r_{x_{i_c}}(q_c))_{c\in H_{e,L}}:x\in B_e\}\right|
\le\sum_e q_{e,L}\le Q_{d,L,n}\,|\{e\}|.
\tag{SIR.23}
$$

Proof. First start with complete members and use their exact section
partitions. A tuple belongs to precisely one section of each parent
member that contains it. This proves the asserted pointwise equality
of fractional covering sums, and the integral count bound follows by
counting nonempty sections. Combining identical sections can only
reduce the total coefficient or number.

For an arbitrary admissible cover, NDR saturation first enlarges
members to complete solution sets, without increasing their number
or total coefficient. This first enlargement can increase coverage;
the subsequent section replacement preserves that enlarged covering
sum exactly. Restricted complete sets are themselves original
admissible sets by RRN's converse, giving the opposite optimum
inequalities in (SIR.21).

For assigned fibers, intersect the exact parent partition with $B_e$.
The owner vector recovers its section uniquely, proving (SIR.22)
and the exact attained-name count (SIR.23). A subset of a section
inherits all its complete native witnesses; it need not itself be
a full solution set. Thus the statement neither enlarges an
encoder's assigned fiber nor supplies an uncounted section selector.
$\square$

## 5. Uniform normalized penalties

**Theorem 5.1 (cover-rate incidence approximation).** Define
$K_{d,L}(0)=1$. The limits

$$
\gamma_{d,L}=\lim_{n\to\infty}\frac{\log_2K_{d,L}(n)}n
 =\inf_{n\ge1}\frac{\log_2K_{d,L}(n)}n
\tag{SIR.24}
$$

exist, and

$$
0\le\gamma_{d,L}-\sigma_d\le\frac{2m_d}{L+1}.
\tag{SIR.25}
$$

For $\Lambda_L^{\rm cov}=\sup_{d\ge1}2^{-d}\gamma_{d,L}$,

$$
\lambda\le\Lambda_L^{\rm cov}\le\lambda+\frac2{L+1},
\qquad \Lambda_L^{\rm cov}\downarrow\lambda.
\tag{SIR.26}
$$

Proof. Disjoint products of restricted networks retain every seed's
incidence. Products of cover members therefore give
$K_{d,L}(n+r)\le K_{d,L}(n)K_{d,L}(r)$. Singleton covers give
$1\le K_{d,L}(n)\le|S_d|^n$. Apply the elementary subadditive
quotient-and-remainder argument used in FMR Theorem 6.4: for fixed
$r\ge1$, write $n=jr+t$, $0\le t<r$, bound the logarithm by
$j\log_2K_{d,L}(r)+\log_2K_{d,L}(t)$ and divide by $n$.
The limsup is at most every length-$r$ quotient, and every quotient
is at least their infimum. This proves (SIR.24).

Take logarithms of (SIR.21), divide by $n$ and use both existing
limits. Since $\log_2 4=2$, this proves (SIR.25). In particular,

$$
0\le2^{-d}(\gamma_{d,L}-\sigma_d)
\le\frac{2(1-2^{-d})}{L+1}<\frac2{L+1}.
\tag{SIR.27}
$$

Take depth suprema and use (SIR.8). Increasing $L$ enlarges the
allowed class and decreases every restricted cover optimum; hence
$\Lambda_L^{\rm cov}$ is nonincreasing. Its displayed error tends
to zero. This is an incidence modulus for regularized quantities;
it gives no computable length modulus for any member. $\square$

**Theorem 5.2 (optimized pressure incidence approximation).** Put

$$
b_{d,L}=\inf_{\mu\in\Delta(S_d)\cap\mathbb Q^{S_d}}\beta_{d,L}(\mu),
\qquad \tau_{d,L}=-\log_2 b_{d,L},
\qquad \Lambda_L^{\rm pres}=\sup_{d\ge1}2^{-d}\tau_{d,L}.
\tag{SIR.28}
$$

The infimum is the same over all real probabilities, without an
attainment assertion. These quantities satisfy

$$
\begin{aligned}
|S_d|^{-1}&\le b_{d,L}\le b_d
                  \le4^{m_d/(L+1)}b_{d,L},\\
0&\le\tau_{d,L}-\sigma_d\le\frac{2m_d}{L+1},\\
\lambda&\le\Lambda_L^{\rm pres}\le\lambda+\frac2{L+1},
\qquad\Lambda_L^{\rm pres}\downarrow\lambda.
\end{aligned}
\tag{SIR.29}
$$

Proof. No-seed singleton networks show
$\beta_{d,L}(\mu)\ge\max_x\mu(x)\ge1/|S_d|$.
All ambient probability masses are at most one. For the rational
infimum, take infima of (SIR.20) and use NPC Theorems 5.3 and
6.2, which identify the rational unrestricted infimum with $b_d$.
This gives the first line of (SIR.29). Negative logarithms reverse
the inequalities as displayed and give the second line.

For completeness, the rational restriction does not create a
different auxiliary infimum. Given a real probability $\mu$ and
$\epsilon>0$, approximate it by a rational probability $\nu$ on
the same support, so closely that
$\nu(x)\le(1+\epsilon)\mu(x)$ for every $x$. This is possible
in the relative interior of that finite support's simplex, including
a singleton support. Pointwise domination of every length-$n$
mass gives
$\beta_{d,L}(\nu)\le(1+\epsilon)\beta_{d,L}(\mu)$.
Take infima and let $\epsilon\downarrow0$. No continuity or
minimizer of the auxiliary pressure has been presumed.

Divide the second line by $2^d$ and take depth suprema, exactly
as in (SIR.27). Increasing $L$ increases the pressure class and
its optimized infimum, so the auxiliary endpoints decrease. The
vanishing uniform error proves the limit. Neither this proof nor
Theorem 5.1 requires an identification of the two auxiliary
hierarchies or makes either hierarchy a computable numerical
bound. $\square$

## 6. Conditional cap certificates with an original-task conclusion

**Theorem 6.1 (faithful bounded-incidence cap transfer).** Let
$d,L\ge1$, let $\mu$ be a probability on $S_d$, and let $C_0>0$.
Suppose

$$
\forall n\ge1\ \forall\mathcal N\in\mathfrak N_{d,L}(n),\qquad
Z(\mathcal N;\mu,\ldots,\mu)\le C_0^n.
\tag{SIR.30}
$$

Then every original complete template, at every length, has mass
at most $C^n$ for

$$
C=4^{m_d/(L+1)}C_0.
\tag{SIR.31}
$$

Any positive rational $\widehat C$ satisfying

$$
\widehat C^{L+1}\ge4^{m_d}C_0^{L+1}
\tag{SIR.32}
$$

is also a valid original cap. In particular, for all $D\ge d$,

$$
M_1(D)\ge\left\lceil\widehat C^{-2^{D-d}}\right\rceil,
\qquad \lambda\ge-2^{-d}\log_2\widehat C.
\tag{SIR.33}
$$

Proof. The premise is exactly $\beta_{d,L}(\mu)\le C_0$.
Apply (SIR.20). Raising positive quantities to $L+1$ makes
(SIR.32) equivalent to $\widehat C\ge C$. For rational $C_0$
this is an exact rational comparison without a floating-point premise.
Apply NPC Theorem 7.1, or (SIR.9).

Its original-competitor restriction uses the actual perfect scaffold
with $2^{D-d}$ present $S_d$ blocks in the right subtree. Each
permitted block target is an original-root request. Every arbitrary
original-root late literal is constant outside the blocks or is a
function of one boundary reply in one actual donor block, even if
that donor differs from the target. On a fixed original code fiber,
the query is fixed before its reply and every count. Equal replies
must produce the same whole target trajectory, hence the same
factor. The restricted fiber is therefore admissible with all its
correlations intact, and its mass is bounded by the transferred
cap. These fibers partition total analytical product mass one.
Counting them proves the ceiling against the unchanged complete
alphabet. No seed vector is made accessible to that competitor.
$\square$

**Definition 6.2 (the remaining bounded-incidence certificate premise).**
A uniform bounded-incidence cap verifier is a total computable
predicate $W(d,L,\mu,C_0,\pi)$ on $d,L\ge1$, rational
probabilities, positive rational caps and finite strings. Soundness
means that acceptance implies (SIR.30). Optimized coverage means
that for every $d,L$ and rational $\epsilon>0$, some accepted
label satisfies

$$
-\log_2 C_0>\tau_{d,L}-\epsilon.
\tag{SIR.34}
$$

This definition still quantifies over every network length and
arbitrary topology with the full potentials (SIR.11). It does not
assert that such a predicate has been constructed.

**Theorem 6.3 (conditional total sound and cofinal transfer).** If a
uniform $W$ satisfies soundness and optimized coverage in Definition
6.2, then a total sound verifier satisfying [NPC, Definition 8.1][NPC]
exists for the original unrestricted problem.

Proof. A certificate for input $(d,\mu,\widehat C)$ contains
$L,C_0,\pi$. Reject malformed data; otherwise require acceptance
by $W$ and the exact rational comparison (SIR.32). The finite
parsing and rational operations terminate, and $W$ is total by
hypothesis. Theorem 6.1 proves soundness for every original length
and template.

Fix $d$ and rational $\epsilon>0$. Choose $L$ with
$\delta=2m_d/(L+1)<\epsilon/3$. By (SIR.34), take an accepted
label with $-\log_2C_0>\tau_{d,L}-\epsilon/3$. Choose a rational
$\widehat C\ge4^{m_d/(L+1)}C_0$ so close from above that

$$
0\le\log_2\frac{\widehat C}{4^{m_d/(L+1)}C_0}<\epsilon/3.
$$

It passes (SIR.32), and

$$
-\log_2\widehat C
>\tau_{d,L}-\epsilon/3-\delta-\epsilon/3
\ge\sigma_d-\epsilon.
\tag{SIR.35}
$$

This is the unchanged optimizer-cofinality requirement. At the
original normalized-rate scale, the incidence loss is strictly
less than $2/(L+1)$, independently of $d$. Together with the
credited depth error $2^{-d}\phi$ and arbitrarily fine cap rounding,
the conditional hypothesis would therefore give the two-sided
effective original-rate approximation of NPC Theorem 8.2. The
unproved premise is the existence and optimized coverage of $W$,
not the finite rational transfer comparison. $\square$

## 7. Actual acquisition and the complete exported alphabet

**Theorem 7.1 (paid realization of the exact refinement).** Suppose
$Ra_1,\ldots,Ra_n$ are public prefix-free, actually present roots
in one stationary original source, with $|a_i|\le H$, each block
of height at most $d$. Given common source-independent finite
joint-cover tables, an assignment rule and complete witnesses for
their assigned fibers, the refinement (SIR.22) is
realized by one source-blind preparation before any target. Its
complete attained names are precisely the attained pairs

$$
(e,a),\qquad
a=(r_{x_{i_c}}(q_c))_{c\in H_{e,L}},
\tag{SIR.36}
$$

where $x$ is the acquired canonical tuple and $e$ its assigned
joint parent name. If all $S_d^n$ tuples are realized by the source
domain, their number is exactly the left-hand side of (SIR.23);
on a smaller actual tuple domain the same formula is restricted
to that domain.
Sufficient preparation resources on every source are

$$
\begin{aligned}
T&\le n(2^d-1),& Q&\le H+d,\\
A&\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\end{aligned}
\tag{SIR.37}
$$

A block request is answered by zero Reads or one original-root
late literal of length at most $H+d$, selected before every supplied
count. When $H+d\le D$ these are permitted original requests.

Proof. Submit every actual word $Ra_iq$, $q\in W_d$, in a
public fixed order, including absent suffixes. These charged
replies determine $x_i=\pi_d(t|_{Ra_i})$ and all possible owner
replies. Select $e$ by the installed public assignment rule, then
compute its actual high-incidence owner vector $a$. The parent
network and its high-seed list depend on the exported parent name
and public tables, so (SIR.36) includes the entire extra selector.
Theorem 4.2 gives its exact attained alphabet and upper bound.

Export only a fixed-width name for the attained pair. Use public
allocation, a fixed scan and a padded finite selection schedule.
Under Assumption 1.2 isolate the acquired constructor arrays,
unexported owner replies, intermediate buffers, control and other
preparation dependence. Every surviving source distinction is
then a function of this name and public inputs. The isolated
workspace has supplied no free source-dependent color or seed.

For a requested port, the section prescribes a full-factor constant
or a table of one remaining seed. The constant uses zero Reads.
For the latter, RRN's converse queries that seed's actual owner
$(j,q_c)$, implemented by the single original-root word $Ra_jq_c$.
The seed's domain guard and tables remain valid on this named
section. Canonicalization preserves that reply and the required
factor. Since $Ra_i$ is present, homomorphic substitution gives

$$
r_{\rho^kt}(Ra_iq)
=r_{\rho^k(t|_{Ra_i})}(q)\qquad(k\ge0).
\tag{SIR.38}
$$

This is the actual-presence premise of
[`original_present_transport`][Depth]. The notation for a subtree
is mathematical, not an extra input. The decoder (SIR.4) gives
every subsequent authentic-count reply with no further Reads.
No count or source-dependent target guided acquisition or query
choice. An artificial wrapper's root and left cone are public
constants; its virtual $Rw$ is realized only by the actual word
at its present occurrence followed by $w$, as in FMR Lemma 3.1.

There are $2^d-1$ words per block. Their suffix lengths sum to
$\sum_{j=0}^{d-1}j2^j=(d-2)2^d+2$; each prefix has length at
most $H+1$. This proves (SIR.37), also at $d=1$. These are the
credited scan bounds of RRN Proposition 7.3, applied to the new
counted refinement. Joint table generation and installation,
membership work, temporary and post-request storage, predictor
size and the paid services remain separate resources. $\square$

**Theorem 7.2 (full variable-shape realization with counted shape).**
For integers $d,L\ge1$ and $h\ge0$, put $D=d+h$ and $n=2^h$.
There is a correct
original preparation and reader with complete attained alphabet at most

$$
U_hK_{d,L}(2^h)
\le U_hQ_{d,L,2^h}K_d(2^h).
\tag{SIR.39}
$$

It serves every original target and authentic subsequent count,
on every $t\in\mathcal F_D$, with sufficient preparation bounds

$$
T\le2^D-1,\qquad Q\le D,\qquad A\le(D-1)2^D+1.
\tag{SIR.40}
$$

The optional one late original-root Read has length at most $D$.

Proof. Apply the credited full-family cutting construction of FMR
Theorem 6.3, using a restricted joint cover. Retain the unlabelled
top shape through height $h$, whose possible alphabet has size
$U_h$. At each actual depth-$h$ slot use its canonical $S_d$
block; at each slot blocked by a shallow leaf put the public
dummy alpha in the analytical tuple. Retain the shape and the
tuple's first-containing-member cover name. If using Theorem 4.2
to obtain that cover, its section selector is already included
in this second component. The possible pair alphabet has the
first bound in (SIR.39), and Theorem 4.2 gives the second.
Only attained pairs count; their number need not equal this upper.

Acquire the complete canonical boundary by the actual original-root
words $Rq$, $q\in W_D$, before receiving a target. It determines
the shape and the entire padded tuple. Compute and export their
fixed-width complete pair name, isolating all other source dependence
under Assumption 1.2. The word count and length sum are (SIR.40).

After the request, a target ending at a branch above the cut has
constant branch trajectory. If it meets a shallow leaf, the retained
shape locates that actual leaf. One Read at its original-root word
gives its label and (SIR.3) supplies the target factor, including
initially absent targets below it. Otherwise it enters one actual
slot and invokes its joint section witness. A surviving donor in
an actual slot is queried at its original-root literal. A donor
in a dummy slot is simulated from the public alpha tree, without
a source-bearing Read; the retained shape specifies which case
applies. Every request therefore uses at most one actual Read,
and (SIR.4) answers all subsequently supplied authentic counts.

This construction counts the cut shape instead of treating it as
free navigation. The top shape varies with the source and belongs
to the complete code. Its shallow leaf labels are reacquired only
when required after the request. It implements an upper bound,
not an independent-child restriction on competing original codes.
The scan replaces old preparation costs and gives no bound on
total installation, workspace, work or physical time. $\square$

**Definition 7.3 (cardinality and resource boundaries of normalization).**
The original optimal alphabet and its paid representative readers
are already identified by RRN Theorem 7.1. For an arbitrary possibly
nonminimal original $m$-name competitor, canonical normalization
may reduce its attained alphabet. RRN Corollary 7.2 supplies exact
$m$-name realization if required, with sufficient fuller-scan bounds
$2^{D+1}-1$ Reads, maximum address $D+1$, and $D2^{D+1}+1$
letters. These are credited correspondences, not preparation-cost
preservation by seed conditioning. The refinement cost is instead
the exact attained selector count (SIR.23).

The factor predictor can use $0\le b\le2D$, $c\in\{0,1\}$,
requiring at most $\lceil\log_2(2D+1)\rceil+1$ bits separately
from the export and count representation. No physical erasure,
timing, authentication or free-total-efficiency conclusion is part
of Theorems 7.1–7.2.

## 8. A fixed-cut boundary for exact solution-set truncation

**Definition 8.1 (the precise decomposition class).** Fix integers
$L,g\ge1$, let $n=g(L+1)$, and partition $[n]$ into $g$ groups
of size $L+1$. On the original $d=1$ blocks let

$$
B_{L,g}=\{x\in S_1^n:
            x_i=x_j\text{ whenever }i,j\text{ are in one group}\}.
\tag{SIR.41}
$$

An exact fixed-coordinate restricted decomposition covers this full
relation by full solution sets of $\mathfrak N_{1,L}(n)$, each
contained in $B_{L,g}$, with no new blocks, variables or cut.
This class describes the same-solution section mechanism, not
all possible admissible covers containing the relation.

**Theorem 8.2 (necessary section count on actual ternary groups).**
$B_{L,g}$ is a full complete native solution set with $3^g$ rows.
Every nonempty full solution set from $\mathfrak N_{1,L}(n)$
contained in it is a singleton. Consequently its minimum exact
decomposition in Definition 8.1 has exactly $3^g$ pieces, with
logarithmic piece count per original block

$$
\frac{\log_2 3}{L+1}.
\tag{SIR.42}
$$

Proof. At $d=1$ there is only the root target, whose factors on
$\alpha,\beta,C_0$ are respectively $(2,1),(1,0),(0,0)$.
For every coordinate in a group, query one fixed group root and
decode these three replies to their root factors. The owner can
query itself; assign the unused absent entry any attained factor.
The simultaneous equations force precisely equality within each
group, with no condition between groups. This gives the asserted
complete template and $3^g$ distinct actual tuples.

Now consider any nonempty restricted full solution set contained
in $B_{L,g}$. All its domains are nonempty. Each block has one
port, and every attained root factor specifies one of the three
actual $S_1$ roots. Thus every assignment of all its seeds is
realizable: there is no further multi-port compatibility within a
block. Different seeds range independently in this particular
full solution set. Each coordinate is a constant or a function
of its one assigned seed; the owner identity still holds.

If a group varied, one of its coordinates would be a nonconstant
function of a seed $c$. Every other coordinate in the group
must equal it for every seed assignment. It cannot be constant.
It cannot depend on a different seed, because varying $c$ with
that other seed fixed would violate equality. It must therefore
be assigned to the same $c$. This requires incidence at least
$L+1$, contradicting the restriction. Every group is consequently
fixed, so the solution set is a singleton. Singletons are constant
networks and attain a matching decomposition of all $3^g$ rows.
Divide its logarithm by $n=g(L+1)$ to get (SIR.42).

The comparison with unrestricted covers uses the credited depth-one
own-root reader, already giving $M_1(1)=1$ in FMR. Its disjoint
product gives every root its own seed, domain
$\{\alpha,\beta,\mathsf{branch}\}$, and the bijective root-factor
table above. All incidences are one and the full solution set is
$S_1^n$. Thus, as an ingredient fixing the boundary's scope,

$$
K_{1,L}(n)=K_1(n)=1,\qquad
A_{1,L,n}(w_1,\ldots,w_n)=\prod_i\sum_{u\in S_1}w_i(u),
\qquad\beta_{1,L}(w)=\beta_1(w)=\sum_{u\in S_1}w(u).
\tag{SIR.42a}
$$

Indeed this one set covers the universe and attains all its
nonnegative mass; no competitor has greater mass than the universe.
The exact-decomposition obstruction therefore gives no lower bound
on optimized pressure, memory, arbitrary recoloring or arbitrary
certificates. It excludes zero-cost same-solution truncation at the
stated cut, while a larger full set covers the relation immediately.
It gives no obstruction to a different lawful recut and does not
assert optimality of $Q_{d,L,n}$ for pressure or cover approximation.
$\square$

**Theorem 8.3 (paid full-family realization of the boundary).** Let
$n=g(L+1)$, $H=\lceil\log_2n\rceil$, $N=2^H$ and $D=H+1$.
Embed the $n$ blocks in the first $n$ frontier slots of a fixed
perfect height-$H$ right-subtree scaffold, filling the other
$N-n$ slots by alpha. There is a correct original code on all
$\mathcal F_D$ merging precisely the resulting $3^g$ canonical
states into one name and naming every other $S_D$ state separately.
Its complete attained alphabet is exactly

$$
|S_D|-3^g+1,
\tag{SIR.43}
$$

with preparation bounds (SIR.40) and at most one late original-root
Read of length at most $D$. For $L=1,g=2$, the construction has
$D=3$, $115$ attained names, seven preparation Reads and
$17$ submitted letters.

Proof. The fixed scaffold with its ordered actual $S_1$ leaves
defines an injective map into $S_{H+1}$. The group choices give
$3^g$ distinct canonical states. Before any target, scan every
$Rq$, $q\in W_D$, and select the described merged-or-singleton
name from the acquired $\pi_D(v)$. Isolate all other acquired
source dependence under Assumption 1.2. Canonical actual sources
attain every name, proving (SIR.43) and the stated paid scan.

On a singleton name, the public table supplies every canonical
factor without a Read. On the merged name, targets strictly
above the frontier are constantly branch. A frontier target is
served by its own original-root literal, decoding alpha, beta
and branch as in Theorem 8.2. Padded frontier slots are constant
alpha and can use zero Reads. Every target in $\mathcal P_D$
is of one of these forms. Canonicalization preserves all used
replies and factors on the full assigned variable-shape fiber.
Equation (SIR.4) proves correctness for every later authentic
count. No group value or source identity is supplied as advice.

Finally $|S_1|=3$, $|S_2|=11$, $|S_3|=123$, so the indicated
case has $123-9+1=115$ names; the scan-letter sum is
$(3-1)2^3+1=17$. This deliberately nonoptimal code witnesses
the actual source class, not the optimum. $\square$

## 9. Mathematical attribution and exact unresolved targets

**Definition 9.1 (source scope and credited ingredients).** Repository
citations designate their mathematical statements at the immutable
[source revision][Base]. The native deductions here are the
same-block high-incidence section reduction, its pressure and cover
comparisons, normalized error and conditional original-cap transfer,
with the fixed-coordinate solution-set boundary. The finite
conditioning, incidence double counting, distributivity and
subadditive limit arguments are mature ingredients. They carry no
worldwide-priority assertion. The statements are ordinary mathematics;
no new kernel-verification claim is attached to them.

| Mathematical source | Exact ingredient and boundary |
| --- | --- |
| [RRN, §§4–7][RRN] | Same-solution representative normalization, two-way owned-seed realization, actual owner guards, once-owned joint potentials and paid scans. These exact carriers are reused, not reproved as new normal forms. |
| [NPC, §§5–8][NPC] | Semantic optimized pressure, rational approximation, original-competitor mass transport and the precise sound/cofinal-verifier obligation. Semantic existence is not an effective cap certificate. |
| [CBN, §§2–8][CBN] | Actual constructor arrays, equality-aware compilation and full block weights. A joint weight need not factor into unary or binary constructor potentials, and bounded incidence gives no supplied uniform width. |
| [FMR, §§2–3 and 6][FMR] and [AAR, §§12–13 and 16][AAR] | Canonicalization, all-count factors, all-word simulation, paid native covers, actual occurrence transport, full-family shape cost and original rate. Fixed-menu passive acquisition is a different endpoint. |
| [NCM, Theorem 4.1 and Proposition 6.1][NCM] | Exact depth-two regularized rate and the cyclic relation with inadmissible coordinate projections. No projection-independence assumption is used here. |
| [NCE, Theorems 6.1–6.2][NCE] and [D3, Theorems 2.3 and 4.1][D3] | The retained original lower, exact $M_1(3)$ and improved original upper; none is a new numerical result of the incidence reduction. |
| [NDR, Theorem 7.2 and Proposition 9.1][NDR] | Fixed-original-block component repair obstruction and that family's faithful finer cut. Incidence truncation retains arbitrarily large components and does not strengthen those negative quantifiers. |
| [JTC, Definition 9.1 and Theorem 9.2][JTC], [SRP, Theorem 1.2][SRP] and [GCB, Theorem 1.2][GCB] | Existing sound recursive joint rules, the support-specific single-residual theorem and exact native binary incidence embedding. Their support and joint-weight conditions remain necessary. |
| [RCE, §§4–8 and 10][RCE] and [JPL, §§4–7][JPL] | Precisely scoped old-calculus pointwise separations and restricted-language optimizer boundaries. They do not disprove unrestricted optimizer-cofinality; conditioning here retains the full joint potentials. |
| Dechter, *Bucket elimination: A unifying framework for probabilistic inference*, §§3–4, [primary text][Dechter] | Finite shared-variable conditioning and summation preserve the full factor sum. Elimination complexity depends on induced width; bounded seed incidence alone provides no such bound. |
| Forney, *Codes on Graphs: Fundamentals*, §2.2, [primary text][Forney] | Repeated variable occurrences are identified by equality. The reduction retains one owner reply, all its equal occurrences and one use of each original weight, not independent replicas. |
| Gaubert–Stott, *A convergent hierarchy of non-linear eigenproblems to compute the joint spectral radius of nonnegative matrices*, Theorem 7, [primary text][GS] | Its approximation factor uses a fixed matrix dimension and positive irreducibility. There is no established representation of all remaining native networks by one such matrix family, with both pressure directions and the native resource correspondence. No effective native bound is imported from it. |

**Definition 9.2 (exact scope of existing formal interfaces).** The
declaration [`original_present_transport`][Depth] assumes
`subtree a u = some t`; (SIR.38) uses precisely actual presence.
`original_prefix_locality` requires equality of all original replies
through the requested word length. Neither supplies an operational
subtree or an unacquired boundary array.

In [`FiniteNaturalJoin.join_covers`][Join], both `Covers` premises
refer to the same total assignment. It preserves that assignment
in the join, not existence of an assignment from separately
compatible margins or an all-size weighted estimate.

[`NativeFiniteRootMinimax.finite_root_minimax`][Minimax] and its
[Blueprint][MinimaxB] concern a finite actual three-reply chart
and complete predecessor-row minimax. The declarations
[`effective_native_birth_provenance` and `returned_native_reader`][Criterion]
and their [Blueprint][CriterionB] require a prefix-free cut, a
complete row with nonempty `OriginFiber`, $r\ge1$, a returned
package and compatible acquired image values; the reader runs
on the substituted source. That target and handoff are different
from stationary-source all-length pressure. They are not used as
a cap verifier in Theorem 6.3.

**Definition 9.3 (unchanged open mathematical obligations).** The
original target is a total sound verifier with accepted rational
caps optimizer-cofinal at every unchanged $\sigma_d$, as in NPC
Definition 8.1 and RRN Open problem 8.2. An alternative sufficient
target is a uniform effective length error

$$
\sigma_d\ge\frac{\log_2K_d(n)}n-\eta_d(n),
\qquad\eta_d(n)\longrightarrow0,
\tag{SIR.44}
$$

with effective control sufficient for terminating two-sided original
rate approximation. Neither target is proved by an incidence cutoff.
For each fixed $d,L$, (SIR.30) still ranges over unbounded lengths
and arbitrary bounded-incidence components with the same guards,
shared seeds, compatibility zeros and full joint block weights.
No sound optimizer-cofinal $W$ of Definition 6.2, finite length
cutoff, uniform width, zero-free condition or fixed-dimensional
matrix correspondence is supplied. Theorems 5.1–5.2 give an
effective error in $L$ between semantic regularized quantities,
not an effective procedure for evaluating those quantities.

Finite cover values upper-bound their regularized infima. Finite
mass maxima lower-bound all-length pressure suprema. Exact finite
evaluation or enumeration of finite proofs does not reverse either
direction or establish optimized coverage. The exact section count
at fixed $L$ may be exponential in $n$; its normalized logarithmic
penalty vanishes as $L$ increases, not as $n$ increases at fixed $L$.
Transferred caps at least one can yield only a trivial rate lower.
These boundaries provide no noncomputability conclusion or universal
obstruction to other overlap-sensitive certificate methods.

The credited interval and finite value remain

$$
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16},
\qquad M_1(3)=4,
\tag{SIR.45}
$$

with lower from NCE and upper and finite value from D3. Sharp
$\lambda$, general exact $M_1(D)$, effective two-sided convergence
and the broader minimal-relations/internal-observer/mutual-recovery
programme remain unresolved. Under the paid services, the retained
observer correspondence is exactly

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{SIR.46}
$$

Its reverse recovers the first branch count and alpha-stage flag.
It does not recover a whole hidden source, unknown age, seed vector,
physical space-time or an authentication service. An original-task
completion still requires the all-size optimized certificate or
length-error obligation, together with its stated separate resources.

[Base]: https://github.com/the-omega-institute/trureturing/tree/f586077f0b16eb03fc18e753a30e4b6b68996dae
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[SRP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[RCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[RRN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[JPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_POTENTIAL_LIMITS.md
[Depth]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[Join]: ../../../D5/S0/Certificates/FiniteNaturalJoin.lean
[Minimax]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean
[Criterion]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[MinimaxB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.md
[CriterionB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.md
[Dechter]: https://arxiv.org/pdf/1302.3572
[Forney]: https://arxiv.org/html/1306.6264v2
[GS]: https://arxiv.org/html/1805.03284v1

## 追加锚（本行以下为增补区）
