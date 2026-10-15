# Recursive relational observation: conditional kernels of actual owner groups

## 1. Native task, credited representation and intended consumer

**Convention 1.1 (status and scope).** This volume is a theory-only
reference input with ordinary finite mathematics and proofs. It supplies
a sound finite conditional-kernel family for the unchanged native task.
Its finite local family is an outer relaxation. Completeness for this
relaxation is distinguished throughout from optimizer-cofinality for
native pressure. No Lean verification, effective native length tail,
physical realization or completion of the mutual-recovery programme is
asserted. All logarithms, entropies and relative entropies have base two.
The native suppliers below are read at public revision
76e56d4505199480f6a995a3a96dfba7fe719fe3, except the expressly pinned
additional RCE sections in §9.

**Definition 1.2 (original sources and paid interface).** Trees form the
free ordered binary magma

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,
\quad
\operatorname{ht}\langle u,v\rangle=1+\max(\operatorname{ht}u,\operatorname{ht}v).
$$

Every finite original-root word in $L,R$, including the empty word, is
a legal literal Read. The reply alphabet is
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$; traversal
beyond a leaf returns absent. Write $r_t(a)$ for the reply. The
homomorphic substitution and source family are exactly

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle,\qquad
\mathcal F_D=\{\langle\alpha,v\rangle:\operatorname{ht}(v)\le D\},
\quad D\ge1.
\tag{COK.1}
$$

One initial source $t$ remains stationary through preparation and later
acquisition; $\rho^kt$ specifies a prediction target. Preparation is one
deterministic effective source-blind procedure depending on $D$ and
common public tables, without the later request. It terminates on every
$t$ and acquires every source distinction by charged literal Reads.
Its finite export $E(t)$ counts every accessible surviving source
distinction, including selectors, control, buffers, lengths, allocation,
handles and accessible timing. A paid handoff and access-isolation
service removes access to all other acquired dependence and supplies
lawful entry. Previous preparation transcripts are inaccessible.

Only after export a source-independent request $p$ is supplied, ranging
over every $R$-starting word with $1\le |p|\le D$. From $E(t),D,p$ and
common tables the reader chooses zero Reads or one fresh Read of the
same stationary source at any finite original-root word. The query
choice precedes its reply and every supplied count. The resulting
predictor, with no further Reads, answers

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\qquad\text{for every subsequently supplied authentic }k\ge0,
\tag{COK.2}
$$

simultaneously for every $t$ and every request. $M_1(D)$ minimizes the
complete attained alphabet $|E[\mathcal F_D]|$ over all these procedures.
There are no subtree, equality, source-identity, age, navigation, reset,
copying or free-advice ports. Preparation work and Reads, installed
tables, post-request workspace, predictor size, address lengths and
letters, count representation and physical time are separate resources.
These are the [FMR][FMR] and [NPC][NPC] interface premises, not inferred
physical operations.

**Definition 1.3 (canonical blocks and full temporal factors).** Put

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle u,v\rangle:u,v\in S_d\},
\quad
W_d=\{q:|q|\le d-1\},\quad m_d=2^d-1.
\tag{COK.3}
$$

For $x\in S_d$, the full temporal factor at $q\in W_d$ is
$g_q(x)=\Gamma_q(x)$. If $q$ ends at an original branch, it is $(0,0)$.
Otherwise let $\ell$ be the first blocking original leaf and write $r$
for the residual suffix beyond it. With $e(\alpha)=0,e(\beta)=1$,

$$
\Gamma_q(x)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(\#L(r)+2\#R(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{COK.4}
$$

The [AAR, §§12–13][AAR] decoder on attained factors is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{COK.5}
$$

It equals $r_{\rho^kx}(q)$ for every $k\ge0$. Conversely the full
trajectory recovers $(b,c)$. Write $h(z)=\operatorname{Pred}(z,0)$,
$G_q=\Gamma_q[S_d]$, and $r_q(x)=r_x(q)$. The full factor vector
separates $S_d$. [FMR, Lemma 2.2][FMR] supplies canonicalization
$\pi_d$ preserving all these factors and boundary replies, including
variable shapes. Every arbitrary finite experiment on a canonical
block is a function of one actual boundary reply in that same block,
or a constant. This assertion includes literals beyond the boundary;
it imposes no target-prefix restriction on a competitor.

**Definition 1.4 (complete templates and their credited owned seeds).**
A complete template $\Theta$ on $n\ge1$ blocks prescribes at every
$(i,q)$ either a constant $g_q(x_i)=z\in G_q$, or

$$
g_q(x_i)=\delta_{i,q}(r_a(x_j)),
\qquad j\in[n],\ a\in W_d,\quad
\delta_{i,q}:\mathcal A\longrightarrow G_q.
\tag{COK.6}
$$

Let $C_\Theta\subseteq S_d^n$ be its full simultaneous solution set.
All references concern the same tuple. Donors, cycles, self queries,
off-target queries and correlations are unrestricted. [NDR,
Theorem 2.2][NDR] supplies complete-template saturation for admissible
subsets, preserving nonnegative mass maxima and cover optima.

[RRN, Theorems 4.2, 5.2 and 6.1][RRN] give the exact two-way
owned-seed representation. A seed $c$ has a nonempty domain
$T_c\subseteq\mathcal A$ and a distinct actual owner port $o_c=(i,q)$.
Every local port prescribes a constant full factor or a table of one
seed. At the owner the table satisfies

$$
h(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{COK.7}
$$

Repeated occurrences are that same variable. For an assignment $s$,
the prescribed factor vector of block $i$ either reconstructs a unique
$x_i(s)\in S_d$ or is incompatible. With any nonnegative whole-block
weights $w_i:S_d\to[0,\infty)$, set

$$
\Phi_i(s)=
\begin{cases}w_i(x_i(s)),&\text{compatible},\\0,&\text{otherwise}.
\end{cases}
\qquad
Z(\mathcal N;\boldsymbol w)=\sum_{s\in\prod_cT_c}\prod_{i=1}^n\Phi_i(s).
\tag{COK.8}
$$

The exact identity is

$$
Z(\mathcal N;\boldsymbol w)
=\sum_{x\in C_\Theta}\prod_iw_i(x_i).
\tag{COK.9}
$$

Every original solution has precisely one lift, recovered as its owner
replies, and every valid such network translates back to a complete
template. Empty seed domains give no solution and can be treated
separately. [CBN][CBN] supplies actual constructor compatibility and
equality-aware reconstruction; [OCB, §§2–3][OCB] refines its temporal
compatibility and elimination boundaries. In particular each original
joint block weight occurs once. It is never replaced by pairwise
weights or by independent copies of repeated seed occurrences.

**Convention 1.5 (credited pressure and original-task bridge).** For
uniform $w$ define

$$
A_n(w)=\max_\Theta\sum_{x\in C_\Theta}\prod_iw(x_i),
\qquad
\beta_d(w)=\sup_{n\ge1}A_n(w)^{1/n}.
\tag{COK.10}
$$

The unrestricted cover number $K_d(n)$ and the native rate satisfy

$$
\begin{aligned}
\sigma_d&=\inf_{n\ge1}\frac{\log_2K_d(n)}n
       =-\log_2\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
       =\sup_{d\ge1}2^{-d}\sigma_d,\qquad
0\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,
\end{aligned}
\tag{COK.11}
$$

where $U_0=1,U_{h+1}=1+U_h^2$ and
$\phi=\lim_h2^{-h}\log_2U_h$. These are [FMR][FMR] and
[NPC, Theorems 5.3 and 6.2][NPC], including one minimizing law valid
for all sizes and templates. Semantic completeness does not give an
effective all-size verifier. The new consumer here is [RRN, Open
problem 8.2][RRN]: construct sound overlap-aware caps without
discarding full joint potentials. Sections 2–6 construct one finite
sound family and identify its remaining global gap.

## 2. Finite actual-owner-group local outer family

**Definition 2.1 (actual owner grouping).** In an actual network let
$O_i$ be the tuple of all seeds owned by block $i$. These tuples
partition the seed set. Let $I_i$ contain the seeds appearing in block
$i$ but owned outside it. Partition $I_i$ into $B_{i,1},\ldots,B_{i,k_i}$
by their actual outside owner block. Thus two incoming seeds with the
same outside owner are in the same group, even if they enter different
ports. Every owned seed occurs at its owner port. Consequently at most
$m_d$ distinct seeds occur locally and $k_i\le m_d$. The tuples
$B_{i,g}$ are subtuples of the corresponding actual $O_j$; they are
not independent donors.

**Definition 2.2 (finite decorations).** At fixed $d$, enumerate all
the following finite one-block data up to a fixed canonical relabeling
of seeds and groups.

1. At most $m_d$ distinct seeds with nonempty domains
   $T_c\subseteq\mathcal A$, each occurring at least once locally.
2. A subset $O$ owned at distinct local ports, with their actual
   full-factor tables satisfying (COK.7).
3. A partition of the remaining seeds into nonempty groups
   $B_1,\ldots,B_k$ of common external owner. For each group record
   distinct owner ports in one outside block and the full owner
   tables satisfying (COK.7).
4. At every local port, a constant in $G_q$ or a full table from
   one declared seed into $G_q$, with an owned port assigned to
   its respective seed.

All domains, ports and table ranges are finite. Bounds on their numbers
make this a finite effectively enumerable list, denoted $\mathcal E_d$.
Canonical labeling only avoids duplicates; it does not identify
different occurrences of a seed or different owner blocks. There is
no bound on the number of blocks in the networks to be tested.

One explicit encoding orders $\mathcal A$ as alpha, beta, branch,
absent, orders $W_d$ by length and then lexicographically with $L<R$,
and orders factors $(b,c)$ lexicographically. Seed and group labels
are consecutive integers. Encode domains by their ordered subsets
and tables by ordered value lists, and retain the lexicographically
least encoding over the finitely many seed and group relabelings.
The resulting sorted list fixes the type indices used below.

**Definition 2.3 (support-aware local relation).** Fix a nonzero
$w:S_d\to[0,\infty)$ and $F=\{x:w(x)>0\}$. For a decoration $\eta$,
an assignment $s=(a,b_1,\ldots,b_k)$ of its seeds belongs to
$R_\eta(w)$ precisely when both conditions hold:

1. Its full local factor vector reconstructs $x(s)\in F$.
2. For each external group $g$, there is one $u_g\in F$ with
   $g_{q_c}(u_g)=B_{o_c}(s_c)$ simultaneously for every incoming
   seed $c$ of that group.

Set $\Phi_\eta(s)=w(x(s))>0$ on $R_\eta(w)$. The second condition is a
joint owner-image test. Separate witnesses for the seeds of one group
are insufficient. The witnesses for different groups are not asserted
to extend simultaneously to a full network.

For heterogeneous block weights, the correct relation for block $i$
uses $F_i$ in condition 1 and the actual outside owner's $F_j$ in
condition 2. Replacing it by $R_\eta(w_i)$ when $F_j\ne F_i$ is not
licensed. A block with identically zero weight makes $Z=0$.

**Proposition 2.4 (coverage, not joint completion).** Every positive
global assignment of every uniform-$w$ actual owned-seed network lies
in the relation of its decoration at each block. The same holds with
the heterogeneous supports just specified. The finite family is an
outer relaxation: no converse global realization statement is included.

Proof. The local block itself supplies condition 1. The actual common
outside owner block of each incoming group supplies its single witness
for condition 2, and has positive weight in a positive global
assignment. All its owned ports have their required full factors and
actual replies. This proves coverage. These tests do not impose the
other ports of the outside blocks, their shared incoming seeds or a
consistent completion around a cycle. They are necessary local tests,
not a construction of those missing data. $\square$

**Definition 2.5 (permutation coefficients and entropy envelope).** For
$A\subseteq[k]$ put

$$
\gamma_k(A)=\frac{|A|!(k-|A|)!}{(k+1)!}
           =\frac1{(k+1)\binom{k}{|A|}},\qquad
B_A=(B_g)_{g\in A}.
\tag{COK.12}
$$

These coefficients are positive, sum to one, and are unchanged on
replacing $A$ by its complement. They are the probabilities that
exactly the owner groups $A$ precede the local block in a uniformly
random ordering of it and its $k$ distinct incoming owner blocks.
For $k=0$ the empty subset has coefficient one.

On a nonempty $R_\eta(w)$ define, for one probability law $p$ on it,

$$
\begin{aligned}
F_\eta(p)&=\sum_{A\subseteq[k]}\gamma_k(A)H_p(O\mid B_A)
                         +\mathbb E_p\log_2\Phi_\eta,\\
h_\eta(w)&=\max_{p\in\Delta(R_\eta(w))}F_\eta(p),\qquad
\Omega_d(w)=\max_{\eta\in\mathcal E_d}2^{h_\eta(w)}.
\end{aligned}
\tag{COK.13}
$$

An empty $R_\eta$ contributes zero to the last maximum, and
$\Omega_d(0)=0$. Empty tuples have one value and entropy zero.
Every entropy in $F_\eta$ uses the same law $p$; maximizing its
different marginal terms independently would define another relaxation.
For nonzero $w$ a no-seed constant decoration at any $x\in F$ is
available, so $\Omega_d(w)>0$. The maxima exist by compactness of
finite simplexes and continuity of finite entropy.

## 3. All-size conditional caps and exact common-law defect

**Theorem 3.1 (conditional-kernel cap).** Fix any actual network, with
arbitrary nonnegative block weights, repeated seeds, guards and
compatibility zeros. At block $i$ use any local outer relation covering
all its positive global assignments, with actual incoming owner groups.
For each $A\subseteq[k_i]$ let
$Q_{i,A}(a\mid b_A)>0$ be a normalized conditional probability on the
whole owned tuple, for every value of its full context. If $C_i>0$ and

$$
\Phi_i(s)\le C_i
       \prod_{A\subseteq[k_i]}
          Q_{i,A}(O_i(s)\mid B_{i,A}(s))^{\gamma_{k_i}(A)}
\tag{COK.14}
$$

on that local relation, then

$$
Z(\mathcal N;\boldsymbol w)\le\prod_i C_i.
\tag{COK.15}
$$

The assertion holds also for the mass of any retained subrelation of
actual solutions. In particular, for every $d$ and every nonnegative
uniform $w$,

$$
\beta_d(w)\le\Omega_d(w).
\tag{COK.16}
$$

Proof. Zero mass is immediate. Otherwise let $P$ be the Gibbs law on
the positive actual seed assignments being summed:

$$
P(s)=Z^{-1}\prod_i\Phi_i(s),\qquad
\log_2 Z=H_P(s)+\sum_i\mathbb E_P\log_2\Phi_i.
\tag{COK.17}
$$

The same definition with a restricted sum handles a retained actual
subrelation. Under this one law the tuples $O_i$ partition $s$.
For a permutation $\pi$ of the actual blocks let $O_{<i,\pi}$ be all
owner tuples preceding $i$. Let $A_i(\pi)$ be the incoming groups
whose owners precede $i$. Their actual tuple $B_{i,A_i(\pi)}$ is a
subtuple of $O_{<i,\pi}$. The entropy chain rule and conditioning give

$$
H_P(s)=\sum_iH_P(O_i\mid O_{<i,\pi})
 \le\sum_iH_P(O_i\mid B_{i,A_i(\pi)}).
\tag{COK.18}
$$

Averaging uniformly over all permutations gives the coefficients
(COK.12), since the relative order of each block and its distinct
incoming owners is uniform. Thus

$$
H_P(s)\le\sum_i\sum_A\gamma_{k_i}(A)H_P(O_i\mid B_{i,A}).
\tag{COK.19}
$$

Take expectations of the logarithm of (COK.14). For each kernel,
conditional relative entropy gives

$$
H_P(O_i\mid B_{i,A})+
    \mathbb E_P\log_2Q_{i,A}(O_i\mid B_{i,A})\le0.
\tag{COK.20}
$$

Substitute these inequalities into (COK.17) and (COK.19).
Every original $\log\Phi_i$ appears once, yielding (COK.15).
There is no independence, acyclicity, bounded degree or positivity
assumption on the original potentials.

For uniform $w$, Proposition 2.4 supplies the outer relations. The
local minimax theorem 4.1 supplies kernels with
$C_i\le\Omega_d(w)+\varepsilon$ for all the finitely many types, for
each $\varepsilon>0$. Apply (COK.15) to every size and let
$\varepsilon$ decrease to zero. The exact RRN correspondence
(COK.9) yields (COK.16). Identically zero $w$ is immediate. $\square$

**Theorem 3.2 (exact global loss under the common Gibbs law).** Under
the positive-mass assumptions and kernels of Theorem 3.1, define

$$
\begin{aligned}
\Delta(P)&=\mathbb E_\pi\sum_i
 I_P(O_i;O_{<i,\pi}\mid B_{i,A_i(\pi)}),\\
r_i(s)&=\log_2
 \frac{C_i\prod_AQ_{i,A}(O_i\mid B_{i,A})^{\gamma_{k_i}(A)}}{\Phi_i(s)},\\
\mathcal D_{i,A}&=
D_2\!\left(P(O_i\mid B_{i,A})\Vert
                 Q_{i,A}(\,\cdot\mid B_{i,A})\mid P(B_{i,A})\right).
\end{aligned}
\tag{COK.21}
$$

All three types of loss are nonnegative, and exactly

$$
\log_2 Z
=\sum_i\log_2 C_i-\Delta(P)
 -\sum_{i,A}\gamma_{k_i}(A)\mathcal D_{i,A}
 -\sum_i\mathbb E_Pr_i.
\tag{COK.22}
$$

Proof. Because $B_{i,A_i(\pi)}$ is a function of $O_{<i,\pi}$,
the difference of the two conditional entropies in (COK.18) is
the displayed conditional mutual information. Averaging gives the
exact loss $\Delta$. Conditional cross entropy is
$H_P(O_i\mid B_{i,A})+\mathcal D_{i,A}$. The definition of $r_i$
is the exact logarithmic slack in (COK.14). Substitute these three
equalities in the Gibbs identity. Zero-probability contexts contribute
zero to conditional relative entropy. Strict positivity of $Q$
makes all terms finite. $\square$

This identity is for the displayed sum and its own Gibbs law. It is
not an identity for unrelated local maximizers, different probability
laws or an arbitrary non-Gibbs law. In particular feasible local laws
need not be marginals of one law with $\Delta=0$.

## 4. Local minimax, fixed-weight effectivity and rational certificates

**Theorem 4.1 (exact local minimax).** For every nonempty $R_\eta(w)$,

$$
2^{h_\eta(w)}
=\inf_{\substack{Q_A>0\\ \sum_a Q_A(a\mid b_A)=1}}
   \max_{s\in R_\eta(w)}
       \frac{\Phi_\eta(s)}
            {\prod_AQ_A(O(s)\mid B_A(s))^{\gamma_k(A)}}.
\tag{COK.23}
$$

The infimum ranges over full owned-tuple kernels at all full contexts.
It need not be attained by strictly positive kernels.

Proof. Let $M=\prod_{c\in O}|T_c|$, with $M=1$ for empty $O$.
For $0<\varepsilon<1$ restrict every kernel entry to be at least
$\varepsilon/M$. This is a nonempty compact convex product of
polytopes. On its product with $\Delta(R_\eta)$ the function

$$
f(p,Q)=\mathbb E_p\log_2\Phi_\eta
                   -\sum_A\gamma_k(A)\mathbb E_p\log_2Q_A(O\mid B_A)
\tag{COK.24}
$$

is continuous, linear in $p$ and convex in $Q$. The compact convex
minimax theorem [Sion, Theorem 3.4][Sion] therefore exchanges
$\max_p\min_Q$ and $\min_Q\max_p$. For fixed $Q$, the latter maximum
is its largest pointwise logarithmic ratio in (COK.23).

For fixed $p$, unrestricted conditional cross entropy has infimum
$H_p(O\mid B_A)$. Smooth its conditional rows to
$(1-\varepsilon)p(a\mid b_A)+\varepsilon/M$, using uniform rows at
zero-probability contexts. Its cross entropy exceeds the entropy by
at most $-\log_2(1-\varepsilon)$. Since $\sum_A\gamma_k(A)=1$,
the restricted minimax logarithm lies between $h_\eta(w)$ and
$h_\eta(w)-\log_2(1-\varepsilon)$. Let $\varepsilon\downarrow0$.
Weak duality supplies the same lower bound for every positive
kernel, establishing both directions of (COK.23). $\square$

**Theorem 4.2 (effective approximation at a fixed rational weight).**
For fixed integer $d\ge1$ and rational $w:S_d\to[0,\infty)$,
$\Omega_d(w)$ is a computable real. For every rational
$C>\Omega_d(w)$, strictly positive normalized rational kernels
with common cap $C$ exist for every nonempty type. Conversely such
kernels imply $C\ge\Omega_d(w)$. These assertions include rational
weights with zeros; they do not assert effective optimization as the
support of $w$ varies.

Proof. Determine $F$, enumerate all finite decorations and test every
assignment for local reconstruction and the finite joint owner-image
conditions. All these operations terminate using rational support
tests and finite tables. The identically zero case is separate.
For a nonempty relation with $N$ assignments, put
$L=\max\log_2\Phi_\eta-\min\log_2\Phi_\eta$. For two laws at total
variation distance $t\le1/2$ and $N\ge2$,

$$
|F_\eta(p)-F_\eta(p')|
 \le 2h_2(t)+2t\log_2N+tL.
\tag{COK.25}
$$

Indeed each conditional entropy is the difference of two entropies
on alphabets of size at most $N$; apply the finite entropy continuity
bound to each. The expectation term is bounded by its oscillation
times $t$. Average with the coefficients summing to one.

A rational probability grid of denominator $M_0$ approximates every
law within total variation $(N-1)/M_0$. Choose $M_0$ so that this is
at most $1/2$ and the computable bound (COK.25) is below the requested
error. Evaluate the finite grid using computable logarithm enclosures,
with $0\log 0=0$. This produces terminating two-sided enclosures for
$h_\eta$, then for $\Omega_d(w)$ by finite maxima and exponentiation.
For $N=1$ the value is simply its log weight.

Theorem 4.1 gives positive real kernels whose pointwise maxima are
strictly below $C$. Positive normalized rational rows are dense in
the corresponding simplexes; finitely many strict inequalities
survive a sufficiently close rational approximation. The type list
is finite, so the same $C$ works throughout. Conversely take
expectations of any pointwise witness and use conditional relative
entropy as in (COK.20); this bounds every $F_\eta(p)$ by $\log_2C$.
No assertion about attaining the infimum at $C=\Omega_d(w)$ is
needed. $\square$

**Definition 4.3 (total rational certificate specification).** Define
$V_{\rm cond}(d,w,C,\pi)$ as follows. Its finite input requires an
integer $d\ge1$, a nonnegative rational weight array on the canonical
$S_d$, a rational $C>0$ and a finite certificate string $\pi$.
Malformed inputs are rejected. Recompute the complete canonical
finite type list and its $R_\eta(w)$. For every nonempty relation,
$\pi$ must supply every row of every kernel $Q_{\eta,A}$, indexed by
the full owned tuple and full context. Check that entries are positive
rationals and that every row sums to one. For each $s\in R_\eta$ put
$r=(k+1)!$ and check the exact rational inequality

$$
\Phi_\eta(s)^r
 \le C^r\prod_{A\subseteq[k]}
       Q_{\eta,A}(O(s)\mid B_A(s))^{\,|A|!(k-|A|)!}.
\tag{COK.26}
$$

Reject missing, duplicate, incorrectly indexed or additional malformed
data. Empty relations need no kernels. For $w=0$ accept precisely the
canonical empty witness, subject to the valid input checks.
Type order is that of Definition 2.2; subsets, contexts and tuple
entries use their induced finite lexicographic orders. A certificate
is the corresponding finite array of rational numerators and positive
denominators, with no implicit unspecified rows.

**Corollary 4.4 (totality, soundness and its exact completeness scope).**
The specification is a total decidable predicate on rational finite
inputs. Acceptance implies $A_n(w)\le C^n$ for every $n$ and every
complete native template. At fixed rational $w$ its accepted rational
caps have infimum $\Omega_d(w)$, and every rational $C>\Omega_d(w)$
has a certificate.

Proof. There are finitely many types, assignments and rational powers.
Every parsing, normalization and inequality test terminates. Taking
the positive $r$-th root of (COK.26) gives (COK.14); Theorem 3.1
proves soundness. Theorem 4.2 proves the infimum and density assertions.
They concern the finite local outer relaxation alone. $\square$

This is a mathematical verifier specification, not a modified or
implemented repository judge. The support tests depend on
$F=\operatorname{supp}w$. Removing zero-weight rows before logarithms
is valid for the present mass bound; it does not permit shrinking a
declared structural support in a different supplier theorem. No
continuity, rational optimizer approximation or effectiveness theorem
for support-varying minimization of $\Omega_d$ has been proved here.

## 5. Comparisons with the credited owner and joint bounds

**Definition 5.1 (the credited finite envelopes).** A nonempty
$P\subseteq S_d$ is range-feasible if $|g_q(P)|\le4$ for every $q$.
Let $H(P)$ contain exactly the targets not determined on $P$ by
any own boundary reply $r_a$, with constants also counted as easy.
Write

$$
Y_P(x)=(g_q(x))_{q\in H(P)},\qquad
b_y(P)=\sum_{\substack{x\in P\\Y_P(x)=y}}w(x),\qquad
\kappa_w(P)=\left(\sum_y b_y(P)^2\right)^{1/2}.
\tag{COK.27}
$$

The [JTC, Theorem 2.2][JTC] and [RCE, §§2–4][RCE] joint envelope is

$$
J_d(w)=\max_{\substack{\varnothing\ne P\subseteq\operatorname{supp}w\\
                       P\text{ range-feasible}}}\kappa_w(P).
\tag{COK.28}
$$

For $w=0$ its value is zero. Allowing declared zero-weight states in
the maximum has the same value by [RCE, Lemma 2.2][RCE]; this does not
remove those states from a structural hypothesis on a declared set.

For the [OCB, Definition 4.2][OCB] owner envelope set

$$
E(P)=\{q:g_q\text{ is a function of }r_q\text{ on }P\}.
\tag{COK.29}
$$

Its test supports are range-feasible nonempty $P$ on which
$(r_q)_{q\in E(P)}$ separates the states. $\mathcal U_d(w)$ is the
largest $w(P)$ over them, and is zero for $w=0$. This test family
is hereditary, so restricting to positive support leaves the maximum
unchanged. Neither these test supports nor range-feasible supports
are all asserted to be native admissible fibers.

**Theorem 5.2 (comparison with both credited envelopes).** For every
$d\ge1$ and every nonnegative $w$,

$$
\beta_d(w)\le\Omega_d(w)\le\min\{\mathcal U_d(w),J_d(w)\}.
\tag{COK.30}
$$

Proof of the owner comparison. Fix a nonempty local type and define
$M(a)=\max_{b:(a,b)\in R_\eta}\Phi_\eta(a,b)$, taking zero for
an empty fiber. Then

$$
F_\eta(p)\le H_p(O)+\mathbb E_p\log_2M(O)
             \le\log_2\sum_aM(a).
\tag{COK.31}
$$

The first inequality uses conditioning and the pointwise maximum;
the second is finite Gibbs domination. For each $a$ with $M(a)>0$
select one maximizing assignment and its actual $x_a$. The owner
identity makes $a$ a function of $x_a$, so these blocks are distinct.
Their set has range at most four at every target, by its one-seed
table. Every actual owned port is in $E(P)$, since its full factor
is its table of that same own reply. Those replies distinguish all
the selected $x_a$. Their mass is therefore at most
$\mathcal U_d(w)$. This works also with no owned seeds: there is at
most one selected state. Taking maxima proves the owner comparison.
The comparison with $J$ follows from the exact identity below;
(COK.16) supplies the first inequality. $\square$

**Theorem 5.3 (exact local-to-joint defect).** Fix any law $p$ on a
nonempty $R_\eta(w)$ and put $X=x(s)$, $P=\operatorname{supp}X$,
$O=O(s)$ and $Y=Y_P(X)$. Partition the hard-target coordinates of
$Y$ into $Y_1,\ldots,Y_k$ according to their prescribed incoming
actual owner group, allowing empty vectors. Then $Y_A=(Y_g)_{g\in A}$
is a function both of $X$ and of $B_A$. Define

$$
\begin{aligned}
\mathcal L_\eta(p)
={}&\sum_A\gamma_k(A)
 \left[H_p(X\mid O,Y_A)+I_p(O;B_A\mid Y_A)\right]\\
&+\frac12\sum_A\gamma_k(A)I_p(Y_A;Y_{A^c}).
\end{aligned}
\tag{COK.32}
$$

With $b_y=b_y(P)$ and $\kappa=\kappa_w(P)>0$, exactly

$$
\begin{aligned}
\log_2J_d(w)-F_\eta(p)
={}&\log_2\frac{J_d(w)}{\kappa}+\mathcal L_\eta(p)\\
&+\sum_y p_Y(y)
 D_2\!\left(p(X\mid y)\,\middle\|\,\frac{w(\,\cdot\,)}{b_y}
                       \text{ on the cell }y\right)\\
&+\frac12D_2\!\left(p_Y\,\middle\|\,(b_y^2/\kappa^2)_y\right).
\end{aligned}
\tag{COK.33}
$$

Every term on the right is nonnegative. In particular this gives the
second comparison in (COK.30).

Proof. A locally constant or owned-seed target is easy on $P$: the
owned seed is its actual own-port reply by (COK.7). A hard target
must therefore be assigned to an incoming seed, and hence to one
specified actual owner group. This justifies the partition. Since
$O$ is a function of $X$ and $Y_A$ is a function of both $X$ and
$B_A$, the chain rule gives the exact identity

$$
H_p(O\mid B_A)
=H_p(X)-H_p(Y_A)-H_p(X\mid O,Y_A)-I_p(O;B_A\mid Y_A).
\tag{COK.34}
$$

Complement symmetry of $\gamma$ gives

$$
\sum_A\gamma_k(A)H_p(Y_A)
=\frac12H_p(Y)+\frac12\sum_A\gamma_k(A)I_p(Y_A;Y_{A^c}).
\tag{COK.35}
$$

Thus

$$
F_\eta(p)
=H_p(X)-\tfrac12H_p(Y)+\mathbb E_p\log_2w(X)-\mathcal L_\eta(p).
\tag{COK.36}
$$

On the finite positive-support set $P$, conditional Gibbs identities
give

$$
\begin{aligned}
H_p(X)-\tfrac12H_p(Y)+\mathbb E_p\log_2w(X)
={}&\tfrac12H_p(Y)+\sum_yp_Y(y)\log_2b_y\\
&-\sum_yp_Y(y)D_2(p(X\mid y)\Vert w/b_y)\\
={}&\log_2\kappa-\tfrac12D_2(p_Y\Vert b_y^2/\kappa^2)\\
&-\sum_yp_Y(y)D_2(p(X\mid y)\Vert w/b_y).
\end{aligned}
\tag{COK.37}
$$

All nonempty cells have $b_y>0$, including when the hard vector is
empty. The support $P$ is range-feasible, since each local table has
at most four values. Hence $\kappa\le J_d(w)$. Combine (COK.36)
and (COK.37) to obtain (COK.33). $\square$

The identity does not assume that a local law extends globally.
When $p$ is an actual Gibbs marginal, it is compatible with the
single common law in Theorem 3.2; when $p$ is an independent local
maximizer it makes no such assertion. It isolates three distinct
losses: the joint cap's finite support comparison, losses in the
local ownership and incoming-group relations, and the weighted Gibbs
loss on that same local state support.

**Corollary 5.4 (precise local saturation conditions).** For
nonzero $w$ and a law $p$ as above,
$F_\eta(p)=\log_2J_d(w)$ if and only if all the following hold:

1. $\kappa_w(P)=J_d(w)$.
2. On $P$,
   $p_X(x)=w(x)b_{Y_P(x)}(P)/J_d(w)^2$.
3. $X$ is a function of the owned tuple $O$ on the positive law.
4. For every $A\subseteq[k]$, $O$ and $B_A$ are conditionally
   independent given $Y_A$.
5. The group vectors $Y_1,\ldots,Y_k$ are mutually independent.

Proof. All terms in (COK.33) must vanish. The two Gibbs terms vanish
exactly at the law in item 2. All coefficients $\gamma_k(A)$ are
positive. The $A=\varnothing$ term of (COK.32) forces
$H(X\mid O)=0$, and this also kills every $H(X\mid O,Y_A)$.
The remaining first-row terms are exactly item 4. The second row
vanishes if and only if every complementary split of the group
vectors is independent. This is equivalent to mutual independence:
split off the first group, then apply the other split equalities
to the remaining marginal, and induct. The reverse direction
follows from mutual independence of all groups. For $k=0$ or $1$
the split terms and independence requirements have their usual
vacuous meanings. These observations prove both directions. $\square$

## 6. Finite real-algebraic saturation at a fixed rational weight

**Theorem 6.1 (deciding saturation of the joint bound).** At fixed
$d\ge1$ and fixed nonzero nonnegative rational $w$, whether
$\Omega_d(w)=J_d(w)$ is decidable by a finite real-algebraic
feasibility problem. If equality fails, then $\Omega_d(w)<J_d(w)$,
and there is an effective search terminating with a rational
$C$ and rational conditional certificate such that

$$
\Omega_d(w)<C<J_d(w).
\tag{COK.38}
$$

This decides equality of two finite relaxations, not equality of
native pressure with either one.

Proof. Enumerate all nonempty range-feasible $P\subseteq F$.
Each $\kappa_w(P)^2$ is rational. Their finite maximum is
$J_d(w)^2>0$, so equality of a given squared norm to the maximum
is exactly testable. Enumerate each decoration $\eta$ and each $P$
attaining this squared maximum.

For each pair introduce variables $p_s$, $s\in R_\eta(w)$, with
$p_s\ge0$ and $\sum_sp_s=1$. All marginal probabilities below are
linear expressions in these variables. Impose

$$
p_X(x)=
\begin{cases}
w(x)b_{Y_P(x)}(P)/J_d(w)^2,&x\in P,\\
0,&x\notin P.
\end{cases}
\tag{COK.39}
$$

The positive right sides make $P$ exactly the support of $X$.
For the functional requirement $O\to X$ impose

$$
p_s p_t=0
\quad\text{whenever }O(s)=O(t)\text{ and }x(s)\ne x(t).
\tag{COK.40}
$$

Determine each hard target on this $P$ and its assigned incoming
group as in Theorem 5.3. If a supposed hard target were constant
or owned, this pair has no feasible law and is discarded. For
every $A,o,b,y$, impose

$$
p(O=o,B_A=b,Y_A=y)\,p(Y_A=y)
=p(O=o,Y_A=y)\,p(B_A=b,Y_A=y).
\tag{COK.41}
$$

These are precisely the finite conditional-independence equations;
at a zero context they give $0=0$ without division. Finally impose,
for every tuple of group-vector values,

$$
p(Y_1=y_1,\ldots,Y_k=y_k)=\prod_{g=1}^kp(Y_g=y_g).
\tag{COK.42}
$$

For zero groups this reads $1=1$, and for one it is a tautology.
All these are polynomial equations and inequalities with rational
coefficients in finitely many real variables.

Corollary 5.4 proves that a feasible pair is exactly a saturating
local law. Conversely, if $\Omega=J$, the finite maximum over
decorations and each compact simplex maximum are attained. A
maximizer therefore supplies one of the enumerated $P$ and solves
the displayed system. Existence is thus a finite disjunction of
existential formulas over real closed fields. Effective quantifier
elimination, as in [Basu, Theorem 2.1 and §2.1.1][Basu], decides it.

If every system is infeasible, attainment and (COK.30) imply a strict
gap. Theorem 4.2 computes shrinking enclosures for $\Omega$, and
$J$ is the square root of an explicit positive rational. Eventually
these enclosures separate. Choose a rational $C$ strictly between
them and enumerate rational positive normalized kernel arrays,
testing (COK.26). Corollary 4.4 ensures that this search terminates.
No complexity bound or execution of quantifier elimination is
asserted. $\square$

Even saturation of the finite relaxation need not be realized by
one common network law. Failure of saturation gives a strict
all-size improvement at that particular weight; it does not show
that minimizing weights change the optimized native rate. The
global defect (COK.22) and joint completion of the local laws
remain separate questions.

## 7. Exact original all-competitor consumer and paid correspondence

**Theorem 7.1 (memory lower bound against all original competitors).**
Let $d\ge1$, let $\mu$ be a rational probability on the entire
$S_d$, and suppose $V_{\rm cond}(d,\mu,C,\pi)$ accepts. Then
every correct original preparation and reader, for every $D\ge d$,
satisfies

$$
|E[\mathcal F_D]|\ge
 \left\lceil C^{-2^{D-d}}\right\rceil.
\tag{COK.43}
$$

Consequently

$$
M_1(D)\ge\left\lceil C^{-2^{D-d}}\right\rceil,\qquad
\lambda\ge-2^{-d}\log_2C,\qquad
\sigma_d\ge-\log_2\Omega_d(\mu).
\tag{COK.44}
$$

The mass-to-memory bridge is the credited [NPC, Theorem 7.1][NPC];
the new input is the constructed sound conditional-kernel cap.

Proof with the original quantifiers. In the right subtree of the
actual source use the fixed perfect scaffold of height $D-d$ with
$n=2^{D-d}$ present canonical $S_d$ blocks at its frontier. Every
tuple gives an actual member of $\mathcal F_D$. Restrict any
original complete-code fiber to this scaffold, retaining all its
correlations. For each requested block target its query is fixed by
the exported name, the public $D$ and the request, before the reply
and before any count. An arbitrary original-root word either stops
in the fixed part and is constant, or enters one actual donor block
with an arbitrary finite suffix. Canonical all-word simulation
reduces that suffix to a boundary reply in that same donor block
or a constant. No donor must equal the target block.

Correctness for every authentic subsequent $k$ means that equal
chosen replies on this entire fiber give the same full target
trajectory, hence the same $\Gamma$. Thus every nonempty restricted
fiber has complete native witnesses and is contained in a
$C_\Theta$. This argument permits different off-target donors for
different requests and imposes no independent-child code structure.
Under the one product block law $\mu^{\otimes n}$, its mass is at
most $C^n$ by Corollary 4.4. The restricted fibers partition a
space of total mass one. If their number is $m$, then $1\le mC^n$.
The complete attained original alphabet is at least $m$, proving
(COK.43). The rate and $\sigma_d$ conclusions follow from
(COK.11), or from the same cover-mass argument at every length.
For the last inequality take rational caps decreasing to
$\Omega_d(\mu)>0$. $\square$

No rival preparation algorithm is replaced in this lower bound.
In particular no seed vector, owner grouping, permutation, kernel
context or support descriptor is made available to its reader.
The kernels are source-independent mathematical proof tables.
The analytical product law is a counting device, not a paid
implementation or an independence restriction on code fibers.

**Proposition 7.2 (credited paid witness realization, with its costs).**
Finite representative covers in the exact RRN representation retain
the original paid realization, as follows.

For a full-family optimal canonical cover on $\mathcal F_D$, scan
the literal words $Rq$, $q\in W_D$. It uses at most

$$
2^D-1\text{ Reads},\qquad
Q_{\max}\le D,\qquad
\text{letters}\le (D-1)2^D+1.
\tag{COK.45}
$$

Export only the complete attained fixed-width cover name, and isolate
the scanned array and all other acquired dependence through the
declared paid service. [RRN, Theorem 7.1][RRN] preserves the exact
optimum; it does not preserve an old preparation cost. Preserving
exactly an arbitrary nonminimal original competitor's attained
cardinality can instead use [RRN, Corollary 7.2][RRN]'s fuller scan:

$$
2^{D+1}-1\text{ Reads},\qquad
Q_{\max}\le D+1,\qquad
\text{letters}\le D\,2^{D+1}+1.
\tag{COK.46}
$$

For public prefix-free present roots $Ra_i$, $|a_i|\le H$, of $n$
actual blocks, [RRN, Proposition 7.3][RRN] gives

$$
\begin{aligned}
\text{Reads}&\le n(2^d-1),\qquad Q_{\max}\le H+d,\\
\text{letters}&\le
n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\end{aligned}
\tag{COK.47}
$$

A nonconstant representative late query is the one original literal
$Ra_jq_{\rm owner}$, selected before reply and count; a constant
branch uses zero Reads.

Proof of the correspondence used here. The scans acquire the
boundary reply arrays by actual original-root Reads. Constructor
reconstruction and canonicalization then compute the canonical
tuple and its joint cover name, using source-independent tables.
This does not independently recolor its children. Every seed is
recovered only at its actual owner port. Its table gives the full
requested factor after that one paid reply; (COK.5) answers all
subsequent counts. For present occurrences, homomorphic substitution
gives

$$
r_{\rho^kt}(Ra_iq)=
r_{\rho^k(t|_{Ra_i})}(q)\qquad(k\ge0).
\tag{COK.48}
$$

Here subtree notation is mathematical identification, not an input
port. Presence is exactly the premise of
original_present_transport in [NativeDepthPatterns][D5N].
An absent root is not transported as a subtree. Artificial wrapper
roots and their fixed left cones contribute public constants, and
all actual queries are translated back to original literals.

The suffix-length identity
$\sum_{\ell=0}^{d-1}\ell2^\ell=(d-2)2^d+2$ gives (COK.47);
the same count at the full-family root gives (COK.45) and (COK.46).
When $H+d\le D$, all the block targets are permitted original
targets. A cover serving those targets alone does not serve every
other target of $\mathcal F_D$; the full-family statement uses the
credited RRN theorem. $\square$

Preparation work, installation and lookup storage, workspace, source
isolation, lawful entry, handoff and authentic count input remain
separate charged resources or declared services. All surviving
source-dependent control and allocation are included in the export;
the proof does not physically erase them for free. Separately a
factor predictor needs at most
$\lceil\log_2(2D+1)\rceil+1$ bits. None of these results bounds
physical time or gives free total efficiency.

## 8. Two actual blocks: a sharp network cap with unchanged universal pressure

**Theorem 8.1 (an exact conditional calculation on an actual network).**
At $d=2$ write $\operatorname{bit}(0)=\alpha$,
$\operatorname{bit}(1)=\beta$ and
$u_{ab}=\langle\operatorname{bit}(a),\operatorname{bit}(b)\rangle$.
On the full $S_2$ use the probability

$$
\mu(u_{ab})=
\begin{cases}
2/6,&a=b,\\
1/6,&a\ne b,
\end{cases}
\qquad
\mu(x)=0\quad\text{otherwise}.
\tag{COK.49}
$$

Take two actual blocks. Seed $a$ is owned at the first block's
$L$ port and seed $b$ at the second block's $R$ port. Both root
factors are the constant branch factor, both $L$ factors are those
of $\operatorname{bit}(a)$, and both $R$ factors those of
$\operatorname{bit}(b)$. These are legal actual full-factor tables,
with the owner reply identities. The seed values are the actual
replies $\operatorname{bit}(a),\operatorname{bit}(b)$; $a,b$ are only
their indices. The domains are $\{\alpha,\beta\}$ with the credited
RRN guards in the inverse complete template. The complete solution set
and its mass are exactly

$$
C_\Theta=\{(u_{ab},u_{ab}):a,b\in\{0,1\}\},\qquad
Z=\sum_{a,b}\mu(u_{ab})^2=\frac5{18}.
\tag{COK.50}
$$

Each block has one incoming actual owner group, so the two coefficients
are $1/2$. For its owned bit $o$ and incoming bit $b'$ choose

$$
Q_\varnothing(o)=\frac12,\qquad
Q_{\{1\}}(o\mid b')=
\begin{cases}4/5,&o=b',\\1/5,&o\ne b'.\end{cases}
\tag{COK.51}
$$

With $C_i=\sqrt{5/18}$ the pointwise conditional inequality is an
equality. Thus its product bound is the exact $5/18$, whereas the
owner-only local constants give $(2/3)^2=4/9$.

Proof. The three depth-two ports prescribe precisely a branch with
the two specified actual leaf labels, hence each block is $u_{ab}$.
Conversely each of the four assignments satisfies every equation,
and its owner replies recover its unique lift. In either block,
for equal bits $\Phi_i^2=1/9$ and for unequal bits $\Phi_i^2=1/36$.
Directly from (COK.51),

$$
\Phi_i^2=\frac5{18}\,Q_\varnothing(o)Q_{\{1\}}(o\mid b').
\tag{COK.52}
$$

Taking square roots gives (COK.14). For the owner-only bound, at
each owned bit the largest incoming weight is $1/3$; summing
over the two owned bits gives $2/3$.

The actual Gibbs law is proportional to $\mu(u_{ab})^2$:
each equal pair has probability $2/5$, each unequal pair $1/10$.
Both owned marginals are uniform and their actual conditional rows
are exactly (COK.51). Each incoming tuple is the whole other owner
tuple, so the chain-rule loss $\Delta$ is zero. The conditional
relative entropies and the pointwise slack in (COK.22) are zero
as well, confirming equality under one common law. Rational caps
strictly above each algebraic $C_i$ give rational pointwise witnesses
arbitrarily close to this network bound. $\square$

**Proposition 8.2 (the same law has $\beta_2=1$).** For the very same
$\mu$ of (COK.49),

$$
A_n(\mu)=1\quad(n\ge1),\qquad
\beta_2(\mu)=\Omega_2(\mu)=J_2(\mu)=1.
\tag{COK.53}
$$

Proof. On $U=\{u_{00},u_{01},u_{10},u_{11}\}$, the root factor is
constant branch and each side factor is determined by that same side's
own actual reply. Hence $U^n$ has simultaneous self-donor native
witnesses for all targets. Its product probability is one. Saturating
these witnesses gives a complete template still of mass one, while no
subset of a probability space has mass above one. This proves the
$A_n$ and $\beta$ statements. Each joint cell norm is at most its
support mass, hence $J_2(\mu)\le1$. Apply
$\beta_2\le\Omega_2\le J_2$ to get all the equalities. $\square$

The sharp bound in Theorem 8.1 is for that particular network.
It cannot be used as a universal cap below one for this law. An
exhaustive conditional certificate includes the self-read local
decorations of Proposition 8.2. Their presence precludes this false
inference, even though the two-block conditional calculation is sharp.

**Proposition 8.3 (a paid full-variable-shape witness).** On the
original $\mathcal F_3$, there is a jointly correct procedure with
exactly $120$ attained names realizing the four-state fiber of
Theorem 8.1. It uses seven preparation Reads, maximum address length
three and seventeen submitted letters. This is a nonoptimal witness;
the credited exact value is $M_1(3)=4$.

Proof. $|S_2|=11$ and $|S_3|=2+11^2=123$. Merge the four canonical
right subtrees $\langle u_{ab},u_{ab}\rangle$ into one code name and
give each of the other $119$ canonical states its own name. Scan
all $Rq$, $|q|\le2$, by the seven literal Reads in (COK.45).
These replies compute $\pi_3(v)$ and its name for every original
$v$ of height at most three. The scan letters total
$1+2\cdot2+4\cdot3=17$. Canonicalization preserves every requested
factor, so no variable shape is discarded. Every canonical state
is attained by an actual source, giving exactly $120$ attained names.

For the merged name, the targets $R,RL,RR$ have constant branch
trajectories. For targets $RLL$ and $RRL$, make the one original
query $RLL$ to obtain the actual owner reply for $a$. For targets
$RLR$ and $RRR$, make the one query $RRR$ to obtain $b$. These
queries are chosen from the name and request before their replies
and before any count. Decode the leaf factor from the reply, then
use (COK.5) for every authentic subsequent count. Singleton names
already determine every full factor and use zero Reads.

All scanned arrays, temporary selectors and other acquired
distinctions are removed from accessible state by the paid isolation
service. Fixed public control and installed tables are common.
The complete retained alphabet is the displayed $120$ names, not
an uncounted name plus a surviving scan buffer. No preparation-cost
optimality, physical erasure theorem or free isolation is claimed.
$\square$

## 9. Credited depth-two closure and the unresolved all-depth relation

**Convention 9.1 (additional public supplier at its exact pin).** The
additional [RCE, §§12–16][RCEnew] are public at
292c09e25e3a1659e17174a95383ae5606fd3371, PR 17390.
Their statements are documentary checked mathematical suppliers,
not independently proof-reviewed or Lean certified here. They are
credited inputs, not results of this volume.

RCE Theorem 12.3 says: for any depth and nonempty declared $P$,
if every permitted experiment attains at most two actual replies
on all of $P$, then each complete temporal target is constant or
decoded from one own-coordinate reply. The number two counts
attained replies of each experiment; it does not authorize two
calls. The premise and decoders include every declared state,
including zero-weight ones.

RCE Theorem 14.3 and Corollary 15.1 give, for arbitrary nonnegative
full block weights on the entire $S_2$, with

$$
W=\sum_{x\in S_2}w(x),\quad a=w(\alpha),\quad b=w(\beta),\quad
t=\max_{g\in S_2\setminus\{\alpha,\beta\}}w(g),\quad
M(w)=\max\{W-a,W-b,a+b+t\},
\tag{COK.54}
$$

the exact equalities

$$
J_2(w)=\beta_2(w)=M(w),\qquad
\max_\Theta\sum_{x\in C_\Theta}\prod_iw_i(x_i)
   =\prod_iM(w_i).
\tag{COK.55}
$$

These include mixed full block weights, zeros and every length.
Corollaries 15.2–15.3 state that the complete existing
recursive-plus-range rational certificate at depth two accepts
exactly $C\ge M(\nu)$, and its optimized endpoint is
$c_+(2)=b_2=17/25$. The attaining law has
$\nu(\alpha)=\nu(\beta)=8/25$ and weight $1/25$ on each of the nine
branch states. The numerical optimum is credited there to NCM/NPC.
RCE §16 retains the all-depth cofinality and effective-convergence
questions. None of these supplier proofs is reproduced here.

**Corollary 9.2 (location of the new family relative to that closure).**
For every nonnegative $w$ on $S_2$,

$$
\Omega_2(w)=J_2(w)=\beta_2(w)=M(w).
\tag{COK.56}
$$

Proof. Insert the credited (COK.55) in the sandwich (COK.30).
The identically zero case uses the zero conventions. $\square$

Thus completeness of the new conditional family at depth two, in
the sense of its cap infimum, is already forced by the credited
closure. It supplies no new optimized rate progress at that depth.
The old recursive-plus-range grammar additionally accepts the exact
rational boundary cap; Corollary 4.4 asserts all strict rational
caps above the local value and does not assert boundary attainment
by strictly positive kernels. Further particular-network effects at
$d=2$, including §8, do not change the optimized endpoint.

**Open problem 9.3 (joint completion and optimizer-cofinality).** Put

$$
b_d=\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\qquad
b_{\rm cond}^{\mathbb Q}(d)=
 \inf_{\mu\in\Delta(S_d)\cap\mathbb Q^{S_d}}\Omega_d(\mu).
\tag{COK.57}
$$

The sound certificate specification gives
$b_{\rm cond}^{\mathbb Q}(d)\ge b_d$. Optimizer-cofinality of this
particular family would require equality: for every rational
$\epsilon>0$ there would be rational $\mu,C$ and an accepted
certificate with $-\log_2C>\sigma_d-\epsilon$. That equality is
unproved at general depth. Even equality of the corresponding
infima over real weights would require a justified rational
approximation bridge for the support-dependent local family;
Theorem 4.2 alone supplies none.

The concrete missing relation is compatibility of local laws across
their shared actual owner blocks, with their full joint weights,
guards and actual-tree zeros retained. A locally feasible law in
(COK.13), or a solution of the algebraic saturation system, need
not be the marginal of any global solution law. Even a jointly
realizable collection may have positive global loss $\Delta$ in
(COK.22). No uniform control of these losses or global completion
theorem has been supplied. The exact identities identify the
remaining obligations without treating soft local assignments as
native implementations.

For a chosen rational weight, Theorem 6.1 offers a finite test:
if every joint-bound saturation law is excluded, one obtains a strict
rational all-size cap at that weight. If saturation is feasible,
the law explicitly identifies the functional and independence
conditions that a further joint rule must constrain. Neither
outcome settles weight-optimized coverage. Increasing unrelated
local samples or a finite checked network size does not impose
the missing shared realization.

[SIR][SIR] gives an exact counted high-incidence reduction, with
regularized semantic quantities approaching the original rate
from above within $2/(L+1)$, uniformly in depth. The present family
is sound without any incidence restriction and therefore also on
each bounded-incidence subfamily. This does not construct the
cofinal verifier needed by SIR's conditional transfer. Fixed
$d,L$ still permits arbitrary sizes, cycles, shared seeds, guards,
hard zeros and full correlated block weights. Bounded incidence
does not here establish bounded width, hyperfiniteness, mixing,
positivity, a fixed transfer matrix or an optimizer length cutoff.

**Convention 9.4 (unchanged original goals and known results).** The
credited bounds remain

$$
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16},
\qquad M_1(3)=4.
\tag{COK.58}
$$

[NCE][NCE] supplies the all-cyclic lower; [D3][D3] supplies the
upper and exact depth-three memory value. [NCM][NCM] supplies
$\sigma_2=\log_2(25/17)$. No new numerical endpoint is obtained.
The exact sharp original $\lambda$, general exact $M_1(D)$,
all-depth optimizer-cofinality, effective length tails and full
minimal-relations/internal-observer/mutual-recovery programme
remain open.

The new original-task consequence concerns what a boundary observer
can recover from a complete retained name and at most one actual
reply: the requested full temporal factor, then every future reply.
It neither recovers an arbitrary whole source nor identifies an
unobserved age or physical space and time. Space, time, boundary and
memory are not declared mutually recoverable merely from this
conditional pressure inequality.

## 10. Attribution, source bridges and evidence limits

**Convention 10.1 (existing and new mathematical content).** The
native representation and paid task are existing suppliers.
RRN supplies the exact guarded owned-seed normal form, both pressure
directions and paid scans; CBN supplies actual constructor
compatibility and once-owned potentials; NPC supplies semantic
minimax, rational weight approximation for native pressure and the
all-competitor memory consumer. None is reintroduced as a new result.
The new repo-derived deductions are the finite actual-owner-group
outer family, conditional-kernel all-size rule, its exact global
loss, local minimax and fixed-rational-weight effectivity, rational
certificate specification, exact local-to-$J$ defects and finite
algebraic saturation criterion, together with their displayed
original-task use and the scoped paid example.

OCB's owner-only envelope and same-law entropy accounting are
credited intermediates. JTC and RCE supply $J$ and its product,
scaffold and old-grammar boundaries. The conditional rule changes
the local domination to full owned-tuple conditional kernels,
retaining the whole block potential. It does not assert an
additional separable-majorant factorization. [JPL][JPL]'s
specified separable-majorant and core-atlas barriers remain within
their stated grammars. NDR's fixed-interface component obstruction
and lawful reblocking boundary do not prohibit this family or
arbitrary global recoloring. [SRP][SRP]'s one-residual theorem and
[GCB][GCB]'s scoped graph-cover statements do not supply unrestricted
cofinality. These distinctions preserve the source-specific consumer
instead of treating a general entropy theorem as the new content.

**Convention 10.2 (mature primary machinery and transfer limits).**

| Primary source | Used correspondence and boundary |
| --- | --- |
| Madiman and Tetali, Information Inequalities for Joint Distributions, with Interpretations and Applications, version 2, Proposition II and Theorem I-prime [MT][MT] | Finite entropy, chain conditioning and fractional-order comparisons on one joint law. Sections 3 and 5 prove the particular owner-group coefficients and native weighted identities; no independent marginal laws are substituted. |
| Sion, On general minimax theorems, Pacific Journal of Mathematics 8(1), Theorem 3.4 [Sion][Sion] | Finite compact convex domains, continuous objective, linear dependence on the law and convex dependence on the positive kernels. Section 4 regularizes the boundary before taking the limit; no all-network extremum is exchanged. |
| Basu, Algorithms in Real Algebraic Geometry: A Survey, version 1, Theorem 2.1 and §2.1.1 [Basu][Basu] | Effective quantifier elimination for finite rational polynomial formulas. Section 6 supplies that exact formula, including zero-context conditional independence; it gives no decision of arbitrary-size native pressure. |
| Abo Khamis, Ngo and Suciu, What Do Shannon-type Inequalities, Submodular Width, and Disjunctive Datalog Have to Do with One Another?, version 3 [AKNS][AKNS] | Entropy, functional dependencies and degree constraints for a fixed finite query schema. These motivate retaining common-law joint constraints; they provide no uniform optimizer-cofinal transfer across all native network sizes. |

Entropy nonnegativity, conditional relative entropy, finite Gibbs
variational identities, compact convex minimax and real-algebraic
decision are mature machinery. Their native source-specific bridge
is the actual owner partition, actual outside-owner grouping,
joint owner-image tests, once-owned $\Phi_i$ and the original-root
all-competitor argument. The new claims are repo-derived; the
bounded search is not a worldwide novelty assertion.

Graph partition approximation does not supply a missing theorem
under the present hypotheses. [Barvinok–Soberon][BS] studies
per-input near-one edge weights with a degree-dependent zero-free
condition. [Borgs–Chayes–Kahn–Lovász][BCKL] obtains pressure
convergence under its bounded-degree high-temperature conditions.
[Hatami–Lovász–Szegedy][HLS] studies local-global graph limits and
a hyperfinite implication. Hard compatibility zeros, arbitrary
joint weights and arbitrary native overlap do not establish those
conditions. No all-graph extremum cutoff, native hyperfiniteness
or noncomputability conclusion is transferred. The inspected
literature does not close the specified gap; that bounded statement
is not a claim of nonexistence.

**Convention 10.3 (exact D5 hypotheses, without a certification claim).**
The declaration original_present_transport in
[NativeDepthPatterns][D5N] assumes an actual present subtree;
original_prefix_locality assumes equality of replies through the
requested length. Section 7 uses presence and canonical reply
preservation, and supplies no new access port.

In [FiniteNaturalJoin][D5J], join_covers assumes both Covers
conditions on the same full assignment. It supplies no automatic
nonempty global realization, weighted all-size estimate or paid
native bridge. The local outer family is not made exact by
calling its compatible rows a join.

The finite_root_minimax declaration in
[NativeFiniteRootMinimax][D5M] concerns a finite actual three-reply
chart and complete predecessor-row recovery.
effective_native_birth_provenance and returned_native_reader in
[NativeEffectiveRootCriterion][D5E] concern a prefix-free cut, a
complete row with nonempty OriginFiber, $r\ge1$ and compatible
acquired image values after a certified actual substitution. Their
[minimax Blueprint][BM] and [criterion Blueprint][BE] use a
different target and source handoff. No bridge from those declarations
to an all-length stationary-source cap is established. Reading those
hypotheses is not compiling or formally certifying this volume.

**Convention 10.4 (limits of the finite examples).** The four-solution
network of Theorem 8.1 has mass $5/18$ and owner-only product $4/9$;
Proposition 8.2 supplies the same-law mass-one self-read family, and
Proposition 8.3 supplies the $120$-name full-variable-shape construction
with its stated paid resources. These examples and their proofs do not
determine the full local-type maximum at arbitrary depth, settle all
instances of the saturation criterion, establish higher-depth strict
improvement or yield convergence of native pressure.

The arbitrary-depth and all-size assertions rest on the proofs in
§§3–7. No optimizer-cofinality, effective length tail, empirical
convergence or Lean certification follows from these finite examples.

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[RRN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[OCB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OVERLAP_CLOSURE_BOUNDARIES.md
[SIR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SEED_INCIDENCE_REDUCTION.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[SRP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[RCE]: https://github.com/the-omega-institute/trureturing/blob/76e56d4505199480f6a995a3a96dfba7fe719fe3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[RCEnew]: https://github.com/the-omega-institute/trureturing/blob/292c09e25e3a1659e17174a95383ae5606fd3371/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[JPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_POTENTIAL_LIMITS.md
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5J]: ../../../D5/S0/Certificates/FiniteNaturalJoin.lean
[D5M]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean
[D5E]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[BM]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.md
[BE]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.md
[MT]: https://arxiv.org/html/0901.0044v2
[Sion]: https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf
[Basu]: https://arxiv.org/html/1409.1534v1
[AKNS]: https://arxiv.org/html/1612.02503v3
[BS]: https://arxiv.org/abs/1406.1771v3
[BCKL]: https://arxiv.org/abs/1002.0115v1
[HLS]: https://arxiv.org/abs/1205.4356v2

## 追加锚（本行以下为增补区）
