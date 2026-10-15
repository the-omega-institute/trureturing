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

## 11. Whole-owner projection edges and finite native covers

**Convention 11.1 (scope and fixed suppliers).** Sections 11–17 give
ordinary mathematical cover-completion and counting results for the
unchanged task of Definition 1.2. The native representation, canonical
scan, and constant-composition capacity are the credited
[RRN][RRNbase], [FMR][FMRbase], and [NPC][NPCbase] results at public
revision `91170b89dfe9dd7eadc64d14d86d2157ed14abdf`. The abstract
rational-lift and averaged-cover principles are mature results of
[Vontobel][VontobelCOK], with the exact correspondence specified in
§17. Completion below changes the finite network by taking a cover.
It does not assert completion on its original base, an upper bound
on individual covers, or an optimizer-cofinal native cap.

**Definition 11.2 (whole-owner edge data).** Fix $d,n\ge1$ and any
valid owned-seed network $\mathcal N$ of Definition 1.4, with all seed
domains nonempty. Retain its actual owner ports, every prescribed
table, constants, and arbitrary nonnegative whole-block weights
$w_i:S_d\to[0,\infty)$. Order each seed tuple by a fixed public
ordering. Let $O_i$ contain all seeds owned at block $i$. For each
distinct outside owner $j\ne i$ whose seeds occur at block $i$, let
$B_{ji}$ be the entire tuple of those seeds, counting each distinct
seed once. Put

$$
\begin{aligned}
E&=\{(j,i):j\ne i,\ B_{ji}\ne\varnothing\},\\
I_i&=(B_{ji})_{(j,i)\in E},\qquad
\operatorname{pr}_{ji}:\prod_{c\in O_j}T_c
       \longrightarrow\prod_{c\in B_{ji}}T_c.
\end{aligned}
\tag{COK.59}
$$

There is one directed edge for an entire outside-owner group.
Different groups may use overlapping projections of $O_j$; their
shared coordinates remain the same variables. References to an own
seed stay internal to its block. In particular $O_i,I_i$ are disjoint
tuples whose union has at most $m_d=2^d-1$ seeds.

Let $R_i$ consist of assignments $a=(o,b)$ to $(O_i,I_i)$ whose
entire prescribed local factor vector reconstructs an actual
$x_i(a)\in S_d$. Write

$$
R_i^+=\{a\in R_i:w_i(x_i(a))>0\}.
\tag{COK.60}
$$

Thus neither actual-tree compatibility nor a weight zero is filled.
No outside-owner-image condition is imposed in $R_i$ itself.
It will follow on positive matching laws from actual owner tuples.

**Definition 11.3 (joint matching polytope).** A collection of local
probability laws $p=(p_i)$, with $p_i\in\Delta(R_i)$, is matching if
for every $e=(j,i)\in E$ the following equality holds as a law of the
whole tuple $B_{ji}$:

$$
\pi_e:=(B_{ji})_*p_i
       =(\operatorname{pr}_{ji}O_j)_*p_j.
\tag{COK.61}
$$

Let $\mathcal P(\mathcal N)$ be this polytope and let
$\mathcal P^+(\mathcal N;\boldsymbol w)$ restrict $p_i$ to $R_i^+$.
Both are finite rational polytopes, possibly empty. Their defining
equations have integer coefficients even when the positive weights
are real: the weights select only the finite support in (COK.60).
Equality of separate seed marginals is not the matching condition.

**Definition 11.4 (group-permutation cover).** For $m\ge1$, choose
one permutation $\sigma_e\in\operatorname{Sym}([m])$ independently
for every $e\in E$. The cover $\mathcal N^\sigma$ has blocks $(i,k)$,
$k\in[m]$. Block $(i,k)$ owns a copy $c_k$ of each $c\in O_i$ at
the copied actual owner port. Its own-seed references use these
copies. If $e=(j,i)$, all occurrences of all seeds in $B_{ji}$ at
$(i,k)$ use their copies owned together at $(j,\sigma_e(k))$.
Every copied table and constant is unchanged, and block $(i,k)$
receives the one whole weight $w_i$.

Distinct copied seeds still have distinct actual owner ports and obey
(COK.7). Hence [RRN, Theorem 5.2][RRNbase] translates every such
cover back to a complete native template on $nm$ actual blocks,
with one lift per actual tuple and exactly its original product
weight. Here a cover describes a family of possible tuples; it is
not an operation copying an unknown physical source.

## 12. Constructive completion on covers and exact incidence

**Theorem 12.1 (empirical finite-cover completion).** Let
$p_i\in\Delta(R_i)$ be rational, and let $m$ be any common
denominator, so every $mp_i(a)$ is an integer. Then $p$ satisfies
(COK.61) if and only if some $m$-sheet group-permutation cover has
one actual solution whose empirical local law on the copies of
each $i$ is exactly $p_i$. Consequently matching is equivalent to
empirical realization on some finite such cover. The assertion
also holds on the positive supports $R_i^+$.

Proof. Choose a list $a_{i,1},\ldots,a_{i,m}$ with empirical law
$p_i$. At $e=(j,i)$ and for each whole group value $b$, matching
says that the sets

$$
\{k:B_{ji}(a_{i,k})=b\},\qquad
\{\ell:\operatorname{pr}_{ji}O_j(a_{j,\ell})=b\}
\tag{COK.62}
$$

have equal cardinality. Match them bijectively, separately for each
$b$, to obtain $\sigma_e$. Do this for every edge. At $(i,k)$,
assign its owned seeds $O_i(a_{i,k})$. Every incoming group then
equals the corresponding group of $a_{i,k}$ by (COK.62), including
all repeated occurrences of its seeds. Thus all copied local
configurations are the selected $a_{i,k}$ and are actual compatible
blocks. Their owner replies give a unique actual tuple by RRN.
Membership in $R_i^+$ additionally makes its product weight positive.

Conversely, in any actual cover solution, $\sigma_e$ is a bijection
between recipient copies and owner copies. Counting each whole group
value at both ends gives (COK.61). Its empirical counts are exactly
those of the asserted $p_i$. This proves necessity and sufficiency,
without requiring independent owner coordinates or an acyclic graph.
The matchings are finite effective constructions from rational lists.
$\square$

**Theorem 12.2 (identical local laws at every copy).** For rational
$p_i\in\Delta(R_i)$, matching is also equivalent to the existence
of a finite group-permutation cover and a probability law on its
actual solutions such that every copy of $i$ has local marginal
exactly $p_i$. If $m$ is a common denominator, a cover with $m!$
sheets suffices. The law can have at most $m$ outcomes.

Proof. Use the lists and permutations in Theorem 12.1. Compose
permutations right to left. Index the sheets by
$g\in\operatorname{Sym}([m])$ and wire the edge $e=(j,i)$ from
$(i,g)$ to $(j,\sigma_e g)$. This is a bijection of the sheet set.
For a uniformly chosen $h\in\operatorname{Sym}([m])$, prescribe
at $(i,g)$ the local configuration

$$
a_{i,(gh)(1)}.
\tag{COK.63}
$$

The owner at the other endpoint has configuration
$a_{j,(\sigma_egh)(1)}$. The matching equation from the original
lists holds at $k=(gh)(1)$, so every group agrees and every outcome
is an actual solution. For fixed $g$, $(gh)(1)$ is uniform on
$[m]$, giving exactly $p_i$. The outcome depends only on $h(1)$,
so there are at most $m$ outcomes. Conversely equal copy marginals
on an actual cover must give the same distribution at both ends of
every shared group, which is precisely (COK.61). $\square$

This construction provides prescribed local marginals on another
network. It supplies no law on the unlifted base. Its global entropy
is at most $\log_2m$; it need not be a Gibbs law or have the large
solution multiplicity established by averaging in §13. Those two
completion mechanisms must be distinguished when using COK.22.

**Proposition 12.3 (prescribed incidence is preserved exactly).**
For every group-permutation cover, a copied seed has exactly the
prescribed block incidence of its base seed. In particular covers
of a network in [SIR, Definition 2.2][SIRbase]'s
$\mathfrak N_{d,L}(n)$ lie in $\mathfrak N_{d,L}(nm)$.
The same assertion holds for the $m!$-sheet construction.

Proof. Let $c$ be owned at $j$ and fix its owner copy $(j,\ell)$.
It occurs in that block. For each other base block $i$ containing
$c$, the whole edge $(j,i)$ routes it to exactly the recipient
copy $k=\sigma_{ji}^{-1}(\ell)$. All of its occurrences in that
recipient block stay together. It occurs in no other copies of $i$.
Distinct base blocks give distinct copied blocks. Thus the incidence
is one plus the number of distinct outside base recipients, exactly
the original incidence. Assigned constant tables still count in this
argument, as SIR requires. Internal repeated references add no block.
For any sheet set and edge bijections, including left multiplication
on $\operatorname{Sym}([m])$, the same inverse-bijection argument
applies. $\square$

## 13. Exact weighted cover counting and its averaged exponent

**Definition 13.1 (type-restricted partition sum).** For rational
$p\in\mathcal P^+(\mathcal N;\boldsymbol w)$ and an admissible
denominator $m$, put

$$
\operatorname{Mult}(m,p)=\frac{m!}{\prod_a(mp(a))!}.
\tag{COK.64}
$$

Let $Z_p(\mathcal N^\sigma;\boldsymbol w)$ sum the product weights
of actual cover solutions whose empirical local law at copies of
every $i$ is $p_i$. Let $\mathbb E_\sigma$ mean the average over
the $(m!)^{|E|}$ independently uniformly permuted labeled full
group edges. Different permutation tuples count separately even
when the resulting native equations happen to coincide. The
averaging is an analytical finite ensemble, not a randomized
preparation on the unknown source.

**Theorem 13.2 (whole-group weighted type identity).** With these
definitions, exactly

$$
\mathbb E_\sigma Z_p(\mathcal N^\sigma;\boldsymbol w)
=\frac{\prod_i\operatorname{Mult}(m,p_i)}
       {\prod_{e\in E}\operatorname{Mult}(m,\pi_e)}
 \prod_i\prod_{a\in\operatorname{supp}p_i}
       w_i(x_i(a))^{mp_i(a)}.
\tag{COK.65}
$$

Each denominator is the multinomial of one whole group law, not
the product of its individual seed multinomials. Arbitrary zeros
outside $R_i^+$ and arbitrary correlations within $w_i$ are allowed.

Proof. There are $\operatorname{Mult}(m,p_i)$ labeled local lists
of type $p_i$. Fix all the lists. For $e=(j,i)$, their edge counts
match. The number of permutations matching every whole value $b$
is $\prod_b(m\pi_e(b))!$, out of $m!$. The matching probability
is therefore $1/\operatorname{Mult}(m,\pi_e)$. For these fixed
lists, different edges choose their permutations independently,
so these probabilities multiply. This independence is only between
public edge permutations conditional on fixed lists; no source,
seed, incoming group, or solution coordinates are assumed independent.

If all edges match, assign each copied owner its value from its own
local list. Incoming values agree by construction and every local
configuration is actual. Conversely an actual seed assignment
determines all local lists. Two edge-consistent list collections
cannot produce the same actual tuple, because the tuple's actual
owner replies recover every copied seed and hence every incoming
entry. This proves a bijection, with no hidden multiplicity from
noninjective nonowner tables. Each such list collection has the
fixed weight on the right of (COK.65). Summing over the lists proves
the identity. Every copied joint potential occurs exactly once.
$\square$

**Definition 13.3 (cover entropy and energy).** For any positive
matching laws, define

$$
\begin{aligned}
H_{\rm cov}(p)&=\sum_i H(p_i)-\sum_{e\in E}H(\pi_e),\\
\mathcal B_{\mathcal N}(p;\boldsymbol w)
 &=H_{\rm cov}(p)+\sum_i\mathbb E_{p_i}\log_2w_i(x_i),\\
r(p)&=\sum_i|\operatorname{supp}p_i|,\qquad
t(p)=\sum_{e\in E}|\operatorname{supp}\pi_e|.
\end{aligned}
\tag{COK.66}
$$

The first quantity can be negative. Log weights are evaluated only
on their positive support, so the second is finite there.

**Corollary 13.4 (explicit finite multiplier loss).** For rational
matching laws and every admissible denominator $m$,

$$
\begin{aligned}
m\mathcal B_{\mathcal N}(p;\boldsymbol w)-r(p)\log_2(m+1)
&\le\log_2\mathbb E_\sigma Z_p(\mathcal N^\sigma;\boldsymbol w)\\
&\le m\mathcal B_{\mathcal N}(p;\boldsymbol w)+t(p)\log_2(m+1).
\end{aligned}
\tag{COK.67}
$$

Proof. For a probability type on $s$ supported symbols, the finite
method-of-types estimate used in [NPC, (NPC.19)][NPCbase] is

$$
(m+1)^{-s}2^{mH(p)}\le\operatorname{Mult}(m,p)\le2^{mH(p)}.
\tag{COK.68}
$$

For completeness, under iid $p$ the type $mp$ is a modal type:
comparing any type to it gives a product of factorial ratios at
most one. There are at most $(m+1)^s$ types. Its probability is
therefore at least $(m+1)^{-s}$ and at most one, while every word
of this type has probability $2^{-mH(p)}$. This proves (COK.68).
Apply its lower numerator and upper denominator bounds to (COK.65),
then its upper numerator and lower denominator bounds for the other
direction. The fixed energy term supplies (COK.67). $\square$

**Theorem 13.5 (fixed-base averaged-cover pressure).** At this fixed
base network and fixed nonnegative whole-block weights,

$$
\limsup_{m\to\infty}
 \left(\mathbb E_\sigma Z(\mathcal N^\sigma;\boldsymbol w)\right)^{1/m}
=2^{\max_{p\in\mathcal P^+(\mathcal N;\boldsymbol w)}
          \mathcal B_{\mathcal N}(p;\boldsymbol w)}.
\tag{COK.69}
$$

If the positive matching polytope is empty, both sides are zero,
with the convention $\max\varnothing=-\infty$.

Proof. A positive solution in any cover has a matching empirical
type, so the empty case is immediate. Otherwise sum (COK.65) over
all denominator-$m$ positive matching types. Set
$r_0=\sum_i|R_i^+|$ and let $t_0$ be the sum of the finite group
alphabet sizes. There are at most $(m+1)^{r_0}$ local type
collections and $t(p)\le t_0$. The upper half of (COK.67) thus
gives the upper bound in (COK.69) after taking $m$th roots.

The positive matching polytope is a compact rational polytope.
Its rational points are dense: its rational vertices span it,
and rational convex coefficients approximate arbitrary convex
coefficients. Entropy and the displayed log-weight energy are
continuous on this fixed support. Approximate a maximizer by
a rational matching $p$, take $m$ through multiples of its
denominator, and apply the lower half of (COK.67). Let the
approximation error tend to zero. This proves the reverse bound.
Some sheet numbers can have no compatible type, which is why the
statement uses a limsup. $\square$

The normalization in (COK.69) is per sheet of this fixed $n$-block
base. Per original block its logarithmic exponent is
$\max\mathcal B_{\mathcal N}/n$. It is an averaged value over
covers. No comparison with the partition value of the unlifted
base, and no upper bound on every individual cover, follows.

## 14. Native pressure and constant-composition consumers

**Corollary 14.1 (correctly directed original pressure consequence).**
Suppose $w_i=w\ne0$, and the base has prescribed incidence at most
$L$, allowing $L=\infty$. Use the auxiliary
$A_{d,L,N}(w)$ and $\beta_{d,L}(w)$ of
[SIR, Definition 2.2][SIRbase]. For every rational positive matching
$p$ and every admissible $m$,

$$
\begin{aligned}
\frac1{nm}\log_2 A_{d,L,nm}(w)
&\ge\frac{\mathcal B_{\mathcal N}(p;w)}n
     -\frac{r(p)\log_2(m+1)}{nm},\\
\log_2\beta_d(w)\ &\ge\log_2\beta_{d,L}(w)
 \ge\frac{\mathcal B_{\mathcal N}(p;w)}n.
\end{aligned}
\tag{COK.70}
$$

Moreover $r(p)\le n4^{m_d}$, so the finite normalized loss is at
most $4^{m_d}\log_2(m+1)/m$, uniformly in the size and topology
of the base, for laws whose denominator divides $m$.

Proof. Some permutation tuple has $Z_p$ at least its average.
Its actual full solution mass is at least $Z_p$, and its incidence
is still at most $L$ by Proposition 12.3. RRN's converse makes it
a lawful competitor in the stated maximum. Corollary 13.4 proves
the finite inequality. Take $m$ through denominator multiples and
then the all-size supremum. At each local block there are at most
$m_d$ seeds, each with at most four values, giving the support
bound. No pressure normalization uses dyadic padding. $\square$

For rational $w$ and rational $C>0$, a rational matching witness with
$\mathcal B_{\mathcal N}(p;w)/n>\log_2 C$ therefore refutes the
proposed universal cap $\beta_d(w)\le C$. More explicitly, choose
a denominator multiple with the displayed finite loss below the
strict gap. Some finite cover then has mass greater than $C^{nm}$.
Finite exact enumeration of its permutations and actual tuples
finds such a violating template. Computable log enclosures and the
strict inequality suffice to find a large enough multiplier. This
is a construction of counterexamples to undersized caps, not an
NPC.8.1 upper certificate or a lower bound on $\sigma_d$.

**Corollary 14.2 (actual native constant-composition sets).** Let
$p\in\mathcal P(\mathcal N)$ be rational, use unit weights, and put

$$
\nu=\frac1n\sum_i(x_i)_*p_i\in\Delta(S_d).
\tag{COK.71}
$$

The original constant-composition capacity of
[NPC, Theorem 4.3][NPCbase] satisfies

$$
\alpha_d(\nu)\ge\max\{0,H_{\rm cov}(p)/n\}.
\tag{COK.72}
$$

Proof. Every row counted in $Z_p$ has exactly
$m\sum_i p_i\{a:x_i(a)=x\}=nm\nu(x)$ occurrences of each actual
block state $x$. The row set is a subset of the complete native
cover solution set, hence is admissible by the credited restriction
closure. Some cover has at least
$2^{mH_{\rm cov}(p)}(m+1)^{-r(p)}$ such distinct rows by (COK.67).
Thus its type subset witnesses the original $a_{nm}(nm\nu)$ in
(NPC.10). Pass through common denominator multiples in (NPC.12)
to get the second entry in the maximum; $\alpha_d\ge0$ supplies
the first. Actual owner replies ensure that rows were not counted
with multiplicity. $\square$

## 15. Exact nonnegative information charge relative to COK

**Definition 15.1 (the matching-population COK functional).** At a
positive matching law let $B_{i,1},\ldots,B_{i,k_i}$ be the whole
incoming groups of block $i$. Define, using (COK.12),

$$
\begin{aligned}
\mathcal U_{\mathcal N}(p;\boldsymbol w)
 &=\sum_i\left[\sum_{A\subseteq[k_i]}\gamma_{k_i}(A)
        H_{p_i}(O_i\mid B_{i,A})
             +\mathbb E_{p_i}\log_2 w_i(x_i)\right],\\
\operatorname{TC}_{p_i}(I_i)
 &=\sum_{g=1}^{k_i}H_{p_i}(B_{i,g})-H_{p_i}(I_i),\\
\mathcal I_{\rm cov}(p)
 &=\sum_i\left[\operatorname{TC}_{p_i}(I_i)
       +\sum_{A\subseteq[k_i]}\gamma_{k_i}(A)
          I_{p_i}(O_i;B_{i,A^c}\mid B_{i,A})\right].
\end{aligned}
\tag{COK.73}
$$

Empty tuples have entropy zero, and their total correlation is zero.
Each entropy or conditional information uses its displayed single
local law $p_i$. Neither independence of incoming groups nor a
common Gibbs law for these different $p_i$ is assumed.

**Theorem 15.2 (exact COK-minus-cover information identity).** For
every positive matching collection, rational or real,

$$
\mathcal U_{\mathcal N}(p;\boldsymbol w)
 -\mathcal B_{\mathcal N}(p;\boldsymbol w)
 =\mathcal I_{\rm cov}(p)\ge0.
\tag{COK.74}
$$

For uniform $w$, each $p_i$ is a law on the corresponding
$R_{\eta_i}(w)$ of Definition 2.3, and consequently

$$
\mathcal U_{\mathcal N}(p;w)/n\le\log_2\Omega_d(w).
\tag{COK.75}
$$

Proof. Each edge entropy in $H_{\rm cov}$ is precisely the entropy
of one incoming group. Also
$H(p_i)=H_{p_i}(I_i)+H_{p_i}(O_i\mid I_i)$. Since
$\sum_A\gamma_{k_i}(A)=1$, the local entropy difference is

$$
\begin{aligned}
&\sum_A\gamma_{k_i}(A)H_{p_i}(O_i\mid B_{i,A})
 -H(p_i)+\sum_gH_{p_i}(B_{i,g})\\
&\qquad=\operatorname{TC}_{p_i}(I_i)
   +\sum_A\gamma_{k_i}(A)
       \left[H_{p_i}(O_i\mid B_{i,A})-H_{p_i}(O_i\mid I_i)\right]\\
&\qquad=\operatorname{TC}_{p_i}(I_i)
   +\sum_A\gamma_{k_i}(A)
       I_{p_i}(O_i;B_{i,A^c}\mid B_{i,A}).
\end{aligned}
\tag{COK.76}
$$

Total correlation is nonnegative by entropy subadditivity;
conditional mutual information is nonnegative as a conditional
relative entropy. The energy terms cancel exactly, proving (COK.74).

For (COK.75), take any positive incoming group value $b$ under
$p_i$. Matching gives positive mass to that projection under
$p_j$. Some supported local configuration of that same owner $j$
therefore has the whole projection $b$. Its one actual reconstructed
tree has positive $w$, and all its owned ports carry the full owner
tables for those values. This supplies the single joint owner-image
witness required for that group in Definition 2.3. The local tree
of $i$ supplies its first condition. Thus the support of $p_i$
lies in $R_{\eta_i}(w)$ and its local COK functional is at most
$h_{\eta_i}(w)\le\log_2\Omega_d(w)$. Summing proves the claim.
For heterogeneous weights the same reasoning uses the respective
owner supports, as specified after Definition 2.3; it does not give
a common $\Omega_d(w_i)$ bound using the wrong outside support.
$\square$

**Corollary 15.3 (conditional quantitative tightness).** Suppose
$w\ne0$ is uniform and a rational positive matching population on
$n$ blocks satisfies, for $\delta,\epsilon\ge0$,

$$
\mathcal U_{\mathcal N}(p;w)/n\ge\log_2\Omega_d(w)-\delta,
\qquad \mathcal I_{\rm cov}(p)/n\le\epsilon.
\tag{COK.77}
$$

Then

$$
0\le\log_2\Omega_d(w)-\log_2\beta_d(w)\le\delta+\epsilon.
\tag{COK.78}
$$

At every admissible multiplier $m$, (COK.70) gives the same
comparison with $\log_2 A_{d,L,nm}(w)/(nm)$, with the additional
loss $r(p)\log_2(m+1)/(nm)$, when the base has incidence at most
$L$.

Proof. The identity gives
$\mathcal B_{\mathcal N}/n\ge\log_2\Omega_d(w)-\delta-\epsilon$.
Corollary 14.1 bounds native pressure below by this quantity.
The existing all-size upper $\beta_d(w)\le\Omega_d(w)$ is
Theorem 3.1. These are the two needed directions; neither is
an individual-cover Bethe upper. The finite assertion follows
from the first line of (COK.70). $\square$

The charge $\mathcal I_{\rm cov}$ is the difference of these
two population functionals. It is distinct from the common-Gibbs
global loss $\Delta(P)$ in (COK.21), and from the local-to-joint
defect $\mathcal L_\eta$ in (COK.32). The low-entropy law of
Theorem 12.2 cannot be substituted into COK.22 as its Gibbs law.
No existence of populations satisfying (COK.77) with small errors
is asserted.

## 16. Paid full-family realization of a constructed cover fiber

**Theorem 16.1 (original-source implementation and complete alphabet).**
Let $B\subseteq S_d^N$ be any nonempty actual solution set of a
constructed group-permutation cover, or any nonempty subset of it,
including the type-restricted rows of §13. Put

$$
H=\lceil\log_2N\rceil,\quad K=2^H,\quad D=d+H.
\tag{COK.79}
$$

Pad its ordered tuples by $K-N$ fixed alpha blocks and insert
them at the frontier of a perfect height-$H$ ordered scaffold
in the right subtree. Let $\iota(B)\subseteq S_D$ be the resulting
canonical trees. There is a jointly correct original preparation
and reader on the entire variable-shape $\mathcal F_D$ with exactly

$$
|E[\mathcal F_D]|=|S_D|-|B|+1
\tag{COK.80}
$$

attained complete names. It uses exactly $2^D-1$ preparation
Reads, maximum submitted address length $D$, and
$(D-1)2^D+1$ submitted letters. At every permitted later request
it uses zero Reads or one actual original-root Read of length
at most $D$, chosen before its reply and every authentic count.

Proof. Ordered scaffold parsing is injective, so
$|\iota(B)|=|B|$. Give precisely these canonical states one
merged name and every other $S_D$ state its own name. All data,
including a finite membership table, copied topology, permutations
and target witnesses, are public source-independent installation.
For rational type witnesses they can be generated by finite
enumeration and exact checking; no unknown source is used in
their generation.

Before any request, on the actual stationary
$t=\langle\alpha,v\rangle$, read every literal $Rq$ with
$q\in W_D$, in a fixed public order, including absent replies.
The acquired constructor array computes $\pi_D(v)$ and its
assigned name by the credited FMR/RRN reconstruction. Every
canonical state is attained by an actual source, giving precisely
(COK.80). With fixed-width naming, public allocation and a padded
finite selection schedule, export that complete name only. The
declared paid handoff/isolation service removes access to the
array, temporary selectors, buffers, control, transcripts and any
other surviving source dependence, including accessible timing.
Thus no extra source-dependent shape or topology descriptor
escapes the alphabet count.

After a public source-independent request $p=Rq$ arrives, a
singleton name fixes the full requested factor and needs no Read.
At the merged name, a target strictly above the frontier has
constant branch factor. A padding target has its known alpha
trajectory, including initially absent suffixes. Otherwise the
target is $Ra_iq'$ with $|a_i|=H$ and $q'\in W_d$ at one
actual cover block. Its witness is a constant or the table of
one seed owned at an actual block $j$ and port $q_c\in W_d$.
In the latter case make precisely the literal Read

$$
Ra_jq_c,\qquad |Ra_jq_c|\le1+H+d-1=D.
\tag{COK.81}
$$

Its reply is that seed by the retained owner identity; the one
target table returns the requested full factor. An entire group
edge is analytical: this execution observes only its selected
seed reply, not the group tuple. The query uses only the name,
public $D,p$, and installed tables, before any count. All targets
in $W_D$ belong to exactly these scaffold, padding or block cases.

For every original variable shape assigned this name,
canonicalization preserves both the queried reply and the
requested factor. Actual frontier occurrences on the merged
canonical fiber are present. Pairing homomorphism therefore gives
the credited occurrence transport

$$
r_{\rho^kt}(Ra_iq')
 =r_{\rho^k(t|_{Ra_i})}(q')\qquad(k\ge0).
\tag{COK.82}
$$

The presence premise is exactly that of
`original_present_transport`, inspected in
[NativeDepthPatterns][D5N] at the same public pin. Subtree notation
in (COK.82) is a mathematical identification, not a callable port.
Alternatively full canonical factor preservation gives the same
trajectory directly. Formula (COK.5) answers every subsequently
supplied authentic $k\ge0$ with no further Reads. This proves
correctness simultaneously for every actual source and request,
without a source-dependent request, reset, equality, copying,
free navigation, source identity, or supplied age.

Finally there are $2^D-1$ scan words, with lengths summing to
$\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1$.
This proves the resource claims. $\square$

This is a deliberately nonoptimal attained code, not a replacement
preserving an arbitrary competitor's alphabet or preparation cost.
The weights and type laws are proof parameters, not observations
supplied to the reader. The pressure calculation in §14 is on
the original $N$ cover blocks before padding; (COK.80) does not
identify padded pressure or optimal memory with the averaged
cover value. Installation size and generation, preparation
work/control and storage, address generation, post-request space,
predictor size, count representation, entry, authentication,
handoff/isolation and physical time remain separate resources.
For the factor alone, the existing bound
$\lceil\log_2(2D+1)\rceil+1$ bits suffices. The access services
are premises, not inferred physical erasure operations.

## 17. Attribution, finite exact readings and the remaining joint gap

**Convention 17.1 (primary attribution and exact representation).**
The following is a native specialization of mature graph-cover
machinery, with the additional actual-owner, incidence, pressure
and paid-query correspondences proved above.

| Primary supplier | Exact use and limit |
| --- | --- |
| P. O. Vontobel, *Counting in Graph Covers: A Combinatorial Characterization of the Bethe Entropy Function*, version 2, Definition 19 and Lemma 20 [Vontobel][VontobelCOK] | Labeled covers independently permute full edges. Here one full edge alphabet is the whole tuple $\prod_{c\in B_{ji}}T_c$, with projections of the same actual $O_j$ at its owner. Several outgoing projections of $O_j$ are constrained at that vertex; they are not independent owner assignments. |
| Vontobel, Theorem 25 and Lemma 29, same version | Rational local consistency is finite-cover lift-realizable; the exact average type count is the product of vertex multinomials divided by full-edge multinomials. Theorems 12.1 and 13.2 give the constructive native realization and count, retaining guards, actual compatibility and every whole-block weight once. |
| Vontobel, Theorems 30 and 33, same version | Bethe entropy and partition values are exponents or limsups of averaged cover counts and masses. Theorem 13.5 uses precisely this averaged direction. It gives no domination of individual covers or comparison that would prove a universal native upper. |
| N. Ruozzi, *The Bethe Partition Function of Log-supermodular Graphical Models*, Theorem 4.1 and Corollary 4.2 [Ruozzi][RuozziCOK] | The binary log-supermodular hypothesis is not supplied by arbitrary native joint weights and compatibility zeros. No such cover-domination theorem is transferred here. The credited [GCB][GCBbase] counterexamples to unrestricted upper substitutions retain their scope. |

To express this correspondence as a normal factor graph, attach
one function vertex to each actual block $i$ and one full edge
with the above tuple alphabet to each $(j,i)$. Add a private
dangling variable $a_i\in R_i$ at $i$. Its vertex function is
$w_i(x_i(a_i))$ when every incoming full-edge value equals its
group in $a_i$ and every outgoing value equals its projection
of $O_i(a_i)$, and is zero otherwise. Distinct $a_i$ label
distinct local configurations even if their nonowner tables have
the same image. The dangling variable is a formal summation
label, not a native observation.

For any fixed edge permutations, satisfying normal-factor-graph
assignments give exactly the edge-consistent local lists in the
proof of Theorem 13.2. Those lists give a unique actual seed
assignment, and actual owner replies give the inverse. Both
directions preserve all weights and the number of original
blocks. Private half-edges have no matching permutation and no
denominator multinomial. This supplies the full-edge alphabet
mapping required for the cited abstract count; forgetting the
private configurations or splitting whole groups into independently
permuted seeds would change it.

The repository-derived content is this exact native specialization,
the identical-copy-marginal completion, incidence preservation,
the consumers (COK.70)–(COK.72), the information identity
(COK.74), and the full-family realization (COK.80). The finite
type bounds and entropy identities are mature ingredients. FMR
and RRN retain credit for canonicalization, guards, actual
converse templates and paid scans; NPC retains credit for
$\alpha_d$ and semantic pressure completeness; SIR retains
credit for its incidence reduction and conditional verifier
transfer. The existing COK, GDB and SCP results supply respectively
the cap envelope, global dependence boundaries and softening
bounds. No transfer from a finite-reader synthesis or predecessor-
row task is used. There is no new Lean certification, independent
review assertion or worldwide originality claim.

**Convention 17.2 (bounded exact counting readings).** The following
finite readings test the count and grouping, without an empirical
convergence claim or a new rate endpoint. In the credited native
binary-slot three-cycle of [GCB, §§1–2][GCBbase], use four sheets
and the uniform local pair type. Each owner list is balanced,
giving six possibilities. For any two such lists, exactly sixteen
of the twenty-four permutations realize the uniform ordered-pair
type. The number of matching cover/configuration pairs is
$6^3\,16^3=884736$ over $24^3=13824$ covers. Their exact
average is $64=(24/6)^3$, as in (COK.65). With local whole-block
matrix $\left(\begin{smallmatrix}1&2\\3&5\end{smallmatrix}\right)$,
each local type has weight $30$, so the weighted average is
$64\,30^3=1728000$.

For a whole-group check, take two depth-two blocks, with the first
owning both binary seeds at its actual $L,R$ ports and the second
using both seeds at those ports; both roots are constant branch.
Use the uniform four-pair local law at both blocks and four
sheets. There is one full group edge with four labels. For each
of its twenty-four permutations, exactly twenty-four actual
solutions have the prescribed two local types. Thus the average
is $24=24^2/24$; replacing the group denominator by two binary
denominators would give the incorrect $24^2/6^2=16$. Giving both
blocks the displayed matrix weights gives exact average
$24\,30^2=21600$. Zeroing one of those four weights makes this
particular full type's contribution zero; it does not make its
zero row a positive matching law.

The regular-cover construction can separately be checked on a
three-block binary-slot cycle with uniform local pair laws and
four-sheet lists: its twenty-four-sheet law has the prescribed
local distribution at every copy, with at most four outcomes,
and every copied seed retains incidence two. These bounded
in-memory checks exercise the stated finite identities. The
arbitrary-size assertions rely on the proofs in §§12–16.

**Open problem 17.3 (what completion still leaves unproved).**
The constructive completion relation is equality of whole incoming
group laws with projections of the same actual owner tuple laws.
Once it holds rationally, local realizability on some finite
cover is no longer an existence gap. It still does not make
independently selected local maximizers match, nor put their
marginals on the unlifted base. In addition, the explicit charge
$\mathcal I_{\rm cov}/n$ need not be small. The useful sufficient
condition is (COK.77); no theorem here supplies such populations
near minimizing native weights, uniformly in depth or across
weight-support changes.

Consequently COK.57's optimizer-cofinality, [GDB, Definition
11.1][GDBbase]'s universal sound cofinal verifier and effective
original length error remain unresolved. The finite multiplier
error in (COK.67) controls cover counting for a prescribed
rational population; it is not an error for $\log_2K_d(n)/n$,
a finite cutoff for arbitrary native templates, or an algorithm
evaluating the all-size pressure. Preserving bounded incidence
does not add bounded width, mixing or positivity. The numerical
rate endpoints are not restated or improved by this construction.
General exact $M_1(D)$, sharp $\lambda$ and the full minimal-
relations/internal-observer/mutual-recovery programme are not
settled. The operational recovery proved here is the requested
full temporal factor and its authentic-count trajectory from
the complete name and at most one actual reply, under the paid
services; it does not identify the whole hidden source, unseen
history or age, or physical space and time.

[RRNbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[FMRbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NPCbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[SIRbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SEED_INCIDENCE_REDUCTION.md
[GCBbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[GDBbase]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[VontobelCOK]: https://arxiv.org/html/1012.0065v2
[RuozziCOK]: https://arxiv.org/html/1202.6035

## 追加锚（本行以下为增补区）
