# Recursive relational observation: exact native conditional weight optimization

**Convention 1.1 (evidence and scope).** This volume gives complete ordinary proofs for optimization of the finite conditional-owner outer envelope at each specified finite depth. It is mathematical reference input, without Lean kernel certification. Numbered claims use the generic-v1 convention; additions belong after the final append anchor. The original native source, legal observations, canonical states, complete temporal factors, actual owner ports, repeated seeds and whole-block weights are retained. Finite algorithm statements specify terminating mathematical procedures; no execution or complexity claim is part of them. All logarithms and entropies have base two.

## 1. Original objects and the finite conditional envelope

**Definition 1.2 (source and paid observation interface).** Trees are the free ordered binary magma

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\qquad
\operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,\qquad
\operatorname{ht}\langle u,v\rangle=1+\max(\operatorname{ht}u,\operatorname{ht}v).
$$

A literal Read at any finite original-root word over $L,R$, including the empty word, returns its constructor, or absent after traversal passes a leaf. The reply alphabet is $\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. The action and source family are

$$
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle,\qquad
\mathcal F_D=\{\langle\alpha,v\rangle:\operatorname{ht}v\le D\},\quad D\ge1.
$$

One initial source stays stationary during preparation and later acquisition. Preparation is deterministic, effective, initially source-blind and terminating on every source; it acquires every distinction by charged literal Reads before knowing the request. Its complete finite export $E(t)$ counts all accessible surviving dependence, including control, selectors, buffers, lengths, allocation, handles and accessible timing. Separately paid handoff, access isolation and lawful entry remove access to other acquired dependence, including transcripts. Only then a source-independent request $p$ arrives, ranging over all $R$-starting words with $1\le |p|\le D$. From the name and public data the reader chooses zero Reads or one fresh Read of that same initial source, before its reply and before every authentic subsequently supplied $k\ge0$. Its predictor must return $r_{\rho^kt}(p)$ for every such $k$, without further Reads. The minimum complete attained alphabet is $M_1(D)$. Subtree, equality, source-identity, age, reset, copying, free navigation and advice are unavailable. Work, preparation Reads, installed tables, workspace, predictor size, address lengths and letters, count representation, access services and physical time remain separate resources. These are the unchanged premises recorded in [COK, §1][COK] and [GDB, §1][GDB].

**Definition 1.3 (entire canonical alphabet and full factors).** For every $d\ge1$, set

$$
C_0=\langle\alpha,\alpha\rangle,\quad S_1=\{\alpha,\beta,C_0\},\quad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle u,v\rangle:u,v\in S_d\},\quad
W_d=\{q:|q|\le d-1\},\quad m_d=2^d-1,\quad s_d=|S_d|.
$$

Write $g_q(x)=\Gamma_q(x)$ and $r_q(x)=r_x(q)$. At an original branch endpoint the factor is $(0,0)$. Otherwise the first original blocking leaf has label $\ell$ and the residual word beyond it is $r$. With $e(\alpha)=0,e(\beta)=1$,

$$
\Gamma_q(x)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(\#L(r)+2\#R(r)+2-e(\ell),\mathbf1_{\{r\text{ ends in }R\}}),&r\ne\varepsilon.
\end{cases}
\tag{NWO.1}
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
\tag{NWO.2}
$$

It equals $r_{\rho^kx}(q)$; its complete trajectory recovers $(b,c)$. Put $h(z)=\operatorname{Pred}(z,0)$ and $G_q=\Gamma_q[S_d]$. Thus $h(g_q(x))=r_q(x)$. The entire factor vector separates $S_d$. The canonicalization and all-word simulation credited in [COK, Definition 1.3][COK] and [GDB, Convention 1.4][GDB] preserve the full boundary factors and replies on arbitrary variable shapes. An arbitrary finite probe on a canonical block is a function of one actual boundary reply in that same block or a constant. No target-prefix restriction is imposed.

**Definition 1.4 (actual networks and original whole weights).** A complete native template on $n$ original blocks gives every port $(i,q)\in[n]\times W_d$ a constant full factor or a total table of one actual reply $r_a(x_j)$, with $a\in W_d$. All equations hold on the same tuple $x\in S_d^n$; let $C_\Theta$ be the full solution set. Off-target donors, self donors, cycles and correlations are unrestricted.

Use the exact owned-seed representation credited to RRN/CBN in [COK, Definition 1.4][COK] and [GDB, Definition 2.1][GDB]. A seed $c$ has a nonempty domain $T_c\subseteq\mathcal A$, a distinct actual owner port $o_c$, and at each occurrence a full-factor table of that same variable. Its owner table obeys

$$
h(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{NWO.3}
$$

Each port is constant or assigned to one seed. On a seed assignment $s$, a block's entire factor vector either reconstructs a unique $x_i(s)\in S_d$ or is incompatible. For arbitrary nonnegative whole-block weights put

$$
\Phi_i(s)=
\begin{cases}w_i(x_i(s)),&\text{compatible},\\0,&\text{otherwise},\end{cases}
\qquad
Z=\sum_{s\in\prod_cT_c}\prod_i\Phi_i(s)
 =\sum_{x\in C_\Theta}\prod_iw_i(x_i).
\tag{NWO.4}
$$

The correspondence goes both ways with one lift per actual tuple, recovered at its actual owners. Every original joint block weight occurs once. Repeated seed occurrences are never independent copies. Empty domains give zero mass; no seeds give one empty assignment, possibly incompatible. Write $O_i$ for the whole tuple of seeds owned by block $i$. These tuples partition the seeds.

**Definition 1.5 (complete finite decoration list).** Retain the entire list $\mathcal E_d$ of [COK, Definition 2.2][COK]. A decoration has at most $m_d$ distinct locally occurring seeds with nonempty domains, a subset $O$ owned at distinct local ports satisfying (NWO.3), and a partition of its other seeds into nonempty groups $B_1,\ldots,B_k$ by their common actual outside owner block. For each group record distinct ports in one outside block and their full owner tables satisfying (NWO.3). At every local port record a constant in $G_q$ or a table from one declared seed into $G_q$; each owned port is assigned to its own seed. Each declared seed occurs locally. Groups represent different outside owner blocks.

The list contains every choice of these finite data, up to canonical relabeling. One encoding orders $\mathcal A$ as alpha, beta, branch, absent; words by length then lexicographically with $L<R$; factors lexicographically; and domains and tables by their ordered entries. Retain the least encoding over seed and group relabelings. This makes the list finite and effectively enumerable without changing any seed identity or outside-owner grouping. Every actual block has such a decoration; there is no bound here on network size.

**Definition 1.6 (exact support and simultaneous owner relation).** For a nonzero weight $w:S_d\to[0,\infty)$ let $F=\operatorname{supp}w=\{x:w(x)>0\}$. On the declared full seed product of $\eta$, let $R_\eta(F)$ contain exactly the assignments $s$ for which the complete local factor vector reconstructs $X(s)\in F$ and, for each external group $g$, there is one $u_g\in F$ such that

$$
g_{q_c}(u_g)=B_{o_c}(s_c)\qquad\text{for every }c\in B_g
\tag{NWO.5}
$$

simultaneously. Set $\Phi_\eta(s)=w(X(s))$ there. Separate marginal witnesses for seeds of the same group do not suffice. Different groups' witnesses are not asserted to extend to one global network. The relation is recomputed whenever support changes. With heterogeneous weights the local test uses the local support and each external group's actual owner's support, respectively; using one common support in that situation is unjustified.

Every positive assignment of an actual uniform-$w$ network belongs to each local relation: its local block supplies $X$, and each actual external owner supplies the single simultaneous witness in (NWO.5). This proves local coverage, without a converse completion assertion.

**Definition 1.7 (one-law envelope).** For $A\subseteq[k]$ let $B_A=(B_g)_{g\in A}$ and

$$
\gamma_k(A)=\frac{|A|!(k-|A|)!}{(k+1)!}.
$$

All these coefficients are positive and sum to one: at each cardinality their sum is $1/(k+1)$. They are the probabilities that exactly groups $A$ precede the local block in a uniformly random ordering of it and its $k$ distinct incoming owners. For a nonempty relation define

$$
\begin{aligned}
L_\eta(p;w)&=\sum_{A\subseteq[k]}\gamma_k(A)H_p(O\mid B_A)
                  +\mathbb E_p\log_2w(X),\\
h_\eta(w)&=\max_{p\in\Delta(R_\eta(F))}L_\eta(p;w),\\
\Omega_d(w)&=\max_{\eta\in\mathcal E_d}2^{h_\eta(w)}.
\end{aligned}
\tag{NWO.6}
$$

Every entropy and the weight expectation in one objective use the same law $p$. Empty relations contribute zero; $\Omega_d(0)=0$. Empty tuples have one value and entropy zero. Finite entropy continuity and compactness give each displayed maximum. A no-seed constant decoration at any $x\in F$ gives a positive value. Define

$$
a_d=\inf_{\mu\in\Delta(S_d)}\Omega_d(\mu).
\tag{NWO.7}
$$

This is the fixed-depth conditional relaxation endpoint. The proofs below retain the complete $S_d,W_d,\mathcal E_d$, even when weights vanish.

## 2. Positive-kernel minimax and the exact all-network use

**Theorem 2.1 (regularized compact minimax with full rows).** For a nonempty $R_\eta(F)$, the exact value is

$$
2^{h_\eta(w)}
=\inf_{\substack{Q_A(o\mid b)>0\\\sum_oQ_A(o\mid b)=1}}
\ \max_{s\in R_\eta(F)}
\frac{w(X(s))}
{\prod_AQ_A(O(s)\mid B_A(s))^{\gamma_k(A)}}.
\tag{NWO.8}
$$

Every row includes the entire declared owned-tuple outcome product, for every full context in the declared $B_A$ product. Unused outcomes and contexts are retained. This is an infimum, without a strict-positive attainment assertion.

Proof. Let $M=\prod_{c\in O}|T_c|$, taking $M=1$ for empty $O$. For $0<\epsilon<1$, require every row entry to be at least $\epsilon/M$. The product of these full-row domains is nonempty, compact and convex. On it and $\Delta(R_\eta(F))$, the function

$$
f(p,Q)=\mathbb E_p\log_2w(X)
 -\sum_A\gamma_k(A)\mathbb E_p\log_2Q_A(O\mid B_A)
$$

is continuous, linear in $p$ and convex in $Q$. The compact convex minimax theorem used in [COK, Theorem 4.1][COK], credited to [Sion, Theorem 3.4][Sion], exchanges $\max_p\min_Q$ and $\min_Q\max_p$. At fixed $Q$, maximizing over $p$ gives its largest pointwise logarithmic ratio.

For a fixed $p$, conditional cross entropy is at least $H_p(O\mid B_A)$ by nonnegativity of conditional relative entropy. At positive-probability contexts take the actual conditional row of $p$; at zero-probability contexts take the uniform full row. Smooth every row to $(1-\epsilon)p(\cdot\mid b)+\epsilon/M$. On observed outcomes it is at least $(1-\epsilon)p(\cdot\mid b)$, so cross entropy exceeds conditional entropy by at most $-\log_2(1-\epsilon)$. Zero-probability contexts contribute zero. As the coefficients sum to one, the restricted minimax logarithm is between $h_\eta(w)$ and $h_\eta(w)-\log_2(1-\epsilon)$. Every positive finite array belongs to some such restricted domain, and weak duality bounds its maximum below by $h_\eta(w)$. Letting $\epsilon$ decrease to zero and exponentiating proves (NWO.8). $\square$

**Corollary 2.2 (strict rational fixed-weight certificates).** For rational $w\ge0$ and rational $C>\Omega_d(w)$, every nonempty type has complete strictly positive normalized rational kernels at cap $C$. Conversely kernels at cap $C>0$ imply $\Omega_d(w)\le C$.

Proof. For each nonempty type choose a positive array whose pointwise maximum in (NWO.8) is strictly below $C$. Approximate its finitely many normalized rows by positive rational normalized rows. Strict positivity and all finitely many strict inequalities survive. There are finitely many types, so this supplies all arrays at the same cap. Conversely the pointwise inequalities bound every objective by $\log_2C$ using conditional cross entropy, or directly by (NWO.8). At $w=0$ the empty witness suffices. No zero weight is logged: relations are constructed from the exact support first. $\square$

**Theorem 2.3 (credited conditional all-size rule, with its common law).** Suppose an actual network has constants $C_i>0$, positive kernels on full rows and local inequalities

$$
\Phi_i(s)\le C_i\prod_AQ_{i,A}(O_i(s)\mid B_{i,A}(s))^{\gamma_{k_i}(A)}
\tag{NWO.9}
$$

on relations covering its positive assignments, with the actual incoming owner groups. Then $Z\le\prod_iC_i$. In particular $\beta_d(w)\le\Omega_d(w)$, where

$$
A_n(w)=\max_\Theta\sum_{x\in C_\Theta}\prod_iw(x_i),\qquad
\beta_d(w)=\sup_{n\ge1}A_n(w)^{1/n}.
\tag{NWO.10}
$$

Proof. Zero mass is immediate. Otherwise use the one actual Gibbs law $P(s)=Z^{-1}\prod_i\Phi_i(s)$ on positive assignments. Its identity is

$$
\log_2Z=H_P(s)+\sum_i\mathbb E_P\log_2\Phi_i.
$$

The whole $O_i$ partition the seeds. For each permutation $\pi$ of actual blocks, let $O_{<i,\pi}$ be preceding owners, and $A_i(\pi)$ the incoming owners preceding $i$. The actual $B_{i,A_i(\pi)}$ is a subtuple of $O_{<i,\pi}$. Thus

$$
H_P(s)=\sum_iH_P(O_i\mid O_{<i,\pi})
\le\sum_iH_P(O_i\mid B_{i,A_i(\pi)}).
$$

Averaging gives precisely the coefficients $\gamma_{k_i}$. Taking expectations of the logarithms in (NWO.9), each conditional relative-entropy inequality

$$
H_P(O_i\mid B_{i,A})+\mathbb E_P\log_2Q_{i,A}(O_i\mid B_{i,A})\le0
$$

cancels the corresponding averaged entropy. This proves the cap, counting each original $\log\Phi_i$ once. Shared seeds, repeated ports, self donors, cycles, compatibility zeros and arbitrary joint block weights all remain under this same law. Uniform weights have the coverage in Definition 1.6. Theorem 2.1 supplies simultaneous caps $\Omega_d(w)+\epsilon$ on the finite type list. Apply the cap at every size, take $n$th roots, then let $\epsilon$ decrease to zero; the exact correspondence (NWO.4) gives the claimed pressure bound. $\square$

**Proposition 2.4 (exact missing common-law losses).** For the same positive-mass Gibbs law and pointwise inequalities, put

$$
\begin{aligned}
\Delta(P)&=\mathbb E_\pi\sum_i I_P(O_i;O_{<i,\pi}\mid B_{i,A_i(\pi)}),\\
\mathcal D_{i,A}&=D_2\bigl(P(O_i\mid B_{i,A})\Vert Q_{i,A}(\cdot\mid B_{i,A})\mid P(B_{i,A})\bigr),\\
\ell_i(s)&=\log_2\frac{C_i\prod_AQ_{i,A}(O_i\mid B_{i,A})^{\gamma_{k_i}(A)}}{\Phi_i(s)}.
\end{aligned}
$$

Then all losses are nonnegative and

$$
\log_2Z=\sum_i\log_2C_i-\Delta(P)
 -\sum_{i,A}\gamma_{k_i}(A)\mathcal D_{i,A}
 -\sum_i\mathbb E_P\ell_i.
\tag{NWO.11}
$$

Proof. Because $B_{i,A_i(\pi)}$ is a function of preceding owners, the difference of the two conditional entropies in the preceding proof is the displayed conditional mutual information. Conditional cross entropy is conditional entropy plus $\mathcal D_{i,A}$. The definition of $\ell_i$ is the exact pointwise logarithmic slack. Substitute these three identities in the Gibbs identity. Strictly positive kernels make all terms finite; zero-probability contexts have zero contribution. This is [COK, Theorem 3.2][COK] with the same actual law. $\square$

Unrelated local maximizers need not be marginals of such a law. Even joint realizability does not force $\Delta(P)=0$. These are distinct obligations from the finite optimization below.

## 3. Support order, approximation and real attainment

**Theorem 3.1 (order, homogeneity and elementary bounds).** On the nonnegative weight cone, $\Omega_d$ is coordinatewise nondecreasing and positively homogeneous, including scale zero. For every $w\ge0$,

$$
\max_{x\in S_d}w(x)\le\Omega_d(w)\le\sum_{x\in S_d}w(x).
\tag{NWO.12}
$$

Proof. If $F\subseteq G$, then $R_\eta(F)\subseteq R_\eta(G)$: the same reconstructed state and the same simultaneous group witnesses remain valid. For $0\le w\le v$, every old law remains feasible and its log-weight expectation can only increase. This gives monotonicity for nonzero $w$; zero follows by nonnegativity. Scaling by $c>0$ keeps support and adds $\log_2c$ to every objective. The zero convention gives $\Omega_d(0w)=0$.

For any local law, the owner identity makes $O$ a function of $X$: each owned seed is the actual reply at its owner port. Hence the average conditional entropy is at most $H(O)\le H(X)$. With $W=\sum_xw(x)>0$,

$$
L_\eta(p;w)\le H_p(X)+\mathbb E_p\log_2w(X)
 =\log_2W-D_2(p_X\Vert w/W)\le\log_2W.
$$

A constant no-seed decoration at any positive-weight state gives that state's weight, proving the lower bound. At zero both bounds are zero. $\square$

**Theorem 3.2 (exact-support continuity and rational infimum).** On each exact-support stratum $\Omega_d$ is continuous. More precisely, if $w,v$ have the same nonempty support and $0<\epsilon<1$ with $(1-\epsilon)w\le v\le(1+\epsilon)w$, then

$$
(1-\epsilon)\Omega_d(w)\le\Omega_d(v)\le(1+\epsilon)\Omega_d(w).
\tag{NWO.13}
$$

Moreover

$$
\inf_{\mu\in\Delta(S_d)}\Omega_d(\mu)
=\inf_{\nu\in\Delta(S_d)\cap\mathbb Q^{S_d}}\Omega_d(\nu).
\tag{NWO.14}
$$

Proof. Identical supports give identical relations, joint owner-image tests and feasible laws. Only the expected log weight changes, between $\log_2(1-\epsilon)$ and $\log_2(1+\epsilon)$. Maximize and exponentiate to get (NWO.13). Finitely many strictly positive coordinates give continuity at every point of that stratum.

For any real probability $\mu$ with support $F$ and $\delta>0$, choose $\epsilon$ with $(1+\epsilon)/(1-\epsilon)<1+\delta$. Choose positive rationals $r_x$ between $(1-\epsilon)\mu(x)$ and $(1+\epsilon)\mu(x)$ for all $x\in F$. Normalize by $\nu(x)=r_x/\sum_{y\in F}r_y$, and set $\nu=0$ elsewhere. Then $\nu$ is rational, has exactly $F$, and $\nu\le(1+\delta)\mu$. Monotonicity and homogeneity give $\Omega_d(\nu)\le(1+\delta)\Omega_d(\mu)$. Taking the infimum over $\mu$ and then $\delta\downarrow0$ proves one direction of (NWO.14); inclusion of rational probabilities proves the other. This is the support-preserving approximation method of [SCP, Proposition 5.2][SCP] applied to the unchanged relation. It does not fill a zero coordinate. $\square$

**Theorem 3.3 (global lower semicontinuity and real minimum).** The function $\Omega_d$ is lower semicontinuous on the entire nonnegative cone and continuous at zero. The real minimum exists and

$$
a_d=\min_{\mu\in\Delta(S_d)}\Omega_d(\mu)
=\inf_{\nu\in\Delta(S_d)\cap\mathbb Q^{S_d}}\Omega_d(\nu),
\qquad \frac1{s_d}\le a_d\le1.
\tag{NWO.15}
$$

Proof. Let $w_j\to w\ne0$, with $F=\operatorname{supp}w$. Eventually $F\subseteq\operatorname{supp}w_j$. Fix any decoration and law $p$ on $R_\eta(F)$, extend it by zero to the larger relations, and use that same law throughout. Its conditional entropies do not change. Every state given positive mass has positive limiting weight, so its finite expected log weight converges. Therefore

$$
\liminf_j\Omega_d(w_j)\ge2^{L_\eta(p;w)}.
$$

Maximizing over laws and types proves lower semicontinuity at $w$. At zero, $0\le\Omega_d(w_j)\le\sum_xw_j(x)\to0$. A minimizing sequence in the compact probability simplex has a convergent subsequence. Lower semicontinuity makes the limit a minimizer. On that simplex (NWO.12) gives $\Omega_d(\mu)\ge\max_x\mu(x)\ge1/s_d$ and $\Omega_d(\mu)\le1$. Combine with (NWO.14). This is real weight attainment, independent of positive-kernel attainment. $\square$

## 4. A complete native failure of global continuity

**Definition 4.1 (separating chain states at depth fifteen).** Let $Z=\{0,\ldots,15\}$ and let $\mathcal J$ be its four-element subsets. For $Q=\{z_0<z_1<z_2<z_3\}$ define $f_Q(z_i)=i$ and $f_Q(z)=0$ outside $Q$. There are $\binom{16}{4}=1820$ such functions. Their joint vector separates $Z$, since a set $Q$ containing any two different indices assigns them different colors.

Use a perfect ordered scaffold of height $11$ with its $2048$ length-$11$ slots. Assign distinct slots $a_Q$ to the functions, four other slots to the binary digits of $z$, and one marker slot. Other slots are alpha. Put

$$
T_0=\alpha,\qquad T_{h+1}=\langle T_h,\alpha\rangle\quad(0\le h\le2).
$$

In $x_z$ place $T_{f_Q(z)}$ at $a_Q$, alpha/beta according to the four digits at the digit slots, and alpha at the marker. Set

$$
F=\{x_z:z\in Z\},\qquad
\mu_0(x_z)=1/16,\qquad \mu_0(x)=0\quad(x\notin F).
$$

Every tree of height at most $d-1$ belongs to $S_d$, by induction in its defining recursion. The $x_z$ have height at most $14$ and therefore belong to $S_{15}$; their digits make them distinct. Each target $q_Q=a_QLLL$ has length $14$ and lies in $W_{15}$.

**Theorem 4.2 (the entire boundary maximum is exactly three sixteenths).** For the original complete decoration list,

$$
\Omega_{15}(\mu_0)=3/16.
\tag{NWO.16}
$$

Proof of the upper bound. Every literal, including words beyond these trees, has at most three actual replies on all of $F$. Above the slots it sees fixed branch. In a chain slot it sees only alpha, branch or absent. At a digit root it sees alpha/beta and at proper descendants it sees absent. Marker and unused slots are fixed. However (NWO.1) gives at $q_Q$, for heights $h=0,1,2,3$, respectively,

$$
\Gamma_{LLL}(T_h)=(5,0),(4,0),(3,0),(2,1).
\tag{NWO.17}
$$

For any decoration whatsoever and any law $p$ on $R_\eta(F)$, put $P=\operatorname{supp}p_X$. Every value of an owned seed under $p$ is an actual reply in $F$ at its owner. Every incoming seed value is likewise an actual reply at its recorded outside owner port in the simultaneous witness required by (NWO.5). At each such fixed port $F$ has at most three replies. Thus every seed takes at most three values under $p$, regardless of a larger declared domain. A target is constant or a table of one seed, so $|g_q(P)|\le3$ for every $q$.

If $P$ contained four distinct states, their indices would give a $Q$ with four distinct factors at $q_Q$, by (NWO.17), a contradiction. Hence $|P|\le3$. Since $O$ is a function of $X$, every conditional entropy is at most $H(X)\le\log_2 3$, while the log weight is always $-4$. Every type's value is at most $3/16$. This bounds the full maximum, not a chosen subfamily.

Proof of attainment. Choose any three distinct indices. In each chain slot let $H$ be its set of heights on those states. If $H=\{h_1<h_2<h_3\}$, the literal $L^{h_2}$ within the slot returns absent, alpha, branch respectively and identifies the height. If $H=\{h_1<h_2\}$, the literal $L^{h_1}$ returns alpha and branch and identifies the height. For singleton $H$ use constants. In every nonconstant slot create one locally owned seed at this selected actual port, with domain exactly these attained replies. Its tables prescribe all full factors at all targets within that slot. The selected exponent is at most two, so each owner port has length at most $13$ and is in $W_{15}$. The owner table is the actual factor at that port and obeys (NWO.3); owners in different slots are distinct.

Give each varying digit its own alpha/beta owner at the digit root, and use it for every target in that slot, including proper-descendant temporal factors. Above-slot factors, fixed slots and marker factors are constants. This specifies every port, including initially absent suffixes. There are at most $1824<m_{15}$ seeds and no external groups, so this is a legal $k=0$ decoration. The varying digit replies distinguish the selected three states. Their actual seed assignments are in $R_\eta(F)$, and their uniform law has $H(O)=\log_2 3$ and expected log weight $-4$. It attains $3/16$, proving (NWO.16). $\square$

**Definition 4.3 (actual symbols for entering joint witnesses).** Define

$$
E_0=\alpha,\quad E_1=\langle\alpha,\alpha\rangle,\quad
E_2=\langle\beta,\alpha\rangle,\quad
E_3=\langle\langle\alpha,\alpha\rangle,\alpha\rangle.
$$

Their $L$ factors and actual $L$ replies give the explicit color-to-symbol bijection

$$
\begin{array}{c|cccc}
h&0&1&2&3\\ \hline
\Gamma_L(E_h)&(3,0)&(2,1)&(1,0)&(0,0)\\
\xi_h=r_{E_h}(L)&\mathsf{absent}&\alpha&\beta&\mathsf{branch}
\end{array}
\tag{NWO.18}
$$

In $u_z$ use the same scaffold, put $E_{f_Q(z)}$ at each $a_Q$, alpha in every digit slot and beta at the marker. These are distinct states of height at most $13$ in $S_{15}$. Their separating $f$-vectors make them distinct; the marker makes them disjoint from $F$.

**Theorem 4.4 (one legal entering type and sixteen joint witnesses).** Let $U$ be the uniform law on the entire $S_{15}$ and $\mu_t=(1-t)\mu_0+tU$ for $0<t<1$. Then

$$
\Omega_{15}(\mu_t)\ge
4\left(\frac{1-t}{16}+\frac{t}{s_{15}}\right),\qquad
\liminf_{t\downarrow0}\Omega_{15}(\mu_t)\ge\frac14>\frac3{16}.
\tag{NWO.19}
$$

Rational $t$ gives rational full-support probabilities.

Proof. Make a local decoration with four owned binary digit seeds at the digit roots. For each $Q$ give its chain slot one incoming seed $c_Q$ with domain the actual alphabet $\mathcal A$. When $c_Q=\xi_h$, prescribe every full factor inside that slot as the factor of $T_h$ at the corresponding suffix. Put all these incoming seeds in one external owner group, with distinct outside owner ports $a_QL$ and owner tables

$$
\xi_h\longmapsto\Gamma_L(E_h).
$$

Equation (NWO.18) proves their actual owner identities. These outside ports have length $12$ and belong to $W_{15}$. The digit tables prescribe all full digit factors. Every above-slot factor is constant branch, and marker and unused-slot factors are their actual constants. This specifies all local targets. All table values are in their original attained $G_q$: the local ones occur in actual $x_z$, and the owner ones in actual $u_z$. Each $c_Q$ occurs in its chain slot, and all repeated occurrences use that one seed. The $1824$ distinct seeds fit the bound $m_{15}$. This is a member of the original $k=1$ list.

For every $z$, set the digit seeds to its actual digits and $c_Q=\xi_{f_Q(z)}$ for every $Q$. The full local vector reconstructs exactly $x_z$. The entire incoming group has the single simultaneous witness $u_z$, because its factors at every $a_QL$ equal the corresponding owner-table values together. This is a joint image witness, not separate witnesses for individual colors.

Whenever all $x_z$ and $u_z$ have positive weight, the uniform law on these sixteen assignments is admissible. Its owned tuple $O$ determines $z$ from the digits, and its one incoming tuple $B$ determines $z$ from the separating $f$-vector. Under that same law $H(O)=4$ and $H(O\mid B)=0$. Both $k=1$ coefficients are $1/2$. For $\mu_t$ each $x_z$ has weight $(1-t)/16+t/s_{15}$, so the exponential objective is four times this weight. This proves (NWO.19). The external witness weights enter the relation through support membership; no second copy of those weights enters the local objective. That is exactly the defined outer relaxation. $\square$

**Corollary 4.5 (global regularity statements that fail).** In general $\Omega_d$ is not upper semicontinuous, continuous, uniformly continuous, globally Lipschitz or convex, even on the probability simplex.

Proof. Theorem 4.2 controls every type at $\mu_0$, and Theorem 4.4 gives a strictly larger lower limit along probabilities tending to it. This disproves upper semicontinuity and continuity; uniform continuity or a global Lipschitz bound would imply continuity. Convexity along the same segment would imply

$$
\Omega_{15}(\mu_t)\le(1-t)\frac3{16}+t\Omega_{15}(U)
\le(1-t)\frac3{16}+t,
$$

contradicting (NWO.19) as $t\downarrow0$. $\square$

No exact value or computed limit of $\Omega_{15}(\mu_t)$ is asserted. The example does not identify $\mu_0$ as a minimizer. It rules out support filling as a general approximation argument; the exact-support construction in Theorem 3.2 remains valid.

## 5. Closed kernels and the exact polynomial epigraph

**Theorem 5.1 (closed real epigraph on each exact support).** Fix nonempty $F\subseteq S_d$, $w$ with exactly support $F$, and $C>0$. For every nonempty $R_\eta(F)$ set

$$
r_\eta=(k+1)!,\qquad n_{\eta,A}=|A|!(k-|A|)!,
\quad \sum_A n_{\eta,A}=r_\eta.
$$

Introduce all full-row real kernel variables $Q_{\eta,A}(o\mid b)\ge0$ with $\sum_oQ_{\eta,A}(o\mid b)=1$ for every full context. Then $C\ge\Omega_d(w)$ is equivalent to existence of these arrays, simultaneously over all nonempty types, satisfying

$$
w(X(s))^{r_\eta}\le
C^{r_\eta}\prod_{A\subseteq[k]}
Q_{\eta,A}(O(s)\mid B_A(s))^{n_{\eta,A}}
\qquad(s\in R_\eta(F)).
\tag{NWO.20}
$$

These are auxiliary nonnegative real kernels. They are different from the strictly positive rational arrays of the original certificate.

Proof. At every cap $\Omega_d(w)+1/j$, Theorem 2.1 supplies positive kernels for all the finitely many nonempty types. Their full rows lie in a finite product of compact closed probability simplexes. Select a subsequence converging simultaneously in every entry. Normalization and all polynomial inequalities survive, giving (NWO.20) at $\Omega_d(w)$. The same arrays work at every larger cap.

Conversely suppose (NWO.20) holds. Every tested weight is strictly positive and every exponent $n_{\eta,A}$ is positive. Thus every kernel entry used by a tested assignment is positive. Only entries unused by all tested assignments for that kernel can vanish; an entirely unused context can have zeros too, but its full normalized row remains.

For each type smooth every full row by $Q^\epsilon=(1-\epsilon)Q+\epsilon/M$, where $M$ is the size of its entire declared owned product. These rows are positive and normalized at every context. Taking the positive $r_\eta$-th root of (NWO.20), the original denominator is $\prod_AQ_A^{\gamma_k(A)}$. Its smoothed version is at least $(1-\epsilon)^{\sum_A\gamma_k(A)}=1-\epsilon$ times the original denominator on each tested assignment. Therefore the positive arrays work at cap $C/(1-\epsilon)$. Theorem 2.1 gives $\Omega_d(w)\le C/(1-\epsilon)$. Let $\epsilon\downarrow0$ to prove the converse. $\square$

**Convention 5.2 (degenerate cases without shortened rows).** Empty relations impose no kernels or inequalities. The empty owned tuple has one outcome and each row entry is one. An empty context tuple has one context row. At $k=0$, $r_\eta=n_{\eta,\varnothing}=1$. All contexts, including zero-probability contexts under any proposed law, retain full rows, with no division by their probabilities. Singleton seed domains obey the same formulas. For $F=\varnothing$ handle $w=0$, $\Omega_d(w)=0$ and $C\ge0$ separately. For nonempty support $\Omega_d(w)>0$, so $C\le0$ is outside its epigraph. No logarithm at a zero weight or zero tested kernel entry is used in these arguments.

**Theorem 5.3 (effective support-disjunctive semialgebraicity).** The entire set

$$
\operatorname{Epi}(\Omega_d)
=\{(w,C):w\ge0,\ C\ge\Omega_d(w)\}
\tag{NWO.21}
$$

is effectively semialgebraic over $\mathbb Q$ for each finite input $d$.

Proof. For each nonempty $F\subseteq S_d$, construct the exact finite relations using local reconstruction and one simultaneous search over $u\in F$ per external group. Conjoin the closed-kernel system (NWO.20) with

$$
w_x>0\ (x\in F),\qquad w_x=0\ (x\notin F),\qquad C>0,
$$

and existentially quantify its kernel variables. Theorem 5.1 identifies this branch with the epigraph on exactly that support. Take the finite disjunction over all nonempty supports and add $w=0,C\ge0$. These are rational polynomial formulas; effective real quantifier elimination gives a semialgebraic description of their projection.

For completeness of effectiveness, the finite input $d$ generates $S_d$ recursively, $W_d$ by bounded words, and all attained factor/reply tables by (NWO.1)–(NWO.2). The bounded domain, port, group and table data in Definition 1.5 generate the entire list. Every seed assignment has a finite reconstruction test against the complete factor vectors. Each group test checks all its owner equations on the same candidate $u$. Thus the defining formula has an effective finite construction, without an oracle about global completion or an arbitrary-size cutoff. This is a terminating algorithm specification, not an execution or efficiency assertion. $\square$

The support disjunction is essential. Substituting the full-support relation at a boundary would change the object, as the native construction in §4 demonstrates.

## 6. Algebraic values and an algebraic minimizing law

**Theorem 6.1 (exact algebraic fixed-weight evaluation).** At any specified nonnegative algebraic weight $w$, $\Omega_d(w)$ is a computable real algebraic number.

Proof. Algebraic coordinate representations allow exact sign and zero tests, hence exact support. Substitute these coordinates into the epigraph formula. Its cap fiber is precisely $[\Omega_d(w),\infty)$. Effective real quantifier elimination with real algebraic coefficients gives a one-variable semialgebraic description. Away from the roots of the finitely many nonzero polynomials in that description, every polynomial sign is locally constant. A finite boundary point of the cap fiber must therefore be a root of one of them. Its coordinates are algebraic over the field of algebraic numbers, hence algebraic over $\mathbb Q$. Effective root isolation and sign determination select its endpoint and yield an exact polynomial and isolating interval. At zero the endpoint is zero directly. These are finite algorithm specifications using the mature real-algebraic machinery also used in [COK, §6][COK] and attributed there to [Basu][Basu]. $\square$

**Theorem 6.2 (computable algebraic optimum and algebraic attainment).** For each finite $d$, $a_d$ is a computable positive real algebraic number. At least one minimizing probability has real algebraic coordinates. The real minimizing set is effectively semialgebraic.

Proof. Add $\sum_xw_x=1$ to the support-disjunctive epigraph formula and existentially quantify the weights and closed kernels. Real attainment from Theorem 3.3 makes the cap set exactly $[a_d,\infty)$, including its least point, and $a_d\ge1/s_d>0$. It is effectively semialgebraic over $\mathbb Q$. The endpoint argument in Theorem 6.1 now yields an exact rational polynomial and isolating interval for $a_d$.

At $C=a_d$ the existential minimizing fiber is nonempty and defined over the real algebraic numbers. That field is real closed. Quantifier elimination, equivalently algebraic sampling or transfer of this existential formula between real closed fields, supplies a solution with algebraic weights and algebraic closed-kernel entries. Its support satisfies one of the exact branches. Its weight is a probability with $\Omega_d(w)\le a_d$, hence equality by the definition of $a_d$. Thus it is an algebraic minimizer.

The minimizing set is the projection to $w$ of the same formula at $C=a_d$, restricted to the probability simplex; all its members attain the minimum. This gives effective semialgebraicity, and decides membership of any specified rational probability. It does not assert existence of a rational point in every minimizing fiber. $\square$

The finite construction is uniform in the integer input $d$ and supplies no useful complexity bound. It does not compute all-size native pressure. Positivity and computability of $a_d$ make $-\log_2a_d$ computable; that logarithmic rate is not asserted algebraic.

## 7. Original rational certificates and strict optimized cofinality

**Definition 7.1 (unchanged certificate predicate).** Use exactly $V_{\rm cond}$ of [COK, Definition 4.3][COK]. Its input is $d\ge1$, a rational nonnegative array $w$ on the entire $S_d$, rational $C>0$ and a finite string. Recompute the complete list and every $R_\eta(\operatorname{supp}w)$. For each nonempty type the string must give every full context row and every owned outcome entry of every kernel. Entries must be positive rationals and each row must sum to one. Test (NWO.20) by exact rational arithmetic. Missing, duplicate, incorrectly indexed or malformed additional data are rejected. Empty relations need no arrays. At zero use only the canonical empty witness, subject to valid input checks. This is the original total finite verifier specification, without an implementation claim; the closed real system of §5 does not alter it.

**Theorem 7.2 (strict rational-cap completeness at the optimized endpoint).** Among rational probabilities $\nu$ and certificates accepted by Definition 7.1, no cap $C<a_d$ is accepted and every rational $C>a_d$ is accepted at some $\nu$. Consequently

$$
\inf\{C:\exists\,\nu\in\Delta(S_d)\cap\mathbb Q^{S_d},\pi,\quad
V_{\rm cond}(d,\nu,C,\pi)\}=a_d.
\tag{NWO.22}
$$

Proof. An accepted label has $C\ge\Omega_d(\nu)\ge a_d$ by Theorem 2.1. Conversely take rational $C>a_d$ and a real minimizer $\mu$. Choose $\delta>0$ with $(1+\delta)a_d<C$. Theorem 3.2 gives a rational $\nu$ on exactly the same support with $\Omega_d(\nu)\le(1+\delta)a_d<C$. Corollary 2.2 supplies complete positive rational arrays at this very cap. This proves both assertions and the infimum.

As a finite algorithm specification, fair enumeration of rational probabilities and their complete rational arrays, with the exact finite predicate, terminates with a witness for every such strict $C$. The separate algebraic calculation decides strict comparison of a rational $C$ with $a_d$. Neither enumeration nor density proves termination at equality. $\square$

**Proposition 7.3 (boundary acceptance is a separate requirement).** If $a_d$ is irrational it is not itself a rational cap input. If $a_d$ is rational, acceptance there requires both an attaining rational probability and positive rational arrays attaining every required type inequality. Real algebraic attainment and nonnegative real closed kernels supply neither requirement by themselves.

Proof. Soundness at $C=a_d$ forces $\Omega_d(\nu)=a_d$. The input rules require rational $\nu$ and strictly positive rational full arrays. Conversely those data satisfying the inequalities are exactly a boundary label. Theorem 6.2 guarantees only algebraic coordinates and Theorem 5.1 permits zero entries; their conclusions therefore do not imply these stronger requirements. $\square$

**Proposition 7.4 (a fixed-weight strict-positive boundary failure).** At $d=1$ take $w(\alpha)=1$ and $w(\beta)=w(C_0)=0$. Then $\Omega_1(w)=1$, but Definition 7.1 rejects cap $C=1$ at this weight.

Proof. The max/sum bounds both equal one. The full list includes one locally owned root seed with declared domain $\{\alpha,\beta,\mathsf{branch}\}$ and owner table $(2,1),(1,0),(0,0)$, respectively. Its relation consists only of the alpha assignment. At $k=0,C=1$, its inequality is $1\le Q(\alpha)$. A positive normalized three-entry row has $Q(\alpha)<1$, making this impossible. The unused declared outcomes cannot be deleted: all full rows of this original type are required. The closed real row $(1,0,0)$ attains its local boundary. For every rational $C>1$, Corollary 2.2 gives positive rational arrays for all types. This is a fixed-weight example, not a claim of failure at every probability at the optimized depth-one boundary. $\square$

## 8. Native consumer, credited endpoints and the remaining gap

**Corollary 8.1 (exact fixed-depth certified rate supremum).** Every accepted probability label gives the inherited native consequences

$$
\beta_d(\nu)\le C,\qquad
M_1(D)\ge\left\lceil C^{-2^{D-d}}\right\rceil\quad(D\ge d),\qquad
\lambda\ge-2^{-d}\log_2C.
\tag{NWO.23}
$$

The supremum of accepted lower endpoints at this depth is exactly $-\log_2a_d$ in block-rate units, and $-2^{-d}\log_2a_d$ in native-rate units.

Proof. The all-size bound is Theorem 2.3. The mass-to-memory and rate transport is the credited [COK, Theorem 7.1][COK], with the unchanged original quantifiers in Definition 1.2. Its premise is a cap for every complete template at every length under the one whole-block probability. Our accepted label supplies precisely that premise, keeping all correlated code fibers and arbitrary original off-target queries. The proof kernels, support descriptors and owner tuples are mathematical tables, not reader inputs or free observations. Theorem 7.2 makes accepted rational caps approach $a_d$ from above; soundness bounds them below by $a_d$. Continuity of $-\log_2C$ at the positive endpoint gives both supremum statements. $\square$

**Convention 8.2 (credited paid realization and separate costs).** The inherited representative scan in [COK, Proposition 7.2][COK] and [GDB, §9][GDB] uses the actual literals $Rq$, $q\in W_D$, before the request. Its bounds are $2^D-1$ Reads, maximum address length $D$ and $(D-1)2^D+1$ submitted letters. An installed nonconstant late prescription queries one actual representative owner literal before the count, and the full factor decoder supplies every authentic future reply. Complete export and paid access isolation retain their original premises. The scan is credited here, not an additional construction or a preparation-cost optimum. Installed tables, selection work, workspace, authentication, handoff, lawful entry and physical time are not made free. Transport through a block root requires an actually present subtree; absent slots are never treated as subtree inputs. No recovery of an arbitrary whole source, unknown age or physical space-time follows.

**Convention 8.3 (inherited depth-two endpoint).** [COK, §9][COK] records the credited ordinary supplier equality

$$
\Omega_2(w)=\beta_2(w)=J_2(w)
=\max\{W-w(\alpha),W-w(\beta),w(\alpha)+w(\beta)+t\},
$$

where $W=\sum_xw(x)$ and $t$ is the maximum weight of a branch state. Its optimized endpoint $17/25$, with weights $(8,8,1,\ldots,1)/25$ on the eleven states, is inherited there from RCE/NCM/NPC. It is not a new numerical result of this volume. Exact acceptance by that older recursive-plus-range grammar does not establish positive conditional-kernel boundary acceptance.

**Open problem 8.4 (joint completion and native optimizer-cofinality).** The credited native semantic identity is

$$
b_d=\min_{\mu\in\Delta(S_d)}\beta_d(\mu)=2^{-\sigma_d},
\qquad
\lambda=\sup_{d\ge1}2^{-d}\sigma_d.
$$

Theorem 2.3 gives $b_d\le a_d$, hence $-\log_2a_d\le\sigma_d$. Equality $a_d=b_d$ at general depth remains unproved. The exact support-preserving rational bridge closes the real/rational issue for this finite envelope; it gives no reverse native inequality.

The missing relation is global compatibility of the local laws through shared actual owners, full guards, original joint weights and actual-tree zeros. A feasible local law or a closed-kernel solution need not extend to one actual network law. Even jointly realized local marginals need not have vanishing loss $\Delta(P)$ in (NWO.11); kernel relative-entropy and pointwise losses also refer to that same actual law. Any pressure equality argument must control the relevant losses on a common realization, rather than combine independently attainable marginal optima.

The raw zero-free, influence, coupling and specified interpolation failures in [GDB, §§4–6][GDB] concern other mandatory premises, none used here. Its equal-neighborhood pressure separation in §8 permits a loose finite outer envelope such as $\Omega_d$ and does not refute its computability. The normalized perturbation kernels and softened seed or actual-tuple carriers in [SCP][SCP] differ from the conditional proof kernels $Q$ here. Their additive estimates do not bound support-varying $\Omega_d$; §4 therefore contradicts none of them. Strictly positive proof rows do not remove native compatibility zeros. Positivity, bounded incidence and finite enumeration supply no mixing theorem, width bound or effective native length cutoff.

The all-size cofinal-verifier and effective length-tail obligations recorded in GDB/SCP remain open. No sharp native pressure or rate, general exact $M_1(D)$, efficient synthesis, implemented verifier, physical service theorem or empirical machine-learning claim is established. The credited interval $(1/8)\log_2(33/13)\le\lambda<3/16$ and $M_1(3)=4$ remain unchanged, as does the broader minimal-relations/internal-observer/mutual-recovery frontier.

## 9. Attribution and evidence limits

**Convention 9.1 (owners and additional content).** COK owns the finite actual-owner-group family, its support-dependent joint tests, positive-kernel minimax, all-network rule, common-law loss and fixed-rational-weight certificate specification. RRN/CBN and NPC/FMR remain the credited owners of its underlying exact representation and original-task transport. GDB owns its same-tuple contraction, raw analytic obstructions and individual-pressure neighborhood boundary. SCP owns its deletion/softening results and the support-preserving rational approximation method used here.

The additional repo-derived deductions in this volume are (NWO.13)–(NWO.15), the all-types native boundary value and entering simultaneous witnesses in §4, the exact closed-kernel epigraph on every support in §5, the algebraic endpoint and algebraic minimizing law in §6, and strict optimized cofinality for the unchanged rational conditional certificates in §7. The inherited minimax and entropy proofs are included to expose the full-row and common-law premises needed by those deductions. They are credited reuse, not additional claimed novelty.

**Convention 9.2 (mature mathematical machinery).**

| Source or method | Exact use and limit |
| --- | --- |
| [COK][COK], Definitions 1.3–2.5, Theorems 3.1–4.2 and Definition 4.3 | Original finite carrier, exact support tests, full conditional arrays and all-size soundness. This volume proves the additional weight optimization and epigraph claims. |
| [GDB][GDB], §§1–2, 4–8 and 11 | Native observation and weight boundaries; specified analytic and individual-pressure obstructions. No global completion premise is imported. |
| [SCP][SCP], Proposition 5.2 and §6 | Credited support-preserving rational approximation; the separate positive-model verifier obligation is retained. |
| [Sion][Sion], Theorem 3.4 | Compact convex minimax for the regularized finite domains of Theorem 2.1. No arbitrary-network extremum is exchanged. |
| Finite entropy, relative entropy and Gibbs variational identities, as used in COK | One local law per objective and one actual global law in Theorem 2.3. No independent marginal substitutions. |
| [Basu][Basu], Theorem 2.1 and §2.1.1; real closed fields and algebraic root isolation | Effective finite polynomial projection, endpoint determination and algebraic sampling in §§5–6. No complexity or native all-size decision follows. |

The mathematical evidence consists of the displayed ordinary deductions and the canonical COK/GDB/SCP reference bodies. Literature citations identify mature machinery through those bodies; no further literature search or worldwide originality assertion is implied. The conclusions are finite-relaxation theorems, not kernel-certified declarations, numerical experiments or empirical findings.

[COK]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[GDB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[SCP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SOFT_CONSTRAINT_PRESSURE.md
[Sion]: https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf
[Basu]: https://arxiv.org/html/1409.1534v1

## 追加锚（本行以下为增补区）
