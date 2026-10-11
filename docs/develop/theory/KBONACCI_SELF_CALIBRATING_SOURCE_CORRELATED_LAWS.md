# K-bonacci self-calibration with source-correlated tape laws

## 40. Persistent-source calibration under a bounded change of tape law

**Definition 40.1 (Source-indexed laws and three terminal probabilities).** Retain the labeled arithmetic source $X$, numerical map $N$ and target $\Omega$ of [Section 36, equation (36.1)](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#36-local-self-calibration-from-window-and-prime-support-side-information), and the supplied observation $\beta:X\to E$ with finite attained range, joint cells $J_\beta$ and persistent set $B_\beta$ of [Definition 37.1](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#37-finite-valued-advice-and-persistent-obstruction-to-adaptive-upper-calibration). In particular, $\Omega(y)=\omega(N(y))$ counts distinct prime divisors. Numerical coincidences between windows do not identify their labeled sources.

On one measurable space $(\Theta,\mathcal F)$, fix one deterministic tape-dependent procedure with the source inputs of Definition 38.1: the supplied value $\beta(y)$ and Boolean answers to prime queries $p\mid N(y)$. Its rules are common to every source and every declared tape. The unknown label $y$, the integer $N(y)$, a magnitude promise and additional predicates are not inputs. All fixed parameters are shared by the entire source family. Replace only the common-law requirement of Definition 38.1 by a family of probability measures $(\mu_y)_{y\in X}$ on $(\Theta,\mathcal F)$; source $y$ uses law $\mu_y$. Thus source/tape correlation is permitted as a stipulated relation. Neither a distribution on $X$ nor a method for acquiring $\beta(y)$ or selecting a tape from $\mu_y$ is assumed.

Retain the finite-record measurability requirements of Definition 38.1, including Borel restrictions on real outputs. Let $L_y$ be finite literal termination, $H_y\subseteq L_y$ be finite termination with a finite real upper proposal $C_y$, and set

$$
\begin{aligned}
R_y&=L_y\setminus H_y,& D_y&=\Theta\setminus L_y,\\
F_y&=\{\theta\in H_y:C_y(\theta)<\Omega(y)\},\\
h_y&=\mu_y(H_y),&e_y&=\mu_y(F_y),\\
d_y&=\mu_y(D_y),&z_y&=\mu_y(R_y).
\end{aligned}
\tag{40.1}
$$

These events are measurable. The probabilities obey $h_y+d_y+z_y=1$. Unknown, abort and $+\infty$ are outcomes in $R_y$, not in the literal-divergence event $D_y$. There is exactly one terminal outcome per terminating run; intermediate numbers are not proposals. Write $\tau_y$ and $Q_y$ for execution length and the finite set of queried primes on all of $L_y$. Their restrictions to $H_y$ agree with Definition 38.1, and their restrictions to $R_y$ are measurable by the same finite-record contract. No uniform bound on their values is imposed.

Use the event-supremum normalization

$$
\operatorname{TV}(\mu,\nu)=\sup_{A\in\mathcal F}|\mu(A)-\nu(A)|,
\qquad
\Delta=\sup_{u,v\in X}\operatorname{TV}(\mu_u,\mu_v).
\tag{40.2}
$$

Fix $0\le\delta,\eta\le1$ and require

$$
\Delta\le\eta,\qquad e_y\le\delta h_y\quad\text{for every }y\in X.
\tag{40.3}
$$

When $h_y>0$, the second inequality is conditional false-output probability at most $\delta$. When $h_y=0$, it reads $e_y=0$ and assigns no conditional probability. The normalization in (40.2) is the standard one; on a finite space it equals half the sum of absolute mass differences. See Levin and Peres, with contributions by Wilmer, *Markov Chains and Mixing Times*, second edition, [Chapter 4, Proposition 4.2, p. 48](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf). Source-independent laws are precisely the case $\Delta=0$; (40.3) with positive diameter is a changed law contract.

**Theorem 40.2 (Joint finite-event transport and the correlation allowance).** Under Definition 40.1, every $x\in B_\beta$ satisfies

$$
h_x+\delta z_x\le\delta+\eta,
\qquad\text{equivalently}\qquad
(1-\delta)h_x\le\delta d_x+\eta.
\tag{40.4}
$$

More precisely, every such procedure and law family obey

$$
\big[(1-\delta)h_x-\delta d_x\big]_+\le\Delta,
\qquad [a]_+=\max\{a,0\}.
\tag{40.5}
$$

This includes arbitrary finite real proposals and all zero-probability cases. It imposes no common execution horizon.

**Proof.** Fix $x\in B_\beta$. Enumerate the primes increasingly and put $P_m=\{p_1,\ldots,p_m\}$ for $m\ge1$. Define two disjoint measurable events on the common tape space:

$$
\begin{aligned}
A_m&=\{\theta\in H_x:\tau_x(\theta)\le m,
\ Q_x(\theta)\subseteq P_m,\ C_x(\theta)\le m\},\\
T_m&=\{\theta\in R_x:\tau_x(\theta)\le m,
\ Q_x(\theta)\subseteq P_m\}.
\end{aligned}
\tag{40.6}
$$

Both sequences increase, with $A_m\uparrow H_x$ and $T_m\uparrow R_x$. Every finite real output is eventually at most $m$, including a negative output; no lower cutoff or countability of the output range is required. Every finite execution has finite length and uses a finite prime menu, including the empty menu and repeated queries after deduplication. These facts justify both exhaustions without a uniform horizon.

For each $m$, persistent unboundedness supplies one actual source

$$
y_m\in J_\beta(x,P_m),\qquad\Omega(y_m)>m.
\tag{40.7}
$$

Choose this source before quantifying over tapes. On a tape in either $A_m$ or $T_m$, its advice and every prime answer along the finite run at $x$ agree with those of $y_m$. The finite-execution transport of Corollary 37.3, also used in Theorem 38.2, therefore preserves the entire run and terminal outcome. On $A_m$ the transported proposal is at most $m<\Omega(y_m)$; on $T_m$ the transported outcome is still a finite nonproposal. Consequently, for this same source and as inclusions in $\Theta$,

$$
A_m\subseteq F_{y_m},\qquad T_m\subseteq R_{y_m}.
\tag{40.8}
$$

There is no exceptional set depending on a law in these inclusions: the deterministic rules apply to every tape, including tapes having probability zero at either source. The union of all relevant bounded menus is already contained in the single $P_m$.

Apply the error hypothesis at $y_m$. Since $H_{y_m}$ and $R_{y_m}$ are disjoint, (40.8) gives

$$
\mu_{y_m}(A_m)+\delta\mu_{y_m}(T_m)
\le e_{y_m}+\delta z_{y_m}
\le\delta(h_{y_m}+z_{y_m})
\le\delta.
\tag{40.9}
$$

The required TV comparison is a bounded test with values $1,\delta,0$ on the measurable partition $A_m,T_m,\Theta\setminus(A_m\cup T_m)$. Its expectation difference costs at most $\operatorname{TV}(\mu_x,\mu_{y_m})$, rather than a separate full allowance for each class. Explicitly, disjointness gives, for either law $\lambda$,

$$
\lambda(A_m)+\delta\lambda(T_m)
=(1-\delta)\lambda(A_m)+\delta\lambda(A_m\cup T_m).
\tag{40.10}
$$

Each of the two event probabilities on the right increases by at most $\operatorname{TV}(\mu_x,\mu_{y_m})$ when replacing $\mu_{y_m}$ by $\mu_x$. Their nonnegative coefficients sum to one. Combining (40.9) and (40.10) yields

$$
\mu_x(A_m)+\delta\mu_x(T_m)\le\delta+\Delta\le\delta+\eta.
\tag{40.11}
$$

This is the usual bounded-test property of TV, applied only to this finite measurable partition. Its finite-space dual formulation is standard; see Levin and Peres, with contributions by Wilmer, [Chapter 4, Proposition 4.5, p. 49](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf). That proposition uses tests in $[-1,1]$ and a factor $1/2$; replacing a test $f\in[0,1]$ by $2f-1$ gives the normalization used here. Equation (40.10) uses the event-supremum definition directly, so no assumption that the original tape space is finite is needed.

Continuity from below under the fixed law $\mu_x$ now gives $h_x+\delta z_x\le\delta+\Delta$. Substituting $z_x=1-h_x-d_x$ proves (40.4), and $\Delta\ge0$ proves (40.5). Although $y_m$ can vary with $m$, the limit is taken only for the two increasing events under $\mu_x$; no convergence of the comparison sources or their laws is asserted. Every step holds at $\delta=0$ and $\delta=1$ without division. At the first endpoint the conclusion is $h_x\le\eta$; at the second it is $0\le d_x+\eta$.

For $\eta=0$, (40.4) recovers the conclusion of Corollary 39.2 with its common-law hypothesis. That corollary's restart construction is not needed here. Independent restarts at source $y$ would use a product law built from $\mu_y$; (40.3) bounds the original law family and does not impose the same bound on those product laws. The deduction above retains the original single tape throughout. $\square$

## 41. Minimum law diameter and the full region at the supplied marker source

**Theorem 41.1 (Attained minimum on the actual arithmetic source).** Fix exactly the numerical advice $\beta_*$, source $x_*=(7,2)$, numerical set $V=\{27\}\cup\{n_j:j\ge1\}$, marker primes $q_j$ and counts $c_j$ supplied by [Proposition 39.3](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#39-output-conditioned-error-and-the-literal-divergence-tradeoff). In particular, $x_*\in B_{\beta_*}$, $N(x_*)=27$, $\Omega(x_*)=1$, and $c_j=\omega(n_j)\ge j+1$. For every $\delta\in[0,1]$ and every nonnegative row $(h,d,z)$ with $h+d+z=1$, the minimum possible pairwise law diameter among all families and common procedures of Definition 40.1 with $\eta=1$ satisfying

$$
\beta=\beta_*,\qquad e_y\le\delta h_y\ (y\in X),\qquad
(h_{x_*},d_{x_*},z_{x_*})=(h,d,z)
\tag{41.1}
$$

is attained and equals

$$
t=\big[(1-\delta)h-\delta d\big]_+
=\big[h-\delta(h+d)\big]_+.
\tag{41.2}
$$

One fixed three-tape deterministic procedure, independent of $\delta$ and the row, suffices for every attainment; only the laws vary. It has $e_{x_*}=0$. In particular, for fixed $\delta,\eta\in[0,1]$ the complete attainable set at this fixed $\beta_*,x_*$ under $\Delta\le\eta$ is the closed region

$$
\mathcal R_{\delta,\eta}
=\{(h,d,z)\in[0,1]^3:h+d+z=1,
\ (1-\delta)h\le\delta d+\eta\}.
\tag{41.3}
$$

The necessary inequality applies at every $x\in B_\beta$ for arbitrary supplied finite-range $\beta$; the sufficiency and minimum in this theorem concern the specified $\beta_*,x_*$.

**Proof.** The lower bound on diameter is (40.5), because Proposition 39.3 already establishes persistence of $x_*$ for $\beta_*$. It remains to construct a complete family attaining it. Reuse that proposition's arithmetic family and marker-search branch directly. In particular,

$$
q_j\nmid27,\qquad
q_j\mid n_i\ \Longleftrightarrow\ i=j,
\qquad c_j=\Omega(y)\ \text{if }N(y)=n_j.
\tag{41.4}
$$

The supplied branch generates $(q_j,c_j)$ in order, queries the prime $q_j$, and returns $c_j$ at the first positive answer. Each individual generation terminates. On advice zero it therefore diverges literally at numerical value $27$ and returns the correct finite value $c_j$ at numerical value $n_j$. These are the existing arithmetic and persistence conclusions of Proposition 39.3; no new marker family or arithmetic witness is required.

Take $\Theta=\{a,b,c\}$ with its full sigma algebra. On advice one the procedure returns unknown on every tape. On advice zero, tape $a$ returns the finite proposal $1$, tape $b$ uses the supplied marker-search branch, and tape $c$ returns unknown. This describes the procedure on every source and every tape. In particular, it makes no attempt to decide whether the hidden integer is $27$ or one of the $n_j$: the marker branch distinguishes them only through its prime answers.

For the specified $\delta,h,d,z$, define probability vectors in the order $(a,b,c)$ by

$$
\alpha=(h,d,z),\qquad
\gamma=(h-t,d+t,z).
\tag{41.5}
$$

Since $0\le t\le h$, both are nonnegative and have sum one. Assign laws to every labeled source by

$$
\mu_y=
\begin{cases}
\gamma,&N(y)=n_j\text{ for some }j\ge1,\\
\alpha,&N(y)=27\text{ or }N(y)\notin V.
\end{cases}
\tag{41.6}
$$

The classification in (41.6) specifies the allowed source dependence of the law; it is not an additional input or branch of the deterministic procedure. The strictly increasing sequence $n_j>27$ from Proposition 39.3 makes these classes disjoint, and they exhaust $X$. All numerical duplicates receive the same advice and law, have the same target, and give the same prime answers. Thus no choice of a generating label is implicit in either (41.6) or the procedure.

For every event $A\subseteq\Theta$,

$$
\alpha(A)-\gamma(A)
=t\big(\mathbf1_{\{a\in A\}}-\mathbf1_{\{b\in A\}}\big).
\tag{41.7}
$$

The absolute value is at most $t$, with equality for $A=\{a\}$. Hence $\operatorname{TV}(\alpha,\gamma)=t$. The only possible source laws are these two, and each is assigned to an actual source: $x_*$ has law $\alpha$, and the source realizing $n_1$ has law $\gamma$. Thus the family has diameter exactly $t$, including $t=0$.

The full outcome rows are

| Actual source class | Law | $h_y$ | $e_y$ | $d_y$ | $z_y$ |
| --- | --- | --- | --- | --- | --- |
| $N(y)=27$ | $\alpha$ | $h$ | $0$ | $d$ | $z$ |
| $N(y)=n_j$ for some $j\ge1$ | $\gamma$ | $h+d$ | $h-t$ | $0$ | $z$ |
| $N(y)\notin V$ | $\alpha$ | $0$ | $0$ | $0$ | $1$ |

For the first row, the proposal $1$ is correct, the marker branch literally makes infinitely many negative queries, and unknown is a finite nonproposal. For a marker source the marker branch terminates correctly at $q_j$, while the proposal $1<c_j$ is false; both are finite outputs. For the remaining sources, advice one forces unknown before any query. These observations prove every entry, including the divergence entries, rather than merely specifying an abstract outcome table.

On the marker row, (41.2) gives

$$
h-t=\min\{h,\delta(h+d)\}\le\delta(h+d).
\tag{41.8}
$$

The other two rows have zero error. Thus $e_y\le\delta h_y$ holds on all of $X$, including sources with zero proposal probability. On the finite tape space every finite record event and every Borel restriction on a terminal real output is measurable: each is a subset of $\{a,b,c\}$. A divergent tape needs no finite terminal output. The marker searches and prime queries are precisely those already justified by Proposition 39.3, with no bound on their length across sources. Consequently this is a family satisfying Definition 40.1 and attaining (41.1) with diameter $t$.

Together with the universal lower bound, this proves an attained minimum, not only an infimum. Since $\eta\ge0$, condition $t\le\eta$ is equivalent to the inequality in (41.3). Every row in that region is therefore attained by (41.5)--(41.6), including the boundary $t=\eta$. Conversely (40.4) excludes every simplex row outside it. The intersection of the simplex with this closed half-space is closed, completing (41.3).

The minimum concerns stipulated laws and a common procedure. In (41.6) the law depends on the numerical source class, while the procedure receives only supplied advice and prime responses; existence of this family supplies no operation for acquiring the advice or generating that source-dependent law from those inputs. The real parameters in (41.5) define exact probability measures, without an effective exact sampler for arbitrary real parameters.

The source-relative bound and minimum are deductions here from the arithmetic persistence and actual marker family of Sections 37 and 39.3. The finite-execution transport and the TV facts cited in Theorem 40.2 are reused ingredients. The complete realization concerns the changed law contract and makes no literature-priority, physical-realization, uniform-runtime or resource claim. $\square$

**Corollary 41.2 (Endpoints and finite nonproposal mass).** At the fixed $\beta_*,x_*$ of Theorem 41.1 the following descriptions include their boundary rows, with all laws attained as in that theorem.

1. At $\delta=0$, the region is $h\le\eta$ within the simplex, and the minimum diameter is $h$. The marker row has error zero because $h-t=0$.
2. At $\delta=1$, every simplex row is attainable with a common law: $t=0$.
3. At $\eta=0$, the region is exactly $(1-\delta)h\le\delta d$, the common-law tradeoff of Corollary 39.2. At $\eta=1$, every simplex row is attainable.
4. If $h=0$, every $d+z=1$ is attainable with diameter zero. In particular $h+d=0$ gives $(h,d,z)=(0,0,1)$; the first two source classes then also have no proposals. No conditional probability is assigned on any zero-proposal row.
5. If $d=0$, the exact condition is $(1-\delta)h\le\eta$. For $\delta<1$ the largest attainable $h$ is $\min\{1,\eta/(1-\delta)\}$, with $z=1-h$. If $z=0$, the exact condition is $h\le\min\{1,\delta+\eta\}$, with $d=1-h$. In particular, the row $(1,0,0)$ has minimum diameter $1-\delta$ and requires a noncommon law whenever $\delta<1$.

**Proof.** Substitute the indicated parameters or simplex faces into (41.2)--(41.3). At $\delta=0$, (41.5) becomes $\gamma=(0,d+h,z)$; at $\delta=1$ it becomes $\gamma=\alpha$. For $\eta=1$, use $t\le h\le1$. For $h=0$, (41.2) gives $t=0$, and (41.8) gives zero error also at every marker source. On $d=0$ the defining inequality has the stated form; division is used only when $1-\delta>0$. On $z=0$, substitute $d=1-h$ to obtain $h\le\delta+\eta$. All attainments follow from the all-source family of Theorem 41.1, so no endpoint is obtained only as a limit. $\square$

## 追加锚（本行以下为增补区）
