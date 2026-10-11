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

## 42. Constant zero advice and the carrier-size boundary

Retain exactly the labeled source $X$, the numerical map $N$, and the target $\Omega$ of (36.1), and put

$$
\beta_0(y)=0\qquad(y\in X).
\tag{42.1}
$$

Thus every source is in the same supplied-advice cell. The prime queries, the literal-divergence convention, and the event notation $(H_y,F_y,D_y,R_y,h_y,e_y,d_y,z_y)$ are those of Definition 40.1. The anchor is

$$
x_*=(7,2),\qquad N(x_*)=27,\qquad \Omega(x_*)=1,
\tag{42.2}
$$

as supplied by Proposition 35.5 and Proposition 39.3. For a row $(h,d,z)$ in the simplex

$$
\mathscr S=\{(h,d,z)\in[0,1]^3:h+d+z=1\},
\tag{42.3}
$$

consider all common measurable tape spaces, deterministic rule families, and source-indexed laws of Definition 40.1 having this row at $x_*$ and satisfying $e_y\le\delta h_y$ for every $y\in X$. The diameter is always the event-supremum quantity

$$
\Delta=\sup_{u,v\in X}\operatorname{TV}(\mu_u,\mu_v).
\tag{42.4}
$$

**Theorem 42.1 (Universal invariant at constant advice).** Every such family, on every measurable common carrier, satisfies

$$
(1-\delta)\sup_{y\in X}h_y\le\Delta.
\tag{42.5}
$$

In particular, at the anchor,

$$
\Delta\ge(1-\delta)h.
\tag{42.6}
$$

**Proof.** Write $H=\sup_y h_y$. For a fixed source $x$ use the increasing finite-record events $A_m$ of (40.6): a tape belongs to $A_m$ when its run at $x$ is a finite proposal, has length at most $m$, queries only the first $m$ primes, and outputs at most $m$. Their union is $H_x$. Since $\beta_0$ is constant, Theorem 37.2 supplies, for each $m$, one source $y_m\in B_{\beta_0}$ whose answers on those first $m$ primes agree with $x$ and whose target is greater than $m$. Finite-execution transport gives

$$
A_m\subseteq F_{y_m}.
\tag{42.7}
$$

Consequently, using the event-TV inequality and then the conditional error bound at $y_m$,

$$
\mu_x(A_m)
\le \mu_{y_m}(A_m)+\Delta
\le e_{y_m}+\Delta
\le \delta h_{y_m}+\Delta
\le \delta H+\Delta.
\tag{42.8}
$$

Continuity from below under $\mu_x$ gives $h_x\le\delta H+\Delta$. Taking the supremum over $x$ yields $H\le\delta H+\Delta$, which is (42.5). This is a universal necessity for the changed law contract; it does not use the anchor construction and does not assert that a law can be acquired from the observed integer. At $\delta=1$ the invariant is the tautology $0\le\Delta$. $\square$

**Theorem 42.2 (Attained arbitrary-measurable minimum).** Let $0\le\delta\le1$ and $(h,d,z)\in\mathscr S$. Among all measurable common carriers, the minimum diameter at $x_*$ is attained and equals

$$
\Delta_{\mathrm{meas}}^{\min}(\delta;h,d,z)=(1-\delta)h.
\tag{42.9}
$$

With a diameter cap $\Delta\le\eta$, the exact anchor region is

$$
\mathcal R_{\mathrm{meas}}(\delta,\eta)
 =\{(h,d,z)\in\mathscr S:(1-\delta)h\le\eta\}.
\tag{42.10}
$$

**Proof.** Put $t=(1-\delta)h$. The set $W=N[X]$ is countably infinite by the arithmetic supplier in Section 35. Let

$$
\Theta_\infty=\{a,b,c\}\mathbin{\sqcup}\{p_n:n\in W,\ n\ne27\}
\tag{42.11}
$$

with the full power-set sigma algebra. The deterministic rule on $a$ immediately proposes $1$; the rule on $b$ queries an infinite fixed prime sequence and therefore diverges literally; the rule on $c$ terminates with an unknown nonproposal; and the rule on $p_n$ immediately proposes the finite real number $\omega(n)$. No rule receives a source label or an integer: $p_n$ is a tape parameter, and the source dependence below is solely a stipulated law relation.

At every labeled source with $N(y)=27$, put mass $(h,d,z)$ on $(a,b,c)$. At a source with $N(y)=n\ne27$, put the following masses:

$$
\mu_y(a)=\delta h,\qquad
\mu_y(p_n)=t,\qquad
\mu_y(b)=d,\qquad
\mu_y(c)=z,
\tag{42.12}
$$

and zero mass on the other $p_m$. This depends only on the numerical value $N(y)$, so labels from distinct windows that generate the same integer receive the same law and the same deterministic outcomes.

At $x_*$ the $a$ proposal is correct and the other two atoms give literal divergence and nonproposal mass, hence the row is $(h,d,z)$. For $N(y)=n\ne27$, the $p_n$ proposal is correct, while the $a$ proposal is false only when $\omega(n)>1$. Therefore

$$
h_y=h,\qquad e_y\le\delta h,\qquad d_y=d,\qquad z_y=z
\tag{42.13}
$$

for every such source, including all zero-proposal cases when $h=0$. The law at $27$ and each law in (42.12) differ by moving mass $t$ from $a$ to $p_n$; two different laws in (42.12) differ by moving mass $t$ from one $p_n$ to another. The event-supremum definition therefore gives

$$
\operatorname{TV}(\mu_u,\mu_v)\le t,
\qquad
\operatorname{TV}(\mu_{x_*},\mu_y)=t\quad(N(y)\ne27),
\tag{42.14}
$$

so the attained diameter is exactly $t$. Equations (42.6) and (42.14) prove (42.9), and (42.10) follows by imposing the cap. The construction uses a countably infinite carrier; each individual law has finite support, but that sourcewise finite support does not make the common carrier finite. The stipulated real probability masses need not have an effective exact sampler. $\square$

**Theorem 42.3 (Finite common carriers have a different minimum).** Suppose the common tape carrier $\Theta$ is finite. If $0\le\delta<1$, every admissible family satisfies

$$
\Delta\ge\sup_{y\in X}h_y,
\tag{42.15}
$$

and hence the minimum at the anchor is

$$
\Delta_{\mathrm{fin}}^{\min}(\delta;h,d,z)=h.
\tag{42.16}
$$

If $\delta=1$, the minimum is $0$. Thus the exact finite-carrier cap region is

$$
\mathcal R_{\mathrm{fin}}(\delta,\eta)=
\begin{cases}
\{(h,d,z)\in\mathscr S:h\le\eta\},&0\le\delta<1,\\
\mathscr S,&\delta=1.
\end{cases}
\tag{42.17}
$$

**Proof.** It is enough to prove (42.15) for one fixed $x$ with $h_x>0$. Let $E=H_x\subseteq\Theta$ be the finite set of tapes that produce finite proposals at $x$. For each tape in $E$, collect its finite queried-prime set and its finite output; let $S$ be the union of those query sets and choose $K$ larger than every collected output. Enumerate the finite carrier. For a source $u$, let $\gamma(u)$ be the least index of a tape that produces a correct finite proposal at $u$, and let $\gamma(u)=0$ when no tape does so. For this contradiction only, regard $\gamma$ as a finite-valued supplied relation; it is not supplied to the original constant-advice procedure. On advice $j>0$, simulate tape $j$ with the original constant input $0$; on advice $0$, return unknown. By the definition of $\gamma$, every finite output of this advice procedure is sound on its entire advice cell. Corollary 37.3 and Theorem 37.2 therefore give a source

$$
y\in C(S,d_S(N(x)))\cap B_\gamma,
\qquad \Omega(y)>K,
\tag{42.18}
$$

with $\gamma(y)=0$; otherwise the advice procedure would make a sound finite halt on a member of $B_\gamma$. Hence no tape in the finite carrier gives a correct finite proposal at $y$, so $F_y=H_y$ as events.

The matching answers in (42.18) replay every finite run from $E$ at $y$, and the common target bound makes each of those proposals false. Thus $E\subseteq F_y$. Since $e_y=h_y$ and $e_y\le\delta h_y$ with $\delta<1$, one has $\mu_y(H_y)=0$, in particular $\mu_y(E)=0$. At $x$, $\mu_x(E)=h_x$, and therefore

$$
\Delta\ge\operatorname{TV}(\mu_x,\mu_y)\ge|\mu_x(E)-\mu_y(E)|=h_x.
\tag{42.19}
$$

Taking the supremum proves (42.15). This finite-color step uses the persistent-source theorem already established in Section 37; it does not assert a new generic transport theorem.

For attainment when $\delta<1$, use the three-point carrier $(a,b,c)$ with the same rules as in Theorem 42.2. Give every source with $N(y)=27$ the law $(h,d,z)$ on $(a,b,c)$, and every source with $N(y)\ne27$ the law

$$
(0,d+h,z).
\tag{42.20}
$$

At the anchor this is the required row. Elsewhere there is no finite proposal, so $h_y=e_y=0$ and the conditional error constraint is vacuous. The two laws have TV distance $h$, so (42.16) is attained. When $\delta=1$, use the same deterministic three-point rules and the common law $(h,d,z)$ at every source. The only possible false mass is the $a$ atom, and it is at most $h_y$, so $e_y\le h_y=\delta h_y$; the diameter is zero. The cap region (42.17) follows from these attainments and the lower bounds. $\square$

The carrier distinction is therefore exact. A larger finite carrier never improves (42.16), because the finite-color argument applies to every finite cardinality. A countably infinite common carrier already attains (42.9), even though every law in (42.12) has finite support. Sourcewise finite supports and a finite common carrier are different requirements. Pure source-independent randomness has $\Delta=0$; by (42.6), it cannot support $h>0$ when $\delta<1$. The positive construction instead uses the explicitly permitted source-correlated law relation, without an observation-based operation for selecting that law or an effective sampler for arbitrary real masses.

At the endpoints, $\delta=0$ gives the common formulas $\Delta_{\mathrm{meas}}^{\min}=\Delta_{\mathrm{fin}}^{\min}=h$, while $\delta=1$ gives zero in both carrier classes. If $h=0$, every $(0,d,z)$ row is attained with diameter zero and no conditional probability is assigned. With $\eta=0$ and $\delta<1$, both exact cap regions force $h=0$; with $\eta=1$, every simplex row is admitted. For the requested row $(\delta,h,d,z)=(1/2,1/2,1/2,0)$, the constant-zero arbitrary-measurable minimum is $1/4$, the finite-carrier minimum is $1/2$, and the earlier supplied $\beta_*$ construction has minimum $[(1-\delta)h-\delta d]_+=0$ by Theorem 41.1. The change is caused by the advice gate and the carrier class, not by a change to $X$, $N$, $\Omega$, the prime-only probes, or the literal-divergence convention.

The arithmetic inputs are exactly the every-pattern unboundedness of Section 35, the labeled source of (36.1), the persistence and finite-color results of Section 37, and the anchor facts and finite-execution marker supplier of Proposition 39.3. The event-TV and finite-record transport facts are reused from Theorem 40.2, with the normalization cited in Definition 40.1. These are ordinary theory deductions under the stipulated source-relative law contract; they make no claim about physical realization, efficiency, uniform execution horizons, literature priority, Lean, or kernel verification.

## 追加锚（本行以下为增补区）

## 43. One common reference: attained radius and the optimizer distinction

**Definition 43.1 (Common-reference radius at constant zero advice).** Retain the actual labeled source $X$, integer map $N$, and target $\Omega$ from (36.1), the common deterministic tape-dependent rules and measurable events of Definition 40.1, and the constant supplied advice $\beta_0(y)=0$ of (42.1). The anchor remains $x_*=(7,2)$, with $N(x_*)=27$ and $\Omega(x_*)=1$. Fix $0\le\delta,\eta\le1$ and an anchor row $(h,d,z)\in\mathscr S$ as in (42.3). Require

$$
e_y\le\delta h_y\quad(y\in X),\qquad
(h_{x_*},d_{x_*},z_{x_*})=(h,d,z).
\tag{43.1}
$$

In place of the diameter cap in (40.3), choose one probability measure $\nu$ on the same measurable space $(\Theta,\mathcal F)$ as all the source laws and impose

$$
\rho_\nu=\sup_{y\in X}\operatorname{TV}(\mu_y,\nu)\le\eta.
\tag{43.2}
$$

The reference may be chosen jointly with the procedure and full law family, but the chosen $\nu$ is fixed for all $y$. It is not a source input, an acquired observation, or a sampling operation. Neither (43.1) nor an anchor terminal-row condition is imposed on $\nu$. In particular, the same deterministic rules can have a conditional error greater than $\delta$ under $\nu$ without violating this definition. The optimization ranges over the common procedure, its common carrier, the full source-law family, and this one reference. Proposal probabilities away from the anchor need not equal $h$.

For a fixed procedure and family, distinguish its best reference radius

$$
\operatorname{rad}(\mu)=\inf_{\nu\in\mathcal P(\Theta,\mathcal F)}
\sup_{y\in X}\operatorname{TV}(\mu_y,\nu)
\tag{43.3}
$$

from the minimum over all admissible procedures and families. An assertion of attainment specifies a reference realizing the radius, not only the infimum in (43.3). The event-supremum TV normalization is (40.2). Its standard finite-space sum formula, triangle inequality and bounded-test dual are given in Levin and Peres, with contributions by Wilmer, *Markov Chains and Mixing Times*, second edition, [Chapter 4, Proposition 4.2, Remark 4.4 and Proposition 4.5, printed pp. 48--49](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf). The measurable-space arguments below use event inequalities directly; the finite-space citation is not an assumption that every carrier is finite.

**Theorem 43.2 (Reference-envelope necessity on the full source).** For every admissible measurable carrier, procedure, family, and common reference in Definition 43.1, put

$$
M=\sup_{y\in X}\nu(H_y),\qquad U=\sup_{y\in X}h_y.
$$

Then

$$
(1-\delta)M\le\rho_\nu,\qquad
U\le M+\rho_\nu,\qquad
(1-\delta)U\le(2-\delta)\rho_\nu.
\tag{43.4}
$$

In particular, every attainable anchor row under the radius cap satisfies

$$
(1-\delta)h\le(2-\delta)\eta.
\tag{43.5}
$$

No uniform execution horizon or sourcewise proposal probability is required.

**Proof.** Let $S_y=H_y\setminus F_y$ be the measurable event of a correct finite proposal, so that $F_y,S_y$ are disjoint and $H_y=F_y\sqcup S_y$. The signed error test

$$
g_y=\mathbf1_{F_y}-\delta\mathbf1_{H_y}
=(1-\delta)\mathbf1_{F_y}-\delta\mathbf1_{S_y}
\tag{43.6}
$$

has values $1-\delta,-\delta,0$ on $F_y,S_y,\Theta\setminus H_y$, respectively. Its oscillation is at most one, including the endpoints. More explicitly, the two event-TV comparisons give

$$
\begin{aligned}
\int g_y\,d\nu-\int g_y\,d\mu_y
&=(1-\delta)\bigl[\nu(F_y)-\mu_y(F_y)\bigr]
 +\delta\bigl[\mu_y(S_y)-\nu(S_y)\bigr]\\
&\le\bigl[(1-\delta)+\delta\bigr]\operatorname{TV}(\mu_y,\nu)
\le\rho_\nu.
\end{aligned}
\tag{43.7}
$$

Thus (43.1) implies

$$
\nu(F_y)-\delta\nu(H_y)\le\rho_\nu
\qquad(y\in X).
\tag{43.8}
$$

The single allowance in (43.7) uses the disjoint false/correct partition. Treating $F_y$ and $H_y$ as unrelated positive tests would give a different bound.

Fix an arbitrary actual source $x$. Use exactly the increasing finite-record events $A_m$ of (40.6), now for the run at $x$: the finite proposal has execution length at most $m$, queries only the first $m$ primes $P_m$, and is at most $m$. They satisfy $A_m\uparrow H_x$. Every finite real proposal, including a negative one, is eventually within this upper cutoff. Constant zero advice and (37.1) supply one actual source $y_m$ with

$$
d_{P_m}(N(y_m))=d_{P_m}(N(x)),\qquad \Omega(y_m)>m.
\tag{43.9}
$$

It is chosen for the whole event before quantifying over tapes. The finite-execution transport of Corollary 37.3 and Theorem 38.2 gives the literal inclusion $A_m\subseteq F_{y_m}$, on every declared tape. Hence (43.8) yields

$$
\nu(A_m)\le\nu(F_{y_m})\le\delta\nu(H_{y_m})+\rho_\nu
\le\delta M+\rho_\nu.
\tag{43.10}
$$

Continuity from below under this one fixed $\nu$ gives $\nu(H_x)\le\delta M+\rho_\nu$. Taking the supremum over $x$ proves $(1-\delta)M\le\rho_\nu$. Although the comparison source varies with $m$, neither its laws nor its proposal events are passed through a limit; the only exhaustion is under $\nu$ at the fixed source $x$.

Separately, event-TV gives $h_y\le\nu(H_y)+\rho_\nu\le M+\rho_\nu$. Taking the supremum proves the middle inequality in (43.4). Multiplying it by $1-\delta\ge0$ and using the first inequality proves the last one. The anchor and cap give (43.5). There is no division by $1-\delta$, so the proof includes $\delta=1$, as well as $h=0$ and $\rho_\nu=0$. $\square$

**Theorem 43.3 (Exact attained measurable-carrier radius).** Under Definition 43.1 the minimum over arbitrary measurable common carriers is attained and equals

$$
\rho_{\mathrm{meas}}^{\min}(\delta;h,d,z)
=\frac{(1-\delta)h}{2-\delta}.
\tag{43.11}
$$

The exact radius-cap region is

$$
\mathcal C_{\mathrm{meas}}(\delta,\eta)
=\{(h,d,z)\in\mathscr S:(1-\delta)h\le(2-\delta)\eta\}.
\tag{43.12}
$$

A countably infinite common carrier suffices, with finite support for every source law and for the reference. The attainer can be chosen invariant under numerical duplication of the source labels.

**Proof.** Theorem 43.2 gives the lower bound. To prove actual all-source attainment, set

$$
q=\frac{h}{2-\delta},\qquad r=(1-\delta)q,
\qquad q+r=h.
\tag{43.13}
$$

Reuse the carrier and deterministic rules of (42.11). Thus $W=N[X]$ is countably infinite, and

$$
\Theta_\infty=\{a,b,c\}\mathbin{\sqcup}\{p_n:n\in W,\ n\ne27\}
$$

has its full power-set sigma algebra. Tape $a$ immediately proposes $1$, tape $b$ queries an infinite fixed sequence of primes without terminating, tape $c$ immediately returns unknown, and tape $p_n$ immediately proposes $\omega(n)$. These same rules apply to every source and every tape with supplied advice zero. The parameter $n$ in a tape name is a fixed tape parameter, not access to the hidden source integer. In particular, the divergent rule makes infinitely many execution steps; it does not return unknown or an infinite proposal.

Choose the single common reference with masses

$$
\nu(a)=q,\qquad \nu(b)=d+r,\qquad \nu(c)=z,
\qquad \nu(p_n)=0\quad(n\ne27).
\tag{43.14}
$$

It is nonnegative and normalized because $q+d+r+z=h+d+z=1$. Assign laws on every labeled source by

$$
\begin{array}{c|cccc}
 &a&b&c&p_n\\ \hline
N(y)=27 &h&d&z&0\quad(n\ne27)\\
N(y)=n\ne27 &\delta q&d+r&z&r
\end{array}
\tag{43.15}
$$

In the second line all $p_m$ with $m\ne n$ have mass zero. This line has total mass $\delta q+(d+r)+z+r=q+(d+r)+z=1$, since $\delta q+r=q$. The laws therefore are probability measures on the one declared carrier. The classification in (43.15) specifies the permitted source/tape law relation and is not a deterministic branch using $N(y)$.

At every label with numerical value $27$, the proposal on $a$ is correct and the row is exactly $(h,d,z)$, with error zero. At every other label $N(y)=n$, the $p_n$ proposal is correct. The $a$ proposal is false precisely when $\omega(n)>1$, because every source has $N(y)>1$ and hence $\Omega(y)\ge1$. Thus the complete outcome rows are

| Actual numerical source class | $h_y$ | $e_y$ | $d_y$ | $z_y$ |
| --- | --- | --- | --- | --- |
| $N(y)=27$ | $h$ | $0$ | $d$ | $z$ |
| $N(y)=n\ne27$ | $q$ | $\delta q\,\mathbf1_{\{\omega(n)>1\}}$ | $d+r$ | $z$ |

In particular $e_y\le\delta h_y$ on every actual source, with no conditional probability assigned when $h_y=0$. Sources of target one outside $27$ are included. Numerical duplicates have the same law, target, prime responses and deterministic outcomes; no selection of a generating label occurs. Every finite-record event and Borel output restriction is measurable on the countable power-set space.

For the law $\alpha$ at numerical value $27$, the signed difference from the reference is

$$
\alpha-\nu=r(\delta_a-\delta_b),
\tag{43.16}
$$

where $\delta_\theta$ denotes a unit point mass at tape $\theta$. For the law $\gamma_n$ at $n\ne27$ it is

$$
\gamma_n-\nu=r(\delta_{p_n}-\delta_a).
\tag{43.17}
$$

In each case event-TV is at most $r$ and an indicated singleton event attains $r$. This also holds when $r=0$. Consequently $\rho_\nu=r$, proving (43.11). Necessity and this all-source attainer give (43.12), including its boundary.

The reference in (43.14) is chosen once and independently of the later source index. Its proposal probability is $q$ everywhere, and at a source of target greater than one its entire proposal mass is false. This is permitted because the error condition constrains the actual laws (43.15), not the reference. The construction does not provide an operation for acquiring those laws from advice or prime responses, or an effective exact sampler for arbitrary real masses. Its common carrier is countably infinite even though each actual law has at most four atoms and the reference has three. $\square$

**Theorem 43.4 (Exact attained finite-carrier radius).** When the common carrier is finite, the minimum and cap region are

$$
\rho_{\mathrm{fin}}^{\min}(\delta;h,d,z)
=\begin{cases}h/2,&0\le\delta<1,\\0,&\delta=1,\end{cases}
\tag{43.18}
$$

$$
\mathcal C_{\mathrm{fin}}(\delta,\eta)
=\begin{cases}
\{(h,d,z)\in\mathscr S:h\le2\eta\},&0\le\delta<1,\\
\mathscr S,&\delta=1.
\end{cases}
\tag{43.19}
$$

Both minima are attained on a three-point common carrier.

**Proof.** For any reference on any common measurable space, event-TV gives the triangle bound

$$
\operatorname{TV}(\mu_u,\mu_v)
\le\operatorname{TV}(\mu_u,\nu)+\operatorname{TV}(\nu,\mu_v),
\qquad \Delta\le2\rho_\nu.
\tag{43.20}
$$

If the carrier is finite and $\delta<1$, Theorem 42.3 gives $\Delta\ge\sup_yh_y\ge h$, so (43.20) implies $\rho_\nu\ge h/2$. This invokes the finite-color persistent-source necessity of that theorem, which applies to every finite cardinality, rather than assuming that two extreme laws describe every family.

For attainment reuse exactly its three-tape procedure: $a$ proposes $1$, $b$ diverges literally, and $c$ returns unknown. Give every source with $N(y)=27$ the law $\alpha=(h,d,z)$ and every other source the law $\gamma=(0,d+h,z)$. The anchor row is the prescribed one; away from $27$ there are no proposals, so all-source error is zero. Choose the midpoint reference

$$
\nu_{\mathrm{mid}}=(\alpha+\gamma)/2=(h/2,d+h/2,z).
\tag{43.21}
$$

Each law differs from it by moving mass $h/2$ between $a$ and $b$, so both TV distances are $h/2$. Both source classes are occupied, for example by $(7,2)$ and $(5,1)$, respectively. This proves an attained minimum for $\delta<1$, also when $h=0$.

At $\delta=1$ use the same procedure and the common law $\alpha$ at every source, with reference $\alpha$. The error is at most $h_y$ at every source and the radius is zero. Finite-record measurability and invariance under numerical duplication are immediate for these finite laws and common tape rules. Imposing the cap proves (43.19). $\square$

**Corollary 43.5 (Endpoints, simplex faces and the strict carrier separation).** All regions (43.12) and (43.19) include their boundary rows and attainments. They have the following consequences.

1. At $\delta=0$, both minima equal $h/2$. At $\delta=1$, both are zero and every simplex row is admitted for every $\eta\ge0$.
2. If $h=0$, every row $(0,d,z)$ with $d+z=1$ has a common-law attainer and radius zero. At $\eta=0$ and $\delta<1$, both regions force $h=0$; at $\eta=1$, every simplex row is admitted.
3. For $0\le\delta<1$, the largest anchor proposal mass at radius cap $\eta$ is $\min\{1,(2-\delta)\eta/(1-\delta)\}$ in the measurable class and $\min\{1,2\eta\}$ in the finite class. Within either class, the split of $1-h$ between literal divergence $d$ and finite nonproposal $z$ does not affect its minimum radius. This includes both faces $d=0$ and $z=0$ and their intersection $(1,0,0)$.
4. If $0<\delta<1$ and $h>0$, the finite minimum is strictly larger:

   $$
   \frac h2-\frac{(1-\delta)h}{2-\delta}
   =\frac{\delta h}{2(2-\delta)}>0.
   \tag{43.22}
   $$

   For fixed $h>0$, the finite minimum stays $h/2$ as $\delta\uparrow1$ and becomes zero at $\delta=1$, while the measurable minimum tends to zero continuously.

**Proof.** Substitute the specified parameters into (43.11)--(43.12) and (43.18)--(43.19), dividing only when $1-\delta>0$. The simplex imposes $h\le1$; every remaining nonnegative split $d+z=1-h$ is realized by the corresponding full-source attainer. Equation (43.22) follows by a common denominator. All zero-proposal statements use the inequality $e_y\le\delta h_y$ itself, not an undefined conditional ratio. The common law at $h=0$ places masses $d,z$ on the divergent and unknown tapes. A larger finite carrier cannot improve (43.18), whereas (43.15) already realizes the measurable optimum on a countably infinite carrier. $\square$

**Proposition 43.6 (Best references for the two existing diameter constructions).** Put $t=(1-\delta)h$. The countable private-atom family (42.12), including its law at $27$, has attained best reference radius

$$
\operatorname{rad}(\mu^{42.2})=t.
\tag{43.23}
$$

For $\delta<1$ the two-law finite family (42.20) has attained best radius $h/2$, so it minimizes both finite-carrier diameter and finite-carrier radius. For $\delta=1$ the common-law attainers have both quantities zero.

**Proof.** In (42.12), each source of numerical value $n\ne27$ has mass $t$ on its own distinct atom $p_n$. Since $W\setminus\{27\}$ is countably infinite, enumerate distinct such values $n_j$. For any probability reference $\nu$ on the same power-set space, countable additivity gives

$$
\nu(\{p_{n_j}\})\longrightarrow0.
\tag{43.24}
$$

Indeed these singletons are disjoint and their masses have sum at most one. The singleton event at $p_{n_j}$ implies

$$
\sup_{y\in X}\operatorname{TV}(\mu_y,\nu)
\ge\sup_j\bigl|t-\nu(\{p_{n_j}\})\bigr|\ge t.
\tag{43.25}
$$

Choosing the law at $27$ as the reference gives distance $t$ to every other law by (42.14), and zero to itself. This proves (43.23) with attainment, for all endpoints as well. Only the private atoms of this particular family are used; their radius conclusion is not a lower bound for every admissible family.

The finite family has only the two distinct laws $\alpha,\gamma$ of Theorem 43.4, with TV distance $h$. Their midpoint has radius $h/2$, and (43.20) prevents any smaller radius. Its finite diameter optimality is Theorem 42.3, while its finite radius optimality is Theorem 43.4. If $h>0$ and $\delta<1$, then $t/(2-\delta)<t$, so the old countable diameter attainer does not attain the measurable radius minimum; this includes $\delta=0$. When $h=0$ or $\delta=1$, $t=0$ and it attains both zero minima. $\square$

**Theorem 43.7 (Every measurable radius attainer has diameter twice its radius).** Suppose $0\le\delta<1$ and $h>0$. If an admissible procedure, full law family and common reference attain (43.11), write $r=\rho_\nu=(1-\delta)h/(2-\delta)$. Then their diameter satisfies

$$
\Delta=2r.
\tag{43.26}
$$

The same diameter conclusion holds for a fixed admissible family whose best reference radius (43.3) equals $r$, even if that infimum is not attained. Consequently, for $0<\delta<1$ and $h>0$, no procedure and law family can minimize both global measurable radius and diameter. At $\delta=0$ simultaneous optima exist, and they also exist when $h=0$ or $\delta=1$.

**Proof.** Use the envelope $M$ of Theorem 43.2. Since $\delta<1$ and this radius is minimal, its inequalities give

$$
h\le\nu(H_{x_*})+r\le M+r
\le\frac r{1-\delta}+r=h.
\tag{43.27}
$$

Thus all inequalities are equalities, and with $q=h/(2-\delta)$,

$$
\nu(H_{x_*})=M=q,\qquad r=(1-\delta)q.
\tag{43.28}
$$

Take the anchor truncations $A_m$ and actual matching high-target sources $y_m$ from (43.9). They satisfy $A_m\subseteq F_{y_m}$ and $A_m\uparrow H_{x_*}$. Because $S_{y_m}$ is disjoint from $F_{y_m}$,

$$
\nu(S_{y_m})\le\nu(H_{y_m})-\nu(A_m)
\le q-\nu(A_m)\longrightarrow0.
\tag{43.29}
$$

This is a bound on their correct-proposal mass under the fixed reference, not a claim that the comparison laws converge or that their correct events are nested. On the actual comparison law, conditional error gives

$$
(1-\delta)h_{y_m}\le\mu_{y_m}(S_{y_m})
\le\nu(S_{y_m})+r.
\tag{43.30}
$$

Using the diameter on the anchor event and then the error hypothesis therefore yields

$$
\begin{aligned}
\mu_{x_*}(A_m)
&\le\mu_{y_m}(A_m)+\Delta
\le\delta h_{y_m}+\Delta\\
&\le\Delta+\frac{\delta}{1-\delta}
\bigl[\nu(S_{y_m})+r\bigr].
\end{aligned}
\tag{43.31}
$$

Taking the limit of the fixed-anchor probabilities and using (43.29) gives

$$
h\le\Delta+\frac{\delta r}{1-\delta}
=\Delta+\delta q,
\qquad \Delta\ge h-\delta q=2r.
\tag{43.32}
$$

This includes $\delta=0$; division was only by $1-\delta>0$. The reverse bound is (43.20), proving (43.26).

For the assertion about a reference infimum, suppose $\operatorname{rad}(\mu)=r$. For any $\varepsilon>0$, choose one reference with $\rho_\nu\le r+\varepsilon$ and use its envelope $M$. Theorem 43.2 and the anchor event give

$$
M\le q+\frac{\varepsilon}{1-\delta},\qquad
\nu(H_{x_*})\ge q-\varepsilon,\qquad
M-\nu(H_{x_*})\le\frac{2-\delta}{1-\delta}\varepsilon.
$$

Without assuming equality in the envelope bound, the same truncations instead give $\nu(S_{y_m})\le M-\nu(A_m)$. Repeating (43.30)--(43.31) and taking the fixed-anchor limit yields

$$
\begin{aligned}
h&\le\Delta+\frac{\delta}{1-\delta}
\bigl[M-\nu(H_{x_*})+\rho_\nu\bigr]\\
&\le\Delta+\delta q+
\frac{\delta(3-2\delta)}{(1-\delta)^2}\varepsilon.
\end{aligned}
$$

Letting $\varepsilon$ decrease to zero proves $\Delta\ge h-\delta q=2r$. Equation (43.20) applied to each such reference gives $\Delta\le2r+2\varepsilon$, and hence $\Delta\le2r$. No limit of measures or construction of an unattained center is used.

By Theorem 42.2 the global measurable diameter minimum is $t=(1-\delta)h$. If $0<\delta<1$ and $h>0$, (43.26) gives $2r=2t/(2-\delta)>t$. Thus a radius attainer cannot also minimize measurable diameter. The explicit measurable attainer in (43.15) has anchor-to-other-law distance $2r$: its difference is $2r\delta_a-r\delta_b-r\delta_{p_n}$. Two distinct nonanchor laws differ by $r(\delta_{p_n}-\delta_{p_m})$ and have distance $r$, confirming the diameter directly on actual occupied source classes. At $\delta=0$ the midpoint finite attainer has diameter $h$ and radius $h/2$, equal to both measurable minima. At $h=0$ or $\delta=1$ the common-law constructions have diameter and radius zero. $\square$

**Proposition 43.8 (A finite diameter minimizer need not minimize finite radius).** For every $0\le\delta<1$ and every $(h,d,z)\in\mathscr S$ with $h>0$, there is an admissible full-source family on a finite common carrier with diameter $h$ and attained best reference radius $2h/3$. It minimizes finite-carrier diameter but not finite-carrier radius.

**Proof.** Use the five tapes $\{a,u,v,b,c\}$ with the full sigma algebra. Tape $a$ immediately proposes $1$, tapes $u,v,b$ each diverge through infinitely many prime queries, and tape $c$ immediately returns unknown. These common rules use only supplied advice zero and prime responses. Let $\kappa=d\delta_b+z\delta_c$, and define three probability laws

$$
\alpha_a=\kappa+h\delta_a,\qquad
\alpha_u=\kappa+h\delta_u,\qquad
\alpha_v=\kappa+h\delta_v.
\tag{43.33}
$$

Assign $\alpha_a$ to every label with $N(y)=27$, $\alpha_u$ to every label with $N(y)=6$, and $\alpha_v$ to every remaining label. The classes are disjoint and exhaust $X$. They are all occupied: $(7,2)$ gives $27$, $(5,1)$ gives $6$, and $(13,26)$ gives $6059$, using Proposition 39.3 and Proposition 35.5. At the first class the row is $(h,d,z)$ and the proposal $1$ is correct; on both other classes all mass outside the unknown tape diverges, so $h_y=e_y=0$. Thus the error condition holds on all sources for every stated $\delta$, and numerical duplicates are treated identically. Every finite-record event is measurable on this finite carrier.

Each pair of laws in (43.33) differs by moving mass $h$ between its two distinct private tapes, so the diameter is exactly $h$, the finite minimum from Theorem 42.3. The reference

$$
\bar\nu=\kappa+\frac h3(\delta_a+\delta_u+\delta_v)
\tag{43.34}
$$

has distance $2h/3$ to each law, by the event-TV sum formula or the event consisting of the other two private tapes. To prove that this reference is best, let $\nu$ be any probability reference on this same carrier and put $T=\nu(\{a,u,v\})$. The singleton of each private tape has mass $h$ under its corresponding law. Averaging these three event lower bounds gives

$$
\sup_{i\in\{a,u,v\}}\operatorname{TV}(\alpha_i,\nu)
\ge h-T/3.
\tag{43.35}
$$

Under $\alpha_i$ the union of the other two private tapes has mass zero. Averaging these other three event bounds gives a lower bound $2T/3$. If $T\le h$, (43.35) is at least $2h/3$; if $T\ge h$, the second lower bound is at least $2h/3$. Thus every reference has radius at least $2h/3$, attained by (43.34). Since $2h/3>h/2$, the family fails to minimize finite radius. This is an actual all-source example, so the cooptimality of the particular two-law construction in Proposition 43.6 does not extend to all finite diameter minimizers. $\square$

**Proposition 43.9 (An exact numerical diagnostic for the two objectives).** At $\delta=1/2$ and anchor row $(h,d,z)=(1/2,1/2,0)$, the measurable radius minimum is $1/6$ and the finite radius minimum is $1/4$. The old countable diameter attainer has diameter $1/4$ and best radius $1/4$. The measurable radius attainer has diameter $1/3$. In particular, half of the minimum measurable diameter, namely $1/8$, is insufficient as a common-reference radius at this row.

**Proof.** Equations (43.11) and (43.18) give $1/6$ and $1/4$. In (43.13) one has $q=1/3$ and $r=1/6$; the reference is $(1/3,2/3,0)$ on $(a,b,c)$, the anchor law is $(1/2,1/2,0)$, and each other numerical source has masses $1/6,2/3,0,1/6$ on $(a,b,c,p_n)$. Thus every other source proposes with probability $1/3$ and has false mass at most $1/6$. The TV distances and diameter are those of (43.16)--(43.17) and Theorem 43.7. Theorem 42.2 and Proposition 43.6 give the old family's two values $1/4$. Finally (43.5) rules out radius $1/8$, since $(1-\delta)h=1/4>(2-\delta)/8=3/16$.

The source-specific conclusions (43.4), (43.11), (43.18) and (43.26), and the actual-source optimizer comparison, are ordinary `repo-derived` deductions from the unchanged arithmetic source and persistence results of Sections 35--37 and the tape constructions of Section 42. The finite-record exhaustion and deterministic transport are reused from Sections 38--40. The event-TV, triangle and finite-space sum facts cited in Definition 43.1 are standard intermediate ingredients, rather than newly claimed general TV theorems. In this contract positive radius permits a stipulated source-correlated law relation; pure source-independent randomness has a common law and radius zero when that law is chosen as reference. By (43.5), at $\delta<1$ radius zero forces $h=0$. The constructions provide no law-acquisition operation, effective sampler for arbitrary real masses, magnitude promise, uniform execution bound, physical realization, literature-priority claim or Lean/kernel verification. $\square$

## 追加锚（本行以下为增补区）
