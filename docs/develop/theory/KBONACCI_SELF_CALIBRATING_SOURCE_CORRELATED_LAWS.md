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
## 44. Prescribed target profiles: exact radius, saturation and support

**Definition 44.1 (Profile and support permissions).** Retain the labeled source, numerical map and target of (36.1), explicitly

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad \Omega(r,g)=\omega(N(r,g)),\qquad \beta_0(y)=0.
\end{aligned}
\tag{44.1}
$$

The common measurable carrier, one common deterministic tape-dependent procedure, finite-record measurability and events are exactly those of Definition 40.1. Source observations consist only of the supplied zero advice and prime-divisibility answers. Literal finite real proposals, finite nonproposals and divergence retain their distinct meanings. In particular every actual target is a positive integer, but no assertion that every positive integer is an attained target is made.

Fix a prescribed nondecreasing function $b:\mathbb N_{>0}\to[0,1)$ and put

$$
B=\lim_{K\to\infty}b(K)\in[0,1],\qquad
 e_y\le b(\Omega(y))h_y\quad(y\in X).
\tag{44.2}
$$

Fix only the anchor row $(h_{x_*},d_{x_*},z_{x_*})=(h,d,z)\in\mathscr S$, where $x_*=(7,2)$, $N(x_*)=27$ and $\Omega(x_*)=1$. Other source rows are free. As in Definition 43.1, choose one probability reference $\nu$ on the same carrier, fixed independently of the source, and minimize

$$
\rho_\nu=\sup_{y\in X}\operatorname{TV}(\mu_y,\nu),\qquad
\operatorname{TV}(\lambda,\kappa)=\sup_{A\in\mathcal F}|\lambda(A)-\kappa(A)|.
\tag{44.3}
$$

There is no error or terminal-row condition on $\nu$, and $\nu$ is neither an input nor a law-acquisition or sampling operation. The distinction between a design infimum and the best-reference infimum of a fixed family remains (43.3).

On an arbitrary measurable carrier, a **finitely supported law** means a finite convex combination $\sum_{i=1}^s w_i\delta_{\theta_i}$ of point evaluations, where $w_i\ge0$ and $\sum_iw_i=1$. Here $\delta_\theta(A)=\mathbf1_{\{\theta\in A\}}$ for measurable $A$; measurable singleton sets or a topology are not assumed. This definition concerns finitely many actual tapes, rather than finitely many unspecified measurable atoms. A finite common carrier means that $\Theta$ itself is finite. Requiring each $\mu_y$ to be finitely supported imposes no common finite set or common bound on the support sizes. A common countable carrier with its power-set sigma algebra permits all the constructions below.

Call the profile **strict** when $b(K)<B$ for every finite $K$. For a nondecreasing profile the alternative is that $b(K_0)=B$ at some finite index, after which $b$ is constant. In particular $B=0$ forces $b\equiv0$, whereas $B=1$ always gives a strict profile under (44.2).

**Theorem 44.2 (Exact design radii and a full-source profile attainer).** In the unrestricted measurable class, and already on a common countable carrier, the radius minimum is always attained and equals

$$
R=\frac{(1-B)h}{2-B}.
\tag{44.4}
$$

For a finite common carrier the attained minimum is $h/2$ for every profile in (44.2), including $B=1$. The unrestricted attainer can be chosen with zero error at every target-one source and with all laws invariant under numerical duplication of labels.

**Proof.** Since $b(\Omega(y))\le B$, the family satisfies the constant-budget hypothesis of Theorem 43.2 with $\delta=B$. Its existing reference-envelope inequality gives

$$
(1-B)h\le(2-B)\rho_\nu.
\tag{44.5}
$$

This is a reuse of the constant-budget necessity, including its trivial lower bound at $B=1$. The new sufficiency must satisfy every prescribed value of $b$, rather than merely its supremum.

If $h=0$, use the common law $d\delta_v+z\delta_u$ on two tapes, with $v$ literally diverging and $u$ returning unknown. Choose the same reference. Every source has zero proposal and error probability and the radius is zero. Suppose henceforth that $h>0$, and set

$$
q=\frac{h}{2-B},\qquad r=(1-B)q,\qquad q+r=h.
\tag{44.6}
$$

On the carrier $\Theta=\{v,u\}\sqcup\{a_j:j\ge1\}$ with its full sigma algebra, tape $a_j$ immediately proposes the integer $j$. Tape $v$ makes an infinite fixed sequence of prime queries without terminating, and tape $u$ immediately returns unknown. These rules apply at every source and on every tape. The index $j$ is a tape parameter, not a hidden source input.

Define a probability law $\lambda$ on the proposal tapes by its tails:

$$
T_1=1,\qquad T_k=B-b(k)\ (k\ge2),\qquad
\lambda(\{a_j\})=T_j-T_{j+1}\ (j\ge1).
\tag{44.7}
$$

The tails are nonincreasing, lie in $[0,1]$ and tend to zero. Telescoping therefore proves nonnegativity, total mass one and $\lambda(\{a_j:j\ge k\})=T_k$. Zero weights cause no difficulty. For $k\ge2$ write

$$
E_k=\{a_1,\ldots,a_{k-1}\},\qquad
f_k=\lambda(E_k)=1-B+b(k).
\tag{44.8}
$$

Choose one reference and the anchor-class law by

$$
\nu=q\lambda+(d+r)\delta_v+z\delta_u,\qquad
\alpha=h\lambda+d\delta_v+z\delta_u.
\tag{44.9}
$$

Both have total mass one by $q+r=h$. Give every label with $N(y)=27$ the law $\alpha$. For every remaining label of target $k=\Omega(y)$, define the law on the entire declared carrier as follows:

$$
\mu_y=
\begin{cases}
\nu,&k=1,\\
\displaystyle \nu-\frac{r}{f_k}\lambda|_{E_k}+r\delta_{a_k},&k\ge2,\ B<1,\\
\nu,&k\ge2,\ B=1.
\end{cases}
\tag{44.10}
$$

The notation $\lambda|_{E_k}$ denotes a restricted measure of total mass $f_k$. In the middle case $f_k\ge1-B>0$, and $r/f_k\le q$. Thus the removed mass is available at each affected atom, its total is $r$, and the added mass $r$ lies at the correct proposal $k$. Every law is nonnegative and normalized. The last case avoids division by zero when $B=1$ and $b(k)=0$.

The full rows, including the target-one cases, are

| Actual source class | $h_y$ | $e_y$ | $d_y$ | $z_y$ |
| --- | --- | --- | --- | --- |
| $N(y)=27$ | $h$ | $0$ | $d$ | $z$ |
| $N(y)\ne27$, $\Omega(y)=1$ | $q$ | $0$ | $d+r$ | $z$ |
| $N(y)\ne27$, $\Omega(y)=k\ge2$ | $q$ | $b(k)q$ | $d+r$ | $z$ |

Indeed every $a_j$ is correct at target one. At $k\ge2$ the false tapes are exactly $E_k$; when $B<1$ their mass is $qf_k-r=b(k)q$, and when $B=1$ it is $qf_k=b(k)q$. The $v$ mass is literal divergence and the $u$ mass is a finite nonproposal. The exact-error expression on the last row is not asserted at target one. For $h=0$ the earlier common law supplies all the zero-proposal rows without defining conditional probabilities.

The law specification covers all labels, including numerical duplicates and target values not distinguished by any finite observation. Its dependence on $N(y)$ and $\Omega(y)$ specifies the stipulated source/law relation; it is not a branch of the deterministic procedure. Every finite record and Borel output restriction is measurable on the declared countable power-set carrier. No claim that all integer targets occur is needed: (44.10) applies to each target that actually occurs.

For the anchor class, $\alpha-\nu=r\lambda-r\delta_v$, so event-TV is exactly $r$. For a middle-case law in (44.10), the negative difference is supported on $E_k$ and has total mass $r$, while the positive difference is $r\delta_{a_k}$. Hence its event-TV is $r$, as seen directly from either of these disjoint events. All other distances are zero. This proves $\rho_\nu=r=R$, also at $B=1$, when $r=0$ and all laws equal $\nu=\alpha$.

For the finite-carrier lower bound, reuse the finite-color argument of Theorem 42.3 and the triangle comparison (43.20). Its argument selects one actual source $y$ matching all the finitely many anchor proposal runs, with target exceeding all their outputs and with no correct proposal on any tape of the finite carrier. Thus $F_y=H_y$ and all anchor proposal tapes lie in $F_y$. The only error-budget step needed there is now

$$
h_y=e_y\le b(\Omega(y))h_y,
\tag{44.11}
$$

which still forces $h_y=0$ because this particular finite target has $b(\Omega(y))<1$. Consequently $\operatorname{TV}(\mu_{x_*},\mu_y)\ge h$ and $\rho_\nu\ge h/2$. No uniform gap from one was used in this finite-color step.

The existing three-tape construction (43.21) attains $h/2$: on tapes proposing $1$, diverging and returning unknown, assign $(h,d,z)$ at every numerical source $27$, assign $(0,d+h,z)$ elsewhere, and choose their midpoint $(h/2,d+h/2,z)$ as reference. All errors are zero, so every profile is satisfied. Both source classes occur, at $(7,2)$ and $(5,1)$ respectively. This is the reused finite-carrier mechanism, with no new source promise. $\square$

**Theorem 44.3 (Saturation and positive proposal tails below limit one).** Suppose $h>0$, $B<1$, and a design and reference attain $\rho_\nu=R$. Put $q=h/(2-B)$ and $M=\sup_y\nu(H_y)$. Then

$$
M=\nu(H_{x_*})=q.
\tag{44.12}
$$

For the anchor finite-record cutoffs, with $m\ge1$,

$$
A_m=\{\theta\in H_{x_*}:\tau_{x_*}(\theta)\le m,\
Q_{x_*}(\theta)\subseteq P_m,\ C_{x_*}(\theta)\le m\},
\tag{44.13}
$$

where $P_m$ consists of the first $m$ primes, choose any one actual source $y_m$ matching the anchor's answers on $P_m$ and having $k_m=\Omega(y_m)>m$. Then

$$
\begin{aligned}
\nu(H_{x_*}\setminus A_m)&\ge q\,[B-b(k_m)],\\
\mu_{x_*}(H_{x_*}\setminus A_m)&\ge\nu(H_{x_*}\setminus A_m).
\end{aligned}
\tag{44.14}
$$

For a strict profile both masses are positive for every finite cutoff. Thus neither the anchor law nor the reference can be finitely supported at such an optimizer.

**Proof.** Theorem 43.2 at $\delta=B$ gives $(1-B)M\le R$; the anchor event gives $h\le\nu(H_{x_*})+R\le M+R$. Since $R=(1-B)q$ and $q+R=h$, all these inequalities saturate, proving (44.12).

For any source $y$ of target $k$, the signed-error event comparison (43.6)--(43.8), with its coefficient replaced by the single number $b(k)$, gives

$$
\nu(F_y)-b(k)\nu(H_y)\le\rho_\nu.
\tag{44.15}
$$

This follows from the two disjoint false/correct event inequalities with coefficients $1-b(k)$ and $b(k)$ summing to one. It is valid on the original arbitrary measurable space, without a finite-space sum convention.

Every source is persistent at constant advice by (37.1). The actual matching-source and finite-execution results of Sections 35--38 supply the stated $y_m$ for the whole event $A_m$, independently of its tapes, and give $A_m\subseteq F_{y_m}$. Therefore (44.15) and (44.12) yield

$$
\nu(A_m)\le b(k_m)q+R,
\qquad q-\nu(A_m)\ge q[B-b(k_m)].
\tag{44.16}
$$

The anchor TV comparison also gives $\mu_{x_*}(A_m)\le\nu(A_m)+R$. Subtracting from $h=q+R$ proves the second inequality in (44.14). These limits and inequalities concern fixed-anchor events; they do not pass the comparison laws or sources through a limit. The events $A_m$ increase to $H_{x_*}$ because each finite real proposal has finite execution length, a finite prime menu and a finite upper output cutoff. Negative real proposals are included as well.

If a law is a finite point mixture, take a cutoff covering the finite records of all its tapes that propose at the anchor. Its mass on $H_{x_*}\setminus A_m$ is then zero. Strictness and (44.14) exclude this for either named law. The bound uses the actual finite $k_m$ of one matching source; it does not assert a cutoff-independent positive lower bound. $\square$

**Theorem 44.4 (Finite-support infima, attainments and complete approximants).** Consider any one of these support classes on arbitrary measurable common carriers:

1. every source law is finitely supported, and the reference is unrestricted;
2. every source law and the reference are finitely supported;
3. only the anchor law is required to be finitely supported;
4. only the reference is required to be finitely supported.

In each class the design infimum is $R$ of (44.4). If $h=0$ it is attained. If $h>0$, it is attained exactly when $b(K_0)=B$ at some finite index. These statements also hold with a common countable carrier. In particular, a strict profile with $h>0$ has no attainment in any of these four classes, even though its unrestricted radius minimum is attained.

**Proof.** The universal lower bound is (44.5). If the profile reaches $B$, (44.7) has a finite support: $T_k=0$ for every $k\ge\max\{2,K_0\}$. The law $\alpha$ and the reference in (44.9) are then finitely supported, and (44.10) adds at most one tape at each actual source. Thus one full-source design simultaneously satisfies all four support permissions and attains $R$. Its common carrier remains countable, with no requirement that the union of these finite supports be finite. The common law for $h=0$ supplies that case.

For a strict profile with $B<1$ and $h>0$, Theorem 44.3 prevents a finite anchor law or a finite reference at an optimizer. Each of the four classes requires at least one of these, so none attains $R$.

For a strict profile with $B=1$, an exact optimizer would have radius zero. Equality of probability measures at event-TV zero would force $\mu_y=\nu=\mu_{x_*}$ for every source. If either the anchor law or reference were a finite point mixture, this would be a common finite point mixture on a finite list of tapes. Apply the finite-color selection in Theorem 42.3 to this list: choose one actual source matching every anchor proposal run in the list, beyond all their outputs, and with no correct proposal on the list. Under the common law its proposal mass is at least $h>0$ and every proposal is false. This violates $b(\Omega(y))<1$. The selection uses a finite auxiliary color relation only in the proof; it does not supply additional advice to the common procedure. Hence the zero minimum cannot be attained in any of the four classes.

It remains to prove that the restricted infima really are $R$. For every integer $L\ge1$, put

$$
c_L=b(L),\qquad b_L(k)=\min\{b(k),c_L\},\qquad
r_L=\frac{(1-c_L)h}{2-c_L}.
\tag{44.17}
$$

This monotone profile reaches its limit $c_L<1$ by index $L$. Apply the explicit laws (44.6)--(44.10) with $b_L,c_L$ in place of $b,B$. Their proposal tail law has finite support, the anchor row is exactly $(h,d,z)$, the reference is finitely supported, and each source law is finitely supported. Their errors at target $k\ge2$ are $b_L(k)h/(2-c_L)$, and at target one are zero; hence they satisfy the original profile $b$ on all sources. Their actual radius is $r_L$. Finally $c_L\uparrow B$ gives $r_L\downarrow R$, with

$$
r_L-R=\frac{h(B-c_L)}{(2-c_L)(2-B)}.
\tag{44.18}
$$

Thus these are complete lawful approximants in all four classes, including $B=1$, where their radii decrease to zero. The lower bound and these approximants establish an infimum, without asserting an unattained boundary reference exists. $\square$

**Theorem 44.5 (A fixed finite-anchor family has a strict gap).** Suppose $h>0$ and the profile is strict. Fix an admissible common procedure and a full law family whose anchor law is finitely supported. Its best-reference radius, allowing every probability reference on the given carrier, satisfies

$$
\operatorname{rad}(\mu)>R.
\tag{44.19}
$$

This holds even if the best-reference infimum of this fixed family is not attained. More precisely, if $B<1$, choose $m$ with $\mu_{x_*}(A_m)=h$ and one actual matching source of target $k>m$. Then

$$
\operatorname{rad}(\mu)\ge
\frac{(1-B)h}{2(1-B)+b(k)}
>\frac{(1-B)h}{2-B}.
\tag{44.20}
$$

If $B=1$, one actual source selected using the finite list supporting the anchor law has a finite target $k$ for which

$$
\operatorname{rad}(\mu)\ge\frac{(1-b(k))h}{2}>0.
\tag{44.21}
$$

The matching sources in these bounds are fixed before the reference is varied.

**Proof.** A finite anchor point mixture permits the stated $m$, by covering its finitely many proposal records. For $B<1$, fix one matching source of target $k>m$, so $A_m\subseteq F_y$. For any reference write $s=\rho_\nu$ and $M=\sup_y\nu(H_y)$. Theorem 43.2 and (44.15) give

$$
M\le\frac{s}{1-B},\qquad
h-s\le\nu(A_m)\le b(k)M+s.
\tag{44.22}
$$

It follows that $h\le s[2+b(k)/(1-B)]$, which proves the first inequality in (44.20). Since $b(k)<B$, its denominator $2(1-B)+b(k)$ is strictly smaller than $2-B$, proving the strict comparison. Both denominators are positive. This bound holds for every reference on the fixed carrier, so it passes to their infimum without taking a limit of measures.

For $B=1$, let $T$ be the finite list of anchor-support tapes. First choose $m$ so that every anchor proposal run on $T$ lies in $A_m$. The finite-color argument supplies one actual source $y$ matching the anchor on $P_m$, with target $k>m$ and with no correct proposal on any tape in $T$. To spell out its source quantifier, color a source by the least tape in $T$ giving a correct finite proposal there, using color zero when there is none. The associated advice procedure simulates that tape, or returns unknown at color zero, and is sound on each advice cell. Theorem 37.2 selects a persistent source in the desired finite probe cylinder above the bound; Corollary 37.3 forces its color to be zero. The selected source works simultaneously for every tape in $T$.

For this $y$, put $k=\Omega(y)$, $t=\operatorname{TV}(\mu_{x_*},\mu_y)$ and $S_y=H_y\setminus F_y$. The anchor law gives $\mu_{x_*}(S_y)=0$. The chosen anchor cutoff satisfies $\mu_{x_*}(A_m)=h$ and $A_m\subseteq F_y$. Thus

$$
(1-b(k))h_y\le\mu_y(S_y)\le t,
\qquad h\le\mu_y(A_m)+t\le b(k)h_y+t.
\tag{44.23}
$$

Eliminating $h_y$ gives $t\ge(1-b(k))h$. For every reference the event-TV triangle inequality gives $2\rho_\nu\ge t$, proving (44.21) after taking the infimum. Again $k$ is one actual finite target and $b(k)<1$.

The global restricted infimum in Theorem 44.4 is approached by changing the whole design, including the finite anchor distribution and its record cutoff. It is not the best-reference infimum of a single fixed finite-anchor family. Equations (44.20)--(44.21) show why taking unattained reference infima cannot remove this distinction. $\square$

**Proposition 44.6 (Limit-one tails and a bounded-anchor counterexample).** Suppose $B=1$, $h>0$, and a design attains the unrestricted zero radius. All its source laws and reference then equal one law $\nu$. For every $m\ge1$, there is an actual source $y$ whose proposal event has positive mass outside its own length/menu/output cutoff $A_{y,m}$, defined by (44.13) with $y$ replacing $x_*$. This does not in general imply positive mass outside every anchor proposal cutoff.

More explicitly, choose $n\ge m$ with $\nu(A_n)>0$ at the anchor, and one source $y$ matching that anchor record with $k=\Omega(y)>n$. Then

$$
\nu(H_y\setminus A_{y,m})\ge\nu(S_y)
\ge(1-b(k))\nu(A_n)>0.
\tag{44.24}
$$

At the anchor itself the general event argument yields only

$$
\nu(H_{x_*}\setminus A_m)\ge[h-b(k_m)]_+
\tag{44.25}
$$

for a matching source of target $k_m>m$. In particular it does give positive anchor tails when $h=1$. A strict profile can nevertheless have an exact zero-radius optimizer with $h=1/4$, $d=3/4$, $z=0$, and with all its anchor proposals on one immediate-output tape.

**Proof.** Radius zero identifies all measures. The anchor cutoffs increase to $H_{x_*}$ of mass $h>0$, so the stated $n$ exists. The one matching source gives $A_n\subseteq F_y\subseteq H_y$. Conditional error at that actual source implies $\nu(S_y)\ge(1-b(k))\nu(H_y)\ge(1-b(k))\nu(A_n)$. Every correct proposal at $y$ is at least $k>n\ge m$, and is therefore outside $A_{y,m}$. This proves (44.24), using the same source for the entire event. Also $\nu(A_m)\le\nu(F_{y_m})\le b(k_m)\nu(H_{y_m})\le b(k_m)$, which proves (44.25). No saturation equality analogous to (44.12) follows from the limit-one envelope.

For the counterexample prescribe

$$
b(k)=1-2^{-(k-1)}\quad(k\ge1).
\tag{44.26}
$$

This is a nondecreasing strict profile with $B=1$, including $b(1)=0$. Use tapes $a$ and $t_j$ for $j\ge1$ on a countable power-set carrier. Tape $a$ immediately proposes $1$. Tape $t_j$ queries the primes other than $3$ in increasing order, and at its first positive answer proposes the integer $j$. If there is no positive answer it makes infinitely many queries and literally diverges. This is one deterministic rule for all sources and supplied advice zero.

Choose the common source law and reference to have masses

$$
\nu(a)=\frac14,\qquad \nu(t_1)=\frac14,\qquad
\nu(t_j)=2^{-j}\quad(j\ge2),\qquad \mu_y=\nu\quad(y\in X).
\tag{44.27}
$$

The geometric sum makes the total mass one. At every source of numerical value $27$ the $t_j$ searches all diverge, since $27$ has only prime divisor $3$. The anchor row is therefore exactly $(1/4,3/4,0)$, and its only proposal tape is $a$, with output $1$. Its proposal tail outside (44.13) is zero once that immediate run is included.

For any actual source of target $k\ge2$, some prime divisor differs from $3$. Every $t_j$ search therefore terminates after finitely many prime queries, and every tape proposes. Its false mass is

$$
e_y=\frac14+\nu(\{t_j:j<k\})
=1-2^{-(k-1)}=b(k),\qquad h_y=1.
\tag{44.28}
$$

At target one all finite proposals are at least one and are correct; if the unique prime divisor is $3$, the searches diverge, and otherwise they terminate. Thus $e_y=0$ at every target-one source, whether or not its numerical value is $27$. The entire actual source family satisfies (44.2), duplicate labels receive identical laws, and radius zero is exact. All finite-record and output events are measurable on the declared carrier. The common law is infinitely supported; bounded anchor proposal records do not make the anchor law finitely supported, because its divergent tapes carry the remaining mass. This separates the false universal anchor-tail assertion at $B=1$ from the valid finite-support obstruction in Theorem 44.4. $\square$

**Corollary 44.7 (Exact cap boundaries, endpoints and applicability).** For $0\le\eta\le1$, the exact attainable anchor-row regions under $\rho_\nu\le\eta$ are

$$
\begin{aligned}
\mathcal C_{\mathrm{meas}}(b,\eta)
&=\{(h,d,z)\in\mathscr S:(1-B)h\le(2-B)\eta\},\\
\mathcal C_{\mathrm{fin}}(b,\eta)
&=\{(h,d,z)\in\mathscr S:h\le2\eta\}.
\end{aligned}
\tag{44.29}
$$

The measurable formula also holds for common countable carriers. In each of the four finite-support classes of Theorem 44.4, the region is $\mathcal C_{\mathrm{meas}}(b,\eta)$ when the profile reaches its limit, and otherwise it is

$$
\mathcal C_{\mathrm{supp}}(b,\eta)
=\{(h,d,z)\in\mathscr S:h=0\ \text{or}\ (1-B)h<(2-B)\eta\}.
\tag{44.30}
$$

Thus the unrestricted and finite-common-carrier radius thresholds are closed and attained. At a strict profile the finite-support threshold is excluded for $h>0$ and every larger cap is feasible. A zero-proposal row is always attained at radius zero.

**Proof.** Equations (44.29) follow from the two minima in Theorem 44.2. For a profile reaching its limit, the finite-support construction in Theorem 44.4 attains the same boundary. For a strict profile with $h>0$, that theorem excludes equality at $R$ and its explicit approximants have radius below every $\eta>R$. This proves (44.30), including $\eta=0$.

At $B=0$ the profile is identically zero, all the design infima are $h/2$, and all are attained. A constant profile $b\equiv c<1$ reduces to Section 43: (44.7) is the single proposal tape $a_1$, the unrestricted minimum is $(1-c)h/(2-c)$ with finite source and reference supports, and the finite common-carrier minimum remains $h/2$. These are reused constant-budget cases, not additional constant-budget results.

At $B=1$ the unrestricted minimum is zero for every simplex row, attained by (44.7)--(44.10) with one common infinitely supported proposal law whenever $h>0$. Every pointwise budget is still below one. Each of the four finite-support classes then has infimum zero, but at cap zero only rows with $h=0$ are feasible; at every positive cap every row is feasible. The finite common-carrier minimum stays $h/2$. Proposition 38.4 already establishes the possibility of sure finite output with pointwise budgets approaching one; the construction here adapts the common proposal tail to the prescribed profile and to the specified anchor row.

For $h>0$ and $B>0$, the finite-common-carrier separation from the unrestricted minimum is

$$
\frac h2-R=\frac{Bh}{2(2-B)}>0.
\tag{44.31}
$$

The split $d+z=1-h$ does not affect any radius formula or support classification. The constructions explicitly supply both literal divergence and finite nonproposal tapes, so they include $d=0$, $z=0$ and $(h,d,z)=(1,0,0)$. No conditional ratio is assigned when $h_y=0$.

The positive tail statement (44.14) concerns the complement of a joint length, prime-menu and output cutoff. It implies neither an unbounded execution time nor a lower bound on query complexity. Indeed in the immediate-output attainer (44.7)--(44.10) every proposal is immediate and uses no prime query; for a strict profile its proposal tail is entirely in the unbounded integer output parameter. Divergent mass, when present, is a separate outcome and is not a long finite proposal. The real-output necessity still allows arbitrary finite real numbers, not only the integer proposals chosen for sufficiency.

The source-specific profile attainer, saturation/support obstruction, fixed-family gap and limit-one counterexample are ordinary `repo-derived` deductions under (44.1)--(44.3). The reference-envelope and finite-color mechanisms are reused from Sections 42--43; the finite-record transport and actual matching-source selection are reused from Sections 35--40. The arithmetic input is the unchanged every-pattern theorem 35.2 and labeled source (36.1); its entry-rank interface is the identity (363.13) in [FIBONACCI_ATOMIC_RELATION_GENERATION](FIBONACCI_ATOMIC_RELATION_GENERATION.md). No exact realization of all positive integer target values is required. The standard TV normalization, triangle inequality and finite-space sum/dual formulas are those of Levin and Peres, with contributions by Wilmer, *Markov Chains and Mixing Times*, second edition, [Proposition 4.2, Remark 4.4 and Proposition 4.5, printed pp. 48--49](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf). The arbitrary-measurable proofs use the event definition directly, and the explicit countable transports compute TV by their equal positive and negative masses. These standard ingredients are not new general TV claims.

All attainments and approximants specify probability laws on one common carrier and one common procedure on the full unchanged source. They supply no operation acquiring a source-dependent law from advice or prime responses, no effective exact sampler for arbitrary real probabilities, no magnitude promise or uniform execution horizon, and no physical, efficiency, literature-priority or Lean/kernel-verification claim. $\square$

## 追加锚（本行以下为增补区）

## 45. Lawful acquisition through one inherited seed

**Definition 45.1 (Preparation, handoff and acquisition error).** Retain the labeled source $X$, the maps $N$ and $\Omega$, the zero supplied advice $\beta_0$, and the prime-only consumer contract of Definition 44.1. A lawful preparation consists of one probability space $(S,\mathcal A,\mathsf P)$, common to every $y\in X$, and one deterministic source procedure. At source $y$, with seed $s$, it may use only $s$, the value $0$, and answers to queries $p\mid N(y)$. Its finite preparation records are measurable, and at every fixed $y$ its preparation terminates after finitely many transitions with probability one. The terminal record declares a consumer tape in the same measurable carrier $(\Theta,\mathcal F)$ used by the consumer. No source label, numerical value, target value, magnitude promise, law on $X$, restart, rejection conditioning or extra probe is supplied.

Write $T_y\subseteq S$ for the measurable full-probability termination event and $\phi_y:T_y\to\Theta$ for the measurable terminal-tape map; output-event measurability is part of the preparation contract. Fix one tape $\theta_0$ and extend $\phi_y$ to $S$ by setting it equal to $\theta _0$ on $S\setminus T_y$. The prepared law and its uniform acquisition error are

$$
\widehat\mu_y=(\phi_y)_*\mathsf P,
\qquad
\varepsilon=\sup_{y\in X}\operatorname {TV}(\widehat\mu_y,\mu_y),
\qquad
\operatorname {TV}(\lambda,\kappa)=\sup_{A\in\mathcal F}|\lambda(A)-\kappa(A)|.
\tag{45.1}
$$

The extension changes no probability because $\mathsf P(T_y)=1$. After the handoff the original consumer runs on the same read-only source and on the declared tape; the preparation record is not a second consumer input. The profile requirement remains

$$
 e_y\le b(\Omega(y))h_y,
\qquad b:\mathbb N_{>0}\to[0,1)\text{ nondecreasing},
\qquad B=\lim_{k\to\infty}b(k).
\tag{45.2}
$$

**Proposition 45.2 (Chronological flattening).** A lawful preparation followed by the consumer is one deterministic seed execution with the preparation transitions preceding the consumer transitions. For every source $y$ and every measurable consumer event $A\subseteq\Theta$,

$$
\mathsf P\{\text{the handed tape lies in }A\}=\widehat\mu_y(A).
\tag{45.3}
$$

In particular the probabilities of the consumer events $H_y,F_y,R_y,D_y$ after preparation are respectively $\widehat\mu_y(H_y),\widehat\mu_y(F_y),\widehat\mu_y(R_y),\widehat\mu_y(D_y)$. Every finite composite record event is measurable, and preparation divergence contributes no mass.

**Proof.** On $T_y$ the handoff is a finite transition followed by the deterministic consumer run, so the handed-tape event is exactly $T_y\cap\phi_y^{-1}(A)$. The finite composite proposal, false-proposal and nonproposal events are respectively $T_y\cap\phi_y^{-1}(H_y)$, $T_y\cap\phi_y^{-1}(F_y)$ and $T_y\cap\phi_y^{-1}(R_y)$. Literal composite divergence is

$$
(S\setminus T_y)\ \cup\ (T_y\cap\phi_y^{-1}(D_y)).
$$

The complement of $T_y$ is null. Its dummy output in (45.1) is only a measure extension; the actual execution on that complement still diverges. A finite composite record is the union, over the two finite lengths and the two finite prime menus, of the corresponding cylinder event for the seed and the finite-record event of the consumer pulled back by the measurable map $\phi_y$; this is a countable union of measurable sets. The same argument applies to each of the four terminal classes. No new random variable is introduced at the handoff, and no source is reset. $\square$

**Lemma 45.3 (Finite-record coupling and common submeasures).** Enumerate the primes as $p_1<p_2<\cdots$, write $P_m=\{p_1,\ldots,p_m\}$, and let $C_m(x)$ be the actual sources matching $x$ on $P_m$. Let $E_m(x)$ be the measurable seed event that preparation at $x$ terminates within $m$ transitions and uses only primes in $P_m$. Then $E_m(x)\uparrow T_x$, and, for every $y\in C_m(x)$, the preparation at $y$ has the same record and output as at $x$ on this entire event. In particular,

$$
\operatorname {TV}(\widehat\mu_x,\widehat\mu_y)
\le1-\mathsf P(E_m(x)).
\tag{45.4}
$$

The finite measure

$$
\rho_{x,m}(A)=\mathsf P(E_m(x)\cap\phi_x^{-1}(A))\qquad(A\in\mathcal F)
\tag{45.5}
$$

is dominated by $\widehat\mu_y$ for every $y\in C_m(x)$. Thus every lawful prepared-law map is TV-continuous in finite prime observations, and two sources with identical complete prime observations have equal prepared laws.

**Proof.** Every finite preparation uses a finite menu, so the stated events exhaust $T_x$. On $E_m(x)$, induction over the actual execution transports each preparation transition to every source matching $P_m$, with the seed fixed. This gives identical records and output tapes, without requiring a measurable diagonal in $\Theta\times\Theta$. For each $A\in\mathcal F$, the two output-event indicators agree on $E_m(x)$, and their expectation difference has absolute value at most $1-\mathsf P(E_m(x))$. Taking the event supremum proves (45.4); restricting to the same event proves (45.5)'s domination. Given $\gamma>0$, choose $m$ with $\mathsf P(E_m(x))>1-\gamma$. The cylinder $C_m(x)$ then gives a TV neighborhood of radius $\gamma$. Identical complete observations permit the same comparison for every $m$, giving equality. All comparisons hold for a whole seed event before any comparison source or individual seed is used. $\square$

**Definition 45.4 (Design and fixed-family optimization).** A lawful design consists of one common consumer of Definition 44.1, a complete family $(\mu_y)_{y\in X}$ satisfying (45.2) and the anchor row $(h,d,z)$, and a lawful preparation on its declared carrier. The global design infimum varies all these objects, including the common seed probability space. For a fixed-family acquisition problem, the consumer, its carrier and the entire family $(\mu_y)$ are fixed; only the lawful preparation varies. Neither optimization introduces a probability law on $X$. Finite support always means a finite point mixture as in Definition 44.1, including on carriers without measurable singleton sets.

## 46. Operational envelopes and a fixed-family criterion

**Theorem 46.1 (Acquisition envelope and the unrestricted lower bound).** Let

$$
M=\sup_{y\in X}\widehat\mu_y(H_y).
\tag{46.1}
$$
Every lawful preparation and every full target family satisfying (45.2) obey

$$
(1-B)M\le\varepsilon,
\qquad
(1-B)h\le(2-B)\varepsilon,
\qquad
h=h_{x_*}.
\tag{46.2}
$$
Thus, when $h>0$ and $B<1$, exact acquisition is impossible and every design has

$$
\varepsilon\ge R:=\frac{(1-B)h}{2-B}.
\tag{46.3}
$$

**Proof.** Fix a source $x$. Let $G_m(x)$ be the seed event on which the preparation and the subsequent consumer proposal both have finite composite length at most $m$, all queried primes lie among the first $m$ primes, and the final proposal is at most $m$. These events increase to the prepared proposal event at $x$ up to a null set. For the whole event $G_m(x)$, before quantifying over seeds, choose by the persistent-source theorem of Section 37 one actual source $y_m$ agreeing with $x$ on those finitely many prime answers and satisfying $k_m=\Omega(y_m)>m$.

Every seed in $G_m(x)$ replays identically at $y_m$ through both the preparation and consumer stages, and its proposal is false there. Hence

$$
G_m(x)\subseteq\phi_{y_m}^{-1}(F_{y_m}).
\tag{46.4}
$$

For $0\le c<1$, the function

$$
q_{y,c}=\mathbf 1_{F_y}-c\mathbf 1_{H_y}
$$
has values among $1-c,-c,0$ and oscillation at most one. The event definition of total variation therefore gives

$$
\widehat\mu_y(F_y)-c\widehat\mu_y(H_y)
\le \mu_y(F_y)-c\mu_y(H_y)+\varepsilon.
\tag{46.5}
$$

Indeed, $q_{y,c}+c=(1-c)\mathbf1_{F_y}+c\mathbf1_{F_y\cup H_y^c}$, and the two nonnegative event coefficients sum to one. This proves (46.5) directly on every measurable carrier. The finite-space TV dual and coupling conventions are those of Levin and Peres, with Wilmer, *Markov Chains and Mixing Times*, second edition, [Propositions 4.5 and 4.7](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf); no finite-space converse is being imported here.

Putting $c=b(k_m)$ and using (45.2), (46.4) and $b(k_m)\le B$ gives

$$
\mathsf P(G_m(x))\le B M+\varepsilon.
\tag{46.6}
$$

Continuity from below under the one fixed seed law at $x$ yields $\widehat\mu_x(H_x)\le BM+\varepsilon$. Taking the supremum over $x$ proves the first inequality in (46.2). At the anchor, event-TV gives $h\le\widehat\mu_{x_*}(H_{x_*})+\varepsilon\le M+\varepsilon$. Multiplying by $1-B$ and using the first inequality proves the second. No sequence of comparison sources is passed through a limit; only the increasing events under the fixed source $x$ are exhausted. $\square$

**Theorem 46.2 (Finite consumer carriers).** If $\Theta$ is finite, every lawful design satisfies

$$
\varepsilon\ge\frac h2.
\tag{46.7}
$$
This bound is attained for every profile, every $(h,d,z)\in\mathscr S$, and every $B$, including $B=1$.

**Proof.** Enumerate the finite carrier. The measurable anchor event $E=H_{x_*}$ has a common finite prime menu and a common finite output bound because the carrier is finite. Include in that menu a finite preparation truncation from Lemma 45.3, chosen so that the prepared laws at the anchor and at every source matching the menu differ by at most $\gamma$.

For this argument only, color an actual source by the least carrier index which gives a correct finite proposal there, and color it $0$ when no carrier tape does so. This is a finite-valued auxiliary observation, not advice supplied to the original procedure. A persistent source for this coloring cannot have color $j>0$: the auxiliary procedure that, on color $j$, runs tape $j$ gives only correct finite proposals on that color cell, contradicting Corollary 37.3 at a persistent source. Thus Theorem 37.2 supplies one actual source $y$ matching the combined menu, with color $0$ and with target larger than every anchor output. Thus every tape in $E$ is a false proposal at $y$, and color $0$ says that every finite proposal at $y$ is false. Therefore $F_y=H_y$. Since $b(\Omega(y))<1$, (45.2) forces $h_y=e_y=0$, and hence $\mu_y(E)=0$.

The two preparation laws differ on $E$ by at most $\gamma$, while $\mu_{x_*}(E)=h$. Thus

$$
 h\le |h-\widehat\mu_{x_*}(E)|+|\widehat\mu_{x_*}(E)-\widehat\mu_y(E)|
      +|\widehat\mu_y(E)-0|\le 2\varepsilon+\gamma.
$$

Letting $\gamma\downarrow0$ proves (46.7). For attainment use three tapes $a,v,u$: $a$ immediately proposes $1$, $v$ literally diverges, and $u$ returns unknown. Give the target law $(h,d,z)$ at every source with numerical value $27$, the law $(0,d+h,z)$ at every other source, and prepare the midpoint law $(h/2,d+h/2,z)$ in one finite transition without queries. The target error is zero at every source and the two endpoint distances from the midpoint are $h/2$. The anchor row is exact. This also covers $h=0$ and all simplex faces. $\square$

**Theorem 46.3 (Exact acquisition criterion on a countable discrete carrier).** Let $\Theta$ be a nonempty countable carrier with its power-set sigma algebra, enumerated without repetitions as $\{\theta_j:j\ge1\}$ in the infinite case and with sums stopped at the final index in the finite case, and let $\tau$ be the topology on $X$ generated by the finite prime-answer cylinders

$$
C(S,b)=\{y\in X:d_S(N(y))=b\},\qquad S\subset\mathbb P\text{ finite}.
\tag{46.8}
$$

For a fixed family of probability laws $(\mu_y)_{y\in X}$ on this carrier, there exists a lawful preparation with $\widehat\mu_y=\mu_y$ for every $y$ if and only if the map

$$
(X,\tau)\longrightarrow(\mathcal P(\Theta),\operatorname {TV}),\qquad y\longmapsto\mu_y,
$$

is continuous. In particular, equal complete prime observations force equal laws.

**Proof.** Necessity is Lemma 45.3: for every $\gamma>0$, a finite cylinder around $x$ has all prepared laws within $\gamma$ of $\widehat\mu_x=\mu_x$.

For sufficiency, let $U$ be uniform on $(0,1)$ and let $p_1<p_2<\cdots$ enumerate the primes. For each available tape index $j$ put

$$
F_j(y)=\sum_{i\le j}\mu_y(\{\theta_i\}),\qquad F_0(y)=0.
\tag{46.9}
$$

Each $F_j$ is $\operatorname {TV}$-continuous. After reading the first $m$ prime answers, let $C_m(y)$ be the corresponding cylinder. The fixed deterministic rule stores the real constants

$$
L_{m,j}=\sup_{w\in C_m(y)}F_{j-1}(w),\qquad
U_{m,j}=\inf_{w\in C_m(y)}F_j(w)\qquad(j\le m),
\tag{46.10}
$$

for every possible finite record, testing only available tape indices $j\le m$, and emits $\theta_j$ at the first stage with
$L_{m,j}<U<U_{m,j}$. If no such stage occurs it may diverge. For a fixed $y$, outside the countable set $\{F_j(y):j\ge0\}$ there is a unique $j$ with $F_{j-1}(y)<U<F_j(y)$. Continuity supplies a finite cylinder on which the two strict inequalities in (46.10) hold, so that seed terminates with $\theta_j$. The exceptional set is null, and the emitted index has distribution $(\mu_y(\{\theta_j\}))_j$.

The intervals used at one stage are disjoint: if $i<j$, then $F_i\le F_{j-1}$ on the same cylinder, and the two strict certificate inequalities cannot hold simultaneously. Each output event is a countable union of Borel intervals in $U$, so all finite-record and output events are measurable. The rule uses only finite observed prime answers and fixed real constants; no effective evaluation of the suprema or exact sampling algorithm for arbitrary real masses is asserted. $\square$

**Theorem 46.4 (Exact acquisition on an arbitrary measurable carrier).** Fix a nonempty measurable carrier $(\Theta,\mathcal F)$ and a family of probability laws $(\mu_y)_{y\in X}$. Since the actual labeled source set $X$ is countable, enumerate it as $x_1,x_2,\ldots$ and define the auxiliary probability measure on tapes

$$
\sigma=\sum_{i\ge1}2^{-i}\mu_{x_i},\qquad
f_y=\frac{d\mu_y}{d\sigma}.
\tag{46.11}
$$

Choose measurable nonnegative versions of these densities. For each occupied prime-prefix cylinder $C$, put

$$
\ell_C(A)=\int_A\inf_{y\in C}f_y\,d\sigma,
\qquad a_C=\ell_C(\Theta).
\tag{46.12}
$$

Under the measurable common-rule semantics of Definition 40.1, exact lawful acquisition is possible if and only if

$$
\lim_{m\to\infty}a_{C_m(x)}=1\qquad\text{for every actual }x\in X.
\tag{46.13}
$$

No topology, measurable-singleton, standard-Borel or countable-generation assumption on the consumer or seed carrier is required. The sufficiency uses the stipulated measurable common-rule semantics, with fixed shared tables; it asserts no effective finite-description or real-sampling algorithm. The measure $\sigma$ is a dominating measure on $\Theta$, not a sampled source or a law supplied on $X$.

**Proof.** Every $\mu_y$ is absolutely continuous with respect to the finite measure $\sigma$. The Radon--Nikodym theorem therefore supplies the densities in (46.11). Countability of $X$ makes their pointwise infimum measurable and makes all simultaneous almost-everywhere comparisons legitimate after a single countable union of null sets. The measure $\ell_C$ is the greatest measure dominated by every $\mu_y$, $y\in C$: any such measure $\rho$ is dominated by $\sigma$ up to a finite scalar, has a density, and that density is at most every $f_y$ almost everywhere, hence at most their infimum. In particular (46.12) is independent, as a measure, of the chosen versions and enumeration. If $C'\subseteq C$, then $\ell_{C'}\ge\ell_C$.

If preparation acquires the family exactly, the common submeasure $\rho_{x,m}$ of Lemma 45.3 is dominated by $\ell_{C_m(x)}$. Its mass tends to one, proving necessity of (46.13).

For sufficiency include the depth-zero cylinder $X$, whose fictitious parent has submeasure zero. For each occupied cylinder $C$ with parent $C^-$, put $\Delta_C=\ell_C-\ell_{C^-}$, using $\Delta_X=\ell_X$. These are positive finite measures of masses $a_C-a_{C^-}$. When that mass is positive, give a tape coordinate $W_C$ the law $\Delta_C/(a_C-a_{C^-})$; for zero mass choose a fixed tape. There are countably many nodes. Take one common seed consisting of a uniform variable $U\in(0,1)$ and these tape coordinates, with their product probability measure, independent of $U$.

The deterministic preparation begins at $X$. At a reached node $C$, it emits $W_C$ if $U<a_C$; otherwise it queries the next prime and moves to the child indicated by the answer. At every non-root reached node it already has $U\ge a_{C^-}$. Therefore the unconditional output submeasure at that node, for any measurable tape event $A$, is

$$
\mathsf P\{a_{C^-}\le U<a_C,\ W_C\in A\}=\Delta_C(A).
$$

The accumulated output submeasure along source $x$ through depth $m$ telescopes to $\ell_{C_m(x)}$. Condition (46.13) makes the preparation terminate after a finite actual prefix with probability one, and its complete output law is $\mu_x$: the increasing submeasures are dominated by $\mu_x$ and their masses tend to one. All finite record events are intervals in $U$ intersected with measurable coordinate events; output events are countable unions of these. Nodes with empty source cylinders are unreachable and receive arbitrary fixed rules. Every query precedes the handoff, and the original consumer subsequently runs on the same source. No failure is conditioned away and no restart is used.

The countable product of probability measures on arbitrary measurable spaces is the standard product-measure construction; it is represented, without standard-Borel assumptions, by `Measure.infinitePi` and its cylinder identity in [pinned Mathlib, Probability/ProductMeasure](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/ProductMeasure.lean). This supplies a common seed measure directly rather than realizing arbitrary tape laws from a real uniform variable. Radon--Nikodym domination, as in [pinned Mathlib, Measure/Decomposition/RadonNikodym](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean), and product measures are reused ingredients. Local lower-envelope and range-partition methods occur for countable-alphabet chains in Gallo, Lerasle and Takahashi, [*Markov approximation of chains of infinite order in the $\bar d$-metric*, Section 3, Lemma 3.1](https://arxiv.org/html/1107.4353v2). Their stationary-chain and coalescence assumptions are not imported: the correspondence here uses the actual countable source set and its prime-prefix tree. $\square$

**Proposition 46.5 (TV continuity is not sufficient on arbitrary measurable carriers).** On a general measurable carrier, the continuity condition in Theorem 46.3 is necessary but not sufficient.

**Proof.** Take $\Theta=[0,1]$ with its Borel sigma algebra and let the consumer always return an unknown nonproposal. Thus every target row is $(0,0,1)$. Let $x_*$ denote the anchor and encode the prime observations as bits relative to the anchor: $s_i(y)=1$ when the answer at the $i$-th prime differs from the anchor answer, and $s_i(y)=0$ otherwise. If all bits agree, set $\mu_y$ equal to Lebesgue measure $\lambda$. Otherwise let $n$ be the first index with $s_n(y)=1$, use the next $n$ bits to choose one of the $2^n$ dyadic intervals $I_{n,j}$ of length $2^{-n}$, and set

$$
\mu_y(A)=\frac{\lambda(A\setminus I_{n,j})}{1-2^{-n}}.
\tag{46.14}
$$

Every finite bit pattern used here is realized by an actual source by Theorem 35.2. At a non-anchor source, fixing the first $2n$ bits fixes its law. At the anchor, sources whose first difference is after $m$ have TV distance $2^{-n}\le2^{-m}$ from $\lambda$. Hence $y\mapsto\mu_y$ is $\operatorname {TV}$-continuous.

Suppose a lawful preparation acquired this whole family exactly. Its preparation records at the anchor exhaust a full-measure event, so for some finite record bound $m$ the event $E_m$ has positive seed mass. The pushforward of $\mathsf P|_{E_m}$ under the anchor output map is a nonzero submeasure of $\lambda$. Choose $n>m$ and a level-$n$ interval $I_{n,j}$ having positive mass under this submeasure. By the finite-pattern theorem choose one actual source whose first difference is at $n$ and whose next $n$ bits encode $j$. It matches the anchor on the entire preparation menu, so the same positive submeasure is produced at that source, while (46.14) assigns the interval $I_{n,j}$ mass zero. This contradicts exact acquisition. The obstruction is a common-submeasure failure inside every anchor cylinder, not a failure of TV continuity. $\square$

**Theorem 46.6 (Zero fixed-family infimum and exactness).** For a fixed family on any nonempty measurable carrier, let

$$
I(\mu)=\inf_{\text{lawful preparations}}
\sup_{y\in X}\operatorname {TV}(\widehat\mu_y,\mu_y).
\tag{46.15}
$$

Then $I(\mu)=0$ if and only if $y\mapsto\mu_y$ is TV-continuous in finite prime observations. On a countable power-set carrier this is also equivalent to exact acquisition. On arbitrary measurable carriers, the family in Proposition 46.5 has zero infimum without exact attainment.

**Proof.** Every prepared family is TV-continuous by Lemma 45.3, and a uniform TV limit of such families is TV-continuous by the triangle inequality. This proves necessity.

Conversely fix $\delta>0$. Call an occupied prefix cylinder $C$ certified if it has a representative $x_C\in C$ with $\sup_{y\in C}\operatorname {TV}(\mu_y,\mu_{x_C})<\delta$. Continuity with radius $\delta/2$ supplies a certified prefix around every actual source. Choose one representative for every certified node and preload, under one source-independent product seed law, tape coordinates $V_C$ of laws $\mu_{x_C}$. Query primes in increasing order and emit $V_C$ at the first certified node. The chosen node depends only on its acquired prefix. Every source reaches such a node after finitely many queries, and the output law there is within $\delta$ of its fixed target law. Finite records and output events are measurable coordinate events. This construction changes only the preparation, with the target family and consumer held fixed. It gives uniform error at most $\delta$ and therefore $I(\mu)=0$. Product-measure existence and the shared-table semantic boundary are exactly those in Theorem 46.4. The countable assertion follows from Theorem 46.3; Proposition 46.5 supplies the failure of general attainment. $\square$

## 47. Sharp global design frontiers

**Theorem 47.1 (Unrestricted and finite-carrier infima).** Let $\mathcal D_{\mathrm{all}}$ be the class of all lawful designs with arbitrary measurable carriers, and let $\mathcal D_{\mathrm{fin}}$ be the subclass with finite consumer carrier. For every profile (45.2) and anchor row $(h,d,z)\in\mathscr S$,

$$
\inf_{\mathcal D_{\mathrm{all}}}\varepsilon=R=\frac{(1-B)h}{2-B},
\qquad
\inf_{\mathcal D_{\mathrm{fin}}}\varepsilon=\frac h2,
\tag{47.1}
$$

and both infima are attained.

**Proof.** The lower bounds are Theorems 46.1 and 46.2. For the unrestricted upper bound, use the countable carrier and the tapes $v,u,a_j$ of Theorem 44.2. Put

$$
q=\frac h{2-B},\qquad r=(1-B)q,
$$

and give the proposal tapes the law $\lambda$ with tails $T_1=1$ and $T_k=B-b(k)$ for $k\ge2$, so $\lambda(a_j)=T_j-T_{j+1}$. Let

$$
\nu=q\lambda+(d+r)\delta_v+z\delta_u,
\qquad
\alpha=h\lambda+d\delta_v+z\delta_u.
\tag{47.2}
$$

The target law at every source with $N=27$ is $\alpha$. At a source of target $k\ge2$ and $B<1$, set $E_k=\{a_1,\ldots,a_{k-1}\}$ and $f_k=\lambda(E_k)=1-B+b(k)$ and prescribe

$$
\mu_y=\nu-\frac r{f_k}\lambda|_{E_k}+r\delta_{a_k};
\tag{47.3}
$$

at every other target-one source use $\nu$. When $B=1$, use $\nu$ at every non-anchor source. The target rows are $(h,d,z)$ at $27$, $(q,d+r,z)$ at other target-one sources, and $(q,b(k)q,d+r,z)$ in the notation $(h_y,e_y,d_y,z_y)$ at target $k\ge2$. The removed mass in (47.3) is available because $r/f_k\le q$; normalization follows from $q+r=h$. The distance from $\nu$ is $r$ at the anchor and at every modified source, and zero elsewhere. All duplicate numerical labels receive the same law.

Take the common seed space $(\Theta,2^\Theta,\nu)$; preparation hands the seed tape to the consumer in one transition without a prime query. It is finite at every source and gives $\widehat\mu_y=\nu$, so its uniform acquisition error is exactly $r=R$. The arbitrary real masses describe a probability measure and are not claimed to have an effective sampler. If $h=0$, use the common two-tape law $d\delta_v+z\delta_u$. The finite-carrier attainer is the midpoint construction in Theorem 46.2. $\square$

**Corollary 47.2 (Endpoint rows).** The two formulas include all endpoints. If $h=0$, both values are zero and the zero-proposal row is attained. If $B=0$, then $b\equiv0$ and $R=h/2$. If $B=1$, the unrestricted value is zero and is attained by the same construction, whereas the finite-carrier value remains $h/2$. Strictness or a plateau does not change either unrestricted infimum. The split $d+z=1-h$ enters only the endpoint laws, not the two radii.

**Proof.** These are the endpoint substitutions and the explicitly normalized seed and target laws in Theorem 47.1. $\square$

## 48. Finite-support profiles and a bounded-band arithmetic bridge

**Lemma 48.1 (Bounded-band matching sources at the anchor).** Let $S\subset\mathbb P$ be finite and let $H\ge1$ be an integer. There is an actual source $y\in X$ with the same answers as $x_*$ on every prime in $S$ and

$$
H+1\le\Omega(y)\le H+21.
\tag{48.1}
$$

No assertion that every target between these endpoints occurs is made.

**Proof.** Choose $H$ distinct primes $T$ outside $S\cup\{3\}$, and put $A_0=T\cup\{3\}$, $J=\prod_{q\in A_0}q$ and

$$
M=\prod_{q\in A_0}q^2\prod_{p\in S\setminus\{3\}}p.
$$

For every sufficiently large prime Fibonacci index $r$, the entry-rank identity (363.13) gives $\gcd(F_r,M)=1$: every prime divisor of this fixed $M$ has rank at least three, and a prime $r$ larger than all those ranks is divisible by none of them. For such $r$ impose

$$
1+F_rg\equiv q\pmod {q^2}\quad(q\in A_0),
\qquad g\equiv0\pmod p\quad(p\in S\setminus\{3\}).
\tag{48.2}
$$

The CRT gives a residue $a$ modulo $M$. All its representatives $g=a+Mt$ have the anchor answers on $S$, and every $q\in A_0$ divides $N=1+F_rg$ exactly once. The actual Fibonacci window contains $L=F_r/(10M)+O(1)$ consecutive values of $t$. For these values write

$$
1+F_r(a+Mt)=J(At+C),
\qquad A=F_rM/J,\qquad C=(1+F_ra)/J.
\tag{48.3}
$$

Here $A,C$ are integers and $A>0$. This progression is primitive. A prime dividing $F_r$ does not divide $J$, and $C\equiv J^{-1}\pmod p$ at such a prime. For $p\in S\setminus\{3\}$ the same nonzero congruence follows from $N\equiv1\pmod p$. For $q\in A_0$, division of $N\equiv q\pmod {q^2}$ gives $C\equiv(J/q)^{-1}\pmod q$, which is nonzero; also $q\mid A$. These are all prime divisors of $A$, so $\gcd(A,C)=1$ and every $At+C$ is coprime to $J$.

Use the lower linear sieve in Bordignon, Johnston and Starichkova, [*An explicit version of Chen's theorem and the linear sieve*, arXiv:2207.09452v6, Theorem 6, Table 1 and Lemmas 17--19](https://arxiv.org/html/2207.09452v6). Its sequence weight is one at each of the $L$ positive integers $At+C$ and zero elsewhere. Set $\mathcal P=\{p:p\nmid A\}$ and $g(p)=1/p$ on this sieve-prime set. For every squarefree $d$ composed of primes in $\mathcal P$, invertibility of $A$ modulo $d$ gives one residue class of $t$, hence the count is $L/d+r(d)$ with $|r(d)|\le1$, uniformly in $r$ and $d$.

Here is the full product-condition correspondence. Fix $u_0=10^9+1$, put $Q_0=\prod_{p<u_0}p$, and let $\mathcal Q_r=\{p\in\mathcal P:p<u_0\}$ with product $Q_r\mid Q_0$. For $z>\exp(4000)$ and $u\ge u_0$, Lemma 18 bounds the product with factors $(1-1/(p-1))^{-1}$ by $(1+1.452\cdot10^{-7})\log z/\log u$. The product with factors $(1-1/p)^{-1}$ over the smaller prime set $\mathcal P\setminus\mathcal Q_r$ is no larger. For $1<u<u_0$, use the same estimate starting at $u_0$ and $\log u\le\log u_0$. Thus Theorem 6's product condition holds with $\varepsilon_s=1/74$ for every $1<u<z$. The exceptional primes $\mathcal Q_r$ are omitted only from this product condition; they remain in $\mathcal P$ and are still sieved.

Take

$$
D=\frac{L}{Q_0(\log L)^3},\qquad z=D^{1/10}.
$$

For large enough $r$, $z>\exp(4000)$ and $D\ge z^2$. The theorem's remainder sum is over squarefree $d\mid\prod_{p\in\mathcal P,\ p<z}p$ with $d<Q_rD$, so it is at most $Q_0D+1=O(L/(\log L)^3)$. Its main mass is $LV(z)$, where

$$
V(z)=\prod_{p\in\mathcal P,\ p<z}(1-1/p)
\ge\prod_{p<z}(1-1/p)\ge\frac{c}{\log z}
$$

for an absolute $c>0$. The final inequality follows directly from Lemma 17's upper bound on $\sum_{p<z}1/p$ and $\log(1-t)\ge-t-t^2$ for $0\le t\le1/2$, since $\sum_p1/p^2<\infty$.

The sieve parameter is $s=\log D/\log z=10$. Its nonnegative delay-equation functions satisfy $10f(10)\ge3f(3)=2e^\gamma\log2$, so $f(10)>1/10$. Table 1 gives $C_2(1/74)=630$ and the theorem gives $h(10)=3e^{-10}/10$. The subtracted coefficient is

$$
\frac1{74}\,630e^2h(10)=\frac{189}{74}e^{-8}<\frac1{100}.
$$

The lower-sieve coefficient is therefore positive. Its main term has order at least $L/\log L$, while the remainder is $O(L/(\log L)^3)$, so a sifted quotient exists for every sufficiently large selected $r$. Any prime dividing $A$ divides none of the quotients; every other prime below $z$ has been sieved. Consequently all prime factors of this quotient are at least $z$.

The largest quotient in the actual window is $O(F_r^2)$, and

$$
\log z=\tfrac1{10}\big(\log F_r-3\log\log F_r+O(1)\big).
$$

With $S,H$ fixed, the ratio of its logarithm to $\log z$ has upper limit at most $20$, and is strictly below $21$ for all sufficiently large $r$. Thus the sifted quotient has at most $20$ prime factors even counted with multiplicity. It is coprime to $J$, whose $H+1$ primes occur in $N$ exactly once. Hence

$$
\Omega(y)=H+1+\omega(At+C)\in[H+1,H+21].
$$

The endpoint width is independent of $S$, although the index threshold depends on $S,H$. This is a new correspondence of the unchanged Fibonacci window with the cited sieve, not a new general sieve theorem or an exact-target realization claim. $\square$

**Theorem 48.2 (Sourcewise finite-support infimum and its attainment).** Let $\mathcal D_{\mathrm{sw}}$ be the class of lawful designs whose every target law $\mu_y$ is finitely supported, with a common countable carrier allowed, and let $\mathcal D_{\mathrm{anch}}$ require only the anchor law $\mu_{x_*}$ to be finitely supported. For both classes,

$$
\inf\varepsilon=R.
\tag{48.4}
$$

If $h=0$, or if the profile reaches its limit at a finite index, the infimum is attained. If $h>0$ and the profile is strict, the following are the exact remaining cases:

1. If $B<1$, neither class attains $R$.
2. If $B=1$ and $d=0$, neither class attains $R=0$.
3. If $B=1$ and $d>0$, both classes attain $R=0$.

**Proof.** For the upper infimum, choose $L\ge1$, put $c_L=b(L)$ and $b_L(k)=\min\{b(k),c_L\}$. Apply the complete countable construction (47.2)--(47.3) with $b_L$ in place of $b$ and with $B_L=c_L$. Its prepared law has finite support because its proposal tail vanishes for $k\ge\max\{2,L\}$, and every target law has that finite support together with at most one added tape $a_k$. It satisfies the original profile since $b_L\le b$, and its error is

$$
R_L=\frac{(1-c_L)h}{2-c_L}\downarrow\frac{(1-B)h}{2-B}=R.
\tag{48.5}
$$

If $b(L)=B$, then $R_L=R$ and the construction attains the boundary. This includes $B=0$.

Assume now $h>0$ and a strict profile. Suppose first that $B<1$ and fix any target design in either support class. Its anchor target law is finitely supported, so one consumer cutoff $A=A_m$ of (44.13) carries all anchor proposal mass $\mu_{x_*}(A)=h$. Fix this integer $m\ge1$, bounding the consumer records, prime indices and outputs, independently of the preparation and its tolerance. For any lawful preparation and any $\gamma>0$, Lemma 45.3 gives a finite preparation menu $P$ on whose matching cylinder the prepared laws differ by at most $\gamma$. Apply Lemma 48.1 to $S=P_m\cup P$ and $H=m+1$. This selects one actual source for the whole cutoff event, with $m+2\le k\le m+22$. Every tape in $A$ is false there. The signed test (46.5) gives

$$
\widehat\mu_y(A)\le b(k)\widehat\mu_y(H_y)+\varepsilon
\le b(m+22)M+\varepsilon.
$$

The preparation coupling and the anchor error imply

$$
 h-\varepsilon-\gamma\le\widehat\mu_y(A).
$$

Using $(1-B)M\le\varepsilon$ and then letting $\gamma\downarrow0$ yields

$$
\varepsilon\ge
\frac{(1-B)h}{2(1-B)+b(m+22)}
>\frac{(1-B)h}{2-B}=R,
\tag{48.6}
$$

because strictness gives $b(m+22)<B$. Thus the boundary is excluded in both support classes.

For $B=1$ and $d=0$, fix any finite anchor target law and any lawful preparation. Because the anchor has no divergent mass, choose measurable finite-record cutoffs $A\subseteq H_{x_*}$ and $R_0\subseteq R_{x_*}$ carrying respectively masses $h$ and $1-h$, and choose an integer $m\ge1$ bounding their records and outputs. Combine the fixed consumer menu with the preparation menu of Lemma 45.3 at tolerance $\gamma$, and apply Lemma 48.1 with the same fixed $H=m+1$ to choose one matching source with $m+2\le k\le m+22$. At the anchor, $\mu_{x_*}(A)=h$ and $\mu_{x_*}(R_0)=1-h$; at the matching source, $A\subseteq F_y$ and $R_0\subseteq R_y$. The test

$$
\psi=\mathbf1_A-b(k)\mathbf1_{H_y}
$$

has oscillation at most one. Its anchor expectation is $(1-b(k))h$, because the anchor law gives no mass to divergent tapes and $R_0\cap H_y=\varnothing$; its expectation at $y$ is at most zero, since $A\subseteq F_y$ and $\mu_y(F_y)-b(k)\mu_y(H_y)\le0$. Therefore

$$
\operatorname {TV}(\mu_{x_*},\mu_y)\ge(1-b(k))h>0.
$$
For any acquisition error, the triangle through the two prepared laws and Lemma 45.3 gives

$$
2\varepsilon+\gamma\ge(1-b(k))h,
\tag{48.7}
$$

Letting $\gamma\downarrow0$ gives the fixed-family bound $\varepsilon\ge(1-b(m+22))h/2>0$, so exact attainment is impossible. Positive anchor divergence cannot be included in the finite nonproposal cutoff and does not obey this argument.

It remains to show the positive $B=1,d>0$ case. Enumerate the primes other than $3$ as $q_1,q_2,\ldots$ and set

$$
 w_3=d,\qquad w_{q_j}=h2^{-(j+1)},\qquad
 w_0=h/2,\qquad w_u=z.
\tag{48.8}
$$

Choose a strictly increasing function $f:\mathbb P\to\mathbb N_{>0}$ with $f(p)\ge p$ and

$$
1-b(f(p)+1)\le w_p.
\tag{48.9}
$$

Choose integer values of $f$ successively in increasing prime order, larger than the preceding value and at least $p$, until (48.9) holds. The limit $b(k)\uparrow1$ makes each such choice possible. The resulting fixed table is common to the entire source family, not advice selected by the source. Use tapes $u,t_0,t_p$ ($p$ prime): $u$ returns unknown; $t_0$ queries primes increasingly until the first divisor and proposes $f(q)$; $t_p$ queries primes strictly larger than $p$ until the first divisor and proposes $f(q)$, diverging if none appears. The preparation uses one query: on the baseline atom of mass $w_0$ it emits $t_0$, on the atom of mass $w_u$ it emits $u$, and on the atom of mass $w_p$ it queries $p\mid N(y)$ and emits $t_p$ on a positive answer and $t_0$ otherwise. It terminates for every seed at every source.

For a source with prime support $P_y$, prescribe the finite law

$$
\mu_y(t_p)=w_p\ (p\in P_y),\qquad
\mu_y(t_0)=w_0+\sum_{p\notin P_y}w_p,\qquad
\mu_y(u)=z.
\tag{48.10}
$$

The seed masses sum to $w_0+z+\sum_pw_p=h/2+z+d+h/2=1$. The preparation pushforward is exactly (48.10): each prime atom either remains at its own $t_p$ or is sent to $t_0$. The law has at most $k+2$ support tapes at a source with $k$ divisors. At the anchor $P_{x_*}=\{3\}$, the row is $(h,d,z)$: $t_0$ has mass $h$, $t_3$ diverges with mass $d$, and $u$ is unknown. At an arbitrary source, only the positively weighted tape indexed by its largest divisor $q_{\max}$ diverges. Thus $d_y=w_{q_{\max}}$, $z_y=z$ and $h_y=1-z-w_{q_{\max}}$. If $f(q_{\min})\ge k=\Omega(y)$, every finite proposal is correct. Otherwise choose the largest divisor $p$ with $f(p)<k$; it is not the largest divisor of $N(y)$ because that prime is at least $k$ and $f(p)\ge p$. The next divisor makes $t_p$ a correct finite proposal. By (48.9) and monotonicity,

$$
 w_p\ge1-b(f(p)+1)\ge1-b(k).
$$

Tape $t_p$ is present with exactly that mass $w_p$, so the correct proposal mass is at least $w_p\ge1-b(k)\ge(1-b(k))h_y$. Therefore $e_y\le b(k)h_y$. Every law (48.10) is normalized and finite. All finite records and output events are measurable on the countable power-set carriers for both seeds and consumer tapes, preparation terminates at every declared seed, and the uniform acquisition error is exactly zero. Numerical duplicates and even distinct integers with identical prime supports receive identical laws. No effective sampler for the real weights or effective construction of the table from an arbitrary real profile is asserted. This proves attainment in both support classes. The cases $h=0$ and the plateau case were already covered. $\square$

**Corollary 48.3 (Support and record distinctions).** Finite consumer carrier, finitely many possible prepared outputs, finite support of each target law, finite anchor support, finite actual preparation records, a uniform query-count bound and a common finite query menu are different restrictions.

**Proof.** For a constant profile $b\equiv c$ with $0<c<1$ and $h>0$, (47.2)--(47.3) has finitely many possible prepared outputs, while its target laws use the unbounded actual target indices $a_k$ on a countable consumer carrier; it attains $R<h/2$. Thus finitely many prepared outputs cannot imply the finite-consumer lower bound. The one-query construction (48.8)--(48.10) has finite target support at each source and a uniform preparation query count of one, but infinitely many possible query primes and output tapes. Finally, let a seed $J\ge1$ have masses $2^{-J}$, query the first $J$ primes, and always emit one fixed unknown tape. Every actual preparation is finite and the output law has one point, while no common finite menu or uniform horizon bounds the preparation. These are lawful all-source constructions; no record bound is inferred from a consumer support bound. $\square$

## 49. Fixed families and operational separations

**Proposition 49.1 (Acquired laws need not be a constant reference).** For every profile there is a fixed admissible family on a finite consumer carrier with anchor row $(0,0,1)$, exact lawful acquisition error zero, and best constant-reference radius $1/2$.

**Proof.** Take two tapes $u_0,u_1$, both immediately returning unknown. Preparation queries prime $2$ once and emits the corresponding tape, with a unit seed. Prescribe its exact pushforward $\mu_y=\delta_{u_{\mathbf1_{2\mid N(y)}}}$. Every target row is $(0,0,1)$ and every error is zero. Both laws occur at actual sources: $N(7,2)=27$ is odd and $N(5,1)=6$ is even. Their TV distance is one, so the triangle inequality forces every constant reference to have radius at least $1/2$, and the midpoint achieves that value. The acquired family is source dependent through one legal query. Agreement of the global infimum with the static formula in Section 44 therefore requires Theorem 46.1; it does not follow by identifying the two optimization problems. $\square$

**Proposition 49.2 (Strict-profile optimizer support belongs to the correct carrier).** Suppose $h>0$ and $b$ is strict. If $B<1$, an optimizer at error $R$ cannot have a finitely supported prepared anchor law, even without a target-support restriction. For any $B$, a preparation with a finitely supported common seed law cannot attain $R$.

**Proof.** Below limit one, the inequalities in Theorem 46.1 saturate at $\varepsilon=R$: with $q=h/(2-B)$ one has $M=\widehat\mu_{x_*}(H_{x_*})=q$. If the prepared anchor law is a finite point mixture, one consumer cutoff $A_m\subseteq H_{x_*}$ carries all that mass. Combine its menu with an arbitrarily accurate preparation coupling of tolerance $\gamma$. Lemma 48.1 with $H=m+1$ supplies one actual matching source of target $m+2\le k\le K=m+22$, before quantifying over seeds. Transport and (46.5) give

$$
q-\gamma\le\widehat\mu_y(A_m)\le b(K)M+R=b(K)q+(1-B)q.
$$

Letting $\gamma\downarrow0$ contradicts $b(K)<B$ and $q>0$. A finite point-mixture seed yields a finite point-mixture output at every source, so this also excludes such seeds below limit one.

At $B=1$, attaining $R$ means exact acquisition. Remove zero-weight seed points from a purported finite seed mixture. Each remaining seed prepares finitely at every actual source, since its weight is positive. Flattening then gives finitely many deterministic composite tape procedures under one common finite seed law, with the exact target outcome probabilities. Collect their finite anchor proposal records and color each source by its first correct composite tape, or zero if none. The auxiliary finite-color argument in Theorem 46.2 selects one actual matching source, above all anchor proposal outputs, with no correct composite tape. Its transported proposal mass is at least $h>0$, all of it false, contradicting $b(k)<1$ at that actual finite target. Infinite seeds are thus essential to the finite-anchor exact attainer (48.8)--(48.10); a uniform one-query preparation is not a finite seed mixture. $\square$

**Corollary 49.3 (Uniform caps and the complete endpoint classification).** For a cap $0\le\eta\le1$, the globally attainable anchor rows under $\varepsilon\le\eta$ on arbitrary measurable carriers, already on countable power-set carriers, are

$$
\{(h,d,z)\in\mathscr S:(1-B)h\le(2-B)\eta\}.
\tag{49.1}
$$

On finite consumer carriers they are $\{(h,d,z)\in\mathscr S:h\le2\eta\}$. In either the sourcewise finite-target-support class or the finite-anchor-target-support class, put $R=(1-B)h/(2-B)$. A row is attainable exactly when

$$
h=0\quad\text{or}\quad \eta>R\quad\text{or}\quad
\big[\eta=R\ \text{and}\ (\text{$b$ reaches $B$ at a finite index}\ \text{or}\ (B=1\text{ and }d>0))\big].
\tag{49.2}
$$

In particular, for $h>0$, unrestricted exact acquisition exists exactly at $B=1$; finite-consumer exact acquisition never exists; and finite-anchor or sourcewise finite-target exact acquisition exists exactly when $B=1$ and $d>0$. For $h=0$, every split $d+z=1$ is exactly acquired in every class. At $B=0$, $b\equiv0$ and all infima are the attained $h/2$. At $B<1$, the $d/z$ split does not change any infimum or support-attainment condition. At $B=1$, positive finite nonproposal mass cannot replace positive literal divergence in (49.2).

**Proof.** Theorem 47.1 supplies the first two attained minima with complete all-source constructions. Theorem 48.2 gives the two support-class infima, excludes precisely their stated boundary cases, and supplies every larger cap through the normalized clipped-profile constructions (48.5). Its exact positive-divergence construction supplies the additional limit-one boundary. The zero-proposal law and the forced identity $b\equiv0$ at $B=0$ give the endpoints without a conditional ratio or division by $1-B$. These are global design statements. Exact acquisition of any one prescribed family remains governed by Theorem 46.4, or Theorem 46.3 on a countable power-set carrier; Theorem 46.6 concerns the fixed-family zero infimum and does not change its target laws. The arithmetic necessities use only actual matching sources, not occurrence of every integer target. The bounded-band bridge is needed precisely to keep the finite profile gap positive as preparation coupling improves. All conclusions are ordinary mathematical consequences under the measurable-rule contract. $\square$

## 追加锚（本行以下为增补区）

## 50. The value of acquisition for one prescribed family

**Definition 50.1 (Actual local probability radii).** Fix the whole labeled source set $X$, the maps $N,\Omega$, the constant zero advice, the common consumer and its nonempty measurable tape carrier $(\Theta,\mathcal F)$ as in Definitions 44.1 and 45.1. Fix every target law $\mu_y$ before varying the preparation. Any profile or anchor-row requirement is a condition on this input family; it does not restrict the prepared laws to satisfy the same row. Write $I(\mu)$ for (46.15). All distances below use event-supremum TV.

Enumerate the primes increasingly and put $C_0(x)=X$. For an occupied finite prime-prefix cylinder $C$, define

$$
\begin{aligned}
\rho_\mu(C)&=\inf_{v\in\mathcal P(\Theta,\mathcal F)}
                   \sup_{y\in C}\operatorname{TV}(v,\mu_y),\\
r_\mu(x)&=\inf_{m\ge0}\rho_\mu(C_m(x)),\\
R_\mu&=\sup_{x\in X}r_\mu(x).
\end{aligned}
\tag{50.1}
$$

The centers are probability laws on the original carrier. No local center is assumed to attain its infimum. The targets in a cylinder include every original label, including different labels with identical observations.

For topological bookkeeping only, let

$$
Q=\left\{\big(\mathbf1_{p_i\mid N(y)}\big)_{i\ge1}:y\in X\right\}
   \subseteq\{0,1\}^{\mathbb N}.
\tag{50.2}
$$

Use its subspace topology. Write $[y]$ for the signature of $y$ and $r_\mu([y])=r_\mu(y)$; the latter is well-defined because all its cylinders depend only on that signature. This is the countable set of actual complete observation signatures, without adjoining any other bit stream. The cylinder topology on $X$ is its pullback. A TV-continuous law family factors through $Q$, since distinct probability measures are separated by TV. A target family need not factor through $Q$.

**Theorem 50.2 (Sharp fixed-family value and the separate endpoint obligation).** Under the measurable common-rule contract of Definition 45.1, on every nonempty measurable consumer carrier,

$$
I(\mu)=R_\mu.
\tag{50.3}
$$

For caps $0\le\eta\le1$, $\eta<R_\mu$ is impossible and $\eta>R_\mu$ is feasible. When $R_\mu=1$, the cap $1$ is attained. Feasibility at $\eta=R_\mu<1$ requires an additional attainment condition; (50.3) alone does not supply it. In particular, the center choices in (50.1) are local to actual observations, rather than one constant reference on $X$ or a redesign of the target family.

**Proof.** Let $\widehat\mu$ be any lawful prepared family and let its uniform error be $\varepsilon$. For a fixed actual $x$ and $\gamma>0$, Lemma 45.3 supplies one $m$ for which

$$
\operatorname{TV}(\widehat\mu_x,\widehat\mu_y)<\gamma
\qquad(y\in C_m(x)).
$$

Thus the single probability law $\widehat\mu_x$ is a center for all target laws in that same cylinder with radius at most $\varepsilon+\gamma$. Let $\gamma$ decrease to zero and then take the supremum over $x$. This proves $R_\mu\le\varepsilon$. The comparison uses a whole cylinder and a whole finite-record seed event, without choosing a comparison source separately for each seed.

Conversely, fix $R_\mu<q<\eta$. Mark each occupied prefix node $C$ with $\rho_\mu(C)<q$, and choose one fixed law $v_C$ with

$$
\sup_{y\in C}\operatorname{TV}(v_C,\mu_y)<q.
\tag{50.4}
$$

There are countably many nodes. Under one source-independent product seed law, preload coordinates $W_C$ with laws $v_C$ for all marked nodes. A common deterministic preparation queries primes in increasing order and hands over $W_C$ at the first marked prefix, also allowing the depth-zero node.

For each actual $x$, the definition of $r_\mu(x)\le R_\mu<q$ guarantees a marked prefix at a finite depth. This preparation therefore terminates at every seed at that source. Its selected node depends only on the acquired prime prefix, so its prepared law there is exactly $v_C$, not a conditioning of $v_C$ on a seed-dependent event. The uniform error is at most $q<\eta$. Finite record events and output-event preimages are measurable coordinate events or countable unions of them. The normalized coordinate laws and their countable product give one inherited seed probability space. The center and marking tables are fixed shared constants of the prescribed problem. They do not supply a source label, a target input, an effective optimizer or an effective sampler. The original consumer subsequently runs on the same static source.

This is the certified-prefix construction of Theorem 46.6 with probability centers in place of representative target laws. The local metric approximation mechanism and the product-measure ingredient are reused; the operational correspondence is the actual finite-prime decoder. Taking the infimum proves (50.3). If $R_\mu=1$, handing any fixed tape over in one transition has error at most $1$, hence exactly $1$ by the lower bound.

For the endpoint, apply the published exact-acquisition criteria to a candidate prepared family $\lambda$, keeping the original $\mu$ fixed. On a countable power-set carrier, attainment is equivalent to existence of a TV-continuous family $\lambda$ such that

$$
\operatorname{TV}(\lambda_y,\mu_y)\le R_\mu
\qquad(y\in X).
\tag{50.5}
$$

Necessity is Lemma 45.3 and sufficiency is Theorem 46.3. On an arbitrary measurable carrier, enumerate the actual labels as $x_i$ and set

$$
\sigma_\lambda=\sum_{i\ge1}2^{-i}\lambda_{x_i},
\qquad
\ell^\lambda_C(A)=\int_A\inf_{y\in C}
                   \frac{d\lambda_y}{d\sigma_\lambda}\,d\sigma_\lambda.
\tag{50.6}
$$

The necessary and sufficient additional condition, together with (50.5), is

$$
\ell^\lambda_{C_m(x)}(\Theta)\longrightarrow1
\qquad(x\in X).
\tag{50.7}
$$

This is precisely Theorem 46.4 applied to $\lambda$. Its dominating measure is on tapes, never a sampled law on $X$. Countability makes the density infima measurable and their versions immaterial as measures. Continuity alone cannot replace (50.7). These reused criteria quantify over one jointly compatible law family; independent choices of optimal centers do not discharge them. At $R_\mu=0$, Theorem 46.6 gives the existing continuity characterization, with exactness on countable power-set carriers and the existing general-carrier exception of Proposition 46.5.

The order $\sup_x\inf_m$ in (50.1) is essential. For a concrete comparison on the original source, use the countable power-set carrier $\mathbb N_{>0}$, an always-unknown consumer, and prescribe

$$
\mu_y=\delta_{j(y)},\qquad
j(y)=\min\{i:p_i\nmid N(y)\}.
\tag{50.8}
$$

Every actual integer $N(y)$ has finite prime support, so $j(y)$ is finite. Query until the first negative answer and hand over that index, using a unit seed. This is exact lawful acquisition; a prefix through $j(y)$ fixes its target law, so $R_\mu=0$. For every fixed $m$, however, the all-positive depth-$m$ cylinder contains laws $\delta_j$ for every $j>m$: Theorem 35.2 realizes the first $j-1$ positive answers and the $j$-th negative answer at an actual source. Any probability on the countable carrier has singleton masses tending to zero along these indices, so that cylinder has radius $1$. Consequently

$$
\sup_x\inf_m\rho_\mu(C_m(x))=0,
\qquad
\inf_m\sup_x\rho_\mu(C_m(x))=1.
\tag{50.9}
$$

Sourcewise finite stopping gives no common finite horizon. Likewise $\rho_\mu(X)$ is only a constant-reference upper bound for $I(\mu)$; Proposition 49.1 already separates them. The global design values of Sections 47--49 vary the targets and do not determine (50.3) for a prescribed family. $\square$

## 51. Finite common carriers attain the prescribed-family value

**Theorem 51.1 (Finite-carrier boundary acquisition).** If the fixed consumer carrier is finite, with any sigma algebra, every complete prescribed target family has a lawful preparation with uniform error exactly $R_\mu$. More generally the same conclusion holds when the carrier's sigma algebra is finite. Neither sourcewise finite target support on an infinite carrier nor finite support at the anchor is a substitute for this hypothesis.

**Proof.** Partition the carrier into the $d$ nonempty atoms of its finite sigma algebra. Choose one actual tape representative in each atom. Every law is identified, without loss of measurable-event information, with a vector in the compact simplex $\Delta_d$. Write $v(A)$ for its mass on a union $A$ of atoms; there are only finitely many such events, and

$$
\operatorname{TV}(v,w)=\max_A|v(A)-w(A)|.
\tag{51.1}
$$

For $q\in Q$, let $C_m(q)$ contain all original labels with that prefix, and define

$$
\begin{aligned}
u_A(q)&=\inf_m\sup_{y\in C_m(q)}\mu_y(A),\\
l_A(q)&=\sup_m\inf_{y\in C_m(q)}\mu_y(A),\\
K(q)&=\{v\in\Delta_d:
          u_A(q)-R_\mu\le v(A)\le l_A(q)+R_\mu
          \text{ for every }A\}.
\end{aligned}
\tag{51.2}
$$

At each fixed depth the extrema are constant on prefix cylinders, hence continuous on $Q$. Therefore $u_A$ is upper semicontinuous and $l_A$ is lower semicontinuous. All original labels remain in the extrema, even when their target laws disagree on one complete observation fiber.

Fix $q$ and choose approximate centers $v_m$ for $C_m(q)$ whose errors are at most $\rho_\mu(C_m(q))+1/(m+1)$. Compactness gives a convergent subsequence. Along it the radii decrease to $r_\mu(q)\le R_\mu$, and, for each event $A$, the center inequalities pass to

$$
u_A(q)-r_\mu(q)\le v(A)\le l_A(q)+r_\mu(q).
$$

Thus $K(q)$ is nonempty. It is compact and convex.

The nonempty values also vary lower semicontinuously; nonemptiness by itself would not be enough. Write every inequality in (51.2), together with the simplex inequalities and the two inequalities for its total-mass equality, as

$$
K(q)=\{v\in\mathbb R^d:Mv\le b(q)\}.
\tag{51.3}
$$

Here $M$ is one fixed finite matrix. Every nonconstant component of $b(q)$ is either $R_\mu-u_A(q)$ or $R_\mu+l_A(q)$, and hence lower semicontinuous. Hoffman's fixed-matrix error bound gives a finite constant $H_M$, independent of any consistent right-hand side, with

$$
\operatorname{dist}_2(v,K(q'))
 \le H_M\left\|(Mv-b(q'))_+\right\|_\infty.
\tag{51.4}
$$

For $v\in K(q)$ and any $\delta>0$, lower semicontinuity of the finitely many right-hand sides supplies a neighborhood of $q$ on which $b_i(q')>b_i(q)-\delta$ for every $i$. The residual in (51.4) is at most $\delta$. A point in $K(q')$ is consequently arbitrarily close to $v$ throughout a sufficiently small neighborhood. This is lower semicontinuity of $K$.

The estimate used here is A. J. Hoffman's classical fixed-matrix bound, [*On approximate solutions of systems of linear inequalities*, J. Research NBS 49, 263--265](https://doi.org/10.6028/jres.049.027); its form for arbitrary fixed norms is stated in Peña, Vera and Zuluaga, [*An algorithm to compute the Hoffman constant of a system of linear constraints*, equation (1) and Proposition 1](https://arxiv.org/pdf/1804.08418v1). A constant for finitely many fixed rows is being used, not a constant for infinitely many tape-event constraints.

The actual signature space $Q$ is metrizable, hence Hausdorff and paracompact. Michael's closed-convex-valued selection theorem therefore supplies a continuous $v:Q\to\mathbb R^d$ with $v(q)\in K(q)$. Its hypotheses are now explicit: a paracompact domain, the Banach range $\mathbb R^d$, nonempty closed convex values, and the lower semicontinuity just proved. The supplier is Michael, [*Continuous Selections. I*, Theorem 3.2″](https://doi.org/10.2307/1969615); this formulation is also recalled in the introduction of Gutev, [*Continuous Selections, Function Spaces and Partitions of Unity*](https://arxiv.org/html/2602.21313v1). No compactness or completion of $Q$ is used.

For every original label $y$, its own target lies between the extrema:

$$
l_A([y])\le\mu_y(A)\le u_A([y]).
$$

Membership in $K([y])$ therefore gives $\operatorname{TV}(v([y]),\mu_y)\le R_\mu$. To turn the selection into a lawful preparation, first apply Theorem 46.3 on the finite power-set carrier of atom indices. Its one common uniform seed and finite-prime cumulative-probability certificates acquire the continuous vector family exactly. Then hand over the chosen representative tape of that atom. This last map is measurable into the original carrier and induces precisely the desired event law. Sourcewise almost-sure finite stopping, common deterministic rules and all finite-record/output measurability are inherited from that theorem. The same consumer runs after the handoff on the same source.

The resulting error is at most $R_\mu$, and Theorem 50.2 forces equality. The selection and error-bound theorems are reused classical mathematics; the assertion is their finite-prime acquisition consequence for the entire prescribed family. $\square$

**Corollary 51.2 (A common finite target support).** On a countable power-set carrier, if all target laws are supported on one common finite nonempty set of actual tapes, the prescribed-family infimum is attained. This condition concerns a common set, rather than a separate finite support at each source.

**Proof.** Let the common set be $S$ and fix $\theta_0\in S$. The measurable map that fixes $S$ and sends every other tape to $\theta_0$ fixes every target law and cannot increase event-TV. Applying it to a center shows that the local radii computed in the full carrier equal those computed using laws on $S$. Theorem 51.1 on $S$ supplies a lawful attainer with those radii, and its tapes are also tapes of the original consumer.

In a one-transition constant-law preparation with a finite point mixture $\nu=\sum_iw_i\delta_{\theta_i}$, the seed carrier may be exactly the distinct tapes of positive weight, with their induced weights and its power-set sigma algebra. Identity handoff is measurable and has law $\nu$ on the consumer carrier. No zero-weight tape need be a possible prepared output. This realizes the finite reference law in the constant-profile example of Corollary 48.3 using its finite positive-weight seed support, without asserting that the whole consumer carrier is finite. $\square$

## 52. Two-point target laws with an unattained positive optimum

**Theorem 52.1 (Countable-carrier failure at every interior boundary).** For every $r\in(0,1)$ there is one fixed target family on a countable power-set consumer carrier, on the entire original $X$, with

$$
I(\mu)=r
\quad\text{and no lawful preparation with error at most }r.
\tag{52.1}
$$

Every target law has at most two support points; the anchor target law has one. Each cap $\eta>r$ has an all-source lawful preparation with a finite positive-weight seed carrier and a common finite prime menu. All targets have row $(h_y,e_y,d_y,z_y)=(0,0,0,1)$ and satisfy every allowed profile. Thus sourcewise finite target support does not imply the finite-common-carrier attainment conclusion.

**Proof.** Encode the actual prime answers relative to the anchor as in Proposition 46.5. Let $E$ be the sources with the anchor's entire observation signature, and let $D_n$ be the sources whose first differing answer is at prime index $n$. These sets partition the whole labeled $X$, with each $D_n$ an occupied clopen set. Every occupied prefix subcylinder of $D_n$ contains infinitely many distinct complete observation classes: Theorem 35.2 gives unbounded $\Omega$ there, whereas a fixed finite list of complete prime supports has bounded $\Omega$.

For each $n$, partition the actual observation classes in $D_n$ into $n$ dense colors. To do so, enumerate its occupied prefix subcylinders and, for each subcylinder and each of the $n$ colors, choose a previously unassigned class and assign that color. At every finite stage only finitely many classes have been used, so the preceding infinitude suffices. Give every remaining class any fixed color. Each color meets every occupied subcylinder. This is one fixed specification of target laws on complete observation classes, not a new observation available to a preparation. The same argument with any fixed finite number of colors applies to $Q$ itself.

Choose $0<c<\min\{r,1-r\}$ and put

$$
\begin{aligned}
\Theta&=\{0\}\sqcup\{(n,i):n\ge1,\ 1\le i\le n\},\\
B_n&=\{(n,i):1\le i\le n\},\\
w_n&=r+\frac cn.
\end{aligned}
\tag{52.2}
$$

Use the power-set sigma algebra and let every tape immediately return unknown. For a source of color $i$ in $D_n$ prescribe, once and for all,

$$
\mu_y=(1-w_n)\delta_0+w_n\delta_{(n,i)};
\qquad
\mu_y=\delta_0\quad(y\in E).
\tag{52.3}
$$

Here $0<w_n<1$, so all laws are normalized with the stated support and terminal row. Labels with identical complete observations have identical laws. Neither the color nor the source label is supplied to the preparation.

For lawful approximations define

$$
v_n=(1-w_n)\delta_0+\frac{w_n}{n}\sum_{i=1}^n\delta_{(n,i)}.
\tag{52.4}
$$

Preload independent coordinates $W_n$ of laws $v_n$ under one common countable product seed law. For a fixed $M\ge1$, inspect the first $M$ prime answers. If the first difference is $n\le M$, emit $W_n$; otherwise emit $0$. The selected coordinate depends only on the observed prefix. All sources and all seeds terminate after this finite menu, and their finite-record and output events are measurable. Only coordinates $1,\ldots,M$ are used, so their finite product, on its finite positive-weight point support, is also a sufficient seed space for this same preparation.

At a source in $D_n$ with $n\le M$, event-TV between (52.4) and (52.3) is

$$
w_n\left(1-\frac1n\right)
 =r+\frac{c-r}{n}-\frac{c}{n^2}<r.
\tag{52.5}
$$

At a source in $D_n$ with $n>M$, the emitted law is $\delta_0$ and the error is $w_n$. On $E$ it is zero. Every $D_n$ is occupied and $w_n$ decreases, so the exact uniform error is

$$
\varepsilon_M=w_{M+1}=r+\frac{c}{M+1}\downarrow r.
\tag{52.6}
$$

The whole target family is unchanged as $M$ varies.

For the lower bound and endpoint obstruction, let $\lambda$ be any TV-continuous probability-valued family with uniform error at most $\varepsilon$. Fix $z\in D_n$. For each color $i$, its density gives actual sources of that color matching successively longer prefixes of $z$. Their target law is the fixed $i$-th law in (52.3), while their $\lambda$ laws converge to $\lambda_z$ in TV. Consequently, for every $i$,

$$
\lambda_z(\{(n,i)\})\ge w_n-\varepsilon.
\tag{52.7}
$$

If $\varepsilon<r$, choose $n$ so large that $n(r-\varepsilon)+c>1$. Summing (52.7) over its $n$ disjoint singletons gives a mass larger than $1$, a contradiction. Thus every continuous approximant, and in particular every lawful prepared family, has error at least $r$.

If $\varepsilon=r$, the same inequalities instead force

$$
\lambda_z(B_n)\ge c
\qquad(z\in D_n).
\tag{52.8}
$$

The blocks $B_n$ are pairwise disjoint, so the probability law $\lambda_{x_*}$ has $\lambda_{x_*}(B_n)\to0$. By TV continuity at the actual anchor, choose $m$ such that

$$
\operatorname{TV}(\lambda_y,\lambda_{x_*})<c/4
\qquad(y\in C_m(x_*)).
$$

Choose $n>m$ with $\lambda_{x_*}(B_n)<c/4$ and choose an actual $z\in D_n$. It belongs to that same anchor cylinder. The one measurable event $B_n$ gives

$$
\lambda_z(B_n)<c/2,
$$

contradicting (52.8). This excludes even a continuous optimum at the boundary. Lemma 45.3 therefore excludes every lawful attainer, regardless of its seed carrier or its sourcewise stopping times.

Together with (52.6), the lower bound proves (52.1). The feasible caps in $[0,1]$ are exactly $(r,1]$. The obstruction is compatibility of probability masses across actual blocks approaching the anchor, rather than an inability to realize a finite target law at one isolated source. No source sampling, source choice during execution, reset, conditioning away failure or color probe is used. $\square$

## 53. A continuous optimum that fails operational attainment

**Theorem 53.1 (Positive nonattainment with a unique continuous best approximant).** For every $r\in(0,1)$ there is one fixed full-source target family on a standard Borel consumer carrier with acquisition infimum $r$ and no lawful attainer, although exactly one TV-continuous family attains uniform approximation error $r$. Every cap $\eta>r$ is lawfully feasible. The consumer always returns unknown, so every target has row $(0,0,0,1)$ and satisfies every prescribed profile.

**Proof.** Let $(\nu_y)$ be the fixed TV-continuous dyadic-hole family of Proposition 46.5 on $Z=[0,1]$ with its Borel sigma algebra. This family is reused, including its actual-source realization; it is not a new zero-infimum example. In every anchor prefix cylinder its greatest common submeasure is zero. Indeed, for any level $n$ beyond the prefix, Theorem 35.2 realizes every level-$n$ dyadic hole by an actual source in that cylinder. A common submeasure gives zero mass to each such interval, hence to $[0,1)$; its possible endpoint mass is also zero because it is dominated by the anchor's Lebesgue law.

Choose an integer $k\ge2$ with $r<1-1/k$ and put

$$
t=\frac{r}{1-1/k}\in(0,1),\qquad \alpha=1-t>0.
\tag{53.1}
$$

Partition the actual observation classes of $Q$ into $k$ dense colors by the occupied-cylinder construction in the proof of Theorem 52.1. Let $c(y)$ be the resulting fixed color, constant on complete observation fibers. On

$$
\Theta=Z\sqcup\{a_1,\ldots,a_k\}
\tag{53.2}
$$

use the disjoint-union Borel sigma algebra and the always-unknown consumer. Prescribe the entire family

$$
\mu_y=\alpha\nu_y+t\delta_{a_{c(y)}}.
\tag{53.3}
$$

All these probability laws, the carrier and the consumer are fixed before optimizing preparation. The color specifies target data only.

The candidate

$$
\kappa_y=\alpha\nu_y+\frac tk\sum_{i=1}^k\delta_{a_i}
\tag{53.4}
$$

is TV-continuous, with $\operatorname{TV}(\kappa_y,\mu_y)=t(1-1/k)=r$ at every source. We show that it is the only continuous family within that cap, and that no continuous family has smaller uniform error.

Let $\lambda$ be continuous with uniform error at most $\varepsilon$. Fix an actual $x$. For each color $i$, choose actual sources of that color matching successively longer prefixes of $x$. Continuity of both $\lambda$ and $\nu$ passes their cap inequalities to

$$
\operatorname{TV}(\lambda_x,\alpha\nu_x+t\delta_{a_i})
   \le\varepsilon
\qquad(1\le i\le k).
\tag{53.5}
$$

Put $p_i=\lambda_x(\{a_i\})$ and $L=\sum_i p_i$. Singleton events and the events consisting of all tags except $a_i$ give respectively

$$
p_i\ge t-\varepsilon,\qquad L-p_i\le\varepsilon.
$$

Summing the two sets of inequalities yields

$$
k(t-\varepsilon)\le L,\qquad
(k-1)L\le k\varepsilon,
$$

and hence $\varepsilon\ge t(k-1)/k=r$.

At $\varepsilon=r$, equality is forced: $L=t$ and every $p_i=t/k$. For a Borel $A\subseteq Z$, compare the measurable event

$$
A\sqcup\{a_j:j\ne i\}
$$

in (53.5). Its signed mass difference is

$$
r+\lambda_x(A)-\alpha\nu_x(A),
$$

which must be at most $r$. Therefore $\lambda_x(A)\le\alpha\nu_x(A)$ for every such $A$. The two restrictions have the same total mass $\alpha$, so applying this domination also to complements inside $Z$ proves equality for every Borel set. Thus $\lambda_x=\kappa_x$ for every actual $x$, proving uniqueness. This finite tag-saturation argument uses event-TV directly, without an arbitrary-carrier maximal-coupling claim.

Every lawful prepared family is continuous by Lemma 45.3. An operational attainer at error $r$ would therefore acquire $\kappa$ exactly. For every anchor prefix cylinder, its greatest common submeasure is

$$
\ell^\kappa_{C_m(x_*)}=\frac tk\sum_{i=1}^k\delta_{a_i},
\qquad
\ell^\kappa_{C_m(x_*)}(\Theta)=t<1.
\tag{53.6}
$$

The displayed tag measure is dominated by every $\kappa_y$. Conversely, the restriction of any common submeasure to $Z$ is dominated by every $\alpha\nu_y$ in that cylinder and is zero by the dyadic-hole property above; its tag masses are at most $t/k$. This proves (53.6). It violates Theorem 46.4 at the actual anchor. Hence the unique continuous optimum is not exactly acquirable, and no lawful preparation attains the cap $r$.

For upper approximations, Theorem 46.6 supplies a lawful preparation of $\nu$ with law $\widetilde\nu_y$ and uniform error at most any prescribed $\delta>0$. Include its whole seed in one common product seed, together with an independent finite selector. With probability $\alpha$, run that preparation on the unchanged source and hand over its tape in $Z$; with probability $t/k$ for each $i$, hand over $a_i$ immediately. This is an initial seed branch, not a restart or a success-conditioned attempt. Every actual source terminates almost surely, and finite-record/output events are measurable inherited events or finite unions of them. The resulting normalized law is

$$
\widetilde\kappa_y
  =\alpha\widetilde\nu_y+\frac tk\sum_i\delta_{a_i}.
\tag{53.7}
$$

Its error at source $y$ is exactly

$$
\operatorname{TV}(\widetilde\kappa_y,\mu_y)
 =r+\alpha\operatorname{TV}(\widetilde\nu_y,\nu_y).
\tag{53.8}
$$

To see the equality on the event-supremum normalization, the signed tag difference has positive mass $r$ on all tags except the actual color and negative mass $r$ at that color. The disjoint base difference has total mass zero. For any event its positive difference is at most $r+\alpha\operatorname{TV}(\widetilde\nu_y,\nu_y)$; taking the positive tags together with base events approaching the positive supremum attains that supremum in the limit. Complements give the same negative supremum. No existence of an event attaining the base supremum is needed.

Choose $\delta<(\eta-r)/\alpha$ for any $\eta>r$. Equations (53.7)--(53.8) give uniform error strictly below $\eta$. The lower bound and the nonacquisition argument now prove $I(\mu)=r$ and the exact feasible-cap split $(r,1]$, even though the continuous relaxation has its unique minimizer (53.4).

For an attained comparison, replace $\nu_y$ by the fixed point law $\delta_0$ on one base tape and retain the same colors and weights. The same tag inequalities give lower bound $r$; the constant law $\alpha\delta_0+(t/k)\sum_i\delta_{a_i}$ is handed over from its finite positive-weight seed support in one transition and attains $r$. Thus the positive value alone does not determine operational attainment.

The common-submeasure and range-partition ingredients are those of Theorem 46.4, with the existing overlap in Gallo, Lerasle and Takahashi, [*Markov approximation of chains of infinite order in the $\bar d$-metric*, Section 3, Lemma 3.1](https://arxiv.org/html/1107.4353v2). No stationary-chain or coalescence conclusion is transferred to the static source. The mathematical increment is the positive-error forced optimum on the actual prime-observation family and its failure of acquisition, together with the different countable two-point obstruction of Theorem 52.1. These are repository-derived operational deductions from the cited suppliers, without a literature-priority claim.

The original general endpoint question remains (50.5)--(50.7): a compatible candidate family is still quantified over. No criterion eliminating that family in favor of the targets alone is established here. Finite common carriers always attain; countable power-set carriers attain at zero but can fail at any interior positive value; general measurable carriers can fail at zero or at positive values, even with a continuous optimum; value $1$ always attains. The two nonattainment constructions use the explicitly stated zero-proposal input subclass and do not classify every prescribed positive-proposal row. All general value and candidate conditions retain every target law, the original consumer and the entire actual $X$. Common measurable tables and product seeds carry no conclusion about effective real sampling, finite descriptions, uniform runtime, physical acquisition or resources. $\square$

## 追加锚（本行以下为增补区）

## 54. A target-intrinsic cap criterion on a countable tape carrier

**Definition 54.1 (Target fibers and their local compatibility refinement).** Fix the entire labeled source (44.1), the zero advice, the consumer and every prescribed target law as in Definition 50.1. In this section the tape carrier $\Theta$ is nonempty and countable, with its power-set sigma algebra. Let $P=\mathcal P(\Theta)$ and $d=\operatorname{TV}$, always with the event-supremum normalization. Probability vectors identify $P$ with the closed subset of $\ell^1(\Theta)$ consisting of nonnegative vectors of sum one, and

$$
d(v,w)=\frac12\sum_{\theta\in\Theta}|v(\{\theta\})-w(\{\theta\})|.
\tag{54.1}
$$

Thus $P$ is complete and separable: finitely supported rational probability vectors are dense. Use only the actual signature space $Q$ of (50.2), with no additional limit signatures. Its occupied prefix neighborhoods are

$$
U_m(q)=\{q'\in Q:q'_i=q_i\ (1\le i\le m)\},
\qquad C_m(q)=\{y\in X:[y]\in U_m(q)\}.
\tag{54.2}
$$

They form a countable clopen basis; $U_0(q)=Q$. Fix a cap $\eta\in[0,1]$. Start with the closed convex sets, possibly empty,

$$
K_0^\eta(q)=\bigcap_{y\in X:\,[y]=q}
                 \{v\in P:d(v,\mu_y)\le\eta\}.
\tag{54.3}
$$

Every label in the fiber occurs in this intersection, even when equal observations have different target laws. For a closed-valued correspondence $K:Q\to 2^P$, allowing empty values, use $\operatorname{dist}(v,A)=\inf_{w\in A}d(v,w)$ for nonempty $A$, put $\operatorname{dist}(v,\varnothing)=+\infty$, and define

$$
\mathcal D K(q)=\left\{v\in K(q):
  \forall\delta>0\ \exists m\ \forall q'\in U_m(q),\quad
          \operatorname{dist}(v,K(q'))<\delta\right\}.
\tag{54.4}
$$

For countable ordinals define the decreasing refinement by

$$
K_{\alpha+1}^\eta=\mathcal D K_\alpha^\eta,
\qquad
K_\lambda^\eta(q)=\bigcap_{\alpha<\lambda}K_\alpha^\eta(q)
   \quad(\lambda\text{ a nonzero limit ordinal}).
\tag{54.5}
$$

The recursion involves only original target balls, actual occupied cylinders, metric distances and intersections. It does not take a proposed prepared-law family as input. Each point in a value is merely a probability center on the original tapes; membership is progressively tested against all neighboring values.

**Theorem 54.2 (Intrinsic necessary-and-sufficient cap feasibility).** The refinement (54.5) stabilizes at some countable ordinal $\beta$: $K_\beta^\eta=K_{\beta+1}^\eta$. Write $K_\infty^\eta$ for its stable value. Then

$$
\begin{aligned}
&\text{there exists a lawful preparation with }
  \sup_{y\in X}d(\widehat\mu_y,\mu_y)\le\eta\\
&\hspace{25mm}\Longleftrightarrow\quad
  K_\infty^\eta(q)\ne\varnothing\quad\text{for every }q\in Q.
\end{aligned}
\tag{54.6}
$$

In particular, the original sharp value

$$
R_\mu=\sup_{x\in X}\inf_{m\ge0}\inf_{v\in P}
                         \sup_{y\in C_m(x)}d(v,\mu_y)
\tag{54.7}
$$

is attained if and only if every $K_\infty^{R_\mu}(q)$ is nonempty. This is a non-effective characterization, without a finite refinement-rank bound or a uniform preparation horizon.

**Proof.** First, all values in the recursion are closed. If $v_j\in\mathcal D K(q)$ and $v_j\to v$, closedness of $K(q)$ puts $v$ in $K(q)$. Given $\delta>0$, choose $j$ with $d(v,v_j)<\delta/2$ and use the neighborhood for $v_j$ at tolerance $\delta/2$. The triangle inequality gives (54.4) for $v$. Convexity also persists: for two surviving centers choose one common cylinder on which both have sufficiently close witnesses in $K(q')$, and take the corresponding convex combination. Limits preserve closedness and convexity. No compactness or nearest-point attainment is used.

Fix a countable basis $\mathcal B$ of the separable metric space $P$. At any strict successor decrease, closedness supplies a pair $(q,V)\in Q\times\mathcal B$ such that $V$ meets $K_\alpha^\eta(q)$ and is disjoint from $K_{\alpha+1}^\eta(q)$. That same pair cannot witness a later decrease, because every later value is contained in $K_{\alpha+1}^\eta(q)$. The set $Q\times\mathcal B$ is countable. If no countable stabilization stage existed, there would be a distinct such pair for every $\alpha<\omega_1$, a contradiction. Equality at one successor stage makes all subsequent successor and limit stages equal. This proves stabilization and makes $K_\infty^\eta$ independent of which stabilization stage is used.

Every continuous selection $v(q)\in K_0^\eta(q)$ survives every stage. Indeed, if it selects $K_\alpha^\eta$, then

$$
\operatorname{dist}(v(q),K_\alpha^\eta(q'))
       \le d(v(q),v(q')),
\tag{54.8}
$$

and continuity supplies the cylinder in (54.4). Limit stages follow by intersection. Lemma 45.3 says that any lawful prepared family factors through $Q$ as just such a TV-continuous selection. This proves the forward implication of (54.6).

For the converse suppose all stable values are nonempty. Stability implies lower semicontinuity: if $v\in K_\infty^\eta(q)$ belongs to an open set $O\subseteq P$, choose a ball about $v$ contained in $O$. Equation (54.4) supplies a cylinder throughout which the stable values meet that ball. Equivalently, for every open $O$, the set of $q$ with $K_\infty^\eta(q)\cap O\ne\varnothing$ is open.

Here the continuous-selection step can be proved directly with its full hypotheses. Every open cover of $Q$ has a disjoint clopen refinement: enumerate the basis members $V_i$ contained in a member of the cover and replace them by

$$
W_i=V_i\setminus\bigcup_{j<i}V_j.
\tag{54.9}
$$

Discard empty members. These clopen sets cover $Q$ and refine the cover. For any nonempty closed-valued lower-semicontinuous $H:Q\to2^P$, choose $v_q\in H(q)$. Lower semicontinuity gives a neighborhood where $\operatorname{dist}(v_q,H(q'))<1$. Applying (54.9) and using the chosen center of a containing neighborhood produces a locally constant $s_0$ with $\operatorname{dist}(s_0(q),H(q))<1$ everywhere.

Inductively suppose $s_n$ is locally constant and its distance to $H(q)$ is less than $2^{-n}$. At each $q$ choose $v_q\in H(q)$ with $d(v_q,s_n(q))<2^{-n}$. Restrict to a neighborhood where $s_n$ is constant and where $\operatorname{dist}(v_q,H(q'))<2^{-n-1}$. The same disjoint refinement gives a locally constant $s_{n+1}$ satisfying everywhere

$$
d(s_{n+1}(q),s_n(q))<2^{-n},
\qquad
\operatorname{dist}(s_{n+1}(q),H(q))<2^{-n-1}.
\tag{54.10}
$$

The summable bounds make $(s_n)$ uniformly Cauchy. Completeness of $P$ gives a continuous uniform limit $s$, and closedness of $H(q)$ puts $s(q)$ in $H(q)$. Apply this construction to $H=K_\infty^\eta$. Neither compactness of $Q$, compactness of the values nor finite-dimensionality is required. Convexity is preserved by the refinement but is unnecessary for this clopen selection argument.

To acquire the resulting selection, enumerate the actual tapes as $\theta_j$, without repetitions, stopping the enumeration in the finite case. Define $F_0=0$ and $F_j(q)=\sum_{i\le j}s(q)(\{\theta_i\})$. Use one common uniform seed $U\in(0,1)$. After reading the first $m$ actual prime answers, test the available indices $j\le m$ and emit $\theta_j$ when

$$
\sup_{q'\in U_m([y])}F_{j-1}(q')<U<
\inf_{q'\in U_m([y])}F_j(q').
\tag{54.11}
$$

These are fixed shared tables indexed by the acquired record, exactly the construction of Theorem 46.3. For each fixed source, outside its countable set of cumulative-mass endpoints, normalization supplies a unique containing interval and continuity certifies it at a finite prefix. Each stage uses finitely many tests and actual prime queries, so its actual execution is finite on that full-probability seed set. Finite record events are Borel interval combinations; each output event is a countable union of these events. The emitted probability law is $s([y])$, with no conditioning away of divergence. The preparation hands this tape, and no additional record input, to the same consumer on the same static source. Membership in (54.3) proves the cap for every original label. Theorem 50.2 identifies the infimum with (54.7), so at that cap the achieved uniform error equals $R_\mu$.

Lower-semicontinuous selection and derived mappings are mature machinery. Michael, [*Continuous selections and countable sets*, Theorem 1.1](https://doi.org/10.4064/fm-111-1-1-10), gives a selection-extension theorem for a countable regular domain, a first-countable range and a nonempty-valued lower-semicontinuous correspondence. Here $Q$ is countable and metric, and $P$ is metric; taking the initial closed subset empty gives the selection consequence. The complete clopen/completeness argument above also supplies it directly. Brown, [*The Derived Mappings and the Order of a Set-Valued Mapping Between Topological Spaces*](https://doi.org/10.1023/A:1008618528989), supplies the established derived-mapping reference frame; no theorem from its subscription text is required here. Finite-dimensional Glaeser bounds, such as Jiang, Luli and O'Neill, [*Smooth Selection for Infinite Sets*, Theorem 1.5](https://arxiv.org/html/2109.04905v2), require a closed Euclidean domain and finite jet/shape-field hypotheses that are not instantiated here. The countable-ordinal bound above is proved separately. The deduction (54.6) is the target-defined cap criterion for this actual acquisition problem, rather than a new general selection theorem or a literature-priority assertion. $\square$

**Theorem 54.3 (Pointwise laws with the all-source gate retained).** Let $\mathcal L_\eta(q)$ be the set of probability laws at signature $q$ realized by lawful preparations satisfying the cap $\eta$ at every original source. Then

$$
\mathcal L_\eta(q)=
\begin{cases}
K_\infty^\eta(q),& K_\infty^\eta(q')\ne\varnothing\text{ for every }q'\in Q,\\
\varnothing,& K_\infty^\eta(q')=\varnothing\text{ for some }q'\in Q.
\end{cases}
\tag{54.12}
$$

**Proof.** The necessity argument of Theorem 54.2 puts each lawful law in the stable value. If some other value is empty, no all-source cap preparation exists, so every $\mathcal L_\eta(q)$ is empty. If all values are nonempty, fix $v\in K_\infty^\eta(q_0)$ and replace just the value at $q_0$ by $\{v\}$. This modified correspondence is nonempty and closed-valued. It remains lower semicontinuous: at $q_0$ use lower semicontinuity for the point $v$; at $q\ne q_0$ restrict to an open neighborhood excluding $q_0$, which exists because $Q$ is Hausdorff. The clopen selection construction and (54.11) then give a lawful all-source cap preparation with law $v$ at $q_0$. This asserts arbitrary single-point prescription, not arbitrary simultaneous prescriptions at several signatures. $\square$

## 55. What the intrinsic refinement detects, and what it cannot detect

**Theorem 55.1 (Two distinct diagnostics of the published endpoint failures).** At cap $r$, the unchanged countable example of Theorem 52.1 has nonempty $K_0^r$ and $K_1^r$ at every actual signature, but $K_2^r([x_*])=\varnothing$. Applying the local operator (54.4) to the unchanged measurable example of Theorem 53.1 gives instead a nonempty stable singleton correspondence after the first refinement. For this second calculation interpret $P$ as all probability measures on that declared measurable carrier, and form $K_0^r$ and its successors by (54.3)--(54.4); no general stabilization theorem is imported. That second example is nevertheless unacquirable. These statements concern the two published families, rather than new constructions of their nonattainment.

**Proof.** Use $E,D_n,B_n,w_n=r+c/n$ and the dense colors of Theorem 52.1. On $D_n$, density and closedness of the cap balls give

$$
K_1^r([z])=\bigcap_{i=1}^n
 \{v\in P:d(v,(1-w_n)\delta_0+w_n\delta_{(n,i)})\le r\}
       \qquad(z\in D_n).
\tag{55.1}
$$

For necessity, approach $z$ through each color and use centers in its $K_0^r$ values at distances tending to zero from the proposed surviving point. For sufficiency, a member of the displayed intersection belongs to $K_0^r$ throughout the open set $D_n$, so all those distances are zero. The law (52.4) belongs to (55.1). At the anchor, $\delta_0\in K_1^r$: a color-$i$ source in $D_n$ has a cap center $(1-c/n)\delta_0+(c/n)\delta_{(n,i)}$ at distance $c/n$ from $\delta_0$, and the centers on $E$ may equal $\delta_0$. Every sufficiently long anchor cylinder has only $E$ and sufficiently late $D_n$, proving (54.4). Thus all first-refinement values are nonempty.

Every member of (55.1) puts at least $c/n$ on each singleton in $B_n$, hence at least $c$ on $B_n$. For any fixed probability $v$, pairwise disjointness gives $v(B_n)\to0$, and therefore

$$
\operatorname{dist}(v,K_1^r([z]))\ge c-v(B_n)
                   \qquad(z\in D_n).
\tag{55.2}
$$

Every anchor cylinder contains arbitrarily late occupied $D_n$. Equation (55.2) excludes every $v$ from the second refinement at the anchor. One compatibility pass is therefore insufficient, even though every initial and first-refinement fiber is nonempty.

For Theorem 53.1 use its unchanged $\alpha,t,k,\nu,\kappa$ and $k$ dense colors. A point surviving the first refinement at $q$ belongs to every cap ball centered at $\alpha\nu_q+t\delta_{a_i}$: approach through color $i$, choose nearby centers, and use TV continuity of $\nu$. The tag-saturation argument (53.5) forces that point to be $\kappa_q$. Conversely the continuous map $\kappa$ selects every initial fiber, so the survival induction (54.8) keeps it at every stage. Consequently the first refinement is precisely the stable map $q\mapsto\{\kappa_q\}$.

Its common-submeasure mass in every anchor cylinder remains $t<1$ by (53.6). The necessary condition of Theorem 46.4 therefore prevents acquisition. The elementary selection construction requires a complete range and a clopen basis, but selecting a continuous law is not the operational sufficiency step on an arbitrary measurable carrier. The countable-carrier realization (54.11) is precisely the additional bridge available in Theorem 54.2. On general carriers, even a stable singleton of continuous cap laws cannot replace common-submeasure exhaustion. $\square$

## 56. Positive correct proposals and countable endpoint nonattainment

**Definition 56.1 (A fixed positive-row input subclass).** Fix an arbitrary allowed profile $b$ and numbers

$$
0<h\le r<1.
\tag{56.1}
$$

Use distinct proposal tapes $p_j$ for $j\ge1$: the common consumer immediately proposes the finite integer $j$ on $p_j$, and immediately returns unknown on every other declared tape. Here $p_j$ denotes a tape, not the prime of the same index. It makes no prime queries. All carriers below contain these tapes as a measurable discrete component. The consumer's finite record and Borel real-output events are measurable, since its output on this component is an integer-valued function and its output on the complement is constant unknown. Prescribing mass $h$ at $p_{\Omega(y)}$ and the remaining mass on unknown tapes gives at every source the target row

$$
(h_y,e_y,d_y,z_y)=(h,0,0,1-h),
\qquad e_y\le b(\Omega(y))h_y.
\tag{56.2}
$$

The index $\Omega(y)$ is part of the fixed target-law specification, never an input to the preparation. The same applies to the color specifications used below. Prepared laws are not required to have row (56.2), as stipulated in Definition 50.1.

**Theorem 56.2 (A positive-row countable failure).** For every (56.1) and every allowed profile, there is a fixed target family on a countable power-set carrier, on the entire actual $X$, with row (56.2), at most three tapes in each target support, and

$$
I(\mu)=R_\mu=r,
\qquad
\{\eta\in[0,1]:\eta\text{ is lawfully feasible}\}=(r,1].
\tag{56.3}
$$

There is no TV-continuous family within cap $r$. Every cap above $r$ has a lawful preparation with a common finite prime menu and a finite positive-weight seed support.

**Proof.** First strengthen the actual dense coloring used in Section 52. The arithmetic supplier is [Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows), on the labeled source (36.1); its needed Fibonacci entry-rank identity is [equation (363.13)](FIBONACCI_ATOMIC_RELATION_GENERATION.md), namely $q\mid F_n\Longleftrightarrow z(q)\mid n$. It makes $\Omega$ unbounded in every occupied finite-prime cylinder. Complete observation classes have a fixed finite $\Omega$, so excluding finitely many classes preserves that unboundedness.

On $Q$, or on any occupied clopen subset, and for any fixed number of colors, enumerate triples consisting of an occupied prefix subcylinder, a color and an integer $K$. For each triple choose a previously unassigned class in that cylinder with $\Omega\ge K$, and assign it that color. Only finitely many classes have been used at that stage, so the choice exists. Assign the remaining classes arbitrarily. Thus, for every actual $z$ in the domain and every color $i$, there are actual sources $y_\ell$ of that color with

$$
[y_\ell]\in U_\ell([z]),\qquad \Omega(y_\ell)\ge\ell.
\tag{56.4}
$$

This construction uses only the actual domain and introduces no source probability, source selection during execution or additional observation. No exact realization of every integer $\Omega$ is required.

We will use a moving-event consequence. If $\lambda$ is TV-continuous, $[y_\ell]\to[z]$ and $j_\ell=\Omega(y_\ell)\to\infty$, then

$$
\lambda_{y_\ell}(\{p_{j_\ell}\})
 \le d(\lambda_{y_\ell},\lambda_z)
                   +\lambda_z(\{p_{j_\ell}\})\longrightarrow0.
\tag{56.5}
$$

The second term vanishes because the $p_j$ are disjoint atoms of a probability measure. Consequently, for fixed measurable $A$ disjoint from all proposal tapes, the inequalities $d(\lambda_{y_\ell},\mu_{y_\ell})\le\eta$ and $\mu_{y_\ell}(A\cup\{p_{j_\ell}\})\ge a$ for every $\ell$ imply $\lambda_z(A)\ge a-\eta$. The same source sequence controls the entire moving event; no coupling or unattainable joint experiment is assumed.

Let $E$ be the complete anchor-signature fiber and $D_n$ the sources with first differing prime answer at index $n$. These sets partition every labeled source; each $D_n$ is occupied and clopen, and $D_n\subseteq C_{n-1}(x_*)$. The anchor support is $\{3\}$, so every source in $E$ has $\Omega=1$. Color the actual classes of each $D_n$ with $n$ colors using (56.4). Choose $0<c<\min\{r,1-r\}$ and put $w_n=r+c/n$. On the countable power-set carrier

$$
\Theta^- =\{o\}\sqcup\{a_{n,i}:n\ge1,\ 1\le i\le n\}
                         \sqcup\{p_j:j\ge1\},
\tag{56.6}
$$

use the consumer of Definition 56.1 and prescribe

$$
\begin{aligned}
\mu_y^-&=(1-w_n)\delta_o+(w_n-h)\delta_{a_{n,i}}
                          +h\delta_{p_{\Omega(y)}}
       &&(y\in D_n\text{ of color }i),\\
\mu_y^-&=(1-h)\delta_o+h\delta_{p_1}&&(y\in E).
\end{aligned}
\tag{56.7}
$$

All coefficients are nonnegative and sum to one; $h\le r<w_n<1$. The sole proposal is exactly the true target, establishing (56.2). All duplicate labels remain and receive their specified laws.

For a continuous family of uniform error at most $\varepsilon$, fix $z\in D_n$ and approach it through each color as in (56.4). The target mass on $\{a_{n,i},p_{\Omega(y_\ell)}\}$ is $w_n$. Equations (56.5) and the event cap give

$$
\lambda_z(\{a_{n,i}\})\ge w_n-\varepsilon
                      =r-\varepsilon+c/n.
\tag{56.8}
$$

If $\varepsilon<r$, summing the $n$ disjoint singleton inequalities for sufficiently large $n$ exceeds total mass one. At $\varepsilon=r$, the block $A_n=\{a_{n,i}:i\le n\}$ has mass at least $c$ at every source in $D_n$. But $\lambda_{x_*}(A_n)\to0$ by pairwise disjointness. Continuity at the actual anchor supplies one cylinder where all laws are within $c/4$ of the anchor law. Choose $n$ beyond that prefix with anchor mass on $A_n$ less than $c/4$, and choose any actual source in the occupied $D_n$. Its mass on $A_n$ is less than $c/2$, a contradiction. Lemma 45.3 excludes every lawful cap-$r$ preparation, including those with arbitrary sourcewise finite stopping times.

For the upper bound fix $M\ge1$ and preload independent coordinates $W_n$, $1\le n\le M$, of laws

$$
v_n=(1-w_n)\delta_o+\frac{w_n}{n}\sum_{i=1}^n\delta_{a_{n,i}}.
\tag{56.9}
$$

Query the first $M$ primes. On first difference $n\le M$ emit $W_n$; otherwise emit $o$. The finite product of the finite categorical laws is one source-independent seed law on its finite positive-weight support. The selected coordinate depends only on actual acquired answers. All seeds and all sources terminate after this common finite menu, and record/output events are measurable. On a handled $D_n$, the only common target/output masses are at $o$ and the actual color atom. Thus event-TV equals

$$
1-\big(1-w_n+\min\{w_n/n,w_n-h\}\big)
       =\max\{h,w_n(1-1/n)\}\le r,
\tag{56.10}
$$

because $w_n(1-1/n)=r+(c-r)/n-c/n^2<r$. On unhandled $D_n$ the error is $w_n$, and on $E$ it is $h$. Since every $D_n$ is occupied, the exact uniform error is

$$
\varepsilon_M=w_{M+1}=r+\frac{c}{M+1}\downarrow r.
\tag{56.11}
$$

The consumer then runs on the same static source and handed tape. The lower bound and these approximants prove $I(\mu^-)=r$, and Theorem 50.2 identifies this with the original sharp expression $R_{\mu^-}$. No mixture weight or terminal row was imposed on an arbitrary prepared family in the lower-bound proof; the moving union event retains the positive target-proposal mass even when preparation reallocates it. $\square$

## 57. The same positive row with a unique continuous, unacquirable optimum

**Theorem 57.1 (Positive-row common-submeasure failure).** For the same parameter range (56.1) and every allowed profile, there is a fixed full-source target family on a standard Borel carrier with row (56.2), sharp value $r$ and feasible caps exactly $(r,1]$. Exactly one TV-continuous family achieves uniform error at most $r$, and that family cannot be lawfully acquired.

**Proof.** Reuse the unchanged dyadic-hole probability family $\nu_y$ of Proposition 46.5 on $Z=[0,1]$ with its Borel sigma algebra. Its map is TV-continuous, and in every anchor prefix cylinder its greatest common submeasure is zero. For any level $n$ beyond the prefix, Theorem 35.2 realizes every level-$n$ hole there; a common submeasure vanishes on each dyadic interval, and domination by the anchor's Lebesgue law also excludes endpoint mass. These are the existing actual-source properties of that family.

Choose an integer $k\ge2$ with $r<1-1/k$ and set

$$
\beta=\frac{r}{1-1/k}<1,
\qquad \alpha=1-\beta>0,
\qquad t=\beta-h\ge\beta/k>0.
\tag{57.1}
$$

Color all actual classes of $Q$ with $k$ colors retaining property (56.4). On the disjoint-union standard Borel carrier

$$
\Theta^+=Z\sqcup\{a_1,\ldots,a_k\}\sqcup\{p_j:j\ge1\},
\tag{57.2}
$$

use the consumer of Definition 56.1 and prescribe, before optimizing,

$$
\mu_y^+=\alpha\nu_y+t\delta_{a_{c(y)}}
                              +h\delta_{p_{\Omega(y)}}.
\tag{57.3}
$$

Normalization follows from $\alpha+t+h=1$. The sole proposal is correct, so every target has exactly row (56.2). The family

$$
\kappa_y=\alpha\nu_y+\frac\beta k\sum_{i=1}^k\delta_{a_i}
\tag{57.4}
$$

is TV-continuous. Its positive signed discrepancy from (57.3) is $r$ on the off-color tags; its negative discrepancies are $r-h$ at the actual-color tag and $h$ at the proposal tape. The base restrictions agree, giving $d(\kappa_y,\mu_y^+)=r$ at every source.

For the lower bound and uniqueness let $\lambda$ be any continuous family of uniform error at most $\varepsilon$, and fix an actual $z$. Write

$$
\begin{aligned}
a&=\lambda_z(Z),& P_0&=\lambda_z(\{p_j:j\ge1\}),\\
p_i&=\lambda_z(\{a_i\}),& L&=\sum_i p_i=1-a-P_0,\\
s&=\sup_{A\subseteq Z\text{ Borel}}
                     \big(\lambda_z(A)-\alpha\nu_z(A)\big)
                         \ge(a-\alpha)_+.
\end{aligned}
\tag{57.5}
$$

For each color $i$, use (56.4) to choose actual $y_\ell\to z$ in the signature topology with that color and $j_\ell=\Omega(y_\ell)\to\infty$. Apply the cap to the single measurable event

$$
A\sqcup\{a_j:j\ne i\}\sqcup
          \big(\{p_j:j\ge1\}\setminus\{p_{j_\ell}\}\big).
\tag{57.6}
$$

Its target mass is $\alpha\nu_{y_\ell}(A)$. Continuity of $\lambda$ and $\nu$, together with (56.5), passes the upper signed-difference inequality to $\lambda_z(A)-\alpha\nu_z(A)+L-p_i+P_0\le\varepsilon$. Taking the supremum over $A$, then averaging over $i$, gives

$$
\varepsilon\ge s+(1-1/k)L+P_0
       =(1-1/k)(1-a)+s+P_0/k\ge r.
\tag{57.7}
$$

For completeness, if $a\le\alpha$ the middle expression is at least $r+(1-1/k)(\alpha-a)+P_0/k$; if $a\ge\alpha$ it is at least $r+(a-\alpha)/k+P_0/k$. At $\varepsilon=r$ these inequalities force $a=\alpha$, $P_0=0$ and $s=0$. Then $L=\beta$, and the individual color inequalities force $p_i\ge\beta-r=\beta/k$; summing gives equality for each tag. The assertion $s=0$ means $\lambda_z|_Z\le\alpha\nu_z$ on every Borel event. Equal total mass makes these restrictions equal. Consequently $\lambda_z=\kappa_z$ for every actual $z$. This proves both the continuous lower bound and the uniqueness of its optimum without assuming component-weight preservation.

A lawful attainer would be continuous by Lemma 45.3, hence would acquire (57.4) exactly. In every anchor prefix cylinder, its greatest common submeasure is

$$
\ell^\kappa_{C_m(x_*)}=\frac\beta k\sum_i\delta_{a_i},
\qquad
\ell^\kappa_{C_m(x_*)}(\Theta^+)=\beta<1.
\tag{57.8}
$$

Indeed the base restriction of any common submeasure is zero by the dyadic-hole property, its proposal restriction is zero because all $\kappa_y$ give those tapes zero mass, and each tag mass is at most $\beta/k$. The displayed measure is itself dominated by every law. The necessary condition of Theorem 46.4 now excludes exact acquisition, so no lawful cap-$r$ preparation exists.

For every $\delta>0$, Theorem 46.6 supplies a lawful preparation of the unchanged $\nu$ family with laws $\widetilde\nu_y$ and uniform error at most $\delta$. Include its seed and an independent finite selector in one common product seed. On an initial branch of probability $\alpha$, run that preparation on the same source and hand over its base tape; on each branch of probability $\beta/k$, immediately hand over $a_i$. These are initial seed branches, with no restart or success conditioning. They terminate sourcewise almost surely, and their finite records and output events are measurable inherited events and finite unions of them. The resulting normalized law is

$$
\widetilde\kappa_y=\alpha\widetilde\nu_y
                             +\frac\beta k\sum_i\delta_{a_i},
\qquad
 d(\widetilde\kappa_y,\mu_y^+)
           =r+\alpha d(\widetilde\nu_y,\nu_y).
\tag{57.9}
$$

For the equality, the fixed positive tag mass is $r$, the negative tag/proposal mass is $r$, and the signed base measure has total mass zero. Positive base events approaching its supremum, together with all off-color tags, approach the positive discrepancy $r+\alpha d(\widetilde\nu_y,\nu_y)$; every measurable event has discrepancy bounded by this number. Complements give the same negative supremum. No event attaining the base supremum is assumed. Taking $\delta<(\eta-r)/\alpha$ makes every $\eta>r$ feasible. The lower bound gives $I(\mu^+)=r$, and Theorem 50.2 gives $R_{\mu^+}=r$ with its original order of quantifiers.

The countable product and Radon--Nikodym inputs in Theorems 46.4 and 46.6 have their same hypotheses here: countably many actual labels, probability measures on the declared measurable tape carrier, a finite dominating measure given by a countable mixture on tapes, and countably many measurable coordinate laws. In (50.6), every $\lambda_{x_i}$ is absolutely continuous with respect to the probability measure $\sigma_\lambda=\sum_i2^{-i}\lambda_{x_i}$; countability makes the simultaneous density infima measurable and permits one countable union of exceptional null sets. This mixture is not a law on sources. The countable product is defined on the product sigma algebra, with no standard-Borel sampling representation required. These are the reused interfaces `Measure.infinitePi` in [pinned Mathlib ProductMeasure](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/ProductMeasure.lean) and `withDensity_rnDeriv_eq` under absolute continuity and Lebesgue decomposition in [pinned Mathlib RadonNikodym](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean). Gallo, Lerasle and Takahashi, [*Markov approximation of chains of infinite order in the $\bar d$-metric*, Section 3, Lemma 3.1](https://arxiv.org/html/1107.4353v2), supplies the existing range-partition/lower-envelope reference frame. Its conditional-past, stationary-chain and coalescence assertions are not applied to these static sources. The positive-proposal result is the full-source moving-event deduction above, not a new product-measure or chain theorem. $\square$

**Theorem 57.2 (Attained comparison with the same row, profile and sharp value).** For every (56.1) and every prescribed profile, a fixed full-source family with row (56.2) and sharp value $r$ also exists that attains $r$. It may use the same carrier and consumer as Theorem 57.1, with every target supported on at most three tapes. Thus the all-source row, profile and sharp scalar together do not decide endpoint attainment.

**Proof.** On the same $\Theta^+$ choose $o=0\in Z$ and replace only the base specification in (57.3) by the fixed point law $\delta_o$:

$$
\mu_y^{\mathrm{att}}=\alpha\delta_o+t\delta_{a_{c(y)}}
                                      +h\delta_{p_{\Omega(y)}}.
\tag{57.10}
$$

This is a separately prescribed optimization problem: its family stays fixed while preparation varies. The calculation (57.5)--(57.7), with $\nu_y=\delta_o$, proves the same lower bound $r$ for every continuous, hence every lawful family, even though preparations may use any tape in the unchanged carrier. The constant law $\alpha\delta_o+(\beta/k)\sum_i\delta_{a_i}$ has exact error $r$ by the same signed-mass calculation. Handing its tape over in one transition from its finite positive-weight categorical seed support acquires it lawfully at every source. This proves attainment and, by Theorem 50.2, the unchanged sharp value formula. The three target families in Theorems 56.2, 57.1 and this theorem exhibit both failure mechanisms and attainment under exactly the same strictly positive row and every allowed profile, including the boundary $h=r$. $\square$

## 58. Scope of the intrinsic criterion and the remaining mathematical boundary

**Question 58.1 (General measurable and positive-profile extensions).** For the fixed original targets, occupied cylinders and measurable carrier, find an intrinsic necessary-and-sufficient condition for lawful attainment of $R_\mu$ on arbitrary measurable carriers, and characterize the remaining prescribed positive-proposal/profile classes. These questions remain unresolved outside the conclusions below.

Theorem 54.2 characterizes cap feasibility for each already prescribed countable power-set problem from its entire target data and actual observation geometry. It neither optimizes over replacement targets nor deduces the criterion from a terminal row or from the profile alone. Its stable values are constructed by (54.3)--(54.5); an arbitrary cap-compatible prepared family is not supplied under another name. Theorem 54.3 retains the global nonemptiness gate, so an individually nonempty fiber cannot certify lawful all-source feasibility when another fiber is empty.

The arbitrary-measurable-carrier target-intrinsic endpoint criterion remains unresolved. There the candidate-family condition (50.5)--(50.7) still requires a jointly compatible choice whose common submeasures exhaust mass one at every actual source. Theorem 55.1 shows why even a stable singleton continuous choice cannot discharge that obligation. The countable-ordinal stabilization proof in Theorem 54.2 also uses the separability of the countable-carrier TV range; that hypothesis is not asserted for the space of all probability measures on an arbitrary measurable carrier. No finite number of refinements, effective ordinal test or finite-description sampling procedure is supplied.

The positive-row constructions settle the input subclass $0<h\le r<1$, $e_y=d_y=0$ and $z_y=1-h$ at all sources, for every allowed prescribed profile. They do not classify $h>r$, other prescribed error/divergence rows, other consumers or all arbitrary measurable carriers. An additional requirement that prepared laws themselves satisfy the target profile or positive row would be a different cap problem; the constructions here do not impose it. Prescribing correlated target laws is distinct from lawfully obtaining them.

Infimum, attained cap and exact acquisition remain separate: a positive $R_\mu$ may be attained by a prepared law different from every target, and each strict cap above $R_\mu$ is feasible by Theorem 50.2 even when the endpoint fails. Countable target supports, a common finite support, continuity and common-submeasure exhaustion are different hypotheses. Sourcewise almost-sure finite execution does not supply a common finite horizon. The special approximants (56.9)--(56.11) and the comparison (57.10) have the expressly proved finite seed supports; the general criterion asserts no such support bound, effectiveness, real-sampling algorithm or resource guarantee.

The mathematical additions are the intrinsic target refinement and its lawful cap/locus consequences, its two distinct endpoint diagnostics, and the positive correct-proposal constructions with their moving-event lower bounds. The local value, continuity necessity, countable inverse-cumulative acquisition, arbitrary-carrier common-submeasure criterion, finite-common-carrier attainment and dyadic-hole family are reused from Sections 45--53. Closed-valued selection and transfinite derived mappings are established mathematics, used with the explicit correspondences and complete proofs above. The event-TV convention and finite-partition mass calculations agree with Levin and Peres, with Wilmer, [*Markov Chains and Mixing Times*, Proposition 4.2 and Remark 4.4](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf). The actual-source coloring uses only Boundaries 35.2 and Fibonacci (363.13). These are ordinary mathematical deductions in the stipulated measurable common-rule model, without a literature-priority assertion.

## 追加锚（本行以下为增补区）

## 59. A lossless target-density range on the original measurable tapes

**Definition 59.1 (Target-generated tape information).** Fix exactly the full labeled source (44.1), every target law, the original consumer and its nonempty measurable tape carrier $(\Theta,\mathcal F)$, as in Definition 50.1. Thus

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor,\ g\in\mathbb Z\},\\
N(r,g)&=1+F_rg,\qquad \Omega(r,g)=\omega(N(r,g)),\qquad \beta_0=0.
\end{aligned}
\tag{59.1}
$$

Here $\omega$ counts distinct prime divisors. All original labels remain in the occupied cylinders $C_m(x)$, including equal-signature labels with different targets. Only actual prime-divisibility answers are source observations. Any prescribed row or profile constrains the original $\mu_y$, without constraining the prepared rows.

Enumerate $X$ without repetitions as $x_1,x_2,\ldots$, and define

$$
\begin{aligned}
\sigma&=\sum_{i\ge1}2^{-i}\mu_{x_i},
&f_i&=\frac{d\mu_{x_i}}{d\sigma},\\
\mathcal G&=\sigma(f_i:i\ge1)\subseteq\mathcal F,
&P_{\mathcal G}&=\left\{g\sigma:g\ge0,\ g\text{ is }\mathcal G\text{-measurable},\ \int g\,d\sigma=1\right\}.
\end{aligned}
\tag{59.2}
$$

Choose finite nonnegative measurable density versions; since $\mu_{x_i}\le2^i\sigma$, they can be chosen with $f_i\le2^i$ everywhere. Densities are identified almost everywhere. The notation $g\sigma$ means the measure $A\mapsto\int_A g\,d\sigma$ on the entire original $\mathcal F$, rather than a measure only on $\mathcal G$. The mixture $\sigma$ is a probability on tapes; its index weights supply no probability or sampling operation on sources.

For a finite positive tape measure $\nu$, write its Lebesgue decomposition relative to $\sigma$ as $\nu=h_\nu\sigma+\nu_\perp$, where $\nu_\perp$ is singular to $\sigma$. Put

$$
\Pi\nu=\left(\mathsf E_\sigma[h_\nu\mid\mathcal G]+\nu_\perp(\Theta)\right)\sigma.
\tag{59.3}
$$

The conditional expectation is on the probability space of tapes: it is the integrable $\mathcal G$-measurable density whose integral over each $B\in\mathcal G$ equals $\int_B h_\nu\,d\sigma$. This is a map on finite measures, not an extra observation or a supplied consumer tape map.

**Theorem 59.2 (Lossless density reduction for radii and lawful caps).** The map $\Pi$ is positive, additive, positively homogeneous and mass-preserving. It is idempotent, fixes every original target, and contracts event-supremum TV between probability measures. The space $P_{\mathcal G}$ is complete and separable in TV. For every occupied cylinder $C$,

$$
\inf_{v\in P_{\mathcal G}}\sup_{y\in C}\operatorname{TV}(v,\mu_y)
=\rho_\mu(C).
\tag{59.4}
$$

Consequently the original sharp value is exactly

$$
R_\mu=\sup_{x\in X}\inf_{m\ge0}\inf_{v\in P_{\mathcal G}}
                       \sup_{y\in C_m(x)}\operatorname{TV}(v,\mu_y).
\tag{59.5}
$$

Moreover, for each cap $\eta\in[0,1]$, a lawful preparation within cap $\eta$ exists if and only if one exists whose prepared laws all belong to $P_{\mathcal G}$. The latter preparation hands tapes in the original $(\Theta,\mathcal F)$ to the same consumer on the same static source. Thus this restriction preserves cap feasibility, endpoint attainment and exact acquisition separately, on arbitrary measurable carriers.

**Proof.** Both measures in the Lebesgue decomposition are finite and positive. Uniqueness makes their absolutely continuous and singular parts additive and positively homogeneous. Conditional expectation exists without a regular conditional distribution: for any nonnegative integrable $h$, apply Radon--Nikodym on $(\Theta,\mathcal G,\sigma|_{\mathcal G})$ to the finite measure $B\mapsto\int_B h\,d\sigma$. Its density is nonnegative, has the same integral as $h$, and is unique almost everywhere. Uniqueness gives additivity and positive homogeneity. A $\mathcal G$-measurable $h$ is its own conditional expectation. These statements prove all the asserted algebraic properties of $\Pi$, including

$$
\Pi\nu(\Theta)=\nu(\Theta),\qquad
\rho\le\nu\Longrightarrow\Pi\rho\le\Pi\nu,
\qquad \Pi\mu_y=\mu_y.
\tag{59.6}
$$

Its image among probability laws is precisely $P_{\mathcal G}$, on which it is the identity.

For the TV contraction, take probabilities $v,w$, dominate them by $\alpha=v+w$, and let their densities be $u,t$. Their greatest common submeasure is $\rho=\min(u,t)\alpha$. The event $\{u>t\}$ and its complement show directly that

$$
\operatorname{TV}(v,w)=\int(u-t)_+\,d\alpha
                     =1-\rho(\Theta).
\tag{59.7}
$$

By (59.6), $\Pi\rho$ is a common submeasure of $\Pi v$ and $\Pi w$ with the same mass. Their positive residual measures each have total mass $1-\rho(\Theta)$, so every event discrepancy between them is bounded by that number. Hence

$$
\operatorname{TV}(\Pi v,\Pi w)\le\operatorname{TV}(v,w),
\qquad
\operatorname{TV}(\Pi v,\mu_y)\le\operatorname{TV}(v,\mu_y).
\tag{59.8}
$$

Applying the second inequality to each center gives one inequality in (59.4); inclusion $P_{\mathcal G}\subseteq\mathcal P(\Theta,\mathcal F)$ gives the other. Each cylinder is handled separately, with no presumed center attainer or exchange of extrema. Equation (59.5) then follows in the original order of quantifiers.

The rational level sets of the countably many $f_i$ generate $\mathcal G$, so their finite Boolean combinations form a countable generating algebra. Every $\mathcal G$-measurable set can be approximated in $\sigma$-measure by this algebra: the class of approximable sets contains the algebra, is closed under complements, and is closed under countable unions by first truncating a union to finitely many terms under the finite measure. Rational simple functions over the algebra are consequently dense in $L^1(\sigma|_{\mathcal G})$. This space is separable and complete. Its inclusion in $L^1(\sigma)$ is isometric, and its nonnegative integral-one subset is closed. For two densities in that subset, (59.7) gives

$$
\operatorname{TV}(g\sigma,k\sigma)=\frac12\int|g-k|\,d\sigma.
\tag{59.9}
$$

This proves the asserted completeness and separability of $P_{\mathcal G}$ even when the full tape sigma algebra has no countable-generation property.

It remains to establish the operational assertion; contraction alone would not establish it. Suppose a lawful preparation has laws $\lambda_y$. Lemma 45.3 supplies, for each actual $x$, common finite-record submeasures $\rho_{x,m}\le\lambda_y$ for every $y\in C_m(x)$, with masses tending to one. Thus $\Pi\rho_{x,m}\le\Pi\lambda_y$ throughout that cylinder, with unchanged mass. The greatest common submeasure $\ell'_C$ of the countable family $(\Pi\lambda_y)_{y\in C}$ therefore satisfies

$$
a'_{C_m(x)}:=\ell'_{C_m(x)}(\Theta)
\ge\rho_{x,m}(\Theta)\longrightarrow1.
\tag{59.10}
$$

These greatest submeasures exist by the same countable RN-infimum argument as Theorem 46.4. They increase under cylinder refinement and are dominated along source $x$ by $\Pi\lambda_x$.

For completeness, their actual realization is the positive-increment construction of that theorem. At the root use $\Delta_X=\ell'_X$; at every other occupied node with parent $C^-$ use $\Delta_C=\ell'_C-\ell'_{C^-}$. Preload an original-tape coordinate $W_C$ of law $\Delta_C/\Delta_C(\Theta)$ when its mass is positive, and a fixed tape when it is zero. All these coordinates and an independent uniform $U\in(0,1)$ belong from the start to one source-independent product seed. At a reached node $C$, hand over $W_C$ if $U<a'_C$; otherwise query the next actual prime. The node-output submeasure is $\Delta_C$, since reaching a non-root node implies $U\ge a'_{C^-}$. Along each actual source the submeasures telescope to $\ell'_{C_m(x)}$, and (59.10) gives a finite actual handoff almost surely with total output law $\Pi\lambda_x$.

Finite records and output-event preimages are measurable interval and coordinate events, or countable unions of them. The normalized coordinates are probability laws on the original arbitrary measurable tapes; the countable product gives a seed directly. The consumer receives the selected tape, with no further record input. This uses no conditional sampling kernel implementing $\Pi$, and supplies no uniform horizon, effectiveness or finite-description sampler. By (59.8) the new uniform error is no greater than that of $\lambda$. Conversely any lawful preparation valued in $P_{\mathcal G}$ is already a lawful preparation on the original carrier.

The finite-measure decomposition and conditional-expectation ingredients are standard: see Fremlin, *Measure Theory*, [232I, Lebesgue decomposition](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), and [242J(b)--(g), printed pp. 13--14](https://www1.essex.ac.uk/maths/people/fremlin/chap24.pdf). Their inputs here are finite tape measures and a sigma subalgebra of a probability space. The acquisition bridge is the original prime-prefix construction of Theorem 46.4. The conclusion is their lossless reduction for this fixed acquisition problem, rather than a new conditional-expectation or product-measure theorem. $\square$

The range in (59.2) is target-defined modulo null sets. Changing countably many density versions changes its sigma algebra only modulo the common null ideal. More generally take another positive target mixture $\sigma'=\sum_i a_i\mu_{x_i}$, with $a_i>0$ and $\sum_i a_i=1$. Its density $w=d\sigma'/d\sigma=\sum_i a_i f_i$ is $\mathcal G$-measurable, finite and positive almost everywhere. The new target densities are $f_i'=f_i/w$, and conversely $1/w=\sum_i2^{-i}f_i'$. These two formulas identify the density-generated sigma algebras modulo their common null ideal. They also identify their law ranges by $g\sigma=(g/w)\sigma'$. Thus enumeration and positive mixture weights do not change the reduced probability-law range.

## 60. Countably atomic likelihood information and original-tape acquisition

**Definition 60.1 (The atomic input subclass).** In addition to Definition 59.1, assume that $\sigma|_{\mathcal G}$ is purely atomic in the following explicit sense. There is a nonempty finite or countable index set $J$ and pairwise disjoint $A_j\in\mathcal G$ such that

$$
\sigma(A_j)>0,\qquad
\sigma\left(\bigcup_{j\in J}A_j\right)=1,
\qquad
\sigma(A_j\cap B)\in\{0,\sigma(A_j)\}\quad(B\in\mathcal G).
\tag{60.1}
$$

Define fixed probability components on the original tapes and target vectors on $J$ by

$$
\kappa_j(A)=\frac{\sigma(A\cap A_j)}{\sigma(A_j)}\quad(A\in\mathcal F),
\qquad p_y(j)=\mu_y(A_j).
\tag{60.2}
$$

The components may be diffuse with respect to $\mathcal F$. Hypothesis (60.1) is a condition on the entire original target family through its likelihood information; it is not a restriction on prepared laws, a finite point-support assumption, or a consequence of countability of $X$.

**Theorem 60.2 (Restricted intrinsic cap criterion with the original carrier retained).** Under (60.1), use the actual signature space $Q$ and every original label, and apply the target refinement (54.3)--(54.5) on $\mathcal P(J)$ to the vectors $p_y$. Denote its stable values by $K_{\infty,J}^{\eta}(q)$. Then, for every $\eta\in[0,1]$,

$$
\begin{aligned}
&\text{a lawful original-tape preparation within cap }\eta\text{ exists}\\
&\qquad\Longleftrightarrow\quad
K_{\infty,J}^{\eta}(q)\ne\varnothing\quad\text{for every actual }q\in Q.
\end{aligned}
\tag{60.3}
$$

Every occupied-cylinder radius equals that of the vector targets, so the cap $\eta=R_\mu$ in (60.3) gives the endpoint criterion with the original sharp value. If $J$ is finite, that endpoint is always attained. The refinement and its countable-carrier selection theorem are reused from Section 54; the additional assertion is their lossless lift to this subclass of arbitrary original tape spaces.

**Proof.** On a positive-mass $\mathcal G$-atom, each real $\mathcal G$-measurable function is constant almost everywhere: its rational sublevel sets have either zero or full atom mass, which determines one essential value. Applying this to all $f_i$ and all atoms, with one countable union of exceptional null sets, gives

$$
\mu_y=\sum_{j\in J}p_y(j)\kappa_j.
\tag{60.4}
$$

In particular every original target vector is a normalized probability. More generally define

$$
\mathcal L(u)=\sum_{j\in J}u(j)\kappa_j\qquad(u\in\mathcal P(J)).
\tag{60.5}
$$

The same atom argument identifies $P_{\mathcal G}$ exactly with these mixtures. For probabilities $u,v$, an event $A\in\mathcal F$ gives discrepancy $\sum_j(u(j)-v(j))\kappa_j(A)$, with every coefficient $\kappa_j(A)$ between zero and one. Its absolute value is bounded by half the sum of the absolute vector discrepancies. The measurable union of the $A_j$ for which $u(j)>v(j)$ achieves the positive discrepancy. Therefore

$$
\operatorname{TV}(\mathcal L(u),\mathcal L(v))
=\operatorname{TV}(u,v)=\frac12\sum_{j\in J}|u(j)-v(j)|.
\tag{60.6}
$$

Define a measurable index map $T:\Theta\to J$ by $T=j$ on $A_j$, and send the measurable null remainder to one fixed $j_0\in J$. Countability of the partition makes preimages of all subsets of $J$ measurable. Equation (60.4) gives $T_*\mu_y=p_y$, and preimages in the event definition give

$$
\operatorname{TV}(T_*v,p_y)\le\operatorname{TV}(v,\mu_y)
\qquad(v\in\mathcal P(\Theta,\mathcal F)).
\tag{60.7}
$$

Thus compression of arbitrary centers and the isometric lift of vector centers prove equality of the radius in each unchanged occupied cylinder. This also follows from (59.4) and (60.6), and preserves the order $\sup_x\inf_m\inf_v\sup_y$ without requiring attained local centers.

A lawful original-tape cap preparation can be compressed by declaring $T$ of its terminal tape. This adds a measurable terminal operation and no source observation. Its index laws have the same cap or a smaller one by (60.7), and its sourcewise almost-sure finite stopping is unchanged. The necessity of Theorem 54.2 therefore gives the all-source nonemptiness condition in (60.3).

Conversely, suppose all stable vector fibers are nonempty. Theorem 54.2 supplies a TV-continuous selected vector family $u([y])$ within cap $\eta$ of every original $p_y$, and acquires its index $J_y$ by the finite-prime uniform-seed certificates (54.11). In one common seed, include that uniform coordinate and independent original-tape coordinates $W_j$ of laws $\kappa_j$. The index acquisition uses only the uniform coordinate and actual prime answers, so it is independent of the $W_j$. At its finite termination hand $W_{J_y}$ to the unchanged consumer. For every $A\in\mathcal F$,

$$
\mathsf P\{W_{J_y}\in A\}
=\sum_{j\in J}\mathsf P\{J_y=j\}\kappa_j(A)
=\mathcal L(u([y]))(A).
\tag{60.8}
$$

The output preimage is the countable union of $\{J_y=j\}\cap\{W_j\in A\}$, hence is measurable. Normalization is exact; index acquisition terminates almost surely at each original source, and the handoff is one further finite operation. The original consumer subsequently runs on that source. Equation (60.6) proves the cap against every fixed $\mu_y$. No constancy of the consumer within an atom is needed, because (60.8) identifies its entire tape law on $\mathcal F$.

The source set in this application of Section 54 is still $X$: in particular its initial vector fiber intersects the cap balls for every label with signature $q$. All occupied prefix neighborhoods and all-source gates are retained. The index construction is only an auxiliary representation; its final output is the actual original tape. For finite $J$, reuse Theorem 51.1 on that finite index carrier and the same lift to attain the original $R_\mu$. The common product seed may still have diffuse tape coordinates and supplies no common finite execution bound. $\square$

Condition (60.1) can equivalently be checked by essential countability of the joint likelihood profile $(f_i(\theta))_{i\ge1}$. Indeed each atom makes all its coordinates constant outside one common null set, so the profile has countable range almost everywhere. Conversely, if it has countable range on a full-measure measurable set, its positive-mass fibers are measurable by countably many coordinate equalities. These fibers cover almost all tapes and are atoms of the generated sigma algebra, since every generating level set is constant on each fiber. This equivalence concerns likelihood information, not countability of the original tapes. Domination, standard Borel structure and separable $L^1$ alone do not imply the condition.

## 61. Local depletion of prepared correct-proposal mass

**Definition 61.1 (Original correct mass in an occupied high-target tail).** For the unchanged consumer put $S_y=H_y\setminus F_y$, its measurable event of a correct finite proposal, and write

$$
s_y=\mu_y(S_y)=h_y-e_y.
\tag{61.1}
$$

Let $\mathscr C$ consist of the occupied finite-prime-prefix cylinders, including $X$. For $C\in\mathscr C$ and an integer $K\ge0$, define

$$
D(C,K)=\{y\in C:\Omega(y)>K\},
\qquad
L_\mu=\sup_{C\in\mathscr C}\sup_{K\ge0}\inf_{y\in D(C,K)}s_y.
\tag{61.2}
$$

Every such tail is nonempty by [Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows) on the actual source (59.1). Its arithmetic interface is [Fibonacci equation (363.13)](FIBONACCI_ATOMIC_RELATION_GENERATION.md), $q\mid F_n\Longleftrightarrow z(q)\mid n$, with the standard recurrence $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$. The quantity $L_\mu$ is fixed by the original targets and consumer events; it quantifies over no prepared-law family.

**Theorem 61.2 (Local depletion and the intrinsic correct-mass lower bound).** For every lawful preparation on the original arbitrary measurable carrier,

$$
\inf_{y\in D(C,K)}\widehat\mu_y(S_y)=0
\qquad(C\in\mathscr C,\ K\ge0).
\tag{61.3}
$$

If its uniform event-TV error is $\varepsilon$, then

$$
\varepsilon\ge L_\mu,
\qquad
R_\mu=I(\mu)\ge L_\mu\ge\inf_{y\in X}(h_y-e_y).
\tag{61.4}
$$

There is no row or error constraint on the prepared laws in this statement, and no assumption that the consumer terminates almost surely.

**Proof.** Fix $C=C_d(z)$, $K$ and $\gamma>0$. Write $D=D(C,K)$ and

$$
p_y=\widehat\mu_y(H_y),\qquad
c_y=\widehat\mu_y(S_y),\qquad M=\sup_{y\in D}p_y\le1.
\tag{61.5}
$$

If $M=0$, every $c_y$ in $D$ is zero. Otherwise choose one actual $x\in D$ with $p_x>M-\gamma/2$. Flatten preparation and consumer chronologically under their one common seed as in Proposition 45.2. Let $G_m(x)$ be the measurable seed event on which the actual composite execution terminates with a finite proposal within $m$ transitions, uses only primes in $P_m$, and has terminal proposal at most $m$. These events increase to the actual composite proposal event at $x$. Finite proposals have finite composite length and finite queried menus; preparation divergence is null. Consequently choose an integer $m\ge\max\{d,K,1\}$ such that

$$
\mathsf P(G_m(x))>p_x-\gamma/2>M-\gamma.
\tag{61.6}
$$

Theorem 35.2 supplies one actual $y$ matching $x$ on all of $P_m$ and satisfying $\Omega(y)>m$. This source is chosen for the whole measurable event $G_m(x)$, before quantifying over its seeds. It belongs to $D$: matching the first $d$ bits puts it in $C$, and $m\ge K$ gives its target bound. Deterministic replay of each finite composite record at that same $y$ keeps its handoff, consumer record and terminal proposal identical. All transported proposals are at most $m<\Omega(y)$, so they are false at $y$. Therefore

$$
\widehat\mu_y(F_y)\ge\mathsf P(G_m(x)),\qquad
c_y=p_y-\widehat\mu_y(F_y)\le M-\mathsf P(G_m(x))<\gamma.
\tag{61.7}
$$

This proves (61.3) by nonnegativity and arbitrary $\gamma$. The selected comparison source is a proof witness, not an operation that selects or samples the execution source. The same source works for the entire finite event, including all its real-output restrictions.

At that witness, event-TV on the source's own correct event gives

$$
s_y\le\widehat\mu_y(S_y)+\varepsilon<\gamma+\varepsilon.
\tag{61.8}
$$

When $M=0$ the analogous inequality holds at every $y\in D$. Thus $\inf_{y\in D}s_y\le\varepsilon$ after letting $\gamma$ decrease to zero. Taking the two suprema in (61.2) proves $\varepsilon\ge L_\mu$. Taking the infimum over lawful preparations and reusing Theorem 50.2 proves the bound on the unchanged sharp expression. Finally $D(X,0)=X$, since every actual $\Omega$ is positive, so $L_\mu\ge\inf_y s_y$.

This proof uses finite-record replay, continuity from below and event-TV. Compared with the saturation calculation (43.29), the approximate supremum over $D(C,K)$ removes the need for an anchor or a radius attainer to realize maximal proposal mass. It constructs no new acquisition procedure, uses no uniform horizon and conditions away no failures. $\square$

**Theorem 61.3 (The universal truthful-row restriction with its all-source premise).** Suppose the original fixed targets satisfy

$$
h_y=h>0,\qquad e_y=0\qquad\text{for every original }y\in X.
\tag{61.9}
$$

For every allowed consumer and arbitrary measurable tape carrier, $R_\mu\ge h$. Thus a proposed sharp value $r<h$ is impossible in this input class. If $h=1$, then $R_\mu=1$ and the endpoint is attained. More generally, under the original profile (44.2), an all-source premise $h_y\ge h_0$ gives

$$
R_\mu\ge L_\mu\ge(1-B)h_0,
\qquad B=\lim_{k\to\infty}b(k).
\tag{61.10}
$$

**Proof.** Under (61.9), every correct mass $s_y$ equals $h$, so every nonempty tail in (61.2) has infimum $h$ and $L_\mu=h$. Apply Theorem 61.2. At $h=1$, TV is at most one, and Theorem 50.2 supplies attainment at that value. Under the more general premise,

$$
s_y=h_y-e_y\ge(1-b(\Omega(y)))h_y\ge(1-B)h_0
\qquad(y\in X),
\tag{61.11}
$$

so the same theorem gives (61.10); the actual $L_\mu$ can be stronger than this profile-only bound.

For $0<h<1$, the already prescribed examples of Theorems 56.2, 57.1 and 57.2 give unattained and attained possibilities at every $h\le r<1$ for the row $(h,0,0,1-h)$ and every allowed profile. Those examples are reused without reconstructing or substituting their families. They show, in particular, that $L_\mu=R_\mu=h$ does not decide attainment. The necessity $h\le R_\mu$ holds with arbitrary target divergence/nonproposal splits under (61.9), because its proof uses only correct mass.

The all-source premise is essential to this conclusion. It is not the anchor-only bound $(1-B)h/(2-B)$ of Theorem 46.1, whose other target rows are free. For nonzero prescribed errors the correct quantity is $h_y-e_y$ or its localized bound (61.2); the inequality $h_y>r$ alone gives no exclusion. Thus the theorem settles the truthful-row parameter obstruction without classifying all nonzero-error profiles or all fixed families at a permissible scalar value. $\square$

## 62. The remaining order-compatible selection problem

**Question 62.1 (Intrinsic exhaustion beyond atomic likelihood information).** Retain the unresolved general problem of Question 58.1 for the original targets, carrier, consumer and occupied cylinders. Theorem 59.2 permits its candidate laws to be sought in the target-defined complete separable range $P_{\mathcal G}$ without losing any lawful cap. Theorem 60.2 gives an intrinsic cap criterion only under the additional atomic input condition (60.1). Find a target-defined construction or obstruction that settles general lawful cap feasibility and endpoint attainment when that condition fails.

The precise remaining obligation can be displayed in this range. A candidate cap selection on the actual signatures has laws $\lambda_q=g_q\sigma$, with nonnegative $\mathcal G$-measurable densities of integral one, and must satisfy

$$
\operatorname{TV}(g_{[y]}\sigma,\mu_y)\le\eta\qquad(y\in X).
\tag{62.1}
$$

For each $q$ its greatest cylinder common-submeasure mass is

$$
\int\inf_{q'\in U_m(q)}g_{q'}\,d\sigma.
\tag{62.2}
$$

By Theorem 46.4, exact acquisition of that selected family requires these masses to increase to one at every actual $q$. Equivalently, after one common null-set removal,

$$
g_q(\theta)=\sup_m\inf_{q'\in U_m(q)}g_{q'}(\theta)
\qquad\text{for every }q\in Q
\text{ and almost every }\theta.
\tag{62.3}
$$

Indeed the increasing infima are bounded by $g_q$, and monotone convergence identifies their limiting integral; equality of that integral with one makes the nonnegative deficit zero. Countability of $Q$ permits the single exceptional-set removal. At each remaining tape, (62.3) is lower semicontinuity of $q\mapsto g_q(\theta)$ in the actual prefix topology. This is the existing exhaustion obligation in densities, not a target-intrinsic solution obtained by renaming candidate prepared laws.

The complete separable range supplies the metric stabilization and clopen continuous-selection hypotheses used in Section 54, but those metric steps do not force (62.3). This failure persists within the reduced range itself. To see it, reuse the fixed positive-row family of Theorem 57.1 and its unique continuous cap-$r$ optimum $\kappa$. The contraction (59.8) makes $\Pi\kappa$ another continuous cap-$r$ family for exactly those same targets. Uniqueness gives $\Pi\kappa_y=\kappa_y$ at every source, so this optimum already belongs to $P_{\mathcal G}$. Its anchor-cylinder common-submeasure mass remains the published $\beta<1$ in (57.8), and no lawful cap-$r$ preparation exists. Hence separability and continuous compatibility still leave a genuine exhaustion gap, even for the existing standard Borel example; no additional example family is needed.

The general prescribed positive-proposal/profile and arbitrary-consumer endpoint classifications likewise remain unresolved beyond the all-source correct-mass obstruction of Section 61 and the explicitly restricted criteria above. The results preserve the original event-TV convention, sharp quantifier order and every actual source. Their common seeds and tables establish measurable law existence with sourcewise almost-sure finite execution; they imply no finite-description or effective sampler, finite seed support, common finite horizon, physical realization or kernel guarantee. The substantive deductions are the lossless target-density reduction with its operational bridge and the local correct-mass depletion bound. Countable refinement, finite-index attainment, common-submeasure acquisition and the endpoint examples are reused results, and the measure-theoretic ingredients are classical. No literature-priority assertion is made.

## 追加锚（本行以下为增补区）

## 63. Target-fixed positive transfers cannot shrink the likelihood range

**Definition 63.1 (The common positive-transfer class).** Keep the entire labeled source (59.1), the original measurable tape carrier, consumer and target family fixed. Use the tape mixture $\sigma$, likelihood sigma algebra $\mathcal G$ and original-tape range $P_{\mathcal G}$ of (59.2). Let $\mathsf M_+(\Theta,\mathcal F)$ be the cone of finite positive countably additive measures, and let $\mathsf M_{\mathbb R}(\Theta,\mathcal F)$ be the real vector space of finite signed measures with variation norm $\|\lambda\|_{\mathrm{var}}=|\lambda|(\Theta)$. A transfer in this section is one map

$$
T:\mathsf M_+(\Theta,\mathcal F)\longrightarrow\mathsf M_+(\Theta,\mathcal F)
\tag{63.1}
$$

which is additive, positively homogeneous for every real scalar $t\ge0$, mass-preserving on every finite positive measure, and target-fixed: $T\mu_y=\mu_y$ for every original label $y$. The same map acts on all measures, rather than being chosen separately by source, cap or cylinder. No idempotence is assumed. This is a mathematical operation on laws; a measurable tape map or a sampling implementation of $T$ is not part of the hypothesis.

**Theorem 63.2 (Forced likelihood range and the finite-atom boundary).** Every transfer (63.1) has a unique real-linear signed extension $\widetilde T$ which is a variation-norm contraction. It fixes every real integrable likelihood density:

$$
\widetilde T(g\sigma)=g\sigma
\qquad\bigl(g\in L^1(\sigma|_{\mathcal G};\mathbb R)\bigr).
\tag{63.2}
$$

In particular its positive probability image contains $P_{\mathcal G}$. This forced range is sharp: the already defined $\Pi$ of (59.3) is in the transfer class and has probability image exactly $P_{\mathcal G}$.

The following three existence statements are equivalent:

1. Some transfer in this class has its probability image contained in a finite-dimensional real subspace of $\mathsf M_{\mathbb R}(\Theta,\mathcal F)$.
2. Some transfer in this class has a relatively TV-compact probability image on the original tapes.
3. Modulo $\sigma$-null sets, $\mathcal G$ has a finite partition into positive-mass atoms, that is, (60.1) holds with finite $J$.

Thus countably infinitely atomic likelihood information, as well as any likelihood information with a nonatomic part, prevents both proposed kinds of positive target-fixed reduction. The finite atoms here are atoms of $\mathcal G$ under $\sigma$, and need not be point tapes or atoms of $\mathcal F$.

**Proof.** For positive $\alpha,\beta$ define $\widetilde T(\alpha-\beta)=T\alpha-T\beta$. If $\alpha-\beta=\alpha'-\beta'$, then $\alpha+\beta'=\alpha'+\beta$; additivity makes the definition independent of the representation. Additivity and homogeneity give the unique real-linear extension. Positivity gives

$$
|\widetilde T\lambda|\le T|\lambda|,
\qquad
\|\widetilde T\lambda\|_{\mathrm{var}}
\le T|\lambda|(\Theta)=\|\lambda\|_{\mathrm{var}}.
\tag{63.3}
$$

For example the first inequality follows by applying positivity to $-|\lambda|\le\lambda\le|\lambda|$ and taking the least positive measure dominating both signs. Consequently the fixed space $V=\{\lambda:\widetilde T\lambda=\lambda\}$ is norm closed. It is a vector sublattice: for $\lambda\in V$, (63.3) gives $|\lambda|\le T|\lambda|$, and the two finite positive measures have the same mass, hence are equal. Absolute values and linear combinations give lattice minima and maxima in $V$.

This fixed-sublattice fact is the classical input of Douglas, [*Contractive projections on an $L^1$ space*, Proposition 13, printed p. 460](https://msp.org/pjm/1965/15-2/pjm-v15-n2-p06-s.pdf), *Pacific Journal of Mathematics* **15** (1965), 443--462. Proposition 13 expressly includes positive contractions on the space of finite measures and requires no projection assumption. The preceding argument verifies its hypotheses and its real-measure consequence here; no classification of conditional expectations is invoked.

Every $f_i\sigma=\mu_{x_i}$ belongs to $V$. Variation-norm convergence of the positive mixture gives $\sigma\in V$, since its finite partial sums are fixed and their omitted masses tend to zero. For rational $t$, lattice closure therefore puts $(f_i-t)_+\sigma$ and

$$
\min\{n(f_i-t)_+,1\}\sigma\quad(n\ge1)
\tag{63.4}
$$

in $V$. These bounded densities converge in $L^1(\sigma)$ to $\mathbf1_{\{f_i>t\}}$. Thus $V$ contains the indicator measure of each rational likelihood superlevel set.

The sets $B\in\mathcal F$ whose indicator measures $\mathbf1_B\sigma$ belong to $V$ form a sigma algebra: complements use $\sigma\in V$, finite intersections use lattice minima, and countable unions follow from finite unions and norm convergence of their increasing indicator measures under the finite measure $\sigma$. This sigma algebra contains every generator of $\mathcal G$. Hence $V$ contains all $\mathcal G$-simple signed density measures. Their $L^1$ density and closedness of $V$ prove (63.2), including unbounded integrable real densities. The properties and exact image of $\Pi$ needed for sharpness are those already proved in Theorem 59.2.

For the compactness boundary, disjoint positive-mass sets $A_1,\ldots,A_k\in\mathcal G$ give probability measures

$$
v_j=\frac{\mathbf1_{A_j}}{\sigma(A_j)}\sigma\in P_{\mathcal G},
\qquad \operatorname{TV}(v_i,v_j)=1\quad(i\ne j).
\tag{63.5}
$$

They all belong to every transfer's probability image by (63.2). Relative compactness implies total boundedness, so a finite cover by balls of radius less than $1/2$ bounds the number of such disjoint sets. There is consequently a largest possible finite cardinality $k$ of a disjoint positive-mass collection. Choose a collection of that cardinality. Its complement is null, since otherwise it could be adjoined; each member is an atom, since otherwise it could be split into two positive-mass measurable sets. This is exactly the finite partition in statement 3. This argument also proves that failure of statement 3 supplies arbitrarily large finite sets of probability measures separated as in (63.5), without any topology on tapes.

A probability image contained in a finite-dimensional real subspace is bounded in variation norm, since every probability has norm one. Its closure there is compact; the probability measures form a closed subset in variation norm, and event-TV on them is half that norm. Thus statement 1 implies statement 2. Conversely, under statement 3 the original-tape identification (60.4)--(60.6) makes $P_{\mathcal G}$ the compact finite simplex of mixtures of the fixed measures $\kappa_j$. Choosing $T=\Pi$ establishes statements 1 and 2. This proves the equivalence. $\square$

The same rigidity acts directly on the proposed order repair. If a reduced cap family has laws $\lambda_q=g_q\sigma\in P_{\mathcal G}$, then $T\lambda_q=\lambda_q$ for all actual signatures. Its cylinder common submeasures are also fixed, since their densities $\inf_{q'\in U_m(q)}g_{q'}$ are nonnegative integrable $\mathcal G$-measurable functions. Thus neither that family nor its common-submeasure masses can change under this transfer class. In particular the already reduced continuous optimum in Section 62, supplied by Theorem 57.1, retains its published mass deficit under every such transfer; its example is not reconstructed here. The obstruction concerns a common additive, positively homogeneous, mass-preserving, target-fixed operation on all finite positive original-tape measures. It does not exclude nonlinear cap-specific selections, transfers that fail these hypotheses, or a different selection within the original cap constraints.

## 64. A finite-dimensional order envelope for original-tape caps

**Definition 64.1 (A fixed target-specified density space).** Retain the original inputs of Definition 59.1 and the actual signature space $Q$ of (50.2). As an additional supplier hypothesis, specify from these fixed targets and their measurable structure one finite-dimensional real linear subspace

$$
E\subseteq L^1(\sigma|_{\mathcal G};\mathbb R),
\qquad
P_E=\left\{g\in E:g\ge0\ \sigma\text{-almost everywhere},\ \int g\,d\sigma=1\right\}\ne\varnothing.
\tag{64.1}
$$

The specification of $E$ is fixed before choosing the preparation; it is not an unknown prepared family. It need not contain any or all of the target densities. Identify $g\in P_E$ with its law $g\sigma$ on the entire original $\mathcal F$, and give $P_E$ the event-TV metric $d_E(g,k)=\frac12\|g-k\|_1$.

For $\eta\in[0,1]$ the initial fibers are

$$
K_{0,E}^{\eta}(q)=\bigcap_{y\in X:\,[y]=q}
 \left\{g\in P_E:\operatorname{TV}(g\sigma,\mu_y)\le\eta\right\}.
\tag{64.2}
$$

Use exactly the distance refinement and countable-ordinal intersections (54.4)--(54.5), with range $P_E$, metric $d_E$ and neighborhoods $U_m(q)$. Write $K_{\infty,E}^{\eta}$ for the stabilized fibers. Every original label occurs in (64.2); even if two labels have identical complete prime observations, neither of their possibly different targets is dropped.

**Theorem 64.2 (Integrable order-envelope cap certificate).** If

$$
K_{\infty,E}^{\eta}(q)\ne\varnothing\qquad(q\in Q),
\tag{64.3}
$$

then a lawful preparation on the original tapes achieves uniform error at most $\eta$, with prepared laws in $\{g\sigma:g\in P_E\}$. The preparation has one source-independent product seed, uses only actual prime answers, and hands its tape to the unchanged consumer on the same static source after sourcewise almost-sure finite execution.

The additional order assertion is the following. Every TV-continuous map $q\mapsto g_q\in P_E$ has cylinder greatest common submeasures

$$
\ell_{C_m(x)}(A)=\int_A\inf_{q'\in U_m([x])}g_{q'}\,d\sigma
\quad(A\in\mathcal F)
\tag{64.4}
$$

whose masses increase to one at every original source $x$. More precisely, a measurable basis envelope $w\in L^1_+(\sigma|_{\mathcal G})$, independent of $q$, supplies for every $q$ and every $\delta>0$ some finite $m$ such that

$$
\ell_{C_m(q)}(\Theta)\ge1-\delta\int w\,d\sigma.
\tag{64.5}
$$

Here $C_m(q)=\{y:[y]\in U_m(q)\}$, as in (54.2). The source-dependent depth in (64.5) need not be uniform on $Q$.

**Proof.** Choose a real basis $e_1,\ldots,e_d$ of $E$, with finite measurable integrable representatives; nonemptiness of $P_E$ ensures $d\ge1$. For $c\in\mathbb R^d$ set $Jc=\sum_jc_je_j$. On the compact coordinate sphere $\|c\|_\infty=1$, the continuous function $c\mapsto\|Jc\|_1$ has a strictly positive minimum: a zero minimum would give a nonzero coordinate vector representing zero in $E$, contrary to linear independence. Homogeneity therefore gives a constant $A<\infty$ with

$$
\|c\|_\infty\le A\|Jc\|_1,
\qquad
|Jc(\theta)|\le\|c\|_\infty w(\theta),
\qquad
w=\sum_{j=1}^d|e_j|,\quad \int w\,d\sigma<\infty.
\tag{64.6}
$$

The elementary upper bound $\|Jc\|_1\le\sum_j|c_j|\|e_j\|_1$ and (64.6) show that the coordinate and $L^1$ norms are equivalent. Thus $E$ is complete and separable, and closed in the surrounding $L^1$ space. Nonnegativity and integral one are closed conditions, so $P_E$ is complete and separable in $d_E$. Every initial fiber (64.2) is closed, because TV distance to each fixed original target is continuous in this metric. The metric stabilization and clopen selection portions of Theorem 54.2 consequently apply: they use countability of $Q$, a countable basis in the range, closed values and completeness. The domain retains its countable clopen prefix basis. Under (64.3) they supply a TV-continuous selection $g_q\in K_{\infty,E}^{\eta}(q)\subseteq K_{0,E}^{\eta}(q)$. This invokes those proved portions only, rather than their countable-tape acquisition step.

We now prove the order assertion, for any TV-continuous $P_E$-valued selection. Write $g_q=\sum_j c_j(q)e_j$ using the same representatives. Since $Q$ is countable, remove one measurable $\sigma$-null set so that all these densities are nonnegative and finite simultaneously. On that null set set all basis representatives, and therefore all $g_q$ and $w$, to zero. This changes no density measure. Equation (64.6) makes every coefficient $c_j(q)$ continuous. For fixed $q$ and $\delta>0$, choose an actual prefix neighborhood such that

$$
\max_j|c_j(q')-c_j(q)|<\delta
\qquad(q'\in U_m(q)).
\tag{64.7}
$$

The same envelope then controls all its densities pointwise, simultaneously:

$$
\inf_{q'\in U_m(q)}g_{q'}
 \ge (g_q-\delta w)_+,
\qquad
\int\inf_{q'\in U_m(q)}g_{q'}\,d\sigma
 \ge\int g_q\,d\sigma-\delta\int w\,d\sigma
 =1-\delta\int w\,d\sigma.
\tag{64.8}
$$

The infimum is measurable because $Q$ is countable. It defines the greatest common submeasure of all the selected laws in the cylinder, by the same countable-density comparison used in Theorem 46.4. Refining a cylinder increases its infimum; since the cylinder includes $q$, these densities are bounded above by $g_q$, and their masses are at most one. Arbitrary $\delta>0$ in (64.8) proves increasing convergence of their masses to one. This is the pointwise order estimate missing from a general $L^1$-continuous selection: finite-dimensional coordinate continuity gives a single integrable bound for every neighbor in a sufficiently small actual cylinder.

To check the original-tape correspondence, apply the positive-increment realization of Theorem 46.4 to these selected laws. More explicitly, for each occupied prefix node $C$, with parent $C^-$, set $\Delta_C=\ell_C-\ell_{C^-}$, and use $\Delta_X=\ell_X$ at depth zero. Cylinder monotonicity makes each increment a positive measure on the original $(\Theta,\mathcal F)$, of mass $a_C-a_{C^-}$, where $a_C=\ell_C(\Theta)$. Give its coordinate $W_C$ the normalized probability law $\Delta_C/(a_C-a_{C^-})$ when this mass is positive, and a fixed original tape law $\delta_{\theta_0}$ when it is zero. There are countably many nodes. Their probability coordinates and an independent $U$ uniform on $(0,1)$ form one common product seed, fixed for every source. No standard-Borel or measurable-singleton hypothesis on the tape carrier is needed for this product or the point evaluation $\delta_{\theta_0}$.

The shared rules and thresholds are exactly the existing realization: at the reached node $C$, hand over $W_C$ when $U<a_C$, and otherwise query the next actual prime. At a non-root node the reached seed already satisfies $U\ge a_{C^-}$, so for every original measurable tape event $A$ the unconditional output measure at that node is

$$
\mathsf P\{a_{C^-}\le U<a_C,\ W_C\in A\}
   =\Delta_C(A).
\tag{64.9}
$$

The root uses lower threshold zero. The accumulated measures telescope along source $x$ to $\ell_{C_m(x)}\le g_{[x]}\sigma$. By (64.8) the probability of no handoff through depth $m$ is $1-a_{C_m(x)}\to0$. Thus the actual handoff is finite almost surely at every source, and its output measure is precisely $g_{[x]}\sigma$, not a conditional version of that law. Finite-record and output-event preimages are measurable interval and coordinate events or countable unions of them. Each reached depth uses finitely many actual prime queries and the fixed tables. The handoff supplies only the original tape, after which the same consumer runs on the same static source. Membership in (64.2) proves the cap against every original target. This is the supplier correspondence for Theorem 46.4, with no new acquisition algorithm. $\square$

Conversely, if an all-source lawful cap preparation has all its laws in $P_E$, Lemma 45.3 makes its density map a TV-continuous selection of (64.2), and the survival argument (54.8) puts it in every refinement stage. Thus (64.3) characterizes feasibility within this fixed density space. It is only a sufficient certificate for unrestricted feasibility: emptiness of a restricted stable fiber excludes $E$-valued preparations and says nothing by itself about other original-tape preparations.

In particular set $\eta$ equal to the independently defined original $R_\mu$ of (50.1), whose centers range over all original-tape probabilities. If (64.3) holds at this value, the theorem and the lower bound in Theorem 50.2 prove attainment of that original sharp value. No equality between an $E$-restricted radius and $R_\mu$ is asserted. Nonemptiness of $P_E$ does not imply nonempty initial or stable cap fibers, either at the endpoint or at another cap. Targets outside $E$ still occur in every required original target ball.

The norm and product ingredients are established mathematics; finite-dimensional completeness and closedness are also recorded as `FiniteDimensional.complete` and `Submodule.closed_of_finiteDimensional` in [pinned Mathlib, Normed/Module/FiniteDimension](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Module/FiniteDimension.lean), while the common product is the `Measure.infinitePi` interface already cited in Theorem 46.4. The basis argument and (64.8) supply their ordinary mathematical application to order exhaustion here. No compactness-only transfer, common finite tape support, common finite horizon, effective refinement test or real-sampling procedure follows. This certificate can be posed with nonatomic $\mathcal G$ and a proper finite-dimensional $E$; its all-source cap hypothesis remains an explicit additional obligation, rather than an automatic supplier.

## 65. Finite TV covers of positive-proposal target tails

**Definition 65.1 (A target-tail finite-cover radius).** Use the original consumer events $H_y,F_y$ of (40.1), original target probabilities $h_y,e_y$, and the occupied high-target tail $D=D(C,K)$ of (61.2). This tail is nonempty. Put

$$
a=\inf_{y\in D}h_y,\qquad b=\sup_{y\in D}e_y,
\qquad
\chi_{\mathrm{TV}}(D)=
\inf_{\substack{n\ge1\\\nu_1,\ldots,\nu_n\in\mathcal P(\Theta,\mathcal F)}}
 \sup_{y\in D}\min_{1\le j\le n}\operatorname{TV}(\mu_y,\nu_j).
\tag{65.1}
$$

Here $b$ is a scalar false-proposal bound on this tail, distinct from the prescribed profile function in (44.2). The centers are arbitrary probability measures on the entire original tape sigma algebra. They need not be targets, lie in $P_{\mathcal G}$, satisfy a row, or be lawfully acquired. The infimum concerns finite covers of the original targets, rather than the local single-center radii in (50.1).

**Theorem 65.2 (Persistent-source finite-cover obstruction).** For any finite family of such centers and any $\delta\ge0$ satisfying

$$
\min_j\operatorname{TV}(\mu_y,\nu_j)\le\delta
\qquad(y\in D),
\tag{65.2}
$$

one has

$$
a\le b+2\delta,
\qquad
\chi_{\mathrm{TV}}(D)\ge\frac{(a-b)_+}{2}.
\tag{65.3}
$$

In particular $a>b$ prevents TV total boundedness and relative TV compactness of this target tail on any measurable tape carrier.

**Proof.** Assign each $y\in D$ the least index $j$ for which (65.2) holds, and give every source outside $D$ color zero. This is a finite coloring $c:X\to\{0,1,\ldots,n\}$. It is only a proof object; neither the consumer nor any preparation is given this color. Apply [Boundaries, Theorem 37.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#37-finite-valued-advice-and-persistent-obstruction-to-adaptive-upper-calibration) to this finite partition and the occupied finite probe cylinder $C$. It gives one actual $x\in C$ with $\Omega(x)>K$ which is persistent for $c$: in every finite further probe menu, sources with the same answers and color as $x$ have unbounded $\Omega$. Thus $x\in D$ and $c(x)=j\ge1$. Every same-color comparison source $y$ belongs to $D$ and obeys

$$
\operatorname{TV}(\mu_x,\mu_y)
\le\operatorname{TV}(\mu_x,\nu_j)+\operatorname{TV}(\nu_j,\mu_y)
\le2\delta.
\tag{65.4}
$$

This use of Theorem 37.2 is its finite-color persistence conclusion, not an alteration of the supplied zero advice.

Let $A_m(x)\subseteq\Theta$ be the original consumer's measurable event of a finite proposal within $m$ transitions, querying only primes in $P_m$, with terminal real proposal at most $m$. These events increase to $H_x$: each actual finite proposal has a finite execution length, a finite prime menu and a finite real value. Hence

$$
\mu_x(A_m(x))\uparrow h_x.
\tag{65.5}
$$

For each $m$ large enough to include the prefix defining $C$ and the threshold $K$, persistence at this same $x$ supplies an actual $y_m$ of color $j$, agreeing with $x$ on $P_m$, with $\Omega(y_m)>m$. This is one source for the whole event $A_m(x)$, selected before quantifying over its tapes. For each tape in that event, deterministic finite-record replay on the matching actual prime answers preserves every consumer transition and its final real proposal. The proposal is at most $m<\Omega(y_m)$ and is therefore false at $y_m$. Consequently $A_m(x)\subseteq F_{y_m}$ and event-TV gives

$$
\mu_x(A_m(x))
 \le\mu_{y_m}(A_m(x))+2\delta
 \le e_{y_m}+2\delta
 \le b+2\delta.
\tag{65.6}
$$

Only continuity from below at the fixed original source $x$ is used in passing to the limit; no convergence of the comparison sources or their measures is assumed. Equations (65.5)--(65.6) yield $a\le h_x\le b+2\delta$. For any chosen finite centers their supremal covering error supplies a $\delta$ in (65.2), so taking the infimum over all finite center families proves the second bound in (65.3). If $a>b$, no finite cover of radius below $(a-b)/2$ exists, which excludes total boundedness and hence relative compactness. $\square$

For the all-source truthful positive row $h_y=h>0$, $e_y=0$, every occupied high-target tail has $a=h$, $b=0$, so its finite-cover radius is at least $h/2$. This is a restriction on the target laws themselves, including on countable carriers; it does not prohibit compact selected prepared-law ranges. Preparation can change the original consumer's row, as already required by the fixed-family contract. Section 61 remains the separate reused correct-mass bound on the unchanged acquisition value. Neither (65.3) nor failure of target precompactness determines cap attainment, identifies $\chi_{\mathrm{TV}}$ with $R_\mu$, or classifies general nonzero-error or divergence profiles.

The three results leave the general nonatomic endpoint problem open. A target-intrinsic necessary-and-sufficient order-exhaustion criterion, or an original-target-defined nonlinear supplier at the unchanged $R_\mu$, is still required beyond the stated subclasses. Necessity and endpoint nonemptiness of the finite-dimensional certificate are not established for unrestricted preparations. General positive-proposal, prescribed error/divergence and arbitrary-consumer endpoint classifications remain unresolved beyond the existing bounds and subclasses. Infimum, attained cap, exact acquisition, metric continuity and common-submeasure exhaustion remain separate, as do local and uniform conclusions and sourcewise finite and common finite stopping. The proofs use original-tape measures, the actual labeled prime-divisibility source and the stipulated measurable common rules; they supply no source probability, extra observation, source selection operation, reset, failure conditioning, effectiveness or resource guarantee. These are ordinary mathematical results with the cited classical inputs and no literature-priority or formal-verification assertion.

## 追加锚（本行以下为增补区）

## 66. A nonlinear common-order cap supplier on the original nonatomic tapes

**Definition 66.1 (Original-target common monotone rank).** Fix the entire labeled source, zero advice, common consumer, original nonempty measurable tape carrier $(\Theta,\mathcal F)$ and all original target laws exactly as in Definitions 50.1 and 59.1. As an additional input condition, designate one actual label $x_\circ$, put $\tau=\mu_{x_\circ}$, and specify a measurable map

$$
 t:\Theta\longrightarrow I=(0,1),\qquad t_*\tau=\lambda,
\tag{66.1}
$$

where $\lambda$ is Lebesgue probability. Require every original target to satisfy

$$
 \mu_y\ll\tau,\qquad
 \frac{d\mu_y}{d\tau}=f_y\circ t,\qquad
 f_y\ge0,\quad \int_I f_y\,d\lambda=1,
\tag{66.2}
$$

with a nondecreasing representative $f_y$. Thus $f_{x_\circ}=1$ almost everywhere. The anchor and rank are fixed from the original target input and measurable structure before varying the preparation; they are not chosen from an unknown prepared family. The rank is a function on tapes, not an observation of the source. This is an explicit subclass condition on the entire original family, and does not follow from countability of $X$, separability of a likelihood range or nonatomicity alone. All original labels remain, and equal complete prime signatures may still have different prescribed $f_y$. The full $\mathcal F$ need not be countably generated. A countable tape carrier cannot satisfy (66.1), since its rank image is countable whereas $\lambda$ gives every countable set mass zero.

Let $\mathcal M$ be the set of $L^1(\lambda)$ classes with a nonnegative nondecreasing representative and integral one. Choose their right-continuous representatives on $I$ when evaluating them pointwise. Such representatives are finite at every $u<1$: normalization and monotonicity give $g(u)\le(1-u)^{-1}$. Define

$$
 \iota(g)(A)=\int_A g(t(\theta))\,d\tau(\theta)
 \quad(A\in\mathcal F),\qquad
 d_{\mathcal M}(g,k)=\frac12\|g-k\|_1.
\tag{66.3}
$$

These are laws on the entire original $\mathcal F$, not laws only on the rank sigma algebra. Their event-TV distance is $d_{\mathcal M}(g,k)$ by (59.7) and $t_*\tau=\lambda$.

For $a\in L^1_+(\lambda)$, let $a^\uparrow$ be its increasing rearrangement: the quantile of the distribution of $a$ under $\lambda$, with the same right-continuous convention. Changes at the countably many quantile discontinuities do not change the density class. For a finite positive measure $\nu$ on the original tapes, write

$$
 \nu=h_\nu\tau+\nu_\perp,
 \qquad
 \mathsf E_\tau[h_\nu\mid\sigma(t)]=\bar h_\nu\circ t,
 \qquad
 a_\nu=\bar h_\nu+\nu_\perp(\Theta),
 \qquad
 \mathfrak R\nu=(a_\nu^\uparrow\circ t)\tau.
\tag{66.4}
$$

The conditional expectation is taken on tapes, and its $\sigma(t)$-measurable version factors through the real-valued rank. This factorization follows by measurable simple-function approximation; it uses no conditional sampling kernel or disintegration. Its class in $L^1(\lambda)$ is unique. Rearrangement depends only on that class, so $\mathfrak R$ is well-defined as a map on measures.

**Theorem 66.2 (Nonlinear lossless original-radius reduction).** Under Definition 66.1, $\mathfrak R$ preserves positive mass, is order-preserving and positively homogeneous, and its probability image is exactly $\iota(\mathcal M)$. It fixes every law in this image, including every original target. For any original-tape probabilities $v,w$,

$$
 \operatorname{TV}(\mathfrak Rv,\mathfrak Rw)
 \le\operatorname{TV}(v,w),\qquad
 \operatorname{TV}(\mathfrak Rv,\mu_y)
 \le\operatorname{TV}(v,\mu_y)\quad(y\in X).
\tag{66.5}
$$

For every occupied actual cylinder $C$,

$$
 \inf_{g\in\mathcal M}\sup_{y\in C}
       \operatorname{TV}(\iota(g),\mu_y)=\rho_\mu(C).
\tag{66.6}
$$

In particular the unchanged original sharp value is

$$
 R_\mu=\sup_{x\in X}\inf_{m\ge0}\inf_{g\in\mathcal M}
       \sup_{y\in C_m(x)}\operatorname{TV}(\iota(g),\mu_y).
\tag{66.7}
$$

The transfer is not additive, so it is outside the transfer class of Definition 63.1.

**Proof.** First consider the unsorted measure $P\nu=(a_\nu\circ t)\tau$. The conditional-expectation and singular-mass argument of Theorem 59.2 applies with reference $\tau$ and subalgebra $\sigma(t)$: these are a probability measure and a sub-sigma algebra, all targets have measurable densities there, and $P$ is positive, additive, homogeneous, mass-preserving and target-fixed. Conditional expectation exists by Radon--Nikodym on $(\Theta,\sigma(t),\tau|_{\sigma(t)})$, without regularity of the full tape space. For completeness, if $\rho$ is the greatest common submeasure of probabilities $v,w$, positivity gives $P\rho\le Pv,Pw$ and $P\rho(\Theta)=\rho(\Theta)$. Equation (59.7) then gives $\operatorname{TV}(Pv,Pw)\le1-\rho(\Theta)=\operatorname{TV}(v,w)$. Since the two output laws have densities $a_v\circ t,a_w\circ t$, this bounds $\frac12\|a_v-a_w\|_1$.

The classical rearrangement step has the following layer-cake proof for the nonnegative integrable functions needed here. For such an $a$, its distribution function $F_a(s)=\lambda\{a\le s\}$ increases to one as $s\to\infty$. Its quantile is therefore finite at every rank in $I$. The quantile definition and right continuity of $F_a$ give $\lambda\{a^\uparrow>s\}=1-F_a(s)=\lambda\{a>s\}$ for every $s\ge0$; changing the quantile at its countably many discontinuities preserves this identity. This proves the required equimeasurability even for unbounded $L^1$ densities. Write $A_s=\{u:a(u)>s\}$ and $B_s=\{u:b(u)>s\}$. Their rearranged superlevel sets are upper intervals $A_s^\uparrow,B_s^\uparrow$ with the same respective lengths, up to null sets. Consequently

$$
 \begin{aligned}
 \|a^\uparrow-b^\uparrow\|_1
 &=\int_0^\infty\lambda(A_s^\uparrow\mathbin\triangle B_s^\uparrow)\,ds\\
 &=\int_0^\infty|\lambda(A_s)-\lambda(B_s)|\,ds\\
 &\le\int_0^\infty\lambda(A_s\mathbin\triangle B_s)\,ds
 =\|a-b\|_1.
 \end{aligned}
\tag{66.8}
$$

Tonelli applies to the nonnegative indicator differences, and integrability makes the final expressions finite. In particular when $b=f_y$ its rearrangement is $f_y$ itself. This is the usual monotone-rearrangement contraction, not a new general rearrangement theorem. Chernozhukov, Fernandez-Val and Galichon, [*Improving Point and Interval Estimates of Monotone Functions by Rearrangement*, Proposition 1 and equation (2.1)](https://arxiv.org/html/0806.4730v3), [*Biometrika* **96** (2009), 559--575](https://doi.org/10.1093/biomet/asp030), state the bounded-function version and relate it to Lorentz's rearrangement inequality. Here (66.8) supplies the required nonnegative $L^1$ extension inside the original-source deduction; no statistical sampling assumption is used.

Equimeasurability preserves $\int a_\nu=\nu(\Theta)$. If $a\le b$ almost everywhere, then $\lambda\{a>s\}\le\lambda\{b>s\}$ for every $s$, so their quantiles satisfy $a^\uparrow\le b^\uparrow$ almost everywhere. Thus sorting preserves order, and scaling a nonnegative function scales its quantile. These facts prove the asserted order and homogeneity properties of $\mathfrak R$. Every $g\in\mathcal M$ is fixed by both $P$ and sorting; normalization identifies the probability image. Combining the $P$ contraction with (66.8) proves (66.5).

Applying (66.5) to each unrestricted center gives one inequality in (66.6); inclusion of $\iota(\mathcal M)$ in all original-tape probabilities gives the other. No cylinder center is assumed to attain its infimum. Taking the same $\sup_x\inf_m$ proves (66.7), without exchanging extrema. Finally the two probabilities with rank densities $2\mathbf1_{(0,1/2)}$ and $2\mathbf1_{(1/2,1)}$ both sort to $2\mathbf1_{(1/2,1)}$, whereas their average sorts to the constant density $1$. Hence $\mathfrak R$ does not preserve averages and is not additive. $\square$

**Theorem 66.3 (Simultaneous integrable lower envelopes and original-tape realization).** Under Definition 66.1, let $Q$ be exactly the actual signature space (50.2), and let $q\mapsto g_q\in\mathcal M$ be continuous in $d_{\mathcal M}$. For its canonical increasing representatives define

$$
 h_m^q(u)=\inf_{q'\in U_m(q)}g_{q'}(u),
 \qquad
 \ell_{C_m(q)}(A)=\int_A h_m^q(t(\theta))\,d\tau(\theta)
 \quad(A\in\mathcal F).
\tag{66.9}
$$

These are the greatest common submeasures of the selected original-tape laws in the indicated actual cylinders. Their masses increase to one at every actual $q$. More precisely, for every $q$, $0<\delta<1$ and $\epsilon>0$, any depth $m$ with

$$
 \|g_{q'}-g_q\|_1<\epsilon\quad(q'\in U_m(q))
\tag{66.10}
$$

gives the simultaneous lower bound

$$
 h_m^q(u)\ge e_{q,\delta,\epsilon}(u)
 :=\begin{cases}
       \left(g_q(u-\delta)-\frac\epsilon\delta\right)_+,&\delta<u<1,\\
       0,&0<u\le\delta.
    \end{cases}
\tag{66.11}
$$

The envelopes are measurable and integrable, with $0\le e_{q,\delta,\epsilon}\le g_q$. Along $\delta_n=2^{-n}$ and $\epsilon_n=\delta_n^2$, their masses increase to one. The depths that certify them are source-dependent. Thus the laws $\iota(g_{[y]})$ have an exact lawful preparation on the entire original carrier, using one source-independent common seed and actual finite-prime execution almost surely at every original source. No common integrable upper envelope of the whole selection is assumed.

**Proof.** For increasing densities $g,k$ and $u>\delta$, monotonicity gives, for almost every $v\in(u-\delta,u)$,

$$
 g(v)\ge g(u-\delta),\qquad k(v)\le k(u),\qquad
 \|g-k\|_1\ge\delta\bigl(g(u-\delta)-k(u)\bigr)_+.
\tag{66.12}
$$

Apply this to every $k=g_{q'}$ in (66.10). The same shifted density and the same error bound work for all these neighbors, proving (66.11). This is a simultaneous pointwise bound, rather than separate exceptional sets or separate optimizers for each neighbor.

With the displayed $\delta_n,\epsilon_n$, the lower envelopes are increasing in $n$: the shifted argument increases, the subtracted $\delta_n$ decreases and the indicator expands. They are bounded by $g_q$. At every continuity point of $g_q$ they converge to $g_q$, and an increasing finite function on $I$ has only countably many discontinuities. Dominated convergence under the single integrable density $g_q$ gives $\int_I e_{q,\delta_n,\epsilon_n}\,d\lambda\to1$. Continuity of the selection supplies a finite depth for each such tolerance; choose these depths increasing. Since $h_m^q$ increases with $m$ and is bounded above by $g_q$ because $q\in U_m(q)$, (66.11) proves

$$
 \int_I h_m^q\,d\lambda\uparrow1,
 \qquad
 h_m^q\uparrow g_q\quad\lambda\text{-almost everywhere}.
\tag{66.13}
$$

The infima in (66.9) are measurable because $Q$ is countable. Any positive measure dominated by all the selected laws in a cylinder is absolutely continuous with respect to $\tau$; its density is bounded by all their densities after one countable union of null sets, hence by their infimum. This proves greatestness on the entire $\mathcal F$, including for competing submeasure densities that do not factor through $t$. Countability of $Q$ also allows (66.13) to hold for every actual $q$ outside one common tape null set. The domination used for convergence is local to $q$ and does not introduce a uniform neighborhood size or a global upper bound.

Equations (66.9)--(66.13) discharge exactly the order-exhaustion hypothesis of Theorem 46.4, whose positive-increment realization is reused. To specify its correspondence, include the depth-zero occupied node $X$ and give it fictitious parent mass zero. At a node $C$ with parent $C^-$, set $\Delta_C=\ell_C-\ell_{C^-}$ and $a_C=\ell_C(\Theta)$; at the root use $\Delta_X=\ell_X$. These are positive measures on the original tapes. Preload, for each of the countably many nodes with positive increment mass, a coordinate $W_C$ with law $\Delta_C/(a_C-a_{C^-})$, and use a fixed original tape at zero-mass nodes. Take all these coordinates and an independent uniform $U\in(0,1)$ under one product probability measure, the same at every source.

At a reached node $C$, the common deterministic rule emits $W_C$ if $U<a_C$ and otherwise queries the next actual prime and follows its answer. Reaching a non-root node implies $U\ge a_{C^-}$, so its unconditional output submeasure is

$$
 \mathsf P\{a_{C^-}\le U<a_C,\ W_C\in A\}=\Delta_C(A)
 \quad(A\in\mathcal F).
\tag{66.14}
$$

Along each actual source, the output submeasures telescope to $\ell_{C_m(x)}$. By (66.13), the probability of no handoff through that finite depth is $1-a_{C_m(x)}\to0$, and the full output law is $\iota(g_{[x]})$. Finite record events and output preimages are measurable interval and coordinate events or countable unions of them. The original consumer receives only this original tape and then runs on the same static source. There is no source sampling, source label, target input, additional probe, reset or failure conditioning.

The product theorem used by Theorem 46.4 has arbitrary measurable probability spaces as coordinates; only countably many are needed here. Its cylinder formula is also the `Measure.infinitePi` result in [pinned Mathlib, Probability/ProductMeasure](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/ProductMeasure.lean). It provides the seed measure directly, and does not assert that these coordinate laws can be sampled effectively from a real uniform variable. No standard-Borel assumption, measurable-singleton assumption, disintegration or finite-description rule is needed. This construction supplies sourcewise almost-sure finite execution, not a common finite horizon or a bound on seed support. $\square$

**Definition 66.4 (Original-target common-order cap fibers).** Under Definition 66.1, for a cap $\eta\in[0,1]$ put

$$
 K_{0,\uparrow}^{\eta}(q)
 =\bigcap_{y\in X:\,[y]=q}
       \{g\in\mathcal M:d_{\mathcal M}(g,f_y)\le\eta\}.
\tag{66.15}
$$

Use exactly the distance-neighborhood refinement (54.4) and countable-ordinal intersections (54.5), with range $\mathcal M$, metric $d_{\mathcal M}$ and unchanged occupied neighborhoods $U_m(q)$. Denote the stable values by $K_{\infty,\uparrow}^{\eta}(q)$. These fibers are defined only by the fixed original targets, rank and actual occupied cylinders; they do not take a candidate prepared family as input. In particular all original labels with one signature occur in the intersection (66.15).

**Theorem 66.5 (Intrinsic lawful cap criterion in the common-order subclass).** The fibers of Definition 66.4 stabilize at a countable ordinal. The following are equivalent:

$$
 \begin{aligned}
 &\text{an original-tape lawful preparation has uniform error at most }\eta;\\
 &\text{such a preparation exists with every law in }\iota(\mathcal M);\\
 &K_{\infty,\uparrow}^{\eta}(q)\ne\varnothing
       \quad\text{for every actual }q\in Q.
 \end{aligned}
\tag{66.16}
$$

In particular attainment at the independently defined original $R_\mu$ is equivalent to nonemptiness of all the fibers at cap $R_\mu$. Cap zero is exact acquisition, not merely an infimum statement. Neither initial nor stable fiber nonemptiness is automatic from the rank hypothesis. The criterion does not require a global integrable upper envelope, finite-dimensional density space or compact set of laws.

**Proof.** The space $\mathcal M$ is closed in $L^1(\lambda)$. Indeed from an $L^1$-convergent sequence choose an almost-everywhere convergent subsequence. On a common full-measure subset of $I$ its limit is nonnegative and ordered in the argument. This set is dense; the ordered limit extends to an increasing function on $I$, agreeing with the original limit except possibly at its countably many jumps. Right-continuous modification gives the chosen representative. Integral one passes to the limit in $L^1$. Hence $\mathcal M$ is complete, and is separable as a subspace of separable $L^1(\lambda)$. Each initial fiber is closed because it is an intersection of closed metric balls in this space.

The metric stabilization and clopen selection portions of Theorem 54.2 therefore apply with their exact hypotheses: $Q$ is countable, its prefix neighborhoods form a countable clopen basis, the range is complete and separable, and the values are closed. Strict successor losses use distinct elements of $Q$ times a countable range basis, giving countable stabilization. Nonempty stable values are lower semicontinuous, and the disjoint-clopen-refinement construction (54.9)--(54.10) produces a continuous selection in a complete range. No countable-tape assumption is used in these portions, and their inverse cumulative sampling step is not invoked.

If a lawful preparation has laws $\lambda_y$ within cap $\eta$, Lemma 45.3 makes those laws factor through $Q$ as a TV-continuous map. Apply $\mathfrak R$ pointwise. Theorem 66.2 gives a continuous $\mathcal M$-valued map $g_q$ whose laws are within the same cap against every original $\mu_y$. Thus it selects (66.15). The survival induction (54.8), with its limit intersections, puts $g_q$ in every refinement stage, proving nonemptiness of every stable fiber. Theorem 66.3 additionally realizes this reduced family lawfully on the original tapes; this is the operational cap-preservation assertion, rather than an assumption that the nonlinear law map is itself a tape map.

Conversely, nonempty stable values supply a continuous selection $g_q\in K_{\infty,\uparrow}^{\eta}(q)\subseteq K_{0,\uparrow}^{\eta}(q)$. Theorem 66.3 supplies its exhausting common submeasures and lawful original-tape realization. Membership in (66.15) proves the cap at every original label. Inclusion of these preparations in all original-tape preparations proves the remaining implication in (66.16). Theorem 50.2 identifies the unrestricted acquisition infimum with $R_\mu$; (66.6)--(66.7) keep that original value and its quantifier order. At cap $R_\mu$, any feasible preparation therefore attains it.

This deduction concerns the explicit common-rank input subclass. For original families without such a target-specified rank and dominating anchor, the nonlinear selection/exhaustion question of Section 62 remains unresolved. In particular this criterion does not classify all positive-proposal rows, all prescribed profiles or arbitrary fixed-consumer endpoint constraints. It preserves any such conditions already imposed on the original target family, while imposing no matching profile condition on prepared laws. $\square$

**Proposition 66.6 (The target-mixture reference collapses a common monotone family).** Suppose instead that the reference in (66.1)--(66.2) is the positive target mixture $\sigma=\sum_i w_i\mu_{x_i}$, where $w_i>0$ and $\sum_iw_i=1$. If $t_*\sigma=\lambda$ and every $d\mu_{x_i}/d\sigma=f_i\circ t$ has one common nondecreasing rank, then every original target equals $\sigma$.

**Proof.** Radon--Nikodym uniqueness gives $\sum_iw_i f_i=1$ almost everywhere on $I$. Choose a common full-measure set where this equality holds and all $f_i$ have their increasing representatives. For $s<u$ in that set, each $f_i(u)-f_i(s)$ is nonnegative. The positively weighted sum of these differences is zero, because both sums equal one. Thus every difference is zero. Each $f_i$ is constant almost everywhere, and normalization makes that constant one. Therefore $\mu_{x_i}=\sigma$ for all $i$. This proves that the mixture in Section 59 cannot supply the common rank for a nonconstant family by itself; the anchor-reference condition in Definition 66.1 is a substantive restriction. $\square$

**Proposition 66.7 (Nonatomic infinite-dimensional full-source positive-profile input).** There is a full original-source family in Definition 66.1 with nonatomic likelihood information, infinite-dimensional target-density span, positive proposal probability at every source and an attained positive original value. Fix $0<c<1$, let $\Theta=I$ with its Borel sigma algebra, $\tau=\lambda$ and $t(u)=u$, and prescribe

$$
 \mu_y=f_{\Omega(y)}\lambda,\qquad
 f_k(u)=c+(1-c)k u^{k-1}\quad(k\ge1).
\tag{66.17}
$$

Fix the consumer that immediately proposes $\lfloor(1-u)^{-1}\rfloor$. Every original label is assigned its displayed target law. The target rows satisfy

$$
 h_y=1,\qquad d_y=z_y=0,\qquad
 e_y=c(1-1/k)+(1-c)(1-1/k)^k
 \quad(k=\Omega(y)),
\tag{66.18}
$$

so the allowed constant profile $b(k)=c+(1-c)\exp(-1)<1$ holds. Every occupied cylinder has $\rho_\mu(C)=1-c$, and $R_\mu=1-c$ is attained by handing over a common $\lambda$ tape without querying the source.

**Proof.** All $f_k$ are nonnegative, increasing and normalized. The actual anchor $x_*=(7,2)$ has $\Omega(x_*)=1$, so $f_1=1$ and $\mu_{x_*}=\tau$ as required. The common consumer is a measurable finite real-output rule on every tape in $I$, has no source input and terminates in one transition. Its false event at target $k$ is $u<1-1/k$. Integrating (66.17) over this event gives (66.18). The inequality $(1-1/k)^k\le\exp(-1)$, with the zero value at $k=1$, proves the profile bound. These are target laws and consumer events, not a target-dependent execution rule.

Every occupied actual cylinder contains sources whose $k=\Omega(y)$ tend to infinity, by the exact finite prime-pattern theorem 35.2. For $A_a=(1-a,1)$, $0<a<1$, these targets satisfy

$$
 \mu_y(A_a)=ca+(1-c)\bigl(1-(1-a)^k\bigr)
 \longrightarrow ca+1-c.
\tag{66.19}
$$

For any original-tape probability center $v$, the event discrepancy therefore gives $\sup_{y\in C}\operatorname{TV}(v,\mu_y)\ge ca+1-c-v(A_a)$. Since $A_a\downarrow\varnothing$ as $a\downarrow0$ on the declared open carrier $I$, continuity from above gives $v(A_a)\to0$. Hence every cylinder radius is at least $1-c$. Conversely $\operatorname{TV}(\lambda,\mu_y)=(1-c)\operatorname{TV}(\lambda,k u^{k-1}\lambda)\le1-c$ for every source. This proves the asserted local radii, unchanged original value and zero-query attainment. The constant seed law is fixed independently of the source and the consumer remains unchanged.

Unboundedly many actual $k$ give polynomials of arbitrarily large distinct degrees $k-1$; comparing highest degrees in each finite linear relation proves that their density span is infinite-dimensional. No claim that every positive integer $k$ is attained is needed. To verify that this is also nonatomic likelihood information in the sense of Section 59, form its positive target mixture $\sigma=s\lambda$. The anchor term gives $s\ge w_*>0$ almost everywhere, and integrability makes $s$ finite almost everywhere. Its likelihood densities include $1/s$ and $f_k/s$ for some actual $k>1$. Their ratio recovers the strictly increasing function $f_k(u)$, whose measurable inverse recovers $u$. Thus the likelihood sigma algebra is the full Borel sigma algebra modulo null sets; conversely every density is Borel. The equivalent probability $\sigma$ is nonatomic, so this family lies outside the atomic subclass of Section 60. The target-density span is infinite-dimensional, although Section 64 can also certify this example's constant optimum using the one-dimensional space $E=\operatorname{span}\{1/s\}$ in its $\sigma$-density coordinates. The example establishes nonvacuity of the common-rank input, not failure of that separate finite-dimensional certificate. It witnesses one allowed nonzero-error positive profile, without classifying other original profiles or rows. $\square$

**Proposition 66.8 (A positive cap need not have an integrable upper envelope).** Even for the full-source family $\mu_y=\tau=\lambda$ on $I$, with the always-unknown consumer and identity rank, every positive cap $\eta$ has an initial fiber (66.15) whose canonical densities have a nonintegrable pointwise supremum. Thus integrability of the supremum of all initial cap-fiber densities is not a necessary condition for lawful cap feasibility, and is not a consequence of Definition 66.1.

**Proof.** Choose $0<d\le\eta$ with $d<1$. For every integer $n\ge2$, the increasing normalized density

$$
 g_n(u)=1-d+dn\mathbf1_{[1-1/n,1)}(u)
\tag{66.20}
$$

has $\operatorname{TV}(g_n\lambda,\lambda)=d(1-1/n)\le\eta$. Since all original targets are $\lambda$, every $g_n$ belongs to every initial fiber. For $u$ sufficiently close to one choose $n=\lfloor(1-u)^{-1}\rfloor\ge2$. Then $u\ge1-1/n$ and $n\ge[2(1-u)]^{-1}$, so $\sup_n g_n(u)\ge d/[2(1-u)]$. The pointwise supremum of all the fiber densities is measurable because it is nondecreasing, and its integral is infinite. Nevertheless the constant law $\lambda$ is an exact zero-query preparation of this full-source input. The integrable envelopes of Theorem 66.3 are simultaneous lower bounds in sourcewise shrinking cylinders, bounded by the density at that source; they do not assert this stronger upper domination. $\square$

## 追加锚（本行以下为增补区）

## 67. Original-target proportional containment and unavoidable nonatomic ranges

This section keeps the full labeled source (44.1), the zero advice, the original consumer and measurable tape carrier, and every original target law fixed before varying preparation. The sharp value is still

$$
R_\mu=\sup_{x\in X}\inf_{m\ge0}\inf_{v\in\mathcal P(\Theta,\mathcal F)}
             \sup_{y\in C_m(x)}\operatorname{TV}(v,\mu_y),
\tag{67.1}
$$

with event-supremum TV. Theorem 50.2 supplies its equality with the lawful acquisition infimum. The first result characterizes the stronger proportional-containment contract, rather than replacing ordinary TV optimization. The second result supplies a genuinely nonatomic attained input whose every lawful sharp-cap range escapes every fixed finite-dimensional space.

**Definition 67.1 (Original-target common-mass coefficient).** Enumerate every actual label as $x_1,x_2,\ldots$, use the positive tape mixture $\sigma=\sum_i2^{-i}\mu_{x_i}$, and choose measurable nonnegative densities $f_y=d\mu_y/d\sigma$. For every occupied prime-prefix cylinder $C$, including the root $X$, put

$$
b_C(\theta)=\inf_{y\in C}f_y(\theta),\qquad
\ell_C=b_C\sigma,\qquad a_C=\ell_C(\Theta).
\tag{67.2}
$$

Here $b_C$ is a density, not the prescribed error profile. Countability of $X$ makes the infimum measurable. The finite-measure Radon--Nikodym argument of Theorem 46.4 makes $\ell_C$ the greatest finite positive measure dominated by every original $\mu_y$ in $C$; its definition as a measure is independent of the mixture enumeration and density versions. If $C'\subseteq C$ then $\ell_{C'}\ge\ell_C$. Define

$$
A(x)=\sup_{m\ge0}a_{C_m(x)},\qquad
\kappa=\inf_{x\in X}A(x)\in[0,1].
\tag{67.3}
$$

A coefficient $c\in[0,1]$ is lawfully proportionally feasible if one lawful preparation, with probability output laws $\lambda_y$ on the entire original $\mathcal F$, satisfies

$$
c\lambda_y\le\mu_y\qquad(y\in X).
\tag{67.4}
$$

Every label occurs in (67.2) and (67.4), including labels with equal signatures and different original laws. The mixture is a measure on tapes, not a distribution or sampling rule on sources.

**Theorem 67.2 (Maximal lawful proportional containment, including its positive endpoint).** For $0<c\le1$, (67.4) is lawfully feasible if and only if $\kappa\ge c$. The set of feasible coefficients in $[0,1]$ is exactly $[0,\kappa]$, and its largest coefficient is attained. When $\kappa=0$ this last assertion is the vacuous zero contract, not a positive containment or a TV-cap conclusion. The criterion is target-only: its inputs are the original measures, their measurable structure and the occupied actual cylinders.

**Proof.** Necessity uses the whole-event finite-record submeasure of Lemma 45.3. If preparation has laws $\lambda_y$, its measure $\rho_{x,m}$ is dominated by every $\lambda_y$ with $y\in C_m(x)$ and has mass increasing to one. Equation (67.4) therefore gives $c\rho_{x,m}\le\mu_y$ for all those labels simultaneously. Greatestness in (67.2) yields

$$
c\rho_{x,m}\le\ell_{C_m(x)},\qquad
c\,\mathsf P(E_m(x))\le a_{C_m(x)}.
\tag{67.5}
$$

Taking the increasing limit of masses gives $A(x)\ge c$ at every actual $x$, and hence $\kappa\ge c$.

For sufficiency fix $0<c\le\kappa$. Give the root a fictitious parent with measure and mass zero. For every occupied node $C$, with parent $C^-$, define

$$
\begin{aligned}
\Delta_C&=\ell_C-\ell_{C^-},&
d_C&=a_C-a_{C^-}\ge0,\\
q_C&=\min(c,a_C)-\min(c,a_{C^-}),&
t_C&=\begin{cases}q_C/d_C,&d_C>0,\\0,&d_C=0.\end{cases}
\end{aligned}
\tag{67.6}
$$

For the root use $\Delta_X=\ell_X$ and $d_X=a_X$. The map $a\mapsto\min(c,a)$ is increasing and has slope at most one, so $0\le q_C\le d_C$ and $0\le t_C\le1$. A zero-mass positive $\Delta_C$ is the zero measure. Along the finite ancestor chain, including the root, put

$$
H_C=\frac1c\sum_{D\preceq C}t_D\Delta_D.
\tag{67.7}
$$

These are positive finite measures increasing along branches, and telescoping gives

$$
H_C(\Theta)=\frac{\min(c,a_C)}c,\qquad
cH_C\le\sum_{D\preceq C}\Delta_D=\ell_C.
\tag{67.8}
$$

For an actual signature $q=[x]$, the increasing measures $H_{C_m(x)}$ have masses tending to one, because $a_{C_m(x)}\uparrow A(x)\ge c$. Their limit defines a probability $\lambda_q$ on the entire original carrier. For example its density is the monotone limit of the densities in (67.7), and monotone convergence proves countable additivity and integral one. Every $y$ with this signature lies in every one of these cylinders, so (67.8) gives $c\lambda_q\le\mu_y$. This proves simultaneous domination for every equal-signature label; it requires no assumption that the original targets factor through signatures.

The following common-seed realization identifies this limiting law with actual finite execution. For each of the countably many nodes with $d_C>0$, take an original-tape coordinate $W_C$ of normalized law $\Delta_C/d_C$. At $d_C=0$ take the point-evaluation law at one fixed tape $\theta_0$; measurable singleton sets are unnecessary for this probability measure. Include these coordinates and an independent uniform $U\in(0,1)$ under one product probability law. Let

$$
B_C=\frac{\min(c,a_C)}c.
\tag{67.9}
$$

At a reached node $C$, the common deterministic rule hands over $W_C$ when $U<B_C$; otherwise it queries the next actual prime and follows its answer. Reaching a nonroot node entails $U\ge B_{C^-}$, since the thresholds are increasing along its branch. For $d_C>0$ and any $F\in\mathcal F$, its unconditional output submeasure is

$$
\mathsf P\{B_{C^-}\le U<B_C,\ W_C\in F\}
=\frac{q_C}{c}\frac{\Delta_C(F)}{d_C}
=\frac{t_C\Delta_C(F)}c.
\tag{67.10}
$$

The root has lower threshold zero. Zero increments contribute no probability and require no normalization by zero. Summing along the actual branch through depth $m$ gives precisely $H_{C_m(x)}$. At every fixed actual source $B_{C_m(x)}\uparrow1$. Every $U<1$ consequently crosses a threshold at a finite depth, even if $a_{C_m(x)}\uparrow c$ without ever reaching $c$. Thus actual preparation is finite almost surely at every source, and its complete output measure is $\lambda_{[x]}$.

Finite-record events are measurable interval events in $U$, with measurable coordinate events when output is specified. For each original $F$, the handoff preimage is the countable union of the events in (67.10), hence measurable. The probability product has only countably many coordinate probability spaces and uses their product sigma algebra. The rule reads only the acquired prefix; the original consumer receives only the original tape and runs on the same static source. No conditioning, discarded failures, source selection or reset is involved.

There is also an explicit exhaustion correspondence. For $y\in C$, its limiting $\lambda_{[y]}$ includes $H_C$, so $H_C$ is a common submeasure of all these selected laws. Along each actual branch its mass increases to one by (67.8). Their greatest common submeasures therefore exhaust one, exactly the hypothesis of Theorem 46.4. This is an order statement, stronger than metric continuity alone.

For $c=0$, hand $\theta_0$ over in one transition with a unit seed. Then $0\lambda_y=0\le\mu_y$ at every label without positive division. Necessity for positive coefficients and the construction at every $0<c\le\kappa$ prove the asserted interval and its endpoint, including the separate case $\kappa=0$. The specialization $c=1$ is the already published exact-acquisition criterion 46.4, reused rather than a new exactness theorem. $\square$

**Corollary 67.3 (Sufficient test at the unchanged sharp TV value).** One always has

$$
R_\mu\le1-\kappa.
\tag{67.11}
$$

If $R_\mu<1$ and $\kappa\ge1-R_\mu$, a lawful preparation attains the original $R_\mu$. In this sufficient-test case $\kappa=1-R_\mu$. At $R_\mu=0$ the test is the reused exact-acquisition condition $\kappa=1$; at $R_\mu=1$ attainment is already Theorem 50.2 and the coefficient-zero condition supplies no additional information.

**Proof.** If $0<c<1$ and $c\lambda_y\le\mu_y$, the finite measure $\mu_y-c\lambda_y$ is nonnegative and has mass $1-c$. Thus

$$
\xi_y=\frac{\mu_y-c\lambda_y}{1-c}\in\mathcal P(\Theta,\mathcal F),\qquad
\operatorname{TV}(\lambda_y,\mu_y)
=(1-c)\operatorname{TV}(\lambda_y,\xi_y)\le1-c.
\tag{67.12}
$$

At $c=1$ domination of two probabilities forces equality. If $\kappa>0$, use Theorem 67.2 at $c=\kappa$ to prove (67.11); if $\kappa=0$, it is just the bound $R_\mu\le1$. For $R_\mu<1$ take the positive coefficient $c=1-R_\mu$. The prepared cap in (67.12) is at most $R_\mu$, and the independent original lower bound $I(\mu)=R_\mu$ forces its uniform error to equal $R_\mu$. Combining (67.11) with the test gives the stated equality of scalars. No infimum over sources is interchanged with a branch limit. $\square$

**Proposition 67.4 (The sufficient test is strictly nonnecessary).** Reuse, without changing or reconstructing it, the attained family of Theorem 57.2. With its published parameters,

$$
\beta=\frac r{1-1/k},\qquad \alpha=1-\beta,\qquad
R_\mu=r,\qquad 0<h\le r<1-1/k.
$$

Every occupied cylinder contains every tag color and sources of arbitrarily large $\Omega$, by its retained coloring property (56.4). The common original-target submeasure is exactly $\alpha\delta_o$: another color gives each tag zero mass, and an actual sufficiently high target gives each fixed proposal tape zero mass. All targets have the same base restriction $\alpha\delta_o$. Therefore

$$
a_C=\alpha\quad(C\text{ occupied}),\qquad
\kappa=\alpha,\qquad 1-\kappa=\beta>r=R_\mu.
\tag{67.13}
$$

The lawful attainer in Theorem 57.2 still exists. In contrast, Theorem 67.2 excludes proportional containment at coefficient $1-r$, since $1-r>\alpha$. This diagnoses strict nonnecessity even in the retained all-source truthful positive-row class, under every allowed profile. It is a calculation on the published example, not a new example or a classification of unrestricted TV caps.

**Theorem 67.5 (Attained nonatomic truthful row with no totally bounded sharp-cap prepared range).** For every $h\in(0,1)$ and every allowed profile $b$, there is one fixed full-original-source problem with all target probabilities nonatomic and row

$$
(h_y,e_y,d_y,z_y)=(h,0,0,1-h)\qquad(y\in X),
\tag{67.14}
$$

with a positive-mass nonatomic likelihood part, $\kappa=1-h$, and original $R_\mu=h$ attained. Nevertheless every lawful family $(\lambda_y)$ satisfying $\sup_y\operatorname{TV}(\lambda_y,\mu_y)\le h$ has a range that is not TV totally bounded. No such family is contained in any fixed finite-dimensional real space of finite signed measures, in particular no density space $E$ of Section 64.

**Proof.** This is an explicitly specified input subclass, on every actual source, not a restriction on the prepared laws. Write $q_i(y)=\mathbf1_{p_i\mid N(y)}$ and define from the original target specification

$$
n(y)=\min\{i:q_i(y)=0\},\qquad
t(y)=\sum_{i\ge1}3^{-i}q_i(y)\in[0,1/2].
\tag{67.15}
$$

Every actual integer $N(y)$ has finite prime support, so $n(y)$ is finite. Use the disjoint-union standard Borel carrier of copies of $I=(0,1)$,

$$
\Theta=\bigsqcup_{n\ge1}B_n\ \sqcup\ \bigsqcup_{j\ge1}P_j,
\tag{67.16}
$$

with its disjoint-union Borel sigma algebra. Component labels are part of a declared tape, not source observations. Let $\pi_j$ be Lebesgue probability on $P_j$. For $t\in[0,1/2]$ put

$$
Z_t=\int_0^1e^{tu}\,du,\qquad
k_t(s)=\frac{e^{ts}}{Z_t}\quad(s\in I).
\tag{67.17}
$$

Let $\nu_y$ be the probability supported on $B_{n(y)}$ with density $k_{t(y)}$ there, and prescribe the entire family

$$
\mu_y=(1-h)\nu_y+h\pi_{\Omega(y)}.
\tag{67.18}
$$

Fix the common consumer to return unknown immediately on $B_n$ and to propose the finite integer $j$ immediately on $P_j$. It uses no prime queries. Every record and every Borel restriction on the output is measurable: its actions depend only on the countable measurable component partition. Every tape terminates, so $d_y=0$. Under (67.18) proposal probability is $h$, every proposal is the correct $\Omega(y)$, and unknown probability is $1-h$. Thus (67.14) satisfies every specified allowed $b$, including $b\equiv0$. Both target components have densities on diffuse interval measures, so every target probability is nonatomic. Equal complete signatures have equal $n,t,\Omega$ in this particular input, but all original labels are still assigned their displayed laws. The quantities $n(y)$ and $t(y)$ are part of the fixed target-law specification; the preparation receives neither them, $\Omega(y)$ nor any source label, and uses only finite observed prime answers.

For each $n$, the set $D_n=\{y:n(y)=n\}$ is the occupied prefix cylinder with its first $n-1$ answers positive and its $n$th answer negative. Theorem 35.2 proves its occupation and unbounded $\Omega$ in it and in every occupied further cylinder. Fix $x$ and $m\ge n(x)$. On $C_m(x)$ the component $B_{n(x)}$ is fixed, and

$$
|t(y)-t(x)|\le\sum_{i>m}3^{-i}
=\tfrac12\,3^{-m}=:\delta_m
\qquad(y\in C_m(x)).
\tag{67.19}
$$

For any $t,t'$ with $|t-t'|\le\delta$, their exponentials and their integrals satisfy $e^{-\delta}\le e^{t's}/e^{ts}\le e^\delta$ and $e^{-\delta}\le Z_{t'}/Z_t\le e^\delta$. Hence

$$
k_{t'}(s)\ge e^{-2\delta}k_t(s)\qquad(s\in I).
\tag{67.20}
$$

In any occupied cylinder, a source with $\Omega>j$ makes its target mass on $P_j$ zero. Every common submeasure therefore gives each $P_j$ zero mass and gives their countable union zero mass. At the fixed $x,m$, all targets are supported on $B_{n(x)}$ and their proposal component, so greatestness and (67.20) give

$$
(1-h)e^{-2\delta_m}\nu_x
\le\ell_{C_m(x)}
\le(1-h)\nu_x.
\tag{67.21}
$$

Every cylinder common mass is at most $1-h$, and (67.21) shows that along each actual branch it tends to $1-h$. Thus $\kappa=1-h$. Theorem 67.2 at $c=1-h$ supplies a lawful family within cap $h$. More specifically, all branch masses satisfy $a_C\le c$, so the positive clipping coefficients of (67.6) equal one. Equation (67.21) makes the limiting output law in (67.7) exactly $\nu_x$. Its error is $h$, because the signed difference $\nu_x-\mu_x=h(\nu_x-\pi_{\Omega(x)})$ has disjoint positive and negative components. This invokes the already verified common-seed realization; preparation does not read or compute the infinite parameter $t(x)$ as an extra input.

The original sharp expression can also be checked directly. In any occupied cylinder choose actual sources with distinct $\Omega$ tending to infinity. For any probability center $v$ on the original tapes, disjointness gives $v(P_{\Omega(y)})\to0$ along these sources. The target mass on that event is $h$, so the cylinder radius is at least $h$. At each $x$, the center $\nu_x$ and (67.19)--(67.20) give

$$
\sup_{y\in C_m(x)}\operatorname{TV}(\nu_x,\mu_y)
\le h+(1-h)\sup_{y\in C_m(x)}
                     \operatorname{TV}(\nu_x,\nu_y)\longrightarrow h.
\tag{67.22}
$$

For example the density ratio bounds imply the supremal density $L^1$ difference is at most $e^{2\delta_m}-1$. Taking the unchanged $\inf_m$ at each actual $x$ and then $\sup_x$ proves $R_\mu=h$. This agrees with, and reuses, the all-source truthful-row lower bound of Theorem 61.3.

To check likelihood information, form the positive original-target mixture $\sigma$ and its generated likelihood sigma algebra $\mathcal G$ of Section 59. For each $n$, select actual $y,z\in D_n$ with $\Omega(y)\ne\Omega(z)$, using unboundedness in that occupied cylinder. Their complete signatures are different. If the first differing bit is $i$, its contribution $3^{-i}$ exceeds the tail sum $\frac12\,3^{-i}$, so $t(y)\ne t(z)$. Each target has strictly positive density on its one $B_n$ piece and its one $P_{\Omega}$ piece. Modulo $\sigma$-null sets,

$$
\{f_y>0\}\cap\{f_z>0\}=B_n.
\tag{67.23}
$$

Thus $B_n$ is likelihood measurable modulo null sets. On it, the two likelihood densities have ratio

$$
\frac{f_y(s)}{f_z(s)}
=\frac{Z_{t(z)}}{Z_{t(y)}}e^{(t(y)-t(z))s}.
\tag{67.24}
$$

This is an injective continuous function with a measurable inverse, and recovers $s$ from likelihood data. Every Borel subset of $B_n$ is consequently in $\mathcal G$ modulo null sets. The restriction of $\sigma$ to this component has a finite strictly positive Lebesgue density: the bounds on $k_t$ are uniform for $0\le t\le1/2$, and every occupied component has positive mixture weight. It is nonatomic. If $B_n$ is represented by the likelihood-measurable set in (67.23), restriction differs only on a null set, so the same atomlessness conclusion holds for that representative. The union of these components has mixture mass $1-h>0$. Hence $\sigma|_{\mathcal G}$ has a nonatomic part of positive mass and cannot satisfy the purely atomic hypothesis (60.1). Diffuseness of the original targets alone would not have proved this.

Finally consider any lawful family $(\lambda_y)$ within cap $h$, imposing no target row, component support, absolute continuity or density-range condition on it. Fix any actual $x\in D_n$. For every integer $\ell\ge n$, Theorem 35.2 supplies an actual $y_\ell\in C_\ell(x)$ with $j_\ell=\Omega(y_\ell)>\ell$. Lemma 45.3 gives $\lambda_{y_\ell}\to\lambda_x$ in TV. The event $B_n\sqcup P_{j_\ell}$ has original target mass one, so the cap forces

$$
\lambda_{y_\ell}(B_n)+\lambda_{y_\ell}(P_{j_\ell})\ge1-h.
\tag{67.25}
$$

For the one fixed measure $\lambda_x$, disjointness of all $P_j$ gives $\lambda_x(P_{j_\ell})\to0$. TV convergence bounds $\lambda_{y_\ell}(P_{j_\ell})$ by that quantity plus $\operatorname{TV}(\lambda_{y_\ell},\lambda_x)$, also tending to zero. Passing to the limit proves

$$
\lambda_x(B_n)\ge1-h\qquad(x\in D_n).
\tag{67.26}
$$

This holds for every occupied $n$ and for every lawful cap-$h$ family, not only for the constructed attainer.

Put $d=1-h>0$. If this family's range were totally bounded, finitely many probability centers would cover it by TV balls of radius $d/4$. For each of these centers $v$, the disjoint events $B_n$ have $v(B_n)\to0$. Choose $n$ so large that every center has $v(B_n)<d/4$, and choose an actual $x\in D_n$. Equation (67.26) gives

$$
\operatorname{TV}(\lambda_x,v)
\ge\lambda_x(B_n)-v(B_n)>3d/4
$$

for every center, contradicting the cover. Thus the range is not totally bounded. Probabilities all have variation norm one. A probability range contained in a finite-dimensional real signed-measure space is therefore bounded there and totally bounded by equivalence of finite-dimensional norms; on differences of probabilities event-TV is half the variation norm. This contradicts the proved obstruction and excludes every such finite-dimensional range, including all fixed $E$-density ranges of Section 64. $\square$

**Corollary 67.6 (Strict boundary of the finite-dimensional cap certificate).** For the original targets of Theorem 67.5, no finite-dimensional $E$ in Definition 64.1 has all its stable fibers nonempty at the original cap $h=R_\mu$. If it did, Theorem 64.2 would supply a lawful cap-$h$ preparation in that fixed finite-dimensional space, contradicting Theorem 67.5. Thus an attained genuinely nonatomic positive-row endpoint need not admit any fixed finite-dimensional certificate of that form.

Section 65's obstruction instead concerns finite covers of the original target tails; it makes no universal statement about selected prepared ranges. Theorem 67.5 supplies that missing universal quantifier for its specified input. The published Section 66.7 example has a constant optimum certifiable by Section 64 and supplies no separation from it. The present family does not satisfy Definition 66.1: any individual original target vanishes on every $B_n$ except its own, while other actual targets put positive mass on those components, so no designated original target dominates the entire family. The new proportional supplier therefore reaches an input outside that common-anchor subclass without asserting a general cap criterion.

**Mathematical sources and boundary 67.7.** The greatest original-target meet uses finite-measure Radon--Nikodym theory, with countably many targets and a finite dominating tape mixture. The pinned Mathlib interface is [RadonNikodym, withDensity_rnDeriv_eq](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean): it requires absolute continuity and the Lebesgue-decomposition interface, available for the finite measures here. Simultaneous infima and comparisons use countability, not a standard-Borel assumption on the general carrier. The normalized positive node increments and uniform coordinate are probability measures on their declared measurable spaces. Their countable product and finite-cylinder formula are [pinned Mathlib, Probability/ProductMeasure, Measure.infinitePi and infinitePi_cylinder](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/ProductMeasure.lean). These interfaces are cited for their mathematical hypotheses; no compiled Lean application is claimed.

The established lower-envelope/range-partition reference is Gallo, Lerasle and Takahashi, [Markov approximation of chains of infinite order in the bar-d metric, Section 3, Lemma 3.1](https://arxiv.org/html/1107.4353v2). It concerns a countable alphabet and conditional pasts. Neither its stationarity nor its coalescence conclusions are applied to the actual static sources. Galves, Garcia, Löcherbach and Orlandi, [Kalikow-type decomposition for multicolor infinite range particle systems, Theorem 1 and equations (9)--(16)](https://arxiv.org/html/1008.2740v3), supplies a continuous-state lower-envelope decomposition under a Borel state space, finite reference measure and a uniform integrated rate-continuity condition. This section does not instantiate those rate or uniform-continuity hypotheses and uses no particle-system simulation conclusion. The common-increment mechanism is mature mathematics; the original-source proportional coefficient and universal sharp-cap range deduction are ordinary repository-derived results, with no literature-priority claim. Finite-dimensional total boundedness uses the elementary norm-equivalence argument, as in the finite-dimensional supplier of Section 64.

The coefficient theorem holds on arbitrary nonempty measurable original tape carriers. On countable power-set carriers it remains a criterion for proportional containment, while the separate Section 54 criterion governs unrestricted TV caps. Theorem 67.5 has a standard Borel diffuse carrier with a verified nonatomic likelihood part; it does not extend that construction to countable carriers under the name nonatomic. Every original label is retained, every preparation uses one source-independent seed and shared measurable finite-record/output rules, and each actual source stops almost surely after finite actual execution. The bound is sourcewise, with no common horizon or seed-support restriction. Tables and probability products supply measurable law existence, not effectiveness, finite descriptions, exact real sampling or physical-resource bounds.

The original arbitrary-measurable target-intrinsic necessary-and-sufficient TV-cap/attainment problem remains unresolved beyond the published subclasses and the sufficient proportional certificate. Proposition 67.4 prevents replacing that question by proportional feasibility. General prescribed positive-proposal, nonzero-error, divergence and arbitrary-consumer profile classifications also remain unresolved. No source label, numerical value, magnitude promise, target input, extra observation, law on sources, source selection operation, reset or conditioning away failures is introduced. These are ordinary proofs only, with no Lean, Scribe, ingestion, freezing or kernel claim.

## 追加锚（本行以下为增补区）

## 68. Local norm-to-order control in a fixed range of regular block densities

Keep the original labeled sources, Advice0 with $\beta_0=0$, consumer, measurable tape carrier and targets of Definition 59.1. In particular $X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\}$, $N(r,g)=1+F_rg$, and $\Omega(r,g)=\omega(N(r,g))$ counts distinct prime factors. Use the original target mixture $\sigma$, likelihood information $\mathcal G$, actual signatures $Q$ and occupied neighborhoods $U_m(q)$ of Sections 59 and 54. The original target and prepared laws below are measures on the entire original $(\Theta,\mathcal F)$; the explicitly introduced rank pushforwards and auxiliary product-seed laws live on their declared spaces. TV has its event-supremum normalization. A supplied range is fixed from the original target and tape data before any preparation is selected; it need not contain the targets.

**Definition 68.1 (A local order deficit of the fixed range).** Let $P$ be a nonempty subset of the nonnegative integral-one density classes in $L^1(\sigma|_{\mathcal G})$. For $g\in P$ and $\epsilon>0$ let $\mathscr H_P(g,\epsilon)$ consist of all nonempty finite or countably infinite subsets $H\subseteq P$ such that $g\in H$ and $\|k-g\|_1<\epsilon$ for every $k\in H$. Put

$$
D_P(g,\epsilon)=\sup_{H\in\mathscr H_P(g,\epsilon)}
       \int\left(g-\inf_{k\in H}k\right)\,d\sigma.
\tag{68.1}
$$

For each such $H$, simultaneous nonnegative measurable representatives can be used. The countable infimum is measurable, is at most $g$, and defines the greatest common submeasure of the laws in $H$. Thus its integral and (68.1) are independent of versions, and $0\le D_P(g,\epsilon)\le1$. Call the fixed range locally order controlled if

$$
\lim_{\epsilon\downarrow0}D_P(g,\epsilon)=0\qquad(g\in P).
\tag{68.2}
$$

The supremum in (68.1) tests every countable family in a norm neighborhood of a fixed density. It takes no unknown prepared family or cap selection as input. It is a condition on the supplied range, distinct from the pointwise lower-semicontinuity test (62.3) for one particular selected family.

**Theorem 68.2 (The fixed-range norm-to-order bridge).** Under (68.2), every TV-continuous selection $q\mapsto g_q\sigma$ into this fixed range has greatest cylinder common submeasures

$$
\ell_{C_m(q)}(A)=\int_A\inf_{q'\in U_m(q)}g_{q'}\,d\sigma
\qquad(A\in\mathcal F)
\tag{68.3}
$$

with $\ell_{C_m(q)}(\Theta)\uparrow1$ at every actual $q$. Consequently every such selection is exactly lawfully acquired on the original tapes. This conclusion does not require total boundedness of the range or a cap condition on the selection.

**Proof.** The actual $Q$ is countable. Choose density representatives for the whole selected family and remove one common null set. For fixed $q$ and $\epsilon>0$, TV continuity, together with $\operatorname{TV}(g\sigma,k\sigma)=\frac12\|g-k\|_1$, supplies a finite actual depth $m$ with

$$
\|g_{q'}-g_q\|_1<\epsilon\qquad(q'\in U_m(q)).
\tag{68.4}
$$

Its set of selected densities belongs to $\mathscr H_P(g_q,\epsilon)$. Hence

$$
1-\ell_{C_m(q)}(\Theta)\le D_P(g_q,\epsilon).
\tag{68.5}
$$

Refining cylinders increases their infimum; the infimum is bounded by $g_q$ because $q\in U_m(q)$. Equation (68.2) and (68.5) therefore prove increasing convergence of the common masses to one. Greatestness of (68.3) is the countable Radon--Nikodym comparison of Theorem 46.4. That theorem acquires exactly these selected original-tape laws. Here the new implication is from a property of all norm neighborhoods in the fixed range to exhaustion for every continuous selection. The exhaustion-to-acquisition theorem 46.4 and the equivalent selected-family condition 62.3 are reused. $\square$

**Definition 68.3 (Regular densities on disjoint original-tape blocks).** As an additional supplier hypothesis, specify the following data from the original targets and tape structure. Let $B_n\in\mathcal F$, $n\ge1$, be pairwise disjoint. For each $n$, let $\tau_n$ be a probability on the original tapes, supported on $B_n$, absolutely continuous with respect to $\sigma$, and with a $\mathcal G$-measurable density $r_n=d\tau_n/d\sigma$. Let $S_n$ be a nonempty compact metric space with metric $d_n$ and its Borel sigma algebra, and let $T_n:B_n\to S_n$ be a measurable rank whose extension by a fixed point off $B_n$ has a $\mathcal G$-measurable version modulo $\sigma$-null sets. Require

$$
\rho_n=(T_n)_*\tau_n,\qquad
\rho_n(V)>0\quad\text{for every nonempty open }V\subseteq S_n.
\tag{68.6}
$$

A density version $r_n$ is zero off $B_n$ almost everywhere. Let $\omega_n:[0,\infty)\to[0,\infty)$ be finite and nondecreasing, with $\omega_n(0)=0$ and $\omega_n(a)\to0$ as $a\downarrow0$. Define the fixed normalized class

$$
\begin{aligned}
\mathcal A_n=\{u\in C(S_n;\mathbb R):\;&u\ge0,\quad\int u\,d\rho_n=1,\\
&|u(s)-u(t)|\le\omega_n(d_n(s,t))\quad(s,t\in S_n)\}.
\end{aligned}
\tag{68.7}
$$

It contains the constant function $1$. With $\mathcal P(\mathbb N)$ denoting the probability vectors on the positive integers, set

$$
\begin{aligned}
\mathcal R&=\left\{\sum_{n\ge1}a_n\,u_n(T_n)\tau_n:
       a\in\mathcal P(\mathbb N),\ u_n\in\mathcal A_n\right\},\\
P_{\mathcal R}&=\left\{\sum_{n\ge1}a_n r_n\,u_n(T_n):
       a\in\mathcal P(\mathbb N),\ u_n\in\mathcal A_n\right\}.
\end{aligned}
\tag{68.8}
$$

The factor $u_n(T_n)$ in a measure means integration against $\tau_n$ on the actual block. The density sum is taken modulo null sets, with zero off the union of the blocks. Its nonnegative terms have integrals $a_n$, so every member of $P_{\mathcal R}$ has integral one, is likelihood measurable modulo null sets, and defines exactly the corresponding law in $\mathcal R\subseteq P_{\mathcal G}$. If $a_n>0$, its law conditional on the measurable event $B_n$ has density $u_n(T_n)$ relative to $\tau_n$. This is conditioning on a declared tape block, not on a source or a preparation failure. No disintegration of the original tape space is assumed. Zero-mass blocks can use $u_n=1$.

**Theorem 68.4 (A complete non-totally-bounded supplier with local order control).** Under Definition 68.3, $\mathcal R$ is a closed, complete, separable, convex range in event-TV. Its real linear span and its affine dimension are infinite, and it is not TV totally bounded. Nevertheless $P_{\mathcal R}$ satisfies (68.2). More precisely, fix a center $g=\sum_n a_n r_n u_n(T_n)$, a finite set $F\subseteq\mathbb N$, and positive radii $b_n$ for $n\in F$. Put

$$
\beta_n(b)=\inf_{s\in S_n}\rho_n\{t:d_n(s,t)<b\}>0.
\tag{68.9}
$$

Then the deficit of every countable family in its $L^1$ ball obeys

$$
D_{P_{\mathcal R}}(g,\epsilon)
\le\sum_{n\notin F}a_n+
       \sum_{n\in F}\left(\frac{\epsilon}{\beta_n(b_n)}
                          +2\omega_n(b_n)\right).
\tag{68.10}
$$

In particular every continuous selection into this fixed infinite-dimensional range has the original-tape exhaustion and acquisition conclusion of Theorem 68.2.

**Proof.** First (68.9) uses both hypotheses in (68.6). Compactness gives a finite cover of $S_n$ by open balls of radius $b/2$. Each has positive $\rho_n$ mass. If its center is within $b/2$ of $s$, that entire ball is contained in the radius-$b$ ball about $s$. The minimum of the finitely many positive masses is a lower bound in (68.9).

For nonnegative $u\in\mathcal A_n$, normalization and its common modulus give

$$
u(s)\le1+\omega_n(\operatorname{diam}S_n)\qquad(s\in S_n).
\tag{68.11}
$$

Indeed integrate $u(s)\le u(t)+\omega_n(\operatorname{diam}S_n)$ in $t$. Thus $\mathcal A_n$ is uniformly bounded and equicontinuous, and is closed in the uniform norm: each defining inequality, nonnegativity and normalization pass to a uniform limit. The classical Arzelà--Ascoli theorem makes it compact. The precise hypotheses are a compact metric domain, a common modulus giving equicontinuity, pointwise relatively compact real values, and a closed class in the uniform topology. They are the compact-domain specialization of [pinned Mathlib, Ascoli, ArzelaAscoli.compactSpace_of_isClosedEmbedding](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/UniformSpace/Ascoli.lean). Compact metric classes are separable. Full support of $\rho_n$ makes continuous functions equal $\rho_n$-almost everywhere equal everywhere, so their $L^1(\rho_n)$ classes have unique continuous representatives.

There is a useful direct norm estimate inside each block, including variable block masses. If $v=a u$ and $w=c z$, where $a,c\in[0,1]$ and $u,z\in\mathcal A_n$, then both $v$ and $w$ have modulus bounded by $\omega_n$. Averaging over the radius-$b$ ball about $s$ gives

$$
\begin{aligned}
|v(s)-w(s)|
&\le \frac{1}{\rho_n(B(s,b))}
       \int_{B(s,b)}|v(t)-w(t)|\,d\rho_n(t)+2\omega_n(b)\\
&\le\frac{\|v-w\|_{L^1(\rho_n)}}{\beta_n(b)}+2\omega_n(b).
\end{aligned}
\tag{68.12}
$$

This holds simultaneously at every $s$, for every such pair. In particular $L^1$ convergence in the fixed weighted class forces uniform convergence, by first choosing $b$ small and then the $L^1$ tolerance small.

Disjoint support and the pushforward identity give the exact global norm formula

$$
\left\|\sum_n a_n r_nu_n(T_n)-
             \sum_n c_n r_nz_n(T_n)\right\|_{L^1(\sigma)}
=\sum_n\|a_nu_n-c_nz_n\|_{L^1(\rho_n)}.
\tag{68.13}
$$

No cancellation between blocks occurs. To prove closedness, let $g_j\in P_{\mathcal R}$ converge in $L^1(\sigma)$ to $g$. Nonnegativity, integral one and vanishing off $B=\bigcup_nB_n$ pass to the limit. Let $a_n=\int_{B_n}g\,d\sigma$; the corresponding masses $a_{j,n}$ converge to $a_n$, and $\sum_na_n=1$. For any $a_n>0$, eventually $a_{j,n}>0$. The normalized block restrictions are $L^1$ Cauchy, since, for positive $a_{j,n},a_{k,n}$,

$$
\|u_{j,n}-u_{k,n}\|_{L^1(\rho_n)}
\le\frac{\|a_{j,n}u_{j,n}-a_{k,n}u_{k,n}\|_{L^1(\rho_n)}
                  +|a_{j,n}-a_{k,n}|}{a_{j,n}}.
\tag{68.14}
$$

Compactness of $\mathcal A_n$ gives a uniformly convergent subsequence with limit $u_n\in\mathcal A_n$. Its original-tape block measures converge in variation to both $a_nu_n(T_n)\tau_n$ and $g\sigma|_{B_n}$, which must be equal. If $a_n=0$, the limit block is zero and choose $u_n=1$. Countable additivity over $B$ now gives $g\sigma=\sum_na_nu_n(T_n)\tau_n$. Thus $P_{\mathcal R}$ is closed in the complete space $L^1(\sigma)$, and $\mathcal R$ is complete in TV. It is closed even among all original-tape probabilities: a TV limit of laws absolutely continuous with respect to $\sigma$ still vanishes on every $\sigma$-null event, and the density distance is half the $L^1$ distance. It is also a subspace of the separable metric range $P_{\mathcal G}$ from Theorem 59.2. Alternatively, finite mixtures with rational weights and functions from countable dense subsets of each $\mathcal A_n$ form a dense subset by (68.13) and truncation of the summable block masses.

Convexity follows by combining block weights and, on every block of positive resulting mass, taking the corresponding normalized convex combination of its two conditional densities. The classes $\mathcal A_n$ are convex. The laws $\tau_n$, obtained with weight one on their block and density $1$, belong to $\mathcal R$. They are linearly independent and $\operatorname{TV}(\tau_n,\tau_j)=1$ for $n\ne j$. The differences $\tau_n-\tau_1$, $n\ge2$, are linearly independent as well. These facts prove the claimed infinite dimensions and failure of total boundedness.

It remains to prove the order assertion, which is stronger than these metric properties. Let $H\in\mathscr H_{P_{\mathcal R}}(g,\epsilon)$ be any countable family. Write each $k\in H$ in the form (68.8), with block weights $c_n(k)$ and conditional representatives $z_n(k)$. Equation (68.13) bounds each individual block distance by $\epsilon$. For $n\in F$ set $e_n=\epsilon/\beta_n(b_n)+2\omega_n(b_n)$. Equation (68.12) gives simultaneously for every $k\in H$ and $s\in S_n$

$$
c_n(k)z_n(k)(s)\ge\bigl(a_nu_n(s)-e_n\bigr)_+.
\tag{68.15}
$$

Transfer this inequality to the original tapes and multiply by $r_n$. After removal of a single null set for the countable family, its common density is bounded below on $B_n$ by $r_n(a_nu_n(T_n)-e_n)_+$. Integration and (68.6) give

$$
\int\inf_{k\in H}k\,d\sigma
\ge\sum_{n\in F}\int(a_nu_n-e_n)_+\,d\rho_n
\ge\sum_{n\in F}a_n-\sum_{n\in F}e_n.
\tag{68.16}
$$

The lower bound is independent of the particular countable family. Taking the supremum of its mass deficit proves (68.10). Given $\delta>0$, first choose a finite nonempty $F$ with $\sum_{n\notin F}a_n<\delta/3$, then choose each $b_n$ with $2\sum_{n\in F}\omega_n(b_n)<\delta/3$, and finally choose $\epsilon$ with $\epsilon\sum_{n\in F}1/\beta_n(b_n)<\delta/3$. This proves (68.2) at the fixed center. No regularity constant uniform in $n$ and no common tail estimate over all centers is used. The estimate supplies the missing simultaneous lower bound for all neighbors, rather than separate pointwise bounds with different exceptional sets. $\square$

**Theorem 68.5 (Exact stable-fiber cap criterion within the supplied range).** For a range $\mathcal R$ supplied by Definition 68.3 and a cap $\eta\in[0,1]$, start with

$$
K_{0,\mathcal R}^{\eta}(q)=
\bigcap_{y\in X:\,[y]=q}
       \{\lambda\in\mathcal R:\operatorname{TV}(\lambda,\mu_y)\le\eta\}.
\tag{68.17}
$$

Use exactly the metric-distance refinement and countable-ordinal intersections (54.4)--(54.5), with metric space $\mathcal R$ and actual neighborhoods $U_m(q)$. Write $K_{\infty,\mathcal R}^{\eta}$ for the stabilized fibers. Then

$$
\begin{aligned}
&\text{a lawful original-tape cap-}\eta\text{ preparation with all laws in }\mathcal R
       \text{ exists}\\
&\qquad\Longleftrightarrow\quad
K_{\infty,\mathcal R}^{\eta}(q)\ne\varnothing\quad(q\in Q).
\end{aligned}
\tag{68.18}
$$

In particular stable nonemptiness at the independently defined original $R_\mu$ is necessary and sufficient for an $\mathcal R$-valued attainer of that original value. It is sufficient for unrestricted attainment, and is not asserted necessary for unrestricted attainment.

**Proof.** All initial values are closed in the complete separable range $\mathcal R$ of Theorem 68.4; the triangle inequality makes distance to each original target continuous. The stabilization and continuous-selection parts of Theorem 54.2 apply with this range. Their actual hypotheses are countability of $Q$, its countable clopen prefix basis, a complete separable metric range, and closed values, allowing empty values. Compactness or finite-dimensionality of the range is not among them. A strict decrease deletes a new pair consisting of a signature and a basis open set in the range, so stabilization occurs at a countable ordinal. Stable nonempty fibers are lower semicontinuous, and the disjoint clopen refinements with summable successive distances in (54.9)--(54.10) give a continuous selection $\lambda_q\in K_{\infty,\mathcal R}^{\eta}(q)$. These metric portions are reused; the countable-tape acquisition step (54.11) is not being applied to diffuse blocks.

Write this selection as $\lambda_q=g_q\sigma$. Theorem 68.4 supplies (68.2), and Theorem 68.2 supplies greatest common submeasures $\ell_C$ with masses $a_C$ exhausting one along every actual branch. The original-tape realization is precisely Theorem 46.4: give the root a zero parent, and put $\Delta_C=\ell_C-\ell_{C^-}$. Each increment is a positive original-tape measure, of mass $a_C-a_{C^-}$. Give a coordinate $W_C$ its normalized probability law when this mass is positive, and use the point-evaluation probability at one fixed original tape when it is zero. There are countably many nodes. All these coordinates and an independent $U$ uniform on $(0,1)$ form one source-independent product seed law. At a reached node the shared rule hands over $W_C$ if $U<a_C$ and otherwise queries the next actual prime. For an original tape event $A$ its unconditional output submeasure at that node is

$$
\mathsf P\{a_{C^-}\le U<a_C,\ W_C\in A\}=\Delta_C(A),
\tag{68.19}
$$

with root lower threshold zero. Zero-mass nodes have empty output intervals. Summing (68.19) along an actual branch through depth $m$ gives $\ell_{C_m(q)}$. Since its mass increases to one and it is dominated by $\lambda_q$, actual handoff is sourcewise almost surely finite and its full output law is $\lambda_q$. Finite records are measurable interval events in $U$; specifying an output event adds a measurable coordinate event, and the full output preimage is their countable union. The countable product is the probability-product construction already used in Theorem 46.4, with [pinned Mathlib, Measure.infinitePi and infinitePi_cylinder](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/ProductMeasure.lean). Each coordinate is a probability on its declared measurable space, which is the product theorem's hypothesis.

Only finite actual prime-divisibility answers precede the handoff; no source label, $N$, magnitude, target value or law on sources is supplied. The unchanged consumer receives only the original tape and runs on the same static source. Preparation does not reset the source or condition away any seed event. The depth of handoff is allowed to depend on the actual source and seed. Membership in (68.17) gives the cap against every label, including equal-signature labels with distinct targets.

Conversely, Lemma 45.3 makes every lawful family with laws in $\mathcal R$ a TV-continuous map on $Q$. If it satisfies the cap, it selects (68.17). The survival induction (54.8) keeps this selection in every refinement, proving necessity in (68.18). Finally the unrestricted original infimum is $R_\mu$ by Theorem 50.2, so a cap-$R_\mu$ family supplied by (68.18) has uniform error exactly $R_\mu$. No equality of unrestricted cylinder radii with $\mathcal R$-restricted radii is needed or asserted. $\square$

**Theorem 68.6 (The unchanged nonatomic positive-row endpoint lies in the supplied range).** Take exactly the original carrier, consumer and targets of Theorem 67.5, with its fixed $h\in(0,1)$ and allowed profile. Use its already declared $B_n$ as the supplier blocks, let $\tau_n$ be Lebesgue probability on the original copy $B_n=(0,1)$, take $S_n=[0,1]$, $T_n(s)=s$, and $\omega_n(b)=b$. Specify all this data from (67.16)--(67.18), before selecting any preparation. It satisfies Definition 68.3. The resulting fixed range consists of arbitrary probability mixtures of the $B_n$ block laws whose normalized conditional densities extend to nonnegative $1$-Lipschitz functions of integral one on $[0,1]$. Its stable fibers are all nonempty at the unchanged original cap $h=R_\mu$, and (68.18) supplies a lawful attainer in this range, on the unchanged original sources and consumer. This is a range certificate for the published input, not a new example of an attained positive row.

**Proof.** Likelihood measurability is not inferred just from diffuseness. The published identities (67.23)--(67.24) put each original $B_n$ and every Borel subset of it in $\mathcal G$ modulo $\sigma$-null sets. On $B_n$ the original mixture has Lebesgue density

$$
w_n(s)=(1-h)\sum_{i:\,n(x_i)=n}2^{-i}k_{t(x_i)}(s).
\tag{68.20}
$$

Occupation of every $D_n$ is already Theorem 67.5. The bounds $e^{-1/2}\le k_t(s)\le e^{1/2}$ for $0\le t\le1/2$ therefore make $w_n$ finite and strictly positive, bounded above and below by positive multiples of the weight sum on that block. Thus $\tau_n\ll\sigma$ with density $\mathbf1_{B_n}/w_n(s)$, likelihood measurable modulo null sets. The rank extension is likelihood measurable by the same published recovery of $s$. Its pushforward is Lebesgue probability on $[0,1]$, with endpoints of mass zero and full support. All blocks remain the original tape blocks; none is a new observation of the source.

The original exponential conditional densities in (67.17) have continuous extensions to $[0,1]$. Since $Z_t\ge1$,

$$
0\le\frac{d}{ds}k_t(s)=t\frac{e^{ts}}{Z_t}
\le\tfrac12 e^{1/2}<1\qquad(0\le t\le1/2).
\tag{68.21}
$$

They are normalized and belong to the specified $\mathcal A_n$. Consequently the already published laws $\nu_y=k_{t(y)}(s)\tau_{n(y)}$ all belong to $\mathcal R$. The parameter estimates (67.19)--(67.20) make $q\mapsto\nu_q$ TV-continuous: its block is constant after the first $n(q)$ actual answers, and its remaining parameter variation tends to zero in a shrinking actual prefix. This checks the interface for this same family, without supplying the parameter to the preparation. Equal signatures have the same $n,t,\Omega$ in this input, so the selection is well-defined on $Q$, while every original label retains its prescribed target.

The unchanged targets are $\mu_y=(1-h)\nu_y+h\pi_{\Omega(y)}$. Their two components are disjoint, and hence

$$
\operatorname{TV}(\nu_y,\mu_y)=h=R_\mu\qquad(y\in X),
\tag{68.22}
$$

where the equality to the original sharp value is the published Theorem 67.5. Thus this continuous selection belongs to every initial fiber (68.17) at cap $h$, and the survival argument puts it in every stable fiber. Theorem 68.5 now proves the desired original-tape correspondence for the supplied range. The original target row remains exactly $(h_y,e_y,d_y,z_y)=(h,0,0,1-h)$ under the original consumer, for every label and the same profile; the selected laws on the $B_n$ yield unknown under that consumer. No row condition on prepared laws has been inserted.

The supplier is genuinely infinite-dimensional even within a single diffuse block, in addition to its disjoint-block noncompactness. For $j\ge1$ the functions

$$
u_j(s)=1+\frac{\cos(2\pi j s)}{2\pi j}
\tag{68.23}
$$

are positive, have integral one, and have derivative of absolute value at most one. Thus $1$ and every $u_j$ belong to $\mathcal A_n$. The differences $u_j-1$ are linearly independent: multiplying any finite vanishing linear combination by each $\cos(2\pi k s)$ and integrating isolates its coefficient by cosine orthogonality. Multiplication by the strictly positive block density preserves that independence on the original tapes. This range is therefore not merely a finite-dimensional class on each block. Its separated laws $\tau_n$ also verify failure of TV total boundedness directly. Corollary 67.6 excludes every Section 64 certificate at this same cap, and the paragraph following Corollary 67.6 excludes a dominating original anchor of Section 66. The present certificate instead uses the regular original conditional densities and finite-center tail estimate (68.10). $\square$

**Question 68.7 (The unrestricted boundary).** For original inputs not satisfying a fixed-range supplier hypothesis, the arbitrary-measurable target-intrinsic necessary-and-sufficient TV-cap and attainment problem remains open as stated in Section 62. The exact necessity in (68.18) concerns preparations whose output laws lie in the specified $\mathcal R$. An empty restricted stable fiber excludes that range, without excluding preparations in another original-tape range. The range-level condition (68.2) is sufficient for every continuous selection into $P$; no converse or universal sharpness assertion is made. It is stronger than a test of a particular selection: a constant selection is lawfully acquired even if the larger range containing it fails (68.2). General prescribed positive-proposal, nonzero-error, divergence and arbitrary-consumer profile classifications remain unresolved. Theorem 68.6 covers the published truthful positive-row input at its original sharp cap, rather than only an always-unknown target family.

The compactness used inside individual regular classes in Theorem 68.4 is the mature Arzelà--Ascoli input with its stated hypotheses. The quantitative averaging estimate (68.12), its finite-block tail consequence (68.10), and the resulting fixed-range supplier and its original-target correspondence are repository-relative deductions; no literature-priority claim is made. The established lower-envelope reference [Galves, Garcia, Löcherbach and Orlandi, Kalikow-type decomposition for multicolor infinite range particle systems, Theorem 1, equations (9)--(16)](https://arxiv.org/html/1008.2740v3) assumes a Borel color space, a finite reference measure, bounded integrated change rates and the uniform integrated rate-continuity condition (9). The static-source range condition here requires neither those rate data nor that uniformity over sources, and no particle-system conclusion is applied. [Gallo, Lerasle and Takahashi, Markov approximation of chains of infinite order in the bar-d metric, Definition 3.1 and Lemma 3.1](https://arxiv.org/html/1107.4353v2) treats countable-alphabet conditional pasts and range partitions; its stationary-chain conclusions are likewise not applied. The metric refinement, lossless likelihood range and acquisition realization are reused from Sections 54, 59 and 46.4, respectively. Condition (62.3) and the finite-dimensional and common-anchor suppliers of Sections 64 and 66 remain distinct reused results. TV compactness alone supplies no replacement for (68.2), as the already published 46.5 and 53.1 show.

## 追加锚（本行以下为增补区）

## 69. A uniform calibration modulus and the cost of carrying it to the source

A selected law can have cylinder common-submeasure masses tending to one along
each individual source branch without one depth sufficing for all branches.
Uniform order calibration adds this common depth requirement; summability adds
an expected-query bound.

**Definition 69.1 (Uniform order-calibration modulus).** Let $Q$ be a nonempty
countable subset of $\{0,1\}^{\mathbb N_{>0}}$, with occupied prefix neighborhoods

$$
U_m(q)=\{q'\in Q:q'_i=q_i\ (1\le i\le m)\},
\qquad m\in\mathbb N_0,
\qquad U_0(q)=Q.
$$

At each fixed depth these sets form a clopen partition of $Q$, and
$U_{m+1}(q)\subseteq U_m(q)$. Let $(\Theta,\mathcal F,\sigma)$ be a nonempty
probability carrier, let $\mathcal G\subseteq\mathcal F$ be a sigma algebra, and
choose finite nonnegative $\mathcal G$-measurable representatives of density
classes satisfying

$$
g_q\ge0,
\qquad
\int g_q\,d\sigma=1
\qquad(q\in Q).
\tag{69.1}
$$

The law $g_q\sigma$ is on the entire $\mathcal F$. For each $q$ and $m$ put

$$
\underline g_m(q)(\theta)=\inf_{q'\in U_m(q)}g_{q'}(\theta),
\qquad
a_m(q)=\int\underline g_m(q)\,d\sigma,
\tag{69.2}
$$

and define the uniform calibration modulus

$$
\boxed{
\Omega_g(m)=\sup_{q\in Q}\bigl(1-a_m(q)\bigr).
}
\tag{69.3}
$$

The infimum is measurable because $Q$ is countable. It lies between zero and
$g_q$, so $0\le a_m(q)\le1$. The measure $\underline g_m(q)\sigma$ is the
greatest common submeasure of the selected laws
$\{g_{q'}\sigma:q'\in U_m(q)\}$. Indeed any common submeasure is absolutely
continuous with respect to $\sigma$, and its Radon--Nikodym density is at most
each of the countably many $g_{q'}$ off a single null set, hence at most their
infimum. We call $g$ uniformly order-calibrated when $\Omega_g(m)\to0$.

Changing representatives for the countable family changes them only on a
countable union of measurable $\sigma$-null sets. Off that one set every
infimum in (69.2) is unchanged, simultaneously for all $q,m$. Thus (69.2)--(69.3)
are representative independent. The same convention applies to countably many
families and their limits below.

**Theorem 69.2 (Uniform modulus gives a uniform original-source query bound).**
For the original-source application retain the entire labeled source, zero
advice, target laws and consumer of Definition 59.1, namely

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad \Omega(r,g)=\omega(N(r,g)),\qquad\beta_0=0.
\end{aligned}
$$

Here $\omega$ counts distinct prime divisors; $\Omega_g$ in (69.3) is a separate
quantity. Enumerate the actual primes as $p_1<p_2<\cdots$, put
$[x]_i=\mathbf1_{p_i\mid N(x)}$, and take exactly $Q=\{[x]:x\in X\}$, without
additional limit signatures. Then

$$
C_m(x)=\{y\in X:[y]\in U_m([x])\},\qquad C_0(x)=X.
$$

Use the original nonempty measurable tape carrier $(\Theta,\mathcal F)$ and
its target mixture $\sigma=\sum_{i\ge1}2^{-i}\mu_{x_i}$ and likelihood sigma
algebra $\mathcal G$ of (59.2), with $X$ enumerated without repetitions. Let $g$
be a family of Definition 69.1 for these data, and set
$\lambda_x=g_{[x]}\sigma$. The mixture is a tape probability, not a supplied
source sampling law. All labels remain in $C_m(x)$, even when equal
signatures have distinct original targets $\mu_x$.

Assume the measurable common-rule semantics of Definitions 40.1 and 45.1:
a preparation uses one source-independent seed probability space and fixed
cylinder tables, observes only actual prime-divisibility answers with zero
advice, and has measurable finite records and output-event preimages. The seed
may be the countable probability product of original-tape coordinates and an
independent uniform variable used in Theorem 46.4. After handoff the unchanged
consumer receives only the declared original tape and runs on the same static
source. No effective evaluation of the fixed tables or sampling from a single
real seed is assumed.

The masses $a_m(q)$ are nondecreasing in $m$, and $\Omega_g(m)$ is
nonincreasing. If $a_m([x])\uparrow1$ at every actual $x$, the positive-increment
realization of Theorem 46.4 acquires exactly $(\lambda_x)$ with sourcewise
almost-sure finite handoff. Its handoff depth $N_x$, counting actual prefix
queries and allowing depth zero, has the exact tail
$\mathsf P\{N_x>m\}=1-a_m([x])$.
In particular, uniform order calibration implies

$$
\boxed{
\sup_{x\in X}\mathsf P\{N_x>m\}=\Omega_g(m).
}
\tag{69.4}
$$

If $\sum_{m\ge0}\Omega_g(m)<\infty$, then

$$
\boxed{
\sup_{x\in X}\mathbb E[N_x]
\le \sum_{m\ge0}\Omega_g(m)<\infty.
}
\tag{69.5}
$$

If $\Omega_g(m_0)=0$, this realization hands off by depth $m_0$ almost surely
at every source.

**Proof.** Refining a prefix neighborhood removes candidate signatures, so its
pointwise infimum increases. This proves both monotonicity statements. The
signature-cylinder correspondence gives the greatest common submeasure
$\ell_C$ of $(\lambda_y)_{y\in C}$ and, at $C=C_m(x)$, gives

$$
\ell_C=\underline g_m([x])\sigma,
\qquad a_C:=\ell_C(\Theta)=a_m([x])
\ge1-\Omega_g(m).
\tag{69.6}
$$

Index each occupied node by its depth and finite prime-answer word, so equal
source sets at different depths remain distinct nodes. Give the depth-zero root
$X$ a fictitious parent with zero submeasure. At each occupied non-root node put
$\Delta_C=\ell_C-\ell_{C^-}$, and put
$\Delta_X=\ell_X$. These are positive original-tape measures. For positive
mass $d_C=\Delta_C(\Theta)$, preload a coordinate $W_C$ with probability law
$\Delta_C/d_C$; for zero mass use the point-evaluation probability at one fixed
original tape. There are countably many nodes, so these coordinates and an
independent $U$ uniform on $(0,1)$ form one common product seed.

At a reached node $C$, hand over $W_C$ if $U<a_C$; otherwise query the next
actual prime. Reaching a non-root node implies $U\ge a_{C^-}$, so for every
$A\in\mathcal F$ the unconditional node-output measure is

$$
\mathsf P\{a_{C^-}\le U<a_C,\ W_C\in A\}=\Delta_C(A),
$$

with root lower threshold zero; a zero-mass node has an empty output interval.
The measures telescope along source $x$ through depth $m$ to $\ell_{C_m(x)}$.
They are dominated by $\lambda_x$, and if their masses tend to one their limit
is exactly $\lambda_x$. Finite records and output-event preimages are measurable
interval and coordinate events, or countable unions of them. Thus the
construction meets the stated handoff hypotheses on the original carrier.

Define $N_x=\infty$ on a branch with no handoff. No handoff through depth $m$
is equivalent to $U\ge a_{C_m(x)}$, including the root test before any query.
Hence $\mathsf P\{N_x>m\}=1-a_m([x])$. Any endpoint ambiguities can be
removed on the single seed-null union of $\{U=a_C\}$ over the countably many
nodes. Surjectivity of $x\mapsto[x]$ onto the actual $Q$ gives (69.4).
For a nonnegative integer-valued depth, with the extended value $\infty$ allowed,
Tonelli's tail-sum identity gives

$$
\mathbb E[N_x]=\sum_{m\ge0}\mathsf P\{N_x>m\}.
\tag{69.7}
$$

Bounding each term by $\Omega_g(m)$ proves (69.5); no exchange of supremum
and sum as an equality is needed. Zero deficit at $m_0$ gives the final
assertion. These are query-depth bounds for this specified realization, rather
than bounds on all preparation transitions or on every possible preparation.
$\square$

Theorem 68.2 gives $a_m(q)\uparrow1$ separately at every $q$ for continuous
selections into a locally order-controlled fixed range. Its depth can depend
on $q$ and the tolerance. Uniform order calibration requires one depth for all
$q$ at a given tolerance, and (69.5) additionally requires a summable modulus.
Neither a uniform tail decay nor a finite uniform expected depth follows from
the local block hypotheses of Section 68 alone.

**Theorem 69.3 (Uniform density stability and shared-modulus $L^1$ closure).**
Let $g$ and $h$ be two families of Definition 69.1. If $\delta\ge0$ satisfies

$$
|g_q(\theta)-h_q(\theta)|\le\delta
\quad\text{for every }q\in Q\text{ and }\sigma\text{-almost every }\theta,
\tag{69.8}
$$

then for every $m$

$$
\boxed{
\Omega_h(m)\le\Omega_g(m)+\delta.
}
\tag{69.9}
$$

In particular, let $g^{(r)}$, $r\in\mathbb N_0$, and $g$ be families of
Definition 69.1. Suppose

$$
\sup_{q\in Q}\|g^{(r)}_q-g_q\|_\infty\longrightarrow0,
\tag{69.10}
$$

and one nonincreasing sequence $\varpi:\mathbb N_0\to[0,1]$, tending to zero,
bounds every stage:

$$
\Omega_{g^{(r)}}(m)\le\varpi(m)
\qquad(r,m\ge0).
\tag{69.11}
$$

Then $\Omega_g(m)\le\varpi(m)$ for every $m$. The same conclusion holds under
the weaker convergence hypothesis
$\|g^{(r)}_q-g_q\|_1\to0$ for every fixed $q\in Q$, with (69.11) retained;
no uniformity in $q$ is required for this $L^1$ closure.
Under the original-source and handoff hypotheses of Theorem 69.2, this gives its
common tail bound, and a summable $\varpi$ gives the common expected-depth bound
$\sup_x\mathbb E[N_x]\le\sum_m\varpi(m)$.

**Proof.** For (69.8), take the union of the exceptional null sets over the
countable $Q$. On its complement all coordinate inequalities hold together,
so for every $q,m$

$$
\inf_{q'\in U_m(q)}h_{q'}(\theta)
\ge\inf_{q'\in U_m(q)}g_{q'}(\theta)-\delta.
\tag{69.12}
$$

Integrating and using $\sigma(\Theta)=1$ gives
$a_m^h(q)\ge a_m^g(q)-\delta$. Taking the supremum of the deficits proves
(69.9). For (69.10), apply it with
$\delta_r=\sup_q\|g^{(r)}_q-g_q\|_\infty$ for all sufficiently large $r$,
when this supremum is finite, and let $r\to\infty$ in (69.11).
The essential-supremum bounds hold simultaneously outside the union of their
null sets over the countable pairs $(r,q)$.

For coordinatewise $L^1$ convergence fix $q,m$, and exhaust $U_m(q)$ by
increasing finite nonempty sets $F_k$ containing $q$; if the neighborhood is
finite, keep $F_k=U_m(q)$ after its last element. Put

$$
b_k^{(r)}=\min_{q'\in F_k}g^{(r)}_{q'},\qquad
b_k=\min_{q'\in F_k}g_{q'}.
$$

The elementary finite-minimum inequality gives

$$
\|b_k^{(r)}-b_k\|_1
\le\sum_{q'\in F_k}\|g^{(r)}_{q'}-g_{q'}\|_1\longrightarrow0
\qquad\text{for each fixed }k.
$$

Since $b_k^{(r)}\ge\underline g_m^{(r)}(q)$, (69.11) implies
$\int b_k^{(r)}\,d\sigma\ge1-\varpi(m)$ for every $r$. Taking $r\to\infty$
first yields $\int b_k\,d\sigma\ge1-\varpi(m)$. Then
$b_k\downarrow\underline g_m(q)$ and $0\le b_k\le g_q$, with $g_q$ integrable.
Dominated convergence gives $a_m^g(q)\ge1-\varpi(m)$. Taking the supremum of
the deficits over $q$ proves $\Omega_g(m)\le\varpi(m)$. Representatives of all
$g^{(r)}_q$ and $g_q$ can be changed only on one null union over $(r,q)$, so
every finite and countable infimum in this proof has the same integral for all
such choices. Finally apply Theorem 69.2 with its stated source hypotheses.
$\square$

A shared modulus thus survives coordinatewise $L^1$ convergence. Uniform
$L^\infty$ control also supplies the perturbation estimate (69.9) without a
shared modulus; $L^1$ or TV convergence alone supplies no corresponding
uniform order-calibration guarantee.

**Theorem 69.4 (Loss under uniform $L^1$ convergence without a shared modulus).**
There are a countable binary prefix space $Q$, a probability carrier
$([0,1],\mathcal B,\lambda)$ and density families $g^{(N)}$ converging uniformly
in $q$ in $L^1(\lambda)$ to $g$ such that

$$
\Omega_{g^{(N)}}(m)=0\text{ for all sufficiently large }m
\quad\text{for each }N\ge1,
\tag{69.13}
$$

but

$$
\boxed{\Omega_g(m)=1\quad\text{for every }m\in\mathbb N_0.}
\tag{69.14}
$$

There is no single decaying modulus bounding all $\Omega_{g^{(N)}}$.
This is an abstract prefix-space counterexample, not an additional target
family prescribed on the original $X$.

**Proof.** For each integer $r\ge2$, partition $[0,1)$ into its $r$ half-open
intervals of length $1/r$, and enumerate all these intervals as
$A_1,A_2,\ldots$ in increasing blocks of $r$. Their measures
$\alpha_n=\lambda(A_n)$ tend to zero, while every point of $[0,1)$ belongs to
infinitely many $A_n$. Put

$$
h_n=\frac{\mathbf1_{A_n^c}}{1-\alpha_n},\qquad n\ge1,
\tag{69.15}
$$

with complements taken in $[0,1]$. Each $h_n$ is a probability density, and

$$
\|h_n-1\|_1=2\alpha_n\longrightarrow0.
\tag{69.16}
$$

Let $q_\ast=0^\infty$, $q_n=0^n10^\infty$ for $n\ge1$, and
$Q=\{q_\ast,q_1,q_2,\ldots\}$. With coordinates indexed from one, the first
$1$ of $q_n$ is at coordinate $n+1$. Its genuine depth-$m$ neighborhoods are

$$
U_m(q_\ast)=\{q_\ast\}\cup\{q_n:n\ge1,\ n\ge m\},
\qquad
U_m(q_n)=
\begin{cases}
\{q_n\},&n<m,\\
U_m(q_\ast),&n\ge m.
\end{cases}
\tag{69.17}
$$

For each fixed $m$, the singleton sets with $1\le n<m$ and the one remaining
tail set form the clopen prefix partition. At $m=0$ every neighborhood is
$Q$; at $m=1$ it is still $Q$, since all first coordinates are zero.

Take $\mathcal G=\mathcal B$, set $g_{q_\ast}=1$, $g_{q_n}=h_n$, and for
$N\ge1$ set

$$
g^{(N)}_{q_\ast}=1,
\qquad
g^{(N)}_{q_n}=\begin{cases}h_n,&n\le N,\\1,&n>N.\end{cases}
\tag{69.18}
$$

Because $\alpha_n\to0$,

$$
\sup_{q\in Q}\|g^{(N)}_q-g_q\|_1
\le2\sup_{n>N}\alpha_n\longrightarrow0.
\tag{69.19}
$$

For fixed $N$, the tail neighborhood contains only unit densities once $m>N$,
and the remaining singleton cylinders have common mass one. Therefore
$\Omega_{g^{(N)}}(m)=0$ for $m>N$.

In the limit, every $t\in[0,1)$ belongs to infinitely many $A_n$, hence for
every $m$ some $n\ge\max\{1,m\}$ has $h_n(t)=0$. Thus
$\underline g_m(q_\ast)=0$ on $[0,1)$ and $a_m(q_\ast)=0$, proving (69.14).
The endpoint $1$ is null. Changing representatives adds only a single null
union over the countably many densities and stages and leaves this calculation
unchanged.

For any fixed $m$, choose a partition block whose every index is at least
$\max\{1,m\}$, and choose $N$ at its last index. At that finite stage the
corresponding $h_n$ vanish collectively on all of $[0,1)$ inside
$U_m(q_\ast)$, so $\Omega_{g^{(N)}}(m)=1$. Consequently
$\sup_N\Omega_{g^{(N)}}(m)=1$ for each $m$, excluding any shared decaying
modulus. $\square$

Each finite stage has an exact cutoff and converges uniformly in TV to the
limit, but its cutoff depends on the stage. This failure does not contradict
Theorem 69.3, whose common bound (69.11) is absent. The local range conditions of
Section 68 are sufficient for sourcewise acquisition of continuous selections;
they do not replace a shared uniform or summable cost modulus.

**Corollary 69.5 (A calibration ladder with a retained expected-query bound).**
Use exactly the original-source, signature-cylinder and measurable handoff data
of Theorem 69.2. Let $P_{\mathcal R}$ be the density range of (68.8) for one
fixed supplied law range $\mathcal R$ of Theorem 68.5. For each $r\ge0$ let
$g^{(r)}:Q\to P_{\mathcal R}$ satisfy, for $\eta_r\in[0,1]$,

$$
\operatorname{TV}(g^{(r)}_q\sigma,\mu_y)\le\eta_r
\quad(y\in X,\ [y]=q),
\qquad\eta_r\to\eta.
\tag{69.20}
$$

Assume coordinatewise $L^1(\sigma)$ convergence to $g$, and (69.11) for one
summable nonincreasing $\varpi$ tending to zero. If the fixed law range
$\mathcal R$ is closed in TV, as supplied by Theorem 68.4, then
$g_q\in P_{\mathcal R}$, the limit satisfies the original target cap $\eta$,
and it has a lawful original-tape realization with

$$
\sup_{x\in X}\mathbb E[N_x]\le\sum_{m\ge0}\varpi(m).
\tag{69.21}
$$

**Proof.** The isometric image of the complete space
$L^1(\sigma|_{\mathcal G})$ is closed in $L^1(\sigma)$, and its nonnegative
integral-one subset is closed, as in Theorem 59.2. Thus each fixed $q$ has a
nonnegative $\mathcal G$-measurable limit representative of integral one.
The equality
$\operatorname{TV}(g^{(r)}_q\sigma,g_q\sigma)
=\tfrac12\|g^{(r)}_q-g_q\|_1$ shows that its law is the TV limit of elements
of the one closed range $\mathcal R$, so $g_q\in P_{\mathcal R}$.
For each original label $y$ with $[y]=q$,

$$
\operatorname{TV}(g_q\sigma,\mu_y)
\le\tfrac12\|g_q-g^{(r)}_q\|_1+\eta_r.
$$

Letting $r\to\infty$ gives the cap $\eta$ at every label, including all
labels sharing a signature. The coordinatewise $L^1$ part of Theorem 69.3
preserves (69.11); Theorem 69.2 then realizes exactly these limit laws on the
original tapes with the same static source and consumer, and proves (69.21).
Neither coordinatewise convergence nor closedness asserts an effective method
for selecting laws or evaluating their cylinder infima. $\square$

Closedness of the one fixed range gives the range-membership conclusion in this
ladder; varying ranges require a separate condition placing the limit laws in
the declared limit range. Pointwise cylinder exhaustion gives sourcewise
almost-sure handoff by Theorem 69.2, whereas a shared decaying modulus
and its summability give the respective uniform tail and expected-query bounds.
Theorem 68.5 alone supplies no such quantitative modulus. Without (69.11), even
uniform $L^1$ convergence and a finite cutoff at each stage do not preserve the
order conclusion, as Theorem 69.4 shows. With (69.11), coordinatewise $L^1$
convergence suffices.

The mature inputs are Radon--Nikodym domination and the countable probability
product on arbitrary measurable carriers, reused with their precise hypotheses
from Theorem 46.4, together with dominated convergence and Tonelli's theorem.
The lower-envelope literature cited in Sections 46 and 68 has its stated
stationary-chain or bounded-rate hypotheses; no conclusion requiring those
hypotheses is applied here. The original-source query bounds, shared-modulus
limit passage and fixed-range cap ladder are their combination in this
repository's prescribed acquisition problem, without a literature-priority
assertion. These conditional results do not settle Question 62.1 on unrestricted
measurable inputs and do not provide an effective sampler or modulus algorithm.

## 追加锚（本行以下为增补区）

## 70. Intrinsic uniform calibration and the exact cap versus query-tail frontier

**Definition 70.1 (Actual request cost and intrinsic selected-law modulus).**
Retain exactly the countable labeled source $X$, static integer $N(x)$,
prime enumeration $(p_i)$, zero advice and original-tape handoff semantics of
Definition 45.1 and Theorem 69.2. Only signatures of actual sources are
present. Write $C_m(x)$ for the occupied depth-$m$ prime-prefix cylinder,
including $C_0(x)=X$. A lawful preparation $A$ may choose arbitrary prime
addresses adaptively from its one shared seed and the actual preceding answers.
Let $K_{A,x}$ be the number of prime requests before finite handoff at $x$,
counting repetitions, and put $K_{A,x}=\infty$ on every nonhandoff branch,
even if that branch makes only finitely many requests. Define

$$
T_A(k)=\sup_{x\in X}\mathsf P\{K_{A,x}>k\},\qquad k\in\mathbb N_0.
\tag{70.1}
$$

Uniform tightness of actual request counts means $T_A(k)\to0$. It supplies
no deterministic ceiling on preparation transitions or requested prime indices.
The seed law has no dependence on the actual source.

For any selected family of probabilities $(\lambda_x)_{x\in X}$ on the
unchanged nonempty measurable tape carrier $(\Theta,\mathcal F)$, enumerate
the actual labels without repetitions and put

$$
\begin{aligned}
\tau_\lambda&=\sum_{i\ge1}2^{-i}\lambda_{x_i},
& f_x^\lambda&=\frac{d\lambda_x}{d\tau_\lambda},\\
\ell_C^\lambda&=\left(\inf_{x\in C}f_x^\lambda\right)\tau_\lambda,
& a_C^\lambda&=\ell_C^\lambda(\Theta),\\
\Omega_\lambda(m)&=\sup_{x\in X}\left(1-a_{C_m(x)}^\lambda\right).
\end{aligned}
\tag{70.2}
$$

Here $C$ is a nonempty occupied prefix cylinder; choose nonnegative measurable
versions of all the densities. The finite-measure
Radon--Nikodym and countable-infimum argument of Theorem 46.4 makes
$\ell_C^\lambda$ the intrinsic greatest common submeasure of
$\{\lambda_x:x\in C\}$. Thus its measure and mass do not depend on the
enumeration or density versions. This is the selected family's own tape
mixture, not a law on sources and not the original-target mixture $\sigma$.
In particular no assumption $\lambda_x\ll\sigma$ is imposed. Uniform order
calibration means $\Omega_\lambda(m)\to0$; when the selected laws satisfy
Definition 69.1 it is exactly its representative-independent modulus.

**Theorem 70.2 (Lawful adaptive uniform tightness and intrinsic order calibration).**
Use the measurable finite-record and output-event semantics of Definition
45.1, including a deterministic common rule after fixing the shared seed.
For the constructive direction retain the fixed shared tables and countable
product seed spaces permitted by Theorem 46.4.
For a lawful exact acquisition $A$ of $(\lambda_x)$, let
$I_{A,x,j}(s)$ be the prime index of its $j$th request, with value zero if
that request is never made. The value is defined by actual finite execution,
also on nonhandoff branches. For $k,m\in\mathbb N_0$ put

$$
J_{A,k,m}=\bigcup_{x\in X}\ \bigcup_{1\le j\le k}
                  \{s:I_{A,x,j}(s)>m\}.
\tag{70.3}
$$

This is one common measurable seed event, and for every fixed finite $k$

$$
J_{A,k,m}\downarrow\varnothing,\qquad
\mathsf P(J_{A,k,m})\longrightarrow0\quad(m\to\infty).
\tag{70.4}
$$

For every actual $x$ the finite measure obtained from its output on
$\{K_{A,x}\le k\}\setminus J_{A,k,m}$ is dominated by all
$\lambda_y$, $y\in C_m(x)$. Consequently

$$
\boxed{\Omega_\lambda(m)\le T_A(k)+\mathsf P(J_{A,k,m})}
\qquad(k,m\in\mathbb N_0).
\tag{70.5}
$$

For an arbitrary selected probability family on the original carrier, the
following two properties are equivalent: it has a lawful exact acquisition
with uniformly tight actual request counts; it is uniformly order-calibrated.
The constructive direction uses the positive-increment acquisition of
Theorem 46.4 and the tail calculation of Theorem 69.2, applied to the
selected family's own mixture (70.2). In that particular
acquisition the actual request count $L_x$ is a sequential prefix depth and

$$
\mathsf P\{L_x>m\}=1-a_{C_m(x)}^\lambda,\qquad
\sup_x\mathsf P\{L_x>m\}=\Omega_\lambda(m).
\tag{70.6}
$$

Uniform order calibration implies TV total boundedness of the selected range.
Total boundedness alone does not imply it, even for a lawfully acquired
finite range on the exact sources and tapes of Theorem 67.5. Summability of
$\Omega_\lambda$ supplies the uniform mean bound (69.5) for (70.6), but
is not necessary for a finite uniform mean of a different adaptive
acquisition. Actual request count and prefix depth therefore remain distinct.

**Proof.** For each $x,j,i\ge1$, the event that the $j$th request has index
$i$ is a countable union over its finite transition times and finite
prime-answer words of measurable finite-record events. This proves the
measurability of $I_{A,x,j}$, and countability of the actual $X$ proves that
of (70.3). Likewise $\{K_{A,x}\le k\}$ is the countable union of the
measurable finite-handoff events with at most $k$ requests.

Fix a seed $s$. Before the first request all actual sources have identical
processing, since the seed and zero advice are the only inputs. After a
request there are at most two answer branches. Between requests the common
rule has one determined continuation for each preceding answer word;
termination or infinite processing without another request adds no query
node. The possible $j$th requests across actual sources thus occupy at most
$2^{j-1}$ nodes, and their first $k$ requests use at most $2^k-1$ addresses.
Repetitions can only decrease the number of distinct addresses. This finite
set has a finite largest prime index, or is empty. Hence this seed belongs
to no $J_{A,k,m}$ once $m$ exceeds that index. This proves the setwise
decrease in (70.4), and continuity from above of the seed probability proves
its probability limit. Only branches followed by actual sources were used;
no infinite signature was made into an additional source.

The elementary fixed-seed binary-tree description is the decision-tree
background in Buhrman and de Wolf, [*Complexity Measures and Decision Tree
Complexity: A Survey*, Sections 3.1--3.2, Theoretical Computer Science
288(1), 21--43](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf).
The argument above uses finite branching through a fixed number of requests,
not their finite-Boolean-input complexity theorems. Random addresses and
unbounded processing between requests are retained.

On $E=\{K_{A,x}\le k\}\setminus J_{A,k,m}$ the actual finite execution at
$x$ uses only $P_m$. Every $y\in C_m(x)$ therefore follows exactly that
execution, with the same seed, and hands over exactly the same tape. This
is the whole-event induction of Lemma 45.3, with a request-count cutoff in
place of its joint transition/menu cutoff. For each $B\in\mathcal F$,

$$
\rho_{x,k,m}(B)=\mathsf P(E\cap\phi_x^{-1}(B))\le\lambda_y(B)
\quad(y\in C_m(x)),
\qquad
\rho_{x,k,m}(\Theta)\ge1-T_A(k)-\mathsf P(J_{A,k,m}).
\tag{70.7}
$$

The measurable output-event argument needs no measurable equality diagonal
on an arbitrary tape carrier. Greatestness of $\ell_{C_m(x)}^\lambda$ gives
(70.5). If $T_A(k)\to0$, choose $k$ first and then use (70.4) to obtain
$\Omega_\lambda(m)\to0$.

Conversely the last limit gives $a_{C_m(x)}^\lambda\uparrow1$ at every
actual $x$. Apply Theorem 46.4 to the family itself. Its positive node
increments $\ell_C^\lambda-\ell_{C^-}^\lambda$, a zero parent at the
depth-zero root, their normalized original-tape coordinates and an
independent uniform coordinate form one shared countable product seed.
The handoff thresholds and measurability are precisely those proved there
and in Theorem 69.2; their telescoping identity gives (70.6). Equal complete
signatures consequently have equal selected laws, whether or not that
equality was assumed initially. Every actual source has finite handoff
almost surely, with its original consumer on the same static source.

As an intermediate consequence, there are at most $2^m$ occupied
depth-$m$ cylinders. Select one actual representative $x_C$ in each.
For $y\in C$, both $\lambda_y$ and $\lambda_{x_C}$ dominate $\ell_C^\lambda$.
Subtracting this measure leaves two positive measures of the same mass
$1-a_C^\lambda$, so the event definition of TV gives

$$
\operatorname{TV}(\lambda_y,\lambda_{x_C})\le1-a_C^\lambda
\le\Omega_\lambda(m).
\tag{70.8}
$$

Thus these at most $2^m$ centers give a finite-prefix TV cover. This is the
common-submeasure/TV step of Lemma 45.3 and Theorem 46.4, not an optimal
coupling assertion on an arbitrary measurable carrier. A vanishing modulus
makes (70.8) a cover at every positive tolerance, proving total boundedness.

For the converse boundary take the unchanged tapes of Theorem 67.5 and
two distinct points $\theta_0,\theta_1\in B_1$. Set
$\lambda_x=\delta_{\theta_{n(x)\bmod2}}$, using its $n(x)$ from (67.15).
The deterministic preparation queries primes increasingly until the first
negative answer and then emits the indicated tape. Every actual integer
has finite prime support, so the handoff uses exactly $n(x)<\infty$
requests. The range consists of two probabilities and is totally bounded.
For each $m$, the cylinder whose first $m$ answers are positive contains
actual sources in both $D_{m+1}$ and $D_{m+2}$ by
[Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows). Its two
distinct point laws have zero common submeasure. Therefore
$\Omega_\lambda(m)=1$ for every $m$, and (70.5) excludes a uniformly
tight exact acquisition of this same finite family. This example preserves
the original tapes and consumer, and prescribes no new target problem.

For the mean boundary, retain these same two original tapes and put
$w_i=1/(i(i+1))$, $i\ge1$. One shared integer seed $I$ with probabilities
$w_i$ selects an actual prime $p_I$. Query it once and hand over
$\theta_{q_I(x)}$, where $q_i(x)=\mathbf1_{p_i\mid N(x)}$. This is the
single random-prime mechanism already used in (48.8)--(48.10), here with
the declared weights and two outputs. Its laws are

$$
\lambda_x=(1-u_x)\delta_{\theta_0}+u_x\delta_{\theta_1},
\qquad u_x=\sum_{i\ge1}w_iq_i(x),
\qquad K_{A,x}=1.
\tag{70.9}
$$

In a depth-$m$ cylinder set $c=\sum_{i\le m}w_iq_i(x)$ and
$r_m=\sum_{i>m}w_i=1/(m+1)$. The infimum of $u_y$ in that cylinder is
$c$, and its supremum is $c+r_m$. Indeed Theorem 35.2 realizes the fixed
prefix together with every finite subsequent all-negative or all-positive
answer word, and the remaining weight tends to zero. These are limits of
actual finite-pattern realizations, not assumed actual infinite words.
The greatest common submeasure therefore has masses $c$ on $\theta_1$
and $1-c-r_m$ on $\theta_0$, giving

$$
\Omega_\lambda(m)=r_m=\frac1{m+1}\longrightarrow0,
\qquad \sum_{m\ge0}\Omega_\lambda(m)=\infty.
\tag{70.10}
$$

Every source nevertheless has expected actual request count one in (70.9).
For the specified prefix acquisition (70.6), every source instead has
infinite expected depth by Tonelli's tail-sum identity. Thus summability is
an additional sufficient mean condition for that prefix acquisition,
not a necessary condition for uniform finite mean under adaptive queries.
No source law, advice, reset or selection of a source enters either example.
The intrinsic/adaptive correspondence combines the cited finite-record and
lower-envelope ingredients in the prescribed source model; it asserts no
effective evaluation of cylinder tables or sampling of arbitrary tape laws
from a single real random variable. $\square$

**Theorem 70.3 (Exact original-input cap versus actual query-tail frontier).**
Fix any $h\in(0,1)$ and allowed profile $b$, and take exactly the source,
carrier, consumer and target laws (67.15)--(67.18) of Theorem 67.5. Let
$\mathcal A_\eta$ consist of all lawful preparations of Definition 45.1
whose prepared laws $\lambda_x$ satisfy
$\sup_x\operatorname{TV}(\lambda_x,\mu_x)\le\eta$.
No target-row, support, density, likelihood-algebra or proportional-containment
condition is imposed on these prepared laws. Then $\mathcal A_\eta$ is empty
for $0\le\eta<h$, and for every $\eta\in[h,1]$ and finite $k\ge0$

$$
\boxed{\min_{A\in\mathcal A_\eta}\ \sup_{x\in X}
                  \mathsf P\{K_{A,x}>k\}=1-\eta.}
\tag{70.11}
$$

For each $\eta$ one preparation attains (70.11) simultaneously at every
finite horizon. More quantitatively, for every $A\in\mathcal A_\eta$,
$k\ge0$, integer $r\ge2$ and $\delta>0$, there are $r$ actual sources
$x_j\in D_{n_j}$, with distinct $n_j>m$ for some finite $m$, all having
positive answers on the first $m$ primes, such that

$$
\boxed{\max_{1\le j\le r}\mathsf P\{K_{A,x_j}>k\}
       \ge1-\frac{r\eta}{r-1}-\delta.}
\tag{70.12}
$$

One may use any $m$ with $\mathsf P(J_{A,k,m})<\delta$, then any distinct
$n_j>m$ and actual representatives of their occupied $D_{n_j}$.
For every lawful cap-$\eta$ family its intrinsic modulus also satisfies

$$
\Omega_\lambda(m)\ge1-\eta\qquad(m\in\mathbb N_0).
\tag{70.13}
$$

When $\eta<1$, every $A\in\mathcal A_\eta$ has
$\sup_x\mathbb E[K_{A,x}]=\infty$. An attainer $A_\eta$ can nevertheless
have finite expectations separately at every actual source, with

$$
(1-\eta)n(x)\le\mathbb E[K_{A_\eta,x}]
\le(1-\eta)\left(n(x)+\frac32\,3^{-n(x)}\right)<\infty.
\tag{70.14}
$$

At $\eta=1$ this attainer uses zero requests. The minimization and the
universal lower bounds count actual adaptive requests, including repetitions;
they do not require competitors to query a sequential prefix.
For this attainer equality holds in (70.13) at every depth.

**Proof.** First extend the whole-event argument in the last part of
Theorem 67.5 to an arbitrary cap $\eta$. Fix $x\in D_n$. For every
$\ell\ge n$, Theorem 35.2 supplies an actual
$y_\ell\in C_\ell(x)$ with $j_\ell=\Omega(y_\ell)>\ell$.
Lemma 45.3 gives $\lambda_{y_\ell}\to\lambda_x$ in TV.
Since the original target at $y_\ell$ assigns mass one to
$B_n\sqcup P_{j_\ell}$, the cap gives

$$
\lambda_{y_\ell}(B_n)+\lambda_{y_\ell}(P_{j_\ell})\ge1-\eta.
\tag{70.15}
$$

For the fixed probability $\lambda_x$, disjointness of the $P_j$ implies
$\lambda_x(P_j)\to0$ as $j\to\infty$. The TV comparison therefore makes
the second term of (70.15) tend to zero and gives

$$
\lambda_x(B_{n(x)})\ge1-\eta\qquad(x\in X).
\tag{70.16}
$$

This argument compares measurable events and finite-record submeasures only;
it includes singular prepared laws. Testing the separate event $P_{j_\ell}$
also gives $\lambda_{y_\ell}(P_{j_\ell})\ge h-\eta$. Its limit zero forces
$\eta\ge h$, in agreement with the original $R_\mu=h$ of Theorem 67.5.
Thus smaller caps are infeasible without any change of input or consumer.

For the finite-source bound fix $A,k,r,\delta$ and choose $m$ by (70.4).
Let $C$ be the actual cylinder with its first $m$ answers positive.
Choose distinct $n_1,\ldots,n_r>m$ and actual $x_j\in D_{n_j}$ by
Theorem 35.2; each belongs to $C$. On $J_{A,k,m}^c$, induction over
the common execution shows that all these sources either hand off within
$k$ requests with the same tape or all fail to hand off within $k$ requests.
In the former case the entire finite record uses only $P_m$.
Let $E$ be this common handoff event intersected with $J_{A,k,m}^c$, and
let $\rho$ be its output submeasure of mass $p=\mathsf P(E)$.
It is dominated by every $\lambda_{x_j}$, as in (70.7). By (70.16),

$$
\rho(\Theta\setminus B_{n_j})\le\eta\quad(1\le j\le r),
\qquad
(r-1)p\le\sum_{j=1}^r\rho(\Theta\setminus B_{n_j})\le r\eta.
\tag{70.17}
$$

The middle inequality holds because the disjoint $B_{n_j}$ contain any tape
at most once. For each $j$, handoff within $k$ on $J_{A,k,m}^c$ has mass
$p$, so

$$
\mathsf P\{K_{A,x_j}>k\}\ge1-p-\mathsf P(J_{A,k,m})
\ge1-\frac{r\eta}{r-1}-\delta.
$$

This proves (70.12), using only finitely many actual comparison sources.
Let $r\to\infty$ and $\delta\downarrow0$ in the supremal bound to obtain
$T_A(k)\ge1-\eta$ for each finite $k$. No source was chosen after
observing an individual seed.

The same finite sum applies to the intrinsic meet $\ell_C^\lambda$ on
the first-$m$-positive cylinder, using the chosen actual sources for every
$r\ge2$. It gives $a_C^\lambda\le r\eta/(r-1)$ for all $r$, hence
$a_C^\lambda\le\eta$. This proves (70.13). In particular no cap below one
permits uniform order calibration. It is also consistent with (70.5):
fixing $k$ and letting $m\to\infty$ there recovers the same cost lower
bound. The finite-event proof above additionally gives the actual witnesses
and quantitative estimate (70.12).

For attainment, use the original nonproposal block laws $\nu_x$ from
(67.17)--(67.18), without reading the infinite parameter $t(x)$ as input.
Let $a_C^\nu$ be their intrinsic common masses. If $m<n(x)$, the
cylinder $C_m(x)$ has only positive prefix answers and contains actual
sources in two distinct $D_n$. Their $\nu$ laws lie on disjoint original
blocks, so $a_{C_m(x)}^\nu=0$. If $m\ge n(x)$, that block is fixed and
(67.19)--(67.20) give

$$
a_{C_m(x)}^\nu\ge e^{-3^{-m}},\qquad
1-a_{C_m(x)}^\nu\le1-e^{-3^{-m}}\le3^{-m}.
\tag{70.18}
$$

Thus these masses exhaust one at each actual source. The positive-increment
preparation of Theorem 46.4, with the tail identity recalled in (70.6),
acquires $\nu_x$ exactly. Write $L_x$ for its number of actual prefix
requests. It has $\mathsf P\{L_x>m\}=1$ for $m<n(x)$ and the bound
(70.18) thereafter. For each finite $k$, an actual source in $D_{k+1}$
has $\mathsf P\{L_x>k\}=1$, and hence

$$
\sup_x\mathsf P\{L_x>k\}=1,\qquad
n(x)\le\mathbb E[L_x]\le
n(x)+\sum_{m\ge n(x)}3^{-m}
=n(x)+\frac32\,3^{-n(x)}.
\tag{70.19}
$$

The expectation bounds use Tonelli's tail-sum identity, not an interchange
of supremum and infinite sum.

Choose one fixed original tape $\theta_0\in B_1$ and extend the same
product seed by one independent uniform coordinate $V\in(0,1)$.
For $V<\eta$ hand over $\theta_0$ immediately; otherwise use the preceding
exact acquisition of $\nu_x$. This is one seed and one common rule at
every actual source. Its law is

$$
\lambda_x^\eta=(1-\eta)\nu_x+\eta\delta_{\theta_0}.
\tag{70.20}
$$

For $\eta\ge h$, subtract the common measure $(1-\eta)\nu_x$ from
both (70.20) and the original target
$\mu_x=(1-h)\nu_x+h\pi_{\Omega(x)}$. The remaining positive measures
are $\eta\delta_{\theta_0}$ and
$(\eta-h)\nu_x+h\pi_{\Omega(x)}$, each of mass $\eta$.
Their discrepancy on every event is at most $\eta$. On the measurable
singleton $\{\theta_0\}$ it equals $\eta$, since all original targets
and $\nu_x$ are nonatomic. Consequently the cap is exactly $\eta$.
This also exhibits a lawful singular competitor: for $\eta>0$ its atom
has positive mass, while the original-target mixture gives that singleton
mass zero. Original-mixture domination was neither assumed nor manufactured.

The atom $\delta_{\theta_0}$ is singular to every $\nu_x$, so its cylinder
common measures are
$\ell_C^{\lambda^\eta}=\eta\delta_{\theta_0}+(1-\eta)\ell_C^\nu$.
Indeed the common atom has that mass in every law, and the remaining
nonatomic part must be dominated by every $(1-\eta)\nu_x$.
By independence and (70.19), the request tail and intrinsic modulus are

$$
\mathsf P\{K_{A_\eta,x}>k\}=(1-\eta)\mathsf P\{L_x>k\},
\qquad
T_{A_\eta}(k)=\Omega_{\lambda^\eta}(k)=1-\eta\quad(k\ge0).
\tag{70.21}
$$

This proves the attained minimum at all horizons simultaneously, and
(70.19) proves (70.14). At $\eta=1$ only the zero-query branch has mass.
Every positive-mass tape coordinate in the other branch is an original-tape
increment law from Theorem 46.4. Its finite records and output-event
preimages are measurable; adjoining the independent interval event in $V$
preserves this property. Handoff is finite almost surely separately at
every actual source. The unchanged consumer receives only that original
tape and runs on the unchanged static source. No $n(x)$, $t(x)$,
$\Omega(x)$, source label, magnitude promise, source sampling, restart or
failure conditioning is supplied to the preparation.

Finally, for every $A\in\mathcal A_\eta$ and finite $k$, the universal
lower bound and the elementary nonnegative-cost inequality give

$$
\sup_x\mathbb E[K_{A,x}]\ge(k+1)\sup_x\mathsf P\{K_{A,x}>k\}
\ge(k+1)(1-\eta).
\tag{70.22}
$$

When $\eta<1$ this diverges as $k\to\infty$, proving the asserted
infinite supremal mean even though (70.14) is finite at every fixed source.
The cap/count synthesis (70.11)--(70.22) and the adaptive/intrinsic
correspondence use the exact previously specified input and the mature
common-measure, finite-branching and tail-sum steps cited above. They are
repository-relative deductions, not a literature-priority claim. The
source-specific likelihood specification and sharp cap are reused from
Theorem 67.5, not introduced as another example. Neither these cost
identities nor their measurable common-seed realizations settle Question
62.1 for unrestricted original measurable inputs, or assert an effective
sampler, a computable modulus or a bound on all preparation transitions.
$\square$

## 追加锚（本行以下为增补区）
