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
