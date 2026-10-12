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
