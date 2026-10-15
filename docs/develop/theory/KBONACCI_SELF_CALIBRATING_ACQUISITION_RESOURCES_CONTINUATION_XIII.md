# Self-Calibrating Acquisition Resources — Continuation XIII

> This volume is ordinary mathematical reference input. Its definitions,
> theorems and proofs carry no assertion of Lean/kernel verification.
> The document uses the `generic-v1` theory convention: existing text is
> preserved, and additions start after the final append anchor and end
> with a new anchor. Mathematical truth in the repository is carried by
> verified Lean declarations, rather than by this prose.

## 219. Joint column reserves, unrestricted retraction and sharp signed faces

The owning full-score interfaces are
[Continuation XII, 216.1 and 218.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XII.md).
This section gives a three-positive stock face beginning at address 3,
a retraction of an entire separated-sign least-stock fiber, one
column-dependent reserve construction, two four-positive applications
and a family with a matching positive-excess lower bound.
Each result states its own domain. Exact quotient preservation is a
sufficient choice in these constructions; the unrestricted comparison
also permits changed quotients and one signed residual.

### 219.1 Full objects and the common budget

**Definition 219.1 (Words, rewards and complete supports).**
For an integer $L\ge3$, let $B_L=\{0,1\}^L$, $w_+=1^L$ and
$\Omega_n=\{w\in B_L:n(w)=n\}$, where $n(w)$ is the first zero
of $w\ne w_+$. All multiple-zero words remain in the domain.
Write $w(Z)$ for the word whose zero set is exactly $Z\subseteq\{1,\ldots,L\}$.
A full score $V$ has independent coefficients $A_w,C_w,P_w,T\ge0$ and rewards

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
 +P_w\mathbf1_{\ell\in\{0,n(w)\}},\qquad
g_V(w_+,\ell)=T\mathbf1_{\ell=0}.
\tag{219.1}
$$

Every cell permits every label $0,\ldots,L$, including labels earlier
than both queries and unqueried labels. The complete catalogs contain
empty schedules, singletons and every distinct pair $i<j$.
An N pair observes $00,01,10,11$; an increasing O pair observes
$0,10,11$, merging the first two N cells before maximizing.
The notation $(i,j;o_0,o_{10},o_{11})$ denotes the entire stopped table.
Reversing an N pair permutes its cells; repeated requests have singleton
information. These statements about information do not reduce the
number of actual requests. Set

$$
\begin{aligned}
B_{\mathcal C}(V)
 &=\max_{D\in\mathcal D_{\mathcal C}}\sum_{w\in B_L}g_V(w,D(w)),
 &&\mathcal C=N,O,\\
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(V)&=B_{\mathcal C}(V)-W_V,\\
\beta_n(V)&=\sum_{\Omega_n}(C_w-A_w),\qquad
K_V=\sum_w(A_w+C_w+P_w)+T,\qquad Q(V)=(\beta(V),K_V).
\end{aligned}
\tag{219.2}
$$

Equivalently, for each schedule sum its cellwise all-label maxima,
then maximize over schedules. Unspecified coefficients vanish;
coincident contributions add. No zero coefficient deletes an event row.
For class totals $A_n,C_n$, the reused stock identities are

$$
K_V-\sum_n|\beta_n|=2\sum_n\min(A_n,C_n)+\sum_wP_w+T,
\qquad W_V=Z_V+\beta_1+\beta_2,
\quad Z_V=\sum_wA_w+\sum_wP_w+T.
\tag{219.3}
$$

If $G=\sum_n(\beta_n)_+$ and $D=\sum_n(-\beta_n)_+$,
absolute stock is $K-G-D$ and literal reserve is $K-G$.
They differ by $D$ and neither is a probability budget.
The legal anchor $R=(1,2;1,2,0)$ gives $\Delta_N\ge\Delta_O\ge0$.
The constant-zero table gives $B_{\mathcal C}\ge Z_V$.

**Definition 219.2 (One residual and the same feasible configuration).**
Put $\alpha=(1,1,0,\ldots,0)$ and use the existing hull

$$
\begin{aligned}
H_L=\{(b,e):&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{n\ge3}b_n,\quad
 b_1+\sum_{n\ge3}b_n-(L+1)e\le1\},\\
F_{(\beta,K)}(b,e)&=\sum_n\beta_n(b_n-\alpha_n)-Ke,
\qquad \sigma_{H_L}(q)=\max_{H_L}F_q.
\end{aligned}
\tag{219.4}
$$

At every $w\in\Omega_n$, the independent base, correct and pair
demands are respectively $1-b_n-e$, $b_n-e$, $1-e$.
At $w_+$ the base demand is $1-e$. Negative singleton demands are
retained. Let $d$ be this complete demand vector, $z_D$ the complete
event vector of a table, $r=z_R=d(\alpha,0)$, $h=d-r$ and
$G_N=(z_D-r)_{D\in\mathcal D_N}$. Define

$$
H_N=\{(b,e)\in H_L:\exists\lambda\ge0,
                   \ G_N\lambda\ge h(b,e)\}.
\tag{219.5}
$$

The vector $\lambda$ is on whole tables and has mass $M=\sum_D\lambda_D$.
It is a probability configuration only when appropriately normalized;
an affine vector of mass greater than one is not executed as a law.
For an actual full input $y\ge0$ with $\Delta_O(y)\le1$, a sufficient
certificate is one full $V\ge0$ and one $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\tag{219.6}
$$

Indeed, at the same $(b,e)\in H_N$ and the same full feasible $\lambda$,

$$
F_{Q(y)}(b,e)\le V\cdot h(b,e)+\theta
 \le V\cdot G_N\lambda+\theta
 \le M\Delta_N(V)+\theta\le\max(1,M).
\tag{219.7}
$$

Here $V\cdot h=F_{Q(V)}$ and each column pairing is at most
$\Delta_N(V)$. All rows are paid on this same object.
Membership in $H_L$ alone supplies no feasible $\lambda$.
No quotient, baseline, unary, suffix, support or terminal coefficient
must be preserved in the unrestricted search. Nonzero zero-cost $V$
remain allowed at $\theta=1$. Equations (219.3)–(219.7) are reused
interfaces, rather than separate mathematical increments.

### 219.2 A three-positive stock face beginning at address 3

**Theorem 219.3 (Gapped unequal positives and four conversion capacities).**
Choose addresses
$1,2,3,i,m,j,\ell\in\{1,\ldots,L\}$ with
$3<i<m<j<\ell\le L$. Let $a,b,c\ge0$ and put

$$
\begin{aligned}
g&=2a+b+c,& h&=a+2b+c,& k&=a+b+2c,\\
G&=g+h+k,& B_0&=2g+h+k=6a+5b+5c,\\
s&=2a+\tfrac32b+\tfrac32c,& t&=a+b+c.
\end{aligned}
\tag{219.8}
$$

Equivalently, $g,h,k\ge0$ satisfy
$3g\ge h+k$, $3h\ge g+k$, $3k\ge g+h$,
with $a=(3g-h-k)/4$ and cyclic formulas for $b,c$.
Unless all vanish, all three are positive.
Prescribe $\beta_3=g$, $\beta_m=h$, $\beta_\ell=k$ and
$\beta_r=-\xi_r\le0$ at every other address. Set

$$
D=\sum_{r\notin\{3,m,\ell\}}\xi_r,\quad E=\xi_1+\xi_2,
\quad K=G+D+B,\quad B\ge0,
\quad J_0=\min(\xi_1,s)+\min(\xi_2,s)+\min(\xi_i,t)+\min(\xi_j,t).
\tag{219.9}
$$

If $B\ge B_0-J_0$, one full score with $T=0$ attains both
unrestricted exact-$Q$ minima, and both minima equal $E$.
Every full competitor at this $Q$ satisfies

$$
\Delta_N\ge\Delta_O\ge
 E+\max\{0,(B_0-B-D)/3\}.
\tag{219.10}
$$

If the debts are supported on $\{1,2,i,j\}$ and bounded there by
$(s,s,t,t)$, a cost-$E$ representative exists in either catalog
if and only if $B\ge B_0-D$. In particular, with no debt, zero cost
is attainable exactly when $B\ge B_0$.
No formula for the entire positive-cost minimum below this face is asserted.

**Proof.** First construct three rational cores $U_1,U_2,U_3$.
In the following table words use skeleton order $(1,2,3,i,m,j,\ell)$;
every other bit is one. An early entry is a $P$ atom and includes
its $01\leftrightarrow10$ swap in the first two bits, with equal mass
and the same five-bit suffix. A late entry is one $P$ atom; a correct
entry is one $C$ atom. Each core has $A=T=0$.

| Core | Early $P$ entries, before the swap | Late $P$ entries | Correct $C$ entries |
| --- | --- | --- | --- |
| $U_1$ | $0100100:1/2$; $0100111:1/6$; $0101001:1/3$; $0101010:2/3$; $0101111:1/3$ | $1110010:2/3$; $1110011:1/3$; $1111100:2/3$; $1111101:1/3$ | $1101010:2$; $1111001:2/3$; $1111010:1/3$; $1111110:1$ |
| $U_2$ | $0100110:1/4$; $0101001:1/4$; $0101010:1/4$; $0101111:1/4$; $0111010:1/4$; $0111011:1/4$ | $1110001:1$; $1111100:1$ | $1101010:1$; $1111001:3/2$; $1111010:1/2$; $1111110:1$ |
| $U_3$ | $0101001:1/2$; $0101110:1/2$; $0111111:1/2$ | $1110010:1$; $1111100:1$ | $1101010:1$; $1111001:1$; $1111110:2$ |

Their correct-class totals at skeleton positions $(3,5,7)$ are
$(2,1,1)$, $(1,2,1)$, $(1,1,2)$, and their $P$ totals are $6,5,5$.
Thus $U=aU_1+bU_2+cU_3$ has correct totals $(g,h,k)$,
$P$ total $B_0$ and $P$ first-zero totals $(s,s,t,t)$ at
actual addresses $(1,2,i,j)$. No pivot class has $P$ mass.

Every nonpivot numerical-label reward is a pointwise subset of the
zero-label $P$ reward. For pivot labels it suffices to check
$P(H)\ge\max(C_3(H),C_m(H),C_\ell(H))$ in each cell $H$.
Here are these exact margins for each core; tuples use N cell order
$00,01,10,11$ and pair indices are skeleton positions.

| Pair | $U_1$ margins | $U_2$ margins | $U_3$ margins |
| --- | --- | --- | --- |
| $(1,2)$ | $(0,2,2,0)$ | $(0,3/2,3/2,0)$ | $(0,3/2,3/2,0)$ |
| $(1,3)$ | $(2,0,0,1)$ | $(1,1/2,0,1/2)$ | $(1,1/2,0,1/2)$ |
| $(1,4)$ | $(2/3,4/3,5/3,1/3)$ | $(1/4,5/4,5/4,1/4)$ | $(0,3/2,1,1/2)$ |
| $(1,5)$ | $(1,1,0,1)$ | $(1,1/2,0,1/2)$ | $(1/2,1,1/2,0)$ |
| $(1,6)$ | $(5/6,7/6,7/6,1/6)$ | $(1/4,5/4,3/4,1/4)$ | $(1/2,1,1/2,0)$ |
| $(1,7)$ | $(7/6,5/6,1/2,5/6)$ | $(3/4,3/4,3/4,1/4)$ | $(1/2,1,1/2,0)$ |
| $(3,4)$ | $(4/3,2/3,1,0)$ | $(1/2,1/2,1,0)$ | $(0,1,1,0)$ |
| $(3,5)$ | $(0,2,0,0)$ | $(0,1,0,0)$ | $(0,1,0,0)$ |
| $(3,6)$ | $(5/3,1/3,1/3,0)$ | $(1/2,1/2,1/2,0)$ | $(1,0,0,0)$ |
| $(3,7)$ | $(1/3,5/3,1/3,0)$ | $(0,1,1/2,0)$ | $(0,1,0,0)$ |
| $(4,5)$ | $(1,4/3,0,2/3)$ | $(1,1/2,0,1/2)$ | $(1,0,0,1)$ |
| $(4,6)$ | $(1,4/3,1,0)$ | $(1,1/2,0,1)$ | $(0,1,1,0)$ |
| $(4,7)$ | $(5/3,2/3,0,1)$ | $(1/2,1,1,0)$ | $(1,0,0,1)$ |
| $(5,6)$ | $(0,1/3,2,0)$ | $(0,1/2,1,0)$ | $(0,0,1,0)$ |
| $(5,7)$ | $(0,1/3,2/3,4/3)$ | $(0,1/2,1/2,1/2)$ | $(0,0,0,1)$ |
| $(6,7)$ | $(5/3,1/3,0,4/3)$ | $(1,0,1/2,1)$ | $(1,0,0,1)$ |

The pairs $(2,r)$ for $r\ge3$ have the $(1,r)$ margins by the swap
symmetry. These rows exhaust all skeleton pairs. Separate inequalities
$P(H)\ge C_v(H)$ are linear, so nonnegative combinations preserve them.
Inactive queries are constant one on the support; their partitions,
singletons and the empty schedule are coarser than covered pairs.
Summing the separate inequalities preserves dominance under coarsening,
including the stopped merge. Thus $B_N(U)=B_O(U)=B_0$.
The table is an exact finite base calculation, followed by a proof for
all nonnegative parameters and all order-preserving skeleton embeddings.

For $r=1,2,i,j$ let $\kappa_r=s,s,t,t$ and
$\eta_r=\min(\xi_r,\kappa_r)$. Convert the fraction
$\eta_r/\kappa_r$ of every core $P$ atom in class $r$ to $A$ at
the same word. If $\kappa_r=0$, then $\eta_r=0$ and no division occurs.
For every nonpivot $r$, add $\xi_r-\eta_r$ of $A$ at $w(\{r\})$,
taking $\eta_r=0$ off the four conversion classes.
Finally add $B-(B_0-J_0)$ of $P$ at $w(\{1\})$.

Conversion preserves zero reward and decreases only that class's
numerical reward. An added $A$ increases only zero reward; added $P$
increases zero and its own numerical label equally.
All cellwise inequalities therefore persist. The resulting single score
has totals $A=D$, $C=G$, $P=B$, $T=0$ and hence
$Q=(\beta,K)$, $Z=B+D$, $W=Z-E$ and $B_N=B_O=Z$.
Both costs equal $E$. This includes exhausted capacities and equality
$B=B_0-J_0$.

For the unrestricted lower bound, use three legal O tables

$$
S_1=(1,3;0,3,0),\quad S_2=(2,3;0,3,0),\quad
J=(3,m;0,m,\ell).
\tag{219.11}
$$

On first-zero class 3 their outputs are two 3s and one 0;
on classes $m,\ell$ the correct label occurs once and zero twice.
On every other first-zero class at most one of the three outputs is
nonzero. For class 1 or 2, if bit 3 is zero then $J$ outputs zero
and at most the other early table outputs 3; if bit 3 is one, both
early tables output zero. At every class beyond 3 both early tables
output zero. The positive word also has only one nonzero output.
These cases include every suffix, intermediate class and multiple zero.
The exhaustion label $\ell$ in $J$ is a legal unqueried output.

Let $I_+=\{3,m,\ell\}$. Subtracting $3Z$ from the three rewards gives
pivot contribution $2\beta_3+\beta_m+\beta_\ell=B_0$;
their $P$ contributions cancel. Off $I_+$ the contribution is at least
$-A_w-P_w$, and at $w_+$ it is $-T$.
Consequently $3(\Delta_O-E)\ge B_0-(A_{\rm out}+P_{\rm out}+T)$.
For an arbitrary full competitor the class identities imply

$$
A_{\rm out}+P_{\rm out}+T
 =B+D-2A_{I_+}-(A_{\rm out}-D)-P_{I_+}\le B+D,
\tag{219.12}
$$

because $A_{\rm out}-D=C_{\rm out}\ge0$.
Constant zero separately gives $\Delta_O\ge E$.
Together with $\Delta_N\ge\Delta_O$ this proves (219.10).
On the capped four-debt subface $J_0=D$, construction and lower bound
match exactly at $B_0-D$ and exclude cost $E$ below it. ∎

**Example 219.4 (A full input gap with a same-quotient repair).**
Take $L=7$ and the consecutive seven-position skeleton, with
$(a,b,c)=(1,2,3)$. Then $(g,h,k)=(7,8,9)$,
$B_0=31$, $s=19/2$, $t=6$.
Choose $(\xi_1,\xi_2,\xi_4,\xi_6)=(1/2,1/2,6,6)$,
$D=J_0=13$, $E=1$, $B=18$.
The construction has

$$
Q(V)=((-1/2,-1/2,7,-6,8,-6,9),55),\quad
T=0,\quad Z=31,\quad W=30,\quad
(\Delta_N(V),\Delta_O(V))=(1,1).
\tag{219.13}
$$

Move all correct mass 7 at $1101010$ to $1100010$, leaving every
other coefficient unchanged, and call the result $Y$.
Its first-zero class, $Q$, $W$ and $T$ stay fixed.
Only pairs involving position 4 change. Their margins, defined as
zero reward minus the largest pivot-correct reward, are:

| Pair | N margins in $00,01,10,11$ | O margins in $0,10,11$ |
| --- | --- | --- |
| $(1,4)$ | $(7/6,25/3,1/6,16/3)$ | $(19/2,1/6,16/3)$ |
| $(2,4)$ | $(7/6,25/3,1/6,16/3)$ | $(19/2,1/6,16/3)$ |
| $(3,4)$ | $(-14/3,35/3,6,2)$ | $(7,6,2)$ |
| $(4,5)$ | $(-1,7/3,1,14/3)$ | $(4/3,1,14/3)$ |
| $(4,6)$ | $(3,-5/3,4,3)$ | $(4/3,4,3)$ |
| $(4,7)$ | $(-4/3,8/3,3,4)$ | $(4/3,3,4)$ |

Other numerical labels remain dominated by zero. The O margins are
nonnegative and the largest total N cell excess is $14/3$.
Short schedules are coarser than these pairs. Therefore
$B_O(Y)=31$, $B_N(Y)=107/3$ and the costs are $(17/3,1)$.
Returning that one correct mass gives the affordable certificate $(V,0)$.
This is a full-score input gap with a repair, rather than an original
acquisition separation.

### 219.3 Retraction of a whole least-stock fiber

**Theorem 219.5 (Separated-sign unrestricted retraction).**
Let $I,J\subseteq\{1,\ldots,L\}$ be disjoint,
$|I|,|J|\ge3$ and $\max I<\min J$.
Let $d_i\ge0$, $\gamma_j>0$, $D=\sum_I d_i$, $G=\sum_J\gamma_j$,
and prescribe $\beta=-d$ on $I$, $\beta=\gamma$ on $J$, zero elsewhere,
$K=D+G$. Put $E=\sum_{i\in I\cap\{1,2\}}d_i$.
On every full score in this exact-$Q$ fiber perform two resets:
set all inactive bits outside $I\cup J$ to one; then, in each $A$ atom
of class $i$, set every other $I$ bit to one. Sum coincident coefficients.
This is an idempotent nonnegative linear pushforward $\rho$ with

$$
Q(\rho V)=Q(V),\quad W_{\rho V}=W_V,\quad
B_N(\rho V)\le B_N(V),\quad B_O(\rho V)\le B_O(V).
\tag{219.14}
$$

Each unrestricted fiber minimum is attained in the retract.
This assertion does not identify the N and O minima or their minimizers.

**Proof.** Zero absolute stock in (219.3) forces $P=T=0$ and no
class cancellation: only $A$ in $I$ with totals $d_i$, and only $C$
in $J$ with totals $\gamma_j$, can occur. Thus $W=D-E$.
Both resets preserve first zeros, nonnegativity and these totals;
performing them twice changes nothing.

For the inactive reset, any table on the new score can be simulated on
the old score by deleting inactive queries and inserting reply one in
its output table. The remaining schedule is legal and has at most two
requests. For O it remains increasing and stops at its first queried
zero. Output labels are untouched. Every new reward is therefore at
most the corresponding old support.

For the guard reset, fix an observation partition $\Pi$ and let
$A(H)$ and $C_j(H)$ be masses in its cell $H$.
The exact optimized table reward on this forced-stock face is

$$
D+\sum_{H\in\Pi}\bigl(\max_{j\in J}C_j(H)-A(H)\bigr)_+.
\tag{219.15}
$$

Label zero earns $A(H)$, label $j$ earns $C_j(H)$ and other labels
earn zero; thus (219.15) retains the complete label maximum.
Every $C$ word has all guard bits one. With no guard query, the reset
changes no cell. With one guard query, moved $A$ leaves a guard-zero
cell with no $C$ and enters a guard-one cell with the same other reply.
Its departure loses no surplus and its arrival can only reduce surplus.
This includes the stopped guard-zero cell. With two guard queries,
only cell 11 contains $C$ and its $A$ mass can only increase.
All other cells remain $C$-free. These cases cover both full catalogs,
including singletons, empty schedules and constant inactive queries.
They prove the two support inequalities.

The full fiber is nonempty, closed and bounded in finitely many
nonnegative coefficients with sum $K$. Both supports are continuous
maxima of finitely many linear functions, so each attains its minimum.
Retracting an unrestricted minimizer gives an equally good retracted
minimizer. This proves separate attainment, without a common-minimizer
assertion. ∎

**Theorem 219.6 (One exact joint suffix relation).**
Under Theorem 219.5, let $v\in\{0,1\}^{|J|}$ denote the bits on
$J$ in address order. Use one collection of nonnegative measures
$u_i(v),z_j(v)$ with

$$
\sum_vu_i(v)=d_i,\quad \sum_vz_j(v)=\gamma_j,\quad
z_j(v)=0\text{ unless the first zero of }v\text{ is at }j.
\tag{219.16}
$$

The $u_i$ atom has sole guard zero $i$; every $z_j$ atom has all guard
bits one. Inactive bits are one. All suffix patterns, including the
all-one $A$ suffix, remain. Put $U=\sum_i u_i$,
$\mu=\max_j\gamma_j$ and $R(H)=\max_j\sum_{v\in H}z_j(v)$.
For $\mathcal C=N,O$, define $\Psi_{\mathcal C}$ to be the maximum
of zero and all the following quantities, on this same allocation:

$$
\begin{aligned}
& (\mu-D+d_i+d_h)_+ &&(i\ne h\in I),\\
& \sum_{t=0,1}\bigl(R\{v:v_a=t\}-(U-u_i)\{v:v_a=t\}\bigr)_+
 &&(i\in I,\ a\in J),\\
& \sum_{H\in\Pi_{\mathcal C}(a,b)}(R(H)-U(H))_+
 &&(a<b\text{ in }J).
\end{aligned}
\tag{219.17}
$$

Here $\Pi_N(a,b)$ has the four bit cells and $\Pi_O(a,b)$ has
$v_a=0$, $(v_a,v_b)=(1,0)$, $(v_a,v_b)=(1,1)$.
Then

$$
\min_{V\ge0:\,Q(V)=(\beta,D+G)}\Delta_{\mathcal C}(V)
 =E+\min_{(u,z)\text{ satisfying }(219.16)}\Psi_{\mathcal C}(u,z),
\tag{219.18}
$$

and both minima are attained. A full representative of cost at most
$b$ exists exactly when $b\ge E$ and one allocation satisfies all
quantities in (219.17) at most $b-E$.

**Proof.** The retract in Theorem 219.5 is parametrized exactly by
(219.16). A pair of guards $i,h$ has all $C$ in 11 and $A$ mass
$D-d_i-d_h$ there, giving the first line of (219.17).
For guard $i$ and positive address $a$, the guard-zero cell contains
only $A_i$ and the guard-one cells have baseline $U-u_i$.
This gives the second line in either catalog. Two positive queries give
exactly their respective partitions in the third line.

A guard singleton is dominated by a guard pair. A positive singleton
has surplus $\sum_t(R-U)_+$, bounded by a mixed term because
$U-u_i\le U$. Empty partitions are coarser; inactive bits are constant.
Thus no short schedule adds another maximum. Equation (219.15) gives
$B_{\mathcal C}=D+\Psi_{\mathcal C}$, hence the displayed equality.
The allocation domain is a nonempty product of finite compact simplices,
and the functional is continuous and convex. Compactness gives
attainment. The same domain is used for N and O, but their positive-pair
partitions differ, so equality of the optimized values is not inferred. ∎

**Example 219.7 (Strict decrease under the retraction).**
Take $I=\{1,2,3\}$, $J=\{4,5,6\}$.
For each guard $i$, put $A$ mass $1/3$ on each suffix $000,100,110$,
using guard bits one before $i$ and zero from $i$ onward.
Put $C$ mass one on each of these suffixes with guards 111, in its
corresponding first-zero class. Here $D=G=3$, $E=2$.
Before retraction $B_N=B_O=5$; afterwards both equal $10/3$.
These values follow by (219.15) on each guard, mixed and positive pair.
Thus nonexpansion can be strict. This dual-score example asserts neither
an original cap attainer nor equality of the two minima in general.

### 219.4 Proper-subset debt cuts

**Proposition 219.8 (One detector mixture for every guard subset).**
Under Theorem 219.5, let $\varnothing\ne S\subseteq I$,
$s=|S|$, and choose $p<q<r$ in $J$.
Put $d(S)=\sum_{i\in S}d_i$ and
$G_3=\gamma_p+\gamma_q+\gamma_r$.
Every unrestricted full score in the fiber satisfies

$$
(2s-1)(\Delta_O-E)\ge
d(S)+(s-1)G_3+\gamma_p-sD,
\qquad \Delta_N\ge\Delta_O.
\tag{219.19}
$$

This is a necessary cut, without a sufficiency or sharp-minimum assertion.

**Proof.** Give weight $s-1$ to $(p,q;0,q,r)$ and weight one to
each $(i,p;0,p,0)$, $i\in S$. Total weight is $2s-1$.
An $A$ word with $w_p=1$ earns $s$ units of base reward.
With $w_p=0$, it earns $s-1$ plus the number of its zero bits in $S$.
This is at least $s$ if its first zero lies in $S$, and at least
$s-1$ otherwise. Its aggregate contribution is at least
$(s-1)D+d(S)$. Correct class $p$ earns $s\gamma_p$ and classes
$q,r$ earn $(s-1)(\gamma_q+\gamma_r)$; other correct contributions
are nonnegative. Subtract $(2s-1)D$ and use
$\Delta_O-E=B_O-D$. This argument is pointwise on all words,
without a suffix restriction. The unqueried output $r$ is legal. ∎

For zero surplus $c_0=\Delta_O-E=0$, the table $(i,p;0,p,0)$
requires $A\{w_p=0\}\ge\gamma_p$, while $(p,q;0,q,r)$ requires
$A\{w_p=0\}\le D-\gamma_q-\gamma_r$.
Therefore $D\ge G_3$. Write $X=D-G_3\ge0$.
All subset cuts for this triple are equivalent to

$$
\sum_{i\in I}\min(d_i,X)\ge\gamma_p+X.
\tag{219.20}
$$

Indeed, the subset inequality is
$d(S)-sX\le\gamma_q+\gamma_r$; maximizing its left side over
subsets gives $\sum_i(d_i-X)_+$.
Using $D-\sum_i(d_i-X)_+=\sum_i\min(d_i,X)$ proves the equivalence.
The empty subset adds only a true zero bound. Condition (219.20) is
still necessary only.

For a concentration example, take $L=8$, $I=\{1,2,3,4,5\}$,
$J=\{6,7,8\}$, $d=(3/40,3/40,1,1,1)$ and
$\gamma=(1,19/20,9/10)$. Then
$D=63/20$, $G_3=57/20$, $K=6$, $E=3/20$.
Subset $\{3,4,5\}$ forces $c_0\ge1/20$ and $\Delta_O\ge1/5$;
the full subset gives only $c_0\ge-1/45$.
This distinguishes concentration from the aggregate cut, without
claiming exclusion from every pre-existing conic combination.

Normalizing the detector weights by $2s-1$ gives one probability law
on whole legal tables, implemented by one source-independent uniform
seed. For an actual first zero beyond $H=\max J$, its base mass is
$s/(2s-1)$ and exact marked-law tail error is
$\max\{(s-1)/(2s-1),a_n\}$.
This execution uses at most two actual requests, rather than executing
all conic detectors on one source. It is not an amplitude-cap theorem.

### 219.5 One column-dependent donor matrix

**Theorem 219.9 (Exact complete support of the joint reserve constructor).**
Let $I,J\subseteq\{1,\ldots,L\}$ be disjoint,
$1,2\in I$, $|I|,|J|\ge3$ and $\max I<\min J$.
Choose $\gamma_j>0$ and write
$G=\sum_J\gamma_j$, $\mu=\max_J\gamma_j$,
$\mu_{-j}=\max_{h\in J\setminus\{j\}}\gamma_h$.
Let $c\ge0$, $S=G+c$, and choose one nonnegative matrix $x_{ij}$
and one nonnegative vector $t_i$ with

$$
\sum_i x_{ij}=\gamma_j,\quad \sum_i t_i=c,\quad
s_i=\sum_jx_{ij}+t_i,
\qquad 0\le\xi_i\le s_i,
\qquad E=\xi_1+\xi_2.
\tag{219.21}
$$

Initially put $P=x_{ij}$ at $w(\{i,j\})$, $P=t_i$ at
$w(\{i\}\cup J)$ and $C=\gamma_j$ at $w(\{j\})$.
Convert fraction $\xi_i/s_i$ of every $P$ atom in guard class $i$
to $A$ at the same word. For $s_i=0$, $\xi_i=0$ and no division
is made. All other coefficients, including $T$, vanish.
Set

$$
v_{ij}=x_{ij}+t_i,\qquad a_{ij}=s_i-G+\gamma_j+\mu_{-j},
\qquad
\delta(x,t)=\max\left\{0,
 \max_{i<h}(s_i+s_h+\mu-S),
 \max_{i,j}\bigl[(v_{ij}-c)_++(a_{ij}-v_{ij})_+\bigr]\right\}.
\tag{219.22}
$$

The constructed score satisfies

$$
\begin{gathered}
\beta_i=-\xi_i\ (i\in I),\quad \beta_j=\gamma_j\ (j\in J),
\quad \beta=0\text{ elsewhere},\quad K=G+S,\quad W=S-E,\\
B_N=B_O=S+\delta(x,t),\qquad
\Delta_N=\Delta_O=E+\delta(x,t).
\end{gathered}
\tag{219.23}
$$

In particular $\delta=0$ exactly when the same allocation obeys

$$
s_i+s_h\le S-\mu,\qquad
x_{ij}+t_i\le c,\qquad
s_i-t_i-x_{ij}\le G-\gamma_j-\mu_{-j}
\tag{219.24}
$$

for all distinct guards and all guard-column pairs.
At $\delta=0$ both unrestricted exact-$Q$ minima equal $E$.
At positive $\delta$, (219.23) is an exact constructor cost;
unrestricted optimality requires a separate matching lower bound.

**Proof.** Each donor atom has first zero its guard because every
guard precedes every positive address. Conversion leaves the
zero-reward measure $U=A+P$ pointwise fixed and decreases only that
guard's numerical reward. Every guard reward is a pointwise subset of
$U$. Positive numerical labels receive only their correct atoms.
Inactive labels earn zero. This accounts for all labels by a
constructor-specific dominance statement.

The zero masses for the three active pair types are as follows.
For a mixed pair the order is guard first, positive second.

| Pair type | Zero masses in $00,01,10,11$ | Competing positive correct rewards |
| --- | --- | --- |
| Guards $i,h$ | $(0,s_i,s_h,S-s_i-s_h)$ | largest reward $\mu$ in 11 |
| Guard $i$, positive $j$ | $(v_{ij},s_i-v_{ij},c+\gamma_j-v_{ij},G-s_i-\gamma_j+v_{ij})$ | $\gamma_j$ in 10; $\mu_{-j}$ in 11 |
| Positives $j,h$ | $(c,\gamma_j,\gamma_h,G-\gamma_j-\gamma_h)$ | $\gamma_j$ in 01; $\gamma_h$ in 10; each other $\gamma_k$ in 11 |

For guard pairs the total surplus is
$(s_i+s_h+\mu-S)_+$.
For a mixed pair it is
$(v_{ij}-c)_++(a_{ij}-v_{ij})_+$.
For a positive pair there is no surplus: every other $\gamma_k$
is bounded by the sum in 11. This includes earlier unqueried labels.
For guard and mixed pairs, the two cells merged by O are already
zero-maximizing. For positive pairs, merging 00 and 01 still gives
their sum of zero rewards. Thus each active pair has identical N and
O support, even if its surplus is positive.

Every inactive bit is one on the support. A schedule containing it
reduces to a singleton or an empty partition. An N singleton is refined
by some distinct active pair, as is the empty schedule; hence its
support is bounded by the displayed N maximum. Each maximizing active
pair has the same O value, so O attains that maximum too.
This avoids requiring that every O singleton itself have a stopped
pair refinement. Constant zero supplies $S$ in both catalogs.
The table proves the support formula.

The single score has $A=\sum_i\xi_i$, $P=S-\sum_i\xi_i$, $C=G$,
$T=0$, giving its quotient and $W=S-E$.
Every full competitor at the same quotient, regardless of cancellations,
suffixes, terminal or support, satisfies $W=Z-E$ and
$B_O\ge Z$ by constant zero. Its cost is at least $E$.
Matching this bound at $\delta=0$ proves the unrestricted minima.
Within this constructor every cell gain over zero is nonnegative,
so zero total gain forces exactly (219.24).
This converse makes no assertion about other representatives. ∎

**Proposition 219.10 (Exact linear and capacitated feasibility).**
Fix the parameters of Theorem 219.9 and row totals $s_i\ge0$ with
$\sum_i s_i=S$, $\xi_i\le s_i$. For a prescribed $\delta\ge0$,
a constructor of cost at most $E+\delta$ exists if and only if one
matrix and reserve vector with the margins (219.21) satisfy

$$
s_i+s_h+\mu-S\le\delta,\qquad
a_{ij}-c\le\delta,\qquad
a_{ij}-\delta\le x_{ij}+t_i\le c+\delta.
\tag{219.25}
$$

Equivalently, choose $0\le t_i\le s_i$, $\sum_i t_i=c$, set

$$
r_i=s_i-t_i,\qquad
\ell_{ij}=\max(0,a_{ij}-\delta-t_i),\qquad
u_{ij}=c+\delta-t_i,
\tag{219.26}
$$

and retain the first two scalar bounds in (219.25).
Require $\ell_{ij}\le u_{ij}$ and every cut

$$
r(A)-\gamma(B)\le
 \sum_{i\in A,j\notin B}u_{ij}
 -\sum_{i\notin A,j\in B}\ell_{ij},
\qquad A\subseteq I,quad B\subseteq J.
\tag{219.27}
$$

Empty subsets are included. For any such $t$, define residual margins
and capacities

$$
R_i=r_i-\sum_j\ell_{ij},\qquad
C_j=\gamma_j-\sum_i\ell_{ij},\qquad
U_{ij}=u_{ij}-\ell_{ij}.
\tag{219.28}
$$

Another equivalent test is $R_i,C_j,U_{ij}\ge0$ and

$$
\sum_{i\in A}R_i\le
 \sum_{j\in J}\min\left(C_j,\sum_{i\in A}U_{ij}\right)
 \qquad(A\subseteq I).
\tag{219.29}
$$

The minimum constructor excess over all $x,t$ with the fixed margins
is attained. These equivalences concern the constructor only.

**Proof.** The exact scalar identity

$$
(v-c)_++(a-v)_+=\max(0,v-c,a-v,a-c)
\tag{219.30}
$$

proves (219.25). Subtracting the lower bounds in (219.26) converts
the matrix problem to a matrix $z=x-\ell$ with row totals $R_i$,
column totals $C_j$ and bounds $0\le z_{ij}\le U_{ij}$.
The residual totals agree because $\sum_i r_i=G=\sum_j\gamma_j$.
Summing any subset of rows and bounding each column by both its total
and incoming capacities proves necessity of (219.29).

For sufficiency take the finite network from source to row $i$ with
capacity $R_i$, from row $i$ to column $j$ with capacity $U_{ij}$,
and from column $j$ to sink with capacity $C_j$.
Its bounded feasible flow polytope is nonempty and compact, so a
maximum real flow exists. At a maximum a residual source-sink path
would permit an increase by the minimum positive residual along a
simple finite path. Consequently no such path exists. Vertices
reachable from the source determine a cut with outgoing arcs saturated
and incoming arcs carrying zero flow; conservation equates its capacity
to the maximum value. This proves the needed finite max-flow fact
without assuming termination of a real-valued augmentation algorithm.

A cut with row set $A$ and column set $B$ has capacity
$R(I\setminus A)+U(A,J\setminus B)+C(B)$.
Minimizing over $B$ gives
$R(I\setminus A)+\sum_j\min(C_j,U(A,\{j\}))$.
Thus (219.29) forces value $\sum_iR_i$. Every source and sink arc
then saturates, producing the required matrix and $x=\ell+z$.
At zero total residual mass use the zero flow.

Expanding the same cut inequalities before lower-bound subtraction
gives (219.27). Its choices $A=\varnothing$, $B=\{j\}$ force
$C_j\ge0$; choices $A=I\setminus\{i\}$, $B=J$ force $R_i\ge0$.
Thus these requirements are not missing from that formulation.
The assumption $\ell\le u$ supplies $U\ge0$.

The original margin set is nonempty: use
$t_i=cs_i/S$ and $x_{ij}=(s_i-t_i)\gamma_j/G$.
Here $G,S>0$. It is closed and bounded, and (219.22) is continuous,
so its minimum is attained. This is exact finite real existence,
with no claim about bit complexity, exact-real sampling or acquisition
runtime. The finite flow theorem is classical machinery; the
full-cell identification with this one allocation is the relation here. ∎

At $\delta=0$, the same test can be written with
$\ell_{ij}=\max(0,s_i-t_i-(G-\gamma_j-\mu_{-j}))$ and
$u_{ij}=c-t_i$. This recovers (219.24) and the row-subset criterion
without imposing proportional columns.
If $E+\delta\le1$ is separately established, the constructed score
gives an exact-$Q$ unit certificate. Unit-O feasibility alone does not
establish this affordability for an arbitrary positive constructor
minimum.

### 219.6 Four guards and profile $(2g,g,g,g)$

**Corollary 219.11 (A continuous concentrated-debt face).**
Let $L\ge8$, $I=\{1,2,3,4\}$, $J=\{5,6,7,8\}$,
$g>0$, $0\le v\le g/3$, $\gamma=(2g,g,g,g)$ and $c=g$.
Then $G=5g$, $S=6g$, $K=11g$.
In column order $5,6,7,8$, choose

$$
\begin{aligned}
x_1=x_2=x_3&=(4g/9,g/9,g/9,g/9),
 &t_1=t_2=t_3&=(g-v)/3,\\
x_4&=(2g/3,2g/3,2g/3,2g/3),&t_4&=v.
\end{aligned}
\tag{219.31}
$$

The row totals are $s_1=s_2=s_3=10g/9-v/3$,
$s_4=8g/3+v$. For every $0\le\xi_i\le s_i$, the resulting quotient
$\beta=-\xi$ on $I$, $\beta=\gamma$ on $J$, zero elsewhere,
has both unrestricted minima equal to $E=\xi_1+\xi_2$.
All inactive addresses through $L$ remain allowed in the catalogs.

**Proof.** The columns sum to $(2g,g,g,g)$ and the reserves sum to $g$.
For every column, $G-\gamma_j-\mu_{-j}=2g$.
In row 4, $s_4-t_4-x_{4j}=2g$; in a small row it is $g/3$ for
column 5 and $2g/3$ for the others.
The largest $x_{ij}+t_i$ is $7g/9-v/3\le g$ in a small row,
and $2g/3+v\le g$ in row 4.
A large/small guard pair has sum $34g/9+2v/3\le4g=S-\mu$;
two small rows have sum at most $20g/9<4g$.
Thus (219.24) holds throughout the closed real interval.
Theorem 219.9 supplies one attainer and its independent unrestricted
constant-zero lower bound. ∎

The row ceiling $s_4\le3g$ holds inside this four-guard constructor:
summing its three inequalities $s_4+s_i\le4g$ gives
$2s_4+6g\le12g$. It is attained at $v=g/3$.
This ceiling is not a bound on all full scores.

The proportional-column constructor of XII 218.6 has
$x_{ij}=\chi_i\gamma_j$. At these parameters its complement condition
forces $\chi_4\le1/2$, and its other mixed condition gives
$2g\chi_4+t_4\le g$. Therefore

$$
s_4=5g\chi_4+t_4\le g+3g\chi_4\le5g/2.
\tag{219.32}
$$

Every proportional allocation is a special case of Theorem 219.9 by
substitution, whereas debts $5g/2<\xi_4\le8g/3+v$ are attained here.
This is a strict extension of that constructor, without an exclusion
of all earlier signed or convex assemblies.

Move correct mass $u$ from $w(\{5\})$ to $w(\{5,6\})$, where
$0\le u\le4g/3-v$, and call the result $Y_u$.
It has the same $Q$ and $W$ and satisfies

$$
(\Delta_N(Y_u),\Delta_O(Y_u))=(E+(u-g)_+,E).
\tag{219.33}
$$

To verify the full range, only pairs observing 6 change.
On pair $(5,6)$ the zero masses are $(g,2g,g,2g)$.
The moved label 5 creates exactly $(u-g)_+$ excess in 00;
the stopped merge has zero mass $3g$ against total label-5 mass $2g$.
For guard/6 pairs, the receiving 10 zero mass is
$14g/9+v/3$ in a small row and $4g/3-v$ in row 4, each at least $u$.
Their 11 cells only lose a correct competitor.
For pairs $(6,h)$, $h=7,8$, the receiving 01 zero mass is $g$,
giving the same possible N excess; the O merged mass is $2g\ge u$.
An inactive query reduces to singleton 6, whose zero-bit baseline
$2g$ covers $u$. All other pairs are unchanged and short schedules
are bounded by refinements. Constant zero gives O support $S$, and
pair $(5,6)$ gives N support $S+(u-g)_+$.

At $g=1$, $v=0$, $\xi=(1,0,0,8/3)$, $u=4/3$,

$$
Q=((-1,0,0,-8/3,2,1,1,1),11),\quad W=5,\quad
B_O(Y)=6,\quad B_N(Y)=19/3.
\tag{219.34}
$$

The input costs $(4/3,1)$ are repaired to $(1,1)$ by the base score.
Splitting total early debt one between guards 1 and 2 within their
capacities gives the same conclusion with three nonzero debts.

### 219.7 Three guards and four ordered positive addresses

**Corollary 219.12 (A second four-positive face).**
Let $I=\{1,2,3\}$ and
$J=\{p,q,r,s\}\subseteq\{1,\ldots,L\}$ with $3<p<q<r<s$.
Let $\mu>0$ and $\mu/2\le v,w\le3\mu/4$.
Take $\gamma=(\mu,\mu,v,w)$, $G=2\mu+v+w$, $c=\mu/2$,
$S=5\mu/2+v+w$, $K=2G+\mu/2$.
Use the one matrix and reserve vector

$$
x_1=x_2=(\mu/4,\mu/4,\mu/8,\mu/8),\qquad
x_3=(\mu/2,\mu/2,v-\mu/4,w-\mu/4),\qquad
t=(\mu/4,\mu/4,0).
\tag{219.35}
$$

The row totals are $(\mu,\mu,\mu/2+v+w)$.
Every debt vector between zero and these totals gives both unrestricted
exact-$Q$ minima equal to $E=\xi_1+\xi_2$ by the conversions in
Theorem 219.9. The separate all-zero case
$\mu=v=w=\xi=0$ is defined by $V=0$.

**Proof.** The margins are immediate and all entries are nonnegative.
The pairs 1/3 and 2/3 have $s_i+s_3=S-\mu$; the pair 1/2 bound
follows from $v+w\ge\mu$.
For small rows, $x_{ij}+t_i$ is $\mu/2$ in the top columns
and $3\mu/8$ in the tail columns.
For row 3 it is at most $\mu/2$ since $v,w\le3\mu/4$.
The complement bounds $G-\gamma_j-\mu_{-j}$ are
$v+w,v+w,\mu+w,\mu+v$.
A small row's complement masses are $\mu/2$ in the top columns
and $5\mu/8$ in the others. Row 3's are
$v+w,v+w,3\mu/4+w,3\mu/4+v$, respectively.
Each is within its bound, proving (219.24) at all closed endpoints.
Theorem 219.9 proves the claim. ∎

Within the three-guard constructor, the opposite-pair inequalities
give $s_1,s_2\ge\mu$, so $s_3\le S-2\mu=\mu/2+v+w$.
This family attains that local ceiling.
For proportional columns, $\mu\chi_i+t_i\le\mu/2$ implies
$\chi_i\le1/2$ and
$s_i=G\chi_i+t_i\le\mu/2+(G-\mu)\chi_i\le G/2$.
If $v+w>\mu$, the attained third debt exceeds this bound by
$(v+w-\mu)/2$. Equality $v+w=\mu$ is an overlap boundary.
Neither ceiling is a global debt exclusion.

Moving mass $u$, $0\le u\le\mu$, from correct atom $w(\{p\})$
to $w(\{p,q\})$ preserves $Q,W$ and gives

$$
(\Delta_N(Y_u),\Delta_O(Y_u))=(E+(u-\mu/2)_+,E).
\tag{219.36}
$$

Indeed, only pairs involving $q$ change. Pair $(p,q)$ has zero masses
$(\mu/2,\mu,\mu,v+w)$ and label-$p$ masses $u,\mu-u$ in
00,01. The N gain is $(u-\mu/2)_+$; the O merge has baseline
$3\mu/2$ against total label-$p$ mass $\mu$.
Every guard/$q$ receiving 10 cell has zero mass $\mu$, covering
both the new label $p$ and existing label $q$ individually.
For another positive pair involving $q$, the receiving cell likewise
has baseline $\mu$ and already supports the label-$q$ mass $\mu$;
the old cell only loses a competitor. Short and inactive schedules
are bounded by the same full-pair comparisons.
This proves the formula, including $u=\mu/2$ and $u=\mu$.

For $L=7$, $J=\{4,5,6,7\}$, $\mu=1$, $v=3/4$, $w=1/2$,
$\xi=(1,0,7/4)$, the score has

$$
Q=((-1,0,-7/4,1,1,3/4,1/2),7),\quad
A=11/4,\quad P=1,\quad C=13/4,\quad T=0,\quad W=11/4.
\tag{219.37}
$$

Its supports are $15/4$ and both costs are one. At $u=1$ the input
costs are $(3/2,1)$, repaired by this same-quotient score.
The proportional row ceiling $13/8$ is below debt $7/4$ by $1/8$.
The two four-positive corollaries differ in guard count and positive
profile; their shared matrix theorem and relocation mechanism are used
once rather than treated as additional relations.

### 219.8 A sharp positive-excess family with arbitrarily many positives

**Theorem 219.13 (Three debts, zero absolute stock and exact cost $2g$).**
Let $g>0$, $0\le d\le g/2$ and
$J=\{j_1<\cdots<j_m\}\subseteq\{1,\ldots,L\}$ with
$m\ge4$, $j_1\ge4$. Set $\gamma_{j_1}=\gamma_{j_2}=g$,
$\gamma_{j_r}=h_r\in(0,g]$ for $r\ge3$, and require

$$
H=\sum_{r\ge3}h_r>g,\qquad
\sum_{r\ge3}(h_r-g/2)_+\le g/2.
\tag{219.38}
$$

Prescribe debts at $1,2,3$ equal to
$(g-d,g-d,H+g/2+2d)$, positives $\gamma$ on $J$, zero elsewhere,
and $K=2H+9g/2$. Then

$$
\min_{Q(V)=(\beta,K)}\Delta_N(V)
 =\min_{Q(V)=(\beta,K)}\Delta_O(V)=2g.
\tag{219.39}
$$

One explicit attainer has $P=T=0$ and constructor excess $2d$
above the constant-zero bound $E=2(g-d)$.
For $d>0$ this is a strictly positive-excess unrestricted minimum.

**Proof.** Choose one vector $z_r$ satisfying

$$
\max(0,h_r-g/2)\le z_r\le\min(h_r,g/2),\qquad
\sum_{r\ge3}z_r=g/2.
\tag{219.40}
$$

The sum of lower endpoints is at most $g/2$ by (219.38).
The sum of upper endpoints equals
$H-\sum(h_r-g/2)_+>g/2$. A finite product of intervals has every
sum between its endpoint sums, so (219.40) has a simultaneous solution.
This is one allocation, without separate choices for different cells.

In Theorem 219.9 take $I=\{1,2,3\}$,
$c=g/2$, $G=2g+H$, $S=H+5g/2$,
$s_1=s_2=g-d$, $s_3=H+g/2+2d$ and $\xi_i=s_i$.
Set $t_1=t_2=g/4$, $t_3=0$.
For each of the two top columns put

$$
x_{1j}=x_{2j}=g/4-d/2,\qquad x_{3j}=g/2+d;
\qquad
x_{1j_r}=x_{2j_r}=z_r/2,\quad x_{3j_r}=h_r-z_r\quad(r\ge3).
\tag{219.41}
$$

All entries are nonnegative. The top columns sum to $g$, the tail
columns to $h_r$, and the row totals including reserves are the stated
$s_i$. All donor $P$ is converted to $A$.

For guards 1 and 2, $a_{ij}=\gamma_j-H-d<0$ and
$v_{ij}\le c$, so every mixed excess is zero.
For guard 3 at a top column, $v=g/2+d$ and $a=g/2+2d$,
giving excess $d+d=2d$.
At a tail column, $v=h_r-z_r\le g/2$ and
$a-v=z_r-g/2+2d\le2d$.
A guard 3/guard 1 or 2 pair has excess $d$;
the pair 1/2 has none since $H>g$.
All positive pairs have support $S$. Thus (219.22) gives
$\delta=2d$, $W=s_3$, $B_N=B_O=S+2d$ and both costs $2g$.
This includes $d=0$ and $d=g/2$.

For unrestricted optimality, here $K=\sum|\beta|$.
Equation (219.3) forces every full exact-$Q$ competitor to have
$P=T=0$, $A$ only in classes 1,2,3 with totals $s_i$ and $C$ only
in $J$ with totals $\gamma_j$. Hence every competitor has $W=s_3$.
The legal stopped table

$$
(3,j_1;0,j_1,j_2)
\tag{219.42}
$$

collects every $A_3$ atom, every $C_{j_1}$ atom and every $C_{j_2}$
atom, whatever their suffixes. Other rewards are nonnegative.
Its exhaustion output $j_2$ is legitimately unqueried.
Therefore $B_O\ge s_3+2g$ and $\Delta_O\ge2g$;
N contains O. This independent bound matches the construction,
proving the unrestricted minima. ∎

The theorem permits every finite $m\ge4$ and arbitrary gaps after
address 3. For instance tails $(3g/4,g/2,\ldots,g/2)$ satisfy
(219.38) at every such $m$. These parameters do not impose a finite
address bound on original competitors.

At $d=0$ the proportional-column constructor cannot attain this same
zero-excess fiber when $H>g$. Its large-row interval would require

$$
\chi_3\ge\frac{H}{H+g},\qquad
\chi_3\le\frac{H+g/2}{H+2g},\qquad
\frac{H}{H+g}-\frac{H+g/2}{H+2g}
 =\frac{g(H-g)}{2(H+g)(H+2g)}>0.
\tag{219.43}
$$

The lower bound follows from its top-column mixed complement
condition; the upper bound follows from nonnegative $t_3$.
This excludes that proportional construction, rather than every
possible predecessor certificate.
At full conversion Corollary 219.12 with $\mu=g$, $H=v+w>g$,
$z_3=z_4=g/4$ agrees with this theorem's $d=0$ boundary.
That common boundary is a single attained region.

**Example 219.14 (Relocation and a strict unit-input repair).**
In Theorem 219.13 move the entire correct mass $g$ at $w(\{j_1\})$
to $w(\{j_1,j_2\})$, keeping all other coefficients, and call it $Y$.
Then

$$
Q(Y)=Q(V),\quad W_Y=W_V,\qquad
(\Delta_N(Y),\Delta_O(Y))
 =\bigl(2g+(g/2-2d)_+,\ 2g\bigr).
\tag{219.44}
$$

For pair $(j_1,j_2)$ the N support becomes $S+g/2$:
the new 00 cell earns $g$ against baseline $c=g/2$.
The O merged baseline $c+g$ still covers $g$.
For guard/$j_2$ pairs the moved label $j_1$ competes with the existing
label $j_2$ of equal mass $g$, so no maximum rises.
For another positive pair involving $j_2$, the receiving cell already
has zero reward $g$. All other cells are unchanged or lose a competitor.
The lower detector (219.42) still collects $s_3+2g$.
Consequently $B_O=S+2d$ and $B_N=S+\max(2d,g/2)$, proving the formula.
It is a strict input gap for $0\le d<g/4$, with the explicit same-$Q$
repair supplied by the theorem.

For a literal rational instance, take $L=7$, $J=\{4,5,6,7\}$,
$g=1/2$, $d=1/16$, $(h_6,h_7)=(3/8,1/4)$,
$(z_6,z_7)=(1/4,0)$. The complete nonzero coefficient list is

$$
\begin{aligned}
A_{w(\{i,4\})}=A_{w(\{i,5\})}&=3/32,&
A_{w(\{i,6\})}&=1/8,&
A_{w(\{i,4,5,6,7\})}&=1/8&& (i=1,2),\\
A_{w(\{3,4\})}=A_{w(\{3,5\})}&=5/16,&
A_{w(\{3,6\})}&=1/8,&
A_{w(\{3,7\})}&=1/4,\\
C_{w(\{4\})}=C_{w(\{5\})}&=1/2,&
C_{w(\{6\})}&=3/8,&C_{w(\{7\})}&=1/4.
\end{aligned}
\tag{219.45}
$$

All other coefficients, $P$ and $T$ vanish. This gives
$Q=((-7/16,-7/16,-1,1/2,1/2,3/8,1/4),7/2)$,
$W=1$, $B_N=B_O=2$.
Moving $C_4$ to $w(\{4,5\})$ gives $B_O(Y)=2$, $B_N(Y)=17/8$;
pair $(4,5)$ has N cell maxima $(1/2,1/2,1/2,5/8)$.
Thus costs $(9/8,1)$ are repaired to $(1,1)$.
These input gaps are not original-model separators.

### 219.9 Source, seed, all event rows and exact closed caps

The source and resource suppliers are
[Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows),
[Acquisition Resources 73.1 and 90.1–90.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md),
[Continuation 109.1 and 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md),
and [Continuation IX 207.20](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md).
Their following correspondences keep score allocation, probability
normalization and actual acquisition distinct.

**Definition 219.15 (Original source and separately selected laws).**
The countable labeled source and its static replies are

$$
\begin{aligned}
X&=\{(r,z):r\text{ prime},\ z\in\mathbb Z,
       \ \lceil F_r/10\rceil\le z\le\lfloor F_r/5\rfloor\},\\
F_0&=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
N(r,z)&=1+F_rz,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},
\qquad n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
\tag{219.46}
$$

The full Borel tape carrier is
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
each block a copy of $(0,1)$. The unchanged consumer returns unknown
on $B_j$ and proposes $j$ on $P_j$.
The original nonatomic targets of
[Source-Correlated Laws 67.5](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#67-original-target-proportional-containment-and-unavoidable-nonatomic-ranges)
remain

$$
\begin{aligned}
t(x)&=\sum_{i\ge1}3^{-i}q_i(x),\qquad
Z_t=\int_0^1e^{tu}\,du,\qquad
\nu_x(du)=Z_{t(x)}^{-1}e^{t(x)u}\,du\text{ on }B_{n(x)},\\
\mu_x&=(1-h_0)\nu_x+h_0\pi_{\Omega(x)},\qquad 0<h_0<1,
\end{aligned}
\tag{219.47}
$$

where $\pi_j$ is uniform on $P_j$ and $\Omega(x)$ counts distinct
prime divisors of $N(x)$. The integral definition covers $t=0$.
For distinct original marks $\theta_j=(B_1,1/(j+2))$, $j\ge0$,
the separately selected laws are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                     +a_{n(x)}\delta_{\theta_{n(x)}},
\qquad 1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
\tag{219.48}
$$

They do not replace the original nonatomic targets or the consumer.
Indeed any finitely marked law has TV distance one from each $\mu_x$:
its finite support has probability one for that law and zero for
$\mu_x$. Numerical table labels mean the actual marks in the original
carrier; unrestricted competitors still have all Borel output events.

Every scored finite pattern has an actual source witness.
For finitely many arbitrary prime addresses, the entry-rank part of
35.2 permits a prime $r$ large enough that $F_r$ is invertible modulo
all indicated primes. Impose $z=-F_r^{-1}$ modulo a prime whose reply
is prescribed one, and $z=0$ modulo a prime whose reply is prescribed
zero. CRT gives a residue modulo their product. Choose $r$ with the
original Fibonacci window longer than that product and take its first
representative above the lower endpoint. It is still below the upper
endpoint. Thus every multiple-zero pattern, every inactive gap and a
positive prefix followed by a prescribed later zero has a witness
fixed before seeds. No probability distribution on sources is introduced.
Each actual integer has finite prime support; a finite all-one word
represents actual later first zeros, rather than an infinite positive source.

**Proposition 219.16 (Whole-table execution and the independent TV rows).**
For a normalized finite distribution on legal tables, partition one
source-independent $U\sim\mathrm{Unif}[0,1)$ into the table masses.
The selected interval fixes the entire schedule and all its outputs
before any reply. N obtains its full preselected schedule. O uses an
increasing preselected schedule and stops at its first queried zero
or exhaustion. The N completion of an O pair
$(i,j;o_0,o_{10},o_{11})$ has outputs
$(o_0,o_0,o_{10},o_{11})$ on $00,01,10,11$, using the same $U$
and actual schedule. It acquires the second reply even when ignored.

This gives zero advice, at most two actual requests and finite handoff
on every source and seed. Repetitions and ignored requests count.
There is no adaptive replacement of the second address, free probe,
restart, seed conditioning, expected-count relaxation, source prior,
address-cost substitution or finite-address restriction on competitors.
Two different finite laws can use partitions of the same uniform seed
or their common finite refinement, without claiming identical outputs.
Score coefficients and conic detector weights are not executed as
probability laws before normalization.

For one probability vector $p_w$ and a first-zero word of class $n$,
TV distance at most $\varepsilon$ from the selected target requires
and is equivalent to the three independent rows

$$
p_w(0)\ge1-a_n-\varepsilon,\qquad
p_w(n)\ge a_n-\varepsilon,\qquad
p_w(0)+p_w(n)\ge1-\varepsilon.
\tag{219.49}
$$

At the finite positive word the base row is $p_+(0)\ge1-\varepsilon$.
These rows hold on all words, even those of zero score weight.
Negative singleton demands stay unchanged.

**Proof.** Execution follows the selected whole table, so no extra
randomness or observations enter. For the TV assertion write the
target masses as $1-a_n,a_n$ on its two marks. The total common mass
of target and output is
$\min(p_w(0),1-a_n)+\min(p_w(n),a_n)$.
Its complement is the maximum of
$1-a_n-p_w(0)$, $a_n-p_w(n)$ and $1-p_w(0)-p_w(n)$,
which proves (219.49). The pair row cannot be omitted: with
$a_n=1/2$, $\varepsilon=1/4$, masses $p(0)=p(n)=1/4$
pass both singleton bounds while TV is $1/2$.
The remaining mass can lie at a different legal mark.
Thus singleton checks alone do not establish the desired event law. ∎

For any finite marked law with labels through $H$ and any actual
first zero $n>H$, its exact error is

$$
\operatorname{TV}\left(\sum_{j=0}^Hp_+(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_+(0),a_n\}.
\tag{219.50}
$$

Half the sum of absolute discrepancies is
$\tfrac12(|a_n-(1-p_+(0))|+(1-p_+(0))+a_n)$,
giving the formula. It treats all Borel events and retains equality
$a_n=\varepsilon$. The strict active horizon is
$L_a=\max(\{n:a_n>\varepsilon\}\cup\{0\})$.
For $\varepsilon\ge1$, immediate base output suffices; the empty
active horizon and equality tails are not removed.

The original arbitrary-address/full-carrier necessity is supplied by
110.2, rather than by a finite score. Its projection fixes the low marks
and sends other tapes to zero. Countability supplies a common conull
seed event for actual sourcewise finite handoff and hard count.
The maximum address of the entire preselected schedule has vanishing
probability tail. Actual finite-pattern witnesses precede seed choices;
for each finite family, finite handoff supplies the required execution
transition cutoffs. Same-class finite simulations and compactness of
one finite catalog simplex produce one full configuration at the exact
closed cap. No uniform address or runtime bound is asserted.
Conversely the finite whole-table law is executed literally and
(219.50) supplies every actual tail. This is reuse of the class-preserving
bridge, not a new transport assertion or preservation of an arbitrary
competitor's entire law.

For a score horizon $H\ne L_a$, both cases of 207.20 are retained.
If $H<L_a$, fix the later replies to zero and project later labels to
zero in the finite representation. This gives the low-word rows for
comparison, rather than a cap attainer on omitted active tails.
If $H>L_a$, extend the active kernel by ignoring new coordinates.
Old rows remain unchanged on every new suffix; a new first zero has
$a_n\le\varepsilon$ and the old positive-word law, so (219.50)
gives the exact closed bound. This includes $L_a=0$.
Neither finite algebraic operation is an uncounted observation.
Auxiliary hull points with $e=0$ and radial parameter zero do not
assert attainment for an original positive vanishing tail.

The normalized probability-vector criterion 109.1 retains its own
hypotheses, in particular the common schedule-mass normalization and
the inequality $c\ge H$ for stopped kernels.
Neither $Q(V)$ nor a signed affine vector is automatically such a kernel.
For a full conic configuration of mass $M$, the reused radial filling
executes masses $\tau\lambda_D$ and anchor mass $1-\tau M$ only when
$0\le\tau\le1/\max(1,M)$. Its event vector is
$r+\tau G_N\lambda$. This pays one total mass and scales the entire
actual amplitude sequence and cap; a positive-tail conclusion requires
the owning positive-parameter hypotheses. No signed vector is sampled.

A concrete reused normalized configuration gives a common-realization
check. At any horizon $H\ge3$, choose each of

$$
(1,2;1,2,0),\quad(1,2;1,2,3),\quad
(1,3;1,3,0),\quad(2,3;2,3,0)
\tag{219.51}
$$

with probability $1/4$ on that same uniform seed.
Its N completions have the same output law on every word.
It is feasible at
$b^\star=(1,1,1,1/4,\ldots,1/4;e=1/4)$:
the two hull equalities are
$\sum_{j\ge3}b^\star_j=(H+1)/4$ and
$b^\star_1+\sum_{j\ge3}b^\star_j-(H+1)e=1$.
On first-zero classes 1 and 2 the correct reading is $3/4$, base
is zero or $1/4$, pair is $3/4$ or one; base demand $-1/4$ remains.
Class 3 has readings $(1/4,3/4,1)$, later classes $(3/4,0,3/4)$,
and the positive base is $3/4$. These are every independent row,
on every suffix. Thus the same full mass-one $\lambda$ witnesses
$b^\star\in H_N$.

Take $a_1=a_2=a_3=1$, $a_4=\cdots=a_H=1/4$ and
$a_{H+k}=2^{1-k}/4$ for $k\ge1$.
The actual cap $1/4$ is attained by (219.51); its first new tail
amplitude equals the cap and (219.50) gives tail error exactly $1/4$.
This is a reused interface example, not an additional amplitude family.
At this same point and same mass-one configuration, the quotients in
(219.34) and (219.37) read $-13/6$ and $-43/16$, respectively.
They are not strict separation readings.

**Corollary 219.17 (Scoped unit certificates and necessary amplitude cuts).**
For an actual full unit-O input whose quotient lies in Theorem 219.3's
sufficient face, or a zero-excess domain of Theorem 219.9 including
Corollaries 219.11–219.12, the unrestricted lower bound forces $E\le1$.
The constructed score has $\Delta_N=E$, the same quotient and
$\theta=0$ in (219.6). In Theorem 219.13 the independent lower bound
instead forces $2g\le1$, and its constructed score has cost $2g$.
For Theorem 219.6 the analogous certificate is conditional on one
allocation with $\Psi_N\le1-E$; unit-O feasibility provides only an
O allocation and does not prove that N condition.

At any original positive closed cap, either original class's feasible
selected-law acquisition must satisfy, for each stated plateau score,

$$
\sum_{j:\beta_j>0}\beta_j a_j
 \le\sum_{i:\beta_i<0}(-\beta_i)a_i+K\varepsilon.
\tag{219.52}
$$

For the sharp family the necessary inequality is

$$
g(a_{j_1}+a_{j_2})+\sum_{r\ge3}h_ra_{j_r}
 -(g-d)(a_1+a_2)-(H+g/2+2d)a_3
 \le2d+(2H+9g/2)\varepsilon.
\tag{219.53}
$$

**Proof.** The unit certificates follow from the attained unrestricted
minima and $\sigma_{H_L}(0)=0$. At the same full feasible $\lambda$
their weak-duality bound is $F_{Q(y)}\le ME$ or $F_{Q(y)}\le2gM$,
respectively, as in (219.7). No independent component budget is added.
For the necessary cuts use 110.2 and both horizon cases to obtain one
normalized finite configuration satisfying every row in (219.49).
Pairing with a score of support $W+c_0$ gives
$F_{Q(V)}(a,\varepsilon)\le c_0$.
Because early coefficients are $-\xi_1,-\xi_2$, the left side equals
$\sum\gamma_j a_j-\sum\xi_i a_i+E-K\varepsilon$.
For a plateau $c_0=E$; for Theorem 219.13, $c_0=2g=E+2d$.
Canceling gives (219.52)–(219.53).
For $\varepsilon\ge1$ the same inequalities are automatic from
$a_j\le1$ and the stock bounds. They are necessary conditions,
not sufficient amplitude classifications or new nonatomic-target claims. ∎

The earlier-label regression remains explicit. On 0100 the legal
N table $(3,4;1,0,0,0)$ has base, correct, pair readings $(0,1,1)$;
replacing its first output by zero gives $(1,0,1)$.
The source $(19,436)$ has $N=1822917$ and this prefix.
No general pruning to zero or queried labels is allowed.
All dominance arguments above concern the displayed constructed score.

### 219.10 Reuse boundaries and comparison sources

The mathematical scopes here are the matched face in Theorem 219.3,
the unrestricted retraction and exact single-allocation relation in
219.5–219.6, the deduplicated matrix relation in 219.9–219.10,
its two four-positive domains, and the independently sharp family
219.13. The subset cuts, examples, normalized detector execution and
necessary amplitude inequalities are consequences and interfaces of
these scopes. General stock, support convexity, constant-zero and
detector lower bounds, weak duality, finite flow, source witnesses and
transport are reused with no separate new-content claim.

Theorem 219.3 has first positive address 3 with two intervening donor
positions. The uniform guard and common-chain scopes in XII 217.2
and 217.6 require at least three guards before the positives.
The moving triple and equal adjacent-triple scopes in 217.3–217.4
and 217.7 retain their own address and profile restrictions.
The two-debt theorem 218.2 has zero absolute stock; example (219.13)
has absolute stock 18 and intervening debts. Its cumulative tail
after position 3 is $-6,2,-4,5$, so the automatic cumulative-tail cone
of 218.9 does not apply. Every cumulative sum is required there,
rather than only a final total sign.

The sole-zero-correct construction in 217.5 explicitly allows first
positive 3, so an address distinction alone cannot exclude it.
Here is its precise equality obstruction at the unsigned nonzero face
$B=B_0$. Write its guard shares as $\alpha_r$, summing to one,
its sole-positive columns as $p_v$, common multi-positive reserve as
$c_{\rm old}$, sole-guard reserve as $d_{\rm old}$ and terminal as $T$.
Its $P$ atoms have zero sets $\{r,v\}$, $\{r\}\cup I_+$,
$\{r\}$, with the corresponding common shares.
If its cost were zero, equality in the detector bound and (219.12)
would force $A_{I_+}=A_{\rm out}=P_{I_+}=0$.
Pivot-3 protection forces $p_3>0$.
Since $P_{I_+}=0$, every guard share at $r>3$ must vanish:
its $\{r,3\}$ atom would otherwise have first zero 3.
Thus only shares 1 and 2 remain. Pair $(1,2)$, cell 11, contains
every sole-zero correct atom and no such guard stock, forcing
$T\ge\max(g,h,k)>0$. Its mixed protections also require
$p_3+c_{\rm old}\ge2g$, $p_m\ge h$, $p_\ell\ge k$ and hence
total stock at least $B_0+d_{\rm old}+T>B_0$, a contradiction.
This excludes that constructor at the specified face; no exclusion
of every old convex or signed-residual assembly follows.

The unrestricted reset in Theorem 219.5 does not follow from choosing
sole-guard carriers in a sufficient construction. It starts from every
full score in its entire face and preserves every positive suffix.
The full-set/equal-triple specialization of (219.19) reuses the
217.7 detector. The proper-subset relation records additional debt
concentration, without claiming sharpness against every conic lower cut.
No fixed four-column or last-bit-zero suffix carrier is asserted
necessary. Extra stock, interleaved signs and equality of the two
general optimized functionals remain outside the retraction result.

The matrix relation contains 218.6 by $x_{ij}=\chi_i\gamma_j$ and
arbitrary permitted $t_i$. The numerical debt capacities in
(219.32) and Corollary 219.12 exclude that proportional constructor
at the displayed quotients. Uniform shares in 217.2 and 217.6 likewise
have capacity at most $S/|I|$; they do not supply these concentrated
debts. For example (219.37), that bound is at most $5/4<7/4$.
For its larger common-share prefix construction 217.5, allow
$p_j\ge\gamma_j$ and extra nonnegative sole-guard and terminal stock.
Writing $P_0=\sum p_j\ge G=13/4$, the remaining reserve is at most
$1/2-(P_0-G)$. Its two top columns imply
$\min(p_p,p_q)+c_{\rm old}\le3/2$, forcing each common share
at most $1/3$ by the mixed-cell condition. Its convertible guard stock
is consequently at most $S/3=5/4$. This is another named-constructor
comparison, not an exhaustive closure theorem.

Theorem 219.13 has three debts and at least four positive coordinates.
The one- and two-positive scopes in 216, the two-debt scope in 218.2,
and the three-positive scopes in 217 keep their stated domains.
At $d=0$, a uniform guard supplier including the third guard would
need capacity exceeding $S/3$; excluding it leaves only $2g$ stock,
below that supplier's top-positive protection threshold.
For 217.5, top-column mixed protection at the same least-stock fiber
forces $p_{j_1}+c_{\rm old}\ge S/2$ and
$p_{j_2}+c_{\rm old}\ge S/2$.
The tail columns require total at least $H$, so total stock $S$ forces
$c_{\rm old}\ge H+d_{\rm old}$, while its remaining reserve is at
most $g/2$. Since $H>g$, this is impossible for that constructor.
The positive-$d$ theorem uses its separate unrestricted detector bound,
rather than inferring unrestricted optimality from these comparisons.
The cumulative-tail erasure cone does not automatically apply to its
positive tail after the early coordinates.

The separated-block operation 218.3 and affine-family test 218.4–218.5
are conditional methods and are not excluded as possible components
of other certificates. Their fixed-method failures do not establish
original nonmembership. The alternative O laws in 112.2 remain valid.
The fixed-baseline carrier-box criterion in X 212.3 is distinct from
a freely selected donor matrix, and no converse transfer is assumed.
The zero-net middle-deletion obstruction 216.4 and the need for all
cumulative erased-tail inequalities 218.8–218.9 both remain.

The equal-profile overlaps within 217 are retained: 217.4's equal
triple is 217.7 at three guards, 217.3's equal zero endpoint is the
same plateau, and 217.5's equal-three common-share core overlaps
217.2. The sole-zero containment diagnostic adds no independent
theorem. The common boundary of 219.12 and 219.13 is counted once.

The consecutive profile $(0,0,2t,t,t,0,\ldots)$ at $L\ge5$,
$K=11t+u$, $t,u\ge0$, is also reused rather than a new region.
Indeed half-$t$ times generator $Z$ of XI 214.8 gives
positive coefficients $(t,t,t)$, $K=7t$, $W=4t$, $T=t$.
The one-pivot score of XI 213.18 at $n=3$, $g=t$, $B=3t$
adds $\beta_3=t$, $K=4t$, $W=3t$, $T=t$.
Pad by constant-one coordinates, add the coefficients and terminal
mass $u$. This one joint score has $P=5t$, $T=2t+u$,
$W=7t+u$, $K=11t+u$. Support subadditivity bounds both costs
above by zero, and constant zero bounds them below by zero.
Thus the whole family is already supplied. At $t=1,u=0$, the
alternative explicit cell vector $(0,3,2,2)$ for pair $(1,2)$ has
sum seven: it is each schedule's sum of cell maxima that equals
seven, not every individual cell maximum.
The terminal is $2t$ at $u=0$, and is not zero when $t>0$.
No additional theorem or coverage claim is attached to this profile.

The comparison with literature is limited to the following statements
and versions. The ordinary proofs above do not import a universal
hard-two containment theorem from any of them.

| Primary source | Reused relation and unproved transfer boundary |
| --- | --- |
| [Gale, *A theorem on flows in networks*, Pacific J. Math. 7(2), 1073–1082, Feasibility and Minimum Cut Theorems](https://msp.org/pjm/1957/7-2/pjm-v7-n2-p04-s.pdf), DOI 10.2140/pjm.1957.7.1073 | Finite nonnegative real capacities and balanced residual row/column margins give the bounded matrix criterion. The lower-bound subtraction and cut elimination are explicit in 219.10. This deterministic allocation of dual weights is not normalized acquisition or a query-cost result. |
| [Blackwell, *Comparison of Experiments*, §§2–5, Theorems 2, 4, 6 and 8](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf) | Finite words, transcript cells and labels correspond to states, observations and actions. Common randomized decision procedures and risk-vector comparisons do not construct an increasing first-zero hard-two schedule or authorize a prior on sources. |
| [Chen, 2502.06530v1](https://arxiv.org/pdf/2502.06530v1) and [2502.06530v2](https://arxiv.org/html/2502.06530v2), Theorem 3, Definition 7 and Corollary 3 | Distinct versions retain a binary-action comparison and a finite-action extension conditional on binary decomposability of the whole value function. A resource-preserving decomposition of this complete all-label problem is not supplied. |
| [Yang–Yang, 2603.11448v1, §2 and Theorem 1](https://arxiv.org/pdf/2603.11448v1) | Compact Polish $X$ and a cone of bounded upper-semicontinuous tests containing constants, with a sup-norm-closed continuous part, decreasing continuous approximation and bounded decreasing-limit closure, support the min-closure/affine-value/order-preserving-coupling equivalence. No matching min-closed legal-table cone with the actual request budget is established. |
| [Zaev, 1404.4962v1, Problem 1.3, Theorem 2.1 and Remark 2.4](https://arxiv.org/html/1404.4962v1) | One constrained coupling has fixed Polish marginals, the specified dominated continuous cost class and a linear constraint subspace. Duality permits an empty feasible set; it supplies neither our matrix's nonemptiness nor stopped resource realization. |
| [Bertschinger–Rauh, 1401.3146v1, Example 18](https://arxiv.org/html/1401.3146v1) | The unique nonnegative factor in the displayed zonotope example has row sums $(2,2,2,0)$ and is not stochastic. This normalization obstruction is not an original-source strict separator. |
| [Embrechts–Hofert–Wang, 1606.08212v1, Theorem 2.2](https://arxiv.org/html/1606.08212v1) | Boolean second-moment compatibility is a convex hull of $xx^T$ under one joint law. Jointness is essential; a PSD relaxation or separate pair marginals do not yield the required affordable table allocation. |
| [Kaniewski–Lee–de Wolf, 1411.7280v1, Definition 8 and Theorem 9](https://arxiv.org/pdf/1411.7280v1) | Scalar nonnegative expectation and worst-path query depth are distinct from a normalized probability-vector law, mean request count and the original all-Borel TV problem. |
| [Angel–Spinka, 1903.00632v2, opening example and Theorems 1–2](https://arxiv.org/html/1903.00632v2) | Uniform laws on $\{0,1\}$, $\{0,2\}$, $\{1,2\}$ have pairwise TV $1/2$, while every common realization has at least two unequal pairs. Pairwise optima need not coexist. The joint mismatch bound assumes one common sigma-finite dominating measure and gives no stopped hard-two implementation or source prior. |

The Gale source is the Pacific Journal paper identified above;
the unrelated PNAS DOI does not identify that theorem.
The Yang–Yang citation is its versioned v1 PDF, whose source anchor
in XII is SHA256
1748332276759372cdb7f0efc61842c799484facf67a4388de4d03171e7df624;
no identity of the entire PDF with another HTML version is assumed.
These are bounded correspondence and reuse statements.
The scoped constructions are repository-derived ordinary mathematics;
no exhaustive exclusion of earlier convex or polar consequences,
literature-absence assertion or worldwide priority claim follows.

### 219.11 The remaining unrestricted obligation

For every $L\ge3$ and every actual full $y\ge0$ with
$\Delta_O(y)\le1$, the positive obligation remains to produce one
unrestricted full $V\ge0$ and $\theta\in[0,1]$ satisfying (219.6).
No exact-$Q$, fixed-anchor, unary, support, terminal, suffix or
constructor requirement may be imposed on this universal search.
The theorems here supply that object only under their stated hypotheses.
The retraction does not prove $\min\Psi_N=\min\Psi_O$;
the matrix cuts do not prove that arbitrary unit-O inputs are reducible
to the donor domain with an affordable single residual.

A genuine negative alternative still requires the same actual
$(b,e)\in H_N$, the same full feasible $\lambda\ge0$ with
$G_N\lambda\ge h(b,e)$, $M=\sum\lambda\ge1$, and an actual
full unit-O input $y$ with strict $F_{Q(y)}(b,e)>M$.
This single realization must retain the original source, full carrier,
unchanged consumer, one source-independent seed, arbitrary addresses,
hard-two actual requests, sourcewise almost-sure finite handoff,
every multiple-zero word, all independent event rows, positive vanishing
amplitudes, actual tails and exact closed-cap transport.
No such separator is supplied by the input gaps or local constructor
obstructions above.

Consequently the original implication, for every positive nonincreasing
vanishing sequence and every positive closed cap,
$\mathcal F_N(a,\varepsilon)\ne\varnothing
\Rightarrow\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing$,
remains unresolved. Separately attainable marginals, an unaffordable
fixed constructor, an off-$H_N$ affine witness, a hull-only point,
a final-total-only tail test or an exact-law failure do not decide it.
All finite equalities and real-parameter existence assertions in this
section are ordinary mathematics; none asserts Lean/kernel validation,
physical sampling cost or universal affordability.

## 追加锚（本行以下为增补区）

## 220. Joint score retractions, transfer cuts and queried-label funding

The objects in this section are complete scores on one Boolean carrier
or complete allocations of actual legal tables. Each assertion uses
one common realization and one total budget. Four relations are studied:
eligible-coordinate resets, pooled prefix-cell domination with a common
coefficient total, arbitrary interior masks with their transfer residual,
and queried-label gates funded by an actual joint block. Their hypotheses
are sufficient conditions for the stated operations; none is imposed on
the unrestricted comparison problem.

### 220.1 Complete score and certificate interface

**定义 220.1（Full words, rewards and supports）。** Fix $L\ge3$.
Let $\mathcal B_L=\{0,1\}^L$, let $n(w)$ be the first zero of a
nonpositive word, and put $\Omega_n=\{w:n(w)=n\}$.
For every $w\ne1^L$ the three coefficients $A_w,C_w,P_w$ are
independently nonnegative; $T\ge0$ is the terminal coefficient.
The full reward is

$$
g_y(w,\ell)=A_w[\ell=0]+C_w[\ell=n(w)]
 +P_w[\ell\in\{0,n(w)\}],\qquad
 g_y(1^L,\ell)=T[\ell=0].
$$

All labels $0,\ldots,L$, including earlier and unqueried labels, are
legal. The complete catalogs contain empty schedules, every singleton,
and every pair $i<j$. A full $N$ pair has cells $00,01,10,11$;
a stopped increasing $O$ pair has cells $0,10,11$, where the first cell
is the union of $00$ and $01$. A table chooses an arbitrary legal output
on each cell. Write $\Pi_C(S)$ for that partition and

$$
 B_C^S(y)=\sum_{H\in\Pi_C(S)}\max_{0\le\ell\le L}
                   \sum_{w\in H}g_y(w,\ell),\qquad
 B_C(y)=\max_S B_C^S(y),\quad C\in\{N,O\}.
$$

Reversing an $N$ pair permutes its information cells; repeating an
address gives singleton information. These are support identities,
not a discount on actual requests: repetitions and ignored replies
still count in an execution.

Use the quotient and baseline of 219.1:

$$
\begin{aligned}
 W_y&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
 \beta_n&=\sum_{w\in\Omega_n}(C_w-A_w),\qquad
 K=\sum_w(A_w+C_w+P_w)+T,\\
 Q(y)&=(\beta,K),\qquad \Delta_C(y)=B_C(y)-W_y.
\end{aligned}
$$

With $Z_0=\sum(A+P)+T$ one has $W=Z_0+\beta_1+\beta_2$.
If $A_n,C_n$ denote class totals, the absolute spare stock is

$$
 K-\sum_n|\beta_n|=2\sum_n\min(A_n,C_n)+\sum_wP_w+T.
$$

These quantities are different: $K$ is the full coefficient total,
$Z_0$ the zero-label reward, and the last expression the spare stock.
Proof weights on words are not a probability distribution on sources.

**定义 220.2（Independent event rows and one residual budget）。**
Let $\alpha=(1,1,0,\ldots,0)$ and reuse the hull $H_L$ of 219.2:

$$
\begin{gathered}
1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\qquad b_2=b_3,\\
(L+1)e\le\sum_{n\ge3}b_n,\qquad
b_1+\sum_{n\ge3}b_n-(L+1)e\le1.
\end{gathered}
$$

For $q=(\beta,K)$ put
$F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke$ and
$\sigma_H(q)=\max_{H_L}F_q$.
At every $w\in\Omega_n$ the demands on the three independent events
$\{0\}$, $\{n\}$, $\{0,n\}$ are respectively

$$
 1-b_n-e,\qquad b_n-e,\qquad1-e.
$$

At $1^L$ the base demand is $1-e$. Negative singleton demands remain.
Let $R=O(1,2;1,2,0)$, let $z_D$ be the complete event vector of a table,
$r=z_R$, $h(b,e)=d(b,e)-r$, and let $G_C$ contain every column
$z_D-r$ of the full catalog. Membership of $H_N$ means membership of
$H_L$ together with one actual complete $\lambda\ge0$ satisfying
$G_N\lambda\ge h$. Put $M=\sum_D\lambda_D$ for that same witness.
Hull membership alone does not supply it.

The positive certificate for an actual $\Delta_O(y)\le1$ is one
unrestricted full $V\ge0$ and $\theta\in[0,1]$ such that

$$
 \Delta_N(V)+\theta\le1,\qquad
 \sigma_H(Q(y)-Q(V))\le\theta.\tag{220.1}
$$

No exact-$Q$, fixed-baseline, unary, suffix or terminal constraint is
part of this search. Nonzero zero-cost $V$ is allowed at $\theta=1$.
For the same $b\in H_N$ and same complete feasible $\lambda$,
nonnegativity of $V$ gives the reused weak-duality calculation

$$
 F_{Q(V)}(b,e)=V\cdot h(b,e)
 \le V\cdot G_N\lambda\le M\Delta_N(V).
$$

Adding one residual bounded by $\theta$ gives
$F_{Q(y)}(b,e)\le M\Delta_N(V)+\theta\le\max(1,M)$.
All independent rows enter this calculation with one allocation.

### 220.2 Eligible coordinates and the original bad-pair graph

**定义 220.3（Eligible-coordinate reset）。** Define

$$
 E(y)=\{a:\ C_w\le A_w\text{ for every }w\ne1^L
                                  \text{ with }w_a=0\}.
$$

This is wordwise domination, stronger than a sign of $\beta_a$.
For $I\subseteq E(y)$ let $f_I$ fix $1^L$, keep the first-zero bit
$n(w)$ zero, set every other bit in $I$ to one, and keep all other bits.
Push $A,C,P$ together by this same map, summing collisions, and keep $T$.
The resulting score is $\rho_Iy$. For fixed $I$ this is a linear map;
choosing $E(y)$ depends on the input.

**定理 220.4（Fixed-schedule contraction and exact edge criterion）。**
For every full nonnegative $y$ and every $I\subseteq E(y)$,
$\rho_I$ is idempotent and preserves $Q,W$. For each fixed schedule
$S$ and each $C=N,O$,

$$
 B_C^S(\rho_Iy)\le B_C^S(y).
$$

Every cell-label reading of a schedule avoiding $I$ is unchanged.
Every pair touching $I$ has equal $N$ and $O$ supports after the reset.
Consequently

$$
 B_N(\rho_Iy)=\max\left(B_O(\rho_Iy),
       \max_{i<j,\ i,j\notin I}B_N^{ij}(y)\right),\tag{220.2}
$$

where the empty outside maximum may be zero.
If $d\ge0$ and $\Delta_O(y)\le d$, then

$$
 \Delta_N(\rho_Iy)\le d
 \quad\Longleftrightarrow\quad
 B_N^{ij}(y)\le W_y+d\text{ for every pair disjoint from }I.
 \tag{220.3}
$$

Thus $I$ must cover every edge of the graph of original pairs
$B_N^{ij}(y)>W_y+d$. Some eligible reset is affordable precisely when
no such edge lies wholly outside $E(y)$; the maximal reset then works.
At $d=1$ it supplies $(V,\theta)=(\rho_{E(y)}y,0)$ in (220.1).
A failed edge criterion rules out these resets at that budget only.

**证明。** First-zero preservation follows because the earlier bits
were already one and the first zero is kept. All first-zero class totals
and $T$ therefore persist, proving $Q,W$ preservation. The reset bits
already have their final values, proving idempotence.

Put $U(w)=A_w+P_w$ on zero words and $U(1^L)=T$.
For a numerical label $\ell\ge1$ the surplus above label zero is

$$
 s_\ell(w)=g_y(w,\ell)-U(w)=
 \begin{cases}
 C_w-A_w,&n(w)=\ell,\\
 -(A_w+P_w),&n(w)\ne\ell,
 \end{cases}
 \qquad s_\ell(1^L)=-T.
$$

For any partition $\Pi$ its support is

$$
 \sum_wU(w)+\sum_{H\in\Pi}
          \max\left(0,\max_{\ell\ge1}\sum_{w\in H}s_\ell(w)\right).
 \tag{220.4}
$$

On the zero face of an eligible coordinate every surplus is
nonpositive. Reset one eligible $a$, except when $n(w)=a$.
A schedule avoiding $a$ preserves its observation cell and the
first-zero label, so each reward reading is identical. In an $N$
schedule querying $a$, the moved vectors leave the corresponding
$a=0$ cell and enter its $a=1$ cell with the other reply fixed.
The source cell is zero-dominated before and after: all remaining
surpluses there are nonpositive. The destination receives only
nonpositive surpluses, so its maximum surplus cannot increase.
The total $U$ is unchanged, and (220.4) proves contraction.

For $O$ with $a$ first, the source is the stopped zero cell and the
destinations are its positive cells. If $a$ is second, the already
stopped first-zero cell is unchanged and the same argument applies to
the two first-positive cells. It applies to singleton and empty
partitions as well. No numerical label has been pruned.

Eligibility survives earlier resets: an output word with an unreset
coordinate $b=0$ receives only old words with $b=0$, so the sums of
$C-A$ there remain nonpositive. The coordinates of $I$ can therefore
be reset successively. These commuting first-zero-preserving word maps
compose to $f_I$, proving simultaneous contraction and exact reading
preservation away from $I$.

Afterward $w_a=0$ implies $n(w)=a$ for every $a\in I$.
For a pair $i<j$, if $i\in I$ its $00,01$ cells are each
zero-dominated: their only possibly rewarded numerical label is $i$
and $C\le A$. Their maxima add to the maximum of the merged stopped
cell. If $j\in I$, the $00$ cell is empty, since $w_j=0$ forces
$n=j$ and hence $w_i=1$. In either case $N=O$ on this pair.
All other $N$ entries are pairs avoiding $I$, whose original readings
persist. This proves (220.2). Since the repaired $O$ support is at most
$W_y+d$, (220.2) proves both directions of (220.3). A subset of $E$
covers all bad edges if and only if $E$ does. $\square$

**推论 220.5（Bounded eligibility saturation）。** Starting at $y_0=y$,
set $y_{t+1}=\rho_{E(y_t)}y_t$. Eligibility is monotone along these
resets. Stop when it no longer enlarges, in at most $L+1$ reset stages.
Write $E_*$ for the terminal set and $V$ for the terminal score.
Then $Q,W$ are unchanged, each fixed support is nonincreasing, pairs
touching $E_*$ have $N=O$, and every pair outside $E_*$ retains its
original $y$ readings. For $\Delta_O(y)\le d$, the saturated reset
is affordable exactly when $E_*$ covers every original bad edge.

**证明。** Each already eligible coordinate's zero face receives only
old words on that face; its $C-A$ sums remain nonpositive.
Each strict enlargement adds a coordinate. If no enlargement occurs,
idempotence leaves the score fixed at the next reset. The maps commute,
so the final score resets their union $E_*$ except at the first zero.
Apply the touched-pair argument and outside reading equality from
220.4 to that union. The graph is the original graph, not a sequence
of separately chosen intermediate graphs. $\square$

Single-pass failure does not rule out saturation. Saturation failure
still does not rule out any unrestricted $(V,\theta)$.

**例 220.6（Interleaved reset and its existing quotient coverage）。**
For $3<j<k<r<s\le L$, $a\ge1$, $g>0$, $h\ge0$, write $w(Z)$ for
the word with exactly zero set $Z$. All unlisted coefficients vanish;
coincident contributions add. Start with

$$
\begin{array}{c|ccc}
 Z&A&C&P\\\hline
 \{3,j,k,r\}&a&0&0\\
 \{3,j,k\}&0&a&0\\
 \{j,k\}&0&1&0\\
 \{j\}&0&0&a-1\\
 \{r\}&h&0&0
\end{array}
$$

Add the existing equal-triple zero core on guards $1,2,3$ and
$J=\{j,k,s\}$: $P=g/3$ at every $w(\{i,q\})$, $P=g/6$ at
$w(\{i\}\cup J)$, and $C=g$ at each $w(\{q\})$.
Take $T=0$. The complete score has

$$
\begin{gathered}
 \beta_j=1+g,\quad\beta_k=g,\quad\beta_r=-h,\quad\beta_s=g,\\
 K=3a+13g/2+h,\quad W=2a-1+7g/2+h,\\
 K-\sum|\beta|=3a-1+7g/2.
\end{gathered}
$$

There is cancellation at class three, pair mass, positive stock and
an eligible negative coordinate between positive coordinates.
For the base without $A_h$, forgetting $r$ makes the $A=a$ and
$C=a$ words have the same observed bits and class three. Their joint
largest reward is $a$; the other rows have largest rewards $1$ and
$a-1$. Thus every schedule avoiding $r$ is bounded by $2a$;
after resetting $r$ this holds for every schedule.

Every original stopped pair involving $r$ has the same bound.
For $(3,r)$ its merged zero branch contributes at most $a$ and the
other base rows at most $a$. For $(j,r)$ all four base rows are in
the merged branch, with maximum $2a-1$. For $(k,r)$ that branch
contributes $a$ and the other branch $a-1$. Any other first address
below $r$ is one on these base words, so $r$ separates the $A=a$
word from rows of joint maximum $a$. When $r$ is first, its zero
branch contributes $a$, and its positive branch has all later bits
one and maximum $a$. Short schedules are coarser. The stopped table
$O(3,j;3,j,0)$ attains $2a$.

For the core the zero-label vectors in $N$ cell order are
$(0,7g/6,7g/6,7g/6)$ for two guards,
$(g/2,2g/3,g,4g/3)$ for guard/positive, and
$(g/2,g,g,g)$ for two positives. Early-label rewards are subsets
of the zero reward; each positive reward $g$ lies in a cell with
at least $g$ of zero reserve. Unused addresses are constantly one.
Thus zero attains all cell maxima and both supports are $7g/2$.
The same $O(3,j;3,j,0)$ attains that support.

The extra $A_h$ has support and baseline $h$. Subadditivity and
this common attaining table give $\Delta_O(y)=1$.
Every $N$ pair avoiding $r$ has support at most $W+1$.
Every word with $C>A$ has $r=1$, so $r\in E(y)$.
Theorem 220.4 gives repaired $N$ cost at most one; the attaining
stopped table survives and both repaired costs equal one.
The original $N(3,r;0,3,0,j)$ collects
$3a+h+13g/6$, with excess $a+1-4g/3$.
Thus $a>4g/3$ gives a strict improvement of the actual input score.
No formula for the original maximum at every parameter is asserted.

At $L=7$, $(j,k,r,s)=(4,5,6,7)$ and $(a,g,h)=(2,1/2,1/2)$,

$$
 \beta=(0,0,0,3/2,1/2,-1/2,1/2),\quad K=39/4,\quad W=21/4.
$$

Here $E(y)=\{1,2,6\}$, the original costs are $(7/3,1)$, and
$\rho_{\{6\}}y$ has costs $(1,1)$. Pair $(3,6)$ has original cell
maxima $(2,31/12,1/2,5/2)$, whose sum is $91/12$.

This example contributes no additional certificate-covered quotient.
Its whole quotient family already has an exact-$Q$ zero-cost score.
Indeed its base quotient has $\beta_j=1$, $\beta_r=-h$,
$K=3a+h$. In the existing one-pivot formula XI 214.2 put
$H=3a+h-1$. Its protection quantity is

$$
 J=\max\left(h,\frac{H+(j-2)h}{j-1},\frac{2H}{j}\right).
$$

Since $H-h=3a-1\ge2$ and $j\ge4$, each displayed term is at most
$H-1$. Formula 214.2 therefore gives minimum zero. Adding the
same old zero-cost core gives one exact-$Q$ zero-cost representative
of the entire displayed family. The structural reset, edge criterion
and bounded saturation in 220.4–220.5 are the content of this unit;
the family illustrates their operation.

### 220.3 Pooled prefix domination and one common coefficient total

**定义 220.7（Joint suffix measures and the domination cone）。**
Choose $1\le k<L$ and $m=L-k$. For words with $n(w)\le k$ reset
all prefix bits except the first zero to one, preserving the entire
suffix $v\in\{0,1\}^m$. Push $A,C,P$ by that same map and sum
collisions. Tail words and $T$ remain fixed. Call the map $\rho_k$.
It is linear, idempotent and preserves $Q,W$.

On the pooled score let $u_i(v)=A+P$, $h_i(v)=C+P$ at the word
with sole prefix zero $i\le k$ and suffix $v$. On all-prefix-one
words let $z(v)=A+P$, with $z(1^m)=T$. For each $j>k$, let
$r_j(v)=C+P$ on its tail first-zero class, zero elsewhere, including
at $1^m$. All these are measures on the same suffix cube. Set

$$
\begin{gathered}
 U=\sum_{i\le k}u_i,\quad s_i=|u_i|,\quad S=\sum_i s_i,
 \quad Z=|z|,\quad R(H)=\max_{j>k}r_j(H),\\
 d_i=s_i-|h_i|=-\beta_i,\quad D=\sum_i d_i,
 \quad E=-\beta_1-\beta_2.
\end{gathered}
$$

The cone $\mathcal D_k$ consists of inputs whose pooled measures obey
both families of inequalities:

$$
\begin{aligned}
 \mathrm{D1}:&\quad h_i(H_{a,t})\le u_i(H_{a,t})
       &&(i\le k,\ a>k,\ t=0,1),\\
 \mathrm{D2}:&\quad h_i(H)\le(U+z)(H)
       &&(i\le k,\ H\text{ any four-cell suffix pair cell}).
\end{aligned}\tag{220.5}
$$

Here $H_{a,t}=\{v:v_a=t\}$; full address subscripts are retained.
For $m=1$ D2 is empty. D1 gives $0\le d_i\le s_i$.
For $k\ge2$, $E=d_1+d_2$; for $k=1$, $\beta_2$ is unrestricted
and $E$ can be negative. There is no pointwise $C\le A$ hypothesis.
Tail signs, interleavings, cancellations, $P$ and $T$ are unrestricted.
The conditions must be checked before discarding any $h_i$ or overlap
data.

**引理 220.8（Exact prefix-label inactivity and contraction）。**
D1–D2 are equivalent to each prefix numerical label being dominated
by zero in every legal pooled query cell. For $y\in\mathcal D_k$,
each fixed complete $N$ or $O$ schedule satisfies
$B_C^S(\rho_ky)\le B_C^S(y)$.

**证明。** Necessity uses the mixed $N$ cell $w_i=0,v_a=t$,
which contains only donor $i$, and the four suffix-pair cells.
For sufficiency sum D1 over $t$ to get $|h_i|\le s_i$.
Empty and suffix-singleton cells are dominated. In a prefix singleton
or prefix pair, donor $i$ is on its own zero side or in $11$, and
its total numerical reward is at most $s_i$. In a mixed pair, donor
$i$ on the zero side satisfies D1; every other donor $\ell$ on the
one side has $h_\ell(H)\le u_\ell(H)\le(U-u_i+z)(H)$.
D2 covers suffix pairs. Every stopped cell is an $N$ cell or a
union of them, so summing the same inequalities covers $O$.
This proves equivalence without changing the output catalog.

Now reduce temporarily to labels zero and $j>k$. The old full
support bounds this reduced support, whereas on the pooled score they
are equal by the proved domination. For the reduced labels a partition
has support equal to its total zero reward plus

$$
 \sum_H\bigl(\max_{j>k}r_j(H)-\operatorname{base}(H)\bigr)_+.
$$

With no prefix query, each reading is unchanged. With one prefix
query, all tail numerical mass lies on its one side. Moved zero mass
exits a tail-reward-free zero side and enters the one side, with suffix
replies unchanged. The former surplus is zero and the latter can only
decrease. In a mixed stopped pair the prefix is first and its zero
side is the stopped cell. With two prefix queries, tail numerical
mass lies entirely in $11$; its zero mass can only increase, since
all donors other than the two queried first-zero classes move toward
$11$. Other cells have no tail numerical reward. This exhausts all
fixed schedules, including shorter ones, and proves contraction.
It is a score operation, not a source garbling or a free query.
$\square$

**定理 220.9（Exact common-$K$ reconstruction）。**
Retain one tuple $(u_i,z,r_j,d_i,K)$ with the stated nonnegative
first-zero-supported measures and $0\le d_i\le s_i$.
Its prefix quotient is $\beta_i=-d_i$, and its tail quotient is
$\beta_j=|r_j|-z(\Omega_j)$. Define

$$
\begin{aligned}
 K_{\rm lo}&=S+z(1^m)+\sum_{v\ne1^m}\max(z(v),r_{n(v)}(v)),\\
 K_{\rm hi}&=2S-D+z(1^m)+\sum_{v\ne1^m}(z(v)+r_{n(v)}(v)).
\end{aligned}\tag{220.6}
$$

Here $n(v)$ is its full tail label. A canonical score in $\mathcal D_k$
realizes these retained data if and only if
$K_{\rm lo}\le K\le K_{\rm hi}$. The entire score is reconstructed
using one scalar $t=(K-K_{\rm lo})/(K_{\rm hi}-K_{\rm lo})$ if the
interval has positive width, and $t=0$ otherwise. For $s_i>0$ set

$$
\begin{aligned}
 C_i(v)&=t(s_i-d_i)u_i(v)/s_i,\\
 A_i(v)&=C_i(v)+d_i u_i(v)/s_i,\\
 P_i(v)&=u_i(v)-A_i(v).
\end{aligned}\tag{220.7}
$$

If $s_i=0$, $d_i=0$ and all three coefficients are zero.
At a tail zero word set

$$
 P(v)=(1-t)\min(z(v),r_{n(v)}(v)),\quad
 A(v)=z(v)-P(v),\quad C(v)=r_{n(v)}(v)-P(v),
 \qquad T=z(1^m).\tag{220.8}
$$

Applied after pooling an input in $\mathcal D_k$, this construction
defines a generally nonlinear idempotent map $J_k$ preserving $Q,W$.
Every fixed support of $J_ky$ equals that of $\rho_ky$ and is at
most its original value.

**证明。** For a donor, $u=A+P$ and $|A|-|C|=d$.
Its total coefficient cost is $s+|C|$, with
$0\le|C|\le s-d$: pooled inactivity gives $|C+P|\le s$.
At a tail word the same $P$ contributes to $z=A+P$ and $r=C+P$,
so $0\le P\le\min(z,r)$. Its cost $z+r-P$ ranges from
$\max(z,r)$ to $z+r$. The terminal cost is $z(1^m)$.
Summing gives exactly (220.6), with $P$ paid once.

Conversely (220.7)–(220.8) are nonnegative and preserve all retained
measures and quotient entries. Their cost is
$K_{\rm lo}+t(K_{\rm hi}-K_{\rm lo})=K$.
For a donor the new $h_i=(1-d_i/s_i)u_i\le u_i$ pointwise,
so D1–D2 hold. Zero donors and zero interval width have the stated
unique formulas; both endpoints use the same scalar on all words.
All-ones donor suffixes and multiple-zero words remain included.

For an actual input the interval is feasible by necessity. On the
pooled input and reconstructed score prefix labels are inactive and
all zero and tail measures coincide. Each fixed support therefore
coincides. Also $W=S+Z-E$ is unchanged. Reextracting the tuple gives
the same $K$ and the same $t$, proving $J_k^2=J_k$.
$\square$

**定理 220.10（Complete costs and cone-restricted joint feasibility）。**
Let $\Psi_C$ be the maximum of zero and these expressions, omitting
pair types that do not exist:

$$
\begin{aligned}
 &\bigl(R(\{0,1\}^m)-(S-s_i-s_h+Z)\bigr)_+
                   &&(i<h\le k),\\
 &\sum_{t=0,1}\bigl(R(H_{a,t})-(U-u_i+z)(H_{a,t})\bigr)_+
                   &&(i\le k<a),\\
 &\sum_{H\in\Pi_C(a,b)}\bigl(R(H)-(U+z)(H)\bigr)_+
                   &&(k<a<b\le L).
\end{aligned}\tag{220.9}
$$

The suffix $\Pi_N$ has four cells and $\Pi_O$ its actual three
stopped cells. On a pooled score satisfying D1–D2, and on its
canonical reconstruction,

$$
 B_C=S+Z+\Psi_C,\qquad \Delta_C=E+\Psi_C.\tag{220.10}
$$

For fixed $q=(\beta,K)$, a full score in $\mathcal D_k$ of cost at
most $b$ exists if and only if one tuple satisfies all quotient
equations, $0\le d_i\le s_i$, the common interval (220.6), and
$E+\Psi_C\le b$. This is simultaneous finite convex feasibility.
When the fiber is nonempty both class minima are attained separately;
no equality of the two minima or common minimizer is asserted.

**证明。** After prefix domination only zero and tail numerical
rewards matter. In a prefix pair only $11$ has tail numerical reward,
with zero mass $S-s_i-s_h+Z$. In a mixed pair the prefix-zero side
contributes $s_i$ and the one side has zero measure $U-u_i+z$.
This gives the same mixed expression for $N$ and $O$. A suffix pair
has exactly the four or three cells displayed. These yield (220.9).

Empty schedules are bounded by refinement. For $k\ge2$ a prefix
singleton is bounded by a prefix pair. For $k=1$ any mixed pair
refines that singleton. A suffix singleton is bounded by the mixed
expression at the same suffix address, since
$U-u_i+z\le U+z$. Thus shorter schedules are included, also when
$m=1$. The identity $W=S+Z+\beta_1+\beta_2$ proves (220.10),
including the possibly negative $k=1$ offset. Cost nonnegativity
follows independently from the legal anchor.

For necessity pool a feasible input; 220.8 does not increase cost.
Retain its one tuple and apply 220.9. Conversely reconstruct that
tuple once. This proves the equivalence. Maximum reward and positive
part are convex in the common measures; $K_{\rm lo}$ is convex and
$K_{\rm hi}$ linear, giving the finite convex relation.
At fixed $K$ the original coefficient fiber is a closed subset of
the compact nonnegative simplex of total $K$, and the costs are
continuous maxima over a finite catalog. Each minimum is therefore
attained. These are cone-restricted assertions, not unrestricted
full-fiber necessity statements. $\square$

After verifying D1–D2, the $h_i$ and pointwise overlap variables are
unnecessary for costs and quotient feasibility. For $N_s=2^m$ the
retained measure entries number
$(k+2)N_s-1$: $kN_s$ donor entries, $N_s$ zero-tail entries and
$N_s-1$ tail numerical entries. At fixed $Q$, $d_i,K$ are parameters.
For $L=8,k=3$ this is $159$ rather than the $766$ original
$A,C,P,T$ entries. It is a normal-form bound, not a global minimum
dimension or a computation-time claim. The common suffix allocation
and common $K$ interval cannot be discarded.

**例 220.11（Nonpointwise domination and failure of automatic affordability）。**
At $L=4,k=2$ the complete nonzero rows, in $(A,C,P)$ order, are

| Word | $A$ | $C$ | $P$ |
| --- | --- | --- | --- |
| 0000 | 0 | 1 | 0 |
| 0001 | 1 | 0 | 0 |
| 0010 | 1 | 0 | 0 |
| 0011 | 0 | 1 | 0 |
| 1000 | 1 | 0 | 0 |
| 1011 | 1 | 0 | 0 |
| 1100 | 0 | 2 | 0 |
| 1110 | 0 | 2 | 0 |

Take $T=1/3$. All unspecified rows vanish. Here
$\beta=(0,-2,2,2)$, $K=31/3$, $W=7/3$.
The complete $(B_N,B_O)$ supports are $(8,8)$ before pooling and
$(19/3,6)$ after it. The retained common interval is
$[25/3,31/3]$. Donor one's singleton marginals agree, and donor
two's zero mass covers its suffix $00,11$ excess in D2.
Thus D1–D2 hold although $C>A$ at $0000$ and $0011$.

Scaling the original by $3/17$ gives an actual unit-$O$ score.
Its canonical reconstruction has $N$ cost $12/17$, the same $Q$,
and residual zero. However $x=(3/11)\rho_ky$ itself is unit $O$
and $\Delta_N(J_kx)=12/11>1$. The operation alone is not automatically
affordable, even inside $\mathcal D_k$. This says nothing against
a different allocation or residual certificate for $x$.

**例 220.12（Stock, cancellation and signed interleaved tail）。**
At $L=8,k=3$ take the following full nonzero rows and $T=0$:

| Word | $A$ | $C$ | $P$ |
| --- | --- | --- | --- |
| 00001001 | 1/2 | 1/6 | 0 |
| 00011001 | 1/3 | 0 | 0 |
| 00011101 | 1/3 | 0 | 0 |
| 10001001 | 1/3 | 0 | 1/4 |
| 10011001 | 1/3 | 0 | 0 |
| 10011101 | 1/3 | 0 | 0 |
| 11001001 | 1/3 | 0 | 0 |
| 11011001 | 1/3 | 0 | 0 |
| 11011101 | 1/3 | 0 | 0 |
| 11101001 | 0 | 1 | 0 |
| 11110111 | 1/2 | 0 | 0 |
| 11111001 | 0 | 1 | 0 |
| 11111011 | 1/5 | 1/5 | 1/3 |
| 11111101 | 0 | 1 | 0 |
| 11111110 | 1/4 | 0 | 0 |

Then

$$
 \beta=(-1,-1,-1,1,-1/2,1,1,-1/4),\quad
 K=121/15,\quad W=27/10,\quad K-\sum|\beta|=79/60.
$$

D1–D2 hold. Both costs are $13/4$ before pooling and $13/6$
afterward. Scaling by $4/13$ gives unit $O$ and a same-$Q$ canonical
score of $N$ cost $2/3$. Early and late pair mass, cancellation,
negative tail coordinates and zero terminal mass are all present.

**反例 220.13（Nonpositive totals cannot replace cell domination）。**
At $L=5,k=3$ use $P=T=0$ and the following rows:

| Word | $A$ | $C$ | $P$ |
| --- | --- | --- | --- |
| 01110 | 1 | 0 | 0 |
| 10001 | 0 | 3 | 0 |
| 10011 | 1 | 0 | 0 |
| 10111 | 2 | 0 | 0 |
| 11000 | 1 | 0 | 0 |
| 11010 | 1 | 0 | 0 |
| 11011 | 0 | 2 | 0 |

Here $\beta=(-1,0,0,0,0)$, $K=11$, $W=5$.
Pooling moves $C=3$ from $10001$ to $10101$ and $A=1$ from
$10011$ to $10111$. D1 fails for donor two at suffix address
four, reply zero: $h_2=3>u_2=0$. The complete support catalog is

| Schedule | $N$ before | $N$ after | $O$ before | $O$ after |
| --- | --- | --- | --- | --- |
| empty | 6 | 6 | 6 | 6 |
| 1 | 6 | 6 | 6 | 6 |
| 2 | 6 | 6 | 6 | 6 |
| 3 | 6 | 6 | 6 | 6 |
| 4 | 8 | 8 | 8 | 8 |
| 5 | 6 | 6 | 6 | 6 |
| 1,2 | 6 | 6 | 6 | 6 |
| 1,3 | 6 | 6 | 6 | 6 |
| 1,4 | 8 | 8 | 8 | 8 |
| 1,5 | 6 | 6 | 6 | 6 |
| 2,3 | 8 | 6 | 6 | 6 |
| 2,4 | 9 | 9 | 6 | 6 |
| 2,5 | 8 | 8 | 8 | 8 |
| 3,4 | 8 | 10 | 6 | 9 |
| 3,5 | 8 | 8 | 6 | 6 |
| 4,5 | 9 | 9 | 8 | 8 |

Thus $B_N:9\to10$ and $B_O:8\to9$. A sign-only hypothesis
cannot justify either pooling or dropping prefix numerical rewards.
This is a counterexample to that weakening, not an original separation.

### 220.4 Interior masks and the exact transfer residual

**定义 220.14（Interior erasure without renumbering）。** For any
$E\subseteq\{3,\ldots,L\}$ let $f_E$ set exactly these bits to one,
without changing the addresses. Put $k_E(w)=n(f_E(w))$, or $\infty$
if the image is $1^L$. Define $z=\mathcal T_Ey$ as follows.
If the original first zero is retained, push $A,C,P$ separately to
$f_E(w)$. If it is erased, discard $C_w$ and route $A_w+P_w$ as
$A$ to the new first-zero word, or as $T$ if terminal. Keep original
$T$ and add coincident contributions. The ambient $L$ addresses,
all words, labels and independent event rows remain. This transforms
proof weights, not sources or acquisition probability laws.

**定理 220.15（Commuting contractions and cumulative transfer cuts）。**
For every full nonnegative $y$ and any masks $D,E\subseteq\{3,\ldots,L\}$,
$\mathcal T_E$ is positive linear and idempotent, and

$$
 \mathcal T_D\mathcal T_E=\mathcal T_{D\cup E},\quad
 W_z=W_y,\quad K_z=K_y-C_E,\quad B_C(z)\le B_C(y)
 \quad(C=N,O),\tag{220.11}
$$

where $C_E=\sum_{n(w)\in E}C_w$. Hence both costs are nonincreasing.
For $\gamma=\beta(y)-\beta(z)$, the first two entries vanish;
at erased $j$, $\gamma_j=\beta_j(y)$, and at retained late $k$,

$$
 \gamma_k=\sum_{n(w)\in E,\ k_E(w)=k}(A_w+P_w).
$$

For every $3\le t\le L$ let $R_t=\sum_{j\le t}\gamma_j$.
The exact transfer identity is

$$
 R_t=\sum_{n(w)\in E,\ n(w)\le t}C_w
   +\sum_{n(w)\in E,\ k_E(w)\le t}P_w
   -\sum_{n(w)\in E,\ n(w)\le t<k_E(w)}A_w.\tag{220.12}
$$

Infinity never satisfies $k_E(w)\le t$. The one final residual is

$$
\begin{aligned}
 \Theta_E&=\sigma_H(Q(y)-Q(z))\\
 &=\max\left(0,\max_{3\le t\le L}\frac{R_t}{t-1},
       \max_{3\le t\le L}
       \frac{3R_t+(t-2)(R_L-C_E)}{t+1}\right).
\end{aligned}\tag{220.13}
$$

In particular $\Theta_E=0$ if and only if every $R_t\le0$.
These are exact zero-charge cuts for this operation, not conditions
necessary for an unrestricted certificate.

**证明。** Retained first-zero classes keep their coefficient types.
An erased late $A$ becomes late $A$ or terminal mass, contributing the
same baseline and total cost. An erased $P$ does the same. Erased late
$C$ had no baseline and is the only discarded cost. This proves the
$W,K$ identities. Subtracting the class totals gives $\gamma$.
In its cumulative sum, an erased $A$ cancels once it arrives, remains
negative while crossing the cut, and an erased $P$ contributes only
on finite arrival. Discarded $C$ contributes at its old address.
This proves (220.12), including terminal arrivals.

For support contraction, every erased bit is one on the image support,
and an output label in $E$ earns zero. Replace such an output in a
new table by zero; rewards cannot decrease. Fix replies to erased
requests to one and delete those requests. The remaining empty,
singleton or pair table is legal in the same catalog. In $O$ the
remaining schedule is increasing and stops at its first queried zero.
For an original retained first zero the rewards agree, since its
label and all remaining queried bits agree. For an erased first zero
the remaining outputs exclude its old label, so its old reward is
exactly $(A+P)[\ell=0]$, equal to the transformed reward. The discarded
$C$ earns nothing. The terminal word agrees as well. Thus each new
table reward is at most the reward of an original legal table.
Maximizing proves the two support contractions without restricting
any earlier or unqueried retained output.

For composition the final bit word is $f_{D\cup E}(w)$.
Original $C$ survives precisely when its original first zero survives
both masks. Original $P$ becomes base precisely when that zero is
erased, and then follows subsequent retained first zeros to the final
word or terminal. Original $A$ follows the same route. These
coefficientwise observations prove composition, commutation and
idempotence, also for overlapping masks.

Reuse the full hull vertices of VI 198.5:
$o=0$, $p=(1,0,\ldots;0)$,
$u_t=(1/(t-1)\text{ on the first }t,0\text{ later};0)$, and
$v_t=(1\text{ on the first }t,e_t\text{ later};e_t)$ with
$e_t=(t-2)/(t+1)$, $3\le t\le L$.
The early residuals vanish, so $o,p$ read zero.
The other readings are $R_t/(t-1)$ and
$[3R_t+(t-2)(R_L-C_E)]/(t+1)$, proving (220.13).
Zero charge forces every $R_t\le0$ through $u_t$.
Conversely these inequalities give $R_L-C_E\le0$ since $C_E\ge0$,
so all displayed readings are nonpositive. This proves sufficiency
and all closed equality cases. $\square$

**推论 220.16（One-pivot landing with the same final budget）。**
Suppose an actual full $y$ has $\Delta_O(y)\le1$ and a mask $E$
lands in a quotient $Q(z)$ with at most one positive late coordinate.
The existing signed one-pivot minimum XI 214.2 gives one full $V$
with $Q(V)=Q(z)$ attaining both unrestricted exact-$Q(z)$ minima,
with common value $d_*(Q(z))$. If every $R_t\le0$, then $(V,0)$
satisfies (220.1). With positive charge it supplies a certificate
precisely when this chosen score and residual obey

$$
 d_*(Q(z))+\Theta_E\le1.\tag{220.14}
$$

**证明。** Any full score has $K\ge\sum|\beta|$, so the supplier's
stock hypothesis holds for $z$. Its attaining score satisfies
$d_*\le\Delta_O(z)\le\Delta_O(y)\le1$. Its exact quotient leaves
residual $\Theta_E$. At zero charge this proves (220.1); at positive
charge the additional inequality (220.14) is required. For the same
$b\in H_N$ and same feasible $\lambda$,

$$
 F_{Q(y)}(b,e)\le M d_*+\Theta_E\le\max(1,M).
$$

The latter conclusion uses (220.14), not unit $O$ alone.
For a union of masks compute its final residual once; separately
optimized per-coordinate residuals are not separate budgets.
$\square$

The one-pivot minimum and its water filling are reused suppliers.
Terminal masks are the existing operation of XII 218.8–218.9;
they add no separate scope here. No proof establishes an affordable
landing mask for every unit-$O$ input.

**例 220.17（A full zero-terminal input and explicit zero-cost landing）。**
For every $L\ge10$ and $\rho\ge0$, take

$$
\begin{array}{c|ccc}
 Z&A&C&P\\\hline
 \{3,9,10\}&1/2&0&\rho\\
 \{4,9,10\}&1/3&0&0\\
 \{5,9,10\}&1/6&0&0\\
 \{6,9\}&0&1/2&0\\
 \{7,10\}&0&1/2&0\\
 \{8\}&0&1/3&0
\end{array}
$$

All other coefficients and $T$ vanish. Then

$$
\begin{gathered}
 \beta=(0,0,-1/2,-1/3,-1/6,1/2,1/2,1/3,0,\ldots),\\
 K=7/3+\rho,\quad W=1+\rho,\quad K-\sum|\beta|=\rho.
\end{gathered}
$$

The full $N(9,10;0,6,7,8)$ collects all $7/3+\rho$ coefficient
mass. In any stopped table output three can be replaced pointwise by
zero without loss, since it earns only the pair mass. The remaining
useful labels $0,6,7,8$ have total rewards
$1+\rho,1/2,1/2,1/3$. A stopped table has at most three cells;
any three label totals sum to at most $2+\rho$.
The table $O(6,7;6,7,0)$ attains it. Therefore the complete costs
are $\Delta_N=4/3$, $\Delta_O=1$.

Erase $E=\{3,\ldots,L\}\setminus\{6\}$.
The result has $C=1/2$ at $w(\{6\})$ and $T=1+\rho$.
The discarded $C_E=5/6$, and the complete cuts are

$$
 R_3=-1/2,\quad R_4=-5/6,\quad R_5=R_6=-1,
 \quad R_7=-1/2,\quad R_t=-1/6\ (t\ge8).
$$

Thus $\Theta_E=0$. An explicit final score, with $H=1+\rho$, is
$P=H/6$ at $w(\{i,6\})$ for $i=1,\ldots,5$,
$T=H/6$, and $C=1/2$ at $w(\{6\})$.
It has the landing quotient, $W=H$ and both supports $H$.
Indeed a cell containing the pivot correct atom has zero reserve at
least $4H/6$: two guards exclude at most two of the five pair atoms;
a guard and pivot leave four; pivot and an inactive coordinate leave
five. Short schedules leave at least as much. Since $4H/6\ge1/2$,
label six cannot beat zero. Guard labels are pointwise dominated by
zero and all other labels earn nothing. This covers every schedule
and earlier or unqueried output. Thus $(V,0)$ is one certificate.
No exclusion of all older exact-$Q$ or convex/polar constructions is
claimed for this example.

**反例 220.18（Arrived pair mass is essential）。** At $L=5$ put only
$P=1$ at $w(\{4,5\})$ and erase $E=\{4\}$.
Although old $\beta_4=0$, the pair mass becomes $A=1$ at
$w(\{5\})$, so the residual has $\gamma_5=1$ and $C_E=0$.
Formula (220.13) gives $\Theta_E=1$, attained at $v_5$.
Both scores themselves have zero query cost. Thus a zero old net
coordinate does not make interior erasure free, and dropping the
arrived-$P$ term in (220.12) gives a false accounting rule.
This is an operation counterexample, not a separation of the original
classes.

### 220.5 An actual joint block funding queried-label gates

**定义 220.19（Fixed remainder, zero-face funding and singleton gates）。**
Take one full feasible allocation $\lambda=\kappa+\eta$ with masses
$M-s$ and $s$. Suppose $\eta$ outputs only $\mathcal A\cup\{0\}$,
where $\mathcal A\subseteq\{1,\ldots,L\}$. For its actual wordwise
output measures write

$$
 r_w=(1-M)e_{R(w)}+\kappa_w,\qquad
 \delta_a=\max\left(0,b_a-e-\min_{w\in\Omega_a}r_w(a)\right),
 \quad \zeta_a=\min_{w:w_a=0}\eta_w(a).
 \tag{220.15}
$$

The remainder may be signed. The maximum with zero makes a gate mass
nonnegative; it does not clip an original event demand.
The stopped singleton $O(a;a,0)$ queries $a$, outputs $a$ on zero
and zero on one. All minima in (220.15) use the same actual block and
fixed remainder.

**定理 220.20（Same-block gate retraction and its exact operational scope）。**
If $\delta_a\le\zeta_a$ for every $a\in\mathcal A$, replace the
entire $\eta$ by $\delta_a$ units of each gate $O(a;a,0)$ and
$s-\sum_a\delta_a$ units of empty output zero. Keep $\kappa$.
The new allocation has exactly mass $M$ and satisfies every original
event row. Base and independent pair rows improve pointwise;
correct rows remain feasible but need not improve pointwise.
If $\kappa$ is already $O$, the result is an $O$ witness.
If $\kappa$ belongs to the existing $W_N$ catalog of VI 190.2,
VI 194.1 then supplies a same-mass $O$ witness.
For arbitrary $\kappa$ this is only a feasible $N$ surgery.

The inequalities are necessary as well as sufficient for this specified
fixed-remainder singleton replacement whose positive output coordinates
are componentwise dominated by the old block. They are not necessary
for general $O$ feasibility or arbitrary surgery.

**证明。** Define $q_w(a)=\delta_a[w_a=0]$.
It is at most $\eta_w(a)$ on the zero face by hypothesis and off
that face by nonnegativity. Choose a single word with every bit in
$\mathcal A$ zero. At this word the bounds coexist, giving
$\sum_a\delta_a\le\sum_a\eta_w(a)\le s$.
Thus the empty-zero mass is nonnegative and the common block is funded.

Now $q_w(0)=s-\sum_aq_w(a)$, whereas
$\eta_w(0)=s-\sum_a\eta_w(a)$.
Their difference is $\sum_a(\eta_w(a)-q_w(a))\ge0$,
proving every base row, including the positive word.
For each first-zero label $n$ independently,

$$
 q_w(0)+q_w(n)
 =s-\sum_{a\ne n}q_w(a)
 \ge s-\sum_{a\ne n}\eta_w(a)
 =\eta_w(0)+\eta_w(n).
$$

For $n\notin\mathcal A$ the numerical coordinates are zero in both
blocks. This proves the pair rows separately, without replacing them
by a sum of separately minimized singleton bounds.
On $\Omega_a$, the new correct coordinate is $r_w(a)+\delta_a$,
whose minimum is at least $b_a-e$. Outside $\mathcal A$ the old
block supplied no correct mass, so the unchanged remainder already
satisfies its correct demand. This covers negative demands as well.
Adding the same remainder proves all rows even if it is signed.

For necessity a candidate gate mass $t_a$ must be at least
$\delta_a$ to meet the correct demand and at most $\zeta_a$ to be
componentwise dominated on the zero face. This gives exactly the
stated criterion. The construction treats empty $\mathcal A$,
zero masses, ties and closed endpoints with the same inequalities.
For $W_N$ invoke VI 194.1 after this replacement; that supplier
preserves mass, improves base/pair coordinates and correct-class
lower envelopes, without asserting pointwise correct dominance.
$\square$

For precision, $W_N$ allows every empty output; singleton $i$ uses
$\{0,i\}$ on zero and $\{0,i+1,\ldots,L\}$ on one.
Its pair $i<j$ allows $\{0,i\}$ on $00,01$,
$\{0,i+1,\ldots,j\}$ on $10$, and
$\{0\}\cup(\{i+1,\ldots,L\}\setminus\{j\})$ on $11$.
$W_O$ additionally shares the first two outputs. These are sufficient
witness catalogs, never restrictions on full competitors.

Whenever this operation yields an $O$ witness $\mu$ of the same mass,
for every full nonnegative score

$$
 F_{Q(y)}(b,e)=y\cdot h(b,e)
 \le\sum_D\mu_D\,y\cdot(z_D-r)\le M\Delta_O(y).
 \tag{220.16}
$$

Thus at this same point an actual unit-$O$ score cannot give
$F_{Q(y)}>M$. No proof supplies a qualifying decomposition at every
point or constructs an unrestricted $(V,\theta)$ for every input.

**例 220.21（Four distinct labels and a joint Hamming block）。**
Take four pairwise distinct labels $a_{00},a_{01},a_{10},a_{11}$,
each strictly before suffix addresses $i<j$, $L\ge j$, and $h\ge0$.
One table $N(i,j;a_{00},a_{01},a_{10},a_{11})$ has mass $h$.
For each label with code $(u,v)$ add two mass-$h$ donors, one for
$(a_{uv},i)$ and code bit $u$, one for $(a_{uv},j)$ and bit $v$:
for bit zero use $N(a_{uv},k;0,a_{uv},0,0)$;
for bit one use $N(a_{uv},k;a_{uv},0,0,0)$.
These nine actual tables form one block $\eta$ of mass $9h$.
Distinctness is essential to the following coordinate identity.

For every word on the zero face of $a_{uv}$, with
$p=(w_i,w_j)$,

$$
 \eta_w(a_{uv})=h\bigl([p=(u,v)]+d_H(p,(u,v))\bigr).
 \tag{220.17}
$$

At Hamming distances zero, one and two this is $h,h,2h$.
The code table contributes only at its code; the two donors each
contribute on the corresponding mismatch. Thus each zero-face minimum
is $h$, including on the actual first-zero class. With $w_{a_{uv}}=1$
the donors give zero; choosing a different suffix code gives zero
also from the code table. Its global coordinate minimum is zero.
It therefore is not a global suffix-only block.

If all actual remainder deficits are at most $h$, replace all nine
tables together. At equal deficits $h$, four gates of mass $h$ and
empty zero of mass $5h$ suffice. At a word with all four proposed
labels zero the four lower masses coexist and are paid once.
Theorem 220.20 supplies every row and resource conclusion. This is
not a separately normalized replacement of the code table alone.

**例 220.22（A compensated occurrence inside the actual $H_N$）。**
At $L=6$ use code labels $1,2,3,4$, suffix addresses $5,6$, and
$h=1/25$. Set

$$
 (b_1,\ldots,b_6;e)
 =(12/25,12/25,12/25,21/50,21/50,9/25;6/25).
 \tag{220.18}
$$

The nine-table block is that of 220.21. The fixed stopped remainder
$\kappa$ is the following complete allocation of mass $3/5$:

| Table | Weight |
| --- | --- |
| $O(1,2;0,2,3)$ | 2/25 |
| $O(1,2;1,2,3)$ | 1/50 |
| $O(1,2;1,2,4)$ | 3/50 |
| $O(1,3;1,3,0)$ | 3/50 |
| $O(1,4;1,4,0)$ | 1/50 |
| $O(2,3;0,3,0)$ | 1/50 |
| $O(2,3;0,3,4)$ | 1/50 |
| $O(2,4;0,4,0)$ | 1/25 |
| $O(3,5;0,5,0)$ | 1/10 |
| $O(4,5;0,5,0)$ | 3/50 |
| $O(4,5;0,5,6)$ | 1/50 |
| $O(4,6;0,6,0)$ | 1/50 |
| $O(5,6;0,6,0)$ | 2/25 |

Then $\lambda=\kappa+\eta$ has mass $24/25$ and its affine
anchor fill is $R/25$, producing one probability law $p_N$.
Equivalently add $R/25$ to $\lambda$ to obtain one feasible mass-one
configuration; its $G$ column is zero. Replace the whole block by
four gates of mass $1/25$ and empty zero of mass $1/5$, giving one
stopped law $p_O$ with the same total mass and anchor fill.

All hull coordinates are nonincreasing and positive, $b_2=b_3$,
and $b_6\ge e$. The tail sum is $42/25=7e$; the other hull
expression equals $12/25\le1$. Feasibility is supplied by the full
$3(2^6-1)+1=190$ independent rows, not inferred from this hull check.
The rowwise class minima of the two actual laws are

| First zero | $N$ base | $N$ correct | $N$ pair | $O$ base | $O$ correct | $O$ pair |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 13/25 | 6/25 | 19/25 | 13/25 | 6/25 | 19/25 |
| 2 | 12/25 | 6/25 | 19/25 | 13/25 | 6/25 | 19/25 |
| 3 | 13/25 | 6/25 | 19/25 | 13/25 | 6/25 | 19/25 |
| 4 | 27/50 | 9/50 | 19/25 | 31/50 | 9/50 | 4/5 |
| 5 | 29/50 | 9/50 | 19/25 | 31/50 | 9/50 | 4/5 |
| 6 | 33/50 | 3/25 | 39/50 | 7/10 | 3/25 | 41/50 |

Positive base is $19/25$ for $N$ and $4/5$ for $O$.
Compare each row with $1-b_n-e$, $b_n-e$, $1-e$.
These are minima over all words in each class of these same laws;
the minimizing words need not coincide. In particular class-two
pair minimum $19/25$ is not the sum $12/25+6/25$ of independent
singleton minima.

For a direct formula put $x_j=w_j$. The gated base polynomial is

$$
\begin{aligned}
50p_O(w,0)={}&32-2x_1-2x_2-3x_3-3x_4-4x_5\\
 &+2x_1x_2+3x_1x_3+x_1x_4+x_2x_3+2x_2x_4\\
 &+5x_3x_5+3x_4x_5+x_4x_6+4x_5x_6.
\end{aligned}\tag{220.19}
$$

Write $\sigma_1=00,\sigma_2=01,\sigma_3=10,\sigma_4=11$ and

$$
 D(w)=1+\sum_{a\le4:\ w_a=0}
                   (d_H((x_5,x_6),\sigma_a)-1)\ge0.
$$

For a fixed two-bit word only its matching code contributes $-1$;
the other terms are zero or one, proving the displayed inequality.
The listed allocations give

$$
\begin{gathered}
 p_N(w,0)=p_O(w,0)-D(w)/25,\\
 p_O(w,n)=b_n-e\quad(w\in\Omega_n),\\
 p_N(w,n)=p_O(w,n)+[\,(x_5,x_6)=\overline{\sigma_n}\,]/25
                   \quad(n\le4),
\end{gathered}\tag{220.20}
$$

and the correct coordinates coincide for $n=5,6$.
The polynomial follows by summing the thirteen stopped tables and
four gates; the Hamming identity gives the base difference and the
extra correct coordinate. Evaluating the remaining Boolean variables
in each first-zero class gives the displayed class minima, proving
all 190 rows with the independent pair event retained.

For the entire nine-table block all four actual deficits and all four
zero-face minima are exactly $1/25$. If the eight donors are kept in
the remainder and only the code table is replaced by constants,
each of four labels requires $1/25$: $4/25$ is required from a block
of mass $1/25$. If the whole block is replaced by its least-demand
constants, the remaining constant-zero mass is $5/25$.
At the positive word the unchanged remainder contributes $11/25$,
so base becomes $16/25<19/25$. Gates instead give base $20/25$.
These are obstructions to those local constant operations at this
actual feasible point. The two actual laws both satisfy the cap;
there is no original $N/O$ separator here.

**推论 220.23（Positive vanishing marked-law family with attained closed cap）。**
For every $0<t\le1$, multiply all six amplitudes in (220.18) and
its cap by $t$. Mix each of the padded $N$ and gated $O$ laws with
empty zero of mass $1-t$. Each is one mass-one law and one complete
allocation. Use the original marked amplitude sequence

$$
 a_n(t)=
 \begin{cases}
 t b_n,&n\le6,\\
 (6t/25)2^{-(n-7)},&n\ge7.
 \end{cases}
 \qquad \varepsilon(t)=6t/25.\tag{220.21}
$$

This sequence is positive, nonincreasing and vanishes. Both classes
have actual hard-two acquisitions satisfying the closed cap on every
source, with equality at an actual first-zero-seven source.

**证明。** The hull tail equality scales and the other expression
is $12t/25\le1$. Mixing with all-base mass $1-t$ scales each correct
row by $t$, sends base to $1-t+t p(0)$ and pair to $1-t+t p(\{0,n\})$.
Thus all finite cap demands remain satisfied by the same allocation.
The scaled code-only deficit is $4t/25>t/25$; whole-block constants
still miss the positive row by $3t/25$.
On the finite positive word $N$ base is $1-6t/25$ and $O$ base is
$1-t/5$. At each actual $n>6$, the exact marked-law errors are

$$
 \max(6t/25,a_n(t))\quad\text{and}\quad
 \max(t/5,a_n(t)),\tag{220.22}
$$

respectively. Since $a_7(t)=\varepsilon(t)$ and the later terms
halve, both satisfy the cap and both attain it at first zero seven.
The actual-source and same-seed construction below realizes these
finite laws on the unchanged carrier. This proves a family of
attainers, not a sharp universal cost or full amplitude classification.
The algebraic $t=0$ degeneration is not in this positive family.
$\square$

### 220.6 Original sources, actual requests and closed-tail correspondence

**约定 220.24（Unchanged source and full tape carrier）。** Reuse the
source of Boundaries 35.2 and the resource contract of 90.1.
With $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$, it is

$$
 X=\{(r,z):r\text{ prime},\ z\in\mathbb Z,
          \lceil F_r/10\rceil\le z\le\lfloor F_r/5\rfloor\},
 \quad N_x=1+F_rz,\quad q_i(x)=[p_i\mid N_x].
$$

Replies are static. Every source has finite prime support and a finite
first absence. For every finite set of prime addresses, 35.2's entry-rank,
CRT and Fibonacci-window construction gives every prescribed pattern.
Choose a sufficiently large prime $r$ with $F_r$ coprime to the finite
prime product and a window longer than that product. The residue of $z$
is $-F_r^{-1}$ for a desired positive answer and zero for a desired
zero answer. Select an integer in the allowed window in that CRT class.
The resulting source witnesses are fixed before the seed. The finite
positive word represents actual later first zeros; it is not an
infinite all-positive source. No probability measure on $X$ is used.

The tape carrier is the original full Borel disjoint union of interval
copies $B_j,P_j$ of $(0,1)$. The unchanged consumer reports unknown on
$B_j$ and proposes $j$ on $P_j$. The original nonatomic family remains

$$
 \mu_x=(1-h_0)\nu_x+h_0\pi_{\omega(N_x)},\qquad0<h_0<1,
 \quad t(x)=\sum_i3^{-i}q_i(x),
$$

where $\nu_x$ has normalized density proportional to $\exp(t(x)u)$
on $B_{n(x)}$ and $\pi_j$ is uniform on $P_j$.
Distinct original marks $\theta_j=(B_1,1/(j+2))$ define the separately
selected targets

$$
 \lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                        +a_{n(x)}\delta_{\theta_{n(x)}}.
$$

Here $1\ge a_1\ge a_2\ge\cdots>0$ and $a_n\to0$.
A finite marked law has TV one from each original nonatomic target;
these selected targets do not replace $\mu_x$. Competitors retain
arbitrary full-carrier outputs. All score resets and masks act only
on proof weights; they do not change any source bit, tape, target or
acquired transcript.

**约定 220.25（One seed and a hard count of actual requests）。**
One source-independent uniform $U\in[0,1)$ chooses the whole finite
table and schedule before any reply, using fixed intervals of the
normalized weights. $N$ obtains its complete preselected schedule.
$O$ follows its increasing preselected schedule and stops at the first
queried zero or exhaustion. Each output is the indicated original mark,
followed by the unchanged consumer. A common refinement of two interval
partitions permits two laws on the same $U$; it is not another seed.
Every finite rule has measurable finite handoff at every source and seed.
The hard bound is two actual requests, including ignored or repeated
requests. Zero advice, arbitrary addresses, sourcewise almost-sure
finite handoff and uniform all-source/all-Borel TV remain in force.
No runtime, mean count, query depth proxy, source index, prior, restart
or adaptive second-address replacement supplies this contract.

The nine tables of 220.21 are actual $N$ pairs. The four gates are
actual singleton $O$ tables. The thirteen tables of 220.22 are actual
increasing stopped pairs. The padded mass-one laws are therefore
realized directly with the same source-independent seed. The request
deletion in the mask proof compares legal finite tables and never
provides an uncounted probe on a source.

A cone allocation of mass $M$ has affine vector
$(1-M)e_R+\sum\lambda_De_D$, which can be signed when $M>1$.
It cannot then be executed as a probability law. Reuse the radial
filling of VI 196.1: execute weights $\tau\lambda_D$ and anchor
mass $1-\tau M$ only for

$$
 0\le\tau\le1/\max(1,M).
$$

The identity is $r+\tau G\lambda\ge r+\tau h$
with amplitudes $\alpha+\tau(b-\alpha)$ and cap $\tau e$.
Transport to a positive vanishing sequence additionally requires all
its amplitude, order and actual-tail conditions; this affine identity
alone supplies no such sequence. The concrete family 220.23 already
has one padded mass-one law and needs no extra funding.

**约定 220.26（Full-row transport and exact actual tails）。**
The suppliers 109.1, 110.1–110.2 and IX 207.20 are reused at their
stated scopes. The degree-two stopped-kernel criterion 109.1 is for
probability-vector kernels with $c\ge H$ and a common schedule-mass
budget, not arbitrary scores. Exact closed-cap transport 110.2 retains
arbitrary-address and full-carrier competitors in both directions.
Its necessity uses measurable projection, countability to choose one
common conull finite-handoff seed event over sources, vanishing tails
of the maximum address of the same whole preselected schedule, actual
finite witnesses, finite-execution cutoffs and finite-catalog compactness.
Its sufficiency executes one normalized complete allocation satisfying
all independent base, correct, pair and positive rows.

If the actual output law $p_x$ is supported on
$\{\theta_0,\ldots,\theta_H\}$ and the actual first zero is
$n=n(x)>H$, its exact marked-law error is

$$
 \operatorname{TV}(p_x,\lambda_x^a)
                   =\max(1-p_x(0),a_n).\tag{220.23}
$$

The two laws can overlap only at $\theta_0$, so their total common
mass is $\min(p_x(0),1-a_n)$; its complement gives (220.23).
Thus this tail error is at most $\varepsilon$ exactly when
$p_x(0)\ge1-\varepsilon$ and $a_n\le\varepsilon$.
Finite output support alone does not identify the laws at different
actual sources with the same low prefix.

A sufficient additional hypothesis for a common tail law is execution
of one finite probability-vector kernel $P$ on $\{0,1\}^H$: its
source-independent seed selects the whole schedule and table, all
observed coordinates lie in $\{1,\ldots,H\}$, and its output uses
only that seed and the acquired replies. Then
$p_x=P(q_1(x),\ldots,q_H(x))$. Every actual $n(x)>H$ has low word
$1^H$; for the same seed the executed low transcripts and outputs
therefore agree on all these sources. Hence
$p_x=P(1^H)=p_{1^H}$ and (220.23) becomes
$\max(1-p_{1^H}(0),a_n)$ under this additional hypothesis.
Here $1^H$ denotes a finite input word, not an infinite all-positive
source. In particular the laws in 220.23 observe only addresses
$1,\ldots,6$, so this substitution at $H=6$ yields (220.22).
The low-coordinate hypothesis qualifies this substitution only;
the original arbitrary-address/full-carrier competitors retain the
entire scope of 90.1 and 110.2.

The equality case $a_n=\varepsilon$ is retained. The active length
is the strict threshold $L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$.
No chosen address is assumed at most $L_a$. The two horizon orderings
use 207.20: extend a shorter active representation with actual tail
rows when its amplitudes are at most the cap; restrict a longer
representation and project surplus labels when making a shorter
comparison. A restricted kernel is not thereby an original attainer
on removed active tails. Neither score operation extends this supplier.

The earlier-output regression remains literal. At $0100$,
$N(3,4;1,0,0,0)$ outputs the earlier unqueried label one.
Its base/correct/pair event readings are $(0,1,1)$; replacing this
output by zero gives $(1,0,1)$. The original source $(19,436)$ has
$N=1822917$ and realizes that four-bit pattern. Labels are not pruned
to queried or later labels in the full catalog.

**例 220.27（Reused normalized companions and their exact row scopes）。**
The four stopped tables

$$
 O(1,2;1,2,0),\quad O(1,2;1,2,3),\quad
 O(1,3;1,3,0),\quad O(2,3;2,3,0)
$$

with weights $1/4$ form one old law. Its $N$ completions use the same
seed and acquire the whole pair, counting any ignored reply.
At first zero one or two correct mass is at least $3/4$ and pair
mass at least $3/4$. At three base/correct/pair are $(1/4,3/4,1)$;
after three they are $(3/4,0,3/4)$; positive base is $3/4$.
Thus at finite horizon $H\ge3$ it supplies every independent row
for $b_1=b_2=b_3=1$, $b_4=\cdots=b_H=e=1/4$, including negative
base demands. At $H=7$ this is $382$ rows and one mass-one $H_N$
witness. For the exact score in 220.6, $F_Q(b,e)=-31/16$, so it is
not a separator. Extend with $a_4=\cdots=a_8=1/4$ and
$a_n=2^{-(n-8)}/4$ for $n\ge9$. Its actual tail error beyond the
seven-address demonstration horizon is $1/4$, including $a_8=e$.
The active length is three, distinct from that horizon.

At $H=10$ the same law verifies all $3070$ rows. A different reused
extension is $a_1=a_2=a_3=1$ and
$a_n=2^{-(n-4)}/4$ for $n\ge4$. It attains cap $1/4$ with
actual error $\max(1/4,a_n)=1/4$ for every $n\ge4$.
The constant late finite $b$ used for the row check is not this decaying
tail. These laws supply correspondence checks for 220.17 and do not
add amplitude coverage.

For 220.11–220.13 a second reused companion gives mass $1/4$ each
to empty zero, empty zero, $O(1,2;1,2,0)$ and $O(3,4;1,4,0)$.
With $a=(4/5,3/4,1/2,1/4)$ and $a_n=1/(n+1)$ for $n\ge5$,
all sixteen words satisfy the three TV rows at cap $11/20$, with
maximum exactly $11/20$. The strict active length is two while the
rule lawfully uses addresses three and four. Positive base is one,
so every actual $n>4$ has exact error $a_n$. At $0100$ its second
pair outputs earlier unqueried one: $O$ uses one actual request and
its $N$ completion two. Every one of the sixteen patterns is an actual
source by the CRT construction at $r=47$, $F_{47}=2971215073$,
using prime probes $2,3,5,7$; prescribed replies at $11,13$ can be
included in that same finite construction. This is a reused normalized
law, separate from the proof-weight score reconstruction.

For the family 220.6, applying its repaired cost-one score to any
normalized original cap-feasible rule gives the necessary inequality

$$
 (1+g)a_j+g a_k-h a_r+g a_s
            \le1+(3a+13g/2+h)\varepsilon.\tag{220.24}
$$

It is necessary only. No sufficient amplitude classification is implied.
For 220.23 the explicit new finite allocation instead gives the two
actual laws directly. A first-zero-seven source exists before the seed
by the same CRT/window supplier. Explicitly $(r,z)=(47,297421613)$
has $N=883703579581572750$ and replies $1111110$ at primes
$2,3,5,7,11,13,17$. The integer $z$ lies in the prescribed Fibonacci
window. This source is fixed for the whole scaled family before $U$
is chosen. Formula (220.22) proves the attained closed endpoint on
that actual source, not just on a formal terminal word.

### 220.7 Reuse, intersections and excluded increments

The eligible-prefix instance common to 220.4 and 220.8 is counted once.
B's cellwise pooled condition is broader in a different direction:
220.11 has $C>A$ at two words on a prefix zero face and thus fails A's
wordwise eligibility. Conversely A can reset an interior eligible
coordinate six after positive coordinate four, as in 220.6; a prefix
cone extending through that positive coordinate cannot satisfy D1,
which forces every prefix $\beta_i\le0$. The two operations therefore
have separate stated domains, with their shared contraction counted
once. The least-stock specialization with $u=A$, $h=z=0$, $r=C$
and $K_{\rm lo}=K_{\rm hi}=D+G$ is already 219.5–219.6.
It supplies no separate increment.

The terminal-mask specialization of 220.15 is already 218.8–218.9.
The arbitrary interior operation adds the arrival/crossing cuts of
(220.12), whose pair-only counterexample 220.18 prevents a
terminal-tail accounting rule from being used unchanged inside a mask.
The old hull, one-pivot, donor, finite-flow, stock, normalization,
weak-duality and source-transport results are reused without additional
credit. The gate result is conditional on an actual joint block and
fixed remainder; its four-distinct-label block is not the old
suffix-separated global-minimum operation of 218.3.

For explicit reuse, the equal-triple interleaved-debt assembly has
$4\le p<d<r<u\le L$, $J=\{p,r,u\}$ and $g>0$, $s,t\ge0$.
Its coefficients are $P=g/3$ at $w(\{i,j\})$ for
$i=1,2,3$, $j\in J$, and $P=g/3$ at $w(\{i\}\cup J)$,
$C=g$ at each $w(\{j\})$, together with $A=s$ at $w(\{d\})$
and $C=t$ at $w(\{3\})$. The core is the existing equal-triple
core with $P=g/6$ at the triple words plus another $P=g/6$ there.
It has zero cost. Adding the two elementary rows bounds the support
by $4g+s+t$; singleton three outputs three on zero and zero on one
and attains it. Thus $P_{\rm total}=4g$, $K=7g+s+t$, $W=4g+s$,
$\beta_3=t$, $\beta_j=g$ for $j\in J$, $\beta_d=-s$,
and both costs are $t$. This entire family is old supplier assembly,
with zero additional credit, including $(L,J,d,g,s,t)=(7,\{4,6,7\},5,1,1,1)$.
Interleaving alone does not turn its elementary addition into new coverage.

The direct per-pair merge/slack formulas are support identities,
not another structural result. An expression $P_{1^L}>0$ is outside
220.1's domain. It is neither silently relabeled as $T$ nor used to
repair an excluded witness. The consecutive profile already discussed
in 219.10 is also omitted as an increment: its actual terminal is
$2t+u$ and its value seven is a sum of schedule cell maxima, not the
value of every cell. No extra theorem is attached to that profile.

The scoped constructions and proofs here are `repo-derived` ordinary
mathematics. They do not assert worldwide priority or exclusion from
all old convex, signed-residual or polar consequences. Their examples
are full-score improvements or local operation obstructions, not
strict original-source separation witnesses.

The primary mappings in 219.10 retain their stated versions and
hypotheses. Blackwell's risk-set comparison requires one common
randomized decision rule; it does not realize a stopped hard-two
schedule. Chen's binary comparison extends to finite actions only
under binary decomposability of the whole value function. Yang–Yang's
versioned v1 compact-Polish and min-closed-test-cone hypotheses have
not been identified with the present legal-table cone. Zaev's constrained
coupling duality allows an empty feasible set. Gale's finite real-capacity
flow theorem supplies deterministic allocation under its balance and
cut hypotheses, not a query budget. Embrechts–Hofert–Wang's Boolean
compatibility and Angel–Spinka's simultaneous-coupling boundaries
require one joint law; separate compatible margins or pairwise optima
are insufficient. Bertschinger–Rauh's nonstochastic factor illustrates
missing common normalization, not our original separator.
These literature-attested statements are reference frames, not missing
premises for a universal conversion. No inaccessible or metadata-only
citation is used as a theorem premise; no identity between different
PDF/HTML versions is assumed. The complete ordinary proofs above
are the evidence for the four scoped relations.

### 220.8 The unrestricted comparison remains open

The positive obligation remains: for every $L\ge3$ and every actual
full $y\ge0$ with $\Delta_O(y)\le1$, produce one unrestricted full
$V\ge0$ and $\theta\in[0,1]$ satisfying (220.1).
There is no universal eligibility cover, cone-placement theorem,
affordable landing mask or qualifying actual block decomposition here.
Exact-$Q$, baseline, unary, terminal, suffix and constructor preservation
are not restrictions on the original obligation.

A negative alternative still requires the same actual $(b,e)\in H_N$,
the same full feasible $\lambda\ge0$, $G_N\lambda\ge h(b,e)$,
$M=\sum\lambda\ge1$, and an actual unit-$O$ score $y$ with
$F_{Q(y)}(b,e)>M$. It must then supply the original full-carrier,
arbitrary-address, common-seed, hard-two-actual-request, all-source,
all-Borel, actual-tail and closed-cap transport with a uniform lower
certificate against every original stopped competitor. A failed reset,
fixed constructor, local constant replacement, exact-law requirement,
hull-only point or final-total-only tail test does not meet it.

Consequently the original implication for every positive nonincreasing
vanishing amplitude sequence and every positive closed cap,

$$
 \mathcal F_N(a,\varepsilon)\ne\varnothing
 \quad\Longrightarrow\quad
 \mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing,
$$

remains open. The four relations retain all independent event rows,
actual constructions, zero and weak-equality endpoints, and their
stated resource correspondence. They are ordinary mathematical proofs;
no Lean/kernel validation, ingestion, coverage, freeze, physical sampling
cost or universal affordability follows from them or from a finite
rational check.

## 追加锚（本行以下为增补区）

## 221. 同一候选余项上的三候选收集与端点图联合替换

### 221.1 完整事件、候选余项与两条条件关系

本节的两条独立条件关系记为 A 与 B。两者均在同一个预先固定的候选余项上检验，允许重新选择所替换块的完整表及其日程。A 用一个共同的至多三候选收集律；B 用最小正确缺额、端点图及全部逐字容量。B 内的模包络网络构造与零边单点情形分别记为 C 与 D；它们不另构成第三、第四个独立区域。固定余项、端点类及模包络只限制这些充分操作，原始完整停止类仍允许任意合法标签、较早未查询猜测与耗尽猜测。

**定义 221.1（完整有限目录与独立帽行）。** 固定整数 $L\ge3$，令 $B_L=\{0,1\}^L$，$J_L=\{0,\ldots,L\}$，$\Omega_n=\{w:w_1=\cdots=w_{n-1}=1,w_n=0\}$。非全正字的首零为 $n(w)$。记 $E_a$ 为恒输出标签 $a$ 的空表；单日程表 $O(i;a,b)$ 按回答 $0,1$ 输出 $a,b$。对 $i<j$，

$$
N(i,j;a,b,c,d),\qquad O(i,j;a,c,d)
$$

分别按四胞 $00,01,10,11$ 与停止胞 $0,10,11$ 输出所列标签。所有标签均可取 $J_L$ 中任一元素，空表、单表及所有双日程均保留。一个停止表的 $N$ 完成式把首停止胞复制到 $00,01$，取得完整日程的两个回答。信息分区中的重复或反序归一不减免实际请求数。

在 $w\in\Omega_n$ 上，三条独立事件行 $\{0\},\{n\},\{0,n\}$ 的需求为

$$
1-b_n-e,\qquad b_n-e,\qquad1-e;
$$

全正字的 $\{0\}$ 需求为 $1-e$。负单点需求也保留；两条单点下界不能代替并集行。整个有限问题有 $3(2^L-1)+1$ 行。

令 $d(b,e)$ 为此需求向量，$z_D$ 为完整表 $D$ 的事件指示向量，取

$$
R=O(1,2;1,2,0),\quad \alpha=(1,1,0,\ldots,0;0),\quad
r=z_R=d(\alpha),\quad h=d(b,e)-r,\quad
G_C=(z_D-r)_{D\in\mathcal D_C}.
$$

完整非负配置 $\lambda$ 的质量为 $M=\sum_D\lambda_D$，其仿射字向量是

$$
f_w=(1-M)\mathbf e_{R(w)}+\sum_D\lambda_D\mathbf e_{D(w)}.
$$

$G_C\lambda\ge h$ 等价于 $f$ 满足上述每一行。$M>1$ 时 $f$ 可有负坐标，不能直接抽样。

使用原有硬域

$$
\begin{aligned}
H_L=\{(b,e):{}&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\quad b_2=b_3,\\
&(L+1)e\le\sum_{n=3}^L b_n,
\quad b_1+\sum_{n=3}^L b_n-(L+1)e\le1\}.
\end{aligned}
$$

$H_N$ 还要求一个实际完整非负 $N$ 配置满足 $G_N\lambda\ge h$。单独的 $H_L$ 成员身份不是该见证。

**定义 221.2（同一个候选余项）。** 固定一个可行 $\lambda$、质量 $M$，选定非负子配置 $\kappa$，质量 $M-S$，定义

$$
\rho_w=(1-M)\mathbf e_{R(w)}+\kappa_w,
\qquad \kappa_w=\sum_D\kappa_D\mathbf e_{D(w)}.
$$

替换块的质量固定为 $S\ge0$，候选正标签集为 $A\subseteq\{1,\ldots,L\}$。A 与 B 的比较必须保持这同一 $\rho,M,S,A$；不能用不同余项上的成功冒充同余项比较。A 可对任一候选 $\kappa$ 重新优化，但必须另验 $n\notin A$ 的全部正确行。B、C、D 使用一个实际分解 $\lambda=\kappa+\eta$，其中 $\eta$ 的质量是 $S$，输出仅在 $A\cup\{0\}$。这种分解使集外正确行自动由原可行性给出。

当 $\kappa$ 已由完整停止表组成，替换后是 $O$ 配置；任意完整 $N$ 余项一般只能得到 $N$ 手术。另一个可用分支是整个替换后配置属于定义 190.2 的 $W_N$，此时才能调用 194.1 的同质量转换。该分支的单表零胞标签在 $\{0,i\}$，正胞在 $\{0,i+1,\ldots,L\}$；双表 $i<j$ 的 $00,01$ 标签在 $\{0,i\}$，$10$ 在 $\{0,i+1,\ldots,j\}$，$11$ 在 $\{0\}\cup(\{i+1,\ldots,L\}\setminus\{j\})$，空表仍任意标签。A 收集器与 B 端点表均属于 $W_O\subset W_N$。194.1 对整个配置保持质量、逐字不降低基点与并集、各首零类正确下包络及全正基点；它不声称逐字正确支配或原律保持。故其结论恰足以保留这些帽行。没有对任意完整 $N$ 余项的转换推断。

**定义 221.3（完整得分与同实现的条件后果）。** 每个非全正字有独立非负得分 $A_w,C_w,P_w$，全正字有 $T\ge0$，其奖励为

$$
g_y(w,\ell)=A_w[\ell=0]+C_w[\ell=n(w)]+P_w[\ell\in\{0,n(w)\}],
\quad g_y(1^L,\ell)=T[\ell=0].
$$

这里的 $A_w$ 是得分，与候选标签集 $A$ 有别。令

$$
\begin{aligned}
W(y)&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
B_C(y)&=\max_{D\in\mathcal D_C}\sum_w g_y(w,D(w)),\quad
\Delta_C(y)=B_C(y)-W(y),\\
\beta_n&=\sum_{\Omega_n}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T,\quad Q(y)=(\beta,K),\\
F_{Q(y)}(b,e)&=\sum_n\beta_n(b_n-\alpha_n)-Ke.
\end{aligned}
$$

这些是证明权重，不能当作概率预算。若上述同一候选得到质量恰为 $M$ 的可行完整停止配置 $\mu$，则每个完整 $y\ge0$ 在同一 $(b,e)$ 上满足

$$
F_{Q(y)}(b,e)=y\cdot h\le y\cdot G_O\mu
\le M\Delta_O(y).
$$

因此单位停止得分有 $F_{Q(y)}(b,e)\le M\le\max(1,M)$。该条件结论使用原来那个完整 $\lambda$ 与质量，所有行各用一次；一个非最优的大 $M$ 不证明最优截断预算上的比较。

### 221.2 条件关系 A：共同基点与三候选收集

**定义 221.4（收集器及同余项缺额）。** 对非空 $F\subseteq A$，$|F|\le3$，定义 $C_F$：一个候选时直接输出它；两个候选 $a<b$ 时查询 $a$，零时输出 $a$，正时猜 $b$；三个候选 $a<b<c$ 时用 $O(a,b;a,b,c)$。每张表的所有标签与日程在回答前选定。它总输出数值标签，且在每个 $\Omega_a$ 上恰当且仅当 $a\in F$ 时输出 $a$。

对非空 $A$，集外正确行要求 $\rho_w(n)\ge b_n-e$，$w\in\Omega_n,n\notin A$。定义

$$
\begin{aligned}
\ell=\max\bigl(&0,\ 1-e-\rho_{1^L}(0),
\max_{n,w\in\Omega_n}(1-b_n-e-\rho_w(0)),\\
&\max_{n\notin A,w\in\Omega_n}(1-e-\rho_w(0)-\rho_w(n))\bigr),\\
u_a&=\max\{0,b_a-e-\min_{\Omega_a}\rho_w(a)\},\\
v_a&=1-e-\min_{\Omega_a}(\rho_w(0)+\rho_w(a)),\quad
\delta_a(c)=\max\{u_a,v_a-c\}.
\end{aligned}
$$

空指标最大值从 $\ell$ 中省略。并集缺额直接取并集读数的最小值，不能拼接两条单点的独立极小值。

**定理 221.5（A 的恰好共同质量判据）。** 固定上述同一余项及集外正确行。质量 $S$ 的替换由 $cE_0$ 和一个质量 $s=S-c$ 的共同收集器混合组成。存在这样的替换满足每条帽行，当且仅当

$$
c\ge\ell,\quad0\le c\le S,\quad
\delta_a(c)\le S-c\ (a\in A),\quad
\sum_{a\in A}\delta_a(c)\le3(S-c).
$$

令 $U=\max_a u_a$，$C=S-U$，则存在某个 $c$ 的等价有限测试为

$$
\ell\le C,\quad v_a\le S\ (a\in A),\quad
\min_{c\in[\ell,C]}\Phi(c)\le3S,
\qquad \Phi(c)=3c+\sum_a\max(u_a,v_a-c).
$$

只须比较 $\ell,C$ 及区间内的折点 $v_a-u_a$。若 $A=\varnothing$，精确分支是 $c=S$ 且 $\rho+SE_0$ 直接满足全部帽行。

**证明。** 写共同表质量为 $t_F\ge0$、$\sum_Ft_F=s$，令 $g_a=\sum_{F\ni a}t_F$。首零 $a$ 前的候选位均为正，故收集器在 $\Omega_a$ 上输出 $a$ 的质量恒为 $g_a$；基点在所有字上恒为 $c$，集外正确质量为零。因此基点、全正基点及集外并集行等价于 $c\ge\ell$；集内正确、并集分别要求 $g_a\ge u_a$、$g_a\ge v_a-c$。全部帽行恰等价于 $g_a\ge\delta_a(c)$ 及已声明的集外条件。

同一个 $t_F$ 给出 $0\le g_a\le s$ 与 $\sum_ag_a=\sum_F|F|t_F\le3s$，所以这些不等式必要。不能要求 $\sum_ag_a=s$：同一张表在互斥首零类上可同时服务三个标签。

反向，$s=0$ 时缺额全零，仅取 $c=S$。$s>0$ 时，若 $\sum\delta_a\ge s$ 就取 $g=\delta$；若小于 $s$，在每坐标的剩余容量 $s-\delta_a$ 中增加质量，直到 $\sum g_a=s$。$A$ 非空保证总剩余容量至少 $s-\sum\delta_a$。于是

$$
g\ge\delta,\quad0\le g_a\le s,\quad s\le\sum g_a\le3s.
$$

使用已有截断立方体几何：$\{x\in[0,1]^A:1\le\sum x_a\le3\}$ 的顶点均为非空至多三元集合的指示向量。其直接证明是，两个分数坐标可作反向微扰；只有一个分数坐标而和约束不活跃时可单独微扰，活跃时该坐标由整数和与其余整数坐标决定，也必为整数。故不存在分数顶点。有限有界多面体由其顶点凸生成。对 $x=g/s$ 取一个有限凸表示 $x=\sum_F\pi_F\mathbf1_F$，令 $t_F=s\pi_F$，加 $cE_0$。这给一个真正的非负质量 $S$ 完整停止块，所有行由同一混合满足。

最后，$\delta_a(c)\le S-c$ 等价于 $u_a+c\le S$ 且 $v_a\le S$。全部坐标给 $c\le S-U$；求和约束恰为 $\Phi(c)\le3S$。$\Phi$ 在折点间仿射，在闭区间上必于端点或折点取得最小值；平段、折点重合、零缺额与闭等号均包含。上述论证仅对替换块使用非负质量，故有符号 $\rho$ 也无例外。$\square$

**例 221.6（A 成功而同余项 B 失败的全部有限行）。** 取 $L=6$，

$$
b=(103/200,103/200,103/200,423/1000,189/500,329/1000),\quad e=47/200,
\quad M=1,\quad S=1/25,\quad A=\{1,2,3,4\}.
$$

余项 $\rho=\kappa$ 的全部 25 张停止表如下；最后一列为质量乘 $1000$。原块是 $\eta=(1/25)N(5,6;1,2,3,4)$。

| 日程 | 停止输出 | $1000\kappa_D$ |
| --- | --- | ---: |
| $6$ | $0,1$ | 30 |
| $1,2$ | $0,0,3$ | 33 |
| $1,2$ | $0,2,4$ | 42 |
| $1,2$ | $0,2,5$ | 4 |
| $1,2$ | $1,2,0$ | 155 |
| $1,3$ | $0,3,0$ | 6 |
| $1,3$ | $1,3,0$ | 95 |
| $1,4$ | $0,4,0$ | 30 |
| $1,5$ | $0,3,0$ | 19 |
| $1,6$ | $0,2,3$ | 30 |
| $2,3$ | $0,1,0$ | 10 |
| $2,3$ | $0,3,0$ | 112 |
| $2,3$ | $2,3,0$ | 4 |
| $2,4$ | $2,4,0$ | 45 |
| $2,5$ | $0,3,0$ | 11 |
| $2,5$ | $0,5,0$ | 23 |
| $3,4$ | $0,0,5$ | 26 |
| $3,4$ | $0,4,0$ | 71 |
| $3,5$ | $0,5,0$ | 45 |
| $3,6$ | $0,6,0$ | 30 |
| $4,5$ | $0,5,0$ | 45 |
| $4,6$ | $0,6,0$ | 30 |
| $5,6$ | $0,1,0$ | 30 |
| $5,6$ | $0,6,0$ | 4 |
| $5,6$ | $0,6,2$ | 30 |

质量和为 $24/25$。在同一余项上，

$$
\ell=0,\quad u=v=(3/100,3/100,3/100,0),\quad c=1/100,\quad s=3/100.
$$

故 $\sum\delta=9/100=3s$，$\Phi(c)=3/25=3S$，取

$$
q=(1/100)E_0+(3/100)O(1,2;1,2,3).
$$

以下每个三元组是整个 $\Omega_n$ 上基点、正确、独立并集的各自最小值。它们可由所列同一完整配置对剩余布尔位逐一消元得出；不同最小值的达到字不要求相同。

| $n$ | 需求 | 原 $N$ 最小值 | 新 $O$ 最小值 |
| ---: | --- | --- | --- |
| 1 | $(1/4,7/25,153/200)$ | $(19/40,7/25,153/200)$ | $(97/200,7/25,31/40)$ |
| 2 | $(1/4,7/25,153/200)$ | $(97/200,7/25,153/200)$ | $(99/200,7/25,31/40)$ |
| 3 | $(1/4,7/25,153/200)$ | $(233/500,7/25,769/1000)$ | $(119/250,7/25,31/40)$ |
| 4 | $(171/500,47/250,153/200)$ | $(577/1000,47/250,153/200)$ | $(587/1000,47/250,31/40)$ |
| 5 | $(387/1000,143/1000,153/200)$ | $(311/500,143/1000,153/200)$ | $(79/125,143/1000,31/40)$ |
| 6 | $(109/250,47/500,153/200)$ | $(701/1000,47/500,159/200)$ | $(711/1000,47/500,161/200)$ |

全正基点分别为 $153/200,31/40$，需求 $153/200$。每张表在一个字只访问一胞，因此所列表质量的有限和直接定义全部 64 字的概率；固定首零前缀后，对每个剩余位使用 $\min_{x\in\{0,1\}}f=\min(f|_{x=0},f|_{x=1})$，得到表中精确界。比较需求验证两律各全部 190 行。另有 $\sum_{n=3}^6b_n=329/200=7e$，上侧式等于 $103/200\le1$，其余次序条件成立；原完整质量一 $\lambda=\kappa+\eta$ 因而实际证明 $H_N$ 成员身份。

在这完全相同的 $\rho,S,A$ 上，B 的端点块只能使正确度和至多 $2S=2/25$，而必需三条度的和为 $9/100>2/25$，所以 B 失败。仅单点门需要 $9/100>S$；原代码块的四个整零面最小值全为零。三候选收集利用互斥首零类共享一张表的质量，并只发出两次实际请求。

原律的 109.1 常数向量为 $(661/1000,29/100,49/1000,0,0,0,0)$，其核阈值为 $(301/500,27/100,59/1000,0,0,0,0)$。标签 2 的常数比阈值少 $1/100$，所以原律本身不是停止核；上面的另一停止律满足同一帽。这只是精确律边界。

### 221.3 条件关系 B：最小正确度与端点图全部容量

**定义 221.7（端点类）。** 取实际分解 $\lambda=\kappa+\eta$，块质量记为 $s=S$，令

$$
\delta_i=\max\{0,b_i-e-\min_{\Omega_i}\rho_w(i)\}\ (i\in A),\qquad
\delta_i=0\ (i\notin A).
$$

端点替换块由空表 $E_0$、单点门 $O(i;i,0)$，以及双表 $O(i,j;a,b,0)$ 组成，其中 $i<j$，$a\in\{0,i\}$、$b\in\{0,j\}$，正输出只在 $A$。耗尽输出必须为零是本构造的限制；它不是原始 $O$ 类的限制。

取有向边 $x_{ij}\ge0$，$i<j$，若 $j\notin A$ 则边为零。定义

$$
\begin{aligned}
I_i&=\sum_{h<i}x_{hi},\quad r_i=\delta_i-I_i,\quad O_i=\sum_{j>i}x_{ij},\\
m(x)&=\sum_i\max(r_i,O_i)=\sum_i\delta_i-\sum_i\min(r_i,O_i),\\
Z(w)&=\{i:w_i=0\},\quad
\Psi_x(Z)=\sum_{i\in Z}\delta_i-\sum_{i<j,\ i,j\in Z}x_{ij}.
\end{aligned}
$$

此处 $r_i$ 是图剩余度，与锚事件向量 $r$ 有别。在 $w\in\Omega_n$ 设

$$
c_w=\min\{\rho_w(0)+s-1+b_n+e,
\ \rho_w(0)+\rho_w(n)+s-1+e+\delta_n\}.
$$

**定理 221.8（B 的精确联合判据及完整表构造）。** 在同一固定余项上，存在质量恰为 $s$ 的端点替换满足全部帽行，当且仅当一个共同的 $x$ 满足

$$
I_i\le\delta_i\ (1\le i\le L),\quad m(x)\le s,\quad
\Psi_x(Z(w))\le c_w\quad(w\ne1^L),
$$

同时满足集外正确行及 $\rho_{1^L}(0)+s\ge1-e$。实际分解已使后两条件成立，但它们仍是字面约束。所得块的字向量为

$$
q_w(a)=[a\in Z(w)]\left(\delta_a-\sum_{i<a,\ i\in Z(w)}x_{ia}\right),
\qquad q_w(0)=s-\Psi_x(Z(w)).
$$

在每个 $\Omega_a$ 上 $q_w(a)=\delta_a$。全部行由同一个 $x$ 和同一完整配置满足；给定图的最小非空日程质量为 $m(x)$。

**证明。** 先证明可以把任何端点可行块的正确度减到 $\delta$。令 $u_i$ 为单点正输出质量，$p_{ij}$ 为双表首零胞输出 $i$ 的质量，$x_{ij}$ 为次零胞输出 $j$ 的质量，$t_{ij}$ 为双日程共同质量。正确度在整个 $\Omega_i$ 恒为

$$
d_i=u_i+\sum_{j>i}p_{ij}+\sum_{h<i}x_{hi}\ge\delta_i,
\qquad t_{ij}\ge\max(p_{ij},x_{ij}).
$$

$d_i>0$ 时，在每个发出 $i$ 的胞中以固定比例 $1-\delta_i/d_i$ 把该输出改成零。它可通过回答前分割完整表质量实现，所有胞的分割用一个有限共同细分。移走正确 $i$ 保持 $\{0,i\}$，移走错误 $i$ 改善其首零并集，所有基点改善，而正确需求仍满足。$d_i=0$ 时 $\delta_i=0$，无需操作。故端点可行性等价于存在正确度恰为 $\delta$ 的块，质量与日程合法性保持。

对精确度块，$I_i\le\delta_i$ 且 $r_i=u_i+\sum_{j>i}p_{ij}$。在字 $w$ 上，标签 $a$ 的首胞与单点贡献在 $w_a=0$ 时可用，次胞 $x_{ia}$ 还要求 $w_i=1$。这给所述 $q_w(a)$；求和给正质量 $\Psi_x(Z)$ 与基点 $s-\Psi_x(Z)$。首零 $a$ 前所有位为正，所以其正确度恰为 $\delta_a$。

非空质量至少为

$$
\begin{aligned}
\sum_i u_i+\sum_{i<j}\max(p_{ij},x_{ij})
&=\sum_i\delta_i-\sum_{i<j}\min(p_{ij},x_{ij})\\
&\ge\sum_i\delta_i-\sum_i\min(r_i,O_i)=m(x).
\end{aligned}
$$

这里一张双表的两个正胞共用 $t_{ij}$，没有把两胞质量相加当成共同预算。代入两条原始基点、并集需求，恰得 $\Psi_x\le c_w$。全正字的所有端点表输出零，集外没有正度，这给其余必要条件。

反向，若 $O_i>0$，取

$$
p_{ij}=\frac{\min(r_i,O_i)}{O_i}x_{ij},\qquad u_i=(r_i-O_i)_+;
$$

若 $O_i=0$，取所有 $p_{ij}=0,u_i=r_i$。这样 $0\le p_{ij}\le x_{ij}$，$u_i+\sum_jp_{ij}=r_i$。加入质量 $p_{ij}$ 的 $O(i,j;i,j,0)$、质量 $x_{ij}-p_{ij}$ 的 $O(i,j;0,j,0)$、质量 $u_i$ 的 $O(i;i,0)$。非空总质量为

$$
\sum_iO_i+\sum_i(r_i-O_i)_+=\sum_i\max(r_i,O_i)=m(x).
$$

加质量 $s-m(x)$ 的 $E_0$。所有质量非负；$i\notin A$ 时 $r_i=0$，只可作零输出守卫。所得有限表配置有给定字公式，集内正确需求由最小缺额满足，集外正确由原分解满足，两条独立其他事件由 $c_w$ 满足，全正行也满足。添加同一 $\rho$ 即完成充分性。

$m(x)$ 的标量等式与已有 109.1 一致：归一块时 $c(a)=H(a)=r_a/s$，$c(0)=1-\sum r_i/s$，$H(0)=\sum(O_i-r_i)_+/s$，所以 $c\ge H$ 恰为 $s\ge m(x)$。该质量恒等式不另计内容。新条件关系是最小度薄化、同余项全部容量与完整块重建的结合。$s=0$、零分母、零度与闭等号均由所述分支包含。$\square$

**注记 221.9（一个有限凸系统）。** 固定余项后 $\delta$ 固定。引入 $t_i\ge\delta_i-I_i$、$t_i\ge O_i$、$\sum_it_i\le s$，其余 $I_i\le\delta_i$ 与每字 $\Psi_x\le c_w$ 全部线性。这是同一图的一次有限可行性问题，不是分别优化每行或每个日程。没有声称全部字的分离可在多项式时间完成。

**例 221.10（B 成功而同余项 A 失败）。** 取

$$
L=6,\quad b=(12/25,12/25,12/25,21/50,21/50,9/25),\quad e=6/25,
\quad M=s=1,\quad\rho=\kappa=0,\quad A=\{1,\ldots,6\}.
$$

原完整 $N$ 见证由以下全部 23 张表组成，质量列精确列出。$O$ 表可取其同日程 $N$ 完成式。

| 完整表 | 质量 |
| --- | ---: |
| $O(1,2;0,2,3)$ | $2/25$ |
| $O(1,2;1,2,3)$ | $1/50$ |
| $O(1,2;1,2,4)$ | $3/50$ |
| $O(1,3;1,3,0)$ | $3/50$ |
| $O(1,4;1,4,0)$ | $1/50$ |
| $O(2,3;0,3,0)$ | $1/50$ |
| $O(2,3;0,3,4)$ | $1/50$ |
| $O(2,4;0,4,0)$ | $1/25$ |
| $O(3,5;0,5,0)$ | $1/10$ |
| $O(4,5;0,5,0)$ | $3/50$ |
| $O(4,5;0,5,6)$ | $1/50$ |
| $O(4,6;0,6,0)$ | $1/50$ |
| $O(5,6;0,6,0)$ | $2/25$ |
| $N(5,6;1,2,3,4)$ | $1/25$ |
| $N(1,5;0,1,0,0)$ | $1/25$ |
| $N(1,6;0,1,0,0)$ | $1/25$ |
| $N(2,5;0,2,0,0)$ | $1/25$ |
| $N(2,6;2,0,0,0)$ | $1/25$ |
| $N(3,5;3,0,0,0)$ | $1/25$ |
| $N(3,6;0,3,0,0)$ | $1/25$ |
| $N(4,5;4,0,0,0)$ | $1/25$ |
| $N(4,6;4,0,0,0)$ | $1/25$ |
| $O(1,2;1,2,0)$ | $1/25$ |

其 $\delta=(6/25,6/25,6/25,9/50,9/50,3/25)$，和为 $6/5$。同余项 A 的基点要求 $c\ge1-e=19/25$，所以数值容量 $3(1-c)\le18/25<6/5$，A 失败。B 取以下全部非零边；未列边为零。

| $i,j$ | $x_{ij}$ |
| --- | ---: |
| $(1,2)$ | $3/25$ |
| $(1,3)$ | $3/25$ |
| $(1,4)$ | $3/50$ |
| $(1,5)$ | $3/50$ |
| $(2,3)$ | $3/25$ |
| $(2,4)$ | $3/50$ |
| $(2,5)$ | $3/50$ |
| $(3,4)$ | $3/50$ |
| $(3,5)$ | $3/50$ |
| $(4,6)$ | $3/50$ |
| $(5,6)$ | $3/50$ |

入度为 $(0,3/25,6/25,9/50,9/50,3/25)$，出度为 $(9/25,6/25,3/25,3/50,3/50,0)$，节约 $\sum\min(r_i,O_i)=9/25$，故非空质量 $m=21/25$。定理的构造给完整停止配置：

| 停止表 | 质量 |
| --- | ---: |
| $O(1,2;1,2,0)$ | $2/25$ |
| $O(1,2;0,2,0)$ | $1/25$ |
| $O(1,3;1,3,0)$ | $2/25$ |
| $O(1,3;0,3,0)$ | $1/25$ |
| $O(1,4;1,4,0)$ | $1/25$ |
| $O(1,4;0,4,0)$ | $1/50$ |
| $O(1,5;1,5,0)$ | $1/25$ |
| $O(1,5;0,5,0)$ | $1/50$ |
| $O(2,3;2,3,0)$ | $3/50$ |
| $O(2,3;0,3,0)$ | $3/50$ |
| $O(2,4;2,4,0)$ | $3/100$ |
| $O(2,4;0,4,0)$ | $3/100$ |
| $O(2,5;2,5,0)$ | $3/100$ |
| $O(2,5;0,5,0)$ | $3/100$ |
| $O(3,4;0,4,0)$ | $3/50$ |
| $O(3,5;0,5,0)$ | $3/50$ |
| $O(4,6;0,6,0)$ | $3/50$ |
| $O(5,6;0,6,0)$ | $3/50$ |
| $E_{0}$ | $4/25$ |

为给全部字一个符号证明，令 $h_0=3/50$，$a=|Z\cap\{1,2,3\}|$，$c=|Z\cap\{4,5\}|$，$d=[6\in Z]$。直接代边得

$$
\Psi_x(Z)/h_0=a(5-a)+(3-a)c+(2-c)d.
$$

首零为 1、2、3 时 $a\ge1$；$a=1,2,3$ 的最大值各为 8。首零为 4 时 $a=0,c\ge1$，最大 6；为 5 时 $a=0,c=1$，最大 4；为 6 时 $a=c=0,d=1$，值 2。这给精确最大值 $(8,8,8,6,4,2)h_0\le b_n$。因为 $\delta_n=b_n-e$，基点 $1-\Psi_x\ge1-b_n\ge1-b_n-e$，并集 $1-\Psi_x+\delta_n\ge1-e$，正确度恰为 $\delta_n$；全正基点为一。这同时证明全部 190 行。

| $n$ | 原 $N$ 的三行最小值 | 图 $O$ 的三行最小值 |
| ---: | --- | --- |
| 1 | $(13/25,6/25,19/25)$ | $(13/25,6/25,19/25)$ |
| 2 | $(12/25,6/25,19/25)$ | $(13/25,6/25,19/25)$ |
| 3 | $(13/25,6/25,19/25)$ | $(13/25,6/25,19/25)$ |
| 4 | $(27/50,9/50,19/25)$ | $(16/25,9/50,41/50)$ |
| 5 | $(29/50,9/50,19/25)$ | $(19/25,9/50,47/50)$ |
| 6 | $(33/50,3/25,39/50)$ | $(22/25,3/25,1)$ |

原、新全正基点分别为 $19/25,1$。次序成立，$\sum_{n=3}^6b_n=42/25=7e$，另一硬域式为 $12/25\le1$，原同一完整配置证明 $H_N$。

原律在 $111100,111101,111111$ 的标签 2 概率分别为 $0,1/25,0$。每个停止表若查询 5，则前两字在该零位停止后不能区分；若不查询 5，后两字除该位外相同，不能区分。因此每张完整停止表及其非负混合均满足

$$
p_{111101}(2)\le p_{111100}(2)+p_{111111}(2).
$$

原律违反它，而上述另一停止律满足同一帽。这是原律不可保持的证明，不能当作原始帽分离。

**例 221.11（端点类是真子类，耗尽猜测保持合法）。** 在同余项 $\rho=0,s=1$ 上取

$$
b=(1,1,1,1/4,1/4,1/4),\quad e=1/4.
$$

四张表 $O(1,2;1,2,0)$、$O(1,2;1,2,3)$、$O(1,3;1,3,0)$、$O(2,3;2,3,0)$ 各质量 $1/4$。首零 1、2 的正确及并集至少 $3/4$；首零 3 的基点、正确、并集是 $(1/4,3/4,1)$；首零 4、5、6 是 $(3/4,0,3/4)$；全正基点 $3/4$。前两类负基点需求 $-1/4$ 保留。因此全部 190 行成立，硬域尾和 $7/4=7e$，上式等于一。

端点类的每张非空表最多贡献两个正确度，所以 $\sum\delta_i\le2s$ 必要。但前三条缺额和为 $9/4>2$，故 B 在此候选失败。合法耗尽猜测标签 3 承担了第三个候选。这个已知四表见证及其边界不提供原始分离或新的幅度分类。

### 221.4 B 内的 C：整零面模包络与两族网络割

**定义 221.12（同块的非负模下包络）。** 保持 221.7 的实际 $\lambda=\kappa+\eta$、同一 $\rho,s,\delta$。对每个正标签 $a$，在其整个零面要求

$$
\eta_w(a)\ge u_a+\sum_{i<a}c_{ia}w_i\qquad(w_a=0),
\quad u_a\ge0,\quad c_{ia}\ge0.
$$

所有包络是同一个实际块的逐字界。全零字同时给出 $U=\sum_au_a\le s$。令

$$
R_0=s-U,\qquad d_a=(\delta_a-u_a)_+,
\qquad C_i(J)=\sum_{a\in J,\ a>i}c_{ia},\quad d(J)=\sum_{a\in J}d_a.
$$

**定理 221.13（C 的完整模包络网络构造）。** 存在下述共同资金路由，当且仅当对每一个 $J\subseteq\{1,\ldots,L\}$，两族割均成立：

$$
\boxed{d(J)\le\sum_iC_i(J)},\qquad
\boxed{d(J)\le R_0+\sum_i\min(u_i,C_i(J))}.
$$

路由由已资助边 $p_{ia}\ge0$ 与中性边 $n_{ia}\ge0$ 组成，满足

$$
p_{ia}+n_{ia}\le c_{ia},\quad
\sum_{a>i}p_{ia}\le u_i,\quad
\sum_{i<a}(p_{ia}+n_{ia})=d_a,\quad
\sum_{i<a}n_{ia}\le R_0.
$$

最后一个求和遍历全部边。由它构造质量恰为 $s$ 的停止块：

| 表 | 质量 |
| --- | --- |
| $O(i;i,0)$ | $u_i-\sum_{a>i}p_{ia}$ |
| $O(i,a;i,a,0)$ | $p_{ia}$ |
| $O(i,a;0,a,0)$ | $n_{ia}$ |
| $E_0$ | $R_0-\sum_{i<a}n_{ia}$ |

所有基点、首零并集及全正基点相对 $\eta$ 逐字不下降，正确行满足同余项需求。该块是 B 的端点类；按 221.8 薄化到 $\delta$ 后，它给 B 的同余项图见证，C 不另计独立关系。

**证明。** 构造有限有向网络。源 $S_0$ 向供体 $i$ 的边容量为 $u_i$，向中性节点 $N_0$ 的边容量为 $R_0$；$N_0$ 向各供体有大但有限容量 $K_0$；供体 $i$ 向接收者 $a>i$ 的容量为 $c_{ia}$；接收者 $a$ 向汇 $T_0$ 的容量为 $d_a$。取

$$
D=\sum_ad_a,\qquad K_0=1+D+U+R_0+\sum_{i<a}c_{ia}>D.
$$

证明实容量最大流割结论时，不假定增广算法在有限步终止，也不使用整性。所有边流在有限闭区间，守恒与容量是闭条件，零流可行，故可行流集合是非空紧多面体；连续的流值有最大值。若最大流的剩余网络中源可达汇，取一条简单剩余路径，各正剩余容量的有限最小值严格正，沿它调整可严格增加流值，矛盾。因此汇不可达。令 $V$ 为剩余网络中源可达顶点集；从 $V$ 向外的原边饱和，从外向 $V$ 的原边零流，否则相应剩余边可达。把守恒式在 $V$ 上求和，最大流值恰等于该割容量。任何流值不超过任何割容量由同样的求和式成立。于是所有割容量至少 $D$ 当且仅当存在值 $D$ 的流。

现逐一计算割。任何割若切到 $K_0$ 边，其容量大于 $D$，不成阻碍。其余割令 $J$ 为汇侧接收者集合；源侧接收者的汇边贡献 $D-d(J)$。若中性节点在源侧，所有供体也在源侧，否则切到 $K_0$ 边，故容量是

$$
D-d(J)+\sum_iC_i(J).
$$

若中性节点在汇侧，先支付 $R_0$，每个供体可独立在源侧付 $C_i(J)$ 或在汇侧付 $u_i$，最小容量是

$$
D-d(J)+R_0+\sum_i\min(u_i,C_i(J)).
$$

这两种恰穷尽不含大边的割，给所述两族，不可只保留总需求割。$J=\varnothing$、$D=0$、零容量与等号均包含。

网络本身无环，值 $D$ 的流可作有限路径分解：在有正流的源汇路径上取最小边流，减去它，每次至少消掉一条正流边；剩余守恒且不可能有无环循环流。经直接源供体路径的质量记为 $p_{ia}$，经中性节点的记为 $n_{ia}$。全部接收者汇边饱和，遂得到所列共同路由不等式。反过来这些路径质量直接给值 $D$ 的合法流，所以路由判据是 iff。

由表中质量构造块。非空与空总和为

$$
\sum_i\left(u_i-\sum_ap_{ia}\right)+\sum_{i<a}(p_{ia}+n_{ia})
+R_0-\sum_{i<a}n_{ia}=U+R_0=s.
$$

正标签 $a$ 的整个字函数是

$$
q_w(a)=(1-w_a)\left(u_a+\sum_{i<a}(p_{ia}+n_{ia})w_i\right).
$$

在零面它不超过所给 $\eta$ 包络，在正面是零而 $\eta\ge0$，故所有正坐标 $q_w(a)\le\eta_w(a)$。相同质量给

$$
q_w(0)-\eta_w(0)=\sum_a(\eta_w(a)-q_w(a))\ge0,
$$

而独立并集有

$$
q_w(0)+q_w(n)-\eta_w(0)-\eta_w(n)
=\sum_{a\ne n}(\eta_w(a)-q_w(a))\ge0.
$$

首零 $a$ 前全部位正，所以 $q_w(a)=u_a+d_a\ge\delta_a$，加同一余项后正确需求成立。集外正确与全正行也保留。这分别证明每种事件，不拼接独立最小值。全部表属于端点类，用 221.8 的统一薄化降低多余正确度仍可行，得到一个 B 图。任意 $N$ 余项的结论仍只是 $N$ 手术；实际 $O$ 余项或整个 $W_N$ 分支才给 $O$。$\square$

两族割在资金与边容量上承担不同义务。例如只有一条容量 $1$ 的边、$u_1=1,d_2=2,R_0=2$ 时第二族成立而第一族失败；容量 $2,u_1=0,d_2=1,R_0=0$ 时第一族成立而第二族失败。这些小网络说明不能删除其中一族，均不声称实际帽分离。

**例 221.14（C 的七位实际块、全部 382 行及 128 个割子集）。** 取

$$
L=7,\quad h=1/100=5/500,\quad
b=(240,240,240,211,194,194,153)/500,\quad e=124/500.
$$

令 $\sigma_2=00,\sigma_3=01,\sigma_4=10,\sigma_5=11$。$\eta$ 由九张质量均为 $h$ 的完整表组成：一张 $N(6,7;2,3,4,5)$；对每个 $a=2,3,4,5$ 和 $k=6,7$，若相应代码位为零用 $O(1,k;1,0,a)$，若为一用 $O(1,k;1,a,0)$。即八张停止供体加一张允许较早未查询标签的完整代码表。

余项 $\rho=\kappa$ 的全部 17 张表为：

| 停止表 | 质量 |
| --- | ---: |
| $O(1;1,0)$ | $1/250$ |
| $O(1,2;1,2,0)$ | $24/125$ |
| $O(1,3;1,3,0)$ | $13/125$ |
| $O(1,4;1,4,0)$ | $23/500$ |
| $O(2,3;0,3,0)$ | $59/500$ |
| $O(2,4;2,4,0)$ | $3/100$ |
| $O(2,4;0,4,0)$ | $3/100$ |
| $O(2,5;0,5,0)$ | $7/500$ |
| $O(2,6;0,6,0)$ | $1/500$ |
| $O(3,4;0,4,0)$ | $29/500$ |
| $O(3,5;0,5,0)$ | $29/500$ |
| $O(3,6;0,6,0)$ | $23/500$ |
| $O(4,5;0,5,0)$ | $29/500$ |
| $O(4,6;0,6,0)$ | $23/500$ |
| $O(5,6;0,6,0)$ | $23/500$ |
| $O(5,7;0,7,0)$ | $3/250$ |
| $O(6,7;0,7,0)$ | $23/500$ |

$\kappa$ 质量 $455/500$，$\eta$ 质量 $45/500$，故原完整 $\lambda$ 质量一。令 $x_i=w_i,p=(x_6,x_7)$，直接逐胞相加得在每一个字上

$$
\eta_w(1)=8h(1-x_1),\quad
\eta_w(a)=h([p=\sigma_a]+x_1d_H(p,\sigma_a))\ (2\le a\le5),\quad
\eta_w(0)=4hx_1.
$$

$x_1=1$ 时括号值随汉明距离 $0,1,2$ 分别为 $1,1,2$；$x_1=0$ 可令某候选代码不匹配使该候选整零面最小值为零。取包络 $u_1=8h,c_{1a}=h$（$2\le a\le5$），其余 $u,c$ 零，$R_0=h$。同余项缺额是 $\delta_2=\cdots=\delta_5=h$，其余零。因此对任意 128 个子集 $J$，令 $k=|J\cap\{2,3,4,5\}|$，有

$$
d(J)=kh=\sum_iC_i(J),\qquad
R_0+\sum_i\min(u_i,C_i(J))=h+kh.
$$

两族对每一子集都成立。可取四条已资助边 $p_{1a}=h$，中性边全零。替换为四张质量 $h$ 的 $O(1,a;1,a,0)$、质量 $4h$ 的 $O(1;1,0)$ 和质量 $h$ 的 $E_0$。其正度 1 为 $8h$，可在 B 内薄化到 $\delta_1=0$：把上述所有首胞标签 1 改为零，变成四张 $hO(1,a;0,a,0)$ 与 $5hE_0$。这也是同余项、同质量可行 B 块，证明 C 确实位于 B 内。

为完整复核有限行，记 $k_a=500\kappa_w(a)$。所有正坐标多项式为

$$
\begin{aligned}
k_1&=173(1-x_1),& k_2&=(1-x_2)(15+96x_1),\\
k_3&=(1-x_3)(52x_1+59x_2),&
k_4&=(1-x_4)(23x_1+30x_2+29x_3),\\
k_5&=(1-x_5)(7x_2+29x_3+29x_4),&
k_6&=(1-x_6)(x_2+23x_3+23x_4+23x_5),\\
k_7&=(1-x_7)(6x_5+23x_6),& k_0&=455-\sum_{a=1}^7k_a.
\end{aligned}
$$

原基点分子为 $455+20x_1-\sum k_a$。新块坐标为

$$
500q_1=40(1-x_1),\quad500q_a=5x_1(1-x_a)\ (2\le a\le5),\quad
500q_0=5+20x_1+5x_1\sum_{a=2}^5x_a.
$$

基点增量分子 $5+5x_1\sum_{a=2}^5x_a\ge0$。固定每个首零前缀，对 $P=\sum k_a$ 从位 7 向后作有限布尔最大值比较，得精确最大值 $(292,215,194,142,112,76,29)$；$\kappa$ 的首零正确分子为 $(173,111,111,82,65,70,29)$。加代码及供体可逐项得到下面的独立行极小值，所有单位为 $1/500$。

| $n$ | 需求基点 | 需求正确 | 需求并集 | 原 $N$ 三行最小值 | 新 $O$ 三行最小值 |
| ---: | ---: | ---: | ---: | --- | --- |
| 1 | 136 | 116 | 376 | $(163,213,376)$ | $(168,213,381)$ |
| 2 | 136 | 116 | 376 | $(260,116,376)$ | $(270,116,386)$ |
| 3 | 136 | 116 | 376 | $(281,116,397)$ | $(291,116,407)$ |
| 4 | 165 | 87 | 376 | $(333,87,420)$ | $(348,87,435)$ |
| 5 | 182 | 70 | 376 | $(363,70,433)$ | $(383,70,453)$ |
| 6 | 182 | 70 | 376 | $(399,70,469)$ | $(424,70,494)$ |
| 7 | 223 | 29 | 376 | $(446,29,475)$ | $(471,29,500)$ |

全正基点分子分别为 $475,500$，需求 $376$。剩余位的精确 min/max 递推及上面全部表定义给各 382 行的有限代数证明；并集直接对基点与该字正确之和取最小值，绝不用独立最小值的和冒充它。$\sum_{a=3}^7b_a=992/500=8e$，上侧式 $240/500\le1$，次序与 $b_2=b_3$ 成立，原同一配置证明 $H_N$。

整零面单点门判据在标签 2 至 5 上失败，却不妨碍共同包络路由。若把八个供体留在余项而只替换代码质量 $h$，在首零分别为 2、3、4、5 且后缀为其匹配代码的四个字上，各供体对应正确质量零，替换各须付 $h$。一张硬两请求停止表至多有三个输出标签，故这四个正确读数之和最多为该表质量的三倍，任何此种停止替换至少需 $4h/3>h$。这是固定代码操作的失败；共同重排九表块则成功。

原核的标签 2 常数 $1/25$ 小于 109.1 阈值 $1/20$，标签 3 常数零小于阈值 $1/100$。原精确律不能停止表示；另一停止律满足同一帽。该核诊断不增加独立精确律障碍或幅度分类。

**例 221.15（模包络不是一般停止可行性的必要条件）。** 在 $L=3$ 取 $b_1=b_2=b_3=1,e=1/4$，221.11 的四表各 $1/4$，全部 22 行可行。固定分解令 $\eta=(1/4)O(1,2;1,2,3)$，$\kappa$ 为另三张表。则 $\delta_3=1/4$，$\eta_w(3)=w_1w_2/4$。在整个 $w_3=0$ 面上，非负模包络 $u_3+c_{13}w_1+c_{23}w_2$ 分别测试 $00,10,01$ 强制三个系数全零。故 $J=\{3\}$ 的第一族割为 $1/4\le0$，失败。但原律本来已是完整停止律；该失败不能否定它或另一分解。

### 221.5 B 内的 D：零边单点 iff 与帽内付费下降

**定理 221.16（D 的完整零边判据）。** 在 221.7 的同一实际分解上，令所有 $x_{ij}=0$。存在质量 $s$ 的单点门与空零替换满足全部帽行，当且仅当集外正确需求、全正行 $\rho_{1^L}(0)+s\ge1-e$ 以及下列全部约束成立：

$$
\begin{aligned}
\text{C0}:&\quad\sum_{a\in A}\delta_a\le s,\\
\text{CB}:&\quad\sum_{a\in A\cap Z(w)}\delta_a
\le s+\rho_w(0)-(1-b_n-e)&& (w\in\Omega_n),\\
\text{CP}:&\quad\sum_{a\in A\cap Z(w)\setminus\{n\}}\delta_a
\le s+\rho_w(0)+\rho_w(n)-(1-e)&& (w\in\Omega_n).
\end{aligned}
$$

替换恰为 $\sum_a\delta_aO(a;a,0)+(s-\sum_a\delta_a)E_0$。这是 B 的 $x=0$，不另计独立关系。它不要求旧块正坐标被逐字支配。

**证明。** 任一此类块的门质量 $t_a$ 在每个 $\Omega_a$ 贡献正确 $t_a$，所以 $t_a\ge\delta_a$ 必要。其基点是 $s-\sum_{a\in Z}t_a$，并集是 $s-\sum_{a\in Z\setminus\{n\}}t_a$，总门质量不超过 $s$。于是原事件行逐字给 C0、CB、CP 对 $t$ 的上界。它们都是对非负坐标和的上界，故把 $t$ 降为逐坐标最小 $\delta$ 仍成立；正确需求也仍成立。这证明所述条件必要。反向直接取这些最小门质量，空质量由 C0 非负，各帽行正是 CB、CP 与已声明正确、全正行，故充分。空 $A$、$s=0$、负原始正确需求、零缺额与闭等号都包括在同一证明中。

在 B 的公式中，零边给 $m=\sum\delta$、$\Psi=\sum_{Z}\delta$；把第二容量式移去 $\delta_n$ 恰是 CP，故逐项等价。旧条件 $\delta_a\le\min_{w_a=0}\eta_w(a)$ 给逐字正坐标支配，因而足以推出这些帽行，却不是本 iff 的必要条件。$\square$

若允许同时选择 $\kappa\le\lambda$，可直接用同一个完整表变量 $\kappa_D$ 与门变量 $t_a$ 写质量及全部仿射帽行，均为线性约束。固定 $\kappa$ 后最小度证明可消去多余 $t$。这一共同选择不能被各行独立的余项或独立优化的资金代替。

**例 221.17（D 的六位实际见证、下降与独立并集行）。** 取

$$
L=6,\quad b=(11/21,11/21,11/21,65/126,65/126,4/9),\quad
 e=2/7,\quad h=2/63=4/126,\quad A=\{1,2,3,4\}.
$$

全部 $\kappa$ 表如下，质量以 $1/126$ 为单位。

| 停止日程 | 输出 $0,10,11$ | $126\kappa_D$ |
| --- | --- | ---: |
| $1,2$ | $1,2,0$ | 12 |
| $1,2$ | $1,2,3$ | 6 |
| $1,3$ | $0,3,0$ | 2 |
| $1,3$ | $1,3,0$ | 6 |
| $1,4$ | $1,4,0$ | 6 |
| $2,3$ | $0,3,0$ | 8 |
| $2,3$ | $0,3,5$ | 1 |
| $2,3$ | $2,3,4$ | 3 |
| $2,4$ | $0,4,0$ | 6 |
| $2,5$ | $0,5,0$ | 3 |
| $2,5$ | $2,5,0$ | 5 |
| $3,4$ | $0,4,0$ | 6 |
| $3,4$ | $0,4,5$ | 4 |
| $3,5$ | $0,5,0$ | 4 |
| $4,5$ | $0,5,0$ | 2 |
| $4,5$ | $0,5,6$ | 10 |
| $5,6$ | $0,6,0$ | 10 |

其质量为 $94/126=47/63$。$\eta$ 为下面八张表，每张质量 $h$：

| 完整表 | 质量 |
| --- | --- |
| $N(5,6;1,2,3,4)$ | $h$ |
| $O(1;1,0)$ | $h$ |
| $O(1,5;0,0,2)$ | $h$ |
| $O(1,6;0,2,0)$ | $h$ |
| $O(1,5;0,3,0)$ | $h$ |
| $O(1,6;0,0,3)$ | $h$ |
| $O(1,5;0,4,0)$ | $h$ |
| $O(1,6;0,4,0)$ | $h$ |

总质量 $M=1$，同余项 $\rho=\kappa$，块质量 $s=8h$。准确缺额 $\delta=(0,h,h,h,0,0)$，零边替换为三张各 $h$ 的 $O(2;2,0),O(3;3,0),O(4;4,0)$ 与 $5hE_0$。

令 $x_i=w_i$，$Z_0(x)=126\kappa_w(0)$。逐胞相加给

$$
\begin{aligned}
Z_0(x)={}&56-2x_1-18x_2-14x_3-12x_4-10x_5\\
&+12x_1x_2+8x_1x_3+6x_1x_4+8x_2x_3+6x_2x_4+8x_2x_5\\
&+6x_3x_4+4x_3x_5+2x_4x_5+10x_5x_6,\\
126p_N(0)={}&Z_0(x)+4(6-3x_1+x_1x_5+x_1x_6),\\
126p_O(0)={}&Z_0(x)+4(5+x_2+x_3+x_4).
\end{aligned}
$$

$\kappa$ 的各首零正确分子为 $(30,26,26,25,29,20)$。原完整律正确分子分别为

$$
34+4(1-x_5)(1-x_6),\quad30+4x_5(1-x_6),\quad
30+4(1-x_5)x_6,\quad29+4(1-x_5)(1-x_6),\quad29,\quad20;
$$

新律为 $(30,30,30,29,29,20)$。固定首零前缀，对基点多项式、正确多项式及其同字之和分别作有限布尔最小值递推，给下面全部事件极小值，单位为 $1/126$。

| $n$ | 需求基点 | 需求正确 | 需求并集 | 原 $N$ 三行最小值 | 新 $O$ 三行最小值 |
| ---: | ---: | ---: | ---: | --- | --- |
| 1 | 24 | 30 | 90 | $(56,34,90)$ | $(60,30,90)$ |
| 2 | 24 | 30 | 90 | $(56,30,90)$ | $(64,30,94)$ |
| 3 | 24 | 30 | 90 | $(60,30,90)$ | $(70,30,100)$ |
| 4 | 25 | 29 | 90 | $(62,29,95)$ | $(78,29,107)$ |
| 5 | 25 | 29 | 90 | $(68,29,97)$ | $(88,29,117)$ |
| 6 | 34 | 20 | 90 | $(76,20,96)$ | $(92,20,112)$ |

全正基点分子是 $90,102$，需求 $90$。这给每律全部 190 行，而不是只给部分单点。尾和 $\sum_{n=3}^6b_n=2=7e$，上式 $11/21\le1$，次序条件满足；同一原完整 $\lambda$ 实际证明 $H_N$。表中界也证明零边 CB、CP 在同余项上逐字成立。

旧块的整零面最小值在标签 1 至 4 为 $(h,0,0,0)$，所以旧的逐字正坐标支配测试不能满足标签 2、3、4 的正缺额。但 D 用帽内余量付款：在 $000000$ 上，基点从 $40/63$ 降至 $38/63$，并集 $\{0,1\}$ 从 $59/63$ 降至 $53/63$，均仍满足其原始需求。这些真实下降不能被说成事件支配。

在 $001110$，用三个质量 $h$ 的恒标签 2、3、4 与 $5hE_0$ 替换整个块，独立并集只有 $41/63<45/63=1-e$；同一字的单点门替换并集为 $45/63$。这是一条独立并集反例行。并集约束不是由各自单点最小值拼成的。

在 $100001$，首零 2、代码 $01$，$\kappa_w(2)=13/63$，两个对应错配供体均不贡献正确 2，代码恰提供 $h$，合计 $15/63=b_2-e$。只把代码改成零会缺 $h$，所以代码确实承担该原配置的正确需求；联合替换八表块才满足帽。

原律的标签 1 核坐标是

$$
p_N(1)=(17/63)(1-x_1)+(2/63)(1-x_5)(1-x_6).
$$

其常数为 $19/63$，109.1 阈值为 $17/63+2/63+2/63=1/3$，故原精确律不是停止核。另一停止律已满足同一帽，没有原始停止分离。

### 221.6 原始来源、同一随机种子与全部实际尾部

**定义 221.18（原始来源、载体与分别声明的标记目标）。** 保持原始可数带标签来源

$$
X=\{(r,g):r\text{ 是素数},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},
\quad N_x=1+F_rg,
\quad q_i(x)=[p_i\mid N_x],
$$

其中 $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$，$p_i$ 为第 $i$ 个素数。回答静态；每个实际整数素因子有限，故 $n(x)=\min\{i:q_i(x)=0\}$ 有限。没有给 $X$ 分布，也没有引入无限全正来源。

原始带空间仍为 $B_j,P_j$ 各个 $(0,1)$ 副本的 Borel 不交并；消费者在 $B_j$ 输出 unknown，在 $P_j$ 提议 $j$。原始非原子族仍为

$$
\mu_x=(1-h_0)\nu_x+h_0\pi_{\omega(N_x)},\qquad0<h_0<1,
$$

其中 $\nu_x$ 在 $B_{n(x)}$ 上有归一化密度正比于 $\exp(t(x)u)$，$t(x)=\sum_i3^{-i}q_i(x)$，$\pi_j$ 在 $P_j$ 上均匀，$\omega(N_x)$ 为原始素因子计数参数。取原带上的不同点 $\theta_j=(B_1,1/(j+2))$，另行声明标记目标

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
$$

有限标记律与每个原始非原子 $\mu_x$ 的 TV 为一：取其有限支持集，标记律质量一而非原子律质量零。因此上述具体标记帽见证不是原始非原子族的替换或其帽见证。完整竞争者仍可输出任意原始带。

**命题 221.19（实际表执行与资源保真）。** 每个显示的质量一完整配置在原来源上由一个来源独立的 $U\in[0,1)$ 执行：用固定区间选择整个日程与所有胞输出，然后取得该日程的回答并交付相应原带点。$N$ 取得预选的整个日程；$O$ 预选递增日程并在首个被查询零或耗尽时停止。不同律可用同一 $U$ 的共同有限细分比较，不产生第二个随机资源。所有本节表在每个来源与种子上最多发出两次实际请求，无建议，且可测有限交付。

**证明。** 有限非负质量和一给固定半开区间分割。区间决定的表及日程与回答无关；每张表的执行树只有零、一或两次请求。输出在预先选定有限集合，是静态回答的可测函数。停止表的 $N$ 完成式在共享首胞后仍取得第二回答，可以忽略它，但该请求仍计数；重复地址的请求也逐次计数。没有适应性第二地址、免费探测、来源先验、运行时间、地址大小、深度或平均次数替换硬两请求预算。$\square$

35.2 的素数入列秩、CRT 与实际 Fibonacci 窗口证明保证每个有限位模式在任意有限地址上有实际来源实现，且同一模式阈值可统一取定。因此本节的全部有限字是在抽种子前选择的实际来源接口，而不是只在抽象虚构来源上验证。全正有限字代表那些实际首零更晚的来源。

例如 $r=19,g=436,N_x=1822917$ 给低字 $0100$。$N(3,4;1,0,0,0)$ 在此字正确输出更早未查询的标签 1，事件读数为 $(0,1,1)$；把它修剪到零给 $(1,0,1)$，损失正确行。故完整原目录不能删除这种输出。本节原代码表也保留同样的合法较早猜测。

另一个独立并集边界是 $p(0)=p(n)=1/4,a_n=1/2,e=1/4$：两条单点下界均达到，却只有并集 $1/2<3/4$，实际 TV 为 $1/2$。所以每个有限表格均单独保留并集行。

**命题 221.20（实际律的尾部与低观察替换）。** 对支持在标记 $0,\ldots,H$ 的实际律 $p_x$ 和实际首零 $n(x)>H$，

$$
\operatorname{TV}(p_x,\lambda_x^a)
=1-\min(p_x(0),1-a_{n(x)})
=\max(1-p_x(0),a_{n(x)}).
$$

闭帽等价于 $p_x(0)\ge1-\varepsilon$ 且 $a_{n(x)}\le\varepsilon$。若另外执行一个来源独立种子选择的有限完整核，所有实际观察坐标均在 $1,\ldots,H$，输出仅依赖该种子及取得的回答，则有 $p_x=P(q_1(x),\ldots,q_H(x))$；这时才可在全部 $n(x)>H$ 来源上把它换成共同的 $P(1^H)$。

**证明。** 首零标记 $n(x)$ 不在输出支持中，目标与实际律只能在标记零相交，其共同质量恰为上述最小值。另一个陈述固定同一个种子：同低字来源给相同的全部取得回答、停止路径和输出，因此有相同字核。有限输出支持本身不控制观察地址，不能证明后一替换。$\square$

本节所有实际示例的观察地址均在其 $L$ 内，输出只依赖表、种子及回答，故额外假设已由列出的表实际满足。对 A、B、D 的 $L=6$ 例，取任意 $0<t\le1$，用 $t$ 倍原完整律加 $(1-t)E_0$，令

$$
a_n(t)=tb_n\ (n\le6),\qquad
 a_n(t)=te\,2^{-(n-7)}\ (n\ge7),\qquad \varepsilon(t)=te.
$$

序列正、非增、趋零，$a_7=\varepsilon$ 是保留的闭等号；严格活跃长度为六。每个有限正确与基点需求随 $b,e$ 仿射变化，原三事件式加全基点律对应的三事件式，恰给新 $tb,te$ 的全部需求；原全基点律在零参数上的正确需求是零，不需要删除该行。硬域尾不等式仍等号，另一式随 $t$ 缩小，同一混合 $N$ 配置仍证明 $H_N$。

| 例 | 实际 $n>6$ 的 $N$ 误差 | 实际 $n>6$ 的 $O$ 误差 | 正闭帽 |
| --- | --- | --- | --- |
| A，221.6 | $\max(47t/200,a_n(t))$ | $\max(9t/40,a_n(t))$ | $47t/200$ |
| B，221.10 | $\max(6t/25,a_n(t))$ | $a_n(t)$ | $6t/25$ |
| D，221.17 | $\max(2t/7,a_n(t))$ | $\max(4t/21,a_n(t))$ | $2t/7$ |

这些公式来自全正基点，分别为原例的 $153/200,19/25,5/7$ 与新例的 $31/40,1,17/21$，再加全基点混合。对每个实际尾项都成立，$n=7$ 两类均达到其闭帽。例如 $r=47,g=297421613,F_{47}=2971215073,N_x=883703579581572750$ 的低七位为 $1111110$，实际首零正是七。连续径向族仅示范关系，已有的幅度族与运输不另计内容。

C 的实际 $L=7$ 例取 $a_n=b_n$（$n\le7$），$a_n=(124/500)2^{-(n-8)}$（$n\ge8$），闭帽 $124/500$。观察只在低七位，故每个实际 $n>7$ 的原误差为 $\max(1/20,a_n)$，新停止误差为 $a_n$；$a_8=e$ 闭等号包含。前缀全部行已由 221.14 验证，正确 2 的最小值 $116/500$ 比目标 $240/500$ 少帽值 $124/500$，故实际首零 2 且后缀匹配代码的来源也达到该帽。薄化后的 B 律同样可行，其尾基点仍为一。此例不增加一个独立幅度分类。

221.11 的四表律也可接 $a_1=a_2=a_3=1$、$a_n=2^{-(n-4)}/4$（$n\ge4$）及闭帽 $1/4$；全正基点 $3/4$，所有实际后期误差为 $\max(1/4,a_n)=1/4$。该既有见证的严格活跃长度为三，而有限展示可取六或其他更长地平线，两者不可混同。

**注记 221.21（有符号锥与原运输边界）。** 对一般质量 $M$ 的可行锥配置，只有

$$
0\le\tau\le1/\max(1,M),\qquad
\tau\mu_D\text{ 及 }(1-\tau M)R
$$

是合法概率填充。其事件向量为 $r+\tau G_O\mu\ge r+\tau h=d(\alpha+\tau(b-\alpha))$。径向参数的序列次序、正幅度、所有实际尾项仍须分别核对；$M>1$ 的原有符号仿射余项不被执行。本节实际表例质量均为一，已直接给出这些条件。

109.1 是概率向量核的共同日程质量刻画，110.2 是两类在正闭帽下的原始全载体、任意地址运输，均按原证明复用。其必要方向保留可数来源上的共同余零有限交付事件、整个预选日程最大地址的尾概率控制、种子前固定的实际有限模式、有限执行截断与有限单纯形紧致性；不是把原始竞争者缩到展示的低地址。207.20 的两种地平线方向也保留：较短活跃表示可在实际尾幅度不超过帽时增加尾行；较长表示可为较短比较作限制及多余标签投影，但该限制本身不是被删去活跃尾上的原始见证。严格活跃长度定义为 $L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$，等帽尾不能删除；所查询地址从不被假定小于 $L_a$。

### 221.7 复用范围与仍未解决的原始关系

两条独立条件关系的数学范围是：A 的共同基点与三候选质量 iff，B 的最小正确度、端点图及全部同余项帽容量 iff。221.6 与 221.10 的相反同余项失败说明两种指定操作不能相互替代。C 的整零面模包络、实容量流、两族割和已资助/中性表是 B 内的充分构造；D 是 B 的零边情形并允许帽内付费事件下降。所有例仍各自同时有原始 $N$ 与另一 $O$ 可行律。

截断子集立方体、三标签收集、109.1 标量质量恒等式、弱对偶、既有包络单点门、完整硬域、运输与已知四表见证均复用，不另计独立数学区域。220 的整零面支配门给 D 的一个充分子域；D 的 iff 允许本节列出的真实基点与并集下降，所以不能把它写成相对原块的全事件支配。旧 138 的掩码凸性与 220 的完整内掩码关系不增加本节信用。200.4–200.5 已覆盖整个单基点首零类得分域，该类的链正规形或再一个供应实例均为零重复信用。

本节只采用上述 A/B 及 B 内 C/D；不包含其他候选的一元性必要条件、错误诊断数值或关于既有凸包的覆盖比较。没有声称新的世界范围优先权或排除所有旧凸、锥、极或有符号组合后果。外部有限多面体及实容量网络流方法是成熟工具；这里的具体帽行关系由完整普通证明承担，不用文献类比代替其前提。

原始全域目标仍是 open：对每个 $L\ge3$ 和每个实际完整 $y\ge0$，若 $\Delta_O(y)\le1$，需构造一个不受额外限制的完整 $V\ge0$ 及 $\theta\in[0,1]$，使

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
$$

其中 $\sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e)$。$V$ 可改变所有单点、基点、完整律、商、支持、后缀及终端；$\theta=1$ 时非零零成本 $V$ 仍合法。固定余项、保持商、端点或模包络不能被加入原目标的必要条件。

负向替代必须在同一个实际 $(b,e)\in H_N$、同一个完整可行 $\lambda\ge0$、$G_N\lambda\ge h$、$M=\sum\lambda\ge1$ 上，给实际完整单位停止得分 $y$ 的严格不等式

$$
F_{Q(y)}(b,e)>M,
$$

再给原始共同种子 $N_2$ 见证与对每个完整载体、任意地址 $O_2$ 竞争者的统一下证书，并保留所有实际来源、Borel 事件、多零字、正趋零尾及正闭帽。端点、单点门、固定代码或模包络失败不满足这个负向条件；精确原律不可停止也不满足它。

本节没有证明每个可负担原配置都能找到上述 $\kappa+\eta$ 分解或 A/B 候选，没有对全部单位停止输入提供同一预算证书，也没有原始严格分离。原始所有正非增趋零序列、所有正闭帽及严格活跃长度 $0,1,2$ 的小端分支均保持其原有义务。本节为普通理论成果，未作 Lean、编译、摄入、覆盖或冻结声明。

## 追加锚（本行以下为增补区）

## 222. Full-score constructors, signed charges and their domains

**Definition 222.1 (Complete words, rewards and tables).** Fix an integer $L\ge3$.
Let $J_L=\{0,\ldots,L\}$, $\Omega=\{0,1\}^L\setminus\{1^L\}$,
$n(w)=\min\{j:w_j=0\}$ and $\Omega_j=\{w:n(w)=j\}$.
A full score $V$ consists of independent nonnegative numbers
$A_w,C_w,P_w$ for every $w\in\Omega$, and $T\ge0$. Its reward is

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
 +P_w\mathbf1_{\ell\in\{0,n(w)\}},\qquad
g_V(1^L,\ell)=T\mathbf1_{\ell=0}.
$$

An empty table has one output, a singleton table has outputs on cells
$0,1$, and a full pair table $N(i,j;a,b,c,d)$, $i<j$, has outputs
$a,b,c,d$ on cells $00,01,10,11$. A stopped pair table
$O(i,j;a,c,d)$ has outputs on cells $0,10,11$; its first cell merges
$00,01$ before any maximization. Every cell allows every label in $J_L$,
including labels earlier than both queries and labels never queried.
The complete catalogs $\mathcal D_N,\mathcal D_O$ include all such
empty, singleton and pair tables. At a schedule $S$ set

$$
B_{\mathcal C}^{S}(V)=\sum_{E\text{ a cell of }S}
 \max_{\ell\in J_L}\sum_{w\in E}g_V(w,\ell),\qquad
B_{\mathcal C}(V)=\max_S B_{\mathcal C}^{S}(V).
$$

Put $R=O(1,2;1,2,0)$, with full completion $N(1,2;1,1,2,0)$, and

$$
\begin{aligned}
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(V)&=B_{\mathcal C}(V)-W_V,\\
Q(V)&=(\beta_1,\ldots,\beta_L;K),\quad
\beta_j=\sum_{\Omega_j}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
$$

Thus $W_V$ is the reward of $R$ and $0\le\Delta_O\le\Delta_N$.
Both $Q$ and $W$ are linear; $B_{\mathcal C}$ and $\Delta_{\mathcal C}$
are homogeneous and subadditive on nonnegative scores. A reversed pair
permutes the full cells, and a repetition gives singleton information.
These are identities for evaluating supports: actual repeated and ignored
requests still count. Unspecified coefficients in every example below
are zero, and coincident contributions add. Zero score coefficients
never remove event constraints.

**Definition 222.2 (Full demands and one signed charge).** For a finite
profile $(b,e)$ let $d(b,e)$ contain the three separate demands

$$
1-b_n-e,\qquad b_n-e,\qquad1-e
$$

on the events $\{0\},\{n\},\{0,n\}$ at every $w\in\Omega_n$,
and the demand $1-e$ on $\{0\}$ at $1^L$.
There are $3(2^L-1)+1$ rows. Negative singleton demands remain literal;
the pair row is independent. Write $z_D$ for a complete table's event
vector, $\alpha=(1,1,0,\ldots,0;0)$, $r=z_R=d(\alpha)$,
$h=d-r$ and $G_{\mathcal C}=(z_D-r)_{D\in\mathcal D_{\mathcal C}}$.
Use the closed hull of 198.5:

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\}.
\end{aligned}
$$

For any signed $q=(\beta;K)$ define

$$
F_q(b,e)=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad
\sigma_H(q)=\max_{H_L}F_q.
$$

In particular $V\cdot h=F_{Q(V)}$. The complete vertex list is
$o=(0,\ldots,0;0)$, $p=(1,0,\ldots,0;0)$ and

$$
u_k=(\underbrace{1/(k-1),\ldots,1/(k-1)}_k,0,\ldots,0;0),\qquad
v_k=(\underbrace{1,\ldots,1}_k,e_k,\ldots,e_k;e_k),\quad
e_k=\frac{k-2}{k+1},\quad3\le k\le L.
$$

For $B=\beta_1+\beta_2$, $S_k=\sum_{j\le k}\beta_j$ and
$\kappa=K-S_L$, all residual readings are

$$
F_q(o)=-B,\quad F_q(p)=-\beta_2,\quad
F_q(u_k)=\frac{S_k}{k-1}-B,\quad
F_q(v_k)=\frac{3S_k-(k-2)\kappa}{k+1}-B.
$$

A full unrestricted certificate for $q$ is one $V\ge0$ and one
$\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad \sigma_H(q-Q(V))\le\theta.
$$

Its objective before imposing the unit bound is

$$
J_q(V)=\Delta_N(V)+\max\{0,\sigma_H(q-Q(V))\}.
$$

Set $H_N=\{(b,e)\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h(b,e)\}$.
For the same complete feasible $\lambda$ at that same point, put
$M=\sum_D\lambda_D$. Nonnegativity gives the reused weak-duality chain

$$
F_q(b,e)\le V\cdot h+\theta
 \le V\cdot G_N\lambda+\theta
 \le M\Delta_N(V)+\theta\le\max\{1,M\}.
$$

For $M\le1$ use $M\Delta_N\le\Delta_N$; for $M\ge1$ use
$\theta\le M\theta$. A mass-one $\lambda$ is a normalized law,
whereas a general conic $\lambda$ is not. In particular $\theta=1$
permits nonzero scores with $\Delta_N(V)=0$. No component, mask, cell
or demand receives an additional budget.

**Definition 222.3 (Erasure of a score).** For any $E\subseteq[L]$,
let $f_E(w)$ set the bits in $E$ to one. Define $T_EV$ rowwise.
If the old first zero survives, move its $A,C,P$ coefficients to
$f_E(w)$ without changing their types. If the old first zero is erased,
discard its $C$ coefficient and move its $A+P$ coefficient to type $A$
at $f_E(w)$ if that word has a zero, and to $T$ otherwise.
The old $T$ persists; collisions add. This is a linear nonnegative
operation on proof scores, with no change to source replies or an
acquisition. Define two different constructor sets:

$$
\begin{aligned}
\mathcal M_L(y)&=\left\{\sum_{E\subseteq[L]}t_ET_Ey:t_E\ge0\right\},\\
\mathcal K_L(y)&=\left\{\sum_{E\subseteq\{3,\ldots,L\}}t_ET_Ey:
 t_E\ge0,\ \sum_Et_E=1\right\}.
\end{aligned}
$$

The first allows all early and late erasures and arbitrary conic scale;
the second is the normalized convex interior-mask constructor.

For interior $E$, $W_{T_Ey}=W_y$: an erased late row had anchor
contribution $A+P$, exactly its new base or terminal contribution,
while the discarded $C$ had zero anchor contribution. A retained first
zero has the same class, including both early classes. Summing proves
the identity for arbitrary full scores. Early erasure need not preserve
$W$ in general.

Both full supports contract under an individual erasure. Indeed, in a
transformed table replace any output in $E$ by zero, fix every erased
reply to one, and delete those queries. The remaining table is legal
in the original class, including the stopped increasing class. At a
word whose first zero survives, its transformed reward is its original
reward. At an erased first zero, the transformed base reward $A+P$
is available at original label zero, while discarded $C$ is nonnegative.
Thus the resulting original table dominates the transformed reward
wordwise. These facts explain conditional uses of masks; they do not
assert that either constructor contains a certificate for every input.

## 223. An exact four-thirds minimum over the entire erasure cone

**Theorem 223.1 (All-erasure conic minimum).** For every $L\ge4$,
pad each displayed four-bit zero word by $1^{L-4}$, put $T=2$ at
$1^L$, and define $y$ by

$$
C_{1101}=C_{1110}=3,\qquad
P_{0100}=P_{0101}=P_{0110}=P_{1000}=P_{1001}=P_{1010}=1.
$$

Then $\Delta_O(y)=1$ and

$$
\min_{V\in\mathcal M_L(y)}J_{Q(y)}(V)=\frac43.
$$

The minimum allows arbitrary nonnegative weights on every early/late
erasure. The input nevertheless has unrestricted unit certificates.
Its lower-bound point lies in $H_L\setminus H_N$.

**Proof.** In schedule order
$\varnothing;1,2,3,4;12,13,14,23,24,34$, the complete supports are

$$
\begin{aligned}
B_N^S(y)&=(8;8,8,8,8;9,9,9,9,9,10),\\
B_O^S(y)&=(8;8,8,8,8;9,9,9,9,9,9).
\end{aligned}
$$

Every entry sums all-label cell maxima of the displayed rows.
Thus $W_y=8$, $Q(y)=(0,0,3,3,0,\ldots;14)$ and the stopped excess
is one. Put

$$
b_*=(11/18,11/18,11/18,11/18,1/6,\ldots,1/6;1/6)
 =\frac7{12}u_4+\frac5{12}v_4.
$$

This proves membership in $H_L$, and $F_{Q(y)}(b_*)=4/3$.
Use these fixed full tables:

$$
D_1=N(2,3;0,0,3,0),\quad
D_2=N(2,4;0,0,4,0),\quad
D_3=N(3,4;0,3,4,0).
$$

For $g_i(V)=V\cdot(z_{D_i}-r)$ set
$\ell(V)=(g_1(V)+g_2(V)+g_3(V))/3$.
The full support gives $\Delta_N(V)\ge\ell(V)$ for every $V\ge0$.
The following table is the complete erasure basis. It records $W=8$
in every row, the three actual excesses, the same hull reading, and
$k_E=\ell(T_Ey)-F_{Q(T_Ey)}(b_*)$.

| $E$ | $(g_1,g_2,g_3)(T_Ey)$ | $F_{Q(T_Ey)}(b_*)$ | $k_E$ |
| --- | --- | --- | --- |
| $\varnothing$ | $(1,1,2)$ | $4/3$ | $0$ |
| $\{4\}$ | $(1,0,-1)$ | $0$ | $0$ |
| $\{3\}$ | $(0,1,-1)$ | $0$ | $0$ |
| $\{3,4\}$ | $(0,0,0)$ | $-4/3$ | $4/3$ |
| $\{2\}$ | $(-1,-1,2)$ | $-1/2$ | $1/2$ |
| $\{2,4\}$ | $(-1,0,-1)$ | $-11/9$ | $5/9$ |
| $\{2,3\}$ | $(0,-1,-1)$ | $-11/9$ | $5/9$ |
| $\{2,3,4\}$ | $(0,0,0)$ | $-4/3$ | $4/3$ |
| $\{1\}$ | $(1,1,2)$ | $-1/2$ | $11/6$ |
| $\{1,4\}$ | $(1,0,-1)$ | $-11/9$ | $11/9$ |
| $\{1,3\}$ | $(0,1,-1)$ | $-11/9$ | $11/9$ |
| $\{1,3,4\}$ | $(0,0,0)$ | $-4/3$ | $4/3$ |
| $\{1,2\}$ | $(-1,-1,2)$ | $-7/3$ | $7/3$ |
| $\{1,2,4\}$ | $(-1,0,-1)$ | $-22/9$ | $16/9$ |
| $\{1,2,3\}$ | $(0,-1,-1)$ | $-22/9$ | $16/9$ |
| $\{1,2,3,4\}$ | $(0,0,0)$ | $-4/3$ | $4/3$ |

For example erasing bit 3 deletes $C_{1101}$, moves the two early
pair rows ending $00$ to their $10$ counterparts, and retains the
other early pair rows and $C_{1110}$. Evaluating the three displayed
tables gives $(0,1,-1)$ and reading zero. The same routing rule on the
nine original nonzero coefficients gives every entry of the table;
there is no optimization premise in these linear calculations.

All $k_E\ge0$. Masks above four fix every scored atom, so this basis
covers every mask for every $L\ge4$. For arbitrary conic coefficients,
without requiring their sum to be one,

$$
\ell(V)-F_{Q(V)}(b_*)=\sum_Et_Ek_E\ge0.
$$

The one residual charge is at least
$4/3-F_{Q(V)}(b_*)$. Adding gives $J_{Q(y)}(V)\ge4/3$.
This also includes $V=0$ and all conic scales.

For attainment take

$$
V_*=\frac12y+\frac16T_{\{3\}}y+\frac16T_{\{4\}}y.
$$

The coefficients sum to $5/6$, which is allowed in the cone.
Its literal rows are $C_{1101}=C_{1110}=2$, $T=5/3$, and

| Word | $P$ in $V_*$ |
| --- | --- |
| $0100,1000$ | $1/2$ each |
| $0101,0110,1001,1010$ | $5/6$ each |
| $0111,1011$ | $1/3$ each |

Consequently $W_{V_*}=20/3$, $Q(V_*)=(0,0,2,2,0,\ldots;32/3)$,
and its full $N$ support vector in the same order is

$$
(20/3;20/3,20/3,20/3,20/3;7,22/3,22/3,22/3,22/3,22/3).
$$

Thus $\Delta_N(V_*)=2/3$. The residual has late coordinates $1,1$
and charge $K=10/3$. Its readings at $o,p,u_3,v_3$ are
$0,0,1/2,5/12$; for every $k\ge4$ they are

$$
F(u_k)=\frac2{k-1},\qquad
F(v_k)=2-\frac{10}3\frac{k-2}{k+1}.
$$

Both latter sequences decrease from $2/3$ at four. Its residual charge
is $2/3$, proving attainment of $4/3$.

For completeness, the support vectors remain complete after padding.
Every extra queried bit is constantly one on every weighted original
or transformed atom. Fixing that reply folds its observation to a legal
low empty, singleton or pair partition. Extra numerical labels earn
zero, and a zero reward is already available in each cell. Conversely
each low table embeds at the larger length. Thus no high-address table
increases these support maxima. All new hull vertices were evaluated
by the displayed formulas; no unscored event row is discarded. $\square$

**Example 223.2 (Unrestricted escapes and the infeasible lower point).**
The exact-$Q$ score supplied by 214.5 is

$$
\widehat V:\quad C_{1100}=C_{1110}=3,\quad
P_{0100}=P_{1000}=2,\quad P_{0110}=P_{1010}=1,\quad T=2.
$$

It has $Q(\widehat V)=Q(y)$, $W=8$, and both complete support vectors

$$
(8;8,8,8,8;9,9,8,9,8,9).
$$

Thus $(\widehat V,0)$ is an unrestricted unit certificate.
Erasure can only change zero bits to ones: it cannot create the correct
row $1100$ from the original class-three correct row $1101$.
Hence $\widehat V\notin\mathcal M_L(y)$.

The zero-cost score supplied by 204.4–204.5 is

$$
V_0:\quad C_{1101}=C_{1110}=3/2,\quad
P_w=3/4\ (w=0100,0101,0110,1000,1001,1010),\quad T=3/2.
$$

Here $W=B_N=B_O=6$ and $Q(V_0)=(0,0,3/2,3/2,0,\ldots;9)$.
Its residual against $y$ reads $0,0,3/4,5/8$ at $o,p,u_3,v_3$ and

$$
\frac3{k-1},\qquad3-5\frac{k-2}{k+1}\quad(k\ge4),
$$

with maximum one at $u_4,v_4$. Thus $(V_0,1)$ is another unrestricted
unit certificate, including the nonzero zero-cost endpoint. Theorem
223.1 also excludes this $V_0$ from the cone.

At the same lower point $F_{Q(V_0)}(b_*)=1/3>0$.
Any complete feasible conic $\lambda$ there would give
$1/3\le M\Delta_N(V_0)=0$. Therefore $b_*\notin H_N$ for every
possible conic mass. Independently, the equal mixture of $D_1,D_2,D_3$
has law $(1/3,0,0,1/3,1/3)$ at word $1100$. Its correct probability
$1/3$ is below $4/9$, and its pair probability $2/3$ is below $5/6$.
Its TV from $(7/18)\delta_0+(11/18)\delta_3$ is $1/3>1/6$.
The lower functional is a legal rule but is not a full feasible allocation
at that point. This cone obstruction supplies no original separation.

## 224. Rigidity and the whole normalized stopped plateau face

**Theorem 224.1 (Normalized full-table counting rigidity).** Let $k=L\ge3$,
$b=(1,\ldots,1)$, $e=(k-2)/(k+1)$ and $s=1-e=3/(k+1)$.
Suppose one normalized common mixture of complete $N$ tables, or of
complete $O$ tables, satisfies every row of $d(b,e)$. Then every
sole-zero word has correct probability exactly $s$, the positive word
has base probability exactly $s$, and in every deterministic decomposition
almost every table uses two distinct queried indices, is correct at each
of its two queried sole-zero words, and outputs either zero or an unqueried
numerical label at the positive word. Its total numerical-exhaustion mass
is exactly $e$. In sorted full $N(i,j)$ order its $01$ output is $i$
and its $10$ output is $j$. This theorem leaves its $00$ output unclassified.

**Proof.** Let $w^{(n)}$ have just one zero, at $n$, and let $w^+=1^k$.
For one deterministic table let $S$ be its set of distinct queried
coordinates, $|S|\le2$, and let $\ell$ be its output at $w^+$.
Every sole-zero word outside $S$ has the positive transcript. Hence

$$
\sum_{n=1}^k\mathbf1_{D(w^{(n)})=n}
 \le |S|+\mathbf1_{\ell\in[k]\setminus S}
 \le2+\mathbf1_{\ell\ne0}.
$$

Integrate under the same normalized mixture. The full correct and
positive rows give

$$
ks\le\sum_{n=1}^kp_{w^{(n)}}(n)
 \le3-p_{w^+}(0)\le3-s=2+e=ks.
$$

Every inequality is equality. Each of the $k$ correct probabilities
is at least $s$ and their sum is $ks$, so each equals $s$; also
$p_{w^+}(0)=s$. The nonnegative deterministic slack has integral zero.
Thus each positive-mass table attains both deterministic bounds: it has
two distinct queried coordinates, is correct on both corresponding
sole-zero words, and, if $\ell\ne0$, then $\ell\notin S$.
The numerical-exhaustion mass is $1-p_{w^+}(0)=e$.
For $i<j$, sole-zero $i$ reaches full cell $01$, and sole-zero $j$
reaches $10$, proving the asserted full-cell entries. No step fixes
$00$, and no such classification is inferred. $\square$

**Theorem 224.2 (Complete normalized $O$ face).** Under the same parameters,
the whole normalized full-row feasible stopped face consists exactly of
common probability laws $\pi$ on three-element subsets of

$$
\{1,\ldots,k,\infty\}
$$

such that every one of the $k+1$ labels has inclusion probability $s$.
For a triple $i<j<r$, query $i,j$ in increasing preselected order,
output $i$ or $j$ at its first queried zero, and output $r$ on exhaustion;
$\infty$ means label zero and is never queried. Zero triple weights are
allowed. These conditions are necessary on all words and sufficient for
all independent base, correct, pair and positive rows.

**Proof.** Theorem 224.1 forces every positive-mass stopped table to have
form $O(i,j;i,j,r)$, $i<j$, with $r=0$ or $r\notin\{i,j\}$.
For any first-zero-$n$ word, its correct-$n$ indicator is no greater
than its indicator at the sole-zero-$n$ word. If $n$ is queried it
is reached correctly, because all selected earlier bits are one. If it
is unqueried, the only possible correct output is the exhaustion guess
$n$, and adding later zeros can remove, but cannot create, that output.

Suppose a positive-mass table guesses a numerical $r<j$. Take a word
with first zero $r$ and also bit $j$ zero, all other bits one.
Since $r$ is unqueried, the table now emits $j$, losing its correct-$r$
contribution. No other forced-form table gains relative to sole-zero
$r$, where the aggregate correct mass is already exactly $s$.
Consequently the full correct row at that multiple-zero word fails.
There are finitely many tables, so every such earlier-guess table has
weight zero. Thus every numerical guess satisfies $i<j<r$.

The remaining tables correspond bijectively to the triples stated in
the theorem. On every first-zero-$n$ word, their output is $n$ exactly
when the triple contains $n$: if selected for querying, all selected
predecessors answer one; if the last selected label, both queries are
earlier; if absent from the triple, it is never emitted. At $w^+$ output
zero is equivalent to inclusion of $\infty$. The tight sole-zero and
positive rows therefore force all inclusion marginals to equal $s$.

Conversely choose any one law on triples with these marginals.
For every zero word its correct mass is $s$, its pair mass is at least
$s=1-e$, and its base mass is nonnegative, hence at least the literal
base demand $-e$. Its positive base mass is $s$. This checks every row,
including arbitrary multiple zeros; it proves sufficiency for the entire
face, rather than for one chosen symmetric law. The marginal sum is
$3$, consistent with $(k+1)s=3$ and one common total mass one. $\square$

**Example 224.3 (Reserve, existence and actual closed tails).** Uniform
weight $1/\binom{k+1}{3}$ on the triples is the plateau law of 87.1;
its realization and endpoint catalog are also supplied by 176.1 and
200.4. Its existence receives no additional amplitude classification.
For $k=3$ the four triples give weight $1/4$ each on

$$
O(1,2;1,2,3),\quad O(1,2;1,2,0),\quad
O(1,3;1,3,0),\quad O(2,3;2,3,0).
$$

An exhaustion-zero queried-endpoint-only normalized rule has total
correct sole-zero degree at most two. Here $ks=2+e>2$, so that
restricted constructor cannot describe the feasible plateau; a numerical
unqueried exhaustion reserve of exactly $e$ is necessary.

On the original selected marked laws take

$$
a_n=1\ (n\le k),\qquad a_{k+j}=e2^{1-j}\ (j\ge1),\qquad
\varepsilon=e.
$$

These amplitudes are positive, nonincreasing and tend to zero, with
strict active length $k$ and $a_{k+1}=e$. Every low-word TV error is
$e$, since its target is the correct point mass and its correct output
probability is $s$. Every actual later source has tail error
$\max(e,a_n)=e$. One source-independent seed chooses the entire triple
before replies; its full $N$ completion obtains both replies and ignores
the reply after the stopped rule would have halted. These ignored
requests count. This is the reused closed-cap transport, not a necessity
classification of arbitrary original full-carrier laws. Theorems
224.1–224.2 impose normalization; they classify neither a general conic
mass $M$, nor the full $N$ face, nor its $00$ cells.

## 225. A fixed direction defeats normalized convex masks after every full input

**Theorem 225.1 (Arbitrary-background convex-mask obstruction).** For every
$L\ge3$ and every full $z\ge0$ with $\Delta_O(z)\le1$, there exists
$t>0$ such that $y=z+tY_0$ is still unit-$O$, has the unrestricted
certificate $(0,0)$, and satisfies $J_{Q(y)}(V)>1$ for every
$V\in\mathcal K_L(y)$. Here, for $\tau=1^{L-2}$,

$$
Y_0:\quad A_{00\tau}=1,\quad C_{01\tau}=C_{10\tau}=1,\quad T=1.
$$

It suffices to choose

$$
t>1+W_z,\qquad t\ge2\max\{0,\sigma_H(Q(z))\}.
$$

**Proof.** The full head schedule separates four unit rewards, so
$B_N(Y_0)=4$, attained by $D_*=N(1,2;0,1,2,0)$.
The stopped head merges the first two atoms of different labels and has
support three. Every later bit is constantly one on this support;
other effective schedules are empty or singleton and have support at
most two. Thus $W_{Y_0}=3$, $\Delta_N(Y_0)=1$,
$\Delta_O(Y_0)=0$ and $Q(Y_0)=(0,1,0,\ldots;4)$.

The two hull capacity inequalities, together with monotonicity, imply

$$
2b_2-4e=b_2+b_3-4e\le1.
$$

Indeed the upper capacity and $b_1\ge b_2$ give
$b_2+b_3+\sum_{j\ge4}b_j-(L+1)e\le1$, and
$\sum_{j\ge4}b_j\ge(L-3)e$.
Consequently

$$
F_{Q(Y_0)}=b_2-1-4e\le-\frac12-2e\le-\frac12,
$$

with equality at $u_3$. Subadditivity of the full stopped support and
linearity of the anchor give $\Delta_O(y)\le\Delta_O(z)\le1$.
At every hull point,
$F_{Q(y)}\le\sigma_H(Q(z))-t/2\le0$, proving the unrestricted
certificate $(V,\theta)=(0,0)$.

Every interior mask fixes $Y_0$. For any convex mask weights of total
one, write the resulting score as $V=V_z+tY_0$, with $V_z\ge0$.
The interior anchor identity gives $W_{V_z}=W_z$. The one full table
$D_*$ earns at least $4t$ on this same combined score, since its reward
on $V_z$ is nonnegative. Therefore

$$
\Delta_N(V)\ge4t-(W_z+3t)=t-W_z>1.
$$

The residual charge is nonnegative, so every such $V$ fails the joint
unit bound. The proof uses no assumption about the support, signs of
net coordinates, or mixture representation of the arbitrary background
$z$. It uses the actual combined support rather than a sum of separately
maximized component costs. $\square$

**Example 225.2 (Saturated unit family and its closed branch).** For every
real $s\ge1$, define

$$
Y_s:\quad A_{00\tau}=s,\quad C_{01\tau}=s-1,\quad
P_{01\tau}=1,\quad C_{10\tau}=s,\quad T=s.
$$

At each word $A_wC_w=0$. Direct full-head maxima are $(s,s,s,s)$,
and stopped-head maxima are $(s+1,s,s)$. The empty and singleton
supports are at most $2s+1$, and later queries are constant on the
weighted words. Hence

$$
W=3s,\quad Q(Y_s)=(-1,s,0,\ldots;4s),\quad
B_N=4s,\quad B_O=3s+1,\quad\Delta_N=s,\quad\Delta_O=1.
$$

On the whole hull, using $b_1\ge b_2$ and the preceding capacity bound,

$$
\begin{aligned}
F_{Q(Y_s)}&=1-b_1+s b_2-s-4se\\
 &\le1-s+(s-1)b_2-4se\\
 &\le\frac{1-s}{2}-(2s+2)e\le\frac{1-s}{2}.
\end{aligned}
$$

Equality at $u_3$ proves $\sigma_H(Q(Y_s))=(1-s)/2$.
Every interior mask fixes the score. Thus for $s>1$ every normalized
convex-mask output has cost at least $s>1$, while $(0,0)$ succeeds.
At the closed value $s=1$, the sole resulting convex score $Y_1$ has
$J_{Q(Y_1)}(Y_1)=1$ and is a valid boundary certificate; the unrestricted
minimum remains zero. No strict failure is asserted at this endpoint.

The normalization restriction is essential. Zero belongs to the
arbitrarily scaled erasure cone and certifies each of these inputs.
Theorem 225.1 is therefore not an obstruction to arbitrary conic scaling.
The single-baseline $A/P$ zero-conflict criterion of 200.5 already
supplies membership for this family; the result concerns a constructor
boundary and adds no original membership region.

## 226. A pure-correct example with different restricted and unrestricted minima

**Theorem 226.1 (The specified pure-correct convex minimum).** For every
$L\ge4$, pad by ones the four zero words

$$
y:\quad C_{0111}=C_{1000}=C_{1101}=C_{1110}=1,\qquad A=P=T=0.
$$

Then $W_y=2$, $Q(y)=(1,1,1,1,0,\ldots;4)$,
$\Delta_N(y)=2$, $\Delta_O(y)=1$, and

$$
\min_{V\in\mathcal K_L(y)}J_{Q(y)}(V)=\frac{16}{15},\qquad
\min_{V\ge0}J_{Q(y)}(V)=\frac25.
$$

**Proof of the convex minimum.** The full table
$N(3,4;2,3,4,1)$ collects all four correct rewards.
A stopped table has at most three output labels and each rewarded label
has total one, so $B_O\le3$; $O(1,2;1,2,3)$ attains three.
Thus the two original excesses are as stated.

Masks above four act trivially. Aggregate the normalized weights on
$\varnothing,\{3\},\{4\},\{3,4\}$ as $a,b,c,d\ge0$ with
$a+b+c+d=1$. Their combined score is exactly

$$
\begin{gathered}
C_{0111}=1,\quad C_{1000}=a,\quad C_{1010}=b,\quad
C_{1001}=c,\quad C_{1011}=d,\\
C_{1101}=a+c,\qquad C_{1110}=a+b.
\end{gathered}
$$

It has $W=2$, $Q=(1,1,a+c,a+b,0,\ldots;2+2a+b+c)$.
For $x=b+d$, $z=c+d$, the residual is
$(0,0,x,z,0,\ldots;x+z)$. Its readings are zero at $o,p$,
$x/2$ at $u_3$, $3x/4$ at $v_3$, and

$$
\frac{x+z}{k-1},\qquad\frac{3(x+z)}{k+1}\quad(k\ge4).
$$

Since $x,z\ge0$, the exact residual support is
$\max\{3x/4,3(x+z)/5\}$.
The following three full tables belong to this example:

$$
E_1=N(1,2;0,1,2,4),\quad E_2=N(1,2;0,1,2,3),\quad
E_3=N(3,4;2,3,4,1).
$$

Their excesses on the same combined score are respectively
$a+b,a+c,2a-d$. Use weights $7/15,7/15,1/15$ on these support
bounds, and use just the $v_4$ residual reading. Then

$$
\begin{aligned}
J_{Q(y)}(V)&\ge\frac7{15}(a+b)+\frac7{15}(a+c)
 +\frac1{15}(2a-d)+\frac35(b+c+2d)\\
 &=\frac{16}{15}+\frac d{15}\ge\frac{16}{15}.
\end{aligned}
$$

At $a=b=c=1/3,d=0$, all-label full $N$ supports, in order
$\varnothing;1,2,3,4;12,13,14,23,24,34$, are

$$
(1;2,2,5/3,5/3;8/3,7/3,7/3,8/3,8/3,8/3).
$$

They follow from the seven literal combined rows above, so the full
excess is $2/3$. The residual support is $2/5$, giving equality.
Constant-one padding folds extra queries to short low schedules, as in
223.1, and the displayed decreasing residual formulas evaluate every
added hull vertex. Hence this is the complete minimum for every $L$.

**Proof of the unrestricted minimum.** The readings of $Q(y)$ at
$o,p,u_3,v_3,u_4,v_4$ are

$$
-2,\quad-1,\quad-1/2,\quad1/4,\quad-2/3,\quad2/5.
$$

For $k\ge4$ they are $4/(k-1)-2$ and $12/(k+1)-2$.
Therefore $V=0$, $\theta=2/5$ attains an unrestricted objective $2/5$.
For a matching lower bound use the same point

$$
v_4=(1,1,1,1,2/5,\ldots,2/5;2/5)
$$

and the following actual mass-one allocation. Each row has weight $1/10$;
the full $N$ column is its completion on the same two queries.

| Triple | Stopped table | Full table outputs on $00,01,10,11$ |
| --- | --- | --- |
| $123$ | $O(1,2;1,2,3)$ | $(1,1,2,3)$ |
| $124$ | $O(1,2;1,2,4)$ | $(1,1,2,4)$ |
| $12\infty$ | $O(1,2;1,2,0)$ | $(1,1,2,0)$ |
| $134$ | $O(1,3;1,3,4)$ | $(1,1,3,4)$ |
| $13\infty$ | $O(1,3;1,3,0)$ | $(1,1,3,0)$ |
| $14\infty$ | $O(1,4;1,4,0)$ | $(1,1,4,0)$ |
| $234$ | $O(2,3;2,3,4)$ | $(2,2,3,4)$ |
| $23\infty$ | $O(2,3;2,3,0)$ | $(2,2,3,0)$ |
| $24\infty$ | $O(2,4;2,4,0)$ | $(2,2,4,0)$ |
| $34\infty$ | $O(3,4;3,4,0)$ | $(3,3,4,0)$ |

For every first-zero $n\le4$, correct probability is $3/5$, pair
probability is at least $3/5$, and base probability is nonnegative,
meeting demand $-2/5$. For every first zero $n>4$, all queried bits
are positive: base and pair probabilities are $3/5$, correct probability
is zero. The corresponding demands are $1/5,0,3/5$. The positive base
probability is $3/5$. This checks all 46 rows at $L=4$ and all
$3(2^L-1)+1$ rows at every padded length, independently of which
additional zeros occur. Thus this very allocation $\lambda$ satisfies
$G_N\lambda\ge h(v_4)$, with mass one and $v_4\in H_N$.

For every unrestricted full $V\ge0$ it gives
$F_{Q(V)}(v_4)\le\Delta_N(V)$. The one residual gives

$$
J_{Q(y)}(V)\ge\Delta_N(V)+F_{Q(y)-Q(V)}(v_4)
 \ge F_{Q(y)}(v_4)=2/5.
$$

Together with the zero score, this proves the unrestricted minimum.
The three detecting tables $E_1,E_2,E_3$ are not this full feasible
allocation: their $7/15,7/15,1/15$ mixture has correct-label-one mass
zero at $0000$ and base mass zero at $1111$, both below $3/5$.
A detector and a full feasible $\lambda$ cannot be interchanged.
The genuine feasible point has $F_{Q(y)}(v_4)=2/5\le1$, so it supplies
no strict original separation. $\square$

**Remark 226.2 (Representative and constructor scope).** The four correct
atoms $0101,1011,1100,1110$ define a different score with its own
detectors and support vector. The constant $16/15$ does not identify
its data with those of Theorem 226.1. The theorem here concerns only
$0111,1000,1101,1110$ and the literal tables in its proof. Its pure-correct
membership is already covered by 198.4 and 200.4. The conic obstruction
of 223, the convex robustness of 225, this quantitative convex example
and the supplement below concern one constructor-boundary subject;
they are not additional original membership regions.

## 227. A six-coordinate quantitative supplement on the same constructor boundary

**Example 227.1 (Complete six-coordinate score and supports).** At $L=6$
define the full score $Y$ by the following nonzero rows, with $T=9$.

| Word | $A$ | $C$ | $P$ |
| --- | --- | --- | --- |
| $000001$ | $0$ | $0$ | $3$ |
| $001100$ | $0$ | $0$ | $2$ |
| $010100$ | $0$ | $0$ | $8$ |
| $011101$ | $0$ | $5$ | $0$ |
| $100000$ | $0$ | $0$ | $6$ |
| $100100$ | $0$ | $0$ | $5$ |
| $100111$ | $0$ | $0$ | $2$ |
| $110000$ | $0$ | $4$ | $0$ |
| $110010$ | $0$ | $6$ | $0$ |
| $110101$ | $0$ | $6$ | $0$ |
| $111010$ | $8$ | $0$ | $0$ |
| $111011$ | $0$ | $9$ | $0$ |
| $111100$ | $0$ | $3$ | $0$ |
| $111101$ | $0$ | $5$ | $0$ |
| $111110$ | $0$ | $11$ | $0$ |

It has $W_Y=48$, $Q(Y)=(5,0,16,1,8,11;92)$.
All 22 schedule supports, including every legal label, are as follows.
The last column also records the sharp convex-mask score $Z_*$ defined
in 227.2, whose anchor is the same 48.

| Schedule | $B_N^S(Y)$ | $B_O^S(Y)$ | $B_N^S(Z_*)$ |
| --- | --- | --- | --- |
| $\varnothing$ | $43$ | $43$ | $43$ |
| $1$ | $48$ | $48$ | $48$ |
| $2$ | $43$ | $43$ | $43$ |
| $3$ | $43$ | $43$ | $43$ |
| $4$ | $43$ | $43$ | $43$ |
| $5$ | $43$ | $43$ | $43$ |
| $6$ | $43$ | $43$ | $43$ |
| $12$ | $48$ | $48$ | $48$ |
| $13$ | $51$ | $51$ | $1119/22$ |
| $14$ | $48$ | $48$ | $48$ |
| $15$ | $48$ | $48$ | $48$ |
| $16$ | $48$ | $48$ | $48$ |
| $23$ | $51$ | $51$ | $557/11$ |
| $24$ | $45$ | $45$ | $4406/99$ |
| $25$ | $48$ | $48$ | $6301/132$ |
| $26$ | $43$ | $43$ | $43$ |
| $34$ | $45$ | $44$ | $4406/99$ |
| $35$ | $53$ | $49$ | $1119/22$ |
| $36$ | $45$ | $44$ | $395/9$ |
| $45$ | $44$ | $43$ | $17299/396$ |
| $46$ | $49$ | $43$ | $1613/33$ |
| $56$ | $51$ | $46$ | $3299/66$ |

Thus $\Delta_N(Y)=5$, $\Delta_O(Y)=3$. At
$o,p,u_3,v_3,u_4,v_4,u_5,v_5,u_6,v_6$, its signed hull readings are

$$
(-5,0,11/2,-2,7/3,-61/5,5/2,-31/2,16/5,-116/7).
$$

These support entries follow directly by summing the displayed
$A,C,P,T$ rewards in each complete cell and taking the maximum over
$0,\ldots,6$. In particular they do not combine independently chosen
input representations or remove zero-score words.

**Proposition 227.2 (Sharp sixteen-mask value).** For this $Y$,

$$
\min_{Z\in\mathcal K_6(Y)}J_{Q(Y)}(Z)=\frac{667}{198}.
$$

Consequently $y=Y/3$ is unit-$O$ but its normalized convex interior-mask
minimum is $667/594=1+73/594$.

**Proof.** Use one fixed full-table law on
$D_a=N(3,5;0,3,5,0)$ and $D_b=N(1,3;0,1,3,0)$, with weights
$\nu_a=73/396$, $\nu_b=323/396$. Use one fixed hull law on
$v_3,v_5,v_6$, with weights

$$
\mu_3=\frac{239}{4752},\qquad\mu_5=\frac{43}{396},\qquad
\mu_6=\frac{3997}{4752}.
$$

Both sets of weights sum to one. For each mask put $V_E=T_EY$,
$g_D(E)=V_E\cdot(z_D-r)$, $f_k(E)=F_{Q(Y)-Q(V_E)}(v_k)$ and

$$
\mathcal L(E)=\nu_ag_{D_a}(E)+\nu_bg_{D_b}(E)
 +\mu_3f_3(E)+\mu_5f_5(E)+\mu_6f_6(E).
$$

The full 16-mask data, all with $W_{V_E}=48$, are

| $E$ | $(g_{D_a},g_{D_b})$ | $(f_3,f_5,f_6)$ | $\mathcal L(E)$ | $\Delta_N(V_E)$ | $\sigma_H(Q(Y)-Q(V_E))$ |
| --- | --- | --- | --- | --- | --- |
| $\varnothing$ | $(5,3)$ | $(0,0,0)$ | $667/198$ | $5$ | $0$ |
| $3$ | $(-21,0)$ | $(12,8,48/7)$ | $667/198$ | $3$ | $12$ |
| $4$ | $(5,3)$ | $(0,1/2,27/7)$ | $10561/1584$ | $5$ | $27/7$ |
| $5$ | $(-13,3)$ | $(0,4,24/7)$ | $667/198$ | $3$ | $4$ |
| $6$ | $(5,3)$ | $(0,0,33/7)$ | $11617/1584$ | $5$ | $33/7$ |
| $34$ | $(-21,0)$ | $(12,17/2,75/7)$ | $10561/1584$ | $3$ | $12$ |
| $35$ | $(-5,0)$ | $(12,12,72/7)$ | $106/11$ | $1$ | $12$ |
| $36$ | $(-21,0)$ | $(12,8,81/7)$ | $11617/1584$ | $0$ | $12$ |
| $45$ | $(-13,3)$ | $(0,9/2,51/7)$ | $10561/1584$ | $3$ | $51/7$ |
| $46$ | $(5,3)$ | $(-2,-7/2,4/7)$ | $667/198$ | $5$ | $12/5$ |
| $56$ | $(-13,3)$ | $(0,4,57/7)$ | $11617/1584$ | $3$ | $57/7$ |
| $345$ | $(-5,0)$ | $(12,25/2,99/7)$ | $20489/1584$ | $0$ | $99/7$ |
| $346$ | $(-21,0)$ | $(10,9/2,52/7)$ | $667/198$ | $0$ | $10$ |
| $356$ | $(-5,0)$ | $(12,12,15)$ | $21545/1584$ | $0$ | $15$ |
| $456$ | $(-13,3)$ | $(-2,1/2,4)$ | $667/198$ | $3$ | $4$ |
| $3456$ | $(-5,0)$ | $(10,17/2,76/7)$ | $106/11$ | $0$ | $76/7$ |

A digit string in the mask column denotes that subset of addresses.
Each $g$ is the reward of its displayed full table minus 48; each $f$
is substitution in the displayed hull vertex. Thus all entries are
finite rational linear evaluations on the literal rows of 227.1.
They retain negative readings and are all at least $667/198$ in the
$\mathcal L$ column.

For any one convex combination $Z=\sum_Et_EV_E$, full support is
at least the $\nu$-average table excess on that same $Z$.
Its one residual charge is at least the $\mu$-average residual reading.
Since $\sum t_E=1$, linearity gives

$$
J_{Q(Y)}(Z)\ge\sum_Et_E\mathcal L(E)\ge667/198.
$$

This lower bound uses neither a sum of mask costs nor a separately
chosen residual for each component.

For matching attainment take the one score

$$
Z_*=\frac{119}{132}Y+\frac1{22}T_{\{3\}}Y
 +\frac{13}{396}T_{\{5\}}Y+\frac2{99}T_{\{4,5,6\}}Y.
$$

Its nonnegative coefficients sum to one. Its complete literal rows are
as follows; the terminal coefficient is $907/99$.

| Word | Type | Coefficient |
| --- | --- | --- |
| $000001$ | $P$ | $119/44$ |
| $000011$ | $P$ | $13/132$ |
| $000111$ | $P$ | $2/33$ |
| $001001$ | $P$ | $3/22$ |
| $001100$ | $P$ | $125/66$ |
| $001110$ | $P$ | $13/198$ |
| $001111$ | $P$ | $4/99$ |
| $010100$ | $P$ | $238/33$ |
| $010110$ | $P$ | $26/99$ |
| $010111$ | $P$ | $16/99$ |
| $011100$ | $P$ | $4/11$ |
| $011101$ | $C$ | $625/132$ |
| $011111$ | $C$ | $35/132$ |
| $100000$ | $P$ | $119/22$ |
| $100010$ | $P$ | $13/66$ |
| $100100$ | $P$ | $595/132$ |
| $100110$ | $P$ | $65/396$ |
| $100111$ | $P$ | $211/99$ |
| $101000$ | $P$ | $3/11$ |
| $101100$ | $P$ | $5/22$ |
| $101111$ | $P$ | $1/11$ |
| $110000$ | $C$ | $119/33$ |
| $110010$ | $C$ | $568/99$ |
| $110101$ | $C$ | $119/22$ |
| $110111$ | $C$ | $103/198$ |
| $111010$ | $A$ | $776/99$ |
| $111011$ | $C$ | $97/11$ |
| $111100$ | $C$ | $125/44$ |
| $111101$ | $C$ | $625/132$ |
| $111110$ | $C$ | $97/9$ |

It has $Q(Z_*)=(5,0,168/11,97/99,250/33,97/9;814/9)$.
The complete support column in 227.1 gives
$B_N(Z_*)=1119/22$, hence $\Delta_N(Z_*)=63/22$.
In the ten-vertex order of 227.1 its residual readings are

$$
(0,0,4/11,50/99,74/297,38/99,29/99,50/99,46/165,50/99).
$$

Thus the one residual charge is $50/99$, and their sum is $667/198$.
Homogeneity of the constructor and of the objective gives the asserted
unit value. $\square$

**Example 227.3 (Reused zero core and the same-point full allocation).**
The score $V_0=(5/2)U_3+(7/2)U_4$ from the zero-cost generators of
216.3, with $m=6,r=3$, has exactly these rows:

$$
\begin{gathered}
C_{110111}=11,\quad C_{111110}=5,\quad
P_{010110}=5/2,\quad P_{010111}=17/2,\quad P_{100111}=11,\\
P_{111010}=P_{111100}=5/2,\qquad T=6.
\end{gathered}
$$

The generator theorem applies at these parameters; its two coefficients
are nonnegative. Directly every one of its 22 full schedule supports
is 33, its anchor is 33, and
$Q(V_0)=(0,0,11,0,0,5;49)$. The residual against $Y$ is
$(5,0,5,1,8,6;43)$ with readings

$$
(-5,0,0,-2,-4/3,-28/5,-1/4,-9/2,0,-32/7).
$$

All are nonpositive, so $(V_0/3,0)$ certifies $Y/3$ unrestrictedly.
Indeed $(tV_0,0)$ certifies $Q(tY)$ for every $t\ge0$.
This application reuses the zero core and its scaled ray, rather than
asserting a new zero-stock result.

The same hull barycenter used by the lower functional is

$$
\bar b=\mu_3v_3+\mu_5v_5+\mu_6v_6
 =(1,1,1,6097/6336,6097/6336,523/576;3469/6336).
$$

A complete normalized allocation there is
$\mu_3P_{3,2}+\mu_5P_{5,2}+\mu_6P_{6,2}$, where $P_{k,2}$ is the
uniform triple law. To specify all 59 entries without suppressing
repeated tables, the following lists give every triple and its individual
mass. Each triple $i<j<r$ means $O(i,j;i,j,r)$, with $r=\infty$
interpreted as output zero; its full completion is $N(i,j;i,i,j,r)$.

| Component | All triples in that component | Mass of each entry |
| --- | --- | --- |
| $k=3$ | $123,12\infty,13\infty,23\infty$ | $239/19008$ |
| $k=5$ | $123,124,125,12\infty,134,135,13\infty,145,14\infty,15\infty,234,235,23\infty,245,24\infty,25\infty,345,34\infty,35\infty,45\infty$ | $43/7920$ |
| $k=6$ | $123,124,125,126,12\infty,134,135,136,13\infty,145,146,14\infty,156,15\infty,16\infty,234,235,236,23\infty,245,246,24\infty,256,25\infty,26\infty,345,346,34\infty,356,35\infty,36\infty,456,45\infty,46\infty,56\infty$ | $3997/166320$ |

For each component and every first zero $n\le k$, correct probability
is $1-e_k$, pair probability is at least $1-e_k$, and base probability
is at least the literal demand $-e_k$. For $n>k$, base and pair are
$1-e_k$ and correct is zero, meeting demands $1-2e_k,0,1-e_k$.
The positive base is $1-e_k$. These statements follow from triple
inclusion on every word, not just sole-zero words. The affine demand
vector therefore obeys

$$
z_{\mu_3P_{3,2}+\mu_5P_{5,2}+\mu_6P_{6,2}}
 \ge\mu_3d(v_3)+\mu_5d(v_5)+\mu_6d(v_6)=d(\bar b).
$$

This proves all 190 independent rows for that same $\bar b$, and its
same-seed full completion gives a complete mass-one $N$ allocation.
Its positive base is $2867/6336$. In contrast, the two-table lower
functional emits label one with probability zero at $000000$, below
the required $2867/6336$. Its mass one does not make it feasible.
Moreover $F_{Q(Y)}(\bar b)=-283/18$, or $-283/54$ for $Y/3$,
so the actual feasible point gives no strict separation.

At this same point the sum of least correct deficits for a whole-block
exhaustion-zero endpoint replacement is

$$
\sum_{n=1}^6(\bar b_n-\bar e)=2+\bar e=16141/6336>2.
$$

Every unit-mass queried-endpoint-only rule can supply total correct
sole-zero degree at most two. The full law just displayed is feasible
because unqueried numerical exhaustion labels remain legal. This is a
boundary of that constructor, not a restriction on the original problem.
For the original companion take $a_n=\bar b_n$ for $n\le6$ and
$a_{6+j}=\bar e2^{1-j}$ for $j\ge1$. The strict active length is six;
all amplitudes are positive and nonincreasing with vanishing tail,
$a_7=\bar e$, and every actual tail error is exactly $\bar e$.

## 228. Original-source correspondence and the remaining universal boundary

**Definition 228.1 (Actual sources and two distinct target families).** The
countable labeled source, with $p_i$ the $i$th prime, is

$$
\begin{gathered}
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N_x=1+F_rg,\quad q_i(x)=\mathbf1_{p_i\mid N_x},\quad
n(x)=\min\{i:q_i(x)=0\}.
\end{gathered}
$$

Replies are static; each actual integer has finitely many prime divisors,
so $n(x)$ is finite. There is no source prior or infinite positive source.
The full Borel carrier is
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with each block
a copy of $(0,1)$. The unchanged consumer returns unknown on $B_j$ and
proposes $j$ on $P_j$. Its original nonatomic target remains

$$
\begin{gathered}
t(x)=\sum_{i\ge1}3^{-i}q_i(x),\quad Z_t=\int_0^1e^{tu}\,du,\quad
\nu_x(du)=Z_{t(x)}^{-1}e^{t(x)u}\,du\text{ on }B_{n(x)},\\
\mu_x=(1-h_0)\nu_x+h_0\pi_{\omega(N_x)},\qquad0<h_0<1,
\end{gathered}
$$

where $\omega$ counts distinct prime divisors and $\pi_j$ is uniform on
$P_j$. On distinct original marks $\theta_j=(B_1,1/(j+2))$, $j\ge0$,
the separately selected targets, for every positive vanishing sequence, are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
 +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
$$

These laws do not replace $\mu_x$. Every finitely marked law has TV
distance one from $\mu_x$, since its finite support is a Borel null set
for the nonatomic target. Finite labels in 222–227 mean these actual marks.

**Proposition 228.2 (Finite patterns and lawful common execution).** Every
finite Boolean pattern at arbitrary finite prime addresses has an actual
source witness, fixed before the seed. A normalized common law on the
complete finite tables executes on those sources with zero advice, one
source-independent seed and at most two actual requests.

**Proof.** Boundaries 35.2 supplies arbitrarily large prime $r$ for which
$F_r$ is coprime to all specified primes. For a desired one impose
$g=-F_r^{-1}$ modulo that prime; for a desired zero impose $g=0$.
CRT supplies a residue modulo their product. Take $r$ with its Fibonacci
window longer than that product and choose the first representative at
or above its lower endpoint; it remains below the upper endpoint.
This realizes all words, including multiple zeros and positive prefixes
with a prescribed later zero, on the original labeled source.

Partition one source-independent $U\sim\mathrm{Unif}[0,1)$ into the
table masses. Its interval fixes the whole schedule and every output
before replies. N obtains the entire preselected schedule; O preselects
an increasing schedule and stops at its first queried zero or exhaustion.
On completion N actually obtains the reply that O would ignore.
Output the selected original mark and hand it to the unchanged consumer.
Handoff is finite for every source and seed. Repeated requests and ignored
replies count toward the hard bound of TWO ACTUAL requests. No adaptive
second address, extra probe, seed conditioning, address charge, depth or
runtime bound, expected-count budget or source distribution is introduced.
Original competitors retain arbitrary addresses and full-carrier outputs.
The error requirement remains uniform over all actual sources and all
Borel events. Nonnegative scores and conic multipliers are not themselves
acquisition probabilities. $\square$

The legal earlier output is indispensable: on $0100$ the table
$N(3,4;1,0,0,0)$ emits the correct unqueried label one. The actual source
$r=19,g=436,N_x=1822917$ has this low word. Its base, correct and pair
readings are $(0,1,1)$; replacing that output by zero gives $(1,0,1)$.
The plateau restriction on earlier exhaustion guesses in 224.2 therefore
does not authorize their deletion from the general catalog.

**Proposition 228.3 (Independent rows and closed tails).** For any output
law $p$ and a first-zero-$n$ target, its TV distance is

$$
\max\{1-a_n-p(0),\ a_n-p(n),\ 1-p(0)-p(n)\}.
$$

Indeed its overlap with the two-point target is
$\min(p(0),1-a_n)+\min(p(n),a_n)$, whose complement is the displayed
maximum. Thus the three independent rows of 222.2 are necessary and
sufficient, on every word and label, including negative singleton demands.
For example $a_n=1/2$, $\varepsilon=1/4$, $p(0)=p(n)=1/4$ passes both
singleton rows but has TV $1/2$; another legal label carries the remainder.
The positive row is also retained, even at zero score weight.

If an actual output law $p_x$ uses only marks $0,\ldots,H$ and $n(x)>H$,
the exact identity is

$$
\operatorname{TV}(p_x,\lambda_x^a)=\max\{1-p_x(0),a_{n(x)}\}.
$$

Half the absolute discrepancies is
$\tfrac12(|a_{n(x)}-(1-p_x(0))|+1-p_x(0)+a_{n(x)})$.
Replacing $p_x$ by a single positive-word law $p_{1^H}$ additionally
requires all observed addresses to be at most $H$ and the output to
depend only on the common seed and acquired replies. The constructed
finite tables have these properties; they are not assumed of arbitrary
competitors. For $\varepsilon>0$ the strict active length is
$L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$. Actual tails stay positive,
vanish, and include ties $a_n=\varepsilon$. At the feasible point of 226
one may take $a_1=\cdots=a_4=1$ and
$a_{4+j}=(2/5)2^{1-j}$, cap $2/5$, giving $L_a=4$ and exact tail error
$2/5$. Padding a hull point by $b_n=e$ does not make those padded
coordinates strictly active. The original small lengths $0,1,2$ are not
removed by the hypotheses $L\ge3$ or $L\ge4$ of the constructor results.

**Remark 228.4 (Conditional transport and reused mathematics).** The
arbitrary-address, full-carrier feasibility equivalences are those of
110.2. Their necessity uses measurable projection fixing the low marks,
countability of $X$ for one common conull finite-handoff/hard-count event,
and the vanishing probability tail of the maximum address of the SAME
whole preselected schedule. Actual finite-pattern witnesses precede seeds.
For each finite witness family choose its finite execution cutoff; this
is not a uniform runtime bound over $X$. The whole-execution comparison
has error at most $\gamma_m+1/m$, where $\gamma_m$ is that schedule-tail
probability. Class-preserving low tables lie in one finite catalog simplex;
compactness and continuity retain every non-strict row at the exact
closed cap. Necessity transports feasibility, not every original law.
Sufficiency executes actual low queries and uses 228.3 on actual tails.

The exact-law criterion 109.1 concerns a normalized degree-two
probability-vector kernel $p_\xi=c+\sum_i\ell_i\xi_i+
\sum_{i<j}Q_{ij}\xi_i\xi_j$: $c\ge H_{\rm ker}$ coordinatewise,
with its one common schedule-mass bound. Normalization makes that bound
follow from the vector inequality, as in 108.4. Its $Q_{ij}$ and
$H_{\rm ker}$ are not the signed score quotient $Q(V)$ or hull $H_L$.
Failure of exact-law realization for one kernel does not exclude a
different feasible kernel at the same cap.

| Reused result | Role in the present statements |
| --- | --- |
| 198.4–198.5 | Pure-correct membership, the closed hull and its complete support formula |
| 199.3–199.4 and 207.3 | One-budget full-score alternative and weak duality |
| 200.4–200.5 | Plateau and zero-conflict membership for the relevant examples |
| 204.4–204.5 and 214.5 | The zero-cost and exact-$Q$ escapes in 223.2 |
| 216.3 | The zero core and scaled ray used in 227.3 |
| 87.1 and 176.1 | Plateau existence and complete triple realization |
| 109.1 and 110.2 | Normalized exact-law criterion and closed-cap feasibility transport |

Finite linear programming, convex support and Farkas alternatives are
used in their classical senses. None of these reused results is a new
amplitude family or original membership region. The distinct conic,
convex and quantitative variants 223, 225–227 form one constructor-boundary
subject; 224 adds the normalized full-$O$ face necessity, leaving $N00$
unclassified. No full $N$ face, conic-mass or arbitrary full-carrier
necessity classification follows.

**Remark 228.5 (Numerical corrections without an additional theorem).** For
$q=(0,0,-3,3,1/2;0)$, the readings at
$o,p,u_3,v_3,u_4,v_4,u_5,v_5$ are
$0,0,-3/2,-17/8,0,1/5,1/8,1/2$; in particular the $u_3$ value is
$-3/2$. The selected-mask $19/20$ comparison concerns $Y/10$, where
$A_{10000}=5,P_{10000}=7,A_{11000}=6,C_{01100}=6,P_{11100}=1,
C_{11110}=5,A_{01101}=4,P_{01111}=3$. This existing example has
$W_Y=23$, $Q(Y)=(2,-5,-6,0,5;37)$ and $B_N=B_O=33$.
Its sharp unrestricted and single-$T_{\{3,4,5\}}$ objectives are both
$1/2$ after scaling by ten. These are corrections to that comparison;
they assert no further erasure-family theorem.

**Open boundary 228.6 (Original universal question).** The positive route
still requires, for EVERY actual full $y\ge0$ with $\Delta_O(y)\le1$,
ONE unrestricted full $V\ge0$ and ONE jointly paid signed residual
$\theta\in[0,1]$ with $\Delta_N(V)+\theta\le1$ and
$\sigma_H(Q(y)-Q(V))\le\theta$, together with the original positive
vanishing sequences, positive closed caps and source/resource correspondence.
The negative route still requires the SAME actual $b\in H_N$, one
complete full feasible $\lambda$ of mass $M\ge1$ at that point, and an
actual unit-$O$ score $y$ with the STRICT inequality $F_{Q(y)}(b)>M$,
plus an original common-seed $N_2$ attainer and a uniform lower bound
against EVERY arbitrary-address, full-carrier $O_2$ competitor.
Both routes remain open. Constructor failure, a detector-only hull point,
exact-law failure or finite checking does not establish original separation.

## 追加锚（本行以下为增补区）
