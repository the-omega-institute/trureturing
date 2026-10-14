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
