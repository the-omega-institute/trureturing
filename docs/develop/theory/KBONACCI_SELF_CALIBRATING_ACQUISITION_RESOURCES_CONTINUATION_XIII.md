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
