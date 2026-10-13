# Self-calibrating acquisition resources: radial directions and one common budget

## 164. Complete deterministic catalogs and event demands

**Definition 164.1 (Original and finite domains).** Retain the actual
countable labeled source, static prime answers, full measurable carrier,
unchanged consumer and nonatomic targets of
[Definition 154.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_III.md#154-the-actual-comparison-and-its-complete-six-coordinate-models).
In particular $n(\xi)$ is the actual first absent prime, the distinct
original marks are $\theta_j=(B_1,1/(j+2))$, and for an entire positive
nonincreasing vanishing sequence the separately declared targets are

$$
\lambda_\xi^a=(1-a_{n(\xi)})\delta_{\theta_0}
                 +a_{n(\xi)}\delta_{\theta_{n(\xi)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\longrightarrow0.
\tag{164.1}
$$

The classes are exactly Acquisition Resources, Definition 90.1, with
zero advice, one source-independent seed, actual almost-sure finite
handoff and at most two actual requests including repetitions. $N$
preselects its schedule and obtains its replies; $O$ uses an increasing
preselected schedule and stops at its first queried zero or exhaustion.
Original competitors retain arbitrary addresses and full-carrier outputs.
All errors are uniform suprema over the actual source set, without a
source distribution. The results here concern the selected marked laws,
not a change of any original nonatomic target.

Fix an arbitrary integer $L\ge3$. Put $B_L=\{0,1\}^L$,
$J_L=\{0,\ldots,L\}$, $m=3(2^L-1)+1$, and
$x=(a_1,\ldots,a_L,e)$. For every zero-containing word $w$ with first
zero $n$, include the three distinct event rows

$$
(w,\{0\}),\quad(w,\{n\}),\quad(w,\{0,n\}),
\qquad
1-a_n-e,\quad a_n-e,\quad1-e
\tag{164.2}
$$

as their demands. For $1^L$ include $(1^L,\{0\})$ with demand $1-e$.
Let $d(x)\in\mathbb R^m$ be this affine demand vector. Words are ordered
lexicographically and their rows as in (164.2). Negative singleton
demands remain in the system. The finite all-positive word is a target
bookkeeping device for actual tails, not an infinite all-positive source.

For a probability vector $p$, the two-point target has TV
$\max\{0,1-a_n-p(0),a_n-p(n),1-p(0)-p(n)\}$, as in Proposition 155.2.
Thus (164.2) retains exactly the complete TV constraint, including its
independent union row and every multiple-zero word.

**Definition 164.2 (Every complete table and its joint event vector).**
An $N$ table has one of the schedules $\varnothing$, $(i)$, $(i,j)$ with
$i<j$, and a label in $J_L$ for each of its respective cells
$\varnothing$, $0,1$, or $00,01,10,11$. An $O$ table has the same
schedules with pair cells $0,10,11$, merging $00,01$.
Every label is allowed in every cell; an output need not be queried.
Write $\mathcal D_N,\mathcal D_O$ for these entire finite catalogs,
retaining duplicate descriptions if they define the same output function.
Their numbers of descriptions are

$$
\begin{aligned}
|\mathcal D_N|&=(L+1)+L(L+1)^2+\binom L2(L+1)^4,\\
|\mathcal D_O|&=(L+1)+L(L+1)^2+\binom L2(L+1)^3.
\end{aligned}
\tag{164.3}
$$

Static reversal or repetition does not add an $N$ output function; its
canonical representative uses at most two requests. This represents laws
and does not assert preservation of mean count. For a table $D$, let
$z_D\in\{0,1\}^m$ indicate membership of its output in each row's event.
Let $Z_C$ have all these columns and define

$$
\Pi_C=\{x:\exists w_D\ge0,\ \sum_Dw_D=1,
                           \ Z_Cw\ge d(x)\},\qquad C=N,O.
\tag{164.4}
$$

The same weights mix whole tables in every row. By Proposition 140.3,
this is equivalent to complete terminal allocations with equal masses
in every schedule cell and one total schedule budget. Completing a
stopped table makes an $N$ table; ignored actual requests still count.
Thus $\Pi_O\subseteq\Pi_N$, and Theorem 109.1 identifies the stopped
kernels with $\mathscr C_L$. Theorem 110.2 transports these feasibility
sets at an original positive closed cap and its actual active length.
Its exact arbitrary-address and full-carrier necessity is reused here.

**Definition 164.3 (Exact unrestricted support).** For $y\ge0$, put
$B_C(y)=\max_{D\in\mathcal D_C}y\cdot z_D$. For a schedule $S$, its
acquired $N$ cell $c$ and a label $r$, put

$$
g_S^c(r)=\sum_{j:c_N(w_j,S)=c}y_j\mathbf1_{r\in E_j}.
$$

The exact $N$ support is the maximum, over all schedules, of
$\max_rg_\varnothing(r)$ for the empty schedule,
$\sum_{u=0,1}\max_rg_i^u(r)$ for a singleton, and
$\sum_{uv}\max_rg_{ij}^{uv}(r)$ for a pair. The exact $O$ pair value is

$$
\max_r\bigl[g_{ij}^{00}(r)+g_{ij}^{01}(r)\bigr]
       +\max_rg_{ij}^{10}(r)+\max_rg_{ij}^{11}(r).
\tag{164.5}
$$

Each maximum runs over every $r\in J_L$. The maximizing labels constitute
one complete deterministic table before answers, so these expressions
are whole-class supports, not independent per-word maxima.

## 165. A unique radial direction away from the first-two prefix

**Definition 165.1 (Closed necessary domain and distinguished prefix).**
Write $S=\sum_{i=3}^La_i$ and set

$$
\begin{aligned}
Q_L&=\{1\ge a_1\ge\cdots\ge a_L\ge e\ge0,
          \ (L+1)e\le S,\ a_1+S-(L+1)e\le1\},\\
\alpha&=(1,1,0,\ldots,0;0),\qquad H_L=Q_L\cap\{a_2=a_3\}.
\end{aligned}
\tag{165.1}
$$

The auxiliary boundary point $\alpha$ has a zero tail; it does not
replace (164.1). Let $R$ preselect $(1,2)$, output $1$ on its first-zero
cell, $2$ on its second-zero cell and $0$ on positive exhaustion. Put
$r=z_R$, $\Delta_C(y)=B_C(y)-y\cdot r$ and

$$
K_{R,L}=\{y\ge0:\Delta_N(y)=0\},\qquad
P_{R,L}=\{x\in Q_L:y\cdot(d(x)-r)\le0\text{ for every }y\in K_{R,L}\}.
\tag{165.2}
$$

**Theorem 165.2 (Radial normal form on the entire closed domain).**
$d(\alpha)=r$, and every $x\in Q_L\setminus\{\alpha\}$ has a unique
representation

$$
x=(1-t)\alpha+tb,\qquad b\in H_L,\quad0<t\le1.
\tag{165.3}
$$

The exact formulas are

$$
\begin{aligned}
t&=1-a_2+a_3,\quad b_1=1-\frac{1-a_1}{t},\quad
b_2=b_3=\frac{a_3}{t},\\
b_i&=\frac{a_i}{t}\ (4\le i\le L),\qquad e_b=\frac e t.
\end{aligned}
\tag{165.4}
$$

Conversely every $b\in H_L$ and $0<t\le1$ gives a point of $Q_L$ by
(165.3), with the stated value of $t$. At $t=0$ the point is $\alpha$;
no unique direction is assigned there. Also

$$
d(x)-r=t(d(b)-r),\qquad
x\in P_{R,L}\Longleftrightarrow b\in P_{R,L}\quad(t>0).
\tag{165.5}
$$

**Proof.** At first zero 1 or 2 the three demands of $\alpha$ are
$(0,1,1)$, and $R$ emits that mark. At a first zero $n\ge3$ they are
$(1,0,1)$, and $R$ emits zero because its first two bits are positive.
It emits zero at $1^L$, whose demand is one. Thus $d(\alpha)=r$ in
all $m$ coordinates. As an input kernel its only nonconstant terms are

$$
R_w=e_1+(-e_1+e_2)w_1+(e_0-e_2)w_1w_2.
\tag{165.6}
$$

It belongs to both complete catalogs, so $\Delta_C(y)\ge0$ for $y\ge0$.

Put $u=1-a_1$, $v=1-a_2$. The defining inequalities of $Q_L$ become

$$
0\le u\le v,\quad a_3\ge\cdots\ge a_L\ge e\ge0,\quad
v+a_3\le1,\quad0\le S-(L+1)e\le u.
\tag{165.7}
$$

All but $v+a_3\le1$ are homogeneous. The number $t=v+a_3$ is in
$[0,1]$. If it is zero then $v=a_3=0$; the ordering forces $u=0$ and
all later coordinates and cap zero, which is exactly $\alpha$.
Otherwise divide all homogeneous coordinates in (165.7) by $t$.
Now $v_b+b_3=1$, equivalent to $b_2=b_3$, so the resulting profile
is in $H_L$ and has precisely the coordinates (165.4). Conversely
multiply the homogeneous coordinates of any $b\in H_L$ by $t$;
then $v+a_3=t\le1$ and all inequalities hold. Applying $1-a_2+a_3$
to (165.3) recovers $t$, hence also $b$, proving uniqueness.
Affineness of $d$ gives (165.5). All arguments include zero caps,
zero late coordinates, plateaus and saturated endpoints. $\square$

## 166. The exact cost of a common conic allocation

**Definition 166.1 (One total conic mass).** For $C=N,O$, let $A_C$ have
columns $z_D-r$, $D\in\mathcal D_C$, and put $h(x)=d(x)-r$. Define

$$
\rho_C(x)=\inf\left\{\sum_D\lambda_D:
               \lambda\ge0,\ A_C\lambda\ge h(x)\right\},
\tag{166.1}
$$

with value $+\infty$ if the system is infeasible. The coefficients are
conic masses, not seed probabilities until their common sum is at most
one. There is one coefficient vector for all $m$ event rows. The $R$
column is zero and is included in both catalogs.

**Theorem 166.2 (Attainment, probability feasibility and all infinite
branches).** For every profile $x$, a finite $\rho_C(x)$ is an attained
minimum, and

$$
\begin{aligned}
x\in\Pi_C&\Longleftrightarrow\rho_C(x)\le1,\\
\rho_C(x)=0&\Longleftrightarrow h(x)\le0,\\
x\in P_{R,L}&\Longleftrightarrow x\in Q_L\text{ and }\rho_N(x)<\infty,\\
\rho_C(x)&=\sup\{y\cdot h(x):y\ge0,\ \Delta_C(y)\le1\}.
\end{aligned}
\tag{166.2}
$$

The last equality includes value $+\infty$. For $t>0$ in (165.3),

$$
\rho_C((1-t)\alpha+tb)=t\rho_C(b),\qquad \rho_N(x)\le\rho_O(x).
\tag{166.3}
$$

At $t=0$, $\rho_C(\alpha)=0$ is defined and proved separately; no
expression $0\cdot\infty$ is used.

**Proof.** If $\lambda^0$ is feasible with mass $s_0$, restrict the
feasible set to $\lambda\ge0$, $\sum\lambda\le s_0$. This is a closed
subset of a finite compact simplex, and the continuous mass objective
attains its minimum there. It is also the unrestricted infimum, since
larger masses cannot improve it. If the attained mass $s$ is at most
one, assign $D$ weight $\lambda_D$ and give $R$ the remaining mass
$1-s$. Its event vector is

$$
\sum_D\lambda_Dz_D+(1-s)r=r+A_C\lambda\ge d(x).
\tag{166.4}
$$

Conversely a probability table $w$ gives
$A_Cw=Z_Cw-r\ge h(x)$ with mass one. This proves the first equivalence,
including its closed endpoint. At mass zero all coefficients vanish,
so attainment gives the second equivalence.

Cone feasibility is
$h(x)\in\operatorname{cone}\{z_D-r\}-\mathbb R^m_{\ge0}$, a closed
finitely generated polyhedral cone. The finite-dimensional Farkas
alternative says this holds if and only if
$y\cdot h(x)\le0$ for every $y\ge0$ with $A_C^Ty\le0$.
Since the zero column is present,
$\max_Dy\cdot(z_D-r)=\Delta_C(y)\ge0$; thus that multiplier condition
is precisely $\Delta_C(y)=0$. Taking $C=N$ proves the third equivalence.
The use of the mature Farkas alternative here and below is the polyhedral
ingredient specified in Section 171, not a separate acquisition theorem.

For any feasible primal and dual pair,

$$
y\cdot h\le y\cdot A_C\lambda
      \le\Delta_C(y)\sum_D\lambda_D\le\sum_D\lambda_D,
\tag{166.5}
$$

which proves weak duality. If the cone system is infeasible, Farkas gives
$y\ge0$ with $\Delta_C(y)=0$ and $y\cdot h>0$. Every positive multiple
is dual feasible, so the dual supremum is $+\infty$, exactly as required.

For the feasible case let $\rho$ be the attained finite minimum and,
for $s\ge0$, define the closed convex set

$$
T_s=\{A_C\lambda-v:\lambda\ge0,\ \sum_D\lambda_D\le s,
                                                \ v\ge0\}.
\tag{166.6}
$$

It is the sum of a compact image and the negative orthant, hence closed.
Its support in direction $y\ge0$ is $s\Delta_C(y)$, because the zero
column permits unused mass. If a coordinate of $y$ is negative its
support is infinite. For $0\le s<\rho$, separation of $h$ from $T_s$
gives $y\ge0$ with $y\cdot h>s\Delta_C(y)$.
Cone feasibility excludes $\Delta_C(y)=0$ with positive $y\cdot h$.
Therefore $\Delta_C(y)>0$; divide by it to obtain a feasible dual vector
of value greater than $s$. Let $s$ tend upward to $\rho$.
Together with weak duality this proves equality when $\rho>0$.
For $\rho=0$, weak duality and $y=0$ give equality directly.
No infeasible or zero case has been dropped.

For $t>0$, scale a feasible conic representation by $t$ and divide a
feasible scaled representation by $t$ for the converse. Equation (165.5)
gives exact homogeneity, including simultaneous infeasibility on both
positive scales. At $\alpha$, $h=0$ and $\lambda=0$ gives zero directly.
Every completed $O$ table has an $N$ column with the same event vector,
so any $O$ conic representation is an $N$ one with the same mass.
This proves $\rho_N\le\rho_O$, including extended values. $\square$

## 167. Exact radial intervals and the missing budget exchange

**Definition 167.1 (Endpoint convention).** For $q\in[0,+\infty]$ set

$$
\tau(q)=
\begin{cases}
1,&q=0,\\
\min\{1,1/q\},&0<q<\infty,\\
0,&q=\infty.
\end{cases}
\tag{167.1}
$$

No division by zero is made in this definition.

**Theorem 167.2 (Necessary and sufficient common-budget comparison).**
For every $b\in H_L$, the class $C$ is probability-feasible along its
radial segment exactly at

$$
\{t\in[0,1]:(1-t)\alpha+tb\in\Pi_C\}
                         =[0,\tau(\rho_C(b))].
\tag{167.2}
$$

In particular

$$
\Pi_N\cap Q_L\subseteq\Pi_O
\quad\Longleftrightarrow\quad
\rho_O(b)\le\max\{1,\rho_N(b)\}
\quad\text{for every }b\in H_L\text{ with }\rho_N(b)<\infty.
\tag{167.3}
$$

Equivalently, for every such $b$ and every complete $N$ conic allocation
of $h(b)$ of finite mass $s$, there must be a complete $O$ conic
allocation dominating $h(b)$ of mass at most $\max\{1,s\}$.

**Proof.** At positive $t$, Theorem 166.2 gives feasibility exactly when
$t\rho_C(b)\le1$ if the value is finite. If it is zero every positive
$t\le1$ is feasible; if it is infinite none is. The point at zero is
$\alpha$ and is feasible separately. When the value is finite and
positive, the endpoint is included because the conic minimum is attained.
This proves (167.2) in all three branches.

Directions of infinite $\rho_N$ contribute only $\alpha$ and no condition.
For a finite $q_N\le1$, the largest $N$-feasible parameter is $t=1$;
containment therefore requires $\rho_O(b)\le1$.
For $q_N>1$ it is $t=1/q_N$, requiring $\rho_O(b)\le q_N$.
Conversely those requirements place the entire closed $N$ radial
interval inside the $O$ interval, proving (167.3). Since
$\rho_N\le\rho_O$, equality of the two costs is required whenever
$1\le\rho_N<\infty$; when $\rho_N<1$ the requirement is
$\rho_N\le\rho_O\le1$.

If the exchange statement holds, apply it to an attained $N$ minimum
to obtain (167.3). Conversely, for any feasible mass $s$, one has
$\rho_N\le s$; (167.3) and an attained $O$ minimum give the required
$O$ allocation of mass at most $\max\{1,s\}$. The exchange is a
statement about dominating the demands, not preserving the supplied
$N$ output laws. $\square$

**Proposition 167.3 (The stronger prefix-cone assertion).**

$$
P_{R,L}\subseteq\Pi_O
\quad\Longleftrightarrow\quad
\rho_O(b)\le1\quad
\text{for every }b\in H_L\text{ with }\rho_N(b)<\infty.
\tag{167.4}
$$

This is a stronger condition than (167.3). A finite hypothetical direction
with $\rho_N(b)=\rho_O(b)>1$ would violate (167.4), while the two
probability-feasible radial intervals would coincide. This distinguishes
the conditions without asserting existence of such a direction.

**Proof.** By cone feasibility and positive homogeneity, every finite
$\rho_N$ direction belongs to $P_{R,L}$ for all $0<t\le1$, including
$b$ itself. At $t=1$ it is $O$ feasible exactly when $\rho_O(b)\le1$.
That condition is also sufficient at every smaller parameter.
The displayed hypothetical costs give equal intervals
$[0,1/\rho_N(b)]$, despite failure at $b$. Thus finite cone feasibility
cannot be silently promoted to probability budget one. $\square$

## 168. Closed auxiliary boundaries and the original positive domain

**Theorem 168.1 (The closed radial criterion preserves the original
remaining obligation).** For a fixed $L\ge3$, failure of
$\Pi_N\cap Q_L\subseteq\Pi_O$ implies an original positive-cap profile
of actual active length $L$ with a complete $N_2$ attainer and no
original $O_2$ attainer, on the actual source and full carrier.
Conversely any original separator not already covered by the residual
construction belongs to $Q_L$. Consequently, when quantified over the
remaining lengths, (167.3) is equivalent to the remaining original
closed-cap comparison, including its auxiliary boundary points.

**Proof.** For an original active prefix, put
$D_3=S-(L-2)e$. The already proved Theorem 113.3 supplies an $O$ rule
when $D_3\le3e$, including equality. In the remaining case
$S>(L+1)e$, and the necessary Theorem 113.2 gives
$S-(L+1)e\le1-a_1$. These are the two additional inequalities of $Q_L$.
Lengths at most two are covered by the same residual supplier.

To handle a failure at a closed auxiliary point, the full finite $O$
probability projection is closed: for convergent feasible profiles take
a convergent subsequence of their weights in the finite catalog simplex
and pass all finitely many inequalities to the limit.
Put $c=1/2$ and take

$$
q=(c,\ldots,c;e_q),\qquad
 e_q=\frac{c(L-2)}{L+1}>0.
\tag{168.1}
$$

Then all amplitudes exceed $e_q$, $S=(L-2)c=(L+1)e_q$, and the head
bound holds with $a_1=c<1$. Thus $q\in Q_L$ and
$D_3(q,e_q)=3e_q$. It has a complete stopped probability allocation:
use mass $c$ of the supplied subset rule $P_{L,2}$ of Theorem 87.1 and
mass $1-c$ of immediate base emission. At every first zero its marked
mass is $3c/(L+1)=c-e_q$, its outside-pair mass is at most $e_q$,
and its base mass is at least $1-c$. These inequalities verify all
three rows; at the positive word its base deficit is exactly $e_q$.
This also follows from Theorem 113.3's residual synthesis, whose sole
nonzero subset-family weight at this profile is $c$.

If $x\in\Pi_N\cap Q_L\setminus\Pi_O$, put
$x_\delta=(1-\delta)x+\delta q$ and mix the whole $N$ allocations.
For $0<\delta<1$ this stays in $\Pi_N\cap Q_L$, has positive cap,
all $a_i>e$ and $a_1<1$. Closedness of $\Pi_O$ ensures that it remains
outside $\Pi_O$ for every sufficiently small positive $\delta$.
Append any positive nonincreasing vanishing tail below its cap.
The sufficient $N$ direction and necessary $O$ direction of the already
proved Theorem 110.2 give the original attainer and exclusion at that
same cap. Neither the actual source nor the tail is replaced in this
step. This uses existing exact transport and a closed-boundary bridge;
it supplies no particular failing point. $\square$

## 169. A conditional certificate against the full original stopped class

**Definition 169.1 (Common-budget separator data).** Choose a direction
$b\in H_L$ with $e_b>0$ and $b_L>e_b$. Supply complete $N$ conic
coefficients $\lambda\ge0$ with $A_N\lambda\ge h(b)$, write
$s=\sum_D\lambda_D$ and $M=\max\{1,s\}$, and supply a row vector
$y\ge0$ satisfying

$$
y\cdot h(b)>M\Delta_O(y).
\tag{169.1}
$$

Here $B_O$ and $\Delta_O$ are computed on the entire catalog by (164.5),
with every schedule, every terminal label and every row. These are
conditional certificate requirements; no instance is presumed.

**Theorem 169.2 (An attained small cap and uniform exclusion at a larger
closed cap).** If the data of Definition 169.1 exist, set

$$
x=\alpha+\frac{b-\alpha}{M},\quad e_x=\frac{e_b}{M},\quad
\gamma=\frac{y\cdot h(b)}M-\Delta_O(y)>0,\quad W=\sum_jy_j,
$$

and

$$
\eta=\frac12\min\{\gamma/W,a_L(x)-e_x\}>0.
\tag{169.2}
$$

There is one original $N_2$ rule of error at most $e_x$ on every allowed
positive nonincreasing vanishing tail with $a_{L+1}\le e_x$.
Every original full-carrier arbitrary-address $O_2$ competitor on the
same entire sequence has error strictly greater than $e_x+\eta$.
Writing $E_C(2;a)=\inf_{A\in\mathcal C_2}e_a(A)$, the precise conclusion is

$$
E_N(2;a)\le e_x<e_x+\eta\le E_O(2;a).
\tag{169.3}
$$

The final infimum inequality is non-strict at the larger cap.

**Proof.** Give $D$ probability $\lambda_D/M$ and give $R$ the remaining
probability $1-s/M$. These weights are nonnegative and sum to one.
Their joint event vector is

$$
r+\frac{A_N\lambda}{M}\ge r+\frac{h(b)}M=d(x).
$$

Thus one full probability allocation satisfies every cap row.
Its score at the demand vector is
$y\cdot d(x)=B_O(y)+\gamma$; every full $O$ probability allocation has
score at most $B_O(y)$. This is exclusion of the entire class, not merely
failure to preserve one $N$ law. Strictness implies $y\ne0$, hence $W>0$.
The radial normal form gives positive cap and
$a_L(x)-e_x=(b_L-e_b)/M>0$.

Realize the $N$ allocation on the actual original primes using one seed
and its whole table. All active words satisfy the three rows.
For an actual first absence $n>L$, the already supplied tail identity is
$\max\{1-p_{1^L}(0),a_n\}\le e_x$. Every allowed tail is therefore
retained; for example $a_{L+j}=e_x/j$, $j\ge1$, is one allowed choice.
Sourcewise handoff is finite, with at most two actual requests.

At the larger cap $e_x+\eta<a_L(x)\le1$, the active length remains
exactly $L$ on that same entire sequence. Every demand decreases by
$\eta$, and its scored gap is
$\gamma-W\eta\ge\gamma/2>0$. The necessary $O$ direction of Theorem
110.2 excludes all original $O$ rules at that larger closed cap, including
arbitrary addresses and arbitrary original tapes. Thus each such rule
has error $>e_x+\eta$, while the infimum of their errors is only known
to be $\ge e_x+\eta$. This proves (169.3); strict individual inequalities
do not warrant a strict inequality for their infimum. $\square$

**Proposition 169.3 (Exact relation to a radial budget failure).** At an
interior direction $b$ with finite $\rho_N(b)$, condition
$\rho_O(b)>\max\{1,\rho_N(b)\}$ yields data as in Definition 169.1.
Conversely any such data imply that condition.

**Proof.** Take an attained $N$ minimum and put
$M=\max\{1,\rho_N(b)\}$. By the dual supremum of Theorem 166.2, including
its infinite case, choose $y\ge0$ with $\Delta_O(y)\le1$ and
$y\cdot h(b)>M$. Then (169.1) holds.
Conversely if $\Delta_O(y)>0$, dividing (169.1) by it and using weak
duality gives $\rho_O(b)>M\ge\max\{1,\rho_N(b)\}$.
If $\Delta_O(y)=0$, the positive scored demand makes the $O$ cone
infeasible by Farkas, so $\rho_O(b)=\infty$ and the same conclusion
holds. This is a certificate specification, not an actual separator.
$\square$

## 170. Every original tail under the same radial law identity

**Theorem 170.1 (Whole-sequence normalization and exact error scaling).**
For any original sequence (164.1), put $t=1-a_2+a_3$ and normalize its
entire sequence by

$$
b_1=1-\frac{1-a_1}{t},\qquad b_2=\frac{a_3}{t},\qquad
b_i=\frac{a_i}{t}\quad(i\ge3).
\tag{170.1}
$$

Then $0<t\le1$, $1\ge b_1\ge b_2=b_3\ge b_4\ge\cdots>0$ and
$b_i\to0$. For each actual source, on the full original carrier,

$$
\lambda_\xi^a=(1-t)R_\xi+t\lambda_\xi^b.
\tag{170.2}
$$

Here $R_\xi$ is the original $(1,2)$ prefix rule's law. Every actual
amplitude, including every $i>L$, is normalized by the same $t$ and
retains its actual mark $\theta_i$ in (170.2).
Given an original $N_2$ or $O_2$ rule $A_b$ for the normalized sequence,
there is a rule in the same class, using one source-independent seed,
whose output law is $(1-t)R_\xi+t\widehat\lambda_{A_b,\xi}$ and whose
uniform error is exactly

$$
e_a(A_{\rm mix})=t e_b(A_b).
\tag{170.3}
$$

**Proof.** Since $a_2\ge a_3>0$, $0<t\le1$.
Moreover $b_1=(a_1-a_2+a_3)/t>0$, $b_1\le1$ and
$b_1-b_2=(a_1-a_2)/t\ge0$. All remaining inequalities and convergence
follow by division of the entire tail by the fixed positive $t$.
At a positive cap set $e_b=e/t$; then $b_i>e_b$ exactly when $a_i>e$,
so active length and every tail-cap comparison are preserved.

Check (170.2) separately at each possible actual first absence.
If $n=1$, $R_\xi=\delta_{\theta_1}$ and the coefficients at the actual
target atoms are

$$
t(1-b_1)=1-a_1,\qquad (1-t)+tb_1=a_1.
$$

If $n=2$, $R_\xi=\delta_{\theta_2}$ and

$$
t(1-b_2)=t-a_3=1-a_2,\qquad (1-t)+tb_2=1-t+a_3=a_2.
$$

If $n\ge3$, including every actual $n>L$, $R_\xi=\delta_{\theta_0}$ and

$$
(1-t)+t(1-b_n)=1-a_n,\qquad tb_n=a_n.
$$

These are full-carrier identities at $\theta_0,\theta_n$. The actual tail
atom is never relabeled as zero in this identity. Only the separate
finite transport uses the target $e_0$ for $1^L$.

Choose the $R$ branch with probability $1-t$ and the $A_b$ branch with
probability $t$, before any replies. Use one seed space consisting of
the branch and the inherited branch seed, as permitted by Definition
71.1; it is fixed source-independently. For interval realizations,
partition one $U\in[0,1)$ and rescale it within the chosen interval to
supply that branch's full local seed. More generally the disjoint union
of the two weighted seed spaces is itself a single seed space.
No sourcewise branch selection or extra observed random variable is used.
The prefix and both class branches preselect their entire schedules;
$O$ stops as required, while the $N$ prefix obtains both scheduled
replies. Each branch has the hard-two bound and sourcewise almost-sure
finite handoff. Null branches are omitted. Completing the stopped rule
in $N$ uses the same global seed and counts ignored requests.

Subtract (170.2) from the mixed output law to obtain
$\widehat\lambda_{{\rm mix},\xi}-\lambda_\xi^a
=t(\widehat\lambda_{A_b,\xi}-\lambda_\xi^b)$.
Homogeneity of signed-measure TV and then the all-source supremum prove
(170.3). For mark-supported finite rules at an actual $n>L$ the same
identity is consistent with the exact tail formula

$$
\max\{t(1-p_{1^L}(0)),a_n\}
           =t\max\{1-p_{1^L}(0),b_n\}.
\tag{170.4}
$$

Every actual tail remains positive and vanishing. The auxiliary point
$\alpha$ belongs only to the closed finite geometry; it is not invoked
as a positive entire target sequence. $\square$

## 171. Projected-polyhedron duality and the unresolved exchange

**Definition 171.1 (The attributed containment ingredient).** The mature
projected-polyhedron criterion used in the common-budget analysis is
[Kellner, *Containment problems for projections of polyhedra and
spectrahedra*, arXiv:1509.02735v1, Theorem 3.1](https://arxiv.org/abs/1509.02735v1).
For $\pi(P_A)=\{x:\exists u,\ a+Ax+A'u\ge0\}$ and
$\pi(P_B)=\{x:\exists v,\ b+Bx+B'v\ge0\}$, with $\pi(P_A)\ne\varnothing$,
the numbered theorem gives containment exactly when
$z^T(b+Bx)\ge0$ for all $x\in\pi(P_A)$ and $z\ge0$ satisfying
$B'^Tz=0$. When $\ker(B'^T)\cap\mathbb R_{\ge0}^k$ is nonzero, the
multipliers can instead be restricted to $\sum z=1$. Its Farkas proof
is a polyhedral statement and needs no spectrahedral Slater assumption.

For the outer $O$ projection use the inequalities

$$
A_O\lambda-h(x)\ge0,\qquad\lambda\ge0,\qquad1-\sum\lambda\ge0.
$$

The auxiliary-variable matrix is $B'=[A_O;I;-\mathbf1^T]$ and the
affine part is $[-h(x);0;1]$. An annihilating nonnegative multiplier
has the form $z=(y,v,k)$ with

$$
A_O^Ty+v-k\mathbf1=0,\quad y,v,k\ge0,
\quad\text{equivalently }k\ge\Delta_O(y),\quad
v=k\mathbf1-A_O^Ty.
\tag{171.1}
$$

Its value is $k-y\cdot h(x)$. Minimizing $k$ at fixed $y$ gives

$$
\Delta_O(y)-y\cdot h(x)=B_O(y)-y\cdot d(x),
\tag{171.2}
$$

exactly the full score inequality. The inner $N$ projection may include
$Q_L$; it is nonempty since $\alpha$ with $R$ is feasible.
The annihilator cone is nonzero: $y=0,v=\mathbf1,k=1$ is an element.
Thus the hypotheses of the numbered theorem, including its optional
simplex normalization, hold for this encoding. That multiplier simplex
is different from the normalization $\Delta_C(y)\le1$ in Theorem 166.2.
Deleting the probability-budget row yields instead the zero-$\Delta$
Farkas cone, explaining why finite conic feasibility omits the mass bound.
Only the numbered containment theorem and its stated hypotheses are
used as this intermediate ingredient.

The radial map, whole-sequence law identity and exact common-budget
comparison are repository-derived compositions with the reused
Theorems 109.1, 110.2, 113.2 and 113.3. They do not constitute a new
standalone LP-duality theorem, a spectrahedral relaxation of the actual
problem, or an exhaustive novelty or literary-priority assertion.

**Open problem 171.2 (All-length exchange at the exact probability
budget).** For every remaining $L\ge7$ and every $b\in H_L$ with finite
$\rho_N(b)$, establish

$$
\rho_O(b)\le\max\{1,\rho_N(b)\},
\tag{171.3}
$$

or provide an explicit failing direction and the complete certificate
of Definition 169.1, with the boundary bridge if necessary.
Equivalently establish the complete-table budget exchange of Theorem
167.2. The entire six-active comparison is supplied by
[Theorem 161.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_III.md#161-every-original-six-active-profile-and-every-actual-tail);
Theorem 162.2 additionally gives the stronger prefix-cone inclusion on
$Q_6$. Neither statement proves (171.3) for larger lengths.
The exact-law obstruction of Theorem 112.2 does not settle this cap
comparison, and failure of the stronger prefix condition (167.4) would
not by itself settle it. No actual full-class separator is given here.
The continuing universal obligation remains the original all-amplitude,
all-tail closed-cap intersection, not a weaker cone or law-preservation
problem.

## 追加锚（本行以下为增补区）
