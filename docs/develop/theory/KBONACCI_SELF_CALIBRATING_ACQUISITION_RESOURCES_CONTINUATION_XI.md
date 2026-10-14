# k-bonacci 自校准获取资源续卷 XI：共同证书的正规形与达到的全评分极值

This volume continues
[Continuation X, §§210–212](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_X.md).
It contains ordinary mathematical proofs, not Lean-kernel verification.
Write $x_+=\max(x,0)$; empty sums are zero and every displayed weak
inequality includes equality. Existing text is retained; further additions
belong below an append anchor.

## 213. Terminal normalization, coupled reward fibers and full-score minima

**Definition 213.1 (Complete scores and the inherited single budget).**
Fix an integer $L\ge3$. For $w\in\{0,1\}^L\setminus\{1^L\}$ let
$n(w)$ be its first zero and $\Omega_n=\{w:n(w)=n\}$.
All words and all labels $0,\ldots,L$ remain. A full score $V$ has
independent nonnegative coefficients $A_w,C_w,P_w$ and $T\ge0$, with

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
                 +P_w\mathbf1_{\ell\in\{0,n(w)\}},\qquad
g_V(1^L,\ell)=T\mathbf1_{\ell=0}.
$$

For each cell $E$, maximize $\sum_{w\in E}g_V(w,\ell)$ over every
label. Sum these maxima within a schedule and maximize over the complete
catalog. The catalog has empty and singleton schedules and every distinct
pair $i<j$; its pair cells are $00,01,10,11$ for $N$, and $0,10,11$
for $O$, where $0$ merges $00,01$. Write the resulting supports as
$B_N,B_O$, and their schedule versions as $B_N^{ij},B_O^{ij}$.
Four output entries denote full-cell order; three denote stopped-cell order.
The anchor $R=(1,2;1,2,0)$ belongs to both catalogs, with full completion
$(1,2;1,1,2,0)$. As in 212.1, put

$$
\begin{aligned}
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(V)&=B_{\mathcal C}(V)-W_V\ge0
                                      &&(\mathcal C=N,O),\\
Q(V)&=(\beta,K),\quad
\beta_n=\sum_{\Omega_n}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
$$

The independent event demands are $1-b_n-e,b_n-e,1-e$ at every
zero word and $1-e$ at the positive word. Negative singleton demands
are not truncated. Zero coefficients remove no constraints. A label
may precede both queried addresses and need not be queried: on $0100$,
the table $(3,4;1,0,0,0)$ has event readings $(0,1,1)$, whereas
changing its first output to zero gives $(1,0,1)$.

Use the existing hull and signed support of 198.5:

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\},\\
F_q(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,\quad
\alpha=(1,1,0,\ldots,0),\quad \sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
$$

Its vertices are $o=0$, $p=(1,0,\ldots,0;0)$ and, for $3\le k\le L$,

$$
u_k=(\underbrace{1/(k-1),\ldots,1/(k-1)}_k,0,\ldots,0;0),\qquad
v_k=(\underbrace{1,\ldots,1}_k,e_k,\ldots,e_k;e_k),\quad
e_k=\frac{k-2}{k+1}.
$$

A complete certificate for any signed $q\in\mathbb R^{L+1}$ consists of
one full $V\ge0$ and one $\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad \sigma_H(q-Q(V))\le\theta.
\tag{213.1}
$$

Its quotient set is $E_N$ of 199.2. At $\theta=1$ every nonzero
zero-cost score remains permitted. With $d$ the complete demand vector,
$r=z_R=d(\alpha,0)$, $h=d-r$ and $G_N=(z_D-r)_D$, write
$H_N=\{b\in H_L:\exists\lambda\ge0, G_N\lambda\ge h(b)\}$.
Theorem 199.3 and Corollary 199.4 supply the alternative and clipped
comparison; they are reused, not new assertions here. For the same full
feasible $\lambda$ of mass $M$, (213.1) gives
$F_q(b)\le M\Delta_N(V)+\theta\le\max(1,M)$.

All measures below are proof weights on an actual finite Boolean cube.
They are not source distributions or acquisition probabilities.
Unspecified coefficients vanish and coincident coefficients add.
Static reversals permute full cells and repetitions carry singleton
information. Every short $N$ function refines into a distinct-pair
$N$ function. These representation facts do not cancel actual requests
and do not invent a later address for a last-coordinate stopped singleton.

### 213.1 Full terminal normalization and exact threshold reserve

**Theorem 213.2 (Canonical least terminal minimizer).**
For every full nonnegative skeleton $V_0$ with $T=0$ and every signed
$q$, let $V_t=V_0+t e_T$ for $t\ge0$. Over the complete $N$ catalog put

$$
d_0=\max_{D(1^L)=0}V_0\cdot(z_D-r),\qquad
d_1=\max_{D(1^L)\ne0}V_0\cdot(z_D-r),\qquad
t_*=(d_1-d_0)_+,
$$

and $\chi_q(t)=\max(0,\sigma_H(q-Q(V_t)))$.
Both catalog subsets are nonempty, $d_0\ge0$, and

$$
\Delta_N(V_t)=\max(d_0,d_1-t),\qquad
\min_{t\ge0}\{\Delta_N(V_t)+\chi_q(t)\}=d_0+\chi_q(t_*).
\tag{213.2}
$$

The displayed $t_*$ is the least minimizer, not necessarily the unique
one. For $0\le s<t\le t_*$ the objective decreases by at least
$3(t-s)/(L+1)$; on $[t_*,\infty)$ it is nondecreasing.
Consequently $q\in E_N$ if and only if some full $T=0$ skeleton satisfies
$d_0+\chi_q(t_*)\le1$. This leaves every A/C/P coordinate free.

**Proof.** If $D(1^L)=0$, adding $t$ increases both its reward and the
anchor by $t$; otherwise only the anchor increases. The two maxima give
the first identity, and the anchor itself gives $d_0\ge0$.
The quotient changes by $(0,\ldots,0;t)$, hence every residual reading
increases by $te$. On $H_L$,

$$
0\le e\le\eta_L:=\frac{L-2}{L+1}<1,\qquad
0\le\chi_q(t)-\chi_q(s)\le\eta_L(t-s)\quad(s\le t).
$$

The first bound follows from $(L+1)e\le\sum_{j\ge3}b_j\le L-2$;
the second follows by maximizing affine readings and zero. No sign
condition on the residual was used. Below $t_*$ the cost decreases
with slope one, proving the strict quantitative decrease. Above it
the cost is constant and the residual is nondecreasing. This also
handles $d_1\le d_0$, when $t_*=0$.

An existing certificate $(V_t,\theta)$ has $\chi_q(t)\le\theta$.
Replacing it by $(V_{t_*},\chi_q(t_*))$ cannot increase the sum in
(213.1). Since $d_0\ge0$, its new residual charge belongs to $[0,1]$.
Conversely any skeleton satisfying the stated inequality is such a
certificate. Both terms use the same budget. No existence of a suitable
skeleton for every unit-$O$ input is inferred. $\square$

**Definition 213.3 (Threshold carrier and its cell reserves).**
Choose any nonempty $J\subseteq\{3,\ldots,L\}$, an actual measure
$\nu\ge0$ on $\{0,1\}^J$ of mass $S$, and arbitrary $\eta_n\ge0$
for $n\in J$. Put $\mu=\max_{n\in J}\eta_n$ and

$$
m_j=\nu\{x_j=0\},\qquad a_{nk}=\nu\{x_n=0,x_k=1\} (n<k),
\qquad a_{nn}=0.
$$

Use the constructor of 203.2 on these ordered selected coordinates:
lift each atom of $\nu$ equally to prefixes $01$ and $10$ as P rows;
set every unselected late bit to one. For each $n\in J$, push length
measure on $[0,\eta_n)$ to C words having all earlier bits one,
bit $n$ zero, and selected later bit $k$ one exactly when $r<a_{nk}$.
Set $T=t$ and $A=0$, with no early C. This is one finite score $V_t$:
interval endpoints give finitely many atoms, and threshold ties have
zero length. It has $W=S+t$ and
$Q=(0,0,\eta;\sum\eta+S+t)$, extending $\eta$ by zero outside $J$.

Every index in the following maxima belongs to $J$. For $j\in J$ set

$$
\begin{aligned}
u_j&=\max\bigl(0,\max_{n\le j}(\eta_n-a_{nj}-m_j/2)\bigr),\\
r_j&=\max\bigl(\{0\}\cup\{\min(\eta_n,a_{nj}):n<j\}
                         \cup\{\eta_n:n>j\}\bigr).
\end{aligned}
$$

For $i<j$ in $J$ write $p_{ab}=\nu\{x_i=a,x_j=b\}$ and set

$$
\begin{aligned}
x_{ij}&=\max\bigl(0,\max_{n\le i}
                   (\eta_n-\max(a_{ni},a_{nj})-p_{00})\bigr),\\
y_{ij}&=\max\bigl(0,\max_{i<n\le j}(\eta_n-a_{nj}-p_{10})\bigr),\\
r_{ij}&=\max\bigl(\{0\}\cup
 \{\min(\eta_n,a_{ni},a_{nj}):n<i\}\cup
 \{\min(\eta_n,a_{nj}):i<n<j\}\cup\{\eta_n:n>j\}\bigr),\\
\kappa&=\max\bigl(0,\max_j(\eta_j-m_j/2)_+,\
 \max_{i<j}[(\eta_i-m_i)_++(\eta_j-p_{10})_+]\bigr),\\
\tau&=\max\bigl(\{\mu\}\cup
 \{u_j+r_j-(S-m_j)/2:j\in J\}\cup
 \{x_{ij}+y_{ij}+r_{ij}-p_{11}:i<j\text{ in }J\}\bigr).
\end{aligned}
\tag{213.3}
$$

Absent indexed families are omitted. In particular one selected late
coordinate and zero masses are allowed. There is no monotonicity or
exchangeability assumption on $\eta$ or $\nu$.

**Theorem 213.4 (Exact all-terminal reserve of the threshold score).**
For all data in 213.3 and every $t\ge0$,

$$
\Delta_N(V_t)=\max(\kappa,\tau-t).
\tag{213.4}
$$

For $D\ge0$ there exists an affordable terminal $t\ge0$ precisely when
$D\ge\kappa$; its least value is $(\tau-D)_+$.
For every signed target $q$ the best total certificate charge among
all terminals on this skeleton is

$$
\kappa+\max(0,\sigma_H(q-Q(V_{(\tau-\kappa)_+}))).
\tag{213.5}
$$

In 213.2 this implies $d_0=\kappa$ and
$(d_1-d_0)_+=(\tau-\kappa)_+$. It does not generally imply $d_1=\tau$.
These minima fix this carrier and threshold placement; they are not
minima over every representative of its quotient.

**Proof.** On an early/late pair the early-zero cell maxima sum to
$S/2$. The $10$ maximum is $m_j/2+u_j$; the $11$ maximum is
$\max((S-m_j)/2+t,r_j)$. Its exact excess is therefore

$$
u_j+\bigl(r_j-(S-m_j)/2-t\bigr)_+.
\tag{213.6}
$$

On a selected late pair the four maxima are exactly

$$
p_{00}+x_{ij},\quad p_{01},\quad p_{10}+y_{ij},\quad
\max(p_{11}+t,r_{ij}).
\tag{213.7}
$$

Here an earlier class $n\le i$ has $01$ reward
$[\min(\eta_n,a_{nj})-\min(\eta_n,a_{ni})]_+\le p_{01}$:
the difference of the two actual threshold events is contained in
$\{x_i=0,x_j=1\}$. Earlier-class $10$ differences are similarly
at most $p_{10}$. The $00$ contribution for $n\le i$ is
$(\eta_n-\max(a_{ni},a_{nj}))_+$, and the $10$ contribution for
$i<n\le j$ is $(\eta_n-a_{nj})_+$. The $11$ contributions are
exactly the three families in $r_{ij}$. Early labels collect half
the baseline in late cells and cannot exceed label zero there.
Thus (213.7) retains, and bounds, every earlier unqueried label.

For clarity the joint non-$11$ estimate from 203.2 applies to these
parameters without a terminal hypothesis. Its single-cell estimates
give $u_j\le\kappa$, $x_{ij}\le\kappa$, $y_{ij}\le\kappa$.
If both late gains are positive, choose winning classes $n\le i<m\le j$
and put $h_n=\max(a_{ni},a_{nj})$. Then

$$
x_{ij}+y_{ij}=\eta_n+\eta_m-h_n-a_{mj}-m_j
 \le\eta_n+\eta_m-\nu(\{x_n=0\}\cup\{x_m=0\})\le\kappa.
$$

The first inequality uses that this union is contained in
$\{x_j=0\}\cup\{x_n=0,x_j=1\}\cup\{x_m=0,x_j=1\}$.
The last follows from the defining two positive parts of $\kappa$.
If one gain vanishes, the single-cell estimate applies. This is one
joint bound, not two copies of $\kappa$. Conversely $u_j$ includes
$(\eta_j-m_j/2)_+$, while $x_{ij}$ includes $(\eta_i-m_i)_+$
because $a_{ij}+p_{00}=m_i$, and $y_{ij}$ includes
$(\eta_j-p_{10})_+$. Hence
$\max(0,\max u_j,\max(x_{ij}+y_{ij}))=\kappa$.

The head pair has excess $(\mu-t)_+$. The excess from (213.7) is
$x_{ij}+y_{ij}+(r_{ij}-p_{11}-t)_+$.
Applying $c+(h-t)_+=\max(c,c+h-t)$ to these expressions gives
(213.4). A query at an unselected coordinate is constant on the entire
scored support and gives at most a shorter information type, representable
using selected coordinates and the head. Short schedules, reversals
and repetitions are thus included in the upper bound. Every schedule
used for equality is legal. The fixed-cost endpoint follows directly.

The large-$t$ limit in (213.2) gives $d_0=\kappa$; the value at zero
fixes the positive breakpoint. If $\tau>\kappa$, then $d_1=\tau$;
if $\tau\le\kappa$, only $d_1\le\kappa$ follows. Theorem 213.2
now gives (213.5), including its least-minimizer interpretation. $\square$

**Example 213.5 (A masked intercept and a nonunique minimum).**
At $L=5$ take

$$
P_{01101}=P_{01111}=P_{10101}=P_{10111}=1/4,\qquad
C_{11000}=C_{11110}=1/2,\qquad A=T=0.
$$

This is 213.3 with $J=\{3,4,5\}$, carrier mass $1/2$ each at
$101,111$, and profile $(1/2,0,1/2)$. It has $W=1$ and
$\Delta_N=\Delta_O=\kappa=d_0=1$, but $\tau=1/2$ and $d_1=3/4$.
To see the last value without identifying hidden affine intercepts,
force a nonzero label in each schedule's positive cell. On a late pair
its best positive-cell reward is $\max(r_{ij},p_{11}/2)$, since either
early label receives $p_{11}/2$; on an early/late pair the extra constant
piece is $u_j$, which is at most $\mu\le\tau$. Thus, with precisely
the definitions (213.3), the restricted maximum is

$$
d_1=\max\bigl(\tau,\max_{i<j}(x_{ij}+y_{ij}-p_{11}/2)\bigr).
\tag{213.8}
$$

Each additional piece is at most $x_{ij}+y_{ij}\le\kappa$.
For this example pair $45$ has maxima $(1/2,1/2,1/2,1/2)$;
forcing its positive output nonzero replaces the last by $1/4$.
The legal table $(4,5;3,0,5,1)$ earns $7/4$, proving the claimed
$d_1$ after subtracting $W$; (213.8) bounds every other schedule.
The stopped maxima on $35$ are $(1/2,1/2,1)$, attaining cost one;
on $45$ they are $(1/2,1/2,1/2)$. Every pair has N support at most
two by (213.4), proving both full costs.
This is an actual unit example with a dominated intercept different from
$\tau$; no earlier label was removed.

Separately, take $V_0=0$ and $q=(0,\ldots,0;1)$. Then
$\Delta_N(V_t)=0$ and
$\chi_q(t)=\eta_L(t-1)_+$, since $v_L$ attains $e=\eta_L$.
Every $t\in[0,1]$ minimizes the objective; its canonical least minimizer
is zero. Both endpoint phenomena are consistent with 213.2–213.4.

**Proposition 213.6 (Low-terminal retained-carrier failure and repair).**
For $L=6$, $c>0$ and $t_0\ge0$, define the actual score $Y$ by

$$
\begin{gathered}
P_{011010}=P_{011100}=P_{101010}=P_{101100}=c/2,\\
C_{110010}=C_{111110}=c,\qquad T=t_0,\qquad A=0.
\end{gathered}
$$

It has $W=2c+t_0$, $Q=(0,0,c,0,0,c;4c+t_0)$ and
$\Delta_N(Y)=\Delta_O(Y)=c$. The threshold placement on its retained
carrier changes only $C_{110010}$ to $C_{110000}$, and has

$$
\kappa=c,\quad\tau=2c,\qquad
\Delta_N(V_t)=\max(c,2c-t),\quad\Delta_O(V_t)=c.
$$

For target $Q(Y)$, optimizing every terminal and every signed residual
on this skeleton gives exact total charge
$c+\eta_6(c-t_0)_+$. At $c=1,t_0=0$ it is $11/7>1$.
Changing the carrier to $2c\delta_{0000}$ repairs the score without
changing $Q(Y)$ or $W_Y$: its rows are

$$
P_{010000}=P_{100000}=c,\qquad
C_{110000}=C_{111110}=c,\qquad T=t_0.
$$

Both repaired costs are $c$, so for $c\le1$ its single charge is
$\theta=0$.

**Proof.** At $c=1,t_0=0$, the complete pair supports of $Y$ in both
catalogs are three on $12,13,14,23,24,34,35,36,45$, $5/2$ on
$15,25$, and two on $16,26,46,56$. Empty and singleton supports are
at most three. These values follow by summing the four displayed P
atoms and two C atoms within each cell and maximizing over all seven
labels. They give the upper bound $3c+t_0$ after scaling and adding
the terminal, while $(3,4;3,0,0)$ earns exactly that value.

For the retained threshold score pair $45$ has N maxima $(c,c,c,c)$
and stopped maxima $(c,c,c)$ at zero terminal. All other pair supports
are at most $3c$ there. The full table $(4,5;3,0,0,6)$ attains $4c$;
its unqueried earlier label 3 is essential. The same stopped table
$(3,4;3,0,0)$ earns $3c+t$ for every $t\ge0$ and bounds the stopped
cost exactly. Substitution in (213.3) gives $\kappa=c,\tau=2c$.
The residual is only a terminal difference, hence
$\chi_{Q(Y)}(t)=\eta_6(t-t_0)_+$. Equation (213.5) proves its exact
minimum at $t=c$.

For the changed carrier (213.3) instead gives $\kappa=\tau=c$;
$(3,6;0,6,0)$ earns $W+c$, proving both costs. The construction and
failure persist if the selected late slots are any $r<s<u<v$, with
head $1,2$, and all other bits set to one. Zero-correct selected slots
still carry varying pair bits; they cannot be deleted. In this version
the residual factor is $\eta_L$, and inactive queries give shorter
information only. The original $Y$ already certifies its own quotient
when $c\le1$. Thus the failure concerns this retained threshold
skeleton even after signed terminal completion, not $E_N$ or the
original comparison. $\square$

### 213.2 A coupled aggregate reward-moment fiber

**Definition 213.7 (Actual moment cones and the shared pair variable).**
On the full cube set
$\phi(w)=(1,(w_i)_i,(w_iw_j)_{i<j})$ and
$\mathcal M(\mu)=\sum_w\mu(w)\phi(w)$.
Let $\mathcal C_n=\operatorname{cone}\{\phi(w):w\in\Omega_n\}$;
membership means representation by one actual nonnegative measure on
that entire first-zero class. Write $|v|$ for its constant coordinate.
For an arbitrary full score $y$ define its label-reward measures

$$
\begin{aligned}
U&=\sum_{w\ne1^L}(A_w+P_w)\delta_w+T\delta_{1^L},&u&=\mathcal M(U),\\
V_n&=\sum_{w\in\Omega_n}(C_w+P_w)\delta_w,&v_n&=\mathcal M(V_n),\\
s_n&=\sum_{\Omega_n}(A_w+P_w),&t&=T.
\end{aligned}
$$

Thus $\beta_n=|v_n|-s_n$.
Let $\mathcal F(y)$ be the full nonnegative scores with this same
$\beta$ and every individual O schedule-cell-label reward equal to
that of $y$. Equality is before maximization. Define $J(y)$ by the
single coupled optimization

$$
\begin{aligned}
J(y)=\max\ &\sum_n|p_n|,\\
p_n&\in\mathcal C_n,\quad x_n-p_n\in\mathcal C_n,\quad
v_n-p_n\in\mathcal C_n,\\
|x_n|&=s_n,\qquad \sum_n x_n+t\phi(1^L)=u.
\end{aligned}
\tag{213.9}
$$

The same $p_n$ is used in both reward measures. The aggregate baseline
equation is one equation on the common cube; one cannot replace it by
independently feasible classwise marginals.

**Theorem 213.8 (Attained coefficient minimum and signed normalization).**
For every full $y$, equality of complete O cell-label readings is
equivalent to equality of complete N readings, and to equality of $u$
and every $v_n$. With $\beta$ fixed, the fiber $\mathcal F(y)$ is
nonempty compact and fixes $T,W,B_N,B_O,\Delta_N,\Delta_O$.
The maximum (213.9) is attained, and

$$
K_{\min}(y):=\min_{z\in\mathcal F(y)}K_z
       =|u|+\sum_n|v_n|-J(y).
\tag{213.10}
$$

Put $K_{\rm floor}=t+\sum_n\max(s_n,|v_n|)$.
Then $K_{\min}\ge K_{\rm floor}$, with equality precisely when there
exist $x_n\in\mathcal C_n$ satisfying the mass and aggregate equations
in (213.9) and, simultaneously,

$$
\begin{cases}
v_n-x_n\in\mathcal C_n,&\beta_n\ge0,\\
x_n-v_n\in\mathcal C_n,&\beta_n\le0.
\end{cases}
\tag{213.11}
$$

At $\beta_n=0$ these require $x_n=v_n$.
In that case an attainer has A zero on every nonnegative-$\beta$ class
and C zero on every nonpositive-$\beta$ class. In particular, when
all $\beta_n\ge0$, (213.11) is exactly the condition for an A-free
representative in this reward fiber.

Call a score normal if it minimizes K in its own fiber. Output scores
in (213.1) may be restricted to normal scores without changing $E_N$.
The inclusion $D_O(1)\subseteq E_N$ holds for all full inputs if and
only if it holds for all normal full inputs. This is a reduction of
the universal question, not a proof of that inclusion or a pointwise
equivalence between membership of $Q(y)$ and its normalization.

**Proof.** Every cell indicator is a multilinear polynomial of degree
at most two. Conversely the empty cell gives the constant moment,
singletons give $w_i$, and the stopped $11$ cell at $i<j$ gives
$w_iw_j$. Applying these observations separately to label zero and
each numerical label proves both reading equivalences. This uses
the polynomial cell observation of 206.5 with aggregate label rewards,
rather than preserving each event/class measure separately.

The empty numerical reading fixes $|v_n|$; fixed $\beta_n$ therefore
fixes $s_n$. The empty zero-label reading fixes $|u|$, so
$T_z=|u|-\sum_ns_n=t$ for every member of the fiber.
Given such $z$, choose $x_n=\mathcal M((A_z+P_z)|_{\Omega_n})$
and $p_n=\mathcal M(P_z|_{\Omega_n})$; they satisfy (213.9).
Conversely, choose actual representing measures for $p_n$, $x_n-p_n$
and $v_n-p_n$, and use them as P, A and C. The chosen P measure is
shared once by both rewards; independent representations of the two
residual cone vectors are legitimate. Their moments are precisely
$x_n$ and $v_n$, and the aggregate equation supplies $u$. Thus these
are exactly all feasible reward data, not just necessary pair tests.

The original $y$ proves nonemptiness. Fixed nonnegative reward totals
bound each individual score coefficient. Closed linear reading constraints
therefore make the fiber compact. The moment-variable feasible set is
also compact: its nonnegative representing measures have bounded masses
$s_n$ and $|v_n|$, so it is a linear image of a closed bounded set of
such measures. A zero-mass cone vector is zero. Every table reward
is fixed, hence so are its maximum and the anchor. For every representative,

$$
K_z=|u|+\sum_n|v_n|-\sum_wP^z_w.
$$

Maximizing the final term over (213.9) proves (213.10) and attainment.
This is finite compact linear optimization, with no relaxation of
Boolean realizability.

Always $|p_n|\le\min(s_n,|v_n|)$, which gives the floor. Equality
of the sum requires equality at every class. If $s_n\le|v_n|$, the
zero-mass cone vector $x_n-p_n$ is zero; if $s_n\ge|v_n|$, the
zero-mass vector $v_n-p_n$ is zero. These give (213.11).
Conversely take $p_n=x_n$ in the first case and $p_n=v_n$ in the
second. The prescribed cone differences give actual residual A or C
measures, and the same aggregate equation makes every choice coexist.
This attains the floor and proves the claimed row elimination.

Choose a minimizer $y^\#$ and put $D=K_y-K_{\min}(y)\ge0$.
It has $Q(y^\#)=(\beta,K_y-D)$ and
$F_{Q(y^\#)}=F_{Q(y)}+De$. Normalizing any output V in its own fiber
keeps $\Delta_N$ and changes the residual reading by $-D_Ve\le0$.
The same $\theta$, including $\theta=1$, still works in (213.1).
For inputs, $y^\#$ is still unit O and
$F_{Q(y)}\le F_{Q(y^\#)}$ on H, so a certificate for $y^\#$ also
certifies $y$. Restricting the universal assertion in the other direction
is immediate. This argument is one-way for an individual input; it
does not equate the membership of its two quotients. Neither input-output
fiber equality nor preservation of the input's unaries is required of
a general certificate. $\square$

**Proposition 213.9 (Strict cross-class freedom, with arbitrary background).**
For any $1\le a<b<j<k\le L$ and $t\ge0$, fix $w_b=0$ and every bit
outside $\{a,b,j,k\}$ to one. On the eight remaining words put A=t
at odd parity of $(w_a,w_j,w_k)$ and C=t at even parity; set P=T=0.
Call this Y. Let Z have only P=t on the four even-parity words.
Then Y and Z have the same complete readings, $\beta=0$, $W=4t$,
and both costs zero; K drops from $8t$ to the floor $4t$.
For every full background $H\ge0$, Y+H and Z+H have identical
readings and $\beta$, their K values differ by $4t$, and

$$
\Delta_{\mathcal C}(Y+H)=\Delta_{\mathcal C}(Z+H)
                         \le\Delta_{\mathcal C}(H),\qquad\mathcal C=N,O.
$$

**Proof.** The possible first-zero classes are a and b, each having
base total $2t$ and numerical total $2t$. Even and odd parity on
three free bits have identical marginals on each subset of at most
two bits: a specified assignment to r bits has $2^{2-r}$ extensions
of each parity, for $0\le r\le2$. Thus the aggregate zero-label
moments match. For each numerical label the C measure of Y equals
the P measure of Z pointwise. Theorem 213.8's reading equivalence
applies. Any table earns at most the total P mass $4t$ on Z and the
anchor earns all of it. Cell equality gives the same costs for Y.
Adding H preserves the equalities before maximization; subadditivity
of the complete excess proves the displayed bound.

Y is already pointwise saturated ($A_wC_w=0$), so 198.1 does not
perform this reduction. If each event/class quadratic moment were
fixed separately as in 206.5, fixing either first-zero class leaves
two free bits; their degree-two moments determine all four atoms and
distinguish the opposite parity supports. Thus the aggregate fiber
permits a strictly different operation. The parity identity itself
is classical and already appears in the moment discussion of 206.6.

At $L=4,(a,b,j,k)=(1,2,3,4),t=1$, A occupies
$0001,0010,1000,1011$, C occupies $0000,0011,1001,1010$, and Z
puts P on the latter four. Their full N cell maxima are

| Pair | $00,01,10,11$ |
| --- | --- |
| $12$ | $(2,0,2,0)$ |
| $13,14,34$ | $(1,1,1,1)$ |
| $23,24$ | $(2,2,0,0)$ |

Every stopped pair and short schedule has support four. This also
checks zero-reward cells and all five legal labels. $\square$

**Proposition 213.10 (Joint obstruction to removing A within the fiber).**
Choose a late class $n$ and addresses $n<j<k<\ell\le L$.
All earlier bits are one, bit n is zero, and all other suffix bits
are one. Put A=t>0 at suffix $(w_j,w_k,w_\ell)=000$ and C=t
at each of $100,010,001$, with P=T=0. This score has
$\beta_n=2t$, $K=4t$, $W=t$ and both complete costs $2t$.
Every cell's numerical-label reward dominates its zero-label reward,
yet $J(y)=0$ and $K_{\min}=4t>3t=K_{\rm floor}$.

**Proof.** A cell containing the A atom observes at most two of the
three variable suffix bits. At least one C atom has the same observations,
so label n is a maximizer in every cell. Its constant rule collects
$3t$, establishing both supports and costs. The zero-label moments
force its mass t onto suffix 000. The numerical measure has total
$3t$, three coordinate moments t, and all pair-product moments zero.
The zero pair products force support at Hamming weight at most one;
the three means use all its mass on the singleton words. There can
be no common P mass. All other first-zero baseline masses are zero,
so moving across classes cannot evade this conclusion.

Equivalently the quadratic

$$
f(z)=1-z_j-z_k-z_\ell+z_jz_k+z_jz_\ell+z_kz_\ell
$$

takes values $1,0,0,1$ at Hamming weights $0,1,2,3$ and is
nonnegative everywhere, while $\int f\,d(V_n-U)=-t$.
Thus the cone difference fails even though each individual two-bit
cylinder reading is nonnegative. At $L=6,n=3,t=1/2$ the rows are
$A_{110000}=1/2$ and
$C_{110100}=C_{110010}=C_{110001}=1/2$.
Both costs are one, $K_{\min}=2$ and $K_{\rm floor}=3/2$;
each of $45,46,56$ has N maxima $(1/2,1/2,1/2,0)$.

An unrestricted repair places only C=$2t$ at any word of $\Omega_n$.
Its cost is $2t$ and its quotient is $(2t e_n,2t)$, so the target
residual is $(0,2t)$ with reading $-2te\le0$. For $t\le1/2$ this
is a certificate with $\theta=0$. The obstruction is to A removal
in the specified reward fiber; it is not $E_N$ nonmembership. $\square$

### 213.3 Automatic early-credit relocation on the whole high-terminal family

**Theorem 213.11 (Same-quotient high-terminal comparison).**
Let $\mathcal I_L$ be the whole family of full scores with A=0,
P supported on $\Omega_1\cup\Omega_2$, arbitrary C and arbitrary T.
For $y\in\mathcal I_L$ put

$$
\gamma_n=\sum_{\Omega_n}C_w,\quad E_a=\gamma_a\ (a=1,2),\quad
E=E_1+E_2,\quad\mu=\max_{n\ge3}\gamma_n,\quad t=T,
\quad\delta=\Delta_O(y).
$$

If $t\ge\mu$, there exists $V\in\mathcal I_L$ with
$Q(V)=Q(y)$, $W_V=W_y$ and $\Delta_N(V)\le\delta$.
There is no restriction on the ordering, size or number of positive late
totals, the early C suffixes, or the actual joint P carrier, including
early-00 P. If $\delta\le1$, the resulting certificate has $\theta=0$.
Moreover

$$
Q(\{y\in\mathcal I_L:\Delta_O(y)=0\})
 =Q(\{V\in\mathcal I_L:\Delta_N(V)=0\}),
\tag{213.12}
$$

including all nonzero zero-cost scores in this family.

**Proof.** On the entire late cube let
$\nu_0(x)=P_{00x}$, $\nu_1(x)=P_{01x}$, $\nu_2(x)=P_{10x}$.
Write $S_a=|\nu_a|$, $\nu=\nu_0+\nu_1+\nu_2$, $S=|\nu|$ and
$W=E+S+t$. These are three parts of the same actual measure.

First suppose $\mu\le E+\delta$. Apply the optimized absorbing-chain
supplier 206.7 with these exact $\gamma,S,t$. If $M_r$ denotes the
sum of the r largest late totals, padded by zeros, set

$$
\begin{aligned}
c_0&=\min((E+S)/2,S+\min(E_1,E_2)),\\
d_0&=\max(0,\mu-t,M_2-E-S,M_3-W,\mu-c_0),\\
s_1&=\min(S,\max(0,(E_2+S-E_1)/2)).
\end{aligned}
$$

That supplier places C=$\gamma_n$ on $1^{n-1}0^{L-n+1}$,
P=$s_1,S-s_1$ on the first two chain words, and T=t.
Its parameter $q=\max(\mu,M_2-t)$ equals $\mu$ because $t\ge\mu$.
Its actual-input lower bound is $d_0\le\delta$, and its exact complete
cost is $\max(d_0,\mu-E)\le\delta$. Its hypotheses are precisely
the present fixed totals and early-P family; no sorted input profile
is required. This branch is a direct use of 206.7.

It remains to handle $\mu>E+\delta$. Define
$m_{aj}=\nu_a\{x_j=0\}$ and $\chi=E_1+\min(E_2,S_0)$.
The legal stopped table $(1,n;1,n,0)$ has reward
$W+\gamma_n-E_2-m_{2n}$. The better of
$(2,n;0,n,0)$ and $(2,n;2,n,0)$ has reward
$W+\gamma_n-m_{1n}-\chi$. In the latter table output 2 loses
the early-00 P mass, since its first zero is 1. Hence the actual input
gives, for every $n\ge3$,

$$
\gamma_n\le E_2+m_{2n}+\delta,\qquad
\gamma_n\le\chi+m_{1n}+\delta.
\tag{213.13}
$$

At a class attaining $\mu$ these inequalities imply
$S_2>E_1$ and $S_1>(E_2-S_0)_+$.
Consequently the following actual measures are defined:

$$
\tau_1=\frac{E_1}{S_2}\nu_2,\qquad
\tau_2=
\begin{cases}
(E_2/S_0)\nu_0,&0\le E_2\le S_0, S_0>0,\\
0,&E_2=S_0=0,\\
\nu_0+((E_2-S_0)/S_1)\nu_1,&E_2>S_0.
\end{cases}
\tag{213.14}
$$

They have masses $E_1,E_2$, satisfy $\tau_1\le\nu_2$ and
$\tau_2\le\nu_0+\nu_1$, and $\tau_2$ is pointwise comparable
with $\nu_0$. Equality $E_2=S_0$ gives $\tau_2=\nu_0$ by either
nonzero branch. Also $t\ge\mu>E$.

Retain every original P row and T=t. Replace all early C by
$C_{01x}=\tau_1(x)$ and $C_{10x}=\tau_2(x)$.
Place every late C total by the threshold constructor 203.2 using
this same $\nu$, $a_{nk}=\nu\{x_n=0,x_k=1\}$, and interval
$[0,\gamma_n)$. No A is introduced. All class totals, S and t
are preserved, hence Q and W are preserved.

On any late-coordinate cell, label 1 earns
$\nu_0+\nu_1+\tau_1\le\nu$, and label 2 earns
$\nu_2+\tau_2\le\nu$. Thus zero dominates both early labels.
Put $m_n=\nu\{x_n=0\}$, $D_{ij}=\nu\{x_i=1,x_j=0\}$ and

$$
\kappa=\max\bigl(0,\max_n(\gamma_n-m_n/2)_+,\
\max_{i<j}[(\gamma_i-m_i)_++(\gamma_j-D_{ij})_+]\bigr).
$$

Deleting the original early C gives a score whose support cannot
increase and whose anchor drops by E. The actual-input lower bounds
(203.11)–(203.12), which retain early-00 mass, give
$\kappa\le\delta+E$. For the constructed late rows the joint
non-$11$ estimate (203.14)–(203.18) bounds all late-pair gains by
one $\kappa$. Its simultaneous positive gains use winning classes
$n\le i<m\le j$ and the union bound displayed in the proof of 213.4;
earlier-label off-diagonal rewards are bounded by the same actual
event differences. Since $t\ge\mu$, zero dominates the $11$ cell.
Every late N pair therefore has support at most
$S+t+\kappa\le W+\delta$.

To check the remaining pairs exactly, let

$$
L_j=\max\bigl(\{\gamma_j\}\cup
       \{(\gamma_n-a_{nj})_+:3\le n<j\}\bigr),\qquad
\tau_{aj}=\tau_a\{x_j=0\}.
$$

For pair $(1,j)$, label 1 dominates both early-zero cells, so their
maxima sum to $S_0+S_1+E_1$. For pair $(2,j)$, the comparable
measures $\tau_2,\nu_0$ make that sum exactly
$S_2+\max(S_0,E_2)$. In either $11$ cell zero wins since $t\ge\mu$
and $t>E$. In $10$ compare the other early label with every late label.
Subtracting the same anchor gives the exact identities

$$
\begin{aligned}
B_N^{1j}(V)-W&=\max(\tau_{2j},L_j-m_{2j})-E_2,\\
B_N^{2j}(V)-W&=\max(\tau_{1j},L_j-m_{1j})-\chi.
\end{aligned}
\tag{213.15}
$$

For $a=1,2$ and $n<j$ the event inclusion
$\{x_n=0\}\subseteq\{x_j=0\}\cup\{x_n=0,x_j=1\}$,
together with $\nu_a\le\nu$, gives $m_{an}-a_{nj}\le m_{aj}$.
Subtract $a_{nj}$ in (213.13) and take positive parts. Including
the $n=j$ guard proves

$$
L_j\le m_{2j}+E_2+\delta,\qquad
L_j\le m_{1j}+\chi+\delta.
$$

Also $\tau_{2j}\le E_2$ and $\tau_{1j}\le E_1\le\chi$.
Both lines of (213.15) are at most $\delta$. The head pair has
support exactly W: its first three cells collect the full early
rewards, and its positive cell is protected by $t\ge\mu$.
Every short N function refines into a pair, so these bounds exhaust
the catalog. The early-credit subtractions occur in alternative
whole-schedule bounds relative to W; they are not separate allowances.

The equality $\mu=E+\delta$ uses the chain branch. Zero totals,
$L=3$, $t=\mu$, $\delta=0$, $E_2=S_0$, and threshold ties all
remain covered. Finally the stopped head table with exhaustion label
at a largest late class gives $\delta\ge(\mu-t)_+$ for every
input in $\mathcal I_L$. Thus $\delta=0$ implies $t\ge\mu$ and
the theorem gives the forward inclusion in (213.12); the reverse
uses $\Delta_O\le\Delta_N$. $\square$

**Proposition 213.12 (A unit input requiring a change of early baseline).**
At $L=5$ define Y by A=0, T=12 and the following actual rows.
All unlisted coefficients are zero.

| Word | P | C in Y | C in V |
| --- | --- | --- | --- |
| $01000$ | $1$ | $0$ | $3/13$ |
| $01001$ | $4$ | $0$ | $3/13$ |
| $01010$ | $3$ | $3$ | $0$ |
| $01011$ | $5$ | $0$ | $3/13$ |
| $01100$ | $0$ | $0$ | $12/13$ |
| $01101$ | $0$ | $0$ | $6/13$ |
| $01110$ | $2$ | $0$ | $12/13$ |
| $01111$ | $5$ | $0$ | $0$ |
| $10000$ | $1$ | $0$ | $0$ |
| $10001$ | $1$ | $0$ | $0$ |
| $10011$ | $1$ | $0$ | $0$ |
| $10100$ | $4$ | $0$ | $0$ |
| $10101$ | $2$ | $0$ | $0$ |
| $10110$ | $4$ | $0$ | $0$ |
| $11000$ | $0$ | $7$ | $0$ |
| $11011$ | $0$ | $0$ | $7$ |
| $11100$ | $0$ | $0$ | $5$ |
| $11101$ | $0$ | $12$ | $7$ |
| $11110$ | $0$ | $9$ | $9$ |

V retains P and T and uses the last column. It is exactly (213.14)
and the threshold construction: $E_1=3,E_2=0,S_2=13$.
Both scores have $\gamma=(3,0,7,12,9)$, $S=33$, $W=48$, $K=76$.
Their complete supports are

| Pair | $B_N(Y)$ on pair | $B_O(Y)$ on pair | $B_N(V)=B_O(V)$ on pair |
| --- | --- | --- | --- |
| $12$ | $48$ | $48$ | $48$ |
| $13$ | $52$ | $52$ | $52$ |
| $14$ | $52$ | $52$ | $52$ |
| $15$ | $48$ | $48$ | $48$ |
| $23$ | $48$ | $48$ | $594/13$ |
| $24$ | $52$ | $52$ | $52$ |
| $25$ | $48$ | $48$ | $48$ |
| $34$ | $53$ | $51$ | $51$ |
| $35$ | $47$ | $45$ | $45$ |
| $45$ | $51$ | $45$ | $45$ |

For both scores the empty support is 45 and the singleton supports
are $(48,45,45,45,45)$. In particular their costs are $(5,4)$ and
$(4,4)$, and $(V/4,0)$ certifies the actual unit-O input $Y/4$.

No certificate for $Y/4$ can retain its A,P,T and all early C, even
if all late C totals, suffixes, unaries and the signed residual are free.

**Proof.** Each entry is the sum of maxima over all six labels on
the displayed finite rows. For example at $34$ the N maxima change
from $(7,11,12,23)$ to $(7,9,12,23)$. This gives all supports in
the table; short supports finish the catalogs. Thus the upper witness
is one actual score, not separately attainable cell data.

For the obstruction retain the unscaled baseline and choose arbitrary
late C totals $\eta_3,\eta_4,\eta_5$, obtaining $\widetilde V$.
The full tables $(1,3;1,1,3,0)$ and $(3,4;0,1,4,0)$ earn at
least $45+\eta_3$ and $41+\eta_4$, respectively. In the second,
the earlier unqueried label 1 collects the original C at $01010$.
Since the anchor stays 48,
$\Delta_N(\widetilde V)\ge\eta_3-3,\eta_4-7$.
If a single scaled budget existed, there would be $\vartheta\ge0$
with
$\Delta_N(\widetilde V)+\vartheta\le4$ and
$\sigma_H(Q(Y)-Q(\widetilde V))\le\vartheta$.
It would force $\eta_3\le7-\vartheta$,
$\eta_4\le11-\vartheta$, hence
$R_4=19-\eta_3-\eta_4\ge1+2\vartheta$.
At the required hull vertex $v_4=(1,1,1,1,2/5;2/5)$ the residual
is exactly $(3/5)R_4\ge3/5+6\vartheta/5>\vartheta$.
This contradiction includes the $\theta=1$ endpoint and zero-cost
candidates in that fixed-baseline class. It makes no assertion that
$v_4\in H_N$.

The two nontrivial early-00 branches can be exercised on the same data:
add $P_{00101}=2$ and $C_{10010}=c$. For c=1, the original costs
are $(4,3)$ and (213.14)'s output costs are $(3,3)$; here $E_2<S_0$.
For c=3 they are $(4,2)$ and $(2,2)$, with $E_2>S_0$.
In either case the output is explicitly determined by (213.14) and
the finitely many threshold intervals; all P and T are retained.
Padding every displayed zero word by ones gives the same readings
at larger L, while every extra label and unscored word remains legal.
This is a baseline-restriction failure with a changed-baseline repair.
The theorem leaves the strip $\max(0,\mu-\delta)\le t<\mu$ and
inputs with general A or late P outside its domain. $\square$

### 213.4 Two distinct attained requirements for late pair rows

**Theorem 213.13 (A whole-score cylinder cut).**
For every $L\ge5$ and every full score V define

$$
m_f(V)=\sum_{w|_{[5]}=11100}P_w,\qquad
\ell(V)=\sum_{n(w)\ge3}P_w,\qquad
\widehat b=(2/3,2/3,2/3,1/4,1/4,1/6,\ldots,1/6;1/6).
$$

Then $\widehat b\in H_L$ and

$$
F_{Q(V)}(\widehat b)\le\Delta_O(V)+m_f(V)/12
                         \le\Delta_N(V)+m_f(V)/12.
\tag{213.16}
$$

For every signed q and every full certificate $(V,\theta)$ for q,
$m_f(V)\ge12(F_q(\widehat b)-1)_+$.
This quantifies over arbitrary A,C,P,T, all baseline and unary changes,
and all signed residuals and nonzero zero-cost cores.

**Proof.** Use this one normalized mixture of legal stopped tables:

| Table | Probability |
| --- | --- |
| $(1,2;1,2,0)$ | $1/3$ |
| $(1,2;1,2,3)$ | $1/6$ |
| $(1,3;1,3,0)$ | $1/6$ |
| $(2,3;0,3,0)$ | $1/6$ |
| $(3,4;0,4,0)$ | $1/12$ |
| $(3,5;0,5,0)$ | $1/12$ |

Its base, correct and independent pair readings on every word are:

| First-zero information | Base | Correct | Pair |
| --- | --- | --- | --- |
| $n=1$ | at least $1/6$ | $2/3$ | at least $5/6$ |
| $n=2$ | at least $1/3$ | $1/2$ | at least $5/6$ |
| $n=3$ | $1/2$ | $1/2$ | $1$ |
| prefix $11100$ | $2/3$ | $1/12$ | $3/4$ |
| prefix $11101$ or $11110$ | $3/4$ | $1/12$ | $5/6$ |
| prefix $11111$, later first zero | $5/6$ | $0$ | $5/6$ |

The positive word has base $5/6$. The first two rows are lower bounds
over every possible suffix, not a restriction to the displayed score
atoms. They follow by evaluating the six fixed tables; the later
tables can only add base/correct mass to the first two fixed contributions.
At $\widehat b$ the first-three base/correct demands are $1/6,1/2$,
the fourth/fifth demands $7/12,1/12$, the later demands $2/3,0$,
and every pair demand is $5/6$. The only deficit is $1/12$ on the
pair row of every $11100$ suffix. Multiplying by all independent
nonnegative rows of one V gives
$W_V+F_{Q(V)}(\widehat b)\le B_O(V)+m_f(V)/12$.
This proves (213.16), including all multiple-zero words.

The hull supplier 198.5 gives the explicit identity
$\widehat b=o/6+(5/9)v_3+(2/9)u_5+v_5/18$.
Thus the same certificate residual is at most $\theta$ at this point.
Adding that one reading to (213.16) and using
$\Delta_N(V)+\theta\le1$ proves the asserted bound. $\square$

**Theorem 213.14 (First sharp full-certificate family).**
For all $L\ge5$, pad the zero words below by $1^{L-5}$ and use the
listed T at $1^L$. Define $Z_f,U_f$ by the following rows; all A vanish.

| Word | P in $Z_f$ | C in $Z_f$ | P in $U_f$ | C in $U_f$ |
| --- | --- | --- | --- | --- |
| $00100$ | $0$ | $0$ | $1$ | $0$ |
| $01000$ | $0$ | $0$ | $18$ | $0$ |
| $01010$ | $0$ | $0$ | $2$ | $0$ |
| $01011$ | $2$ | $0$ | $0$ | $0$ |
| $10000$ | $0$ | $0$ | $1$ | $0$ |
| $10010$ | $1$ | $0$ | $19$ | $0$ |
| $10011$ | $1$ | $0$ | $0$ | $0$ |
| $10100$ | $0$ | $0$ | $4$ | $0$ |
| $10110$ | $0$ | $0$ | $0$ | $1$ |
| $11010$ | $0$ | $0$ | $0$ | $21$ |
| $11011$ | $0$ | $2$ | $0$ | $0$ |
| $11100$ | $1$ | $0$ | $0$ | $6$ |
| $11110$ | $0$ | $1$ | $0$ | $6$ |
| T | $1$ | — | $21$ | — |

Let E have only $C_{11100}=1$ and put

$$
Y_t=tZ_f+E,\qquad
q_t=Q(Y_t)=(0,0,2t,1,t,0,\ldots;9t+1)\quad(t\ge0).
$$

Every $Y_t$ is an actual full score with
$\Delta_N(Y_t)=\Delta_O(Y_t)=1$. Over every complete unit certificate
for $q_t$, both the least $m_f(V)$ and the least $\ell(V)$ are
$(t-11)_+$, attained by the same certificate, for every real $t\ge0$.

**Proof.** The whole N pair maxima for the two cores are as follows.
Each tuple is in $00,01,10,11$ order.

| Pair | $Z_f$ | $U_f$ |
| --- | --- | --- |
| $12$ | $(0,2,2,2)$ | $(1,20,25,21)$ |
| $13$ | $(2,0,2,2)$ | $(20,1,21,25)$ |
| $14$ | $(0,2,1,3)$ | $(19,2,6,40)$ |
| $15$ | $(0,2,2,2)$ | $(21,0,25,21)$ |
| $23$ | $(2,0,2,2)$ | $(20,5,21,21)$ |
| $24$ | $(0,2,1,3)$ | $(6,20,18,23)$ |
| $25$ | $(1,1,1,3)$ | $(25,0,21,21)$ |
| $34$ | $(0,4,1,1)$ | $(19,21,6,21)$ |
| $35$ | $(1,3,1,1)$ | $(40,0,6,21)$ |
| $45$ | $(1,0,1,4)$ | $(24,0,21,21)$ |

These values are obtained by summing the explicitly given independent
row rewards. The empty supports are 6 and 66. Singleton cell maxima
are $(2,4),(2,4),(4,2),(1,5),(2,4)$ for $Z_f$, and
$(21,45),(25,41),(40,26),(24,42),(45,21)$ for $U_f$.
Thus $W_{Z_f}=6$, $W_{U_f}=67$, both full costs are zero, and

$$
Q(Z_f)=(0,0,2,0,1,0,\ldots;9),\qquad
Q(U_f)=(0,1,21,6,6,0,\ldots;100),\qquad \ell(U_f)=0.
$$

The stopped anchor attains W for both scores, so their O costs also
vanish. The score E has both costs one. Subadditivity gives the
upper bound one for $Y_t$; the same stopped table $(1,4;1,4,0)$
earns six on $Z_f$ and one on E, giving $6t+1$ against anchor $6t$.
This is simultaneous attainment for all $t\ge0$.

At $\widehat b$, $F_{Q(Z_f)}=F_{Q(E)}=1/12$, so 213.13 forces
$m_f(V)\ge(t-11)_+$ and hence the same bound on $\ell(V)$.
For the matching upper bound at $t=11$ use $(U_f,1)$:

$$
q_{11}-Q(U_f)=(0,-1,1,-5,5,0,\ldots;0),\qquad
F_{q_{11}-Q(U_f)}=1+5(b_5-b_4)\le1.
$$

The exact support is one, since $b_4=b_5$ occurs in H. For $t\ge11$
take $V=U_f+(t-11)Z_f$ and $\theta=1$. Its cost is zero, its
residual is unchanged, and $m_f(V)=\ell(V)=t-11$.

At $t=0$ use $(0,3/5)$, since $\sigma_H(b_4-e)=3/5$ by the
vertices of 198.5, attained at $v_4$. For $0\le t\le11$, put
$\lambda=t/11$ and take

$$
V=\lambda U_f,\qquad
\theta=(1-\lambda)\frac35+\lambda.
$$

The affine identity $q_t=(1-\lambda)q_0+\lambda q_{11}$ and
sublinearity of the single residual support prove (213.1). Its late
P mass is zero. All three witnesses have the required closed endpoints.

Padding adds only constant-one queries on the scored support. A pair
using such a query gives at most a short information type, and extra
labels earn zero there while staying legal. This bounds all schedules
at every L. The deficit calculation of 213.13 already treats every
suffix, not just padded atoms.

In particular $t=12$ has exact required late mass one, attained by
$(U_f+Z_f,1)$, whereas $t=11$ has late mass zero. The point
$\widehat b$ is outside $H_N$: a feasible full $\lambda$ there
would imply $F_{Q(Z_f)}(\widehat b)\le M\Delta_N(Z_f)=0$, contrary
to $1/12$. Every $q_t$ has the unrestricted certificate $(Y_t,0)$.
Neither the hull point nor this sharp representation requirement is
an original separator. $\square$

**Theorem 213.15 (Two whole-catalog cuts for a different quotient ray).**
For $L\ge5$ put $p_z(V)=\sum_{w|_{[5]}=z}P_w$ for five-bit z,

$$
\begin{aligned}
m_o(V)&=\sum_{3\le n(w)\le5}P_w,\qquad m_0=p_{11000}+p_{11001},\\
L_1(q)&=-14(\beta_1+\beta_2)+21(\beta_3+\beta_4+\beta_5)
            +9\sum_{j\ge6}\beta_j-9K,\\
L_2(q)&=-3(\beta_1+\beta_2)+5(\beta_3+\beta_4)+4\beta_5
            +2\sum_{j\ge6}\beta_j-2K.
\end{aligned}
$$

Every full score satisfies

$$
\begin{aligned}
L_1(Q(V))&\le36\Delta_N(V)+6m_0+2p_{11010}+p_{11100},\\
L_2(Q(V))&\le8\Delta_O(V)+m_0\le8\Delta_N(V)+m_0.
\end{aligned}
\tag{213.17}
$$

Every complete certificate for a signed q therefore satisfies

$$
6m_0+2p_{11010}+p_{11100}\ge L_1(q)-36,\quad
m_0\ge L_2(q)-8,\quad
m_o(V)\ge\max(0,L_1(q)/6-6,L_2(q)-8).
\tag{213.18}
$$

These lower bounds impose no restriction on the full output score
or its quotient other than (213.1).

**Proof.** The first cut uses the following full N tables and weights;
their total weight is 36.

| Schedule | Full outputs | Weight |
| --- | --- | --- |
| $12$ | $(1,1,2,3)$ | $2$ |
| $12$ | $(1,1,2,5)$ | $7$ |
| $13$ | $(1,0,3,0)$ | $5$ |
| $14$ | $(1,1,4,0)$ | $4$ |
| $23$ | $(2,0,3,0)$ | $1$ |
| $23$ | $(2,2,3,0)$ | $4$ |
| $24$ | $(0,0,4,0)$ | $4$ |
| $34$ | $(0,0,4,0)$ | $4$ |
| $35$ | $(0,0,5,0)$ | $1$ |
| $45$ | $(0,0,5,0)$ | $4$ |

Let a,c be their weighted counts of output zero and output $n(w)$.
Minima of $(a,c,a+c)$ over each first-zero class are, respectively,
$(9,13,27),(13,13,27),(9,12,21),(14,12,26),(22,12,34)$.
The only deficits of a+c below 27 occur at prefixes
$11000,11001,11010,11100$, by $6,6,2,1$ respectively.
At prefix $11111$ the zero count is 27.
These finite readings cover all words: for first zero k the preceding
bits and bit k are fixed, and enumerating the remaining $5-k$ bits
in the ten displayed table functions gives these counts, independently
of all suffix bits after five.

The row coefficients of $L_1(Q(V))$ on (A,C,P) are
$(5,-23,-9)$ in the early classes, $(-30,12,-9)$ in classes 3–5,
and $(-18,0,-9)$ in later classes; the T coefficient is $-9$.
Subtracting 36 times the anchor row from $(a,c,a+c)$ dominates
these coefficients except for exactly the four indicated pair deficits.
For later classes its actual coefficients are $(-9,0,-9)$,
which dominate the required ones. Multiply all independent rows by
their nonnegative coefficients and sum. Each whole table excess
is bounded by $\Delta_N(V)$, proving the first cut.

For the second use these eight full tables, each of weight one:

$$
\begin{gathered}
(1,2;1,1,2,3),\quad(1,2;1,1,2,5),\quad
(1,3;1,1,3,0),\quad(1,4;1,1,4,0),\\
(2,3;0,0,3,0),\quad(2,4;2,2,4,0),\quad
(3,4;0,0,4,0),\quad(4,5;0,0,5,0).
\end{gathered}
$$

The first two full outputs agree in each table, so all are stopped
functions. The class minima of $(a,c,a+c)$ are
$(2,4,6),(3,3,6),(2,3,5),(3,3,6),(5,2,7)$.
The only deficits below pair count six are one on each of
$11000,11001$. The positive-prefix zero count is six.
The required (A,C,P) coefficients are $(1,-5,-2)$ early,
$(-7,3,-2)$ in classes 3,4, $(-6,2,-2)$ in class 5 and
$(-4,0,-2)$ later, with T coefficient $-2$.
Subtracting eight anchors verifies every row, paying just the two
stated pair deficits. Later classes have actual coefficients
$(-2,0,-2)$. This proves the second cut for O and N.

For the one residual use the hull identities

$$
\begin{aligned}
L_1(q)&=5F_q(o)+12F_q(u_5)+18F_q(v_5),\\
L_2(q)&=F_q(o)+\tfrac53F_q(v_4)+\tfrac83F_q(u_5)+\tfrac83F_q(v_5).
\end{aligned}
$$

Their coefficient sums are 35 and 8. Thus the same residual costs
at most $35\theta$ or $8\theta$ in these two readings, respectively.
Equation (213.17) and $\Delta_N+\theta\le1$ give
$L_1(q)\le36+6m_0+2p_{11010}+p_{11100}$ and
$L_2(q)\le8+m_0$. The three weighted parts are disjoint submasses
of $m_o$, so their sum is at most $6m_o$. This proves (213.18).
The two necessary inequalities inspect one certificate and never
provide two budgets. $\square$

**Theorem 213.16 (Second sharp full-certificate family).**
For every $L\ge5$ and real $s\ge0$, set
$q_s=sq^{o}$ with $q^{o}=(0,2,4,5,5,0,\ldots;29)$.
The minimum of $m_o(V)$ over all complete unit certificates for $q_s$
is

$$
\max(0,5s/6-6,s-8).
\tag{213.19}
$$

The same value is the minimum of the total late pair mass $\ell(V)$,
and both are attained simultaneously. Every $q_s$ is the quotient of
an actual zero-O input $sY_o$ and also of a zero-N score $sZ_o$.

**Proof.** The following table defines $Y_o,Z_o,U_o,B_o$ completely.
Entries are (C,P); all A vanish. Zero words are padded by ones for
$L>5$, and the final row is T at $1^L$.

| Word | $Y_o$ | $Z_o$ | $U_o$ | $B_o$ |
| --- | --- | --- | --- | --- |
| $00100$ | $(0,1)$ | $(0,0)$ | $(0,48)$ | $(0,16)$ |
| $00101$ | $(0,0)$ | $(0,1)$ | $(0,0)$ | $(0,0)$ |
| $00110$ | $(0,1)$ | $(0,1)$ | $(0,24)$ | $(0,8)$ |
| $01000$ | $(0,1)$ | $(0,1)$ | $(0,70)$ | $(0,18)$ |
| $01010$ | $(0,1)$ | $(0,1)$ | $(0,29)$ | $(0,13)$ |
| $01100$ | $(0,1)$ | $(0,1)$ | $(0,5)$ | $(0,5)$ |
| $10000$ | $(0,1)$ | $(0,1)$ | $(0,31)$ | $(0,11)$ |
| $10001$ | $(0,0)$ | $(0,0)$ | $(0,22)$ | $(0,6)$ |
| $10010$ | $(0,1)$ | $(0,1)$ | $(0,46)$ | $(0,14)$ |
| $10100$ | $(2,1)$ | $(1,1)$ | $(48,22)$ | $(16,6)$ |
| $10110$ | $(0,0)$ | $(0,0)$ | $(24,0)$ | $(8,0)$ |
| $10111$ | $(0,0)$ | $(1,0)$ | $(0,0)$ | $(0,0)$ |
| $11000$ | $(0,1)$ | $(2,1)$ | $(123,0)$ | $(35,4)$ |
| $11010$ | $(0,0)$ | $(2,0)$ | $(31,0)$ | $(21,0)$ |
| $11011$ | $(4,0)$ | $(0,0)$ | $(22,0)$ | $(0,0)$ |
| $11100$ | $(5,0)$ | $(4,0)$ | $(152,0)$ | $(52,0)$ |
| $11101$ | $(0,0)$ | $(1,0)$ | $(0,0)$ | $(0,0)$ |
| $11110$ | $(5,0)$ | $(5,0)$ | $(176,0)$ | $(60,0)$ |
| T | $4$ | $4$ | $171$ | $55$ |

Their full N maxima on all pairs are

| Pair | $Y_o$ | $Z_o$ | $U_o$ | $B_o$ |
| --- | --- | --- | --- | --- |
| $12$ | $(2,3,5,5)$ | $(2,3,5,5)$ | $(72,104,193,176)$ | $(24,36,61,60)$ |
| $13$ | $(2,3,5,5)$ | $(2,3,5,5)$ | $(99,77,176,193)$ | $(31,29,60,61)$ |
| $14$ | $(3,2,5,5)$ | $(3,2,5,5)$ | $(123,53,152,217)$ | $(39,21,52,69)$ |
| $15$ | $(5,0,5,4)$ | $(4,1,5,4)$ | $(176,0,176,193)$ | $(60,0,60,61)$ |
| $23$ | $(2,3,5,5)$ | $(2,3,5,5)$ | $(99,94,176,176)$ | $(31,30,60,60)$ |
| $24$ | $(4,2,5,5)$ | $(3,2,5,5)$ | $(123,70,152,200)$ | $(39,22,52,68)$ |
| $25$ | $(5,0,5,4)$ | $(4,1,5,4)$ | $(171,22,176,171)$ | $(55,6,60,55)$ |
| $34$ | $(3,4,5,5)$ | $(3,2,5,5)$ | $(123,75,152,195)$ | $(39,27,52,63)$ |
| $35$ | $(5,4,5,4)$ | $(5,0,5,5)$ | $(176,22,176,171)$ | $(60,6,60,55)$ |
| $45$ | $(6,0,5,4)$ | $(5,1,5,4)$ | $(176,22,176,171)$ | $(60,6,60,55)$ |

For $Z_o,U_o,B_o$ the stopped maxima are the first two entries
summed, then the last two entries. For $Y_o$ the stopped triples
are $(5,5,5)$ on $12,13,14,23,24,34$,
$(5,5,4)$ on $15,25,35$, and $(6,5,4)$ on $45$.
The empty and each singleton support are respectively
$13,13,468,156$ for the four scores. Thus the displayed atoms give
the following whole-catalog data:

$$
\begin{array}{c|c|c|c|c|c}
 &W&Q&\Delta_N&\Delta_O&m_o\\ \hline
Y_o&15&q^{o}&3&0&1\\
Z_o&15&q^{o}&0&0&1\\
U_o&540&(0,72,176,152,176,0,\ldots;1044)&5&5&0\\
B_o&180&(0,24,56,52,60,0,\ldots;348)&1&1&4
\end{array}
$$

All these readings use every label before maximizing. Queries beyond
five are constant on this scored support, giving at most a short
information type and no larger support. The cut proofs, in contrast,
already check all actual suffixes including every later first zero.

Now $L_1(q_s)=5s$ and $L_2(q_s)=s$, so (213.18) is the lower
bound in (213.19). For matching upper bounds note

$$
\begin{aligned}
F_{36q^{o}-Q(U_o)}&=32(b_4-b_3)+4(b_5-b_4)\le0,\\
F_{12q^{o}-Q(B_o)}&=8(b_4-b_3)\le0.
\end{aligned}
$$

Use the following single scores, all with $\theta=0$:

$$
V_s=
\begin{cases}
(s/36)U_o,&0\le s\le36/5,\\
(1-\lambda)U_o/5+\lambda B_o,\quad\lambda=(5s-36)/24,
                                      &36/5\le s\le12,\\
B_o+(s-12)Z_o,&s\ge12.
\end{cases}
\tag{213.20}
$$

Homogeneity and subadditivity of $\Delta_N$ bound each by one.
In the middle branch $s=(1-\lambda)36/5+12\lambda$, so its
residual is the same convex combination of the two nonpositive
residuals. The last branch uses the exact quotient of $Z_o$.
Their late P masses are $0,(5s-36)/6,s-8$, respectively, all on
the specified prefixes. The first lower bound dominates the second
until s=12; both branches and s=0 agree at their endpoints. This
proves simultaneous attained minima for $m_o$ and $\ell$ over all
full certificates, including those with arbitrary A and signed residuals.

For example s=20 requires at least 12 units of late P, attained by
$B_o+8Z_o$. It changes the correct profile from
$(0,40,80,100,100)$ to $(0,40,88,92,100)$ at K=580, with residual
$8(b_4-b_3)\le0$. Thus the lower bound does not rely on exact Q
or on a retained input profile. On the other hand $(sZ_o,0)$ is
always an unrestricted exact-Q zero-cost certificate.
The normalized second-cut hull point is

$$
b^{\#}=(5/8,5/8,5/8,5/8,1/2,1/4,\ldots,1/4;1/4)
 =\tfrac18o+\tfrac5{24}v_4+\tfrac13u_5+\tfrac13v_5.
$$

It satisfies $F_{q_s}(b^{\#})=s/8$. For s>0 the zero-N core
proves $b^{\#}\notin H_N$, rather than providing a primal separator.
$\square$

**Corollary 213.17 (One structural failure of the early-P-only output class).**
Restrict only the output V in (213.1) by $\ell(V)=0$, allowing every
A,C,T, any quotient change, signed residual and nonzero zero core.
This certificate class does not cover all actual full unit-O inputs:
213.14 excludes it for $t>11$ and 213.16 excludes it for $s>36/5$.
These are two distinct sharp attained resource families proving the
same structural inadequacy. Their minima concern different target
quotients and must not be added. Neither family is outside $E_N$,
neither auxiliary hull point is in $H_N$, and no restriction on the
input class follows from this failure of an output restriction.

### 213.5 Full one-late quotient minima and intermediate-pair necessity

**Theorem 213.18 (One water-level score attains both full minima).**
For every $L\ge n\ge3$ and $c_1,c_2,g,B\ge0$, put
$E=c_1+c_2$, $c_{\min}=\min(c_1,c_2)$, $c_{\max}=\max(c_1,c_2)$,

$$
\begin{aligned}
q&=(c_1,c_2,0,\ldots,0,g\text{ at }n,0,\ldots,0;E+g+B),\\
R_n&=\min\left(B,\frac{n-2}{n-1}(B+c_{\min}),
                         \frac{n-2}{n}(B+E)\right),\qquad
D=(g-R_n)_+.
\end{aligned}
$$

Over the entire fiber $\mathcal F(q)=\{V\ge0:Q(V)=q\}$ of full
scores, including arbitrary A and all correct cancellations, late P,
unaries, correlations and T,

$$
\min_{\mathcal F(q)}\Delta_N=
\min_{\mathcal F(q)}\Delta_O=D.
\tag{213.21}
$$

Both minima are attained by the same actual score. Explicitly, let
$a\ge0$ be the unique solution

$$
(a-c_1)_++(a-c_2)_++(n-2)a=B.
\tag{213.22}
$$

Writing $W_0=E+B$, its branches are

$$
a=
\begin{cases}
W_0/n,&c_{\max}\le W_0/n,\\
(B+c_{\min})/(n-1),&c_{\max}>W_0/n,\quad
 c_{\min}\le(B+c_{\min})/(n-1),\\
B/(n-2),&\text{otherwise}.
\end{cases}
$$

Branch equalities give the same value. Let $w(Z)$ denote the full
word whose zero set is Z. Set

$$
\begin{gathered}
p_1=(a-c_1)_+,\quad p_2=(a-c_2)_+,\quad
p_i=a\quad(3\le i<n),\\
P_{w(\{i,n\})}=p_i\quad(1\le i<n),\qquad
C_{w(\{1,n\})}=c_1,\quad C_{w(\{2,n\})}=c_2,\quad
C_{w(\{n\})}=g,\qquad T=a,\qquad A=0.
\tag{213.23}
$$

This one score has Q=q, W=$W_0$, and both costs D, including all
zero and closed-branch cases. In particular every actual unit-O input
in this full quotient fiber has the certificate (213.23) with $\theta=0$.

**Proof.** We first bound every full competitor, without imposing A=0.
For $i<j\le n$ use the stopped table

$$
T_{ij}=(i,j;i,j,n)\quad(j<n),\qquad
T_{in}=(i,n;i,n,0).
$$

Uniformly mix all $\binom n2$ such tables. If the first zero is
$k<n$, every schedule containing k outputs k, with probability $2/n$,
whatever the later zero pattern. If the first zero is n, every table
outputs n. After n and on the positive word, zero probability is
exactly $2/n$. Test the affine demand coordinates
$e=(n-2)/n$, $b_k=1$ for $k<n$, $b_n=1+e$, and $b_k=e$ after n.
Before n the base demand is nonpositive and correct/pair demands are
$2/n$. At n the correct demand is one and base demand negative.
After n correct demand is zero, pair demand $2/n$, and base demand
$1-2e\le2/n$. Thus every independent row is dominated, including
the positive row. Multiplying by one arbitrary full score and subtracting
its own anchor proves

$$
\Delta_O(V)\ge F_{Q(V)}(b,e)
       =g-\frac{n-2}{n}(B+E)\quad(V\in\mathcal F(q)).
\tag{213.24}
$$

For center $a_0\in\{1,2\}$ instead mix uniformly the $n-1$ tables
whose schedule contains $a_0$. First-zero $a_0$ and n are always
correct; every other first zero before n is correct with probability
at least $1/(n-1)$. After n the zero probability is $1/(n-1)$.
Take $e=(n-2)/(n-1)$, $b_{a_0}=b_n=1+e$, other $b_k=1$ before n,
and $b_k=e$ after n. The same independent-row check gives

$$
\Delta_O(V)\ge g-\frac{n-2}{n-1}(B+c_{3-a_0}).
\tag{213.25}
$$

Finally the single table $(1,2;1,2,n)$ dominates all demands for
$e=1$, $b_1=b_2=b_n=2$ and other $b_k=1$. It gives
$\Delta_O(V)\ge g-B$. Combining these bounds with zero proves
$\Delta_O(V)\ge D$, and $\Delta_N\ge\Delta_O$ proves the N lower
bound. Each bound uses one normalized legal mixture. These auxiliary
vectors have $b_n>1$ and are algebraic row tests, not points in H,
original amplitudes or $H_N$ witnesses. F here is its displayed affine
formula evaluated off H, with no claim about $\sigma_H$ there.

For the upper bound (213.22) has a unique solution because its left
side is continuous, strictly increasing with slope at least $n-2$,
starts at zero and is unbounded. Solving when zero, one or two of
$c_1,c_2$ lie above a gives the displayed branches.
Set $x_1=p_1+c_1=\max(a,c_1)$, $x_2=\max(a,c_2)$ and $x_i=a$
for $3\le i<n$. Append a as a terminal weight, giving n weights
of total $W_0$. Let $r_2$ be their two-largest sum. For any n
nonnegative weights of this total with first two at least $c_1,c_2$,

$$
r_2\ge\max\left(\frac{2W_0}{n},\
c_{\max}+\frac{W_0-c_{\max}}{n-1},\ E\right).
\tag{213.26}
$$

The first inequality is the average of all pair sums. For the second,
pair the constrained coordinate of value $x\ge c_{\max}$ with the
largest remaining one; $x+(W_0-x)/(n-1)$ is increasing in x.
The two constrained coordinates give the third inequality. The
water-level weights attain the maximum: respectively all equal,
one constrained value above the common level, or both above it.
Thus $W_0-r_2=R_n$ in all branches. This elementary allocation
identity is used within the score construction, not as a separate
general optimization claim.

Equation (213.22) makes the P-plus-terminal stock of (213.23) exactly
B, and its Q and anchor are as stated. On a pair $i<j<n$, the
$00$ cell has no scored mass, the $01,10$ maxima are $x_i,x_j$,
and $11$ compares its zero baseline, g, and each unqueried early
reward $x_a$ for $a\in\{1,2\}\setminus\{i,j\}$.
If n does not win that last cell, the total is at most $W_0$:
the zero baseline and queried rewards, or the three distinct
coordinate rewards, are paid by their own entries in the n weights.
If n wins, the total is $x_i+x_j+g$.
On $(i,n)$, $01$ has no scored mass, $00$ has maximum $x_i$,
$11$ has maximum a, and $10$ compares its zero baseline, g and
the other early reward. A non-target winner again gives at most
$W_0$; a target winner gives $x_i+a+g$.
Every label has been included, including an earlier unqueried early
label. Hence every active pair support is at most
$W_0+(g-W_0+r_2)_+=W_0+D$.

If $g>R_n$, the pair of coordinates realizing $r_2$ gives exactly
this support: terminal weight a is represented by querying n, and
otherwise query the two predecessors. On each active pair one of
$00,01$ has zero scored mass, so merging them does not decrease
the maximum; the attaining function is also stopped.
If $g\le R_n$, the anchor attains $W_0$. Every short N function
refines into a pair, and queries beyond n are constant one on all
scored atoms; no larger support appears. This proves both equalities
and simultaneous attainment.

For an arbitrary full input in the fiber, writing $A_{\rm tot}=\sum A$,
the quotient identities are

$$
B=2A_{\rm tot}+\sum P+T,\qquad
W_y=E+B-A_{\rm tot}.
$$

Thus the constructed anchor may exceed the old one. Exact Q does
not fix W or the separate correct totals; no input baseline was
silently retained. The lower bound applies to that input with its own
anchor, giving $D\le\Delta_O(y)\le1$ for a unit input. The new score
therefore certifies the same Q with the one residual zero. $\square$

**Theorem 213.19 (Sharp necessity of intermediate pair stock).**
For every $L\ge n\ge4$ let
$I_n(V)=\sum_{3\le n(w)<n}P_w$.
For all $g,B\ge0$ and every full score with
$Q(V)=(g e_n,g+B)$,

$$
\Delta_O(V)\ge g-\frac{n-2}{2n-3}(B+I_n(V)),
\qquad \Delta_N(V)\ge\Delta_O(V).
\tag{213.27}
$$

For every $d,r\ge0$, at $g=d+(n-2)r$ and $B=nr$, the exact least
$I_n(V)$ over all such full exact-Q scores with $\Delta_N(V)\le d$
is $(n-3)r$. The same score (213.23), with $c_1=c_2=0$ and a=r,
attains this mass and both costs d. This includes nonzero zero-cost
cores when d=0 and r>0.

**Proof.** Put $e=(n-2)/(2n-3)$ and $s=1/(2n-3)$. Use one stopped
mixture: weight e on $(1,2;0,0,n)$ and weight s on each
$(i,n;0,n,0)$, $1\le i<n$. The weights sum to
$e+(n-1)s=1$. At first zero 1 or 2 its zero probability is at least
$e+s=1-e$; at a first zero $3\le k<n$ it is at least s.
At first zero n its correct probability is one. After n and on
the positive word the zero probability is exactly $(n-1)s=1-e$.

Use auxiliary $b_n=1+e$ and $b_k=e$ elsewhere. All correct demands
outside n are zero and all base demands outside n are
$1-2e=s$. At n the base demand is negative. Only the independent
pair demand $1-e$ on intermediate classes may fail, by at most e.
Summing every row against one arbitrary full V gives

$$
\Delta_O(V)\ge F_{Q(V)}(b,e)-eI_n(V)=g-e(B+I_n(V)).
$$

If $\Delta_N(V)\le d$, this implies
$I_n(V)\ge(g-d)/e-B=(n-3)r$ at the specified parameters.
The water-level score has exactly one P atom of mass r in each
intermediate class and $R_n=(n-2)r$, so its two costs are d.
This proves attainment over the full exact-Q fiber, with all A and
correct-row cancellations allowed in the lower quantifier. The
off-hull demand direction supplies no original negative and the
exact-Q obstruction is not an iff test for unrestricted $E_N$.
$\square$

**Example 213.20 (All branches, unit stock and the zero endpoint).**
At $L=n=5,c_1=c_2=0,g=4,B=5$, (213.23) is

$$
P_{01110}=P_{10110}=P_{11010}=P_{11100}=1,\qquad
C_{11110}=4,\qquad T=1.
$$

It has W=5, Q=$(0,0,0,0,4;9)$, and both costs one.
For every $i<j<5$ its N maxima are $(0,1,1,4)$ and O maxima
$(1,1,4)$; for every $(i,5)$ they are $(1,0,4,1)$ and $(1,4,1)$.
All pair supports are six, and all empty/singleton supports are five.
Theorem 213.19 forces $I_5\ge2$ for every full exact-Q score of N
cost at most one; these two intermediate P atoms attain equality.
Changing only g to three gives a zero-cost core and the same exact
intermediate requirement two for exact-Q zero-cost representatives.

The one-clamped branch with unequal credit occurs at
$c_1=3,c_2=1,B=4,g=19/4,n=5$. Here a=$5/4$,
$R_n=15/4$, W=8, K=$51/4$, and both costs one. The actual rows are
$C_{01110}=3$, $C_{10110}=1$, $C_{11110}=19/4$,
$P_{10110}=1/4$, $P_{11010}=P_{11100}=5/4$, and T=$5/4$.
For a both-clamped example take $c_1=c_2=2,B=3,g=4,n=5$:
a=1, $R_n=3$, P is one on $11010,11100$, early C is two on
$01110,10110$, late C is four on $11110$, and T=1; both costs
are one. At $B=0$ equation (213.22) gives a=0 and R=0 for any
early credits; at all-zero parameters the score is zero. The branch
ties are already included in the exact equation, requiring no limit.

The conclusion covers nonnegative net coordinates supported on
$\{1,2,n\}$, even when the input uses arbitrary A or late P.
It makes no claim for multiple late net coordinates, negative beta,
or a joint budget obtained by adding separately optimal allocations.
The value D is an exact-Q minimum, not a necessary and sufficient
criterion for unrestricted signed-residual membership in $E_N$.

### 213.6 Suppliers, original realization and the remaining comparison

**Definition 213.21 (Owning results and bounded literature position).**
The new relations here are the full-skeleton terminal minimum and its
exact threshold reserve; the coupled aggregate reward fiber and attained
coefficient minimum; automatic early-credit allocation on the whole
high-terminal input family; two sharp full-certificate late-P requirements;
and the full one-late exact-Q minimum with intermediate-pair necessity.
The following supplier maps specify the reused hypotheses and the
additional operation, rather than counting a reused theorem again.

| Owning result | Parameters and use here | Boundary retained |
| --- | --- | --- |
| [198.5](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#198-完整目录得分约化符号凸包与混合预算缺口) | The same L, signed $(\beta,K)$ and vertices $o,p,u_k,v_k$ evaluate every residual; $e_{\max}=(L-2)/(L+1)$ controls terminal changes. | Hull membership alone is not membership of $H_N$; zero hull coordinates are not original tails. |
| [199.3–199.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#199-完整事件锥的有符号替代零成本闭包与剩余原始比较) | Full nonnegative V, signed q and one $\theta$ in (213.1), with all independent rows in $G_N$. | The alternative and clipped-comparison equivalence do not assert universal inclusion. Nonzero zero-cost V at $\theta=1$ remains legal. |
| [203.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md#203-实际-pair-容量的阈值迁移与完整预算补偿) | In 213.3 use $\gamma=\eta$, actual carrier $\nu$, and ordered selected coordinates J; in 213.11 use the full actual late projection and $\gamma_n$. The clipped interval bounds and joint union estimate are applied before any terminal protection. | Its high-terminal equality requires E=0 and $t\ge\mu$; its general bound is an upper bound. Here low-terminal reserve is derived explicitly, and early-credit allocation is proved separately. |
| [206.5–206.6](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VIII.md#206-pairwise-moments-exact-chain-minima-and-dense-early-credit-certificates) | Degree-two cell indicators applied to aggregate zero-label rewards and each numerical-label reward. | Separate event/class moment preservation is stronger than the coupled fiber. Generic moment compression and the parity identity are existing tools. |
| [206.7](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VIII.md#206-pairwise-moments-exact-chain-minima-and-dense-early-credit-certificates) | Same $(\gamma,S,t)$; when $t\ge\mu$, its $q=\max(\mu,M_2-t)$ is $\mu$. Its lower $d_0$ and exact chain cost fund precisely the $\mu\le E+\delta$ branch. | No chain construction is asserted automatically affordable outside that inequality. |
| [212.2–212.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_X.md#212-coupled-surplus-carriers-equality-block-moves-and-joint-fixed-data-minima) | The retained baseline and aggregate carrier constraints give a comparison for the changed-baseline operation in 213.11–213.12. | That fixed-baseline class does not contain every output here; its moment-box criterion is not used as an unconditional existence result. |
| [109.1, 110.2 and 112.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md) | Probability-vector kernels, all-word cap rows, exact closed caps and the original resource contract, as specified in 213.22 below. | Dual scores are not kernels; an exact-law obstruction permits another stopped law at the same cap. |

These are repository-derived ordinary consequences within the stated
domains. Classical finite convex optimization, parity and support-function
operations are not claimed as new. The whole-score witness mixtures
are explicit applications of the complete event geometry, not a new
general duality or transport theorem. No disjointness from every older
convex or signed closure, new optimal amplitude classification, exhaustive
novelty result or worldwide-priority claim is made.

David Blackwell, [*Comparison of Experiments*, pp. 93–98,
§§2–5](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
defines attainable loss vectors and comparison through one common
stochastic kernel. Here a Boolean word is a state, a schedule supplies
a transcript partition, and a terminal label is an action. This is
the useful correspondence. An arbitrary comparison kernel in that
framework need not preserve an increasing stopped schedule or a hard
bound of two actual requests, so its comparison theorem supplies no
missing N-to-O conversion.

Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1,
Theorem 1(ii), Theorems 7–8 and §1.6](https://arxiv.org/pdf/1001.2161v1),
supplies the finite Farkas and polyhedral framework used by the owning
199.3–199.4 alternative. In 213.8 the generators are the actual
$\phi(w)$, the constraints are the shared-P and aggregate moment
equations, and bounded nonnegative masses give compactness directly.
No generic LP fact substitutes for realization of these generators.

Danila Zaev, [*On the Monge–Kantorovich problem with additional linear
constraints*, arXiv:1404.4962v1, Problem 1.3, the compactness argument
preceding Corollary 1.5, and Theorem 2.1](https://arxiv.org/html/1404.4962v1),
considers one measure with prescribed marginals and additional linear
constraints. That common-measure condition is the relevant comparison
for (213.9). The present finite Boolean fiber proves its own coefficient
accounting; no transport distance, martingale constraint or acquisition
budget is inferred from the general constrained-transport theorem.

Nils Bertschinger and Johannes Rauh,
[*The Blackwell relation defines no lattice*, arXiv:1401.3146v1,
Example 18](https://arxiv.org/html/1401.3146v1), exhibit zonotope
containment with no common stochastic postprocessing matrix: their
unique nonnegative representing matrix fails to be stochastic.
This distinguishes separate decision readings from a common rule.
Their matrices are not embedded as an original-source separator here.
Kailin Chen, [*Experiments in the Linear Convex Order*,
arXiv:2502.06530v1, Theorem 3, Definition 7 and Corollary 3](https://arxiv.org/html/2502.06530v1),
gives binary-action comparison and an extension requiring a binary
decomposition of the value function, with finite action space for the
stated strategy comparison. No such decomposition preserving the
whole hard-two catalog is assumed here. These primary passages delimit
the analogy; none proves one of the missing universal implications.
The versioned sources and named owner results bound the literature
position, without an exhaustive search assertion.

**Definition 213.22 (Original-source and common-seed correspondence).**
The actual labeled source remains

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
        \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
$$

with $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and increasing primes
$p_i$. It is countable and each static integer has finite prime support.
[Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows)
supplies actual source witnesses for every finite pattern on arbitrary
finite addresses. Thus all multiple-zero words in these catalogs
have the original interpretation; the positive finite word is not an
infinite all-positive source.

The full tape space is
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$ with
each block a copy of $(0,1)$ and the disjoint-union Borel sigma algebra.
The fixed consumer returns unknown on each $B_j$ and proposes j on
each $P_j$. The original nonatomic targets are those of
[Source-Correlated Laws 67.5](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#67-original-target-proportional-containment-and-unavoidable-nonatomic-ranges),
retained by Acquisition Resources 73.1. Explicitly, for their fixed
parameter $h_0\in(0,1)$, let $t(x)=\sum_i3^{-i}q_i(x)$,
let $\nu_x$ have density $e^{t(x)u}/\int_0^1e^{t(x)v}\,dv$ on
$B_{n(x)}$, and let $\pi_j$ be uniform on $P_j$.
Then $\mu_x=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, where $\Omega(x)$
is the number of distinct prime divisors. These laws and the consumer
are unchanged. In particular the marks
$\theta_j=(B_1,1/(j+2))$, $j\ge0$, support the separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                     +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_j\longrightarrow0.
\tag{213.28}
$$

Selected marked laws do not replace the original nonatomic family.
The acquisition receives no source label, integer value, first-zero
index, source law or extra observation. It has zero advice, one
source-independent common seed, and actual sourcewise almost-sure
finite handoff on the original carrier. Errors are uniform over every
actual source and every Borel event. Definition 90.1 counts at most
two actual requests, including repetitions and ignored replies.
$\mathcal N_2$ preselects its schedule and obtains its replies;
$\mathcal O_2$ preselects an increasing schedule and stops at the
first queried zero or exhaustion. Output labels need not be queried.
Arbitrary addresses and full-carrier outputs remain in the competitor
quantifiers. No address, depth, runtime, expected-count or source-average
resource replaces this hard count.

Theorem 109.1 applies only to an actual normalized probability-vector
kernel on every word, of degree at most two. To avoid confusing its
coefficients with the score quotient, write

$$
p_w=c+\sum_i l_iw_i+\sum_{i<j}Q^{\rm ker}_{ij}w_iw_j,\qquad
H^{\rm ker}=\sum_i\left(\sum_{j>i}(-Q^{\rm ker}_{ij})_+-l_i\right)_+.
$$

Its stopped criterion is $c\ge H^{\rm ker}$ coordinatewise;
normalization supplies the scalar schedule-mass bound as in 108.4.
It is not a criterion on the proof scores constructed here.
Theorem 110.2 transports normalized finite configurations satisfying
all the independent cap rows at the same positive closed cap.
For $0<\varepsilon\le1$ use the strict active length
$L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$.
At every actual tail source $n>L_a$ its exact supplied identity is

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
          (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
       =\max(1-p_{1^{L_a}}(0),a_n).
\tag{213.29}
$$

Equality $a_n=\varepsilon$ remains. The necessity direction includes
arbitrary-address, full-output original competitors: countability gives
one probability-one seed event of finite hard-two handoff, the maximum
preselected address has vanishing seed tails, finite-pattern witnesses
and Source-Correlated Laws 45.3 transport entire finite executions,
and finite-catalog compactness retains the closed cap. These are the
hypotheses and operations of the owning 110.2 proof, not a new transport
claim or a source-distribution argument.

A normalized table mixture used here is realized by partitioning a
single uniform seed into its schedule/table masses before answers.
The whole deterministic table is fixed on each seed interval. Execute
the increasing schedule and stop at its first queried zero or exhaustion;
its N completion acquires the whole same preselected schedule and ignores
later replies, preserving the output law by 90.2. Every execution of
these finite mixtures hands off after at most two actual requests.
Different mixtures can use different partitions of the same seed,
or their common refinement, without claiming seedwise equal outputs.
The six-table law of 213.13 is an actual normalized rule but fails a
cap row at $\widehat b$, so it is not a cap attainer there. Integer
weights in 213.15 are support witnesses, not additional requests.

For an explicit reused feasible interface, put probability $1/4$ on
each stopped table

$$
(1,2;1,2,0),\quad(1,2;1,2,3),\quad
(1,3;1,3,0),\quad(2,3;2,3,0).
\tag{213.30}
$$

Its same-seed full N completions give a mass-one full $\lambda$ at
$v_3\in H_N$. For n=1,2 its correct mass is $3/4$ and pair mass
at least $3/4$; the base demand is negative and is retained. For n=3
the base/correct/pair masses are $(1/4,3/4,1)$; for every later first
zero they are $(3/4,0,3/4)$, and the positive base mass is $3/4$.
These are every-word readings including arbitrary multiple zeros.
Take $a_1=a_2=a_3=1$ and
$a_n=2^{-(n-4)}/4$ for $n\ge4$. At the exact closed cap $1/4$
every actual later-source error is $\max(1/4,a_n)=1/4$, including
$a_4=1/4$. This illustrates the existing original interface; it is
not a new cap classification deduced by treating a score as a kernel.

There is also an actual-law check of 213.18's uniform lower mixture.
Take $a_1=\cdots=a_n=1$, $e_0=1-2/n$ and
$a_{n+j}=e_0 2^{1-j}$ for $j\ge1$. Before n its correct probability
is at least $2/n$, at n it is one, and every actual later source has
law $(2/n)\delta_{\theta_0}+(1-2/n)\delta_{\theta_n}$.
Its error is $\max(e_0,a_{n+j})=e_0$, including the first tail
equality. This realizes the legal mixture at a positive closed cap
with zero advice and the same seed; it asserts no optimality of that
cap. Auxiliary off-hull test coordinates and zero score masses have
not replaced positive vanishing original amplitudes.

**Definition 213.23 (Unresolved universal obligation).**
The remaining full-score question is still

$$
Q(y)\in E_N\quad\text{for every }L\ge3\text{ and every full }
y\ge0\text{ with }\Delta_O(y)\le1.
\tag{213.31}
$$

Theorems 199.3–199.4 identify its equivalent clipped comparison
$\rho_O(b)\le\max(1,\rho_N(b))$ for every $b\in H_N$.
The original question remains, for every sequence (213.28) and
every positive closed cap,
$\mathcal F_N(a,\varepsilon)\ne\varnothing\Rightarrow
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing$,
with the complete slice and normalized stopped region of 110.1 and
109.1. Small active lengths and cap one retain their existing transport;
caps above one admit immediate base output.

Terminal and moment normalization reduce searches without supplying
an affordable skeleton for every input. The whole high-terminal
early-P family leaves its low-terminal strip, arbitrary A and late-P
inputs outside that theorem. The exact one-late fiber result leaves
multiple late coordinates and negative beta outside its theorem.
The two late-P necessities exclude one output restriction, and their
displayed inputs already have unrestricted certificates or zero-N cores.
No combination of these separate conclusions proves (213.31).

A genuine original negative still requires the same actual objects
throughout:

$$
\begin{gathered}
y\ge0,\quad\Delta_O(y)\le1,\quad b\in H_N,\qquad
\lambda\ge0,\quad G_N\lambda\ge h(b),\\
M=\sum_D\lambda_D\ge1,\qquad F_{Q(y)}(b)>M,
\end{gathered}
\tag{213.32}
$$

followed by the owned transport to an actual common-seed $N_2$
attainer and a uniform lower certificate against every original
arbitrary-address, full-carrier $O_2$ competitor. An $H_L$ point alone,
separately realized event rows, an exact-Q or retained-carrier failure,
and the exact-law obstruction 112.2 do not supply (213.32).
Neither the universal implication nor such an original separator is
established here; these ordinary structural results leave that goal active.

## 追加锚（本行以下为增补区）
## 214. Simultaneous late coordinates: signed cones, fixed fibers, and a necessary stock envelope

This increment uses the full score and catalog inherited from Definition 210.1. Words use the literal answer bits: $0$ means a zero answer, $1$ means a positive answer, $n(w)$ is the first literal zero, and $1^L$ is the all-positive word. Thus $w(Z)$ has literal zeros exactly at $Z$. The separate zero indicators in §214.4 are $z_i=1-w_{j_i}$, with $j_6=\ell$. Every word, including multiple-zero words and the all-positive word, remains in the domain. A score has independent nonnegative rows $A,C,P$ on zero words and terminal mass $T$ on the all-positive word. Its quotient is

$$
Q(V)=(\beta,K),\qquad \beta_j=\sum_{\Omega_j}(C-A),\qquad
K=\sum_w(A_w+C_w+P_w)+T,
$$

and its excess is the complete all-label support minus its anchor. Empty schedules, singleton schedules, increasing pairs, reversed pairs, repeated addresses, arbitrary labels (including earlier and unqueried labels), and the independent pair row are always included. The finite statements below are statements about this full catalog; a listed table is only a detector or a supplier inside that catalog.

The original universal implication remains the surrounding question:
$\mathcal F_N(a,\varepsilon)\ne\varnothing$ should imply
$\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing$ at every positive closed cap, or else a same-realization separator must be supplied. None of the four results below settles that implication.

### 214.1. A signed exact-$Q$ cone with one positive late coordinate

**Definition 214.1 (signed one-pivot cone).** Let $L\ge3$, let $q=(\beta,K)$ satisfy
$K\ge\sum_{j=1}^L|\beta_j|$, and suppose that at most one late coordinate is positive. Put

$$
D=(-\beta _1)_++(-\beta _2)_+.
$$

If all late coordinates are nonpositive, define $D_*=D$ directly. Otherwise let $n$ be the unique index with $n\ge3$ and $g=\beta_n>0$, set $H=K-g$, and put

$$
a=\bigl(|\beta _1|,|\beta _2|,-\beta _3,\ldots,-\beta _{n-1},
              \sum_{j>n}(-\beta_j)\bigr).
$$

In this positive-pivot branch, $a$ has $n$ nonnegative entries, $\sum_i a_i\le H$, and $a_{[1]}\ge a_{[2]}$ denote its two largest entries. Define

$$
J=\max\left\{a_{[1]}+a_{[2]},
       \frac{H+(n-2)a_{[1]}}{n-1},\frac{2H}{n}\right\},
\qquad
D_* =D+(g-H+J)_+ .
$$

**Theorem 214.2 (full signed one-pivot minimum).** Over all nonnegative full scores $V$ with $Q(V)=q$,

$$
\min_{Q(V)=q}\Delta_N(V)=\min_{Q(V)=q}\Delta_O(V)=D_* .
\tag{214.1}
$$

One and the same score attains both minima. If every late coordinate is nonpositive, the value is $D$, with no pivot required. All zero masses, ties, $n=L=3$, $K=\sum|\beta_j|$, and the closed value $D_*=1$ are included. The theorem allows arbitrary signed early coordinates, arbitrary late pair rows, changed anchors and unaries, and simultaneous negative late coordinates. It does not cover two positive late coordinates.

**Proof.** First consider the lower rows. The stopped schedule $(1,2)$, with output zero at a queried early zero whenever the corresponding early coefficient is negative and with the ordinary correct output otherwise, gives the anchor lower bound $\Delta_O\ge D$; its $N$ completion gives the same bound.

In the positive-pivot branch, take any two-element subset $S\subseteq\{1,\ldots,n\}$, query it in increasing order, output at a first zero $i<n$ the label $i$ when $i\le2$ and $\beta_i\ge0$, and output $0$ otherwise; at a first zero at $n$ output $n$; on exhaustion output $0$ when $n\in S$ and $n$ otherwise. This is a legal stopped table, and it retains every label allowed by Definition 210.1. Average such tables under an arbitrary law on the two-element sets. Write
$p_i=\Pr(i\in S)$ and $r=\min_i p_i$. The resulting detector outputs $n$ on every $\Omega_n$, outputs the designated early correct or base label on $\Omega_j$ with probability at least $p_j$ for $j<n$, has base probability $p_n$ on every $\Omega_j$ with $j>n$, has every independent pair probability at least $r$, and has positive-word base probability $p_n\ge r$.

Put $k=r-1$. For $j<n$ define

$$
\xi_j=\begin{cases}
p_j-r,&j\le2,\ \beta_j\ge0,\\
-1-p_j+r,&j\le2,\ \beta_j<0,\\
r-p_j,&j\ge3,
\end{cases}
$$

and put $\xi_n=2-r$, $\xi_j=r-p_n$ for $j>n$. The detector's complete event vector dominates the anchor plus the coefficient vector of
$\sum_j\xi_j\beta_j+kK$. On an early positive class the three required event thresholds are
$(2r-p_j-1,p_j,r)$; on an early negative or later negative class they are
$(p_j,2r-p_j-1,r)$ (with $p_n$ after the pivot); on $\Omega_n$ they are
$(2r-2,1,r)$; and the terminal threshold is $r$. These are requirements on event probabilities, not nonnegative slacks; the actual probability minus its threshold is the slack. Since $2r-p_i-1\le0$, every independent $A,C,P$ row, including negative singleton rows and the pair row, is covered. Multiplying by an arbitrary nonnegative score gives

$$
\Delta_O(V)\ge D+g-H+\sum_i a_i p_i+B r,
\qquad B=H-\sum_i a_i.
\tag{214.2}
$$

Three concrete detector mixtures give the three sharp lower tests. Put weight one on the pair of the two largest entries of $a$; this gives
$D+g-H+a_{[1]}+a_{[2]}$. Put equal weight on all pairs containing an index of largest mass and average over the remaining $n-1$ choices; this gives
$D+g-H+[H+(n-2)a_{[1]}]/(n-1)$. Put equal weight on all $\binom n2$ pairs; this gives
$D+g-H+2H/n$. Together with $D$, these are exactly $D_*$.

For the matching score choose nonnegative $z_i\ge a_i$ with
$\sum_i z_i=H$ and with the largest-two sum equal to $J$. Such a choice is obtained by water filling: choose $h\ge0$ with
$z_i=\max(a_i,h)$ and the required sum (with the evident $h=0$ convention when $B=0$). If $h\le a_{[2]}$, the largest-two sum is $a_{[1]}+a_{[2]}$; if $a_{[2]}\le h\le a_{[1]}$, it is
$[H+(n-2)a_{[1]}]/(n-1)$; and if $h\ge a_{[1]}$, it is $2H/n$. Conversely, every vector $z\ge a$ of sum $H$ has largest-two sum at least $a_{[1]}+a_{[2]}$ and at least the average pair sum $2H/n$. Pair the coordinate above the largest floor with the largest remaining coordinate: if that coordinate has value $x\ge a_{[1]}$, their sum is at least $x+(H-x)/(n-1)\ge[H+(n-2)a_{[1]}]/(n-1)$. Thus every vector obeys all three bounds and water filling is optimal.

Write $w(Z)$ for the length-$L$ word whose zero set is $Z$. For each $i<n$ put
$P_{w(\{i,n\})}=z_i-a_i$ and, on that word, put $C=\beta_i$ if $\beta_i\ge0$ and $A=-\beta_i$ if $\beta_i<0$. Put $C_{w(\{n\})}=g$, put $A_{w(\{j\})}=-\beta_j$ for $j>n$, and put $T=z_n-a_n$; all other coefficients are zero. The rows on coincident words add. Direct substitution gives $Q(V)=q$ and anchor $W_V=H-D$.

For a full catalog cell, a guard $i<n$ can contribute at most $z_i$, while all post-pivot negative-base atoms together with the terminal atom contribute at most $z_n$. A table that collects no reward from the positive-pivot atom earns at most $H$. If it collects that atom, its cell is assigned label $n$, which collects no guard reward; only guards in other cells can contribute. A schedule isolating two guards earns at most $g+z_i+z_j$; one guard and the pivot earns at most $g+z_i+z_n$; a schedule using an address after the pivot can isolate only its own negative-base atom, at most $z_n$, and two such addresses recover at most $z_n$ beyond the pivot. These bounds use the maximum over every legal numerical label in each cell. Hence

$$
B_N(V),B_O(V)\le\max(H,g+J),
$$

while the pair of slots realizing $J$ gives a stopped table attaining the corresponding value: two guard slots use their maximizing guard labels and pivot label on exhaustion; a guard-pivot pair uses the guard label, pivot label on the $10$ cell, and zero on the $11$ cell. The modified anchor earns $H$. Thus equality holds and
$\Delta_N(V)=\Delta_O(V)=D_*$ in the positive-pivot branch.

If all late coordinates are nonpositive, instead put, for every $j$,

$$
 C_{w(\{j\})}=(\beta_j)_+,\qquad
 A_{w(\{j\})}=(-\beta_j)_+,\qquad
 P=0,\qquad T=K-\sum_j|\beta_j|.
$$

All these coefficients are nonnegative; every negative early and late coordinate is retained. The quotient is exactly $q$, and the anchor is
$W_V=\sum_{j\le2}(\beta_j)_++\sum_{j\ge3}(-\beta_j)_++T=K-D$.
The total of the pointwise maximum rewards is $K$, so every schedule in either full catalog has support at most $K$. The modified $(1,2)$ anchor collects every coefficient: it emits the appropriate correct or base label on the early singleton words and zero on every late singleton and the positive word. Its reward is $K$. Hence both supports equal $K$ and both excesses equal $D$. This also covers $K=0$, all zero coefficients, and all unused terminal stock, and completes (214.1). $\square$

**Corollary 214.3 (one exact certificate and its boundary).** If an actual unit-$O$ input has a quotient in the cone of Theorem 214.2, the single score above has $Q(V)=Q(y)$, $\Delta_N(V)=D_*\le\Delta_O(y)\le1$, and the residual is zero. Thus the certificate uses one common score and $\theta=0$. For every complete feasible $\lambda$ for the same $b\in H_N$, of mass $M$, the existing weak-duality row gives
$F_{Q(y)}(b)\le M\Delta_N(V)\le M\le\max(1,M)$; no $H_L$ point is substituted for the original $H_N$ witness. A detector mixture itself has actual tail error
$\max(1-p_n,a_m)$ at a later first absence $m$, by the closed-tail identity supplied with Theorem 110.2; it is not asserted to attain every arbitrary cap. The nonnegative one-late specialization is Theorem 213.18, so the new content is the signed early cone and the aggregate post-pivot negative stock.

### 214.2. A fixed-$\{3,4\}$ fiber and a common-seed companion

**Definition 214.4 (fixed two-late fiber).** Let $L\ge4$, $g,h,B\ge0$, and

$$
q=(0,0,g,h,0,\ldots,0;g+h+B).
$$

For a score on this fiber, $B=K-\beta_3-\beta_4=2\sum A+\sum P+T$; an arbitrary competitor need not have $W=B$, because $W=B-\sum A$. The minimization below is over every nonnegative full score, with arbitrary $A$, early $P$, late $P$, cancellations, changed anchor and arbitrary labels.

**Theorem 214.5 (one simultaneous minimum for the fixed fiber).** Define

$$
\Phi(g,h,B)=\max\left\{0,\ g-\frac B3,
 \frac{g+2h-B}{2},\frac{3g+h-B}{4},
 \frac{2g+2h-B}{4},g+h-\frac{2B}{3},
 \frac{4g+3h-2B}{5}\right\}.
\tag{214.3}
$$

Then

$$
\min_{Q(V)=q}\Delta_N(V)=\min_{Q(V)=q}\Delta_O(V)=\Phi(g,h,B).
\tag{214.4}
$$

The same score attains both minima. Equivalently, for an allowance $d\ge0$ the least stock is

$$
B_*(g,h,d)=\max\left\{0,3g-3d,g+2h-2d,3g+h-4d,
2g+2h-4d,\frac{4g+3h-5d}{2},\frac{3(g+h-d)}2\right\}.
\tag{214.5}
$$

In particular the exact zero-cost threshold is $B\ge\max(3g+h,2g+2h)$. Fixed addresses are part of the theorem; no relabelling to arbitrary positions is claimed.

**Proof.** Use the following nine legal stopped tables, where $(i,j;x,y,z)$ means that the increasing schedule $(i,j)$ outputs $x,y,z$ in cells $0,10,11$:

$$
\begin{array}{c|c}
 a=(1,2;0,0,3)&b=(1,2;0,0,4)\\
 c=(1,3;0,3,0)&e=(2,3;0,3,0)\\
 f=(1,3;0,3,4)&g_0=(2,3;0,3,4)\\
 h_0=(2,4;0,4,0)&i_0=(3,4;0,4,0)\\
 j_0=(3,4;3,4,0)&
\end{array}
$$

For a multiset of $k$ tables let $N_0(w)$ count output zero and $N_n(w)$ count output $n(w)$ on a zero word. Its coefficients on independent $(A,C,P)$ rows are
$(N_0-k\mathbf1_{n\ge3},N_n-k\mathbf1_{n\le2},N_0+N_n-k)$, and its terminal coefficient is $N_0-k$. The following six bundles, with their displayed $(u,v,m;k)$, have rowwise sums dominating the complete functional
$u\beta_3+v\beta_4-k(\beta_1+\beta_2)-m\mathcal S(V)$, where
$\mathcal S(V)=K-\sum_j\beta_j=2\sum A+\sum P+T$. This assertion is before imposing the early equalities and holds on every suffix and every multiple-zero word:

$$
\begin{array}{c|c|c|c|c|c}
\text{bundle}&\text{tables}&u&v&m&k\\\hline
1&a,c,e&3&0&1&3\\
2&f,h_0&1&2&1&2\\
3&b,c,e,i_0&2&2&1&4\\
4&c,e,f,g_0,i_0&4&3&2&5\\
5&a,c,e,i_0&3&1&1&4\\
6&f,g_0,j_0&3&3&2&3
\end{array}
$$

For completeness, the verification is uniform. On an early prefix $00,01,10$, the bundle has no output equal to the actual early first-zero label, and its total zero-output count is at least $k-m$. On class $3$ the bundle has exactly $u$ correct outputs, on class $4$ exactly $v$, and at most $m$ outputs outside the set $\{0,n\}$; on every class $n>4$ the first four bits are $1111$, the zero count is $k-m$ and the correct count is zero. Thus the rowwise coefficients dominate respectively
$(-u-2m,u,-m)$ on class $3$, $(-v-2m,v,-m)$ on class $4$, $(-2m,0,-m)$ later, and $(-m)$ at the terminal, while its actual early coefficients dominate $(k-2m,-k,-m)$. Multiplication by arbitrary nonnegative $A,C,P,T$ and summation first gives
$k\Delta_O(V)\ge u\beta_3+v\beta_4-k(\beta_1+\beta_2)-m\mathcal S(V)$. Only now use $\beta_1=\beta_2=0$ and $\mathcal S(V)=B$ on the fiber to obtain $k\Delta_O(V)\ge ug+vh-mB$. Since $\Delta_N\ge\Delta_O$, the six bundles yield all six nonzero terms in (214.3), and the anchor gives the term $0$.

It remains to attain the bound with one score. Use the following eight scores, all padded by ones to length $L$; omitted rows are zero and coincident rows add:

$$
\begin{array}{c|c|c|c|c}
\text{score}&(g,h,d,B)&C\text{-atoms}&P\text{-atoms}&T\\\hline
U&(1,0,0,3)&1101:1&0101:1,1001:1&1\\
V&(0,1,0,2)&1110:1&0110:\tfrac12,1010:\tfrac12,1100:\tfrac12&\tfrac12\\
Z&(1,1,0,4)&1101:1,1110:1&0100,0101,0110,1000,1001,1010:\tfrac12&1\\
X&(2,1,1,3)&1100:1,1101:1,1110:1&0100,0101,1000,1001:\tfrac12&1\\
Y&(2,3,1,6)&1100:2,1110:3&0100,0110,1000,1010:1&2\\
Z_3&(3,3,1,8)&1100:3,1110:3&0100:2,0110:1,1000:2,1010:1&2\\
E_3&(1,0,1,0)&1101:1&-&0\\
E_4&(0,1,1,0)&1110:1&-&0
\end{array}
$$

Here $1101$ has zero set $\{3\}$. In pair order $12,13,14,23,24,34$, the exact $N$ cell maxima, in cell order $00,01,10,11$, are

$$
\begin{array}{c|cccccc}
 &12&13&14&23&24&34\\\hline
U&(0,1,1,1)&(1,0,1,1)&(0,1,0,2)&(1,0,1,1)&(0,1,0,2)&(0,2,0,1)\\
V&(0,\tfrac12,\tfrac12,1)&(0,\tfrac12,\tfrac12,1)&(\tfrac12,0,1,\tfrac12)&(0,\tfrac12,\tfrac12,1)&(\tfrac12,0,1,\tfrac12)&(\tfrac12,0,1,\tfrac12)\\
Z&(0,\tfrac32,\tfrac32,1)&(1,\tfrac12,1,\tfrac32)&(1,\tfrac12,1,\tfrac32)&(1,\tfrac12,1,\tfrac32)&(1,\tfrac12,1,\tfrac32)&(1,1,1,1)\\
X&(0,1,1,2)&(1,0,2,1)&(\tfrac12,\tfrac12,1,\tfrac32)&(1,0,2,1)&(\tfrac12,\tfrac12,1,\tfrac32)&(1,1,1,1)\\
Y&(0,2,2,3)&(1,1,2,3)&(2,0,3,2)&(1,1,2,3)&(2,0,3,2)&(2,0,3,2)\\
Z_3&(0,3,3,3)&(2,1,3,3)&(3,0,3,2)&(2,1,3,3)&(3,0,3,2)&(4,0,3,2)
\end{array}
$$

The anchors are $3,2,4,3,6,8,0,0$ for $U,V,Z,X,Y,Z_3,E_3,E_4$. Consequently the pair excess vectors are zero for $U,V,Z$,
$(1,1,\tfrac12,1,\tfrac12,1)$ for $X$,
$(1,1,1,1,1,1)$ for $Y$, and $(1,1,0,1,0,1)$ for $Z_3$.
Each raw ray $E_3,E_4$ has one unit correct atom and no anchor; exactly one cell can collect it under any schedule, so every pair has excess $1$.
These maxima follow by summing, in each cell $E$,

$$
\max\left\{\sum_E P+T\mathbf1_{1^L\in E},\
        \max_{1\le\ell\le L}\sum_{E\cap\Omega_\ell}(C+P)\right\}.
$$

Thus earlier and unqueried labels are included. Every empty or singleton observation is a coarsening of an active $N$ pair. Every address above four is constantly one on these scored words, and every label above four has zero reward. Reversals permute $N$ cells and repetitions give singleton information. These facts bound every full $N$ schedule, and hence every $O$ schedule, by the listed anchor plus $d$ for every $L\ge4$.

Put $F_1=3g-3d$, $F_2=g+2h-2d$, $F_3=3g+h-4d$, $F_4=2g+2h-4d$, $F_5=(4g+3h-5d)/2$, and $F_6=3(g+h-d)/2$. For any branch attaining the maximum $B_*$, the following single conic sums reproduce $(g,h,B_*)$ and have excess at most $d$:

$$
\begin{array}{c|l}
0&gE_3+hE_4\\
F_1&(g-d-h)U+(d-h)E_3+hX\\
F_2&(h-d-g)V+(d-g/2)E_4+(g/2)Y\\
F_3&t=(h+d-g)_+:\ (g-h-d+t)U+(h-d-2t)Z+(d-t)X+tZ_3\\
F_4&t=(g+d-h)_+:\ (h-g-d+t)V+(g-2d-t)Z+(d-t)Y+tZ_3\\
F_5&((3d-h)/2)X+((3d+h-2g)/2)Y+(g-2d)Z_3\\
F_6&t=(h-d)_+/2,\ s=(g+h-d)/2:\ (d-h+2t)E_3+((h-g+d)/2-t)E_4+(s-2t)X+tY
\end{array}
$$

A maximum of the seven real affine forms always exists. The zero branch gives $g+h\le d$ by $F_6\le0$. On any other maximizing branch, comparisons with the other six forms give the following bounds, valid also at ties: the $F_1$ branch gives $d\ge h$ and $g\ge d+h$; $F_2$ gives $d\ge g/2$ and $h\ge d+g$; $F_3$ gives $h\ge d$, $g\ge h$, $2g\ge h+3d$ and $0\le t\le\min(d,(h-d)/2)$; $F_4$ gives $g\ge2d$, $h\ge g$, $h\ge3d$ and $0\le t\le\min(d,g-2d)$; $F_5$ gives $g\ge2d$, $h\le3d$, $2g\le3d+h$; and $F_6$ gives $d\ge|g-h|$, $g\le2d$, $g+h\ge d$ and $0\le t\le\min(s/2,(h-g+d)/2)$. These inequalities make every displayed coefficient nonnegative. Substitution of the generator tuples gives $(g,h,B_*)$ and total weighted allowance $d$ in each nonzero branch; the zero branch has allowance $g+h\le d$. Thus the cases cover all real parameters, not only interior cones. For example $(g,h,d)=(4,2,1)$ selects $F_3=10$ and gives $U+Z+X$, with quotient late coordinates $(4,2)$, stock $10$ and allowance $1$. A sum of scores has support at most the sum of supports, while its anchor is linear, so the one conic sum has excess at most $d$; it is one score on one carrier, not several separately funded scores. If $B>B_*$, add $B-B_*$ to $T$; the anchor rises by $B-B_*$ and each table reward rises by at most that amount, so the excess cannot increase. Exact support increase or preservation of excess is not needed. Taking $d=\Phi(g,h,B)$ and combining with the lower bounds proves (214.4)--(214.5), including all ties and zero endpoints. $\square$

**Corollary 214.6 (one-budget exact certificate).** If a full unit-$O$ input has quotient in this fiber, Theorem 214.5 gives one exact-$Q$ score with $\theta=0$ and $\Delta_N=\Phi\le\Delta_O\le1$. For a signed target outside the fiber it gives only the sufficient residual test

$$
\Phi(g,h,B)+\max\{0,\sigma_{H_L}(q-q_2(g,h,B))\}\le1,
\tag{214.6}
$$

where $q_2(g,h,B)=(0,0,g,h,0,\ldots,0;g+h+B)$ and $g,h,B\ge0$ are the same parameters as in Definition 214.4. The second term is one residual charged to the same budget. It does not license adding separately affordable fibers.

**Proposition 214.7 (an explicit same-seed continuous companion).** Let
$s\in[5/11,5/9]$ and $e=2s/5$. For a finite $L\ge4$ set

$$
b=(1-s/5,6s/5,6s/5,s,e,\ldots,e).
$$

There are four distinct objects in this construction. The deterministic anchor kernel is $R=(1,2;1,2,0)$. The nonnegative dual score $V_\star$ has
$C_{1100}=C_{1101}=C_{1110}=1$, $P_{0101}=P_{1000}=1$, $T=1$, with positive padding and every other row zero. The conic acquisition measure is

$$
\lambda_s=\frac{s}{5}\bigl[\delta_{(13;130)}+\delta_{(13;134)}+
\delta_{(23;030)}+\delta_{(23;034)}+\delta_{(34;040)}\bigr],\qquad
M=\lambda_s(\mathcal D_O)=s.
$$

Finally the normalized probability-vector kernel is

$$
p_s=(1-s)p_R+\sum_D\lambda_s(D)p_D.
\tag{214.7}
$$

Here $(ij;xyz)$ is a deterministic stopped table with schedule $(i,j)$ and outputs $(x,y,z)$ in cells $0,10,11$, and $p_D$ is its output law. The nonnegative weights in (214.7) sum to one. One source-independent uniform seed selects the entire table before any answer, by a partition of $[0,1)$ into these six weights. The $O$ rule stops at its first queried zero; its $N$ completion obtains both preselected replies and ignores any reply not used by the stopped table. These use the same seed and output the same original mark, with at most two actual requests and finite handoff.

**Proof.** For first-zero classes $1,2,3,4$, the correct probabilities and the minima of the base and independent pair probabilities over every word in the class are

$$
\begin{array}{c|cccc}
 &1&2&3&4\\\hline
p_s(n)&1-3s/5&1-s&4s/5&3s/5\\
\min p_s(0)&s/5&3s/5&1-4s/5&1-3s/5\\
\min[p_s(0)+p_s(n)]&1-2s/5&1-2s/5&1&1\\
\text{correct slack}&0&1-9s/5&0&0\\
\text{base slack}&2s/5&11s/5-1&4s/5&4s/5
\end{array}
$$

The last two rows subtract $b_n-e$ and $1-b_n-e$, respectively. To obtain the table, evaluate the five stopped outputs on the first four bits; every suffix gives the same outputs, so multiple-zero suffixes are unrestricted. The two potentially restrictive slacks are nonnegative exactly when $5/11\le s\le5/9$. Pair demand is $1-e$ and positive-word base mass is $1-e$. The first base demand is $-s/5$, retained without truncation. For $n>4$, all first four replies are one: correct probability is zero, base and pair probabilities are $1-e$, with $b_n=e$. Thus every independent finite cap row holds, including both closed endpoints.

The conic measure has event matrix
$G_{\mathcal C}\lambda_s=z_{p_s}-r$ because $M=s$, $r=z_R$, and
$z_{p_s}=(1-s)r+\sum_D\lambda_s(D)z_D$, where $z_{p_s}$ is the complete event vector of the normalized kernel $p_s$.
Therefore the same full measure satisfies $G_O\lambda_s\ge h(b,e)$ and, after completion of its tables, $G_N\lambda_s\ge h(b,e)$.
Also

$$
\sum_{j=3}^Lb_j-(L+1)e=s/5,\qquad
b_1+\sum_{j=3}^Lb_j-(L+1)e=1.
$$

The remaining order conditions in $H_L$ follow from $s\le5/9$; hence $(b,e)\in H_L$ and this same feasible $\lambda_s$ establishes $(b,e)\in H_N$.

For the separate score, $Q(V_\star)=(0,0,2,1,0,\ldots,0;6)$ and $W_{V_\star}=3$. Its exact $N$ pair supports, in order $12,13,14,23,24,34$, are $(4,4,3,4,4,4)$; its stopped pair supports are the same. Short and inactive-address schedules have no larger support, by the all-label cell formula and coarsening. Thus both costs are $1$. Weak duality with this score and the very same $\lambda_s$ gives

$$
F_{Q(V_\star)}(b,e)=2b_3+b_4-6e=s=M,
\qquad \rho_N(b,e)=\rho_O(b,e)=s.
$$

This is conic attainment; $V_\star$ is not a probability kernel and $\lambda_s$ is not normalized by itself.

For the actual marked targets take
$a_1=1-s/5$, $a_2=a_3=6s/5$, $a_4=s$ and
$a_n=e2^{-(n-5)}$ for $n\ge5$. This is a positive monotone vanishing sequence, with strict active length four at cap $e$ and $a_5=e$. Execute the normalized mixture on the original prime queries and return its original marks. Every actual $n>4$ has law $(1-e)\delta_{\theta_0}+e\delta_{\theta_4}$, so the exact tail error is $\max(e,a_n)=e$, including $a_5=e$. Theorem 110.2 supplies the original closed-cap correspondence with arbitrary-address and full-carrier competitors under its selected-law hypotheses. Active-four cap feasibility is already Theorem 96.2; this companion records explicit same-$\lambda$ conic attainment in that regime and is not a separator or an arbitrary-position relabelling. $\square$

### 214.3. Balanced equal triple

**Theorem 214.8 (balanced three-late full-fiber minimum).** Let $L\ge5$, $c,g,B\ge0$, and

$$
q=(c,c,g,g,g,0,\ldots,0;2c+3g+B).
$$

Among all nonnegative full exact-$Q$ scores, including arbitrary $A$, early and late $P$, classwise cancellations, changed anchors, suffixes and all legal labels,

$$
\min\Delta_N=\min\Delta_O=
D(c,g,B):=\max\left\{0,g-B,3g-2c-B,
\frac{4g-5c-B}{3},\frac{4g-\frac92c-B}{4}\right\}.
\tag{214.8}
$$

One score attains both minima. Equivalently, the least stock at allowance $d$ is

$$
\Phi_3(c,g,d)=\max\left\{0,g-d,3g-2c-d,4g-5c-3d,
4g-\frac92c-4d\right\}.
\tag{214.9}
$$

The theorem includes $c=0$, $g=0$, $B=0$, all ties and zero-cost cores. It covers only equal early credits and equal late totals at fixed addresses $3,4,5$.

**Proof.** Use four stopped detector bundles. The notation $(i,j;x,y,z)$ is as above. Bundle A is $(1,2;1,2,3)$ together with half each of
$(1,3;1,3,0),(1,4;1,4,0),(2,3;0,3,0),(2,4;2,4,0),(3,4;0,4,0),(4,5;0,5,0)$; its total weight is $4$. Bundle B is
$(1,3;1,3,0)+(2,3;0,3,0)+(3,4;0,4,5)$, of weight $3$. Bundle C is $(3,4;3,4,5)$, of weight $1$. Bundle D is $(1,2;1,2,5)$, of weight $1$.

For a bundle of weight $m$, let $N_0(w),N_n(w)$ be its weighted counts of output zero and actual first-zero label $n$. The row coefficients are
$(N_0-m\mathbf1_{n\ge3},N_n-m\mathbf1_{n\le2},N_0+N_n-m)$ and the terminal coefficient is $N_0-m$. Direct substitution on each suffix gives the following minima, in class order $1,2,3,4,5,n\ge6$, followed by the terminal row:

$$
\begin{array}{c|rrrrrr|r}
 &1&2&3&4&5&n\ge6&T\\\hline
A&(1,-2,-1)&(3/2,-5/2,-1)&(-3,2,-1)&(-5/2,3/2,-1)&(-3/2,1/2,-1)&(-1,0,-1)&-1\\
B&(1,-2,-1)&(2,-3,-1)&(-2,2,0)&(-1,1,0)&(-1,1,0)&(-1,0,-1)&-1\\
C&(0,-1,-1)&(0,-1,-1)&(-1,1,0)&(-1,1,0)&(-1,1,0)&(-1,0,-1)&-1\\
D&(0,0,0)&(0,0,0)&(-1,0,-1)&(-1,0,-1)&(-1,1,0)&(-1,0,-1)&-1
\end{array}
$$

For a proposed right side $v\cdot\beta-K$, its row coefficients are $(-v_n-1,v_n-1,-1)$ and $-1$ at $T$. The displayed minima dominate the corresponding rows, so multiplying by the actual nonnegative score and summing gives

$$
\begin{aligned}
4\Delta_O&\ge-\beta_1-\tfrac32\beta_2+3\beta_3+\tfrac52\beta_4+\tfrac32\beta_5-K,\\
3\Delta_O&\ge-\beta_1-2\beta_2+3\beta_3+2\beta_4+2\beta_5-K,\\
\Delta_O&\ge2\beta_3+2\beta_4+2\beta_5-K,\\
\Delta_O&\ge\beta_1+\beta_2+\beta_3+\beta_4+2\beta_5-K.
\end{aligned}
$$

Substitution of $q$ gives the four nonzero branches in (214.8); the anchor gives $0$. The inequalities apply to $N$ because $\Delta_N\ge\Delta_O$.

For attainment use the following seven scores on length-five words, padded by ones for larger $L$; the entries are `word:weight`, with literal $0$ denoting a zero answer and positive padding by ones; $A=0$ throughout:

$$
\begin{array}{c|c|l|l|c}
& (c,g,d,B)&C\text{-atoms}&P\text{-atoms}&T\\\hline
Z&(0,2,0,8)&11001:2,11101:2,11110:2&01001,01010,01100,10001,10010,10100:1&2\\
U&(2,5,0,11)&01000:2,10000:1,10110:1,11000:4,11010:1,11100:5,11110:5&00010:1,00100:1,01000:1,10000:3&5\\
V&(2,8,1,19)&00101:1,01000:1,10100:1,10110:1,11000:5,11001:1,11010:2,11100:7,11101:1,11110:8&00100:1,00110:1,01000:2,01010:1,01100:1,10000:3,10001:1,10010:1,10100:1&7\\
X&(0,2,1,5)&11000:1,11010:1,11100:2,11110:2&01000:1,01110:1,10010:1,10100:1&1\\
H&(1,1,0,1)&00000:1,10000:1,11000:1,11100:1,11110:1&-&1\\
J&(1,1,1,0)&00000:1,10000:1,11000:1,11100:1,11110:1&-&0\\
K&(0,1,3,0)&11000:1,11100:1,11110:1&-&0
\end{array}
$$

In the $V$ row, the compact list means weights $1$ on the first four displayed $C$ words, then weights $5,1,2,7,1,8$ on the remaining six; the compact list in its $P$ column means weights $1,1,2,1,1,3,1,1,1$ in the displayed order. In particular $U$ has $K=30$, stock $11$ and anchor $15$, while $V$ has $K=47$, stock $19$ and anchor $23$. The corresponding anchors are $8,15,23,5,3,2,0$ in the order
$Z,U,V,X,H,J,K$. For every score, direct use of the cell formula

$$
\max\left\{\sum_{E}P+T\mathbf1_{1^L\in E},
       \max_{1\le\ell\le L}\sum_{E\cap\Omega_\ell}(C+P)\right\}
$$

on all ten pairs $(12),(13),(14),(15),(23),(24),(25),(34),(35),(45)$ gives support at most the listed anchor plus the listed $d$: the pair supports for $Z,U,V,X,H,J,K$ are respectively

$$
(8^{10}),\quad(15^{10}),\quad(24,24,24,24,24,24,23,24,23,24),
(6,6,6,5,6,6,5,6,5,5),
(3^{10}),\quad(3,3,3,2,3,3,2,3,2,2),
(1,2,2,1,2,2,1,3,2,2).
$$

Here $(a^{10})$ denotes ten repeated entries equal to $a$. The maximum over empty and singleton schedules is respectively $8,13,21,5,2,2,2$ for $Z,U,V,X,H,J,K$, also below the same bounds. Addresses above five are constant one on the scored support and labels above five have zero reward, while reversals and repetitions coarsen or permute these cases. Thus these are full-catalog bounds, not a selected-table check.

For the real-parameter proof, normalize by $g>0$ and write $x=c/g$, $y=d/g$. The normalized seed points are

$$
Z=(0,0),\quad U=(2/5,0),\quad V=(1/4,1/8),\quad X=(0,1/2),
\quad H=(1,0),\quad J=(1,1),\quad K=(0,3).
$$

For $x,y\ge0$, comparison of the five affine stock forms gives exactly the following regions; boundary overlaps are allowed:

$$
\begin{array}{c|l|l}
\text{active stock}/g&\text{region}&\text{vertices or boundary}\\\hline
4-\frac92x-4y&y\le x/2,\quad5x+6y\le2&ZUV\\
4-5x-3y&y\ge x/2,\quad3x+2y\le1&ZVX\\
3-2x-y&x\le1,\quad5x+6y\ge2,\quad3x+2y\ge1,\quad2x+y\le3&XVUHJK\\
1-y&x\ge1,\quad0\le y\le1&HJ\text{ and increasing }x\\
0&y\ge\max(1,3-2x)&KJ\text{ and }y\ge1\text{ for }x\ge1
\end{array}
$$

For example the first two forms differ by $x/2-y$, and their differences from $3-2x-y$ are $1-5x/2-3y$ and $1-3x-2y$; the difference between $3-2x-y$ and $1-y$ is $2-2x$. These comparisons give the table, including its unbounded regions, and any maximum lies in at least one listed region. The polygon is convex and is partitioned by the four triangles $XVU$, $XUH$, $XHJ$, $XJK$, whose interiors are disjoint. This proves the entire face-fan cover.

On a bounded triangle let $\lambda_i\ge0$, $\sum_i\lambda_i=1$, be its barycentric coordinates at $(x,y)$. If seed $i$ has parameters $(c_i,g_i,d_i,B_i)$, use the single score

$$
V=g\sum_i\frac{\lambda_i}{g_i}V_i.
$$

Its early coordinates are $c$, its three late coordinates are $g$, and its stock is
$g\sum_i\lambda_i B_i/g_i=\Phi_3(c,g,d)$, because each vertex stock lies on that region's same affine form. Its total weighted cost allowance is
$g\sum_i\lambda_i d_i/g_i=gy=d$. Linearity of the anchor and subadditivity of full support give $\Delta_N(V)\le d$, with one common allocation. The formulas agree on shared faces by their parameter identities; no choice at a tie loses coverage.

On the strip use $g[(1-y)H+yJ]$, then add correct mass $c-g$ to a singleton word in each early class. The added reward of every table is at most $2(c-g)$, exactly the anchor increment, so excess cannot increase. The stock is $g-d$. In the zero-stock region with $x\le1$, use $g[(1-x)K+xJ]$; it has early total $c$, late total $g$ and cost allowance $g(3-2x)\le d$. For $x\ge1$, use $gJ$ plus the same early additions; its allowance $g\le d$ suffices. When $g=0$, early correct singleton rows of mass $c$ and terminal stock give zero excess directly.

For a prescribed $B\ge\Phi_3(c,g,d)$ add $B-\Phi_3(c,g,d)$ to $T$. Every table reward increases by at most the anchor increment, so excess cannot increase. For example $J$ has excess $1$ at $T=0$ and excess $1/2$ after adding $T=1/2$; preservation of excess is not assumed. Take $d=D(c,g,B)$, for which all five stock inequalities give $B\ge\Phi_3(c,g,d)$. The lower bounds and this one-score construction prove (214.8). $\square$

**Corollary 214.9 (balanced residual and amplitude consequence).** For every actual full unit-$O$ input $y$ with $Q(y)=q(c,g,B)$, Theorem 214.8 supplies one score $V$ with $Q(V)=Q(y)$ and $\Delta_N(V)=D(c,g,B)\le\Delta_O(y)\le1$, hence a one-score, one-budget exact-$Q$ certificate with $\theta=0$. Pairing with the same complete feasible $\lambda$ of mass $M$ for any $b\in H_N$ gives $F_{Q(y)}(b)\le M D\le M\le\max(1,M)$. In general, an exact-$Q$ unit certificate with $\theta=0$ exists if and only if $D(c,g,B)\le1$. For another signed quotient $q$, choosing $c,g,B$ with

$$
D(c,g,B)+\max\{0,\sigma_{H_L}(q-q(c,g,B))\}\le1
\tag{214.10}
$$

is only a sufficient one-residual test. Pairing the same complete feasible $\lambda$ of mass $M$ gives
$F_q\le M D+\theta\le\max(1,M)$. For an actual original hard-two attainer at active length at least five, the transported rows imply the necessary amplitude inequality

$$
 c(a_1+a_2)+g(a_3+a_4+a_5)
 \le 2c+D(c,g,B)+(2c+3g+B)\varepsilon .
\tag{214.11}
$$

Unequal early credits, unequal or signed triples, arbitrary replacement positions, and larger positive late domains remain outside this theorem.

### 214.4. A necessary six-coordinate projection and fixed-lift diagnostics

**Definition 214.10 (six-coordinate slice).** Fix ordered late addresses
$j_1<j_2<j_3<j_4<j_5<\ell$, five equal correct totals $g$ and a sixth total $h$ with $0\le h\le g$, and cap parameter $d\ge0$. Stay in the input slice $A=0$, $E=0$, with $E=\gamma_1+\gamma_2$, $\gamma_j=\sum_{\Omega_j}C_w$, and $P$ supported on $\Omega_1\cup\Omega_2$, including the early prefix $00$. Other correct coefficients may be present, but the displayed endpoint measures set all unlisted coefficients to zero. Define

$$
\begin{aligned}
z_i&=1-w_{j_i},\quad j_6=\ell,\quad\text{so }z_i=1\text{ exactly when the selected answer is zero},\\
S&=\nu(\{0,1\}^6),\qquad m_i=\int z_i\,d\nu,\qquad
D_{ij}=\int(1-z_i)z_j\,d\nu,\\
\nu&\text{ is the one common late projection of the full early-pair measure},\qquad \nu(\{0,1\}^6)=S,\\
\nu&\text{ is a proof measure, not a source distribution},\\
u&=(g-d)_+,\qquad v=(h-d)_+.
\end{aligned}
$$

Thus $0\le v\le u$. The stock in this theorem is one stock $B=S+T$.

**Theorem 214.11 (directed six-coordinate stock envelope).** Every complete score in this slice with $\Delta_O\le d$ satisfies

$$
T\ge u,\qquad
S\ge\max\left\{\frac{13u}{4},\frac{22u+v}{7}\right\},\qquad
B\ge u+\max\left\{\frac{13u}{4},\frac{22u+v}{7}\right\}.
\tag{214.12}
$$

This is a necessary projection statement. It is not a full-fiber minimum and does not assert that an endpoint lift is affordable at cost $d$.

**Proof.** The legal head table $(1,2;1,2,j_1)$ has reward at least $S+g$, against anchor $S+T$, and therefore gives $T\ge g-d$. Combining this with $T\ge0$ gives $T\ge(g-d)_+=u$, also when $g<d$. For each selected late class $j$, the two legal tables $(1,j;0,j,0)$ with the two early addresses have disjoint pair-loss sets, both contained in the selected zero cylinder. Each loss is at least $(\gamma_j-d)_+$, so

$$
 m_i\ge2u\ (i\le5),\qquad m_6\ge2v.
\tag{214.13}
$$

The legal late/late table $(j_i,j_k;0,j_k,0)$ gives
$D_{ik}\ge u$ for $1\le i<k\le5$, and $(j_i,\ell;0,\ell,0)$ gives $D_{i6}\ge v$. These are lower bounds from one full score and the same common measure; no independently funded projection is introduced. The underlying full catalog retains its independent base rows; this slice fixes their score coefficients $A$ to zero.

For the first cut put

$$
P_4(z)=2z_1+z_2+\sum_{1\le i<j\le4}(1-z_i)z_j+(1-z_4)z_5.
$$

If $k=z_1+z_2+z_3$, then for $z_4=1$ it equals
$3+(3k-k^2)/2$, and for $z_4=0$ it equals $(5k-k^2)/2+z_5$; each is at most $4$. Integrating and using (214.13) gives
$4S\ge2m_1+m_2+\sum_{i<k\le4}D_{ik}+D_{45}\ge13u$.

For the second cut put

$$
P_6(z)=3z_1+2z_2+z_3+
\sum_{1\le i<k\le5}(1-z_i)z_k+(1-z_5)z_6.
$$

With $k=z_1+z_2+z_3+z_4$, if $z_5=0$ then
$P_6=(7k-k^2)/2+z_6$, and if $z_5=1$ then
$P_6=4+(5k-k^2)/2$. For $k=0,1,2,3,4$ both expressions are at most $7$. Hence

$$
7S\ge3m_1+2m_2+m_3+\sum_{1\le i<k\le5}D_{ik}+D_{56}
\ge22u+v.
$$

The two inequalities use the same $\nu$, so adding two separately attainable stocks is not occurring. This proves (214.12). $\square$

**Proposition 214.12 (exact projection endpoints).** In the single common Boolean projection cone defined by

$$
 m_i\ge2u (i\le5),\quad m_6\ge2v,\quad
 D_{ik}\ge u\ (i<k\le5),\quad D_{i6}\ge v,
\tag{214.14}
$$

one has $\min S=13u/4$ when $v=3u/4$ and $\min S=23u/7$ when $v=u$, with equality at the following measures. The displayed masses already include their factor $u$.

For $v=3u/4$, put mass $u/4$ on each of

$$
001111,010111,011011,011101,011110,100111,101011,101101,101110,
110010,110101,110110,111011.
$$

Then

$$
S=13u/4,\quad m=(2,2,2,9/4,5/2,9/4)u,
$$

all $D_{ik}=u$ for $i<k\le5$, and
$(D_{16},D_{26},D_{36},D_{46},D_{56})=(1,1,3/4,3/4,3/4)u$.

For $v=u$, put mass $2u/7$ on

$$
001111,010111,011011,011101,100111,101011,101101,110011,110101
$$

and mass $u/7$ on

$$
011110,101110,110110,111011,111101.
$$

Then

$$
S=23u/7,\quad m=(2,2,2,16/7,16/7,20/7)u,
$$

all high-high $D_{ik}=u$, and
$(D_{16},D_{26},D_{36},D_{46},D_{56})=(8/7,8/7,8/7,1,1)u$.

At $u=0$ one has $v=0$ and the zero measure attains zero. The inequalities from $P_4$ and $P_6$ prove the lower endpoints; the displayed moments verify feasibility and equality, so both are exact projection minima. All inequalities are closed and scaling by arbitrary $u\ge0$ preserves them.

**Proof.** The mass totals are $13u/4$ and $9(2u/7)+5(u/7)=23u/7$. Counting each bit and each directed pair gives the displayed vectors; the high-high and low-directed counts are immediate from the lists. Thus (214.14) holds, while the two cut inequalities force the stated lower values. $\square$

**Proposition 214.13 (canonical lift and fixed-method failures).** Lift either endpoint on one actual early-pair carrier: an atom $z$ of $\nu$ supplies half its mass to each raw word with early prefix $01$ and $10$, selected answers $w_{j_i}=1-z_i$ and inactive answers one. Write $\widetilde\nu$ for the resulting measure on all late raw answer coordinates, of mass $S$. For each selected correct class $n=j_i$ and $0\le r<\gamma_n$, put every bit before $n$ to one, bit $n$ to zero, and every later bit $k$ to one exactly when

$$
 r<a_{nk},\qquad
 a_{nk}=\widetilde\nu\{w_n=0,w_k=1\},\qquad
 a_{j_i j_k}=\nu\{z_i=1,z_k=0\}\quad(i<k).
\tag{214.15}
$$

Put at each resulting correct word its interval length in $r$, add coincident words, and keep $T=1$. This is the threshold construction (203.9)–(203.10). Its correct totals are $\gamma_n$; its early-pair projection, hence every $m_i,D_{ik}$, is the original $\nu$. The threshold $a_{j_i j_k}=m_i-m_k+D_{ik}$ is distinct from the directed loss $D_{ik}$. There is one score and one stock. At both specified endpoints $\mu=\max\gamma_n=2>T=1$, so the protected-terminal equality in Theorem 203.2 is unavailable.

For the first endpoint, take $u=d=1$, $g=2$, $h=7/4$, $T=1$. Then

$$
S=13/4,\quad W=17/4,\quad B_N=B_O=6,\quad
\Delta_N=\Delta_O=7/4.
\tag{214.16}
$$

At the $(j_4,j_5)$ schedule the $N$ cell maxima are
$(3/2,3/4,2,7/4)$ and the $O$ maxima are $(9/4,2,7/4)$. The maxima within the other schedule classes are empty/singleton $17/4$, early pair $21/4$, early/high $45/8$, early/low $39/8$, and late pair $6$; individual supports are given in the complete table below.

For the second endpoint, use $u=d=1$, $g=h=2$, $T=1$. The fourteen atoms are the nine mass-$2/7$ strings

$$
001111,010111,011011,011101,100111,101011,101101,110011,110101
$$

and the five mass-$1/7$ strings

$$
011110,101110,110110,111011,111101.
$$

The lift has

$$
S=23/7,\quad W=30/7,\quad B_N=B_O=44/7,
\qquad\Delta_N=\Delta_O=2.
\tag{214.17}
$$

At $(j_4,j_5)$ the $N$ maxima are $(9/7,1,2,2)$ and the $O$ maxima are $(16/7,2,2)$. The remaining full support maxima are empty/singleton $30/7$, early pair $37/7$, early/high $79/14$, early/low $34/7$, and late pair $44/7$; every high-high pair except $(j_4,j_5)$ has support $6$, the pairs $(j_i,\ell)$ for $i\le3$ have $36/7$, and $(j_4,\ell),(j_5,\ell)$ have $37/7$.

**Proof of the lift calculations.** In selected-pair order
$12,13,14,15,16,23,24,25,26,34,35,36,45,46,56$, the thresholds $a_{j_i j_k}=m_i-m_k+D_{ik}$ of the two endpoints are respectively

$$
\begin{aligned}
a^{(1)}&=(1,1,3/4,1/2,3/4,1,3/4,1/2,3/4,3/4,1/2,1/2,3/4,3/4,1),\\
a^{(2)}&=(1,1,5/7,5/7,2/7,1,5/7,5/7,2/7,5/7,5/7,2/7,1,3/7,3/7).
\end{aligned}
$$

For each selected class split $[0,\gamma_n)$ at these thresholds, clipped to that interval. On each subinterval the raw correct word is constant and its coefficient is the subinterval length. In each catalog cell $E$, maximize

$$
\max\left\{\sum_E(A+P)+T\mathbf1_{1^L\in E},\
       \max_{1\le a\le L}\sum_{E\cap\Omega_a}(C+P)\right\}.
$$

This includes every earlier and unqueried label. The resulting support totals for both $N$ and $O$ are in the following complete schedule-class table. Here $a\in\{1,2\}$ is an early address and $i,k$ are selected-index positions, not raw answer bits.

$$
\begin{array}{c|cc}
\text{schedule class}&\text{first endpoint}&\text{second endpoint}\\\hline
\varnothing\text{ or any active singleton}&17/4&30/7\\
(1,2)&21/4&37/7\\
(a,j_i),\ 1\le i\le4&45/8&79/14\\
(a,j_5)&43/8&79/14\\
(a,\ell)&39/8&34/7\\
(j_i,j_k),\ 1\le i<k\le3&6&6\\
(j_i,j_4),\ 1\le i\le3&6&6\\
(j_i,j_5),\ 1\le i\le3&23/4&6\\
(j_4,j_5)&6&44/7\\
(j_i,\ell),\ i=1,2&5&36/7\\
(j_3,\ell)&21/4&36/7\\
(j_i,\ell),\ i=4,5&21/4&37/7
\end{array}
$$

For example at $(j_4,j_5)$ the first lift has raw pair-cell masses
$(3/2,3/4,1,0)$. Its correct class $j_5$ gives $2$ in cell $10$ and the unqueried class $\ell$ gives $7/4$ in cell $11$, yielding the displayed four maxima. The merged stopped cell $0$ collects $9/4$. At the second endpoint the pair masses are $(9/7,1,1,0)$; the four maxima are $(9/7,1,2,2)$ and the merged zero-cell maximum is $16/7$. Thus the largest entries in the table are attained, giving (214.16) and (214.17).

At each endpoint $m_i\ge\gamma_{j_i}$. For an inactive address $k>j_i$ the raw projection has $w_k=1$ throughout, so $a_{j_i k}=m_i\ge\gamma_{j_i}$ and the threshold construction also keeps that bit one. Inactive bits before a correct class are one by construction. Thus all gap and padding coordinates are one on every scored word; their queries coarsen to one of the listed empty, singleton or pair observations. Their output labels have zero reward, while all active labels were already included in every cell maximum. Reversed $N$ pairs permute cells; repetitions provide singleton information, with the actual requests still counted. This proves the full-catalog bounds for arbitrary ordered selected late addresses, including gaps.

These are fixed-lift calculations, not lower bounds against every exact-$Q$ representative. Both lifts exceed $d=1$ and therefore are not affordable full scores, acquisition laws, universal obstructions, or original separators. $\square$

The endpoint atoms may be embedded into actual finite source words by the finite-pattern supplier for the original prime-divisibility source. The weights are proof weights, not a source distribution. For a full score in the slice with $\Delta_O\le d$, first discard every unselected late $C$ row, retaining all $P,T$ and the six selected correct classes. The anchor $W=B=S+T$ is unchanged and every table reward, hence full support, can only decrease. If the removed correct mass is $G_{\rm out}$, the original charge $K=5g+h+G_{\rm out}+B$ becomes exactly $K^\sharp=5g+h+B$; one cannot remove its amplitude contribution while silently retaining or dropping its charge. Pair the resulting score with an actual normalized cap-feasible $O$ acquisition transported by Theorem 110.2. Its complete rows give expected reward at least
$W+g\sum_{r=1}^5a_{j_r}+ha_\ell-K^\sharp\varepsilon$,
while its support is at most $W+d$. Consequently

$$
 g\sum_{r=1}^{5}a_{j_r}+h a_\ell
 \le d+(5g+h+B)\varepsilon,
\tag{214.18}
$$

for the selected active addresses. This implication is conditional on the existence of the full score and acquisition; the projection endpoint by itself supplies neither.

### 214.5. Source bridge, literature correspondence, and limits

All four statements use the original source and resource contract. The source is

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\quad
N(r,g)=1+F_rg,\quad q_i=\mathbf1_{p_i\mid N(r,g)},
$$

with $n(x)$ the first absent prime. Every finite answer word has an actual source witness. The full Borel carrier is $\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$ with the unchanged consumer (unknown on $B_j$, proposing $j$ on $P_j$), and the marks are $\theta_j=(B_1,1/(j+2))$. The original nonatomic family $\mu_x$ remains exactly the family specified in Definition 213.22 and Source-Correlated Laws 67.5; neither its carrier nor its consumer is replaced. Separately, following 73.1 and 110.1, choose the marked laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\to0.
$$

There is no distribution on source labels. There is zero advice, one source-independent common seed, sourcewise almost-sure finite handoff, arbitrary addresses, arbitrary full-carrier outputs, and at most two actual requests, including repetitions and ignored replies. An $N$ rule preselects its schedule and obtains its replies; an $O$ rule preselects an increasing schedule and stops at its first queried zero or exhaustion. The actual finite table is selected before answers by the common seed. Its original tape output is then transported with the measurable finite-mark projection. For active length $L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$, every actual tail source $n>L_a$ obeys the exact identity

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
=\max\{1-p_{1^{L_a}}(0),a_n\},
\tag{214.19}
$$

including the closed equality $a_n=\varepsilon$. Theorem 109.1 is used only for its normalized degree-two stopped-kernel criterion $c\ge H$ together with its common scalar condition $\beta\le1$ (redundant once the normalized vector condition holds); Theorem 110.2 is used only for its exact closed-cap transport, with arbitrary addresses and full-carrier necessity. Theorem 112.2 remains an exact-law obstruction with another stopped law at the same cap, not a cap separator.

The continuous companion in Proposition 214.7 has one explicit original tail: $a_1=1-s/5$, $a_2=a_3=6s/5$, $a_4=s$, and $a_n=e2^{-(n-5)}$ for $n\ge5$. Its active length is four, $a_5=e$ is the closed endpoint, and the common seed realizes the five table events with at most two actual requests. Its actual tail law is $(1-e)\delta_{\theta_0}+e\delta_{\theta_4}$ and its tail error is $e$.

The literature correspondence is limited. David Blackwell, *Comparison of Experiments*, §§2 and 5, supplies the attainable-risk and common-randomization analogy, but its unrestricted decision procedures do not identify the stopped three-cell catalog with the four-cell catalog here. Lasse Leskela, *Stochastic relations of random variables and processes*, arXiv:0806.3562, Theorem 2.5 and Remark 2.7, gives closed-relation coupling tests and the finite tests for countable spaces; it supplies the warning that marginal feasibility is not joint feasibility and supplies no score-preserving hard-two conversion. Samal's fractional cut bounds, Kaniewski--Lee--de Wolf's randomized query trees, Winkler's finite-moment extreme-point result, and Altman--Avrachenkov--Garnaev's water-filling theorem are structural analogies only; none supplies the original source, stopped first-zero operation, full-carrier TV, signed residual, and one-budget bridge.

The universal comparison is unresolved. A general full-score certificate is still missing for simultaneous positive late coordinates outside Theorems 214.2, 214.5 and 214.8, for unequal or signed late profiles, for arbitrary positions beyond the fixed fibers, and for mixed early-$A$/late-$P$ inputs. Theorem 214.11 and Proposition 214.12 supply necessary projection stock and its two projection endpoints; Proposition 214.13 supplies fixed-method diagnostics. It does not provide an affordable full-score representative, a $b\in H_N$ separator, a uniform lower certificate against every original full-carrier $O_2$ competitor, an $H_N$/$H_L$ identification, or a full-$\lambda$/$H_N$ separator. Separately affordable allocations never become one common affordable allocation by addition. No claim of universal classification, whole-goal completion, kernel verification or exhaustive literature novelty is made.

## 追加锚（本行以下为增补区）
