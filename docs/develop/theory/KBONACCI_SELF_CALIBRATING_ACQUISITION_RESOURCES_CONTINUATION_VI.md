# Self-calibrating acquisition resources: conditioned joint certificates and sparse common budgets

## 182. Original sources, shared rows and attributed ingredients

**Definition 182.1 (The original domain and the finite certificate).**
Retain [Definition 172.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_V.md#172-finite-auxiliary-cores-within-the-original-acquisition-contract)
and Acquisition Resources, Definition 90.1. Thus the actual source is

$$
X=\{(s,g):s\text{ prime},\ g\in\mathbb Z,
       \lceil F_s/10\rceil\le g\le\lfloor F_s/5\rfloor\},\qquad
N(s,g)=1+F_sg,
$$

with static prime replies $u_i(x)=\mathbf1_{p_i\mid N(x)}$ and
finite actual first absence $n(x)=\min\{i:u_i(x)=0\}$. Every finite
answer word has an actual witness by the supplier in Definition 110.1.
There is no probability law on $X$. Keep the full original measurable
tape carrier, its consumer and its nonatomic targets. The separately
declared marked targets are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                     +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\qquad
1\ge a_1\ge a_2\ge\cdots>0,
\quad a_i\longrightarrow0.
\tag{182.1}
$$

Error means the uniform supremum of TV over all actual sources.
There is zero advice and one source-independent common seed, with
actual sourcewise almost-sure finite handoff. $N_2$ preselects a
schedule and obtains all its replies; $O_2$ preselects an increasing
schedule and stops at its first queried zero or exhaustion. Both
have a hard bound of two actual requests, counting repetitions and
ignored replies. Original competitors retain arbitrary addresses
and outputs anywhere in the original carrier. No address, depth,
runtime, mean-count or random-source bound replaces this resource.

Fix $L\ge3$, $B_L=\{0,1\}^L$, $J_L=\{0,\ldots,L\}$ and the
augmented complete-table catalog $E_L$ of Definition 176.1. In a
pair table $(i,j;s,t,k)$, $i<j$, the labels $s,t,k$ are its outputs
on stopped cells $0,10,11$. Equal schedule/table descriptions are
identified, and each retained coefficient counts once in the total
mass. Different schedules with identical kernels may remain.
Use the full catalogs $\mathcal D_N,\mathcal D_O$ and event vectors
$z_D$ of Definition 164.2 when no subcatalog is specified.

For a profile $b=(b_1,\ldots,b_L;e)$, $d(b)$ is the demand vector
of Definition 164.1: at every first-zero-$n$ word, the events
$\{0\},\{n\},\{0,n\}$ demand respectively
$1-b_n-e,b_n-e,1-e$; at $1^L$, event $\{0\}$ demands $1-e$.
All negative singleton demands remain. The pair row is independent
of the singleton rows. For probability vectors this is exactly

$$
\operatorname{TV}\bigl(p,(1-b_n)\mathbf e_0+b_n\mathbf e_n\bigr)
=\max\{0,1-b_n-p(0),b_n-p(n),1-p(0)-p(n)\}.
\tag{182.2}
$$

Here $\mathbf e_j$ is a unit vector, distinguished from scalar caps.
Let $R=(1,2;1,2,0)$ and
$\alpha=(1,1,0,\ldots,0;0)$, so $d(\alpha)=z_R$.
The domain $H_L$, the attained full-catalog costs $\rho_N,\rho_O$,
and $\rho_E$ are those of Definitions 165.1, 166.1 and 179.1.
In particular, with $S=\sum_{i=3}^Lb_i$,

$$
H_L=\{1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\ b_2=b_3,\ (L+1)e\le S,\ b_1+S-(L+1)e\le1\}.
\tag{182.3}
$$

**Definition 182.2 (Classical ingredients inside the acquisition proof).**
The intermediate LP strong-duality ingredient is
[Boyd and Vandenberghe, *Convex Optimization*, Section 5.2.3 and
Exercise 5.23](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The binary pair-regularity ingredient is
[Kolmogorov and Zabih, *What Energy Functions Can Be Minimized via
Graph Cuts?*, IEEE TPAMI 26(2), Theorem 4.1 and equation (7), p. 150](https://www.cs.cornell.edu/~rdz/Papers/KZ-PAMI04.pdf).
Its inequality is $E_{00}+E_{11}\le E_{01}+E_{10}$.
A positive pair coefficient violates this inequality in the original
bits; complementing one color of a bipartite graph restores it.
[Kolmogorov, *Generalized roof duality and bisubmodular functions*,
arXiv:1005.2305v2, Sections 1--2](https://arxiv.org/pdf/1005.2305v2)
supplies the relaxation context, including the distinction between
half-integrality and Boolean exactness. These are attributed classical
ingredients, used within the joint acquisition criterion below.
Neither graph regularity nor LP duality is a new standalone theorem
here. The threshold calculation below establishes the exact property
needed in this application; no universal acquisition comparison is
attributed to these sources.

## 183. One conditioned allocation for both suffix energies

**Definition 183.1 (Fixed deletion geometry and separate compensation).**
Fix $C\subseteq\{2,\ldots,L\}$ and a two-coloring $\chi$ of
$\{2,\ldots,L\}\setminus C$. For one allocation
$\lambda_D\ge0$ on $E_L$, put $\tau=\sum_D\lambda_D$ and

$$
f_u=(1-\tau)R_u+\sum_{D\in E_L}\lambda_DD_u.
\tag{183.1}
$$

This is an affine vector of total coordinate sum one. It is not
assumed nonnegative when $\tau>1$. Reuse the affine suffix forms of
Proposition 179.2: in first-zero class $n$, with $v_j=u_j$ for $j>n$,

$$
\begin{aligned}
f_u(0)&=C_n+\sum_{j>n}\beta_{nj}v_j
                      +\sum_{n<j<k\le L}Q_{jk}v_jv_k,\\
f_u(n)&=\gamma_n+\sum_{j>n}\kappa_{nj}(1-v_j),
\qquad Q_{jk},\kappa_{nj}\ge0.
\end{aligned}
\tag{183.2}
$$

The $Q_{jk}$ for $2\le j<k\le L$ come from this same allocation.
Impose the fixed graph constraint

$$
Q_{jk}=0\quad\text{if }j,k\notin C\text{ and }\chi(j)=\chi(k).
\tag{183.3}
$$

For each $n$, the base and pair energies have triples $(K,c,d)$
given by

$$
\begin{array}{c|c|c|c}
\text{row}&K&c_j\ (j>n)&d\\\hline
\text{base}&C_n&\beta_{nj}&1-b_n-e\\
\text{pair}&C_n+\gamma_n+\sum_{j>n}\kappa_{nj}
              &\beta_{nj}-\kappa_{nj}&1-e
\end{array}
\tag{183.4}
$$

They share $Q$, but their constants and unary coefficients differ.
Let $A_n=C\cap\{n+1,\ldots,L\}$ and
$V_n=\{n+1,\ldots,L\}\setminus C$. For each assignment
$\eta\in\{0,1\}^{A_n}$ and each row separately, set

$$
\begin{aligned}
K^\eta&=K+\sum_{j\in A_n}c_j\eta_j
                  +\sum_{\substack{j<k\\j,k\in A_n}}Q_{jk}\eta_j\eta_k,\\
c_i^\eta&=c_i+\sum_{j\in A_n}Q_{ij}\eta_j\quad(i\in V_n).
\end{aligned}
\tag{183.5}
$$

In incidence sums $Q_{ij}=Q_{ji}$ and $Q_{ii}=0$. Take separate
variables $t_{ij}^{n,\mathrm{row},\eta}$ and
$\ell_i^{n,\mathrm{row},\eta}$ for every conditioned energy.
Suppressing these superscripts within one system, its compensation
inequalities are

$$
\begin{aligned}
0&\le t_{ij}\le Q_{ij} &&(i<j,\ i,j\in V_n),\\
\ell_i&\ge0,\qquad
c_i^\eta+\sum_{j\in V_n\setminus\{i\}}t_{ij}+\ell_i\ge0
                                      &&(i\in V_n),\\
K^\eta-\sum_{\substack{i<j\\i,j\in V_n}}t_{ij}
             -\sum_{i\in V_n}\ell_i&\ge d.
\end{aligned}
\tag{183.6}
$$

Zero edges force $t_{ij}=0$. For an empty $V_n$, the system is
exactly $K^\eta\ge d$.

**Theorem 183.2 (Exact conditioned all-word criterion at one budget).**
Fix $M\ge1$ and the geometry in Definition 183.1. The following
are equivalent for one allocation on $E_L$ satisfying (183.3):

1. $\lambda\ge0$, $\tau\le M$, and the event vector of (183.1)
   dominates $d(b)$ on every word.
2. The same $\lambda$, $Q$ and mass satisfy $\tau\le M$, all the
   systems (183.6), and the additional inequalities

$$
\gamma_n\ge b_n-e\quad(1\le n\le L),\qquad
f_{1^L}(0)\ge1-e.
\tag{183.7}
$$

The base and pair compensation variables are not identified.
There are literally

$$
2\sum_{n=1}^L2^{|C\cap\{n+1,\ldots,L\}|}
\le2L\,2^{|C|}
\tag{183.8}
$$

energy systems, including empty suffixes, in addition to the $L$
correct-minimum rows, the all-positive row, graph constraints,
endpoint masses and their one budget. For fixed $C,\chi,M$, this
is a finite system linear in $\lambda$ and the separate auxiliary
variables, with $O(2^{|C|}L^3)$ compensation coordinates.

**Proof.** The endpoint polynomial argument of Theorem 178.2 and
Proposition 179.2 supplies (183.2). Nonnegative $E_L$ masses have
nonnegative quadratic base coefficients. The possibly negative
coefficient of $R$ affects only $u_1u_2$, which becomes zero or a
constant after any first zero, never a suffix-suffix term. A correct
middle label $n$ in a zero-first endpoint contributes $1-v_j$ when
its second query $j>n$; every other correct contribution is constant
on the first-zero class. Thus $\kappa\ge0$ also for the affine
vector, and its correct minimum is $\gamma_n$. This shortcut belongs
to the declared $E_L$ class and its proved signs.

Adding the base and correct expressions yields exactly the second
energy in (183.4), with the same $Q$. Conditioning its fixed bits,
or those of the base energy, gives (183.5). The remaining positive
edge graph is bipartite by (183.3). It remains to establish the
compensation equivalence inside each of these acquisition rows.

For a finite bipartite remaining graph and its energy
$E(v)=K+\sum_i c_iv_i+\sum_{i<j}Q_{ij}v_iv_j$, relax to

$$
m_{\rm rel}=\min_{0\le x_i\le1}
\left[K+\sum_i c_ix_i
          +\sum_{i<j}Q_{ij}\max(0,x_i+x_j-1)\right].
\tag{183.9}
$$

Introducing $y_{ij}\ge0$, $y_{ij}\ge x_i+x_j-1$ makes this a
feasible finite-value LP. Finite LP strong duality, with the supplier
in Definition 182.2, gives

$$
m_{\rm rel}
=K+\max_{0\le t_{ij}\le Q_{ij}}
 \left[-\sum_{i<j}t_{ij}
       +\sum_i\min\left(0,c_i+\sum_jt_{ij}\right)\right].
\tag{183.10}
$$

Indeed $t_{ij}$ multiplies $x_i+x_j-1-y_{ij}$; minimizing over
$y_{ij}\ge0$ forces $t_{ij}\le Q_{ij}$, and minimizing over each
$x_i\in[0,1]$ gives the displayed unary minimum. The maximum is
attained on the compact $t$ box. Put
$\ell_i=\max(0,-c_i-\sum_jt_{ij})$. Then (183.6) is equivalent
to this dual lower bound being at least $d$. Conversely any feasible
$t,\ell$ proves that lower bound directly, since for Boolean $v$,

$$
Q_{ij}v_iv_j\ge t_{ij}(v_i+v_j-1),\qquad
E(v)\ge K-\sum_{i<j}t_{ij}-\sum_i\ell_i.
\tag{183.11}
$$

The bipartite relaxation is exact here. For any fractional $x$,
use an auxiliary uniform threshold $T$ to form
$V_i=\mathbf1_{T<x_i}$ on one color and
$V_j=\mathbf1_{T>1-x_j}$ on the other. Every unary expectation
is $x_i$, and on every remaining edge simultaneously,

$$
\mathbb E[V_iV_j]=\max(0,x_i+x_j-1).
$$

Hence each relaxed objective is an average of Boolean objectives.
Its minimum is at least the Boolean minimum; the reverse inequality
holds because Boolean points are allowed in (183.9). This is the
integrality property corresponding to bipartite complementation of
the regularity ingredient. The auxiliary threshold proves an identity
of minima, not an acquisition sampler or an extra execution seed.

Apply (183.10)--(183.11) separately to the two energies for every
fixed-bit assignment. They enumerate all suffix words exactly,
including words with arbitrarily many later zeros. Add (183.7) for
the correct and all-positive rows. This proves both directions.
Empty vertex sets have zero sums, isolated vertices retain their
unary bounds, zero $Q$ gives zero $t$, and all inequalities include
equality. None requires positive weights or a limiting argument.
Counting one base and one pair system per assignment gives (183.8);
at most $O(L^2)$ auxiliary coordinates in each gives the stated count.
This count concerns descriptions of the finite system, not the
runtime, request count or arithmetic precision of an acquisition.
$\square$

## 184. Clipped normalization and a smaller literal conditioning count

**Theorem 184.1 (Probability equivalence at the clipped common budget).**
For fixed $M\ge1$, the criterion of Theorem 183.2 at $b$ is
equivalent to the existence of one probability mixture on $E_L$
with the same graph restriction, whose event vector dominates
$d(x)$ for

$$
x=\alpha+\frac{b-\alpha}{M}.
\tag{184.1}
$$

More generally its forward allocation supplies the entire closed
segment $\alpha+t(b-\alpha)$, $0\le t\le1/M$.
For $b\in H_L$ with finite $s=\rho_N(b)$, choosing
$M=\max\{1,s\}$ therefore places the largest $N$-feasible radial
point in this stopped class, provided this single restricted
allocation exists.

**Proof.** Reuse the padding identity of Proposition 179.2 and the
radial correspondence of Theorems 166.2--167.2. Explicitly, assign
probability $\lambda_D/M$ to each endpoint and additional probability
$1-\tau/M$ to $R$. The weights are nonnegative and sum to one,
including $\tau=M$. Combine an existing $R$ coordinate with its
padding once. The resulting event vector is

$$
z_R+\frac{\sum_D\lambda_D(z_D-z_R)}{M}
\ge z_R+\frac{d(b)-z_R}{M}=d(x).
\tag{184.2}
$$

Its suffix $Q$ is the old $Q$ divided by $M$, so it retains (183.3).
For the reverse direction, if $p=\sum_D\pi_DD$ is such a
probability mixture, set $\lambda_D=M\pi_D$ and $\tau=M$.
Then $f=R+M(p-R)$ dominates $d(b)$, and its suffix $Q$ is
multiplied by $M$. Theorem 183.2 supplies the separate certificates.
At any $t\in[0,1/M]$, use endpoint weights $t\lambda_D$ and
$R$ padding $1-t\tau$. This proves the segment statement.
Theorem 167.2 gives its largest $N$-feasible parameter
as $1/M$. At $t=0$ the profile is the auxiliary $\alpha$, not a
positive original vanishing sequence. Positive original profiles and
their whole tails have the realization in Section 189. $\square$

**Theorem 184.2 (Literal $C=\{2\}$ count for the supplied geometry).**
Suppose the positive $Q$ graph on $\{2,\ldots,L\}$ is a subgraph
of the triangle on $2,3,4$ together with the path
$4-5-\cdots-L$. Then $C=\{2\}$ makes Theorem 183.2 exact with
exactly $2L+2$ energy systems. The alternative $C=\{3\}$ gives
$2L+4$ systems for the same specified enumeration.

**Proof.** Deleting vertex two leaves a subgraph of the path
$3-4-5-\cdots-L$, which is bipartite. For first zero one,
$A_1=\{2\}$ has two assignments and therefore four base/pair
systems. For every $n=2,\ldots,L$, $A_n$ is empty and gives two
systems. The total is $4+2(L-1)=2L+2$. Empty suffix systems are
included. Deleting vertex three instead leaves a subgraph of
$2-4-5-\cdots-L$; both $n=1,2$ have two assignments, so its total
is $8+2(L-2)=2L+4$. The graph can omit edges through zero
weights or plateaus. This is a literal count for these choices;
it is not a minimum over all certificates, graphs or protocols.
The additional rows and the single budget of Theorem 183.2 remain.
$\square$

**Theorem 184.3 (Two boundaries of the conditioned test).** Sharing
$Q$ does not in general permit sharing the base and pair compensation
variables. The correct-minimum shortcut of (183.7) does not extend
to the full stopped catalog without its nonnegative-$\kappa$ proof.
An affine row vector at $\tau>1$ need not be a probability law.

**Proof.** On one edge with $Q=1$, the energy with $K=0$, $c=(0,0)$
has dual expression $-t$, uniquely maximized at $t=0$.
The energy with $K=2$, $c=(-1,-1)$ has dual expression $t$ on
$0\le t\le1$, uniquely maximized at $t=1$. The two algebraic
energies thus have a shared edge and different exact witnesses.
The full stopped table $(2,3;0,0,1)$, outside $E_3$, has correct
probability $u_2u_3$ in first-zero class one. Its all-one-suffix
value is one and its minimum is zero. Finally, immediate-base mass
two in (183.1) gives $f_u=2\mathbf e_0-R_u$, with correct-label-one
coordinate $-1$ in first-zero class one. Normalization and padding
in Theorem 184.1 are essential before a probability or execution
claim. These are boundaries of the method, not whole-class cap
separators. $\square$

## 185. Cyclic windows with the same residual amplitude projection

**Definition 185.1 (The original cyclic-window branch).** For $h\ge3$,
take the cyclic list $1,2,\ldots,h,\ast$ and its $h+1$ consecutive
length-three windows. In each window sort the numerical labels
increasingly, with $\ast$ last. Query the first two labels, stopping
at their first zero, and emit that zero label or the third selected
label on positive exhaustion. The symbol $\ast$ means output zero;
it is never queried. Give each indexed window mass $1/(h+1)$ and
write $P_h^{\rm cyc}$ for the resulting complete-table mixture.

**Theorem 185.2 (All-word law and exact description counts).** For
every first-zero-$n$ word with $n\le h$,

$$
P_{h,u}^{\rm cyc}(n)=\frac3{h+1},\qquad
1-P_{h,u}^{\rm cyc}(0)-P_{h,u}^{\rm cyc}(n)
   \le\frac{h-2}{h+1},
\tag{185.1}
$$

and its entire base polynomial is

$$
P_{h,u}^{\rm cyc}(0)
=\frac{u_1u_2+u_1u_h+u_{h-1}u_h}{h+1}.
\tag{185.2}
$$

Replacing the subset branches of Theorem 173.1 by these windows
at $h=6,\ldots,L$ retains that theorem's residual amplitude
projection and exact uniform cap for a tight core. It uses the same
$w_h,W,E,r$; it does not enlarge the amplitude projection.
The raw descriptions across every such $h$ number

$$
\sum_{h=6}^L(h+1)=\frac{(L+1)(L+2)}2-21.
\tag{185.3}
$$

If $g_L>0$ and exactly $k$ of these $w_h$ are positive, their
distinct positive complete tail tables number $L-1+2k$. If every
$w_h>0$, this is $3L-11$. These counts exclude the core.

**Proof.** Each label lies in exactly three windows. If a window
contains the actual first zero $n$, every selected label preceding
$n$ is positive. Thus it emits $n$, whether that label is its first
query, second query or unqueried last label. If a window does not
contain $n$, it cannot emit $n$. This proves the correct identity
for every later-zero pattern; nonnegative base mass gives the pair
bound. Exactly three windows contain $\ast$, and their numerical
query pairs are $(1,2),(1,h),(h-1,h)$, proving (185.2).
On $1^h$ the base mass is $3/(h+1)$. If the first absence exceeds
$h$, the branch has no correct-tail mass and outside-pair mass
exactly $(h-2)/(h+1)$.

These are precisely the correct, pair and positive-prefix inputs
used in the residual extension of Theorem 173.1. The same telescoping
weights therefore give its existing amplitude and cap formulas;
the core rows and independent pair rows are unchanged inequalities.
For a tight core the all-positive base is $1-\varepsilon$, so the
supplied actual-tail identity is unchanged. The word laws themselves
need not agree with the subset law. All endpoints are numerical
triples or canonical base-exhausting pairs in $E_L$.

Formula (185.3) counts indexed descriptions before removing zero
weights or combining duplicates. When $g_L>0$, $w_L>0$ and its
$L-2$ consecutive numerical triples already contain every numerical
triple from each smaller cyclic branch. Every active $h$ adds the
distinct pairs $(1,h),(h-1,h)$; all active branches also share pair
$(1,2)$. These pairs are distinct from numerical triples and from
each other. Their total is $(L-2)+2k+1=L-1+2k$.
If all weights are positive, $k=L-5$, giving $3L-11$.
Active raw descriptions instead number $\sum_{w_h>0}(h+1)$.
No description count here bounds runtime, precision or requests.
The request bound is separately the hard-two contract.

For the sharp-five core used below, its suffix graph is the triangle
on $2,3,4$ plus edge $4-5$. In (185.2) only edge $(h-1,h)$ can
be a suffix-suffix edge; the edges incident to one become constants
or unary terms. Thus the positive combined graph is a subgraph of
the triangle plus path $4-5-\cdots-L$. Plateaus can remove edges.
Theorem 184.2 applies. $\square$

## 186. A separated anchor and a strict common-budget improvement

**Definition 186.1 (Numerical-cycle branches and a finite core).**
For $h\ge6$, put mass $3/(h+1)$ on $R$. On the cyclic list
$3,4,\ldots,h$, put mass $1/(h+1)$ on each of its $h-2$
consecutive length-three windows. Sort each to $i<j<k$ and use
the numerical table $(i,j;i,j,k)$. Write $P_h^{\rm num}$ for this
mixture. It has $h-1$ indexed complete-table descriptions.

Fix $L>m\ge5$ and any core $(A,e_0,q)$ satisfying Definition 172.2,
including $A_m=e_0$ and slack $q_{1^m}(0)>1-e_0$.
Retain residuals and the scalars from Definition 172.3:

$$
\begin{aligned}
g_{m+1}&\ge\cdots\ge g_L\ge0,\qquad g_{L+1}=0,\\
w_h&=\frac{h+1}{3}(g_h-g_{h+1}),\\
W&=\frac{(m+2)g_{m+1}+\sum_{i=m+2}^Lg_i}{3}\le1,\\
E&=\frac{(m-1)g_{m+1}+\sum_{i=m+2}^Lg_i}{3},\qquad r=1-W.
\end{aligned}
\tag{186.1}
$$

Use exactly the residual amplitudes of (173.1), and a different
explicit law:

$$
\begin{aligned}
\varepsilon&=re_0+E,\\
a_i&=rA_i+W &&(i\le m),\\
a_i&=\varepsilon+g_i &&(m<i\le L),\\
p_u&=r q_{(u_1,\ldots,u_m)}
             +\sum_{h=m+1}^Lw_hP_{h,u}^{\rm num}.
\end{aligned}
\tag{186.2}
$$

Append any original positive nonincreasing vanishing tail with
$a_{L+1}\le\varepsilon$. This retains all its actual amplitudes.

**Theorem 186.2 (Sparse all-word feasibility and the anchor budget).**
The law in (186.2) belongs to the finite full stopped class and
meets every cap-$\varepsilon$ row on every word, with exact uniform
error $\varepsilon$ on the original sources. Its actual-tail error is

$$
\max\{t_{\rm tail},a_{n(x)}\},\qquad
t_{\rm tail}=r\bigl(1-q_{1^m}(0)\bigr)+E\le\varepsilon
\quad(n(x)>L).
\tag{186.3}
$$

It has one full-$O$ conic allocation at the unscaled profile
$(a_1,\ldots,a_L;\varepsilon)$ of mass $1-g_{m+1}$. Consequently

$$
\rho_N\le\rho_O\le1-g_{m+1}.
\tag{186.4}
$$

If $q\in\operatorname{conv}(E_m)$, the allocation is in $E_L$
and also gives $\rho_O\le\rho_E\le1-g_{m+1}$. The upper bound is
strictly below one exactly when $g_{m+1}>0$. It is a feasible upper
bound, not an optimum or an equality of the two costs.

**Proof.** The sparse branch is normalized because
$3+(h-2)=h+1$. Each numerical label belongs to three cyclic windows.
For first zero $n\in\{3,\ldots,h\}$, such a window emits $n$
exactly when it contains it: preceding selected labels are positive,
and the first-zero label can be the unqueried final output.
Only $R$ emits one or two, and its correct mass in either of those
classes is $3/(h+1)$. Thus for every suffix word,

$$
P_{h,u}^{\rm num}(n)=\frac3{h+1}\quad(n\le h),\qquad
P_{h,u}^{\rm num}(0)+P_{h,u}^{\rm num}(n)\ge\frac3{h+1},\qquad
P_{h,u}^{\rm num}(0)=\frac3{h+1}u_1u_2.
\tag{186.5}
$$

When the first absence exceeds $h$, correct mass is zero and
outside-pair mass is exactly $(h-2)/(h+1)$. At $h=6$, the numerical
cycle has four vertices and its four windows are the four distinct
triples of $\{3,4,5,6\}$. The stated support descriptions require
no minimum claim about all possible designs.

The existing residual telescoping and amplitude argument is reused:

$$
\sum_hw_h=W,\qquad
\sum_h\frac{3w_h}{h+1}=g_{m+1},\qquad
\sum_hw_h\frac{h-2}{h+1}=E,\qquad
W=E+g_{m+1},\qquad r+W=1.
\tag{186.6}
$$

All masses are nonnegative. The join is
$a_m-a_{m+1}=r(A_m-e_0)\ge0$, and
$\varepsilon=1-g_{m+1}-r(1-e_0)\le1$.
If $r>0$ then $\varepsilon\ge re_0>0$; if $r=0$ then
$W=1$ and $E>0$ because all indices $h\ge6$ have positive
$(h-2)/(h+1)$. This proves positive ordered amplitudes at most
one, with the unchanged positive vanishing tail. These algebraic
conditions and the amplitude sandwich are the suppliers of
Sections 172--174, not a new amplitude projection.

For $n\le m$, the three rows of the same mixture obey, separately,

$$
\begin{aligned}
p_u(n)&\ge r(A_n-e_0)+g_{m+1}=a_n-\varepsilon,\\
p_u(0)+p_u(n)&\ge r(1-e_0)+g_{m+1}=1-\varepsilon,\\
p_u(0)&\ge r(1-A_n-e_0)=1-a_n-\varepsilon+E.
\end{aligned}
\tag{186.7}
$$

No singleton projection has been substituted for the pair row.
For $m<n\le L$, the correct mass is exactly

$$
p_u(n)=\sum_{h=n}^L\frac{3w_h}{h+1}=g_n.
\tag{186.8}
$$

Every such word has $u_1=u_2=1$, and the core sees $1^m$.
Numerical windows never emit zero. Hence throughout this whole
first-zero class, regardless of all later bits,

$$
p_u(0)=r q_{1^m}(0)+g_{m+1}=1-t_{\rm tail}.
\tag{186.9}
$$

The outside-pair mass is $t_{\rm tail}-g_n\le\varepsilon$;
the base deficit is $t_{\rm tail}-a_n\le\varepsilon$;
the correct deficit is $a_n-g_n=\varepsilon$.
Equation (182.2) gives TV exactly $\varepsilon$. The same base
identity (186.9) holds at $1^L$. For every actual $n(x)>L$,
the original finite rule outputs no label $n(x)$ and has this same
base mass. The supplied tail identity (110.9) gives (186.3), with
every later-zero pattern retained. The actual first-zero class
$m+1$ witnesses uniform equality even if $g_{m+1}=0$.
If $q_{1^m}(0)=1-e_0$, then $t_{\rm tail}=\varepsilon$ and all
actual tails have error exactly $\varepsilon$. For a slack core
only the maximum in (186.3) is asserted; equality on every tail
does not follow from its cap rows.

The new budget fact follows by separating one anchor before any
row projection. In (186.2), the explicit $R$ component from all
residual branches has total mass $g_{m+1}$. Their numerical
tables have total mass $E$. Refine the core into full stopped
complete tables using the supplier of Definition 164.2 and
Proposition 140.3, with all weights multiplied by $r$.
Keep those core tables and numerical triples as conic coefficients
$\lambda_D$. Their one total mass is

$$
\tau=r+E=1-g_{m+1},\qquad
z_p=z_R+\sum_D\lambda_D(z_D-z_R)\ge d(a,\varepsilon).
\tag{186.10}
$$

This is the common-budget definition of $\rho_O$, and completing
each table gives the $N$ inequality. The argument does not require
$(a,\varepsilon)\in H_L$; the same finite conic LP is defined at
that profile. If the core is in $E_m$, use its $E_m$ refinement
instead and the natural embedding into $E_L$, giving the additional
$\rho_E$ bound. Possible core $R$ mass remains inside the retained
conic coefficients; removing the displayed residual anchor is enough.

Plateaus have $w_h=0$, so their intervals are omitted. At $W=1$
the core is omitted, with no division by $r$. If $g_L=0$, $L$ is
an auxiliary length rather than necessarily the active length;
only amplitudes strictly above the cap are active. If every residual
is zero, $W=E=0$, $r=1$, and (186.4) gives the non-strict bound
one. Non-strict core endpoints are allowed throughout.
The same-seed original execution and arbitrary-address transport
are given in Section 189. $\square$

## 187. A sharp-five core with a fixed suffix graph at every length

**Definition 187.1 (The declared sharp core).** Use the seven-cell
law (118.5) at

$$
\delta=\frac3{20},\qquad \alpha_{\rm core}=0,\qquad
t=\frac{81}{100},\qquad u=\frac1{25},\qquad v=\frac1{50}.
\tag{187.1}
$$

The ordinary supplier Theorem 118.1 gives

$$
A=\left(\frac{17}{20},\frac{17}{20},\frac{17}{20},
                \frac{83}{100},\frac34\right),\qquad
e_0=\frac{233}{600},\qquad q_{1^5}(0)=1-e_0.
\tag{187.2}
$$

Its schedule weights in the notation of (118.4) are
$w=79/200$, $x=1/15$, $y=193/600$, $z=1/20$, with
$w+2x+y+3z=1$. This core differs from the core in Proposition 175.1.
Refine it by the common-cell coupling (176.4), omitting zero
schedule masses. No new proof of its five-active optimum is needed.

**Theorem 187.2 (Fixed graph, exact late base and subunit family).**
For every $L\ge6$ and $g_6\ge\cdots\ge g_L\ge0$ with
$W=(7g_6+\sum_{i=7}^Lg_i)/3\le1$, use Definition 186.1 at $m=5$
with the declared core. The resulting profile belongs to $H_L$,
and

$$
S-(L+1)\varepsilon=\frac r{10},\qquad
1-a_1=\frac{3r}{20},\qquad
\rho_N\le\rho_O\le\rho_E\le1-g_6.
\tag{187.3}
$$

The first identity is $D_3-3\varepsilon=r/10$. It is positive
exactly when $r>0$. If $g_L>0$, the actual active length is $L$
and the budget bound is strictly below one. The closed boundary
$W=1$ is feasible; it retains the strict budget bound when $g_6>0$
but has zero excess.

For every first-zero class $6\le n\le L$, the sparse law has

$$
p_u(0)=1-\varepsilon,\qquad p_u(n)=g_n,\qquad
1-p_u(0)-p_u(n)=\varepsilon-g_n.
\tag{187.4}
$$

The same base value holds at $1^L$ and hence for every actual first
absence $n(x)>L$. It has TV exactly $\varepsilon$ on those classes and every permitted
actual tail, including $a_{L+1}=\varepsilon$. Its positive suffix
graph is the triangle $2-3-4$ plus edge $4-5$ when $r>0$,
with every label $\ge6$ isolated; when $r=0$ all these edges vanish.
Thus Theorem 184.2 has $2L+2$ energy systems without any growing
late graph.

**Proof.** The parameters satisfy (118.1): in particular
$u+v=3/50\le1/15=4\delta/9$ and $t+u=17/20=1-\delta$.
The other bounds follow directly from (187.1). The core supplier
therefore supplies all its words and its tight positive-prefix row.
Apply Theorem 186.2. Since $A_2=A_3$, the extended profile has
$a_2=a_3$. The excess identity of Proposition 174.2, applied to
$A_3+A_4+A_5-6e_0=1/10$, gives the first part of (187.3).
Also $1-a_1=r(1-A_1)=3r/20$. Hence
$a_1+S-(L+1)\varepsilon=1-r/20\le1$, establishing (182.3).
The conic inequality comes from the same separated anchor;
$E_m$ membership follows from Proposition 176.2.
Tightness of the core turns (186.9) into (187.4), also at $1^L$,
so the exact actual-tail conclusion follows from (186.3).

For the graph, (118.5) has first-cell support $\{0,i\}$,
middle output $j$ and exhaustion support $\{0,j+1,\ldots,5\}$
on schedule $(i,j)$. For a positive schedule mass $\beta$, coupling
first masses $a_s$ to exhaustion masses $b_k$ with coefficient
$a_sb_k/\beta$ reproduces every cell. Its endpoints are canonical
or zero-first and hence in $E_5$. The base polynomial from the
seven schedules, with the fixed weights above, is

$$
q_u(0)=3z-z(u_2+u_3+u_4)
 +(w-5\delta/9)u_1u_2+zu_1u_3+zu_1u_4
 +z(u_2u_3+u_2u_4+u_3u_4+u_4u_5).
\tag{187.5}
$$

Its suffix edges on labels at least two have coefficients $z$.
The sparse residual base contributes only $g_6u_1u_2$, never a
suffix-suffix term after any first zero. Thus the corresponding
suffix coefficients are $rz$ on precisely the displayed four
edges, and zero on edges incident to labels $\ge6$.
This statement concerns the common suffix graph; a particular
first-zero class retains only its induced remaining edges.
The all-word criterion with $C=\{2\}$ follows. $\square$

**Theorem 187.3 (An exact seven-active sparse example).** Set
$L=7$, $g_6=1/100$, $g_7=1/200$. For the core of Definition 187.1,

$$
\begin{aligned}
W&=\frac1{40},&E&=\frac3{200},&r&=\frac{39}{40},&
\varepsilon&=\frac{3149}{8000},\\
a&=\left(\frac{683}{800},\frac{683}{800},\frac{683}{800},
\frac{3337}{4000},\frac{121}{160},
\frac{3229}{8000},\frac{3189}{8000}\right).
\end{aligned}
\tag{187.6}
$$

With any retained positive monotone vanishing tail below this cap,
the original same-seed $O_2$ and $N_2$ laws have uniform error exactly
$3149/8000$ and one $E_7$ conic allocation of mass $99/100$.
The literal conditioned system has sixteen base/pair energy systems,
in addition to its seven correct rows and its all-positive row.

**Proof.** Equations (186.1)--(186.2) give
$w_6=7/600$, $w_7=1/75$ and the displayed exact values.
Both late residuals are positive, so the active length is seven.
Theorems 186.2--187.2 give all words, the independent pair row,
the exact tails and the common budget $1-g_6=99/100$.
Theorem 184.2 gives $2(7)+2=16$ systems.
This is a different amplitude and cap instance from Proposition
180.1: that proposition uses the core $(175.1)$ and cap $233/800$.
No equality of these laws, cap optimality or full-class gap follows
from either example. $\square$

## 188. A shared classical relaxation bound inside the two-row test

**Theorem 188.1 (One error allowance for both acquisition energies).**
Fix one allocation as in Definition 183.1, one first-zero class
and, optionally, one conditioned assignment. Let $E_B,E_P$ be
its base and pair energies, with the same nonnegative remaining
$Q$ and their own $K,c,d$. Choose any two-coloring of the remaining
vertices, without assuming its graph is bipartite, and put

$$
\Delta=\frac12
  \sum_{\substack{i<j\\\chi(i)=\chi(j)}}Q_{ij}.
\tag{188.1}
$$

For each of these two energies let $m_B$ be its Boolean minimum
and $m_{\rm rel}$ the relaxation (183.9). Then the same $\Delta$
satisfies

$$
0\le m_B-m_{\rm rel}\le\Delta.
\tag{188.2}
$$

Thus a true margin $m_B-d\ge\Delta$ guarantees its compensation
certificate. Actual Boolean feasibility only implies
$m_{\rm rel}\ge d-\Delta$, which is a necessary test and not a
sufficient one. The sufficient relaxed test is $m_{\rm rel}\ge d$.
These supplier applications test the two rows of the fixed common
allocation; they do not construct a missing allocation or separate
the full stopped class.

**Proof.** Use the relaxation and opposite-threshold calculation
inside Theorem 183.2, with the classical relaxation context in
Definition 182.2. Boolean points show $m_{\rm rel}\le m_B$.
At a relaxed minimizer, use one auxiliary threshold as before.
Cross-color products have expectation $\max(0,x_i+x_j-1)$.
Same-color products have expectation $\min(x_i,x_j)$.
Their excess over the relaxed product lies in $[0,1/2]$: when
$x_i+x_j\le1$, it is at most $(x_i+x_j)/2$; when the sum is at
least one, it is $1-\max(x_i,x_j)\le1/2$.
Linear expectations are exact, for arbitrary signs of $c$.
Consequently

$$
m_B\le\mathbb E[E(V)]\le m_{\rm rel}+\Delta.
$$

The allowance depends only on $Q$ and the coloring, so it applies
to both row energies simultaneously even though their minima and
their dual witnesses differ. Zero edges contribute nothing; empty
suffixes have $\Delta=0$. The threshold is a proof device, not
an additional acquisition randomization. LP strong duality supplies
the compensation certificate exactly when its relaxed minimum is
at least its demand, on any graph. From (188.2),
$m_B\ge d+\Delta$ implies $m_{\rm rel}\ge d$, whereas
$m_B\ge d$ gives only $m_{\rm rel}\ge d-\Delta$.
Also $m_{\rm rel}+\Delta<d$ excludes that fixed allocation;
$m_{\rm rel}<d$ alone does not. This is an explicitly attributed
use of relaxation and rounding within the new acquisition criterion,
not a standalone originality claim for those tools. $\square$

**Theorem 188.2 (Sharp triangle and the insufficient weakened test).**
The allowance $1/2$ is attained by a unit triangle, and the test
$m_{\rm rel}\ge d-\Delta$ alone can hold when the Boolean row
fails.

**Proof.** For
$E(v)=-v_1-v_2-v_3+v_1v_2+v_1v_3+v_2v_3$, its Boolean values
at cardinalities $0,1,2,3$ are $0,-1,-1,0$, so $m_B=-1$.
Writing $s=x_1+x_2+x_3$, the relaxed value is at least
$-s+\max(0,2s-3)\ge-3/2$, with equality at all $x_i=1/2$.
A two-versus-one coloring has one monochromatic unit edge, so
$\Delta=1/2=m_B-m_{\rm rel}$. In particular the unconditioned
compensation test is not exact on this triangle. Conditioning one
vertex makes each remaining graph bipartite, as used in Section 184.

For the same unit triangle with $K=0,c=0$, instead
$m_B=m_{\rm rel}=0$ and $\Delta=1/2$. At demand $d=1/4$,
the weakened test $m_{\rm rel}\ge d-\Delta$ holds, but the actual
Boolean row fails. These are exact algebraic boundaries of a row
test, not original $N/O$ counterexamples or universal certificates.
$\square$

## 189. Original realization and the unchanged full-catalog obligation

**Theorem 189.1 (Same-seed handoff, every actual tail and closed caps).**
Every probability allocation produced in Sections 184--187 has
original $O_2$ and $N_2$ realizations using the identical common
seed and original marked tapes. Every word and actual tail row
proved above holds uniformly on $X$. Theorem 110.2 supplies the
existing exact closed-cap transport, with full-carrier arbitrary-address
competitors retained.

**Proof.** Partition one source-independent uniform $U\in[0,1)$
into the finitely many whole-table masses; omit zero masses and
combine duplicate coordinates once. The chosen interval fixes its
entire schedule and terminal labels before replies. For a general
finite core, use its full stopped complete-table refinement, as in
Proposition 140.3. Alternatively its predetermined cell partitions
use the same rescaled $U$; they are fixed source-independently.
No new independent randomness is needed.

Execute that preselected increasing schedule as actual prime
requests, stopping at its first queried zero or exhaustion, and
hand off the chosen original tape $\theta_j$. Each execution is
measurable and finite and uses at most two actual requests. With
the identical $U$, the $N$ rule completes the same schedule and
reconstructs the stopped cell, ignoring replies after that cell while
counting those actual requests. Static replies make its output
identical for every source and seed. Original tapes remain in the
full measurable carrier; the original consumer and nonatomic targets
have not changed. Explicit stopped tables give membership in
$\mathscr C_L$ by Theorem 109.1, whose exact coefficient criterion
is $c\ge H$.

The complete cap rows include every $u\in B_L$, not only chain
words, and keep the separate pair row. Every actual $n(x)>L$
sees $1^L$, so for any such finite law its exact TV is

$$
\max\{1-p_{1^L}(0),a_{n(x)}\}.
\tag{189.1}
$$

This is the supplied identity (110.9). The all-positive row bounds
the first entry by the cap, and the retained original tail bounds
the second. For Section 186 the first entry is $t_{\rm tail}$;
for the tight core in Section 187 it is $\varepsilon$.
No infinite all-positive actual source is presumed. There is no
restriction on actual later zeros. Equality $a_{L+1}=\varepsilon$
and every other non-strict endpoint are included.

For the radial law of Section 184, an original extension at scale
$t>0$ uses the whole-sequence identity of Theorem 170.1:
first-two amplitudes are $1-t(1-b_i)$, and all amplitudes $i\ge3$,
including every actual $i>L$, are $tb_i$, with cap $te$.
That supplier preserves order, positivity, vanishing and the actual
tail comparisons when applied to its original positive domain.
Original tail marks are not replaced by zero in that target identity;
the finite all-positive row is only the transport device.

Finally use Theorem 110.2 rather than a new projection or shortening
claim. It transports necessity for arbitrary original addresses,
repetitions and full-carrier outputs and sufficiency for the explicit
finite probability laws at the exact closed cap. If $g_L=0$, the
auxiliary law may still use labels through $L$; (189.1) and the
all-word proof give its original feasibility, while applying that
transport at the actual active length uses its established projection.
No competitor is assumed to be an $E_L$ or sparse-table mixture.
$\square$

**Definition 189.2 (The still missing intersection).** The fixed
original obligation of Definition 181.1 remains, for every sequence
(182.1) and positive closed cap, at its actual active length,

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing.
\tag{189.2}
$$

On the remaining radial directions this is the full-catalog demand

$$
\rho_O(b)\le\max\{1,\rho_N(b)\}
\quad(b\in H_L,\ \rho_N(b)<\infty).
\tag{189.3}
$$

Theorem 167.2 owns this equivalence and finite attainment.
When $s=\rho_N(b)\ge1$, it requires cost equality
$\rho_O(b)=\rho_N(b)$, since $\rho_N\le\rho_O$.
When $s<1$, it requires only $\rho_O(b)\le1$.
The conditioned criterion exactly tests one fixed restricted
allocation and its graph at $M=\max\{1,s\}$; existence of such
an allocation for every $b$ is unproved. The sparse family supplies
explicit subunit upper budgets and all-word original attainers;
it does not resolve the $s\ge1$ cost-equality directions or enlarge
the prior residual amplitude projection. Sufficiency of $E_L$ and
the universal allocation inequality (179.5) also remain unproved.

A failed restricted graph, compensation test or subcatalog is a
method failure, not a full-class separator. A negative answer would
need an explicit original common-seed $N_2$ attainer and a uniform
lower certificate against every original full-carrier arbitrary-address
$O_2$ competitor, including all actual tails, as in Section 169.
The exact-law obstruction of Theorem 112.2 does not exclude a
different stopped law at the same cap. The results here are ordinary
mathematical deductions with the cited classical and repository
suppliers; they assert neither optimality of the new family,
universal classification, exhaustive novelty or literary priority,
nor a Lean/kernel verification.

## 追加锚（本行以下为增补区）

## 190. 完整见证目录与同一锥质量

**定义 190.1（原问题、事件行与仿射锚）。** 保留定义 182.1 的实际可数带标签来源、静态素数回答、完整可测纸带载体、原消费者及原非原子目标。所比较的是另行声明的标记目标

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                 +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\longrightarrow0.
$$

资源类严格采用获取资源定义 90.1：零建议、一个与来源无关的共同种子、实际几乎处处有限交接，以及至多两次实际请求，重复请求也计数。$N_2$ 预选整个日程并取得其全部回答；$O_2$ 预选递增日程，在首次被查询的零或日程耗尽时停止。原竞争者仍可使用任意地址及载体内任意输出；误差是实际来源集上的一致 TV 上确界，不引入来源分布。

固定 $L\ge3$，令 $B_L=\{0,1\}^L$、$J_L=\{0,\ldots,L\}$，以 $\mathbf e_t$ 表示输出标签 $t$ 的单位向量。令

$$
\Omega_n=\{w:w_1=\cdots=w_{n-1}=1,\ w_n=0\},
\qquad 1\le n\le L.
$$

采用定义 164.1 的全部 $3(2^L-1)+1$ 个事件行。对 $x=(a_1,\ldots,a_L;e)$，每个 $w\in\Omega_n$ 的 $\{0\},\{n\},\{0,n\}$ 三行需求分别为 $1-a_n-e,a_n-e,1-e$；$1^L$ 的 $\{0\}$ 行需求为 $1-e$。负的单点需求也保留。记此需求向量为 $d(x)$，表 $D$ 的事件指示向量为 $z_D$。取

$$
R=(1,2;1,2,0),\qquad
\alpha=(1,1,0,\ldots,0;0),\qquad
\mathbf r=z_R=d(\alpha),\qquad h(x)=d(x)-\mathbf r.
\tag{190.1}
$$

这里 $R$ 的三个标签依次对应停止胞 $0,10,11$。独立的并集行 $\{0,n\}$ 不由两条单点下界替代；所有多零字和全正字均保留。

**定义 190.2（$S$ 与扩大的 $W$ 见证目录）。** 表的整个日程和每个终端标签在回答前确定。空日程允许任意 $J_L$ 标签。单日程 $(i)$ 在零胞允许 $\{0,i\}$，在正胞允许 $\{0,i+1,\ldots,L\}$。对 $i<j$，$S_N$ 的四胞允许集合为

$$
\begin{array}{c|cccc}
\text{胞}&00&01&10&11\\\hline
\text{允许标签}&\{0,i\}&\{0,i\}
 &\{0,i+1,\ldots,j\}&\{0,j+1,\ldots,L\}.
\end{array}
\tag{190.2}
$$

$W_N$ 只扩大最后一胞为

$$
\{0\}\cup\bigl(\{i+1,\ldots,L\}\setminus\{j\}\bigr).
\tag{190.3}
$$

$S_O,W_O$ 分别采用相同允许集合，并要求 $00,01$ 共享同一标签。记 $N$ 表为 $(i,j;a,b,k,\ell)$，记停止表为 $(i,j;a,k,\ell)$。每个允许的完整确定表及其非负混合都在对应目录中。空集合范围只留下其中的标签 $0$；尤其 $j=L$ 时 $S$ 的耗尽胞只允许 $0$。

定义 176.1 的 $T_L,E_L$ 和锚 $R$ 都在 $S_O$ 中。它们是可用见证，不是对原竞争者的限制。另记

$$
I_O=\{(i,j;a,0,n):i<n<j,\ a\in\{0,i\}\}\subset W_O.
\tag{190.4}
$$

等日程、等完整表的重复描述只计一次；不同日程但相同输出函数可以保留。每个系数在同一总质量中只计一次。除空日程外，这些目录都不允许猜测小于首查询地址的正标签；$W$ 允许耗尽胞猜测首地址与次地址之间的未查询标签。

**定义 190.3（完整配置、正确下包络与受限成本）。** 对任一上述目录 $\mathcal K_C$，其中 $\mathcal K=S,W$、$C=N,O$，完整配置是有限非负系数 $\lambda_D$。令

$$
s=\sum_D\lambda_D,\qquad
q_w=\sum_D\lambda_D\mathbf e_{D(w)},\qquad
f_w=(1-s)\mathbf e_{R(w)}+q_w,
\qquad m_n(f)=\min_{w\in\Omega_n}f_w(n).
\tag{190.5}
$$

同一配置用于全部字、全部胞和全部事件行。$f$ 的坐标总和为一，但 $s>1$ 时它可有负坐标，不能称为可执行概率核。令 $A_C^{\mathcal K}$ 的列为 $z_D-\mathbf r$，并定义

$$
\rho_C^{\mathcal K}(x)=
\inf\left\{\sum_D\lambda_D:
 \lambda_D\ge0,\ A_C^{\mathcal K}\lambda\ge h(x)\right\},
\qquad \inf\varnothing=+\infty.
\tag{190.6}
$$

完整闭帽可行性就是 $f$ 的各事件坐标满足 $d(x)$；正确单点行因其需求在整个 $\Omega_n$ 上相同，等价于 $m_n(f)\ge a_n-e$。原完整目录的成本仍记为 $\rho_N,\rho_O$，绝不以受限成本替换。

## 191. 联合重耦与停止供体的归一

**定理 191.1（保留后胞联合分布的首胞重耦）。** 固定日程 $(n,j)$ 的质量 $\beta>0$。令 $A_0,A_1$ 为其 $00,01$ 胞输出 $n$ 的质量，令 $Q(k,\ell)$ 为该配置实际已有的 $10,11$ 两标签的联合质量。因此

$$
0\le A_0,A_1\le\beta,\qquad
\sum_{k,\ell}Q(k,\ell)=\beta.
$$

可以保持日程质量、四胞边缘和后两胞的联合分布，使首胞标签对只含

$$
\begin{array}{c|cccc}
(a,b)&(0,0)&(n,n)&(0,n)&(n,0)\\\hline
c_{ab}&\beta-\max(A_0,A_1)&\min(A_0,A_1)
 &(A_1-A_0)_+&(A_0-A_1)_+.
\end{array}
\tag{191.1}
$$

其中 $t_+=\max\{t,0\}$。故每个日程至多剩一种首胞分歧方向，全部字的输出律保持不变。

**证明。** 为完整表 $(n,j;a,b,k,\ell)$ 赋质量

$$
\frac{c_{ab}Q(k,\ell)}{\beta}.
\tag{191.2}
$$

四个 $c_{ab}$ 非负、总和为 $\beta$，其两首胞的标签 $n$ 边缘分别为 $A_0,A_1$。对 $(a,b)$ 求和得到原联合质量 $Q(k,\ell)$，而非另行选择的后胞边缘乘积。对 $(k,\ell)$ 求和得到 $c_{ab}$。所有组合仍在 $S$ 或 $W$ 的合法胞集合内。一个字只访问一胞，因此四个边缘不变使每个字的输出向量不变。$\beta=0$ 的日程直接省略，不作除法。这是回答前对完整表的有限耦合，不产生新的来源观测。$\square$

**定理 191.2（$W_O$ 供体的合法归一）。** 每个停止 $W$ 表可以替换为同质量的停止 $S$ 表、$I_O$ 表、单日程或空日程，保持首地址不变，保持每个字的基点指示，并使每个实际首零标签的正确指示不下降。因此每个基点与并集行都不下降，且不产生首胞分歧。

**证明。** 空日程与单日程保留。对 $(i,j;a,k,\ell)$，若 $k=\ell>0$，替换为同输出函数的单日程 $(i;a,k)$，其正胞标签 $k>i$ 合法。若 $k,\ell>0$、$k\ne\ell$ 且 $\ell<j$，令

$$
r=\min(k,\ell),\qquad t=\max(k,\ell),
$$

替换为 $(i,r;a,r,t)$。由 $i<r<t\le L$，它是合法的 $S_O$ 表；原 $k\le j$、$\ell<j$ 还保证 $r<j$。在 $w_i=0$ 时输出同为 $a$；在 $w_i=1$ 时原、新输出均为正标签，所以基点指示相同。若旧输出恰为实际首零 $r$，则 $w_r=0$，新表输出 $r$；若旧输出恰为实际首零 $t$，则 $w_r=1$，新表输出 $t$。这涵盖此前未查询的零，因实际首零定义要求它以前的所有位为正。故旧的每个正确出现均保留。

其余情况中，$\ell=0$ 或 $\ell>j$ 的表已在 $S_O$；$k=0$ 且 $i<\ell<j$ 的表在 $I_O$。若 $\ell>j$ 且 $k=0$，仍属 $S_O$。这些情况穷尽所有允许标签。标签 $0$ 从不作为正标签参加排序。正确指示非下降而基点指示不变，遂使对应并集指示非下降。$\square$

## 192. 两个完整向量的三角交换

**定理 192.1（正向交换，包括 $k=0$）。** 设 $i<n<j$、$a\in\{0,i\}$、$k\in\{0,n+1,\ldots,j\}$、$h=0$ 或 $j<h\le L$。令 $\ell$ 是日程 $(n,j)$ 在相应 $S$ 或 $W$ 目录中允许的耗尽标签。取两个表

$$
A=(n,j;0,n,k,\ell),\qquad B=(i,j;a,n,h).
$$

对二者各取相同质量 $\eta\ge0$，替换为

$$
A'=(n,j;0,k,\ell),\qquad B'=(i,n;a,n,h).
\tag{192.1}
$$

替换表属于同一相应停止目录，总质量保持 $2\eta$。每个字的基点和实际首零并集坐标不下降；每个正确坐标逐点不变；全正字的基点坐标不变。

**证明。** $A'$ 共享首胞标签 $0$，其后胞仍合法。$B'$ 的中胞 $n$ 属于 $\{0,i+1,\ldots,n\}$，其耗尽标签 $h=0$ 或 $h>j>n$ 合法。令 $u=w_i,v=w_n,z=w_j$。每单位匹配质量的向量变化是

$$
\begin{aligned}
\Delta_+
&=\mathbf e_{A'(w)}+\mathbf e_{B'(w)}
       -\mathbf e_{A(w)}-\mathbf e_{B(w)}\\
&=(1-v)z(\mathbf e_0-\mathbf e_n)
          +u(z-v)(\mathbf e_n-\mathbf e_h).
\end{aligned}
\tag{192.2}
$$

第一差为 $(1-v)z(\mathbf e_0-\mathbf e_n)$；第二差为 $u(z-v)(\mathbf e_n-\mathbf e_h)$，故 $a,k,\ell$ 均消去，特别没有排除 $k=0$ 的理由。实际变化是 $\eta\Delta_+$。

$v=z$ 时变化为零。$(v,z)=(0,1)$ 时，若 $u=0$，变化为 $\mathbf e_0-\mathbf e_n$，实际首零至多为 $i<n$，所以 $n$ 是错标签；若 $u=1$，变化为 $\mathbf e_0-\mathbf e_h$，实际首零至多为 $n$，而非零 $h>j$ 是错标签。$(v,z)=(1,0)$ 时，变化为 $u(\mathbf e_h-\mathbf e_n)$；$w_n=1$ 排除 $n$ 正确，$w_j=0$ 排除非零 $h>j$ 正确。若 $h=0$，这些式子仍成立，基点只会增加；若 $h>j$，最后一种情况只在错标签间转移质量。于是正确坐标不变、基点不下降，独立的并集坐标也不下降。在全正字 $v=z=1$，变化为零。所有后缀及多零模式均已包含在这逐字分类中。$\square$

**定理 192.2（反向交换的标量与向量）。** 设 $i<n<j$、$a\in\{0,i\}$，$k,\ell$ 是 $(n,j)$ 的合法 $W$ 后胞标签。取

$$
A=(n,j;n,0,k,\ell),\qquad B=(i,j;a,0,n)\in I_O.
$$

对二者各取质量 $\eta\ge0$，替换为

$$
A'=(n,j;0,k,\ell),\qquad B'=(i,n;a,n,0).
\tag{192.3}
$$

这保持总质量 $2\eta$，每个正确坐标逐点不变，所有基点与实际首零并集坐标不下降；全正字基点可严格增加。

**证明。** $A'$ 合法，$B'$ 在 $S_O$ 中。令 $u,v,z$ 同上，直接相减得到完整向量等式

$$
\begin{aligned}
\Delta_-
&=\mathbf e_{A'(w)}+\mathbf e_{B'(w)}
       -\mathbf e_{A(w)}-\mathbf e_{B(w)}\\
&=\bigl[(1-u)(1-v)(1-z)+uvz\bigr]
                         (\mathbf e_0-\mathbf e_n).
\end{aligned}
\tag{192.4}
$$

具体地，第一差为 $(1-v)(1-z)(\mathbf e_0-\mathbf e_n)$，第二差为 $u(v+z-1)(\mathbf e_0-\mathbf e_n)$。二者系数之和等于方括号中的标量；它不是输出向量本身。实际变化是 $\eta\Delta_-$，$k=0$ 同样合法且消去。

该系数只在 $u=v=z=0$ 或 $u=v=z=1$ 时为一。在前者实际首零至多为 $i<n$；在后者 $w_n=1$。因此所去掉的 $n$ 从不正确，只把错标签质量移到基点。全正字属于后一情况，所以它的基点增加 $\eta$。其余字变化为零，无须限制实际后缀。$\square$

## 193. 同时正确下包络、供给匹配与有限终止

**定理 193.1（首地址阶段的精确下包络）。** 假设所有首地址 $i<n$ 的非空表已经停止且依定理 191.2 归一，首地址 $n$ 的双日程已经依定理 191.1 重耦。对每个 $j>n$，令 $A_{0,nj},A_{1,nj}$ 为日程 $(n,j)$ 的两个首胞输出 $n$ 的质量。令 $\kappa_{0,nj}$ 为所有较早首地址停止 $S$ 供体 $(i,j;a,n,h)$ 的质量，令 $\kappa_{1,nj}$ 为所有 $I_O$ 供体 $(i,j;a,0,n)$ 的质量，其中 $i<n$、$h=0$ 或 $h>j$。存在常量 $\gamma_n\in\mathbb R$，使整个 $\Omega_n$ 上

$$
\begin{aligned}
f_w(n)&=\gamma_n+\sum_{j>n}
 \bigl[(A_{0,nj}+\kappa_{0,nj})(1-w_j)
       +(A_{1,nj}+\kappa_{1,nj})w_j\bigr],\\
m_n(f)&=\gamma_n+\sum_{j>n}
 \min\{A_{0,nj}+\kappa_{0,nj},
                  A_{1,nj}+\kappa_{1,nj}\}.
\end{aligned}
\tag{193.1}
$$

在 $S$ 中 $\kappa_{1,nj}=0$，无需供体归一；在 $n=L$ 时两式的和为空。

**证明。** 在 $\Omega_n$ 上，所有 $w_i$、$i<n$ 固定为一。空日程与单日程给正确 $n$ 的贡献是常量。首地址大于 $n$ 的非空表不能输出 $n$，因为所有允许的正标签至少为首地址。首地址为 $n$ 的单日程给常量，双日程只访问 $00$ 或 $01$，产生两个 $A$ 项。

较早首地址双日程若次地址不大于 $n$，其访问胞固定，贡献并入 $\gamma_n$。若其次地址 $j>n$，归一后的 $S$ 表只能在中胞输出 $n$，贡献 $\kappa_{0,nj}(1-w_j)$；归一后的 $I_O$ 表只能在耗尽胞输出 $n$，贡献 $\kappa_{1,nj}w_j$。这穷尽所有表。锚 $R(w)$ 在各 $\Omega_n$ 上为常量：$n=1,2$ 时等于 $n$，其余时等于 $0$，所以可能有符号的 $1-s$ 只改变 $\gamma_n$。后缀各位在 $\Omega_n$ 中独立自由，逐项选取较小值同时可达，得到第二式。多零后缀也是这些选取之一。$\square$

**定理 193.2（碰撞损失的消除及合法合并）。** 在定理 193.1 的阶段，以正向交换匹配增加型首胞分歧与 $\kappa_0$ 供体，以反向交换匹配减少型分歧与 $\kappa_1$ 供体。有限次后可以合并全部首地址 $n$ 的双日程首胞，同时保持当前正确下包络和所有先前处理的正确坐标，使每个基点及并集行不下降，总质量不变。

**证明。** 固定 $j$ 并暂略下标。重耦后增加型质量为 $\delta_+=(A_1-A_0)_+$，减少型质量为 $\delta_-=(A_0-A_1)_+$，二者至多一个非零。未经匹配便把首胞合并，会造成当前正确下包络损失

$$
\begin{aligned}
D&=\min(A_0+\kappa_0,A_1+\kappa_1)
                  -\min(A_0,A_1)-\min(\kappa_0,\kappa_1)\\
 &=\min\{\delta_+,(\kappa_0-\kappa_1)_+\}
          +\min\{\delta_-,(\kappa_1-\kappa_0)_+\}.
\end{aligned}
\tag{193.2}
$$

若 $A_1\ge A_0$，减去公共 $A_0$ 后，第一行变为 $\min(\kappa_0,\delta_++\kappa_1)-\min(\kappa_0,\kappa_1)$，即第二行的第一项；另一顺序对称。因此 $D\ge0$，仅作最小值合并不足以保证下包络。

把实际增加型完整表与实际 $\kappa_0$ 供体逐一匹配。每步取两者剩余质量的最小值 $\eta$，执行定理 192.1，直到一类耗尽。总匹配质量恰为 $\min(\delta_+,\kappa_0)$。同理用定理 192.2 匹配减少型与 $\kappa_1$，总匹配质量为 $\min(\delta_-,\kappa_1)$。匹配不能抽取互不相容的边缘质量：它抽取的是重耦所得完整分歧表及真实完整供体，各表可以按质量分割。

每单位正向匹配令 $A_1,\kappa_0$ 各减一单位，新增较早首地址、次地址为 $n$ 的表，在整个 $\Omega_n$ 上恒输出 $n$，使 $\gamma_n$ 增一单位。反向匹配令 $A_0,\kappa_1$ 各减一单位，同样使 $\gamma_n$ 增一单位。这也直接核对了定理 192.1、192.2 的逐点正确坐标守恒。

对固定 $j$，每一步至少耗尽一个有限的分歧或供体分量。替换的 $A'$ 已共享首胞，替换的较早首地址表次地址为 $n$，不会再进入次地址 $j>n$ 的供给。故既没有新分歧，也没有可回流的同阶段供体，匹配有限终止。其后

$$
\min(\delta_+,\kappa_0)=0,
\qquad \min(\delta_-,\kappa_1)=0,
\tag{193.3}
$$

这里均指剩余质量。式 (193.2) 遂给 $D=0$。在 $S$ 中只有正向分支，损失简化为 $\min\{\kappa_0,\delta_+\}$。

现合并日程 $(n,j)$ 的首胞：共享标签 $n$ 的质量取 $a=\min(A_0,A_1)$，其余首胞输出 $0$。设此时日程质量为 $\beta$，后两胞的实际联合质量为 $Q(k,\ell)$。若 $\beta>0$，给共享首胞类型 $(n,n)$ 与 $(0,0)$ 分别赋完整表质量 $aQ(k,\ell)/\beta$ 与 $(\beta-a)Q(k,\ell)/\beta$；$\beta=0$ 则省略。这个合并保留实际后胞联合分布和总质量。

合并后的当前下包络是

$$
\gamma_n+\sum_{j>n}
 [\min(A_{0,nj},A_{1,nj})
                     +\min(\kappa_{0,nj},\kappa_{1,nj})],
\tag{193.4}
$$

由 $D=0$ 恰等于合并前值。首胞中每种标签 $n$ 的边缘只会减少，质量转入 $0$，因此基点逐字不下降。在当前 $\Omega_n$ 上并集 $\{0,n\}$ 的质量不变；在较早首零类上只去掉错标签 $n$，正确坐标不变且并集不下降；在较晚首零类和全正字上首胞未被访问。故同一合并同时保存全部已经处理的正确下包络并改善所有基点、并集行。各 $j$ 的供体独立按次地址分组，新增常量表不进入其他 $j>n$ 的组，以上操作可依次完成。$\square$

## 194. 全长度的同质量转换

**定理 194.1（$S$ 的精确下包络与 $W$ 的非下降转换）。** 对每个 $L\ge3$、$s\ge0$，每个质量为 $s$ 的完整 $S_N$ 配置都存在质量恰为 $s$ 的完整 $S_O$ 配置。以 $f^N,f^O$ 表示它们含同一锚的仿射向量，则

$$
\begin{aligned}
f_w^O(0)&\ge f_w^N(0)&& (w\in B_L),\\
f_w^O(0)+f_w^O(n)&\ge f_w^N(0)+f_w^N(n)
                                      &&(w\in\Omega_n),\\
m_n(f^O)&=m_n(f^N)&& (1\le n\le L),\\
f_{1^L}^O(0)&=f_{1^L}^N(0).
\end{aligned}
\tag{194.1}
$$

每个完整 $W_N$ 配置同样存在等质量 $W_O$ 配置，前两行保持，后两行保证

$$
m_n(f^O)\ge m_n(f^N),\qquad
f_{1^L}^O(0)\ge f_{1^L}^N(0).
\tag{194.2}
$$

此陈述不要求正确坐标逐字支配，也不要求保留原 $N$ 的完整输出律。$W$ 的非下降正确下包络陈述不排除其他构造恢复等式。

**证明。** 按首地址 $n=1,\ldots,L$ 作有限归纳。阶段开始时，所有较早首地址非空表均已停止，较晚首地址保持原合法胞集合。空日程与单日程始终保留。在 $W$ 中先归一所有较早首地址的停止供体，运用定理 191.2；其首地址不变，所有正确指示只会增加，基点不变、并集不下降。在 $S$ 中不需要这一步。

重耦当前首地址的每个双日程，运用定理 191.1，保持全部字律以及后胞联合分布。由定理 193.1 得到当前完整首零类的精确下包络。执行定理 193.2 的有限供体匹配和首胞合并。两种交换的正确坐标逐点守恒；合并恰保留当前下包络，并保留较早首零类的每个正确坐标。新供体的首地址小于 $n$ 且已停止，新当前表也已停止，没有新较早分歧。因此归纳不变量传到下一首地址。

所有操作均保持总质量，逐字保持或改善基点和相应并集坐标。在 $S$ 中，重耦不改变正确坐标，交换逐点保持正确坐标；一次合并只调整当前首零类的正确分布但精确保留其下包络，此后操作在此类上只改变错标签。故每个最终正确下包络恰等于初值。全正字不访问被合并的首胞，正向交换在此字无变化，所以其基点也恰等于初值。

在 $W$ 中，供体归一可能增加任何首零类的正确坐标，反向交换可能增加全正字基点。其余操作仍如上保持已处理下包络。因此各最终下包络和全正字基点均不小于初值。此论证同时处理所有首零类，没有用分别达到的极小值冒充同一个字；只有式 (193.1) 的独立后缀各项极小值确实可同时实现。

每个阶段从有限完整表开始，重耦和归一产生有限完整表，匹配因每步耗尽分量且不能回流而有限终止。共有 $L$ 个阶段，最后所有双日程都共享首胞，得到对应停止目录的完整配置。$n=1$ 没有较早供体，$n=L$ 没有后缀和双日程。零质量、相等边缘、供体不足及 $s=0$ 都由空操作或非严格最小值处理。$s>1$ 的有符号锚在新旧向量中完全相同，所有比较均为有限仿射等式或不等式，不把它当作概率律。$\square$

**定理 194.2（完整帽行的受限可行性相等）。** 对定义 190.1 的任一有限参数 $x$，

$$
\rho_N^S(x)=\rho_O^S(x),\qquad
\rho_N^W(x)=\rho_O^W(x),
\tag{194.3}
$$

包括值 $0$ 与 $+\infty$。在任一给定质量 $s$ 上，两个相应目录的完整闭帽可行性相等；特别是质量一的概率可行性投影相等。

**证明。** 当前正确需求 $a_n-e$ 在 $\Omega_n$ 上恒定，故正确下包络非下降保存全部正确行。基点与并集行由定理 194.1 逐字保存，全正行也保存。于是每个可行 $N$ 配置产生同质量可行 $O$ 配置。反向把每个停止表的共享首胞复制为两个 $N$ 首胞，得到同律、同质量的合法 $N$ 配置。忽略的回答在原执行中仍计请求。因此各质量可行性相等，取下确界即得式 (194.3)；不可行与零质量分支不需要极限。$s=1$ 时向量确为概率核，得到概率投影相等。$\square$

**定理 194.3（整个停止目录的必要得分界）。** 若一个 $S_N$ 或 $W_N$ 配置以质量 $s$ 满足全部帽行，则对每个非负完整行得分 $y$，

$$
y\cdot h(x)\le s\Delta_O(y),\qquad
\Delta_O(y)=\max_{D\in\mathcal D_O}
                    y\cdot(z_D-\mathbf r)\ge0.
\tag{194.4}
$$

最大值取原完整有限停止目录，而不是受限目录。

**证明。** 定理 194.1 给同质量可行停止配置 $\mu$。于是

$$
y\cdot h(x)\le y\cdot A_O\mu
 =\sum_D\mu_D\,y\cdot(z_D-\mathbf r)
 \le\Bigl(\sum_D\mu_D\Bigr)\Delta_O(y).
$$

锚 $R\in\mathcal D_O$ 使 $\Delta_O(y)\ge0$。这包括 $s=0$ 和 $\Delta_O(y)=0$，无须除法。$y$ 可同时给所有多零字、单点、并集和全正行赋权；此证明使用新配置的帽可行性，不声称新旧律之间每种加权正确行得分均增加。$\square$

## 195. 扩大目录中的全正等式边界

**定理 195.1（$W$ 不能普遍附加全正基点等式）。** 在 $L=3$，取质量各为 $1/2$ 的

$$
A=(2,3;2,0,0,0)\in W_N,\qquad
B=(1,3;0,0,2)\in W_O.
\tag{195.1}
$$

所得概率核 $p$ 满足

$$
p_{011}(0)=p_{110}(0)=1,\qquad
p_{111}(0)=p_{101}(0)=\tfrac12,\qquad
m_2(p)=\tfrac12.
\tag{195.2}
$$

即使允许整个有限停止目录，也不存在概率核 $p'$ 同时逐字支配这些基点行、满足 $m_2(p')\ge1/2$，并保持 $p'_{111}(0)=1/2$。这否定的是加强的支配加等式要求，不是闭帽可行性的分离。

**证明。** 直接代入两个表得到式 (195.2)：$\Omega_2=\{100,101\}$，两个字上的正确标签 $2$ 质量均为 $1/2$。若 $p'$ 存在，则其任一正质量确定停止表 $D$ 必须同时满足 $D(011)=D(110)=0$。

对每个这样的完整停止表，有

$$
\mathbf1_{D(100)=2}+\mathbf1_{D(111)\ne0}
                    \le\mathbf1_{D(101)\ne0}.
\tag{195.3}
$$

若 $D(111)\ne0$，为区分 $111$ 与强制零输出的 $011,110$，日程必须同时查询地址 $1,3$。因此恰为 $(1,3)$，其 $101,111$ 输出相同，$100,110$ 输出相同，故 $D(101)\ne0$、$D(100)=0$。

若 $D(100)=2$，为区分 $100$ 与 $110$ 必须查询地址 $2$。若再有 $D(101)=0$，为区分 $100$ 与 $101$ 还须查询地址 $3$，日程只能为 $(2,3)$。但二字的地址 $2$ 均为零，停止规则不能继续取得地址 $3$，两输出必相同，矛盾。故也有 $D(101)\ne0$。而前一种非零全正情况的日程 $(1,3)$ 不能满足后一种查询 $2$ 的必要条件，两项左事件不能同时发生。这证明式 (195.3)，也覆盖空日程与单日程。

混合该不等式，得

$$
p'_{100}(2)+1-p'_{111}(0)\le1-p'_{101}(0).
$$

左边由正确下包络及全正等式至少为一，右边由基点支配至多为 $1/2$，矛盾。定理 194.1 在 $W$ 中允许增加全正基点，因而不受此反例影响。证明没有证明正确下包络等式不可恢复，亦没有给出某个帽下全停止类不可行的证书。$L=3$ 是出现 $i<n<j$ 的最小长度。$\square$

## 196. 可执行概率、同种子与每条原始尾部

**定理 196.1（锥配置的概率填充与原始实现）。** 设定理 194.1 的转换配置质量为 $s$，且它满足 $A_N^{\mathcal K}\lambda\ge h(b)$，其中 $\mathcal K=S$ 或 $W$。对

$$
0\le\tau\le\frac1{\max\{1,s\}},
\tag{196.1}
$$

令转换后的各表概率为 $\tau\mu_D$，另加锚 $R$ 概率 $1-\tau s$。它给出一个合法停止概率核，满足参数 $x=\alpha+\tau(b-\alpha)$ 的全部闭帽行。质量一的原 $N$ 配置及其转换 $O$ 配置可以使用同一个与来源无关的种子，且原始实现保留全部字、实际尾部、闭端点和硬两请求契约。

**证明。** 式 (196.1) 使所有概率非负且总和为一，包括 $\tau s=1$。若锚已有系数，只把填充质量加到该坐标一次。事件向量为

$$
\mathbf r+\tau A_O^{\mathcal K}\mu
 \ge\mathbf r+\tau h(b)
 =d\bigl(\alpha+\tau(b-\alpha)\bigr).
\tag{196.2}
$$

最后的仿射身份由 $d(\alpha)=\mathbf r$ 直接得到，亦是式 (165.5) 的既有径向身份。所有帽行用同一概率配置，未拆分单点、并集预算。$\tau=0$ 是有限辅助锚；$s>1$ 的原仿射 $f$ 不因满足某些行而被称为概率律，只有上述非负填充概率可执行。

在 $s=1$ 时，把一个来源无关的 $U\in[0,1)$ 分成长度为 $\mu_D$ 的半开区间，零质量省略，区间预先固定整个表。原 $N$ 配置也有同一 $U$ 上自己的固定区间分割；两分割可取有限共同细化。因此两规则使用同一个种子，而不要求同一种子处输出相同。上述重耦、归一与交换均在回答前完成，未添加额外随机观测。填充情形以同样方式先选锚或完整表。

选定 $O$ 表后，实际查询其至多两个递增素数地址，遇首次被查询零即停，或正回答耗尽日程；随后交付原纸带 $\theta_{D(w)}$。所有记录和输出事件均可测，每个来源和种子处执行有限。其 $N$ 完成规则使用完全相同的 $U$，取得整个预选日程的全部回答，再重构停止胞；忽略的请求仍计数。单日程和空日程亦按其实际长度计数。硬预算始终是实际请求数，不是地址、深度、时间或平均数。

原来源明确为定义 110.1 的

$$
\begin{aligned}
X&=\{(r,g):r\text{ 为素数},\ g\in\mathbb Z,
      \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\quad q_i(x)=\mathbf1_{p_i\mid N(x)},
\quad n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
$$

其中 $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$。输出的 $\theta_j=(B_1,1/(j+2))$ 是原完整载体 $\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$ 内的不同原始点，每块为 $(0,1)$ 的副本；消费者和原非原子目标不变。有限字的实际实现由定义 110.1 所引有限纤维结果供应，所有多零模式都在帽行中。这里未创造无限全正来源。

停止概率核的 $\mathscr C_L$ 成员资格及其 $c\ge H$、$\beta\le1$ 概率向量条件复用[定理 109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#109-an-exact-coefficient-criterion-with-one-common-probability-budget)。对每个实际 $n(x)>L$，规则看到有限字 $1^L$，但目标仍带实际原标记 $\theta_{n(x)}$。由该卷式 (110.9)，精确尾误差为

$$
\operatorname{TV}\left(\sum_{j=0}^Lp_{1^L}(j)\delta_{\theta_j},
     (1-a_{n(x)})\delta_{\theta_0}
                +a_{n(x)}\delta_{\theta_{n(x)}}\right)
 =\max\{1-p_{1^L}(0),a_{n(x)}\}.
\tag{196.3}
$$

因最终全正基点不下降，原来的每个实际尾幅 $a_n\le e$ 都保留，包括 $a_{L+1}=e$。任何晚零均不改变这个结论，实际尾目标没有被折叠为 $0$。

原始正闭帽及其实际活跃长度的充分与必要运输，复用[定理 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)：它承担任意地址、重复计数和完整载体输出的必要性，本构造只提供合法见证，不限制竞争者。辅助长度大于实际活跃长度时，仍按该既有运输在实际长度处理，而不提出新的缩短定理。

若 $b$ 来自完整正、单调、消失幅序列且尾部满足帽比较，则径向应用在 $\tau>0$ 时采用[定理 170.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#170-every-original-tail-under-the-same-radial-law-identity) 的整个序列身份：前两幅变为 $1-\tau(1-b_i)$，所有 $i\ge3$，包括每个实际 $i>L$，变为 $\tau b_i$，帽为 $\tau e_b$。于是正性、次序、消失性及所有尾帽比较保留。辅助零幅或零帽端点只属有限几何，不宣称它们是正原始尾序列。这些运输及误差身份均使用已有供应定理。$\square$

## 197. 剩余的见证存在桥梁

**定义 197.1（预算截断下的 $W_N$ 存在义务）。** 采用定义 165.1 的

$$
\begin{aligned}
Q_L=\{&(a_1,\ldots,a_L;e):
 1\ge a_1\ge\cdots\ge a_L\ge e\ge0,\\
 &(L+1)e\le\sum_{i=3}^La_i,\quad
 a_1+\sum_{i=3}^La_i-(L+1)e\le1\},\qquad
H_L=Q_L\cap\{a_2=a_3\}.
\end{aligned}
$$

对每个仍待比较的长度和每个 $b\in H_L$，若完整目录成本 $s=\rho_N(b)<\infty$，令 $M=\max\{1,s\}$。剩余的一个充分桥梁是存在某个配置

$$
\lambda_D\ge0\ (D\in W_N),\qquad
A_N^W\lambda\ge h(b),\qquad
\sum_D\lambda_D\le M.
\tag{197.1}
$$

式 (197.1) 尚未对所有这样的 $b,L$ 得到证明。它允许选择不同的 $N$ 律，不要求表示某个给定的完整 $N$ 律，也不要求每个非最优表示都能转换。

**定理 197.2（充分桥梁与分离的必要现象）。** 若式 (197.1) 成立，则完整成本 $\rho_O(b)\le M$。因此任何真正的完整目录分离 $\rho_O(b)>\max\{1,\rho_N(b)\}$ 都必须排除该预算内的一切 $W_N$ 可行见证。若 $s\ge1$ 且式 (197.1) 成立，则 $\rho_O(b)=\rho_N(b)$；若 $s<1$，所需结论只是 $\rho_O(b)\le1$。没有 $W_N$ 见证本身不是完整分离的充分证据。

**证明。** 转换式 (197.1) 的见证，定理 194.1 给质量不变的 $W_O$ 可行见证。它属于完整停止目录，故 $\rho_O(b)\le\sum_D\lambda_D\le M$。对 $s\ge1$，再用已有 $\rho_N\le\rho_O$ 得成本相等；$s<1$ 时 $M=1$。逆否命题给分离的必要条件，但完整停止目录仍可能在 $W_O$ 以外取得可行见证，所以不作逆向推断。径向预算与原比较的对应使用定理 167.2、170.1，而不由此额外证明普遍的式 (197.1)。$\square$

**定理 197.3（按转录修剪后的缺口定位）。** 在完整 $N$ 目录的任一胞中，把不可能成为实际首零的正输出改为 $0$：被查询为正的同名标签不可能正确；已有更早查询零时，晚于它的标签也不可能正确。修剪逐字改善基点与并集指示，不损正确指示，不改日程及总质量。修剪后，若每个非空日程的所有正标签都不小于首地址，配置恰落在 $W_N$。所以存在式 (197.1) 的见证，等价于存在预算 $M$ 内某个完整 $N$ 可行配置，其修剪后的完整表全部遵守 $W$ 胞集合。

**证明。** 被修剪的标签在该胞兼容的所有实际字上都不是首零，故改到 $0$ 保持正确指示并改善另两事件指示。单日程 $(i)$ 的零胞在排除首地址以前的猜测后只剩 $0,i$，正胞只剩 $0$ 或大于 $i$ 的标签。双日程 $(i,j)$ 的 $00,01$ 胞只剩 $0,i$；$10$ 胞只剩 $0$ 或 $i<t\le j$；$11$ 胞只剩 $0$ 或大于 $i$ 且不等于 $j$ 的标签，恰为式 (190.2)、(190.3)。空日程任意标签仍保留。反向 $W$ 表已经符合这些兼容性，修剪不改变它，故存在量词的两种表述等价。

若真正完整分离发生，则任何预算 $M$ 内完整 $N$ 可行配置经修剪后都不能全部落在 $W_N$，因而必须保留某个非空日程猜测首地址以前正标签的正质量。该现象只是一切可行见证上的必要条件：一个给定配置包含这种猜测，不排除另一个配置满足式 (197.1)，也不推出该给定律缺少精确 $W$ 表示。较早未查询标签的正确质量可以共同依赖两个后缀位，定理 193.1 的一位供体分解没有涵盖它。消除这些项而保持预算的正规形构造仍是证明义务。$\square$

上述转换的承重步骤是供体归一、两个向量交换和有限首地址归纳。定理 119.3 的首胞等式限于五活跃等式面；定理 178.2、命题 179.2 提供 $E_L$ 的后缀形式和锥质量填充，它们各自的范围仍保持。完整目录的得分最大值使用定义 164.3、166.1；式 (194.4) 只是已构造见证的必要界。利用完整目录对偶证明普遍预算桥梁或构造完整分离证书，均仍需另行证明。没有将其他受限目录合并为 $W$，也没有由受限成本相等推出普遍比较或幅族分类。

数学引文：Kaniewski、Lee 与 de Wolf，[*Query complexity in expectation*，定义 8、定理 9、§3.1–3.2](https://arxiv.org/pdf/1411.7280)，提供确定查询树的随机混合及标量非负文字式的既有框架，其最坏路径请求数与标量期望结论并不提供这里共享向量预算及递增首零停止转换。Boyd 与 Vandenberghe，[*Convex Optimization*，§5.2.3–5.2.4](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)，提供强对偶与线性规划例子的既有框架；§5.2.3 为强对偶及 Slater 条件，§5.2.4 含线性规划对偶例子。有限重耦、交换恒等式与首地址归纳的证明不以额外对偶假设为前提。

## 追加锚（本行以下为增补区）

## 198. 完整目录得分约化、符号凸包与混合预算缺口

本节固定原始硬两资源。源是
$$
X=\{(r,g):r\ {\rm 为素数},\ g\in\mathbb Z,\ \lceil F_r/10\rceil\le g\le
\lfloor F_r/5\rfloor\},\qquad N(r,g)=1+F_rg,
$$
静态回答为 $q_i(x)=\mathbf 1_{p_i\mid N(x)}$，实际首个缺失地址
$n(x)=\min\{i:q_i(x)=0\}$ 总是有限。每个有限标记字都有实际源点。$N_2$
预先选取至多两个实际请求并取得全部回答，重复请求仍计数；$O_2$ 预先选取递增
地址并在第一次被查询到的零处停止，正回答耗尽时也停止。两者均只使用一个与源无关
的共同种子，输出可以是原始完整纸带上的任意标记。下面的权重是对这些实际字的有限
行系数，不是源上的概率分布。

对首零为 $n$ 的每个零字 $w$，保留三条独立事件行：基行、正确行和并行行，权重
分别记为 $A_w,C_w,P_w$，其需求为
$$
1-b_n-e,\qquad b_n-e,\qquad 1-e.
$$
全一字的基行权重记为 $T$，需求为 $1-e$。任何输出标签
$0,\ldots,L$ 在空、单点及双点终端胞中都保留；权重为零只表示该行当前不贡献分数，
不删除原始约束。对首零为 $n$ 的字，三个事件的输出奖励向量分别是
$$
F_0(w)=A_w+P_w,\qquad F_n(w)=C_w+P_w,\qquad F_r(w)=0\ (r\notin\{0,n\}),
$$
而全一字只有 $F_0(1^L)=T$。令
$$
\beta_n=\sum_{w:\,\operatorname{first0}(w)=n}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
$$
则目标函数商为
$$
Q(y).h(b)=\sum_{n=1}^L\beta_n(b_n-\alpha_n)-Ke,\qquad
\alpha=(1,1,0,\ldots,0;0).
\tag{198.1}
$$
所有差分坐标都允许带符号。对完整的 $N$ 与 $O$ 目录，分别以全部空、单点和双点
终端胞的全标签最大值定义 $B_N(y),B_O(y)$，并令
$$
\mathbf r=d(\alpha),\qquad
\Delta_C(y)=B_C(y)-y\mathbin{\cdot}\mathbf r\quad(C=N,O).
\tag{198.2}
$$
这里的 $B_C$ 是完整目录最大值，包含多零字、任意输出标签和全一字。

**定理 198.1（首零单点到并行行的精确饱和约化）。** 对每个非负行权重 $y$，在每个
零字置
$$
t_w=\min\{A_w,C_w\},\qquad
D_y=\sum_w t_w,
$$
并定义
$$
S(y)_w=(A_w-t_w,\ C_w-t_w,\ P_w+t_w),\qquad
S(y)_{1^L}=T.
\tag{198.3}
$$
则 $S(y)$ 保持每个字的三个奖励向量、保持 $y\mathbin{\cdot}\mathbf r$、保持
$B_N,B_O$ 以及两个 $\Delta_C$，并且
$$
S(y).h=y.h+eD_y.
\tag{198.4}
$$
把统一 $H_L$ 证书写成下列充分性断言：
$$
\forall y\ge0\;\Bigl(\Delta_O(y)\le1\Longrightarrow
\exists V\ge0\;\exists\theta\in[0,1],\;
\Delta_N(V)\le1-\theta\ \land\
\sup_{b\in H_L}(y-V).h(b)\le\theta\Bigr).
\tag{198.5}
$$
在这个存在性断言内，输入可以限制为饱和行，输出也可以限制为饱和见证；这给出
(198.5) 的充分路线及其在该存在性证书内的饱和等价性，原始普遍比较的必要性不在本节范围内。

**证明。** 对任意不同标记 $0,n$，其单点指示函数之和逐字等于并行指示函数，即使
字同时在两标记之外也成立。因此从两条单点行各移去 $t_w$，并把 $t_w$ 加到并行
行，三种奖励在每个字上逐点不变，所有目录的最大值和锚坐标也不变。需求系数的差为
$$
(1-e)-(1-b_n-e)-(b_n-e)=e,
\tag{198.3a}
$$
逐字求和得到 (198.4)。固定奖励 $x,z$ 的表示为
$x-p,z-p,p$，其中 $0\le p\le\min(x,z)$；总权重 $x+z-p$ 在
$p=\min(x,z)$ 唯一最小。因而当 $e>0$ 时，饱和表示唯一最大化得分需求；当
$e=0$ 时，纤维中的表示在需求上全部并列。

先处理输入。若饱和输入 $S(y)$ 的 (198.5) 见证是同一个 $V$ 与 $\theta$，则
$$
(y-V).h(b)=(S(y)-V).h(b)-eD_y\le\theta
$$
对每个 $b\in H_L$ 成立，而 $\Delta_O(S(y))=\Delta_O(y)$。所以对所有饱和
输入成立就对所有输入成立；反向只是把全输入断言限制到饱和输入。

再处理输出。若 $V$ 是任意输入的一个存在性见证，以同样的饱和变换替换它，则
$\Delta_N(S(V))=\Delta_N(V)$，并且
$$
(y-S(V)).h(b)=(y-V).h(b)-eD_V\le(y-V).h(b).
$$
因此存在饱和输出见证当且仅当存在一般输出见证。两步合起来，(198.5) 的输入和输出
限制确实是等价的存在性约化；它不声称每一个未饱和输出都满足该界，原始普遍比较的
必要性也不在本节范围内。饱和不是加法：一条基行和一条正确行各为一时，逐行饱和得到一条
并行行，而分别先饱和后相加仍保留两条单点行；所以不能从此约化继承分解预算。

**定理 198.2（共同非齐次马尔可夫目录的完整支持相等）。** 设 $L\ge3$，所有首零
类和事件类型使用同一族非负二阶行随机矩阵
$$
P_1,\ldots,P_L,\qquad
P_k(u,0)+P_k(u,1)=1\quad(u=0,1).
$$
令
$$
\pi_n(w)=\prod_{k=n+1}^{L}P_k(w_{k-1},w_k)
$$
为固定首零类中的后缀乘积，并以这些乘积乘上非负类总量构造完整行权重。则
$$
B_N(y)=B_O(y),\qquad \Delta_N(y)=\Delta_O(y).
\tag{198.6}
$$
特别地，在 $\Delta_O(y)\le1$ 时，取 $V=y,\theta=0$ 即给出 (198.5) 的证书。

**证明。** 对 $i<j$ 且 $w_i=0$，把奖励乘积在 $i,j$ 处分开。对 $j$ 后的
后缀求和为一；从 $i$ 处的状态零到 $j$ 处状态 $v$ 的转移矩阵为
$$
K_{ij}=P_{i+1}P_{i+2}\cdots P_j .
$$
因而对每个输出标签 $r$ 同时有
$$
G_{ij}^{0v}(r)=K_{ij}(0,v)\,G_i(r).
\tag{198.7}
$$
系数非负且对 $v$ 求和为一，所以 $N$ 的 $00,01$ 两胞最大值之和恰为
$O$ 合并胞的最大值。空日程、单日程及其余双胞逐项相同；再对全部标签和全部首零
类取最大，得到 (198.6)。矩阵只参数化了对偶行权重的共同乘积，既不是源点上的概率
律，也不引入第二条源轨迹。若对每一行同步取最小值，所得饱和行仍有相同的乘积因子，
故这一类在 (198.3) 下闭合。

**定理 198.3（四码正确行的精确吸收）。** 设 $L\ge6$，取四个字
$$
0\,1\,1\,1\,0\,0\,1^{L-6},\quad
1\,0\,1\,1\,0\,1\,1^{L-6},\quad
1\,1\,0\,1\,1\,0\,1^{L-6},\quad
1\,1\,1\,0\,1\,1\,1^{L-6}
$$
的首零类编码为 $n=1,2,3,4$，在第 $5,6$ 位分别附加码
$00,01,10,11$，只给正确事件非负权重 $\nu_1,\nu_2,\nu_3,\nu_4$。更简洁地，
把四个码字记作 $w_1,\ldots,w_4$，并令
$$
m=\min_i\nu_i,\qquad
d=\nu_3+\nu_4-m,\qquad
\tau=\nu_3+\nu_4-\frac85m .
\tag{198.8}
$$
则
$$
B_N(y)=\sum_{i=1}^4\nu_i,\qquad
B_O(y)=\sum_{i=1}^4\nu_i-m,\qquad
y\mathbin{\cdot}\mathbf r=\nu_1+\nu_2,
\tag{198.9}
$$
且
$$
0\le\tau\le d,\qquad \sup_{b\in H_L}y.h(b)\le\tau .
\tag{198.10}
$$
若 $d>0$，归一化商 $y/d$ 由 $V=0$ 和
$\theta=\tau/d\in[2/5,1]$ 证实 (198.5)；若 $d=0$，取
$V=0,\theta=0$。四个权重都为一时，端点 $2/5$ 由 $v_4$ 达到：前四个幅均为 $1$，其余幅和
帽均为 $2/5$。这是既有定理 87.1 的重叠极限，而非新的幅族分类。对有限和使用
时，这一项只提供一个显示的残差预算 $\tau$，不声称存在普遍的逐项分解预算。

**证明。** $N$ 查询两个码位可命中四个码字，故得 (198.9) 的第一式。任何停止的
硬两表至多有三个终端标签；因此只能收集四个权重中最大的三个。反之，任意选定的
三个数值标签，查询其中最早两个，耗尽时猜其最大标签，即可在三个停止胞中收集它们，
故第二式成立。将单调系数写成
$$
a=b_1,\qquad c=b_2=b_3,\qquad x=b_4,
$$
由 $a_i\ge e\ (i\ge5)$ 及前缀约束得
$$
a+c+x-5e\le a+c+x+\sum_{i=5}^La_i-(L+1)e\le1.
\tag{198.11}
$$
于是
$$
a+2c+x-4e
 \le \min\{2+e,\ 4-4e\}\le\frac{12}{5}.
\tag{198.12}
$$
四个缺额
$$
u=(1-a+e,\ 1-c+e,\ 1-c+e,\ 1-x+e)
$$
的总和至少为 $8/5$。将 (198.12) 代入
$y.h=\nu_3+\nu_4-\sum_i\nu_i u_i$，得到
$$
y.h\le\nu_3+\nu_4-\frac85m=\tau.
$$
又 $\nu_3+\nu_4\ge2m$，故 $0\le\tau\le d$。$d>0$ 时作径向归一化；
$d=0$ 时没有除法。等权时取
$$
v_4=(1,1,1,1,2/5,\ldots,2/5;2/5),
$$
其中所有后续幅和闭帽均为 $2/5$，下约束取等，且
$a+2c+x-4e=12/5$，故 $y.h(v_4)=2/5$。这正是定理 87.1 的既有四码尖端；
其余坐标不是新的幅族分类。

**定理 198.4（任意正确行加全正尾的前三大项迁移）。** 设 $C_n\ge0$ 是首零类
$n$ 的全部正确行总量，$T\ge0$ 是全正基行总量。令
$$
q_3=\text{multiset}\{C_1,\ldots,C_L,T\}\text{ 的前三大项之和}.
\tag{198.13}
$$
构造 $V$ 如下：把每个 $C_n$ 放在吸收链字
$1^{n-1}0^{L-n+1}$ 的正确行，并保留全正行 $T$。则
$$
B_O(y)=B_N(V)=B_O(V)=q_3,\qquad
y\mathbin{\cdot}\mathbf r=V\mathbin{\cdot}\mathbf r=C_1+C_2+T,
\tag{198.14}
$$
从而 $Q(y)=Q(V)$ 且
$$
\Delta_N(V)=\Delta_O(y).
\tag{198.15}
$$
归一的 $y$ 若满足 $\Delta_O(y)\le1$，则 $V,\theta=0$ 是统一证书。任何
只含正确行和全正尾的完整目录都不能给出
$\rho_O>\max\{1,\rho_N\}$ 的分离。

**证明。** 固定停止表只使用至多三个标签。数值标签 $n$ 在所有首零为 $n$
的字上最多获得 $C_n$，标签零只从全正行获得 $T$，故得分不超过
$q_3$。选取前三大项；若全为数值标签 $i<j<k$，先询问 $i,j$，在三个停止胞
分别输出 $i,j,k$，便同时命中所选三类；若零项被选，则输出 $i,j,0$。并列时任取
前三项。吸收链上任意排序的 $N$ 双询问只出现 $00,10,11$ 三类，故同一上界可达，
得到 (198.14)。式 (198.1) 只依赖 $C_n,T$，锚也只依赖这两个总量，故得到
(198.15)。这处理每个多零字及三条独立行；某行得分为零并不删除其原始约束。

这里必须区分行得分 $y,V$ 与原始锥分配。固定 $b\in H_L$，令
$\lambda\ge0$ 是实际的 $N$ 目录分配，满足
$$
A_N\lambda\ge h(b),\qquad s=\sum_D\lambda_D.
$$
若得分 $y$ 在归一域中满足 $\Delta_O(y)\le1$，定理 198.4 给出的 $V$ 仍是
非负得分，且 $\Delta_N(V)=\Delta_O(y)\le1$。由弱对偶性，
$$
y.h(b)=V.h(b)\le V.A_N\lambda
       \le s\,\Delta_N(V)\le s.
\tag{198.16}
$$
当 $s<1$ 时，把零列 $R$ 的系数补成 $1-s$：
$\lambda'=\lambda+(1-s)e_R$ 仍满足 $A_N\lambda'\ge h(b)$，质量为一，因而同一
推理给出 $y.h(b)\le1=\max\{1,s\}$；$s\ge1$ 时则直接有
$y.h(b)\le s=\max\{1,s\}$。因此该家族不可能成为正确行加尾的完整分离器。
这里的 $y,V$ 从始至终都是得分向量，$\lambda$ 才是分配；本结论不提供任意
混合基行/并行行的 $O$ 原始分配。四码例的精确迁移属于本定理的正确行子类，其
残差吸收仍按 (198.10) 使用。

**定理 198.5（全长度带符号 $H_L$ 的精确凸包支持）。** 设
$$
\begin{aligned}
H_L=\{(a_1,\ldots,a_L;e):\;&1\ge a_1\ge\cdots\ge a_L\ge e\ge0,\\
 &(L+1)e\le\sum_{i=3}^La_i,\quad
 a_1+\sum_{i=3}^La_i-(L+1)e\le1,\quad a_2=a_3\}.
\end{aligned}
\tag{198.17}
$$
令
$$
q(a,e)=\sum_{n=1}^L\beta_n(a_n-\alpha_n)-Ke,\quad
B=\beta_1+\beta_2,\quad
S_k=\sum_{n=1}^k\beta_n,\quad
\kappa=K-S_L .
\tag{198.18}
$$
则 $H_L$ 的凸包恰由 $2L-2$ 个点
$$
\begin{aligned}
o&=0,\qquad p=(1,0,\ldots,0;0),\\
u_k&=(\underbrace{1/(k-1),\ldots,1/(k-1)}_{k},0,\ldots,0;0),\\
v_k&=(\underbrace{1,\ldots,1}_{k},\underbrace{e_k,\ldots,e_k}_{L-k};e_k),\qquad
 e_k=\frac{k-2}{k+1},\qquad 3\le k\le L
\end{aligned}
\tag{198.19}
$$
生成。对任意有符号的 $(\beta,K)$，都有精确支持公式
$$
\sup_{(a,e)\in H_L}q(a,e)
 =
\max\left\{
 -B,\ -\beta_2,\
 \max_{3\le k\le L}\left(\frac{S_k}{k-1}-B\right),\
 \max_{3\le k\le L}\left(
 \frac{3S_k-(k-2)\kappa}{k+1}-B
 \right)
\right\}.
\tag{198.20}
$$
故残差约束是在完整的 $2L-2$ 个线性顶点不等式上检验，而不要求
$\beta_n,K,\kappa$ 非负。零容量顶点仅属辅助凸几何，不是原始正尾的实现者。

**证明。** 令 $a_{L+1}=e$，$x_i=a_i-a_{i+1}$，则 $x_2=0$，而
$x_1,x_3,\ldots,x_L,e\ge0$。记
$$
D=\sum_{k=3}^L(k-2)x_k.
$$
式 (198.17) 等价于
$$
D\ge3e,\qquad
\ell=x_1+\sum_{k=3}^L(k-1)x_k-2e\le1.
\tag{198.21}
$$
此外 $\ell=a_1+D-3e\ge a_1$，故 $a_1\le1$。将 $e$ 分配到容量
$(k-2)x_k/3$，再把每一对 $(x_k,e)$ 分裂为射线
$$
(x_k,e)=(1,0),\qquad (x_k,e)=(1,(k-2)/3),
$$
并保留 $x_1$ 射线，即可把任一点写成这些射线的非负组合；各射线的
$\ell$-值分别是 $k-1,(k+1)/3$ 和 $1$，再把未用的系数放到 $o$。
归一化第一类射线给 $u_k$，第二类给 $v_k$，$x_1$ 给 $p$，因而得到
(198.19) 的生成。直接代入 (198.18)：
$$
q(o)=-B,\quad q(p)=-\beta_2,\quad
q(u_k)=\frac{S_k}{k-1}-B,
$$
以及
$$
q(v_k)=\frac{3S_k-(k-2)\kappa}{k+1}-B.
$$
线性函数在凸包上的上确界是顶点最大值，得到 (198.20)。由于系数是差分坐标，
该推导对所有符号成立，不能把残差当作非负权重表。

**定理 198.6（混合吸收链迁移的预算反例）。** 对 $L\ge4$，在
$0101,1010,1101,1110$ 上分别放置单位并行、并行、正确、正确行，并在后面接全
一尾。则
$$
B_N(y)=B_O(y)=3,\qquad y\mathbin{\cdot}\mathbf r=2,\qquad
\Delta_O(y)=1.
\tag{198.22}
$$
把四行仅按首零类迁移到吸收链所得 $V$ 具有
$$
B_N(V)=B_O(V)=4,\qquad
V\mathbin{\cdot}\mathbf r=2,\qquad
\Delta_N(V)=2,
\tag{198.23}
$$
且其商坐标为 $\beta_3=\beta_4=1$、其余 $\beta_n=0$、$K=4$。然而
$$
\sup_{b\in H_L}y.h(b)=\frac23.
\tag{198.24}
$$
所以该迁移不是保留完整得分预算的普遍方法，也不是原始帽下的分离证书。

**证明。** 要同时命中 $0101$ 上的单位并行奖励和 $1101$ 上的单位正确奖励，必须查询地址一；要同时
命中 $1010$ 上的单位并行奖励和 $1110$ 上的单位正确奖励，必须查询地址二。两次查询后，$1101$ 与 $1110$
具有相同的 $11$ 记录而奖励不交，故四行不能全部命中。相反，停止表
$(1,2;1,2,3)$ 命中其中三行，得到 (198.22)。附加的全一位不增加信息。
吸收链表 $(2,3;0,3,4)$ 可命中四行，给出 (198.23)；锚只命中两条并行行。
在 $H_L$ 中写 $a=b_1\ge c=b_2=b_3\ge x=b_4$，则
$$
a+c+x-5e\le1,\qquad
c+x\le\frac{2(a+c+x)}3
 \le\frac23+\frac{10e}3 .
$$
因此
$$
y.h=c+x-4e\le\frac23-\frac{2e}3\le\frac23,
$$
而前四个幅均为 $1/3$、其余幅和 $e$ 为零时取等。这个例子只否定所选的
首零类迁移，不否定另一种提升或残差吸收。

**定理 198.7（单一零位迁移与非零零成本商）。** 对 $L\ge3$，在字 $110$ 上放
单位正确行，在 $010,100$ 上分别放单位并行行，在 $111$ 上放单位正基行。原
完整支持和锚均为三，故
$$
\Delta_N(y)=\Delta_O(y)=0,\qquad
Q(y):\ \beta_3=1,\ \beta_n=0\ (n\ne3),\ K=4.
\tag{198.25}
$$
把两条并行行迁移为 sole-zero 字 $011,101$ 后，完整目录的支持均为四，锚仍为三，
因而 $\Delta_N=\Delta_O=1$，商 $Q$ 不变；整体乘二给出输入
$\Delta_O=0$ 与固定迁移 $\Delta_N=2$ 的输出。定义
$$
D_N(c)=\{Q(V):V\ge0,\ \Delta_N(V)\le c\},
\tag{198.26}
$$
则 $D_N(0)\ne\{0\}$。因此 $\theta=1$ 端点必须保留全部零成本的非零商，不能把
$\Delta_N(V)\le0$ 简化为 $V=0$。

**证明。** 若表在 $110$ 上输出标签三，因硬两请求必漏掉前三个位中的某一位；翻转
所漏位分别得到 $010,100,111$，这些字保留相同的已查询记录和输出，却失去该
正确行奖励。这里的 $110$ 是正确行事件；$010,100$ 是并行行事件，三者的奖励
事件在该论证中是分开的。若表不输出标签三，正确奖励本身至多损失，故全目录上界为
三且由直接表达到。迁移后，查询地址三并在零胞输出三、在正胞输出零，即可命中四行。
对 $L>3$，在四个显示字后追加相同的 $1^{L-3}$；这些坐标在显示字上恒为一，即使被查询也不提供区分信息，故该见证可不查询它们，而任意竞争者无须回避这些坐标。
首零类总量、锚以及 (198.1) 的商坐标均未改变。缩放保持商方向而把固定迁移的
$\Delta_N$ 放大到二，得到 (198.26) 的非零零成本元素。

**定理 198.8（有限条件和的单一预算证书）。** 设有限和分解为
$$
y=\sum_t M_t+\sum_j C_j+\sum_k E_k,
\tag{198.27}
$$
其中 $M_t$ 属于定理 198.2 的共同马尔可夫类，$C_j$ 属于定理 198.4 的
正确行加尾类，$E_k$ 属于定理 198.3 的四码类。令
$$
V=\sum_t M_t+\sum_j\operatorname{chain}(C_j),\qquad
\theta=\sum_k\tau(E_k).
\tag{198.28}
$$
若待检验的得分还满足归一条件 $\Delta_O(y)\le1$，并且
$$
\sum_t\Delta_O(M_t)+
\sum_j\Delta_O(C_j)+\theta\le1,
\tag{198.29}
$$
则
$$
0\le\theta\le1,\qquad
\Delta_N(V)\le1-\theta,\qquad
\sup_{b\in H_L}(y-V).h(b)\le\theta.
\tag{198.30}
$$
这里的归一条件与分项预算分别承担 (198.5) 的输入域和输出剩余预算，不能互相替代。
固定任意 $b\in H_L$ 及实际的非负 $N$ 分配 $\lambda$，满足
$$
A_N\lambda\ge h(b),\qquad S=\sum_D\lambda_D.
$$
$V$ 是得分向量而不是分配。弱对偶性给出
$$
V.h(b)\le V.A_N\lambda\le S\,\Delta_N(V)\le S(1-\theta).
$$
令 $E=y-V$。由 (198.30)，$E.h(b)\le\theta$，所以
$$
y.h(b)\le S(1-\theta)+\theta.
\tag{198.31}
$$
当 $S\ge1$ 时右端不超过 $S$。当 $S<1$ 时，以零列 $R$ 补足
$\lambda'=\lambda+(1-S)e_R$；它保持 $A_N\lambda'\ge h(b)$，质量变为一，故
$V.h(b)\le1-\theta$，进而$y.h(b)\le1=\max\{1,S\}$。
这是一个展示的充分分解，不是任意 $y$ 的分解定理。

**证明。** 完整目录支持函数满足次可加性，
$$
\Delta_N\left(\sum_i y_i\right)\le\sum_i\Delta_N(y_i).
$$
定理 198.2 给出每个 $M_t$ 的 $N/O$ 支持相等，定理 198.4 给出
$\operatorname{chain}(C_j)$ 的支持不增，故 (198.29) 推出 $\Delta_N(V)\le1-\theta$。
对每个四码项，定理 198.3 给出残差不超过 $\tau(E_k)$；有限求和得到 (198.30)。
随后对任意给定的 $b,\lambda$ 使用上面的弱对偶及零列补足，得到 (198.31)。全程只
使用一个显示的总预算。一般地，$\Delta_O(\sum_i y_i)$ 可能严格小于
$\sum_i\Delta_O(y_i)$，所以总和支持小并不推出 (198.29)；逐项饱和也不是加法。
该证书没有给出任意饱和混合基/并行行的归一提升，也没有制造新的停止概率核。

**定理 198.9（原始源上的共同种子与尾部保持）。** 上述每个有限支持的确定停止表及
其有限混合，都可在原始源上实现为同一个源无关种子的规则：先以 $U\in[0,1)$ 的
固定区间选择整张表和全部终端标签，再按所选表预先提出至多两个递增素数请求；首次
查询到零即停止，正回答耗尽则交付终端标签。对应的 $N_2$ 规则使用同一个 $U$
选择整张表，取得预选日程全部回答，再按相同终端胞输出，忽略的回答仍计入请求数。
因此每个源点和种子处均为实际有限交付，重复地址也按硬两次计数。规则输出的是原始
完整载体中的标记，原消费者与原非原子目标不变；选定的
$\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}}$
仍只是分别选取的标记律，不把源赋予概率分布，也不改变原目标。

在正、单调、消失幅序列上，定理 109.1 的归一概率向量条件仍精确给出停止核：
其向量条件为 $c\ge H$，而 108.4 说明在归一化域中标量
$\beta\le1$ 自动成立；这里的标量 $\beta$ 是 108.3 的调度总质量，
不是 (198.1) 的带符号坐标 $\beta_n$，也不能把这两个条件误写成相互独立的两个预算。定理 110.2
承担完整载体和任意地址竞争者的闭帽必要性与充分性，定理 170.1 承担同一径向因子
下的全序列尾部身份。对实际首零 $n>L$，全正字的精确误差为
$$
\max\{1-p_{1^L}(0),a_n\},
\tag{198.32}
$$
其中实际尾幅满足 $0<a_{L+1}\le e$，等号允许；全正行基点及其余实际尾幅按既有
径向身份同时缩放，保持正性、次序和趋零性。定理 198.5 证明中写作
$a_{L+1}:=e$ 只是凸包的辅助几何赋值，不替代这个实际尾部条件；多零字、零转移、
闭端点和相等权重都包含在这些逐字行中。辅助凸包中的零幅和零容量点不被称为原始
正尾的实现者。

**证明。** 有限表的终端概率向量分割来自同一个 $U$ 的半开区间，表的选择先于
任何回答；条件分割只读取已获得的停止胞，因此没有第二个随机源。有限实际首零保
证查询和交付终止。原始源的每个有限字模式都有实际见证，故表的逐字行在原源上
确实被执行。尾部遇到 $1^L$ 时输出分布只由全正胞决定，与实际标记
$\theta_{n(x)}$ 的两点全变差给出 (198.32)。其余运输、任意地址和重复请求的必要
性直接使用既有 110.2；不以有限支持表限制竞争者。径向缩放由既有 170.1 的整个序列
公式给出，未把辅助 $e=0$ 点扩充为正尾序列。

**命题 198.10（完整原始比较的剩余精确缺口）。** 对每个 $L\ge3$、每个原始正、
单调、趋零幅序列和每个正闭帽，仍需证明
$$
\mathcal F_N\ne\varnothing\quad\Longrightarrow\quad
\mathcal F_N\cap\mathcal C_L\ne\varnothing,
\tag{198.33}
$$
或给出一个满足原始共同种子 $N_2$ 契约的具体达到者，以及针对原始完整载体、任意
地址的 $O_2$ 统一下界证书。等价地，在有限 $\rho_N$ 的适用方向上，仍需建立
$$
\rho_O(b)\le\max\{1,\rho_N(b)\}.
\tag{198.34}
$$
本节已经排除了正确行加全正尾家族的分离，给出了共同马尔可夫、四码残差和有限
条件和的充分路线，并把所有残差检验化为 (198.20) 的有限带符号支持。但是，任意
饱和混合基行与并行行仍可能有更便宜的替代提升或被吸收的残差；尚无保持
$D_N(0)$ 中非零商、完整终端胞支持和同一归一预算的普遍提升定理。定理 198.6 和
198.7 的固定迁移失败只是方法边界，不是原始帽分离；本命题因而保留
(198.33) 的未决义务，不声称普遍成功、完整分类或新的原始 $O$ 概率核。

## 追加锚（本行以下为增补区）
## 199. 完整事件锥的有符号替代、零成本闭包与剩余原始比较

本节的锥与商固定 $L\ge3$，定义 199.9 的原始帽切片允许全部活跃长度 $L\ge0$。
沿用定义 190.1、164.1、165.1 的完整事件行、完整 $N$ 与
$O$ 目录以及
$$
H=H_L=\{b=(b_1,\ldots,b_L;e):1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\ b_2=b_3,\ (L+1)e\le\sum_{n=3}^Lb_n,\ b_1+\sum_{n=3}^Lb_n-(L+1)e\le1\}.
$$
记 $\alpha=(1,1,0,\ldots,0;0)$、$\mathbf r=d(\alpha)$。所有不等式均为闭不等式，
所有目录均包含空表、单日程、双日程、全部输出标签、多零字、独立 pair 行和全正字行。

完整目录 $\mathcal D_C$ ($C=N,O$) 指所有空、单点和双点终端胞的完整表；事件行总数为
$3(2^L-1)+1$。对 $w\in\Omega_n$，基行、正确行、独立 pair 行的需求分别为
$1-b_n-e$、$b_n-e$、$1-e$，全正字 $1^L$ 的基行需求为 $1-e$；负的单点需求和
多零字均保留。这些行的需求向量记为 $d(b)$，并令 $h(b)=d(b)-\mathbf r$。因而
$z_D$ 与 $G_C$ 都同时编码全部 Boolean 字、独立 pair TV 行、零权重的行和全正行，
而不是只编码当前评分的非零坐标。

**定义 199.1（完整事件行、目录矩阵与有符号商）。** 对每个完整表 $D$，令
$z_D$ 为它在全部事件行上的事件指示向量，并令
$$
a_D=z_D-\mathbf r.
$$
对 $C\in\{N,O\}$，令 $G_C$ 是列为所有 $a_D$ 的完整矩阵。因锚表 $R$ 在两个完整目录中均有
$a_R=0$，对任意非负事件评分
$$
y=(A_w,C_w,P_w)_{w\ne1^L}\ ,\quad T\ge0
$$
定义
$$
\beta_n=\sum_{w\in\Omega_n}(C_w-A_w),\qquad
K_y=\sum_{w\ne1^L}(A_w+C_w+P_w)+T,
$$
并置 $Q(y)=(\beta_1,\ldots,\beta_L,K_y)$。对任意有符号对
$q=(\beta_1,\ldots,\beta_L,K)\in\mathbb R^{L+1}$，置
$$
F_q(b)=\sum_{n=1}^L\beta_n(b_n-\alpha_n)-Ke,
\qquad
\sigma_H(q)=\max_{b\in H}F_q(b).
\tag{199.1}
$$
于是 $F_{Q(y)}(b)=y\!\cdot h(b)$；简记 $F_y=F_{Q(y)}$。评分 $y$ 和下文的评分
$V$ 始终逐行非负，而商差 $q-q'$ 可以是任意有符号向量。比如
$(0,-1,1,0,\ldots,0;0)$ 在 $H$ 上表示常数一，因为 $b_2=b_3$；它不是任何
非负评分的代表，这不改变有符号商的定义。

**定义 199.2（预算像、有序锥、有限方向和完整证书集）。** 对 $C\in\{N,O\}$ 和
$t\ge0$，置
$$
\Delta_C(y)=\max_{D\in\mathcal D_C}a_D\!\cdot y\ge0,
\qquad
D_C(t)=\{Q(y):y\ge0,\ \Delta_C(y)\le t\}.
\tag{199.2}
$$
令
$$
P_H=\{q:F_q(b)\le0\ \text{对所有 }b\in H\},
\qquad q\preceq_Hq'\ \Longleftrightarrow\ q-q'\in P_H,
\tag{199.3}
$$
并记 $\rho_C$ 为定义 166.1 的完整目录锥质量；定义 190.3 定义受限成本并保留这一
完整成本记号，此处始终使用完整目录。令
$$
H_C=\{b\in H:\rho_C(b)<\infty\}.
$$
定义完整 $N$ 证书集
$$
E_N=\left\{q:\begin{array}{l}
\exists V\ge0\ \exists\theta\in[0,1],\\
\Delta_N(V)\le1-\theta\ \text{且}\ \sigma_H(q-Q(V))\le\theta
\end{array}\right\}.
\tag{199.4}
$$
特别地，当 $\theta=1$ 时允许每一个满足 $V\ge0$、$\Delta_N(V)=0$ 的非零
$V$；零评分、零预算和 $\theta=0$ 也不被删除。

**定理 199.3（任意有符号商的完整单预算替代）。** 对任意固定
$q\in\mathbb R^{L+1}$，恰有一项成立：

* (I) $q\in E_N$；
* (II) 存在 $b\in H$ 以及完整 $N$ 目录上的有限向量
  $\lambda=(\lambda_D)_{D\in\mathcal D_N}\ge0$，使
  $$
  G_N\lambda\ge h(b),\qquad
  M=\sum_{D\in\mathcal D_N}\lambda_D\ge1,
  \qquad F_q(b)>M.
  \tag{199.5}
  $$

**证明。** 取定理 198.5 给出的 $H$ 的有限顶点表示
$H=\operatorname{conv}\{v^1,\ldots,v^m\}$，其中 $m=2L-2$。由于 $F_q-F_{Q(V)}$
关于 $b$ 仿射，(I) 等价于非负变量 $(V,\theta)$ 的有限系统
$$
\begin{cases}
 a_D\!\cdot V+\theta\le1,&D\in\mathcal D_N,\\
 -h(v^j)\!\cdot V-\theta\le-F_q(v^j),&1\le j\le m,\\
 V\ge0,\quad\theta\ge0.
\end{cases}
\tag{199.6}
$$
第一组中 $D=R$ 的列为零，所以它同时给出 $\theta\le1$；闭端点没有被删去。

对形如 $Mx\le d, x\ge0$ 的系统应用等式形 Farkas 替代：系统不可行当且仅当
存在乘子 $w\ge0$ 使 $M^{\mathsf T}w\ge0$ 且 $d\!\cdot w<0$。这是把非负松弛并入
有限生成锥后的形式，见 Volker Kaibel, *Basic Polyhedral Theory*,
[arXiv:1001.2161v1, Theorem 1(ii)](https://arxiv.org/abs/1001.2161)；有限锥闭性
和点—射线表示亦见该文 Theorems 7、8、10。将目录行乘子记为
$\lambda_D\ge0$，顶点行乘子记为 $\mu_j\ge0$，不可行性给出
$$
G_N\lambda\ge\sum_j\mu_jh(v^j),\qquad
S:=\sum_D\lambda_D\ge u:=\sum_j\mu_j,\qquad
\sum_j\mu_jF_q(v^j)>S.
\tag{199.7}
$$
严格不等式迫使 $u>0$；若 $u=0$，则最后一式变成 $0>S\ge0$。置
$$
\bar b=\frac1u\sum_j\mu_jv^j\in H,
\qquad \bar\lambda=\lambda/u,
\qquad M=\sum_D\bar\lambda_D=S/u.
$$
由 $h$ 与 $F_q$ 的仿射性，(199.7) 变为
$$
G_N\bar\lambda\ge h(\bar b),\qquad M\ge1,\qquad F_q(\bar b)>M,
$$
即 (II)。

反过来若 (I)、(II) 同时成立，则对 (II) 中的 $b,\lambda$，由
$V\ge0$、$G_N\lambda\ge h(b)$ 及弱对偶性得
$$
\begin{aligned}
F_q(b)&\le F_{Q(V)}(b)+\theta
       =V\!\cdot h(b)+\theta\\
&\le V\!\cdot G_N\lambda+\theta
 \le M\Delta_N(V)+\theta\\
&\le M(1-\theta)+\theta\le M,
\end{aligned}
$$
最后一步用 $M\ge1$ 与 $\theta\ge0$。这与 $F_q(b)>M$ 矛盾，故两项互斥；
Farkas 替代又保证其中一项必有，结论涵盖 $M=1$、$\theta=0,1$ 和所有零权重。取
$q=Q(y)$ 即得全部非负事件评分的结论；这只是本定理在非负评分像上的特例，不另立
第二个替代定理。$\square$

**推论 199.4（精确成员判据与原始截断比较）。** 对任意有符号 $q$，
$$
q\in E_N
\quad\Longleftrightarrow\quad
F_q(b)\le\max\{1,\rho_N(b)\}
\quad\text{对所有 }b\in H_N.
\tag{199.8}
$$
因而
$$
D_O(1)\subseteq E_N
\quad\Longleftrightarrow\quad
\rho_O(b)\le\max\{1,\rho_N(b)\}
\quad\text{对所有 }b\in H_N.
\tag{199.9}
$$
这里的左侧是完整的证书存在性断言，右侧是原始完整目录的 clipped comparison，
所以 (199.9) 是等价式而不是实际包含性的证明。

**证明。** 若 $q\in E_N$ 且 $b\in H_N$，取达到 $\rho_N(b)$ 的完整配置；若其质量
小于一，则在零列 $R$ 上补足到质量一。定理 199.3 的互斥性给出
$F_q(b)\le\max\{1,\rho_N(b)\}$。反之，若该点态界成立而 $q\notin E_N$，
(II) 给出 $F_q(b)>M\ge1$ 且 $\rho_N(b)\le M$，从而
$F_q(b)>\max\{1,\rho_N(b)\}$，矛盾。

令 $q=Q(y)$ 并对所有 $y\ge0$、$\Delta_O(y)\le1$ 取上确界。完整目录的
有限锥对偶（定理 166.2）给出该上确界为 $\rho_O(b)$，包括无穷值，故得到
(199.9)。饱和约化只能在这个不受限制的线性替代完成以后使用：定理 198.1 的
输入、输出饱和保持证书的存在性，但此处没有把饱和误作凸约束或加法，也没有由此
声称 (199.9) 的左侧已经成立。$\square$

**定理 199.5（零成本有序闭包）。** 对 $C=N,O$，有精确恒等式
$$
D_C(0)+P_H
=\{q:F_q(b)\le0\ \text{对所有 }b\in H_C\}.
\tag{199.10}
$$
特别地，
$$
D_O(0)\subseteq D_N(0)+P_H
\quad\Longleftrightarrow\quad H_N\subseteq H_O.
\tag{199.11}
$$
由于 $O$ 是 $N$ 的子类而 $H_O\subseteq H_N$，(199.11) 等价于
$H_N=H_O$，也等价于
$D_O(0)+P_H=D_N(0)+P_H$。这里不需要、也不声称
$D_O(0)=D_N(0)$，更不声称两个原始商集严格不同。

**证明。** 先取 $q=Q(V_0)+p$，其中 $V_0\ge0$、$\Delta_C(V_0)=0$、$p\in P_H$。
若 $b\in H_C$，取有限配置 $\lambda\ge0$ 使 $G_C\lambda\ge h(b)$，则
$$
F_q(b)\le V_0\!\cdot h(b)
 \le V_0\!\cdot G_C\lambda
 =\sum_D\lambda_D(a_D\!\cdot V_0)\le0.
$$
反向设 $F_q\le0$ 在 $H_C$ 上成立。要求 $V_0\ge0$ 同时满足
$$
 a_D\!\cdot V_0\le0\ (D\in\mathcal D_C),
 \qquad -h(v^j)\!\cdot V_0\le-F_q(v^j)\ (1\le j\le m).
\tag{199.12}
$$
若该系统不可行，应用同一 Farkas 替代，得到 $\lambda_D,\mu_j\ge0$ 且
$$
G_C\lambda\ge\sum_j\mu_jh(v^j),\qquad
\sum_j\mu_jF_q(v^j)>0.
$$
此时 $u=\sum_j\mu_j>0$，否则严格式不可能成立。以 $u$ 归一的仿射重心
$b=\sum_j\mu_jv^j/u$ 属于 $H$，且
$G_C(\lambda/u)\ge h(b)$、$F_q(b)>0$，所以 $b\in H_C$，与假设矛盾。
因此 (199.12) 有解；其第一组给 $\Delta_C(V_0)=0$，第二组给
$q-Q(V_0)\in P_H$，从而得到 (199.10)。

若 (199.11) 左侧成立，任取 $b\in H_N$ 和任意
$Q(y_0)\in D_O(0)$。由 (199.10) 的 $N$ 侧恒等式，
$F_{Q(y_0)}(b)\le0$。定理 166.2 证明中以“Cone feasibility is”开头的段落
对一般 $C$ 给出极性可行性判据：取 $C=O$，上述所有零成本非负评分的不等式
恰保证存在 $\lambda\ge0$ 使 $G_O\lambda\ge h(b)$，所以
$\rho_O(b)<\infty$，即 $b\in H_O$。反之若 $H_N\subseteq H_O$，任取
$q\in D_O(0)$，由 $O$ 侧 (199.10) 得 $F_q\le0$ 在 $H_O$ 上，因而也在
$H_N$ 上；再用 $N$ 侧 (199.10) 得 $q\in D_N(0)+P_H$。这证明 (199.11) 及其等价形式。
$\square$

**定理 199.6（闭多面体的衰退锥与零成本吸收）。** 对 $t\ge0$ 及
$C=N,O$，
$$
\operatorname{rec}D_C(t)=D_C(0),
\tag{199.13}
$$
并且
$$
\operatorname{rec}E_N=D_N(0)+P_H.
\tag{199.14}
$$
因此对 $q_0\in D_O(0)$，射线
$\{s q_0:s\ge0\}$ 全部属于 $E_N$ 当且仅当存在
$V_0\ge0$ 使 $\Delta_N(V_0)=0$ 且
$q_0-Q(V_0)\in P_H$。若 $Q(y)$ 已由 $(V,\theta)$ 证实，且
$Q(y_0)=q_0$ 有上述零成本提升，则对任意 $s\ge0$，同一 $\theta$ 由
$V+sV_0$ 证实 $Q(y+s y_0)$。

**证明。** 评分多面体
$$
Y_C(t)=\{y\ge0:a_D\!\cdot y\le t\ (D\in\mathcal D_C)\}
$$
非空，其衰退系统为 $Y_C(0)$。有限维多面体的线性像仍为闭多面体，且
$\operatorname{rec}(Q(Y_C(t)))=Q(\operatorname{rec}Y_C(t))$；这是 Kaibel
上述文献 Theorems 7、8、10 的有限锥表示的直接应用，故得 (199.13)。

把 $E_N$ 写成变量 $(q,V,\theta)$ 的有限投影：$V\ge0$、
$a_D\!\cdot V+\theta\le1$、$0\le\theta\le1$ 以及
$F_{q-Q(V)}(v^j)\le\theta$。衰退方向的 $\theta$ 分量必须为零，且
$V_0\ge0$、$a_D\!\cdot V_0\le0$，并满足
$F_{q_0-Q(V_0)}(v^j)\le0$。故其 $q$ 投影正是
$D_N(0)+P_H$；反向将任意这两个分量代入上述齐次系统即得 (199.14)。

$0\in E_N$，取 $V=0,\theta=0$ 即可。对闭凸集，零点出发的整条射线在该集内当且仅当其方向属于衰退锥：必要性可由任意
$z\in E_N$、$t\ge0$ 和
$(1-\varepsilon)z+\varepsilon(t/\varepsilon)q_0\in E_N$，令
$\varepsilon\downarrow0$ 并用闭性得到 $z+tq_0\in E_N$。于是射线判据由
(199.14) 得出。

最后，若 $Q(y)$ 有 $(V,\theta)$ 证书，则
$$
\Delta_N(V+sV_0)\le\Delta_N(V)+s\Delta_N(V_0)\le1-\theta,
$$
且对每个 $b\in H$，
$$
F_{Q(y+s y_0)-Q(V+sV_0)}(b)
=F_{Q(y)-Q(V)}(b)+sF_{q_0-Q(V_0)}(b)\le\theta.
\tag{199.15}
$$
这里用的是已建立的零成本增量；没有把任意 $O$ 评分的预算误拆成各分量预算，
也没有由零衰退控制推出正预算结论。$\square$

**命题 199.7（完整证书失败产生有限概率见证）。** 设 $y\ge0$、
$\Delta_O(y)\le1$ 且 $Q(y)\notin E_N$。则存在 $b\in H$、完整 $N$ 配置
$\lambda\ge0$ 及 $M=\sum_D\lambda_D\ge1$，令
$$
x=(1-M^{-1})\alpha+M^{-1}b,
$$
则 $x\in Q_L$，配置 $\lambda/M$ 是质量一的完整 $N$ 概率向量，并且
$$
G_N(\lambda/M)\ge h(x),
\qquad y\!\cdot d(x)>y\!\cdot\mathbf r+1\ge
 y\!\cdot\mathbf r+\Delta_O(y).
\tag{199.16}
$$
所以所有完整 $O$ 概率配置都被同一评分的严格 support gap 排除。

**证明。** 由定理 199.3 的 (II) 取 $b,\lambda,M$。凸性给
$x\in Q_L$，且
$$
\mathbf r+M^{-1}G_N\lambda\ge
\mathbf r+M^{-1}h(b)=d(x).
$$
因为 $F_y(b)>M$，
$$
 y\!\cdot d(x)=y\!\cdot\mathbf r+M^{-1}F_y(b)
 >y\!\cdot\mathbf r+1
 \ge y\!\cdot\mathbf r+\Delta_O(y).
$$
右端是完整 $O$ 目录在评分 $y$ 下的最大值，故严格支撑间隔排除了任意完整
$O$ 概率配置。若 $x$ 位于辅助零容量或非活跃坐标边界，沿用定理 168.1 的
正闭帽平台和定理 110.2 的原始运输；该平台的每个活跃幅严格高于正帽，证明不需要
所有确定表有正质量，也不需要所有事件行严格松弛。内部方向的定量间隔沿用定理
169.2。此命题是由证书失败推出见证的条件命题，不反向声称存在失败评分。$\square$

**定理 199.8（按目录实现的共同种子与原始边界）。** 保留定义 110.1 的实际源
$$
X=\{(r,g):r\text{ 为素数},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},
\qquad N(r,g)=1+F_rg,
$$
以及静态素数回答、实际有限首缺 $n(x)$ 和每个有限布尔字的实际源见证。纸带仍为
完整不交并 Borel 载体 $\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$，
标记仍为 $\theta_j=(B_1,1/(j+2))$；原消费者在同一源和交付的原纸带上运行，
原非原子目标不变。另行选定的标记律为
$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad 1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\to0.
\tag{199.17}
$$
对每个 $C\in\{N,O\}$，任取完整目录 $\mathcal D_C$ 上的概率向量
$w=(w_D)_{D\in\mathcal D_C}$，其中 $w_D\ge0$、$\sum_Dw_D=1$。用一个
来源无关的 $U\sim\operatorname{Unif}[0,1)$，在回答前选定整张表及全部终端标签：
$\mathcal D_N$ 上的混合实现原始 $\mathcal N_2$ 规则，取得预选日程的全部回答；
$\mathcal D_O$ 上的混合实现原始 $\mathcal O_2$ 规则，在递增日程的首个实际查询零
或耗尽时停止。对后一规则，按命题 90.2 取得全部预选回答并忽略首零之后的回答，
得到保持每个源的输出律及同一个 $U$ 的 $\mathcal N_2$ 补全；额外取得而忽略的
实际请求仍全部计数。

这些实现零建议、有限交接，硬预算为至多两次实际请求，重复请求也计数。完整目录
按定义 164.2 用静态回答消去重复并规范日程，只用于表示律，不断言平均次数不变。
原始竞争者仍可使用任意地址、重复请求（在 $\mathcal N_2$ 中）和完整载体输出；
不加入源律、源标签、$N(x)$、首缺值、额外观察、第二种子、运行时间界或地址界。

乘子有两个不同的指标域：$\mu_j/u$ 对辅助顶点 $v^j\in H_L$ 取重心；
命题 199.7 的 $w_D=\lambda_D/M$ 对完整 $N$ 表取概率混合。在式 (199.7) 的
未归一乘子记号下，后一个操作为
$$
\bar b=\sum_j\frac{\mu_j}{u}v^j,\qquad
w_D=\frac{\bar\lambda_D}{M}
    =\frac{\lambda_D/u}{S/u}=\frac{\lambda_D}{S},
\qquad u=\sum_j\mu_j>0,\quad S=\sum_D\lambda_D\ge u.
$$
命题 199.7 将 $\bar\lambda$ 重新记为 $\lambda$。将式 (199.7) 的全部乘子同时
乘以任一正数，两个归一操作都不变；它们均不是对实际源取平均。

表混合的实现本身不蕴含帽可行性。若它还满足完整向量不等式 $Z_Cw\ge d(x)$，
才得到该有限剖面的全部闭帽行；所有布尔字、多零字、每个独立 pair TV 行和全正行
均在其中，评分为零的行也不删除。在正帽及其实际活跃长度上，由定理 110.2
得到同类原始规则的闭帽可行性，并保留任意地址、完整载体竞争者的必要方向。
因此命题 199.7 的配置只供应 $N$ 实现；对 $O$ 的排除仍由完整 $O$ 支撑间隔及
定理 168.1、110.2 给出。

对任意有限标记核及实际首零 $n>L$，精确尾误差仍为
$$
\max\{1-p_{1^L}(0),a_n\}.
\tag{199.18}
$$
凡 $p_{1^L}(0)\ge1-\varepsilon$ 且 $a_n\le\varepsilon$，上式即不超过
$\varepsilon$，包括 $a_n=\varepsilon$。全正有限字只记录实际尾部，不是无限全正源。
在归一概率向量核上，式 (108.4) 给出标量
$\beta=\mathfrak m(H)$，故 $c\ge H$ 自动蕴含 $\beta\le1$；定理 109.1
保留这两个条件。这里的 $H$ 是系数向量，$\mathfrak m$ 对输出标签求和；
该无下标调度总质量 $\beta$ 不同于定义 199.1 的有符号商坐标 $\beta_n$。
定理 170.1 对整个实际幅序列使用同一正径向因子，每个幅仍在原标记上，保持
正性、单调性、趋零性、实际活跃长度以及相应缩放后的精确闭帽。辅助 $e=0$ 点
不是原始正尾实现者；边界运输仍仅使用定理 168.1 和 110.2。

**证明。** 对所选类别的全部表排序为 $D_1,\ldots,D_k$，将 $[0,1)$ 划为
$$
I_{D_i}=\left[\sum_{j<i}w_{D_j},\ \sum_{j\le i}w_{D_j}\right),
\qquad 1\le i\le k.
$$
这些区间长度均按完整表指标 $D$ 归一，零质量区间为空。在 $U\in I_D$ 时选表
$D$；此选择与实际源无关且先于回答。$N$ 表在双日程上有 $00,01,10,11$ 四胞，
$O$ 表有 $0,10,11$ 三胞；分别按各自转录输出，便实现相应类别的混合核。
有限日程和静态回答保证有限交接。补全 $O$ 表时，将其首零标签同时赋给 $N$ 表的
$00,01$ 胞，沿用原区间及原 $U$，故逐源、逐种子输出相同，新增忽略请求照计。

反向不能由种子划分推出：对固定双日程及固定种子，停止于第一查询零后，$00$ 与
$01$ 是同一可观察胞；在它们上取不同标签的 $N$ 表不是这个停止转录的可测函数。
这一区别适用于定义 164.2 的全部完整表。定理 112.2 进一步给出实际帽可行核
$p^N\notin\mathscr C_L$，其三个字的事件概率 $0,\gamma,0$ 违反式 (112.1)，
而另一核 $p^P$ 属于同一帽切片与 $\mathscr C_L$ 的交。因此此处没有任意
$N$ 律到 $O$ 律的同律运输。

顶点重心与表概率分别由 $\sum_j\mu_j/u=1$ 和 $\sum_D\lambda_D/M=1$
归一；后式使用命题 199.7 的配置记号。两者的指标不同，也都不在 $X$ 上选源。
若 $Z_Cw\ge d(x)$，每行事件概率恰为同一表混合的对应坐标，故全部闭帽行同时成立。
式 (199.18) 是定理 110.2 的实际尾标记与有限标记律的精确全变差式 (110.9)，
其必要方向继续覆盖任意地址与任意原纸带。式 (108.4) 的归一恒等式和定理 170.1
的整序列径向恒等式分别给出标量预算与全部正尾的保持。$\square$

**定义 199.9（原始比较的未决精确命题）。** 任取满足
$1\ge a_1\ge a_2\ge\cdots>0$、$a_i\to0$ 的整个原始幅序列以及
$0<\varepsilon\le1$，实际活跃长度为
$$
L=\max\bigl(\{i:a_i>\varepsilon\}\cup\{0\}\bigr).
$$
令 $B_L=\{0,1\}^L$、$J_L=\{0,\ldots,L\}$，共同核载体为
$$
\mathscr P_L=\prod_{w\in B_L}\Delta(J_L),\qquad
\Delta(J_L)=\left\{v\in\mathbb R_{\ge0}^{J_L}:\sum_{r\in J_L}v(r)=1\right\}.
$$
沿用定义 108.1 的 $\mathscr N_L\subseteq\mathscr P_L$，$e_r$ 为标签 $r$ 的单位
概率向量。对含零字置
$n_L(w)=\min\{i\le L:w_i=0\}$，并置
$$
\eta_w=(1-a_{n_L(w)})e_0+a_{n_L(w)}e_{n_L(w)}\quad(w\ne1^L),
\qquad \eta_{1^L}=e_0.
$$
定义 110.1 的式 (110.5) 所给的帽可行核切片是
$$
\mathcal F_N(a,\varepsilon)
=\{p\in\mathscr N_L:\operatorname{TV}(p_w,\eta_w)\le\varepsilon
                       \text{ 对每个 }w\in B_L\}.
$$
这些是式 (110.6) 的全部闭帽行，包括独立 pair 行和全正行。由于实际 $L$ 的
定义，所有 $n>L$ 都满足 $a_n\le\varepsilon$，故尾部使用式 (199.18)。

在同一归一核载体上，沿用定义 108.2 的唯一多线性系数，正部与向量不等式均逐坐标
解释。对次数至多二的核写
$$
p_w=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j,
\qquad
V_i=\sum_{j>i}(-Q_{ij})_+,\quad h_i=(V_i-\ell_i)_+,
$$
并记系数向量 $H(p)=\sum_i h_i$ 和无下标标量
$$
\beta(p)=\sum_i\max\{\mathfrak m(V_i),\mathfrak m(h_i)\},
\qquad \mathfrak m(v)=\sum_{r\in J_L}v(r)\quad(v\ge0).
$$
此处 $H(p)$ 不同于辅助剖面域 $H_L$。系数定义的停止核类为
$$
\mathscr C_L
=\{p\in\mathscr P_L:\deg p\le2,\ c\ge H(p),\ \beta(p)\le1\}
=\mathscr O_L\subseteq\mathscr N_L,
$$
最后的等式由定理 109.1 给出。核归一使
$\mathfrak m(h_i)\ge\mathfrak m(V_i)$，所以式 (108.4) 给出
$\beta(p)=\mathfrak m(H(p))\le\mathfrak m(c)=1$，其中最后一步使用
$c\ge H(p)$。$\mathscr C_L$ 的条件独立于所选帽，不能用帽行替代。

原始比较要求对上述每个整个序列及每个正闭帽成立
$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing.
\tag{199.19}
$$
由定理 110.2，后件恰为原始 $\mathcal O_2$ 帽可行性；其中的核可以不同于前件
所给的任何核，不要求保留其律。定理 112.2 的 $p^N$ 仍在帽切片内而不在
$\mathscr C_L$ 内，$p^P$ 则见证其交非空。

这些核定义包含 $L=0,1,2$，空和按零计；$\varepsilon=1$ 时 $L=0$，即刻基点
输出可行，更大的帽也由同一规则处理。小活跃长度及既有残差充分范围沿用
定义 110.3 与定理 168.1 所列供应者。对其余范围，定理 110.2、167.2 和 168.1
把普遍的式 (199.19) 等价地化为完整有限方向命题
$$
\forall L\ge3\ \forall b\in H_L,\qquad
\rho_N(b)<\infty\ \Longrightarrow
\rho_O(b)\le\max\{1,\rho_N(b)\}.
\tag{199.20}
$$
其中 $H_L$ 的零帽或非活跃坐标边界属于辅助闭域；定理 168.1 将该闭域中的失败
运输到正帽、实际活跃长度及所有允许的正单调趋零尾部，不把边界本身当作原始实现。
由推论 199.4，式 (199.20) 又等价于每个 $L\ge3$ 的完整包含
$D_O(1)\subseteq E_N$。式 (199.19)—(199.20) 仍为未决命题；零成本有序包含的
等价刻画和条件性的证书失败推论均不判定这一正预算包含。

## 追加锚（本行以下为增补区）

## 200. 较早零守卫的加权缺陷与完整证书的实际切片

本节保留[定义 110.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)的实际可数带标签来源：

$$
\begin{aligned}
X&=\{(r,g):r\text{ 为素数},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
$$

这里 $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$，$p_i$ 是递增的素数序列；回答静态，
每个有限回答字都有实际来源见证，实际 $n(x)$ 总有限。完整可测纸带载体、原标记
$\theta_j$、消费者和非原子原目标 $\mu_x$ 不变。所讨论的目标是另行选定的

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\longrightarrow0.
$$

资源严格采用[获取资源定义 90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions)：
零建议，一个与来源无关的共同种子，实际源上几乎处处有限交接，至多两次实际请求，
包括重复请求及取得后忽略的请求。$N_2$ 预选日程并取得全部回答；$O_2$ 预选严格
递增日程并在首个被查询的零或耗尽时停止。竞争者可用任意地址和完整载体内任意输出；
误差是所有实际来源上的 TV 上确界，不引入来源概率律。辅助有限剖面的零帽和零幅
仅用于以下几何，原始幅序列仍严格正且趋零。

**定义 200.1（完整评分、带符号支持与证书域）。** 固定任意整数 $L\ge3$，令
$B_L=\{0,1\}^L$、$J_L=\{0,\ldots,L\}$，对每个含零字记
$n(w)=\min\{i:w_i=0\}$、$\Omega_n=\{w:n(w)=n\}$。
沿用[定义 164.1—164.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#164-complete-deterministic-catalogs-and-event-demands)的完整目录
$\mathcal D_N,\mathcal D_O$：空日程、单日程 $(i)$ 和双日程 $(i,j)$，$i<j$，
每个终端胞允许全部 $J_L$ 标签。$N$ 的双日程胞是 $00,01,10,11$，$O$ 的胞是
$0,10,11$，其中首胞合并 $00,01$。静态回答允许用这些代表描述重复或反序日程的
输出函数，不把原执行中重复的实际请求免计。

对每个 $w\in\Omega_n$ 保留基行 $\{0\}$、正确行 $\{n\}$ 和独立 pair 行
$\{0,n\}$，在剖面 $b=(b_1,\ldots,b_L;e)$ 上的需求分别为

$$
1-b_n-e,\qquad b_n-e,\qquad1-e.
\tag{200.1}
$$

全正字 $1^L$ 的基行需求为 $1-e$。这些共 $3(2^L-1)+1$ 行组成 $d(b)$；
负的单点需求也原样保留。所有多零字都在系统中，任何评分的零权重不删除对应约束。
令 $z_D$ 为完整表的联合事件向量；对共同概率混合 $U$，$z_U$ 是同一混合在全部
事件行上的概率向量。置

$$
R=(1,2;1,2,0),\qquad \alpha=(1,1,0,\ldots,0;0),\qquad
\mathbf r=z_R=d(\alpha),\qquad h(b)=d(b)-\mathbf r.
$$

$R$ 的三个标签依次对应停止胞 $0,10,11$。令 $G_C$ 的列为全部
$z_D-\mathbf r$，$D\in\mathcal D_C$。取任意逐行非负评分
$y=((A_w,C_w,P_w)_{w\ne1^L},T)$，其中正确权重 $C_w$ 和正字权重 $T$ 均任意。
定义

$$
\begin{aligned}
B_C(y)&=\max_{D\in\mathcal D_C}y\cdot z_D,&
\Delta_C(y)&=B_C(y)-y\cdot\mathbf r\ge0\quad(C=N,O),\\
\beta_n(y)&=\sum_{w\in\Omega_n}(C_w-A_w),&
K_y&=\sum_{w\ne1^L}(A_w+C_w+P_w)+T,\\
Q(y)&=(\beta_1(y),\ldots,\beta_L(y);K_y).&&
\end{aligned}
\tag{200.2}
$$

非负性来自两个目录都含 $R$。对任意有符号 $q=(\beta_1,\ldots,\beta_L;K)$，令

$$
F_q(b)=\sum_{n=1}^L\beta_n(b_n-\alpha_n)-Ke,
\qquad F_y=F_{Q(y)}=y\cdot h.
\tag{200.3}
$$

定义 199.1—199.2 的完整闭域及证书记为

$$
\begin{aligned}
H=H_L=\{b:\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{n=3}^Lb_n,\quad
 b_1+\sum_{n=3}^Lb_n-(L+1)e\le1\},\\
\sigma_H(q)&=\max_{b\in H}F_q(b),\qquad
P_H=\{q:\sigma_H(q)\le0\},\\
D_C(t)&=\{Q(V):V\ge0,\ \Delta_C(V)\le t\}\quad(t\ge0),\\
E_N&=\{q:\exists V\ge0\ \exists\theta\in[0,1],\
\Delta_N(V)\le1-\theta,\ \sigma_H(q-Q(V))\le\theta\}.
\end{aligned}
\tag{200.4}
$$

$D_C(t)$ 是评分的商像，不是评分集合。$V$ 必须逐行非负，而残差
$F_{Q(y)-Q(V)}$ 允许全部符号；$\theta=1$ 时仍允许非零的 $\Delta_N(V)=0$ 评分。
以下使用定理 198.5 的完整顶点表示

$$
\begin{aligned}
H&=\operatorname{conv}\{o,p,u_k,v_k:3\le k\le L\},\\
o&=(0,\ldots,0;0),\qquad p=(1,0,\ldots,0;0),\\
u_k&=(\underbrace{c_k,\ldots,c_k}_{k},0,\ldots,0;0),
       \qquad c_k=\frac1{k-1},\\
v_k&=(\underbrace{1,\ldots,1}_{k},
       \underbrace{e_k,\ldots,e_k}_{L-k};e_k),
       \qquad e_k=\frac{k-2}{k+1}.
\end{aligned}
\tag{200.5}
$$

具体地，对任意有符号 $q$，记 $B=\beta_1+\beta_2$、$S_k=\sum_{n=1}^k\beta_n$、
$\kappa=K-S_L$，则其支持是全部下列值的最大值：

$$
F_q(o)=-B,\quad F_q(p)=-\beta_2,\quad
F_q(u_k)=\frac{S_k}{k-1}-B,\quad
F_q(v_k)=\frac{3S_k-(k-2)\kappa}{k+1}-B.
\tag{200.6}
$$

这里不删去 $o,p$ 或任何一个 $u_k,v_k$，也不对带符号商加非负条件。

**定义 200.2（较早零守卫及代表相关的冲突量）。** 写 $x_w=A_w+P_w$。
对 $3\le j\le L$、$1\le i<j$ 定义

$$
\begin{aligned}
\kappa_j(i;y)&=\sum_{\substack{w\ne1^L:\ n(w)<j,\ w_j=0,\ w_i=1}}x_w,\\
c_j(y)&=\min_{1\le i<j}\kappa_j(i;y),\\
\Gamma_k(y)&=\frac1{k-1}\sum_{j=3}^kc_j(y),\qquad
\Gamma(y)=\max_{3\le k\le L}\Gamma_k(y).
\end{aligned}
\tag{200.7}
$$

这些是有限非负和与达到的有限最小值。每个 $j$ 选一个最小化地址 $i_j<j$，
选择只依赖固定的整个评分，在任何来源回答之前完成。令

$$
J_{i,j}=(i,j;0,j,0),\qquad
U_k=\frac1{k-1}\left(R+\sum_{j=3}^kJ_{i_j,j}\right).
\tag{200.8}
$$

$J_{i,j}$ 先查询 $i$，零时输出 $0$；正时查询 $j$，在零时输出 $j$，否则输出 $0$。
它属于定义 190.2 的 $S_O$，从而属于完整 $\mathcal D_O$。
$U_k$ 是 $k-1$ 个完整停止表的等权概率混合；这些表不连续执行。
$\Gamma$ 依赖评分代表 $y$，不定义为仅依赖 $Q(y)$ 的函数。
这里的最小化只比较所显示的各 $j$ 独立选守卫的混合族，不是完整 $O$ 类的最优性断言。

**引理 200.3（全部字上的概率与精确加权缺陷）。** 对任意所选守卫、任意
$3\le k\le L$ 和首零 $n=n(w)\le k$ 的字，令

$$
m_k(w)=\#\{j:3\le j\le k,\ n<j,\ w_{i_j}=1,\ w_j=0\}.
$$

则 $U_k(w)$ 的全部非零概率为

$$
\begin{aligned}
U_k(w)(n)&=c_k,\\
U_k(w)(j)&=c_k\mathbf1_{\{w_{i_j}=1,\ w_j=0\}}
       &&(3\le j\le k,\ j>n),\\
U_k(w)(0)&=1-c_k(1+m_k(w)),\\
U_k(w)(\{0,n\})&=1-c_km_k(w),
\end{aligned}
\tag{200.9}
$$

其余正标签的质量为零。对首零 $n>k$ 的每个字以及 $1^L$，$U_k(w)=\delta_0$。
因此，使用最小化守卫时，联合事件向量满足精确恒等式

$$
y\cdot\bigl(d(u_k)-z_{U_k}\bigr)
 =c_k\sum_{\substack{w\ne1^L:\ n(w)\le k}}x_wm_k(w)
 =\frac1{k-1}\sum_{j=3}^k\kappa_j(i_j;y)
 =\Gamma_k(y).
\tag{200.10}
$$

**证明。** 当 $n=1,2$ 时，恰由 $R$ 输出正确标签 $n$；当 $3\le n\le k$ 时，
$R$ 输出 $0$，且 $i_n<n$ 保证 $J_{i_n,n}$ 先收到一再收到零，恰输出 $n$。
所有 $j<n$ 的守卫表都收到两个正回答并输出 $0$。每个 $j>n$ 的守卫表恰在
$w_{i_j}=1,w_j=0$ 时输出错误标签 $j$，其余情形输出 $0$。于是正确标签由一个表
贡献，错误正标签由所计的 $m_k(w)$ 个表各贡献一次；表数为 $k-1$，故得到
(200.9)，所有概率非负且总和为一。若 $n>k$ 或 $w=1^L$，所有被查询位都为正，
每个表都输出 $0$。这覆盖任意多个后继零，并未把同一首零类缩为单一字。

在 $u_k$，当 $n\le k$ 时，基、正确、pair 三行的需求为 $1-c_k,c_k,1$。
由 (200.9)，需求减事件概率依次为

$$
c_km_k(w),\qquad0,\qquad c_km_k(w).
\tag{200.11}
$$

当 $n>k$ 时三行需求为 $1,0,1$，全正字的需求为 $1$，都恰好达到。
故正确行和正字行虽有任意 $C_w,T$，在该缺陷恒等式中贡献零；基与 pair 权重
则以 $x_w$ 相加。交换有限求和得 (200.10)。对非最小化守卫，同一公式的倒数
第二项仍成立。各 $j$ 的选择独立，任何选择都逐项不小于 $c_j(y)$，而同时取
最小化地址便同时最小化每个 $k$ 的加权缺陷及它们的最大值。该结论仅属于
(200.8) 的混合族。$\square$

$U_k$ 是供支持计算使用、带有上述公式所列缺陷的归一合法 $O$ 概率见证；
它不是一个零帽可行实现者。即使 $\Gamma(y)=0$，也只保证被该评分计权的总缺陷
为零，不能删除零权重行上的缺陷或宣称 $z_{U_k}\ge d(u_k)$。

**定理 200.4（完整目录的加权守卫界）。** 对每个 $L\ge3$ 和全部非负评分
$y=((A_w,C_w,P_w),T)$，令 $\delta=\Delta_O(y)$。则

$$
\sigma_H(Q(y))\le\delta+\Gamma(y).
\tag{200.12}
$$

不要求饱和评分、共同马尔可夫表示或任何分量预算；$B_O$ 始终取完整目录的支持。

**证明。** $z_{U_k}$ 是完整 $O$ 表事件向量的概率混合，所以
$y\cdot z_{U_k}\le B_O(y)$。结合 (200.10)，

$$
F_y(u_k)=y\cdot(d(u_k)-z_{U_k})+y\cdot z_{U_k}-y\cdot\mathbf r
       \le\Gamma_k(y)+\delta.
\tag{200.13}
$$

其余顶点可用既有合法概率核控制。$o$ 由空日程立即输出 $0$ 恰好实现；$p$ 由
查询地址 $1$、零时输出 $1$、正时输出 $0$ 恰好实现。故 $F_y(o),F_y(p)\le\delta$。
对 $v_k$，用[定理 87.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#87-unit-leading-plateaus-and-unbounded-address-to-count-ratios)的子集核 $P_{k,2}$：
在有序标签集 $\{1,\ldots,k,\infty\}$ 中均匀选三个标签，查询前两个最小数值标签，
遇零时输出该数值标签，否则耗尽后输出第三标签；$\infty$ 解释为 $0$，从不查询。
这是一族完整的递增停止表，其全行计算也用于
[定理 168.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#168-closed-auxiliary-boundaries-and-the-original-positive-domain)。

记 $s_k=3/(k+1)=1-e_k$。若 $n\le k$，恰在所选三元子集包含 $n$ 时输出 $n$，
概率为 $s_k$，不依赖其后的零模式。因此正确行达到需求 $1-e_k$，pair 概率至少
$s_k$，基概率至少零，满足其可能为负的需求 $-e_k$。若 $n>k$，所有所选数值位
均为正，输出 $0$ 的概率为 $s_k$，输出 $n$ 的概率为零；此时需求分别为

$$
1-2e_k,\qquad0,\qquad1-e_k,
\tag{200.14}
$$

故基行有余量 $e_k$，正确与 pair 行恰好达到。全正字的基需求是 $1-e_k$，
同样恰好达到，不能将其与 (200.14) 的基需求混同。由 $y\ge0$ 可得
$y\cdot d(v_k)\le y\cdot z_{P_{k,2}}\le B_O(y)$，于是 $F_y(v_k)\le\delta$。
最后 $F_y$ 关于 $b$ 仿射，(200.5) 的全部顶点已受控，取最大值得 (200.12)。
这只使用合法核给完整支持作下界，不把支持换成受限目录的值。$\square$

**定理 200.5（零冲突的精确支持判据）。** 对每个 $3\le j\le L$，令

$$
W_j(y)=\{w:n(w)<j,\ w_j=0,\ A_w+P_w>0\},\qquad
Z_{<j}(w)=\{i<j:w_i=0\}.
$$

空族的交集约定为 $\{1,\ldots,j-1\}$。则

$$
\Gamma(y)=0
\quad\Longleftrightarrow\quad
\bigcap_{w\in W_j(y)}Z_{<j}(w)\ne\varnothing
\quad\text{对每个 }3\le j\le L.
\tag{200.15}
$$

**证明。** 因为 $\kappa_j(i;y)$ 是非负有限和，它为零恰好表示每个
$w\in W_j(y)$ 都有 $w_i=0$。所以 $c_j(y)=0$ 等价于该交集非空。
所有 $c_j\ge0$ 且 $\Gamma_L$ 包含每个 $c_j$，故 $\Gamma=0$ 等价于所有
$c_j=0$，得到 (200.15)。$\square$

例如，若全部正基权重和 pair 权重只支持于一个首零类 $\Omega_n$，则每个非空
$W_j$ 有 $j>n$，可取共同守卫 $i_j=n$。若这些权重支持的每个字的零位置构成一个
连续区间，则每个 $W_j$ 中的字在 $j-1$ 处均为零，可取 $i_j=j-1$。
更一般地，不同 $j$ 可有不同的共同较早零地址。这些情形均允许全部正确权重
$C_w$ 和 $T$ 任意，并保留所有未计权行。定理 198.1 的饱和操作保持
$A_w+P_w$ 及全部表奖励与锚不变，因而保持 $\kappa_j,c_j,\Gamma,\delta$；
本判据本身无需先作饱和。

**推论 200.6（实际的零评分证书切片）。** 有如下完整商像的包含：

$$
\{Q(y):y\ge0,\ \Delta_O(y)+\Gamma(y)\le1\}\subseteq E_N.
\tag{200.16}
$$

其明确证书为 $V=0$、$\theta=\Delta_O(y)+\Gamma(y)$。特别地，

$$
\{Q(y):y\ge0,\ \Delta_O(y)=0,\ \Gamma(y)=0\}
 \subseteq P_H\subseteq D_N(0)+P_H.
\tag{200.17}
$$

若 $\Gamma(y)=0$ 且 $\Delta_O(y)\le1$，可取 $V=0$、$\theta=\Delta_O(y)$。

**证明。** $\delta,\Gamma\ge0$，故 (200.16) 的假设给 $0\le\theta\le1$。
$V=0$ 满足 $V\ge0$、$\Delta_N(V)=0\le1-\theta$，而定理 200.4 给

$$
F_{Q(y)-Q(V)}(b)=F_y(b)\le\theta\qquad(b\in H).
$$

这正是定义 199.2 的完整证书。若 $\delta=\Gamma=0$，则 $Q(y)\in P_H$；
又 $Q(0)\in D_N(0)$，故得到 (200.17)。所有选择都达到，论证包含零权重和
$\theta=0,1$ 的闭端点。这里给出的 $V=0$ 只是一类证书，未缩减 $E_N$：在
$\theta=1$，完整定义依然允许所有非零零成本 $N$ 评分。$\square$

**命题 200.7（真正失败必须具有的守卫冲突）。** 以下均使用完整目录评分。

1. 若 $y\ge0$、$\Delta_O(y)=0$ 且 $Q(y)\notin D_N(0)+P_H$，则存在
   $3\le j\le L$ 使 $c_j(y)>0$。
2. 若 $y\ge0$、$\delta=\Delta_O(y)\le1$ 且 $Q(y)\notin E_N$，则对定理
   199.3 给出的任意 $b\in H$、完整 $N$ 配置 $\lambda\ge0$ 和质量
   $M=\sum_D\lambda_D\ge1$，其中 $G_N\lambda\ge h(b)$、$F_y(b)>M$，有
   $$
   \Gamma(y)>M-\delta\ge1-\delta.
   \tag{200.18}
   $$
3. 在[定义 165.1 与定理 165.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#165-a-unique-radial-direction-away-from-the-first-two-prefix)的闭域
   $Q_L$ 内，设 $x=(1-t)\alpha+tb$，$b\in H$、$0<t\le1$，且某非负评分的
   完整停止支持间隔 $g_{\rm sep}=y\cdot d(x)-B_O(y)>0$。则
   $$
   g_{\rm sep}=tF_y(b)-\delta
      \le t\Gamma(y)-(1-t)\delta,\qquad
   \Gamma(y)\ge\frac{g_{\rm sep}+(1-t)\delta}{t}>0.
   \tag{200.19}
   $$

**证明。** 第一项是 (200.17) 的逆否命题。第二项将
$M<F_y(b)\le\delta+\Gamma(y)$ 移项即可；所用 $b,\lambda,M$ 的存在性来自
定理 199.3，不在此假定存在一个实际失败评分。第三项由
$d(x)-\mathbf r=t(d(b)-\mathbf r)$ 和定理 200.4 直接得到 (200.19)。
该计算只对所显示的 $Q_L$ 径向表示使用，$t=0$ 不作除法。

上述每一种失败都强制 $\Gamma(y)>0$，从而某个 $c_j(y)>0$。这等价于：对每个
候选较早地址 $i<j$，都有一个字 $w\in W_j(y)$ 在 $i$ 处回答一。这样的正基或
pair 支持必涉及至少两个不同首零类，否则该单一首零位置本身就是共同守卫，与
$c_j>0$ 矛盾。这是必要条件，不是分离的充分条件。$\square$

将第三项解释为原始有限帽分离时，还必须有完整 $N$ 概率可行见证，并使用既有
[定理 167.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#167-exact-radial-intervals-and-the-missing-budget-exchange)的径向概率区间、
[定理 168.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#168-closed-auxiliary-boundaries-and-the-original-positive-domain)的残差范围与正闭帽运输，以及定理 110.2 的原始类保持运输。
辅助方向的支持间隔本身不提供这样的原始实现；命题 199.7 则给出完整证书失败时
取得有限概率见证的既有条件结论。

**例 200.8（既有非零零成本评分的锐性与边界）。** 取定理 198.7 的评分：在
$010,100$ 上各置单位 pair 权重，在 $110$ 上置单位正确权重，在 $111$ 上置
$T=1$；当 $L>3$ 时所有显示字追加 $1^{L-3}$，其余行权重为零。其已有完整支持为

$$
B_N(y)=B_O(y)=y\cdot\mathbf r=3,\qquad
Q(y)=(0,0,1,0,\ldots,0;4).
$$

于是 $\delta=\Delta_N(y)=0$，$Q(y)\in D_N(0)$。在本节的守卫量中，

$$
\kappa_3(1;y)=\kappa_3(2;y)=1,\qquad c_j(y)=0\ (j>3),\qquad
\Gamma(y)=\frac12.
$$

又 $F_y(u_3)=1/2$，结合 (200.12) 得
$\sigma_H(Q(y))=\delta+\Gamma(y)=1/2$，所以守卫界在这个既有评分上达到等号。
然而可直接取 $V=y,\theta=0$：$\Delta_N(V)=0$ 且残差恒零。因此正 $\Gamma$
并不推出证书失败，也不推出任何原始帽分离。这个例子的目录支持和非零零成本商
归属定理 198.7；这里仅计算其守卫量以说明 (200.12) 的锐性。该辅助点 $u_3$
没有有限 $N$ 锥配置：否则 $G_N\lambda\ge h(u_3)$、$\lambda\ge0$ 会给出
$1/2=F_y(u_3)\le y\cdot G_N\lambda\le0$，矛盾。它不被用作原始零帽目标。

**命题 200.9（共同种子实现与实际尾部范围）。** 以上守卫核可在原始来源上用一个
与来源无关的 $U\in[0,1)$ 实现，且零建议、硬两实际请求及实际有限交接均保持。
把 $[0,1)$ 分成 $k-1$ 个等长区间，预先选定 $R$ 或某个 $J_{i_j,j}$，只执行
该表，输出标签 $r$ 时交接原标记 $\theta_r$。选择、全部终端标签及守卫地址在
回答前已定；同一个 $U$ 对全部实际来源使用。每条分支递增且在首个查询零或耗尽
时停止，至多两次实际请求，在每个来源和种子上有限交接。子集核也用同一个
区间种子选择其整个三元子集，无需额外随机源。完成整个预选日程而忽略首次零之后
的回答，给出相同种子的 $N$ 实现，忽略的实际请求仍计数；这是命题 90.2 的方向。

对每个实际首零 $n(x)>k$，守卫核输出 $\theta_0$，故对选定标记目标的 TV 误差
恰为 $a_{n(x)}$。一般有限标记混合在实际活跃长度 $L$ 之后仍使用定理 110.2 的
精确尾式

$$
\operatorname{TV}\left(\sum_{r=0}^Lp_{1^L}(r)\delta_{\theta_r},
                \lambda_x^a\right)
       =\max\{1-p_{1^L}(0),a_{n(x)}\}\qquad(n(x)>L).
\tag{200.20}
$$

原始活跃长度由 $a_i>\varepsilon$ 定义，故全部实际尾部 $a_n\le\varepsilon$
仍严格正且趋零；等号 $a_n=\varepsilon$ 保留。全正有限字只用于这些实际尾源的
计算，不添加无限全正源。需要径向解释时，复用
[定理 170.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#170-every-original-tail-under-the-same-radial-law-identity)对整个实际序列的同一缩放及律恒等式。
原始竞争者的任意地址与全载体输出仍由定理 110.2 覆盖，不由守卫核的有限地址
范围限制。这里实现的是用于支持计算的特定合法核及其所列误差，不是把任意
$N$ 律转换为 $O$ 律，也不把 (200.10) 的辅助零帽缺陷当作原始可行性。

**200.10（剩余的联合补偿义务与来源边界）。** 对 $\delta=\Gamma=0$ 的评分，(200.17)
确实给出有序零预算包含；对 $\delta+\Gamma\le1$ 的评分，(200.16) 确实给出完整
$E_N$ 证书。但对一般评分，仍须解决

$$
D_O(0)\subseteq D_N(0)+P_H,\qquad D_O(1)\subseteq E_N.
\tag{200.21}
$$

前一包含尚需吸收有 $c_j>0$ 的守卫冲突；后一包含还须处理 $\delta+\Gamma>1$
的评分，并在同一个预算内寻找非负 $N$ 评分 $V$ 与 $\theta\in[0,1]$，同时满足

$$
\Delta_N(V)\le1-\theta,\qquad
F_{Q(y)-Q(V)}(b)\le\theta\quad\text{对全部 }b\in H.
\tag{200.22}
$$

具体缺口是把不相容的较早零守卫要求重组为 $V$ 的补偿，同时控制包括全部 $v_k$
在内的残差顶点和 $\Delta_N(V)$ 的共同预算。逐字另选守卫不再是同一预选规则；
分别计量冲突分量不能从混合评分的共同支持最大值推出各分量预算。即使零预算
冲突全能吸收，正预算部分的联合控制仍需证明。由推论 199.4、定义 199.9 和
定理 110.2，这一未决部分仍对应每个原始正单调趋零序列及每个正闭帽的
$\mathcal F_N\ne\varnothing\Rightarrow\mathcal F_N\cap\mathscr C_L\ne\varnothing$；
本节没有证明该普遍比较，没有给出原始分离者，也没有改变其完成条件。

定理 198.5 的带符号凸包、定理 199.3 的替代、定理 199.5 的零成本有序闭包、
定义 190.2 的停止
见证、定理 87.1 的子集核和定理 110.2、167.2、168.1、170.1 的运输各按原范围复用。
本节的结果是 (200.10) 的加权守卫缺陷、(200.12) 的全评分界、(200.15) 的支持
交集判据及其证书切片和失败必要条件。成熟的随机查询混合与标量非负文字式框架
见 Jędrzej Kaniewski、Troy Lee、Ronald de Wolf，
[*Query complexity in expectation*, arXiv:1411.7280v1, Definition 8、Theorem 9](https://arxiv.org/abs/1411.7280v1)。
该文的标量期望框架不供应这里的归一概率向量核或原始停止获取比较；本节的
联合行缺陷由显式完整表混合计算。有限多面体支持与分离背景见 Volker Kaibel，
[*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorems 1、7、8、10](https://arxiv.org/abs/1001.2161v1)，
其在完整证书替代中的具体应用归属定理 199.3。本节只给普通数学定义、证明和范围，
不作文献优先权或内核验证声明。

## 追加锚（本行以下为增补区）

## 201. 共享终端的加权割覆盖补偿与单一完整预算

本节沿用定义 199.1—199.2、200.1 的完整事件评分与证书域。对 pair 权重仅在前两
首零类、正确权重任意的评分，定理 201.3 以有限层集的共享终端构造保持商与锚，
并给出完整 $N$ 支持的精确超额。它在一个总预算中吸收一类具有真实守卫冲突的评分。
原始来源和获取资源按定义 110.1、获取资源定义 90.1 保留；201.8 明列其适用范围。

**定义 201.1（早期 pair 评分族与有限层集容量）。** 固定 $L\ge3$，令
$\Omega=\{0,1\}^L\setminus\{1^L\}$，$n(w)=\min\{i:w_i=0\}$，
$\Omega_j=\{w:n(w)=j\}$。完整标签集为 $\{0,\ldots,L\}$。每个 $w\in\Omega_j$
保留三个独立事件 $\{0\},\{j\},\{0,j\}$，其非负评分分别为 $A_w,C_w,P_w$；
全正字的基事件评分为 $T\ge0$。在 $b=(b_1,\ldots,b_L;e)$ 上，需求依次为

$$
1-b_j-e,\qquad b_j-e,\qquad1-e,\qquad
 d(b)_{1^L}=1-e.
\tag{201.1}
$$

全部 Boolean 字、多零字、可能为负的单点需求及独立 pair TV 行均保留。
评分为零不删除原行。完整 $N$ 目录包含空表、单询表和所有 $i<j$ 的四胞
$00,01,10,11$ 表；完整 $O$ 目录的双询胞为 $0,10,11$。每胞可选任意标签，
包括未查询标签和较早标签。记

$$
\begin{aligned}
R&=(1,2;1,2,0),&\alpha&=(1,1,0,\ldots,0;0),&
\mathbf r&=z_R=d(\alpha),\\
h(b)&=d(b)-\mathbf r,&G_C&=(z_D-\mathbf r)_{D\in\mathcal D_C},&
B_C(y)&=\max_{D\in\mathcal D_C}y\cdot z_D,\\
\Delta_C(y)&=B_C(y)-y\cdot\mathbf r,&
\rho_C(b)&=\min\{\textstyle\sum_D\lambda_D:\lambda\ge0,\ G_C\lambda\ge h(b)\},
&&C\in\{N,O\}.
\end{aligned}
\tag{201.2}
$$

不可行时 $\rho_C=\infty$；有限最小值的达到沿用定义 166.1、定理 166.2。
$R$ 的标签按停止胞排列，在 $N$ 中其前两胞都输出 $1$。对有符号 $q=(\beta_1,\ldots,\beta_L;K)$，商及其仿射读数为

$$
\begin{aligned}
\beta_j(y)&=\sum_{w\in\Omega_j}(C_w-A_w),&
K_y&=\sum_{w\in\Omega}(A_w+C_w+P_w)+T,\\
Q(y)&=(\beta_1,\ldots,\beta_L;K_y),&
F_q(b)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad F_y=F_{Q(y)}=y\cdot h.
\end{aligned}
\tag{201.3}
$$

本节的评分族要求

$$
A_w=0,\qquad \operatorname{supp}P\subseteq\Omega_1\cup\Omega_2,
\qquad C_w\ge0\ (w\in\Omega),\quad T=t\ge0.
\tag{201.4}
$$

置

$$
\begin{aligned}
\gamma_j&=\sum_{w\in\Omega_j}C_w,& E&=\gamma_1+\gamma_2,&
G&=\sum_{j=3}^L\gamma_j,\\
\mu&=\max_{3\le j\le L}\gamma_j,& S&=\sum_wP_w,&B&=S+t,
\qquad\delta=\Delta_O(y).
\end{aligned}
\tag{201.5}
$$

这里 $B$ 是可重分配的评分总量，不是 $B_C$。令 $m=L-2$，定义常数

$$
c_1=2,\qquad c_2=3,\qquad
c_k=4-\frac{2}{\lceil k/2\rceil}\quad(k\ge3).
\tag{201.6}
$$

这些 $c_k$ 专指割覆盖系数，不是定义 200.2 的守卫成本 $c_j(y)$。
若 $\mu>0$，取不同的正权重值
$0=t_0<t_1<\cdots<t_r=\mu$，并令

$$
J_\ell=\{j\in\{3,\ldots,L\}:\gamma_j\ge t_\ell\},\qquad
 d_\ell=t_\ell-t_{\ell-1},\qquad
\Lambda(\gamma)=\sum_{\ell=1}^r d_\ell c_{|J_\ell|}.
\tag{201.7}
$$

于是 $\gamma_j=\sum_\ell d_\ell\mathbf1_{j\in J_\ell}$。
若 $\mu=0$，层集和为空且 $\Lambda=0$。等价地，把晚期权重按数值排序为
$g_1\ge\cdots\ge g_m\ge g_{m+1}=0$，则

$$
\Lambda(\gamma)=\sum_{k=1}^m c_k(g_k-g_{k+1})
 =\int_0^\mu c_{|J_s|}\,ds,\qquad J_s=\{j\ge3:\gamma_j\ge s\}.
\tag{201.8}
$$

积分仅是有限阶梯和的记号，排序不重标原地址。以下所有评分、子集测度与割权重均不
归一为概率核，不是来源分布，也不构成执行中的额外随机性。

证书使用原闭域

$$
\begin{aligned}
H=H_L=\{b:\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\}.
\end{aligned}
$$

沿用 $P_H=\{q:F_q\le0\text{ 在 }H\text{ 上}\}$、
$D_C(v)=\{Q(V):V\ge0,\Delta_C(V)\le v\}$（$v\ge0$）、
$H_N=\{b\in H:\rho_N(b)<\infty\}$，以及

$$
E_N=\{q:\exists V\ge0,\ \exists\theta\in[0,1],\quad
\Delta_N(V)\le1-\theta,\quad
\sup_{b\in H}F_{q-Q(V)}(b)\le\theta\}.
\tag{201.9}
$$

评分 $V$ 非负，商残差允许带符号。定理 198.5 的全部顶点仍参与残差检验，尤其
$u_k=((k-1)^{-1},\ldots,(k-1)^{-1},0,\ldots,0;0)$ 的前 $k$ 项非零。
这些零帽顶点属于辅助几何。

**引理 201.2（非负子集块与全部矩端点）。** 对任意非空
$J\subseteq\{3,\ldots,L\}$，置 $z=\max J$、$I=J\setminus\{z\}$、
$h=|I|$、$k=|J|=h+1$。在 $I$ 的子集上定义有限非负测度 $\nu_J$：

$$
\nu_J(Z)=
\begin{cases}
2\mathbf1_{Z=\varnothing},&h=0,\\
2\mathbf1_{Z=I}+\mathbf1_{Z=\varnothing},&h=1,\\
\displaystyle\frac{2h}{q\binom hq}\mathbf1_{|Z|=q},
   &h=2q-1\ge3,\\
\displaystyle\frac{2}{\binom{2q}q}\mathbf1_{|Z|=q}
 +\frac{2q}{(q+1)\binom{2q}{q+1}}\mathbf1_{|Z|=q+1},
   &h=2q\ge2.
\end{cases}
\tag{201.10}
$$

其总质量和全部所需一阶、定向二阶矩为

$$
\nu_J(2^I)=c_k,\qquad
\nu_J\{Z:i\in Z\}=2\quad(i\in I),\qquad
\nu_J\{Z:i\in Z,\ j\notin Z\}=1\quad(i\ne j\text{ 在 }I).
\tag{201.11}
$$

记 $w(H)$ 为零地址集合恰为 $H$、其余位全为一的字。对应评分块 $W_J$ 在
每个 $w(\{j,z\})$ 的正确行放单位质量，$j\in J$；在

$$
w(\{a,z\}\cup Z)\quad(a=1,2,\ Z\subseteq I)
$$

的 pair 行各放 $\nu_J(Z)/2$。其余行及 $T$ 为零，重合的字逐行相加。
该块在每个 $j\in J$ 的首零类有正确总量一，pair 总量为 $c_k$，且 pair 支撑
全在首零类 $1,2$。

**证明。** $h=0$ 时总质量为二，没有内部地址，两个矩断言均为空。
$h=1$ 时总质量三，唯一地址的包含质量二，二地址断言为空。
对均匀 $r$ 元子集，指定地址的包含比例为 $r/h$，指定有序地址对的
“包含第一个、排除第二个”比例为 $r(h-r)/(h(h-1))$。当 $h=2q-1\ge3$，
总质量为 $2h/q=4-2/q=c_{2q}$；对应两矩分别为

$$
\frac{2h}{q}\frac qh=2,\qquad
\frac{2h}{q}\frac{q(q-1)}{h(h-1)}=1.
$$

当 $h=2q\ge2$，两个均匀层的总质量为 $2$ 与 $2q/(q+1)$，故

$$
\begin{aligned}
\nu_J(2^I)&=2+\frac{2q}{q+1}=4-\frac2{q+1}=c_{2q+1},\\
\nu_J(i\in Z)&=2\frac q{2q}+\frac{2q}{q+1}\frac{q+1}{2q}=2,\\
\nu_J(i\in Z,j\notin Z)
 &=2\frac{q^2}{2q(2q-1)}
   +\frac{2q}{q+1}\frac{(q+1)(q-1)}{2q(2q-1)}=1.
\end{aligned}
$$

这里包括 $q=1$：第二层是整个二元集，其定向二阶矩贡献零；第一层的贡献为一。
只要 $I$ 非空就有 $c_k\ge3$。有两个不同内部地址时，(201.11) 还给出

$$
\nu_J(i,j\in Z)=1,\qquad
\nu_J(i\notin Z,j\notin Z)=c_k-3\ge0.
\tag{201.12}
$$

正确字 $w(\{j,z\})$ 的最小零恰为 $j$，包括 $j=z$ 时的单零字；这是选取
$z=\max J$ 的作用。pair 字的最小零恰为 $a$。两个 $a$ 的半质量合起来为
$c_k$，各行非负，故所有首零类总量如述。$\square$

**定理 201.3（共享终端的加权补偿与精确预算）。** 对定义 201.1 的评分 $y$，若
$B\ge\Lambda(\gamma)$，则存在明确非负评分 $V$ 满足

$$
\begin{aligned}
Q(V)&=Q(y),& V\cdot\mathbf r&=y\cdot\mathbf r=E+B,\\
V\cdot d(b)&=y\cdot d(b)\quad\text{对全部 }b,&
\Delta_N(V)&=(\mu-B+\Lambda(\gamma))_+.
\end{aligned}
\tag{201.13}
$$

具体地，保留原评分在 $\Omega_1\cup\Omega_2$ 的全部正确行，加入
$\sum_\ell d_\ell W_{J_\ell}$，并置

$$
T_V=\tau=B-\Lambda(\gamma)\ge0,
\tag{201.14}
$$

其余基行、pair 行和晚期正确行均为零，重合行相加。因此下列闭条件充分保证
$\Delta_N(V)\le\delta$：

$$
B\ge\Lambda(\gamma)+(\mu-\delta)_+.
\tag{201.15}
$$

特别地，$S\ge\Lambda(\gamma)$ 也充分。在 (201.15) 下，若 $\delta\le1$，同一个
$V$ 与 $\theta=0$ 给出 $Q(y)\in E_N$；当 $\delta=0$ 且 $B\ge\Lambda+\mu$ 时，
$Q(y)\in D_N(0)$。$y=0$ 时构造给 $V=0$；$y\ne0$ 时 $V\ne0$。

**证明。** 引理 201.2 与有限层集恒等式给出 $V$ 的晚期正确总量恰为各
$\gamma_j$，早期正确总量仍为 $E$，pair 总量为 $\Lambda$，正字权重为 $\tau$。
故所有 $\beta_j$ 保持，且

$$
K_V=E+G+\Lambda+\tau=E+G+B=K_y.
\tag{201.16}
$$

锚 $R$ 收集全部早期正确、早期 pair 与正字权重，不收集晚期正确权重，因而
两锚分数都是 $E+B$。商保持给 $V\cdot h=y\cdot h$，再加锚保持即得需求得分
保持。若 $y\ne0$，其非负总质量 $K_y>0$，由 (201.16) 得 $V\ne0$。

为估计完整目录，先从 $V$ 删去保留的早期正确行，所得核心记为 $V_{\rm core}$。
固定任意双询地址及其四个 $N$ 胞。对单块 $W_J$，每个非 $11$ 胞中，任意
输出标签的奖励都不超过该胞的 pair 总质量。下面逐一核对此断言；质量均指两类
pair 行合计，胞顺序按所列地址排列，反序时交换 $01,10$ 即可。

| 查询地址类型 | 相关 pair 胞质量 | 非 $11$ 胞中的晚期正确奖励 |
| --- | --- | --- |
| 两个内部地址 $i,j\in I$ | $00,01,10,11$ 分别为 $1,1,1,c_k-3$ | 标签 $i$ 在 $01$、标签 $j$ 在 $10$ 各得一；其余为零 |
| 内部地址 $i$ 与终端 $z$ | $00,10$ 分别为 $2,c_k-2$；其余为零 | $00$ 只有标签 $i$ 得一；$10$ 每个其他 $J$ 标签至多得一 |
| 早期地址 $a\in\{1,2\}$ 与内部地址 $i$ | $00,01,10,11$ 分别为 $1,(c_k-2)/2,1,(c_k-2)/2$ | 早期零分支无晚期正确奖励；$10$ 只有标签 $i$ 得一 |
| 早期地址 $a$ 与终端 $z$ | $00,10$ 各为 $c_k/2$；其余为零 | 仅 $10$ 有晚期正确奖励，每个标签至多一 |
| 地址 $1,2$ | $00,01,10,11$ 分别为 $0,c_k/2,c_k/2,0$ | 全部晚期正确奖励在 $11$ |

前两行使用 (201.11)—(201.12)；内部—终端行中 $c_k-2\ge1$。
早期—终端行中 $c_k/2\ge1$，也覆盖只有终端的 $h=0$ 块。
所有早期输出标签的奖励只是 pair 质量的一部分，标签 $0$ 恰得该胞全部 pair
质量，其他非 $J$ 晚期标签得零。因此表中确实比较了每个输出标签。

还须包含不在 $J$ 的晚期查询地址。这些地址在块的每个非零行上恒为一。
与内部地址配对时，唯一含零的已用胞有 pair 质量二且只有该内部正确标签可能得一；
与终端配对时，唯一含零的已用胞有 pair 质量 $c_k$，每个正确标签至多得一。
与早期地址配对时，早期零胞有 pair 质量 $c_k/2$ 而没有晚期正确奖励；
两个外部地址则全部行都在 $11$。这覆盖任意间隔、在终端之后的地址以及空的内部集。

现在固定同一查询对、同一胞及同一标签，把上述非负不等式乘 $d_\ell$ 后对全部
层相加。各层的 $z=\max J_\ell$ 可以不同：相加所固定的是实际查询对、胞和
输出标签，不要求共同的块终端。令 $P_c$ 为相加后该胞的 pair 质量，则每个
$c\ne11$ 的全标签最大值不超过 $P_c$。在 $11$，标签 $0$ 得
$P_{11}+\tau$，每个早期标签至多得 $P_{11}$，每个晚期标签的正确奖励至多为
其全局总量 $\gamma_j\le\mu$。因此在相加之后才取胞最大值，得到

$$
\begin{aligned}
\text{该双询表族的最优核心得分}
 &\le\sum_{c\ne11}P_c+\max\{P_{11}+\tau,\mu\}\\
 &=\Lambda+\tau+(\mu-P_{11}-\tau)_+\\
 &\le\Lambda+\tau+(\mu-\tau)_+.
\end{aligned}
\tag{201.17}
$$

空表和单询表的输出函数可由某个不同地址的 $N$ 双询表忽略多余回答实现，故同界
覆盖完整 $N$ 目录。这只是输出函数的表示；执行时取得而忽略的请求仍计数。
这里没有给每个层另设预算，也没有相加各层独立取得的支持最大值。

加回早期正确行，任意表至多多得 $E$。查询 $(1,2)$，在 $00,01$ 输出 $1$、
在 $10$ 输出 $2$，在 $11$ 选择 $0$ 或一个最大 $\gamma_j$ 的晚期标签，
同时取得早期全部奖励和

$$
E+\Lambda+\max\{\tau,\mu\}.
$$

这达到 (201.17) 加 $E$ 的上界。减去 $E+B=E+\Lambda+\tau$，便得
$\Delta_N(V)=(\mu-\tau)_+$，包括 $\tau=\mu$ 和 $\tau=0$。

对原 $y$，合法停止表 $(1,2;1,2,j)$ 与 $(1,2;1,2,0)$ 给出

$$
B_O(y)\ge E+S+\max\{\mu,t\},\qquad
\delta\ge(\mu-t)_+.
\tag{201.18}
$$

若 $S\ge\Lambda$，则 $\tau\ge t$，故 $\Delta_N(V)\le\delta$。
更一般地，在 $B\ge\Lambda$ 的构造域内，(201.15) 恰使显示的
$(\mu-B+\Lambda)_+$ 不超过 $\delta$；这是对该构造预算的判断，不是任意代表的
必要条件。没有除以 $\delta$，故 $\delta=0$、$B=\Lambda$ 及 (201.15) 的等号
均包括在内。$\mu=0$ 时没有块，$V$ 只保留早期正确行并取 $T_V=B$，超额恰为零。

在 (201.15) 下，若 $\delta\le1$，残差为零且 $\Delta_N(V)\le\delta\le1$，所以
$(V,0)$ 满足 (201.9)。对任何同一个完整配置 $\lambda\ge0$、
$G_N\lambda\ge h(b)$，还有

$$
F_y(b)=V\cdot h(b)\le V\cdot G_N\lambda
 \le\Delta_N(V)\sum_D\lambda_D.
\tag{201.19}
$$

在有限 $\rho_N(b)$ 上取达到的最小配置，即有
$F_y(b)\le\rho_N(b)\le\max\{1,\rho_N(b)\}$。这与推论 199.4 的完整证书判据
相容，但没有从一个评分推出一般 $O$ 达到者。$\square$

作为容量的直接比较，(201.6) 给出 $c_k\le k+1$，且 $k\ge3$ 时严格小于；
$c_k$ 随 $k$ 非减并恒小于四。由
$\sum_{k=1}^m(k+1)(g_k-g_{k+1})=G+\mu$ 和
$\sum_{k=1}^m(g_k-g_{k+1})=\mu$，将这些逐层不等式代入 (201.8)，得到

$$
\Lambda(\gamma)\le G+\mu,\qquad
\Lambda(\gamma)\le c_m\mu,
\qquad c_m\mu<4\mu\quad\text{仅在 }\mu>0\text{ 时}.
\tag{201.20}
$$

若至少三个晚期权重为正，则第三大权重以下的正长度层满足 $|J_s|\ge3$，所以
$\Lambda<G+\mu$。$\mu=0$ 时两边全为零。因而 $S\ge G+\mu$ 只是由
$\Lambda\le G+\mu$ 推出的较强充分假设，其结论包含于 (201.15) 的充分范围。等权的 $k$ 个晚期
标签各重 $\lambda>0$ 时，$\Lambda=c_k\lambda$，系数依次为
$2,3,3,3,10/3,10/3,\ldots$。

**推论 201.4（饱和基行扩张，保留同一预算）。** 设一般非负评分满足

$$
A_w\le C_w\quad(w\in\Omega),\qquad
\operatorname{supp}(A+P)\subseteq\Omega_1\cup\Omega_2.
\tag{201.21}
$$

按定理 198.1 先作饱和

$$
y'=(A'=0,\ C'=C-A,\ P'=P+A,\ T'=T).
$$

令 $a_* =\sum_wA_w$，并严格以饱和后的权重定义

$$
\begin{aligned}
S'&=S+a_*,&\gamma'_j&=\sum_{w\in\Omega_j}(C_w-A_w),&
E'&=\gamma'_1+\gamma'_2,\\
G'&=\sum_{j=3}^L\gamma'_j,&\mu'&=\max_{j\ge3}\gamma'_j,&
B'&=S'+T,\qquad\Lambda'=\Lambda(\gamma').
\end{aligned}
\tag{201.22}
$$

若 $\delta=\Delta_O(y)\le1$ 且
$B'\ge\Lambda'+(\mu'-\delta)_+$，则定理 201.3 对 $y'$ 给出的同一 $V$ 满足

$$
\Delta_N(V)\le\delta\le1,\qquad
F_{Q(y)-Q(V)}(b)=-ea_*\le0\quad(b\in H).
\tag{201.23}
$$

故 $(V,0)$ 仍为 $Q(y)$ 的完整证书；更一般地，在不要求 $\delta\le1$ 时，
相同阈值给出 $Q(y)\in D_N(\delta)+P_H$。零预算时取
$B'\ge\Lambda'+\mu'$ 即可。

**证明。** 定理 198.1 保持逐字逐标签奖励、锚和两个支持，故
$\Delta_O(y')=\delta$，且 $F_{y'}=F_y+ea_*$。
假设 (201.21) 使 $C'\ge0$ 且 $P'$ 仍仅在早期类。定理 201.3 保持
$Q(V)=Q(y')$ 与锚 $E'+B'$，因此残差恰为 (201.23)。特别地
$K_{y'}=K_y-a_*$，构造中的早期正确量、pair 总量和余量须使用饱和后的值。
由于晚期 $A$ 在 (201.21) 下为零，晚期 $\gamma'_j=\gamma_j$；早期正确量和
可用 pair 总量仍须按 (201.22) 改写。整个证明只使用原预算一，没有为基行或层集
增加另一份预算。$\square$

**推论 201.5（零成本评分给出的加权必要幅界）。** 任取有限晚期非负权重
$\gamma=(\gamma_3,\ldots,\gamma_L)$，按 (201.5)—(201.8) 定义 $G,\mu,\Lambda$。
若 $b$ 有完整有限 $N$ 锥配置，则

$$
\sum_{j=3}^L\gamma_j b_j
 \le\bigl(G+\Lambda(\gamma)+\mu\bigr)e.
\tag{201.24}
$$

特别地它适用于所有 $b\in H_N$。对原始任意正、非增、趋零序列，若存在原始
$N_2$ 达到者在正闭帽 $e>0$ 下具有统一误差不超过 $e$，则对任意有限
$J\subseteq\{3,4,\ldots\}$ 和非负权重 $\gamma_j$，保持这些实际标签有

$$
\sum_{j\in J}\gamma_j a_j
 \le\left(\sum_{j\in J}\gamma_j+\Lambda(\gamma)+\max_{j\in J}\gamma_j\right)e.
\tag{201.25}
$$

空支持的 $\mu,\Lambda$ 均约定为零。等权单位的 $k\ge1$ 个晚期标签给
$\sum_{j\in J}a_j\le(k+c_k+1)e$；$k=3$ 的前缀系数七已属于
[定理 137.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#137-five-necessary-bounds-without-saturation-or-active-length-assumptions)。

**证明。** 直接取引理 201.2 的加权块和，并取 $T=\mu$，不放早期正确行。
记此评分为 $W_\gamma$。定理 201.3 的同一胞计算给出

$$
\Delta_N(W_\gamma)=0,\qquad
W_\gamma\cdot\mathbf r=\Lambda+\mu,\qquad
K_{W_\gamma}=G+\Lambda+\mu,
$$

因此

$$
F_{W_\gamma}(b)=\sum_{j=3}^L\gamma_jb_j-(G+\Lambda+\mu)e\le0
$$

由任何有限配置和 (201.19) 得出。这个计算仅依赖完整行需求，不需要 $b\in H$、
饱和头部或额外单调性，故同样适用于实际有限帽剖面。

对原始 $0<e\le1$，取实际活跃长度
$L=\max(\{i:a_i>e\}\cup\{0\})$。由
[定理 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)，
原始达到者给出该长度上同一完整概率配置 $w$，满足 $Z_Nw\ge d(a,e)$。
把 $J$ 明确分为

$$
J_{\rm act}=\{j\in J:a_j>e\}=J\cap\{3,\ldots,L\},\qquad
J_{\rm inact}=J\setminus J_{\rm act}.
$$

若活跃部分非空，则 $L\ge3$，锚 $R$ 在该长度上有定义。由
$\sum_Dw_D=1$ 得 $G_Nw\ge d(a,e)-\mathbf r$。在长度 $L$ 上对其他晚期
标签取零权重，使用 $W_{\gamma^{\rm act}}$ 得

$$
\sum_{j\in J_{\rm act}}\gamma_ja_j
 \le(G_{\rm act}+\Lambda(\gamma^{\rm act})+\mu_{\rm act})e.
$$

这里没有把稀疏 $J_{\rm act}$ 压缩或重标；块终端仍为每个实际层集的最大标签。
非活跃部分，包括 $a_j=e$ 的标签，满足
$\sum_{j\in J_{\rm inact}}\gamma_ja_j\le G_{\rm inact}e$。
删除非负坐标只减小各层集基数，(201.6) 的非减性给
$\Lambda(\gamma^{\rm act})\le\Lambda(\gamma)$，且
$\mu_{\rm act}\le\mu$。两界相加即得 (201.25)。若活跃部分为空，只用后一界，
也包括 $L=0,1,2$；若 $e>1$，由 $a_j\le1<e$ 直接得结论。这些界均仅是必要条件。
$\square$

**命题 201.6（六地址的完整支持与非零代表）。** 取 $L=6$，在六个字

$$
011000,\quad010100,\quad010010,\quad
101000,\quad100100,\quad100010
$$

各放单位 pair 权重，在四个单零字 $w(\{j\})$、$j=3,4,5,6$ 各放正确权重二，
取 $T=1$，其余权重为零，记所得评分为 $y$。其参数为

$$
S=6,\quad G=8,\quad\mu=2,\quad\Lambda=6,\quad B=7,
\qquad G+\mu=10.
\tag{201.26}
$$

定理 201.3 的 $V$ 保留六条 pair 行和 $T=1$，将四个正确权重二分别放到零集
$\{3,6\},\{4,6\},\{5,6\},\{6\}$。这正是 $J=\{3,4,5,6\}$ 的块乘二：
$h=3$ 的三个二元子集各有 $\nu_J$ 质量一。两个评分均有

$$
Q=(0,0,2,2,2,2;15),\qquad y\cdot\mathbf r=V\cdot\mathbf r=7.
$$

**证明。** 对给定查询对逐胞取全部七个标签的最大值，结果为：

| 查询对 | $y$ 的完整 $O$ 表支持 | $y$ 的完整 $N$ 表支持 | $V$ 的完整 $N$ 表支持 |
| --- | --- | --- | --- |
| $12$ | $8$ | $8$ | $8$ |
| $13,14,15,23,24,25$ | $7$ | $7$ | $7$ |
| $16,26$ | $8$ | $8$ | $7$ |
| $34,35,45$ | $8$ | $8$ | $8$ |
| $36,46,56$ | $8$ | $10$ | $7$ |

这些值直接由定义 164.3 的胞公式给出。例如查询 $36$ 时，$y$ 在四胞
$00,01,10,11$ 的 pair 质量为 $4,0,2,0$，正确标签 $3$ 在 $01$ 得二，
正确标签 $6$ 在 $10$ 得二，标签 $4,5$ 在 $11$ 各得二，正字在那里给标签零一分。
所以 $N$ 的值为 $4+2+2+2=10$，$O$ 合并首两胞后为 $4+2+2=8$。
在 $V$ 中标签 $3$ 移至 $00$，其他正确标签移至 $10$，故值为 $4+0+2+1=7$。
内部地址 $3,4,5$ 的置换以及早期地址 $1,2$ 的交换保留表中各类，其余类型可由
同一逐标签公式计算。

常数表的最大值两者都是七，单询表的最大值对 $y$ 为八、对 $V$ 为七。因此

$$
B_O(y)=8,\quad B_N(y)=10,\quad B_N(V)=8,
\qquad\Delta_O(y)=1,\quad\Delta_N(y)=3,\quad\Delta_N(V)=1.
\tag{201.27}
$$

这在 $S=\Lambda<G+\mu$ 上给出预算一的 $(V,0)$ 证书。辅助点 $u_6$ 满足
$F_y(u_6)=8/5$，故任何 $V=0,\theta\le1$ 的证书都失败；非零 $V$ 是这里
显示的有效代表。

另取 pair 权重均为 $1/2$、正确权重均为一，仍取 $T=1$，记为 $\widehat y$；
按同一位置移动得到 $\widehat V$。此时

$$
S=3,\quad G=4,\quad\mu=1,\quad\Lambda=3,\quad B=4,
\qquad\widehat y\cdot\mathbf r=4,
$$

且

$$
B_O(\widehat y)=B_N(\widehat V)=4,\qquad B_N(\widehat y)=5,
\qquad\Delta_O(\widehat y)=\Delta_N(\widehat V)=0.
\tag{201.28}
$$

完整 $N$ 中查询 $36$ 达到五；停止表各胞由减半后的 pair 质量与正字权重一控制，
最大值四，锚达到此值。$\widehat V\ne0$，且
$F_{\widehat V}(u_6)=4/5>0$。因此 $\rho_N(u_6)=\infty$：否则零超额评分
与有限配置的 (201.19) 会给出 $4/5\le0$。$u_6$ 仅检验 $V=0$ 证书切片，
不是原始零帽模型或帽分离者。对 $L>6$，向所有显示字追加相同的 $1^{L-6}$；
新增坐标在评分支撑上恒为一，查询它们不会提高这些完整支持。
$\square$

**命题 201.7（全长度冲突评分的零成本吸收）。** 对任意 $L\ge4$、$m=L-2$ 和
$\lambda>0$，令 $y_L$ 在每个单零字 $w(\{j\})$、$3\le j\le L$ 的正确行放
$\lambda$。对 $a=1,2$，在零集 $\{a\}\cup\{k,\ldots,L\}$ 的字上放 pair 权重
$\lambda$（$k=3$）或 $\lambda/2$（$4\le k\le L$），并取 $T=\lambda$。
则

$$
\begin{aligned}
S&=(m+1)\lambda,&G&=m\lambda,&\mu&=\lambda,&B&=(m+2)\lambda,\\
\Delta_O(y_L)&=0,&\Delta_N(y_L)&=\lambda,&
\Gamma(y_L)&=\frac{\lambda m}{m+1}.
\end{aligned}
\tag{201.29}
$$

其非零商有定理 201.3 给出的明确非负代表 $V_L$，且

$$
Q(V_L)=Q(y_L),\qquad V_L\cdot\mathbf r=y_L\cdot\mathbf r=(m+2)\lambda,
\qquad\Delta_N(V_L)=0.
\tag{201.30}
$$

因而这些零预算射线可按定理 199.6 加入任何既有完整证书而不增加其预算。

**证明。** 总质量如 (201.29)。查询两个晚期地址 $3\le i<j\le L$ 时，pair
质量在 $00,01,10,11$ 依次为

$$
(i-1)\lambda,\quad0,\quad(j-i)\lambda,\quad(L-j)\lambda.
\tag{201.31}
$$

单零正确标签 $i$ 在 $01$ 得 $\lambda$，标签 $j$ 在 $10$ 得 $\lambda$，
其余正确标签在 $11$ 各得 $\lambda$；正字在 $11$ 给零标签 $\lambda$。
$O$ 首停胞把 $00,01$ 合并，零标签的 $(i-1)\lambda\ge2\lambda$ 覆盖
该胞每个正确奖励；$10$ 的 $(j-i)\lambda\ge\lambda$ 和 $11$ 的
$(L-j+1)\lambda\ge\lambda$ 也覆盖全部标签。因此该停止日程的支持为
$L\lambda=(m+2)\lambda$。$N$ 分开首两胞，额外恰得 $\lambda$，支持为
$(L+1)\lambda$。

查询早期地址 $a$ 与晚期 $j$ 时，早期零分支的 pair 总量为 $S/2$，没有晚期
正确奖励；早期一分支的零胞 pair 质量为 $(j-1)\lambda/2\ge\lambda$，正胞
的 pair 加正字质量为 $(L-j)\lambda/2+\lambda\ge\lambda$。
这些质量逐标签覆盖正确行，故 $N$ 与 $O$ 都恰得 $S+\lambda=L\lambda$。
查询 $1,2$ 也恰得 $S+\lambda$。常数输出零得 $S+\lambda$，任何常数标签均
不超过它；单询早期地址的两胞值之和为 $S/2+(S/2+\lambda)$，单询晚期 $j$
的两胞值之和为 $(j-1)\lambda+(L-j+1)\lambda$。所以完整空、单、双目录的
支持都已覆盖，得到两个超额。

按定义 200.2，$j=3$ 时选择守卫一或二的成本都是 $\lambda$。
$j\ge4$ 时，早期守卫的成本为 $(j-1)\lambda/2\ge\lambda$，晚期守卫
$3\le i<j$ 的成本为 $(j-i)\lambda$，在 $i=j-1$ 达到 $\lambda$。
因此每个 $c_j(y_L)=\lambda$，而

$$
\Gamma(y_L)=\max_{3\le k\le L}\frac{(k-2)\lambda}{k-1}
            =\frac{m\lambda}{m+1}>0.
$$

等权层只有 $J=\{3,\ldots,L\}$，所以构造明确为
$V_L=\lambda W_J$ 再加 $T_{V_L}=(m+2-c_m)\lambda$。
由 $c_m\le m+1$，有 $T_{V_L}\ge\lambda=\mu$，故定理 201.3 给
(201.30)。非零性来自正的正确总量。若 $(V_*,\theta)$ 已证实某个商 $q$，则对
$s\ge0$ 取 $V_*+sV_L$，由定理 199.6 保留
$\Delta_N\le1-\theta$ 及原残差界，仍是同一预算证书。

本族的商读数为

$$
F_{y_L}(b)=\lambda\sum_{j=3}^Lb_j-(2L-2)\lambda e,
\qquad F_{y_L}(u_L)=\frac{\lambda m}{m+1}>0.
\tag{201.32}
$$

零成本代表使任何 $b\in H_N$ 必满足
$\sum_{j=3}^Lb_j\le(2L-2)e$；它也使 $\rho_N(u_L)=\infty$，因为有限配置
会与 (201.32) 的严格正值矛盾。因此正 $\Gamma$ 和 $\Delta_N(y_L)>0$ 并未产生
完整证书失败。$L=4$ 的帽比较和相应幅界沿用
[定理 96.2、推论 96.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#96-the-analytic-hard-two-boundary-for-four-active-amplitudes)，
其范围仍由这些既有结论给定。$\square$

**201.8（原始资源、来源与未决范围）。** 原始可数带标签来源完整地取为

$$
\begin{aligned}
X&=\{(r,g):r\text{ 为素数},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
\tag{201.33}
$$

其中 $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$，$p_i$ 按递增顺序枚举素数。
静态回答、有限实际首缺以及每个有限 Boolean 字的实际来源见证均按定义 110.1
复用，包含这里用到的所有多零字。纸带仍是原不交并 Borel 载体
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$，各块为 $(0,1)$ 的副本；
原可测标记 $\theta_j=(B_1,1/(j+2))$、同一来源上运行的原消费者和非原子目标
$\mu_x$ 不变。另行选定的标记律仍为

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\longrightarrow0.
\tag{201.34}
$$

两类严格采用获取资源定义 90.1：零建议，每类只有一个与来源无关、对全部来源
共同使用的种子 $U$，实际逐源几乎处处有限交接，硬上界为两次实际请求。
重复请求和取得后忽略的请求都计数。$N_2$ 预选完整日程并取得全部回答；$O_2$
预选严格递增日程，在首次查询零或耗尽时停止。竞争者保留任意地址和原完整载体
内任意输出，误差是所有实际来源上的 TV 上确界。地址大小、深度、运行时间和
平均请求数均不替换这一实际计数。

评分 $y,V,W_\gamma$、子集测度 $\nu_J$ 及层权重 $d_\ell$ 是确定的非负对偶量。
对任意原始达到者，定理 110.2 的必要方向先给一个完整同类概率配置；上述不等式
作用于该同一个配置的全部行。若使用既有有限概率配置实现规则，则按定理 199.8
用一个 $U\in[0,1)$ 的固定区间在回答前选择整张表和全部终端标签，只执行所选表，
交付实际原标记。此为每类自己的共同种子实现；割覆盖没有再添加随机源、建议、
来源分布或来源观察，也没有把 $V$ 归一成获取规则。

任意原地址及完整纸带竞争者的闭帽必要性、同类有限表的充分性仍全部由
[定理 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)
承担。在实际活跃长度 $L=\max(\{i:a_i>e\}\cup\{0\})$，每个实际首缺 $n>L$
的精确尾误差仍为

$$
\max\{1-p_{1^L}(0),a_n\},\qquad0<a_n\le e,
\tag{201.35}
$$

包括 $a_n=e$。有限正字仅为这些实际尾源记账，不是无限全正源。
全部原始正、非增、趋零尾部均保留。需要径向解释或闭辅助边界时，只复用
[定理 165.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#165-a-unique-radial-direction-away-from-the-first-two-prefix)、
[定理 168.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#168-closed-auxiliary-boundaries-and-the-original-positive-domain)和
[定理 170.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#170-every-original-tail-under-the-same-radial-law-identity)
在原范围内的正规形、正闭帽边界与整个实际序列身份；不由评分补偿推断任意
$N$ 律到 $O$ 律的转换。定义 199.9 中的停止核条件继续由定理 109.1 与归一恒等式
(108.4) 给出。

割的分数覆盖是成熟背景，见 Robert Šámal，
[*Cubical coloring — fractional covering by cuts*, arXiv:0911.2589v1,
Lemma 2.1、Corollary 2.2](https://arxiv.org/abs/0911.2589v1)。该文对边传递图的
割覆盖量与最大割密度给出关系，并有
$x(K_{2n})=x(K_{2n-1})=2-1/n$（$n\ge2$）；这里的 $c_k=2x(K_k)$ 仅用于 $k\ge3$，
$c_1,c_2$ 是 (201.6) 的特殊值。引理 201.2 给出了所需非负子集公式和矩，
定理 201.3 则在完整事件评分内逐胞使用这些矩。
饱和归属定理 198.1，任意正确行加尾的既有迁移归属定理 198.4，带符号支持归属
定理 198.5，完整证书与零成本吸收归属定理 199.3—199.6，守卫冲突归属定义 200.2
与定理 200.4—200.5。这里不从一般分数割覆盖或评分重排取得原始获取运输。

本节的阈值是显式代表的充分条件，没有证明其最优性或对任意代表的必要性。
即使在 (201.4) 内，低总量区域

$$
B<\Lambda(\gamma)+(\mu-\delta)_+
\tag{201.36}
$$

仍未由此构造分类，特别是零预算时的 $B<\Lambda+\mu$。
未满足充分阈值不等于 $Q(y)\notin E_N$。一般完整评分仍有未决的

$$
D_O(0)\subseteq D_N(0)+P_H,\qquad D_O(1)\subseteq E_N,
\qquad\rho_O(b)\le\max\{1,\rho_N(b)\}\quad(b\in H_N).
\tag{201.37}
$$

推论 199.4、定义 199.9 和定理 110.2 所界定的原始全称义务依旧是：对每个完整
正单调趋零序列和每个正闭帽，从 $\mathcal F_N\ne\varnothing$ 得到
$\mathcal F_N\cap\mathscr C_L\ne\varnothing$，或给出完整原始 $N_2$ 达到者及
排除所有原始 $O_2$ 竞争者的统一证书。这里的必要幅界、零成本代表和完整评分
子族包含均不替代该义务，也不提供一般 $O$ 达到者。

## 追加锚（本行以下为增补区）

## 202. 混合基行评分的联合支持与单一残差预算

**定义 202.1（完整行域与混合评分族）。** 固定整数 $L\ge6$ 及实参数

$$
s>1,\qquad 0\le\eta\le1,\qquad c>2-\eta.
\tag{202.1}
$$

沿用定义 199.1—199.2、200.1 的全部 $B_L=\{0,1\}^L$ 字及
$J_L=\{0,\ldots,L\}$ 标签。对每个含零字 $w$，令
$n(w)=\min\{i:w_i=0\}$，$\Omega_j=\{w:n(w)=j\}$。
基行 $\{0\}$、正确行 $\{n(w)\}$、独立 pair 行 $\{0,n(w)\}$ 的需求依次为

$$
1-b_{n(w)}-e,\qquad b_{n(w)}-e,\qquad1-e;
$$

全正字 $1^L$ 的基行需求为 $1-e$。这 $3(2^L-1)+1$ 条行组成 $d(b)$，
包括全部多零字、可能为负的单点需求和零评分行。评分为零不删除行。

完整目录 $\mathcal D_N,\mathcal D_O$ 均保留空日程、单日程和所有
$i<j$ 的双日程，每个终端胞允许全部 $J_L$ 标签。双日程的 $N$ 胞为
$00,01,10,11$，$O$ 胞为 $0,10,11$。令

$$
\begin{aligned}
R&=(1,2;1,2,0),&\alpha&=(1,1,0,\ldots,0;0),&
\mathbf r&=z_R=d(\alpha),\\
B_C(y)&=\max_{D\in\mathcal D_C}y\cdot z_D,&
\Delta_C(y)&=B_C(y)-y\cdot\mathbf r&& (C=N,O),\\
\beta_j(y)&=\sum_{w\in\Omega_j}(C_w-A_w),&
K_y&=\sum_{w\ne1^L}(A_w+C_w+P_w)+T,&
Q(y)&=(\beta_1,\ldots,\beta_L;K_y).
\end{aligned}
\tag{202.2}
$$

$R$ 的标签按停止胞排列；在 $N$ 中，$00,01$ 都输出 $1$。
对任意有符号 $q=(\beta_1,\ldots,\beta_L;K)$，写

$$
F_q(b)=\sum_{j=1}^L\beta_j(b_j-\alpha_j)-Ke,\qquad
F_y=F_{Q(y)}.
$$

下列评分只指定非零行，其余行权重均为零：

$$
\begin{aligned}
z_1&=010\,1^{L-3},&z_2&=100\,1^{L-3},&z_3&=110\,1^{L-3},\\
w_1&=011100\,1^{L-6},&
w_2&=101101\,1^{L-6},&
w_3&=110110\,1^{L-6}.
\end{aligned}
$$

$Z$ 在 $z_1,z_2$ 的 pair 行、$z_3$ 的正确行以及 $1^L$ 的基行各放单位权重。
这正是定理 198.7 的零成本评分，不重新定义其供应结论。
$W$ 在 $w_1,w_2,w_3$ 的正确行及 $1^L$ 的基行各放单位权重。
$E$ 只在 $0^L$ 的基行放单位权重。定义

$$
Y=cZ+sW+(s+\eta)E.
\tag{202.3}
$$

特别地，$Y$ 的正字权重为 $c+s$，而 $A_{0^L}=s+\eta$、
$C_{0^L}=P_{0^L}=0$。$Z,W,E,Y$ 是事件评分，不是来源分布或表概率。

辅助闭域及带符号支持沿用

$$
\begin{aligned}
H=H_L=\{b:\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\},\\
\sigma_H(q)&=\max_{b\in H}F_q(b).
\end{aligned}
\tag{202.4}
$$

定理 198.5 供应其完整凸包顶点；在本节记为

$$
\begin{aligned}
o&=(0,\ldots,0;0),&p&=(1,0,\ldots,0;0),\\
u_k&=(\underbrace{(k-1)^{-1},\ldots,(k-1)^{-1}}_{k},
                0,\ldots,0;0),\\
v_k&=(\underbrace{1,\ldots,1}_{k},
                \underbrace{e_k,\ldots,e_k}_{L-k};e_k),
& e_k&=\frac{k-2}{k+1},\qquad 3\le k\le L.
\end{aligned}
\tag{202.5}
$$

沿用 $P_H=\{q:\sigma_H(q)\le0\}$、
$D_N(t)=\{Q(V):V\ge0,\Delta_N(V)\le t\}$ 及完整证书域

$$
E_N=\{q:\exists V\ge0,\ \exists\theta\in[0,1],\
             \Delta_N(V)\le1-\theta,\
             \sigma_H(q-Q(V))\le\theta\}.
\tag{202.6}
$$

残差允许全部符号；证书不要求 $V\le Y$。守卫量
$\kappa_j(i;y),c_j(y),\Gamma_k(y),\Gamma(y)$ 按定义 200.2 取完整评分的值。

**定理 202.2（同一混合评分的完整联合支持）。** 对定义 202.1 的全部参数，

$$
\begin{aligned}
Y\cdot\mathbf r&=3c+3s,&
Q(Y)&=(-\eta,s,c+s,0,\ldots,0;4c+5s+\eta),\\
B_O(Y)&=3c+3s+\eta,& B_N(Y)&=3c+4s+\eta,\\
\Delta_O(Y)&=\eta,&\Delta_N(Y)&=s+\eta,\\
\Gamma_k(Y)&=\frac{c}{k-1}\quad(3\le k\le L),&
\Gamma(Y)&=\frac c2.
\end{aligned}
\tag{202.7}
$$

两个支持均对全部空、单、双目录和全部输出标签取最大，不只对显示的达到表取最大。

**证明。** 锚 $R$ 命中 $Z$ 的两条 pair 行与正字行、$W$ 的两个早期正确行与
正字行，不命中 $E$。故锚分数为 $3c+3s$。各首零类的正确减基总量为
$s-(s+\eta)=-\eta,s,c+s$；总行权重为
$4c+4s+(s+\eta)$，得到商坐标。

令 $H_s=sW+(s+\eta)E$，此记号是评分，不是辅助域 $H$。
其五个有奖字及唯一有奖标签为

$$
(w_1,1),\quad(w_2,2),\quad(w_3,3),\quad(1^L,0),\quad(0^L,0),
\tag{202.8}
$$

前四项权重为 $s$，末项权重为 $s+\eta$。固定同一完整确定表 $D$。
若日程非空，$0^L$ 与 $1^L$ 总有不同转录。若一个 $N$ 表命中全部五项，
这两个字须占据两个不同的零标签胞，另三个字又各需标签 $1,2,3$ 的不同胞，
合计至少五胞；硬两 $N$ 表至多四胞。因此至少失去一项，失去的权重至少为
$s$，从而

$$
H_s\cdot z_D\le4s+\eta\qquad(D\in\mathcal D_N).
\tag{202.9}
$$

空日程输出 $0$ 时至多得 $2s+\eta$，输出任一其他标签至多得 $s$，亦满足此界。
单日程已包含在上述非空论证内。

对非空 $O$ 表，若不命中 $0^L$，至多三个终端标签只能命中 $W$ 的四个互异
有奖标签中的三个，分数至多 $3s$。若命中 $0^L$，首停胞的标签为 $0$；
该胞不能命中三个正确行，也不含 $1^L$。余下至多两胞各至多命中一个 $W$
有奖字，故

$$
H_s\cdot z_D\le(s+\eta)+2s=3s+\eta
       \qquad(D\in\mathcal D_O).
\tag{202.10}
$$

空日程仍至多得 $2s+\eta$。两种上界都逐表比较全部标签；
$4,\ldots,L$ 的标签在 (202.8) 上没有奖励，但仍为合法选择。

定理 198.7 已给 $Z\cdot z_D\le3$，对完整 $N$、$O$ 目录均成立。
对上述同一个 $D$ 加上 $cZ\cdot z_D\le3c$，得到 (202.7) 的两个支持上界。
相加的是同一表上的不等式。以下两张完整表分别同时达到这些界：

$$
D_O=(1,2;0,2,0),\qquad
D_N=(5,6;0,2,3,0).
\tag{202.11}
$$

前者标签按 $0,10,11$ 排列，后者按 $00,01,10,11$ 排列。
它们在所有正评分行上的输出为：

| 字 | 有奖事件 | $Y$ 的权重 | $D_O$ 的输出 | $D_N$ 的输出 |
| --- | --- | --- | --- | --- |
| $z_1$ | $\{0,1\}$ | $c$ | $0$ | $0$ |
| $z_2$ | $\{0,2\}$ | $c$ | $2$ | $0$ |
| $z_3$ | $\{3\}$ | $c$ | $0$ | $0$ |
| $w_1$ | $\{1\}$ | $s$ | $0$ | $0$ |
| $w_2$ | $\{2\}$ | $s$ | $2$ | $2$ |
| $w_3$ | $\{3\}$ | $s$ | $0$ | $3$ |
| $1^L$ | $\{0\}$ | $c+s$ | $0$ | $0$ |
| $0^L$ | $\{0\}$ | $s+\eta$ | $0$ | $0$ |

相应得分恰为 $3c+3s+\eta$ 与 $3c+4s+\eta$。因此这里确有同一评分上的
达到者，而不是把分别可达的分量最大值当成同时可达。

以上论证覆盖任意查询地址。特别地，$7,\ldots,L$ 在 $Z,W$ 的评分支撑上
全为一，在 $0^L$ 上却全为零，不能以这些地址在全部支撑上恒定为由删除它们。
(202.9)—(202.10) 对查询这些地址的竞争表照样成立，定理 198.7 的 $Z$ 界
本就包含其全一后缀。故任意间隔、后缀地址以及 $L=6$ 均被计入。

最后，守卫计算只使用 $x_w=A_w+P_w$。基行字 $0^L$ 在每个候选较早地址
$i$ 上都为零，故不贡献任何 $\kappa_j(i;Y)$。两个 pair 字给

$$
\kappa_3(1;Y)=\kappa_3(2;Y)=c,\qquad
c_3(Y)=c,\qquad c_j(Y)=0\quad(j>3).
\tag{202.12}
$$

后一个等式因两 pair 字在地址 $j>3$ 全为一。代入定义 200.2 即得
$\Gamma_k=c/(k-1)$ 与 $\Gamma=c/2$。$\square$

**命题 202.3（完整带符号残差、端点与零预算应用）。** 取

$$
V_-=(c-\eta)Z,\qquad V_+=(c+\eta)Z.
\tag{202.13}
$$

则 $V_-,V_+$ 都非负且非零，并有

$$
\begin{aligned}
\Delta_N(V_-)&=\Delta_N(V_+)=0,\\
\sigma_H(Q(Y)-Q(V_-))&=\eta,&
\sigma_H(Q(Y)-Q(V_+))&=0.
\end{aligned}
\tag{202.14}
$$

因此 $(V_-,\eta)$ 是定义 199.2 的同一完整预算证书，而 $(V_+,0)$ 给出
零预算应用

$$
Q(Y)\in D_N(0)+P_H\subseteq E_N.
\tag{202.15}
$$

这里复用定理 198.7 的零成本评分、定理 198.5 的支持公式及定理
199.3—199.6 的证书和有序闭包；当 $\eta>0$ 时，(202.14) 的 $\eta$
不是所需残差预算的最小值，$\eta=0$ 时两个显示预算相同。

**证明。** 由 $c>2-\eta$ 与 $0\le\eta\le1$，有 $c-\eta>0$。
定理 198.7 及支持的正齐次性给出两个零超额。令

$$
q_-=Q(Y)-Q(V_-),\qquad q_+=Q(Y)-Q(V_+).
$$

直接相减得到完整的有符号坐标

$$
\begin{aligned}
q_-&=(-\eta,s,s+\eta,0,\ldots,0;5(s+\eta)),\\
q_+&=(-\eta,s,s-\eta,0,\ldots,0;5s-3\eta).
\end{aligned}
\tag{202.16}
$$

取 $K_Y=4c+5s+\eta$。在定理 198.5 的每一个顶点上，三个读数如下，
其中每个 $k$ 均遍历 $3,\ldots,L$：

| 顶点 | $F_Y$ | $F_{q_-}$ | $F_{q_+}$ |
| --- | --- | --- | --- |
| $o$ | $\eta-s$ | $\eta-s$ | $\eta-s$ |
| $p$ | $-s$ | $-s$ | $-s$ |
| $u_k$ | $\dfrac{c+2s-\eta}{k-1}-s+\eta$ | $\eta-\dfrac{s(k-3)}{k-1}$ | $-\dfrac{(s-\eta)(k-3)}{k-1}$ |
| $v_k$ | $c+s-K_Ye_k$ | $(s+\eta)(1-5e_k)$ | $s-\eta-(5s-3\eta)e_k$ |

例如，在 $u_k$ 上三个商的前缀和分别为 $c+2s-\eta,2s,2(s-\eta)$，
而前三个商的 $\beta_1+\beta_2$ 均为 $s-\eta$，故得该行。
在 $v_k$ 上前三个幅均为一，读数分别是各自第三坐标减去其总权重乘 $e_k$。
这也包含 $k=3$、$k=L$，没有省略零帽顶点或有帽顶点。

由于 $e_k\ge1/4$，且 $K_Y>0$、$5s-3\eta>0$，三个 $v_k$ 读数均不超过
它们在 $v_3$ 的共同值

$$
-\frac{s+\eta}{4}<0.
\tag{202.17}
$$

$o,p$ 的读数也都为负。$q_-$ 的 $u_k$ 读数不超过 $\eta$，在 $u_3$
恰为 $\eta$；$q_+$ 的 $u_k$ 读数不超过零，在 $u_3$ 恰为零。
完整凸包支持公式因而给出 (202.14)。同一张表还给

$$
\sigma_H(Q(Y))=F_Y(u_3)=\frac{c+\eta}{2},
\tag{202.18}
$$

因为 $c+2s-\eta>0$，$F_Y(u_k)$ 随 $k$ 非增，其余顶点均为负。

证书 $(V_-,\eta)$ 使用一个 $\theta=\eta\in[0,1]$，且
$\Delta_N(V_-)=0\le1-\eta$；整个有符号残差的支持恰为 $\eta$。
当 $\eta=0$，两个显示代表同为 $cZ$，残差支持为零。
当 $\eta=1$，$V_-=(c-1)Z\ne0$，$\theta=1$ 的剩余预算为零，
残差支持恰为一；此端点没有把所有零成本代表缩成零评分。
$V_+=(c+1)Z$ 则仍给 $\theta=0$，残差支持为零。
这些结论没有除以 $\eta$。

另一个零预算选择是 $V_{\mathrm{wide}}=(c+s)Z$。
它仍由定理 198.7 得零超额，且对每个 $b\in H$，

$$
\begin{aligned}
F_{Q(Y)-Q(V_{\mathrm{wide}})}(b)
 &=\eta(1-b_1)-s(1-b_2)-(s+\eta)e\\
 &\le-(s-\eta)(1-b_2)-(s+\eta)e\le0.
\end{aligned}
\tag{202.19}
$$

第一步使用 $b_1\ge b_2$，第二步使用 $s>\eta$ 及 $b_2\le1,e\ge0$。
此选择与 $V_+$ 都只是既有零成本供应者的应用；不要求它们逐行不超过 $Y$，
也不从评分的缩放取得获取概率核。$\square$

**命题 202.4（固定切片的实际失败与分项预算的无界高估）。** 在 (202.1) 的
整个参数范围内，对每个 $\theta\in[0,1]$，选择 $V=0$ 或 $V=Y$ 都不能给
(202.6) 的证书，且推论 200.6 的充分切片不适用：

$$
\sigma_H(Q(Y))>1,\qquad
\Delta_N(Y)>1,\qquad
\Delta_O(Y)+\Gamma(Y)=\eta+\frac c2>1.
\tag{202.20}
$$

另一方面，固定任意 $\eta\in[0,1]$ 和 $c>2-\eta$，让 $s>1$ 无界增大，
命名基行分量的停止预算与整个评分的预算满足

$$
\begin{aligned}
\Delta_O((s+\eta)E)&=s+\eta,&
\Delta_O(Y)&=\eta,\\
\Delta_O(cZ)&=0,&\Delta_O(sW)&=0.
\end{aligned}
\tag{202.21}
$$

故这个指定分解的预算和为 $s+\eta$，比完整共同预算恰好多 $s$。
其差无界，包括整个预算为零的 $\eta=0$ 端点。

**证明。** (202.18) 及 $c>2-\eta$ 给 $(c+\eta)/2>1$，排除 $V=0$。
(202.7) 与 $s>1$ 给 $\Delta_N(Y)=s+\eta>1\ge1-\theta$，排除 $V=Y$。
同样 $c/2+\eta>1+\eta/2\ge1$，排除所显示的守卫充分切片。
这些都是指定选择或充分条件的失败，与 (202.15) 的完整证书同时成立。

$E$ 的锚分数为零，空日程恒输出 $0$ 恰得一，任何表至多得一。
故 $\Delta_O((s+\eta)E)=s+\eta$。$Z$ 的零超额归属定理 198.7；
$W$ 仅有三个单位正确类总量和单位正字权重，定理 198.4 的前三大项公式给
$B_O(W)=3=W\cdot\mathbf r$。与 (202.7) 相减即得 (202.21)。
一般的支持次可加性已用于定理 198.8，这里的定量结论是该固定代表族在完整
目录上有无界差 $s$；没有从分项预算反推整个评分的预算。

由 200.8 对同一个 $Z,u_3$ 的结论，$\rho_N(u_3)=\infty$。
故 $u_3$ 只在辅助域内排除零评分证书，不能充当原始达到者；
(202.18) 不对原始可达到集合给出任何新下界。$\square$

**定义 202.5（供应者的适用范围与原始未决命题）。** 定理 201.3 对
$A=0$、pair 支撑仅在 $\Omega_1\cup\Omega_2$ 的评分，在
$B\ge\Lambda(\gamma)$ 下给出保持商和锚的显式代表，预算控制使用 (201.15)；
推论 201.4 将之扩张到逐字 $A_w\le C_w$ 且
$\operatorname{supp}(A+P)\subseteq\Omega_1\cup\Omega_2$ 的评分，
并仍要求其所列的饱和后容量阈值。
这些结论、其阈值的充分性和定理 199.3—199.6 的证书存在性框架均按原范围复用。

本节 $Y$ 的 pair 与基支撑虽均在早期首零类，却有
$A_{0^L}=s+\eta>0=C_{0^L}$；定理 198.1 的饱和在此字移走的量为零。
因此不能把 $Y$ 直接代入上述两组假设。当 $\eta>0$ 时，其
$\beta_1=-\eta$ 也排除同商的 $A=0$ 代表，因为后者的每个 $\beta_j$
均非负；在 $\eta=0$ 不作这个排除。这些代表条件的失败不是
$Q(Y)\notin E_N$ 的结论，(202.15) 已给相反的成员结论。
此处需要另算的是 (202.7) 的原代表联合支持及 (202.21) 的定量差；
零成本代表的存在按命题 202.3 消费既有供应者。

原始问题的来源仍取定义 110.1 与 (201.33) 的完整可数集

$$
X=\{(r,g):r\text{ 为素数},\ g\in\mathbb Z,\
       \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},
\qquad N(r,g)=1+F_rg,
\qquad q_i(x)=\mathbf1_{p_i\mid N(x)}.
\tag{202.22}
$$

$F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$，$p_i$ 为递增素数序列；
回答静态，实际首缺 $n(x)=\min\{i:q_i(x)=0\}$ 有限，
每个有限 Boolean 字保留其实际来源见证。纸带是原完整不交并 Borel 载体
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$，各块为 $(0,1)$ 的副本。
原标记 $\theta_j=(B_1,1/(j+2))$、同一来源上的原消费者及非原子目标
$\mu_x$ 不变；另行选定的标记目标仍为

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                 +a_{n(x)}\delta_{\theta_{n(x)}},
\qquad1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0.
\tag{202.23}
$$

获取资源仍为定义 90.1 的零建议、来源无关的单一共同种子、逐源几乎处处有限
交接及至多两次实际请求；重复请求和取得后忽略的请求均计数。
$N_2$ 预选完整日程并取得全部回答，$O_2$ 预选严格递增日程并在首次查询零或
耗尽时停止。原始竞争者仍可使用任意地址及完整载体内任意输出；
误差仍对全部实际来源取 TV 上确界，不对来源取平均。

(202.11) 的表本身是合法的目录表；若给定目录概率混合，其共同种子实现直接
沿用定理 199.8。这里的 $Y,V_-,V_+,V_{\mathrm{wide}}$ 均为对偶评分，
其归一化不定义这样的概率混合，也不提供一般原始 $O_2$ 帽达到者。
实际帽可行性仍要求同一个概率配置同时满足全部事件行。
任意地址、完整载体的必要方向及同类有限表的充分方向均沿用定理 110.2。

对任意正闭帽 $0<\varepsilon\le1$，实际活跃长度为
$L=\max(\{i:a_i>\varepsilon\}\cup\{0\})$；原问题允许所有活跃长度，
(202.1) 的具体评分族只处理 $L\ge6$。记 $p_w$ 为有限标记核在字 $w$ 上的
输出概率向量。对每个实际首缺 $n>L$，定理 110.2、199.8 供应精确尾误差

$$
\max\{1-p_{1^L}(0),a_n\},\qquad0<a_n\le\varepsilon.
\tag{202.24}
$$

等号 $a_n=\varepsilon$ 保留，实际尾标记不并入基点，有限全正字不代表实际
无限全正源。辅助闭边界与整条正尾的径向解释仍仅按定理 168.1、170.1 使用。

定义 199.9 的原始全称命题仍为未决：对每个 (202.23) 的完整序列及每个正闭帽，
是否有

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
 \ \Longrightarrow\
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing?
\tag{202.25}
$$

其中 $\mathscr C_L=\mathscr O_L$ 的归一停止核条件由定理 109.1 及 (108.4)
供应。一般完整评分的
$D_O(0)\subseteq D_N(0)+P_H$、
$D_O(1)\subseteq E_N$ 及
$\rho_O(b)\le\max\{1,\rho_N(b)\}$（$b\in H_N$）
仍按 (199.19)—(199.20)、(201.37) 保留为未决命题。
本族的精确支持和有序零预算应用不改变这些全称量词。

## 追加锚（本行以下为增补区）
