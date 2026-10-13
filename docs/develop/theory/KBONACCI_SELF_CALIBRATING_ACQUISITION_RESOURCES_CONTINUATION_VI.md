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
