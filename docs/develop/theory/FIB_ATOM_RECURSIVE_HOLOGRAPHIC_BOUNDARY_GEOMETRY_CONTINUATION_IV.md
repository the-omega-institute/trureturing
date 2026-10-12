# FIB atomic recursive holographic boundary geometry IV: centered finite-source response

## 92. The original occurrence source and the Fibonacci finite part

**Definition 92.1 (one finite native source and its centered response).**
Let $\mathcal T$ be the free nonempty finite ordered source algebra
$t::=\alpha\mid\beta\mid\langle t,t\rangle$ of
[FIB relational continuation, Definition 1.1](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md).
An occurrence is an actual node at its left/right address, not a subtree value;
equal subtrees at different addresses remain different vertices. For each
$t\in\mathcal T$, let $V_t$ be its occurrence vertices, $r$ its root,
$E_t$ its parent–child edges, and $N_t=|V_t|$. Use precisely the closed
counting-measure, unit-conductance comparison operator of
[the boundary geometry, §52](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md)
and [Continuation III, §91](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md):

$$
(L_t f)(x)=\sum_{y\sim x}(f(x)-f(y)),\qquad
\langle f,L_t f\rangle=\sum_{\{x,y\}\in E_t}|f(x)-f(y)|^2.
\tag{92.1}
$$

There is no root killing term. Labels, order and every occurrence remain part
of the source even though this operator gives the same unit conductance to
every existing edge. For $\lambda>0$, set

$$
\begin{aligned}
G_\lambda(t)&=\langle\delta_r,(L_t+\lambda I)^{-1}\delta_r\rangle,\\
C(t)&=\langle\delta_r,L_t^+\delta_r\rangle,\\
R_\lambda(t)&=G_\lambda(t)-\frac1{N_t\lambda},\qquad
A(t)=N_t^2 C(t).
\end{aligned}
\tag{92.2}
$$

Here $L_t^+$ is zero on constants and is the inverse of $L_t$ on the
mean-zero subspace. Thus $C$ is the centered finite part, and $R_\lambda$
is the centered residual at positive screening. The term $1/(N_t\lambda)$
is the exact root weight of the constant mode, not $1/\lambda$.
These definitions specify mathematical functionals; evaluating the
subtraction from supplied observations additionally requires knowledge of
$N_t$. The definition grants no node-count observation.

For an edge $e$, orient it away from $r$ and let $N_e$ be the number of
occurrences in the component below $e$ after deleting it. Every occurrence,
edge, mass, operator and response in (92.1)–(92.2) belongs to the same
original $t$. In an execution with immutable $\mathrm{INITIAL}=t$, none
of these symbols is evaluated on a substituted current register.

**Definition 92.2 (the native Fibonacci comparison family).**
Let $F_0=0$, $F_1=1$ and $F_{j+2}=F_{j+1}+F_j$. Take exactly the
original ordered substitution
$\rho\alpha=\beta$, $\rho\beta=\langle\beta,\alpha\rangle$,
$\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle$. Its source
family is

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_n=\langle T_{n-1},T_{n-2}\rangle\quad(n\ge2).
\tag{92.3}
$$

Write $N_n=N_{T_n}$, $C_n=C(T_n)$ and $A_n=A(T_n)$. These are
separately specified finite inputs for the responses in Definition 92.1.
Their comparison does not replace INITIAL during one execution. In
particular, the occurrence operator here is not the operator on complete
successive source states considered in Continuation III, §89, nor is a
post-observation quotient from its §90 substituted for the source.

**Theorem 92.3 (native Fibonacci centered recurrence and infinite limit).**
For all $n\ge0$, $N_n=2F_{n+1}-1$. The centered finite parts satisfy

$$
\begin{aligned}
C_0=C_1&=0,\\
C_n&=\left(\frac{N_{n-1}}{N_n}\right)^2(C_{n-1}+1)
    +\left(\frac{N_{n-2}}{N_n}\right)^2(C_{n-2}+1)
       &&(n\ge2),\\
A_0=A_1&=0,\\
A_n&=A_{n-1}+A_{n-2}+N_{n-1}^2+N_{n-2}^2
       &&(n\ge2).
\end{aligned}
\tag{92.4}
$$

Moreover $0\le C_n\le2$ for every $n$, and

$$
\lim_{n\to\infty}C_n=\frac{\sqrt5}{2}.
\tag{92.5}
$$

**Proof.**
First establish the finite-graph background identities on the actual
source of Definition 92.1. The energy formula, constant kernel of a
connected graph Laplacian and spectral definition of the pseudoinverse
are classical intermediate facts; see von Luxburg,
[*A Tutorial on Spectral Clustering*](https://arxiv.org/abs/0711.0189),
§3.1, Propositions 1–2, and §6, also the
[repository source note](../../../Library/Geometry/vonluxburg2007spectralclustering.md).
They are used here as background, not as new standalone results.

When $N_t>1$, choose a real orthonormal eigenbasis $v_0,\ldots,v_{N_t-1}$
of $L_t$, with $v_0=N_t^{-1/2}\mathbf1$ and positive eigenvalues
$\nu_1,\ldots,\nu_{N_t-1}$. The elementary spectral decomposition gives

$$
\begin{aligned}
G_\lambda(t)&=\frac1{N_t\lambda}
    +\sum_{j=1}^{N_t-1}\frac{|v_j(r)|^2}{\nu_j+\lambda},\\
R_\lambda(t)&=\sum_{j=1}^{N_t-1}\frac{|v_j(r)|^2}{\nu_j+\lambda},\qquad
C(t)=\sum_{j=1}^{N_t-1}\frac{|v_j(r)|^2}{\nu_j}.
\end{aligned}
\tag{92.6}
$$

In particular, for each fixed original finite $t$,

$$
\lim_{\lambda\downarrow0}R_\lambda(t)=C(t).
\tag{92.7}
$$

For $\gamma_t=\min_j\nu_j>0$ and
$D_t=\sum_{j=1}^{N_t-1}|v_j(r)|^2/\nu_j^2$, the exact remainder is

$$
\begin{aligned}
C(t)-R_\lambda(t)
 &=\lambda\sum_{j=1}^{N_t-1}
   \frac{|v_j(r)|^2}{\nu_j(\nu_j+\lambda)},\\
0\le C(t)-R_\lambda(t)&\le\lambda D_t
 \le\frac{\lambda}{\gamma_t}C(t).
\end{aligned}
\tag{92.8}
$$

The constants are source-dependent. This proves a fixed-tree limit,
not a uniform limit over arbitrary $t$ or over the Fibonacci family.
For either singleton label, $L_t=0$, $G_\lambda(t)=1/\lambda$,
$R_\lambda(t)=C(t)=0$; the sums are empty, and no positive gap
$\gamma_t$ is needed.

For the component-mass calculation put
$f=\delta_r-N_t^{-1}\mathbf1$ and $u=L_t^+\delta_r$.
Then $\sum_xu(x)=0$ and $L_tu=f$. Summing this equation over the
component below $e$ cancels all its internal edges and gives
$u(\operatorname{child}(e))-u(\operatorname{parent}(e))=-N_e/N_t$.
Consequently the same finite-source energy is

$$
C(t)=u(r)=\langle u,f\rangle=\langle u,L_tu\rangle
       =\sum_{e\in E_t}\left(\frac{N_e}{N_t}\right)^2.
\tag{92.9}
$$

This is the usual centered Poisson/edge-flux identity, here instantiated
on the retained native occurrences as an intermediate calculation.
It includes the singleton by the empty sum. The right side is not a
formula on leaf masses or on a graph in which identical subtrees have
been merged.

For $t=\langle a,b\rangle$, every edge inside $a$ or $b$ has the
same below-edge mass as in that original subtree, and the two new
root edges have masses $N_a$ and $N_b$. Equation (92.9) therefore gives

$$
N_t=1+N_a+N_b,\qquad
A(t)=A(a)+A(b)+N_a^2+N_b^2.
\tag{92.10}
$$

The recurrence $N_n=1+N_{n-1}+N_{n-2}$ with $N_0=N_1=1$ proves
$N_n=2F_{n+1}-1$ by induction, and (92.10) proves both forms of (92.4).

For boundedness, the counts are nondecreasing and
$N_{n-1}\le2N_{n-2}+1$ for $n\ge2$. At $n=2$ this is immediate;
at $n\ge3$ use
$N_{n-1}=N_{n-2}+N_{n-3}+1$ and $N_{n-3}\le N_{n-2}$.
Thus, with $x_n=N_{n-1}/N_n$ and $y_n=N_{n-2}/N_n$,

$$
0<x_n<\frac23,\qquad 0<y_n\le x_n<\frac23,\qquad
x_n+y_n=1-\frac1{N_n}<1,
\qquad x_n^2+y_n^2<\frac23.
\tag{92.11}
$$

If the two preceding centered responses are at most two, (92.4) is
at most $3(x_n^2+y_n^2)<2$. Starting with zero proves
$0\le C_n\le2$, before any use of a limsup.

Let $\varphi=(1+\sqrt5)/2$. Solving the scalar Fibonacci recurrence,
or verifying its two characteristic roots and initial values, gives

$$
F_j=\frac{\varphi^j-(-\varphi^{-1})^j}{\sqrt5}.
\tag{92.12}
$$

It follows that $x_n\to\varphi^{-1}$ and $y_n\to\varphi^{-2}$.
Set $s=\varphi^{-2}+\varphi^{-4}=5-2\sqrt5$, so $0<s<1$.
The finite quantities $M=\limsup_n C_n$ and $m=\liminf_n C_n$
exist by (92.11) and nonnegativity. For every $\epsilon>0$, both
preceding terms eventually lie in $[m-\epsilon,M+\epsilon]$.
Use these two bounds in (92.4), take the lower and upper limits,
and then let $\epsilon\downarrow0$. This gives

$$
m\ge s(m+1),\qquad M\le s(M+1).
\tag{92.13}
$$

Hence $m\ge s/(1-s)$ and $M\le s/(1-s)$. Since $m\le M$,
they coincide. Finally
$s/(1-s)=(5-2\sqrt5)/(2\sqrt5-4)=\sqrt5/2$.
This proves convergence, rather than an inference from finite values. $\square$

## 93. Positive screening from finite native perfect trees

**Definition 93.1 (finite perfect comparison sources).**
Let $B_0=\alpha$ and $B_{k+1}=\langle B_k,B_k\rangle$ for
$k\in\mathbb N_0$. These are separate finite ordered native sources,
each of whose repeated subtree copies has its own occurrences.
They have $N_{B_k}=2^{k+1}-1$. Put
$g_k(\lambda)=G_\lambda(B_k)$ for $\lambda>0$, with the same
closed operator and measure as in Definition 92.1.

**Theorem 93.2 (screened Fibonacci limit without an infinite source).**
For every fixed $\lambda>0$,

$$
\lim_{n\to\infty}G_\lambda(T_n)
 =\lim_{k\to\infty}g_k(\lambda)
 =b_\lambda
 :=\frac{2}{\lambda+1+\sqrt{\lambda^2+6\lambda+1}}.
\tag{93.1}
$$

More precisely, for every $h\ge0$ and every $n\ge2h+2$,

$$
|G_\lambda(T_n)-b_\lambda|
 \le\lambda^{-1}\left(\frac3{3+\lambda}\right)^{2h+3}.
\tag{93.2}
$$

All operators in this assertion are the original finite-source operators.
No infinite-source operator realization is assumed.

**Proof.**
For a finite subtree with closed response $g=G_\lambda(t)$,
adding one unit parent seam changes its child-root block to
$L_t+\lambda I+|r\rangle\langle r|$. Its diagonal inverse is
$g/(1+g)$, by the elementary rank-one inverse identity.
Eliminating the two child blocks at the root of
$\langle a,b\rangle$ therefore gives the finite Schur complement

$$
G_\lambda(\langle a,b\rangle)
 =\frac1{\lambda+2-G_\lambda(a)/(1+G_\lambda(a))
                    -G_\lambda(b)/(1+G_\lambda(b))}.
\tag{93.3}
$$

The root diagonal is $\lambda+2$, because the original closed root has
exactly two children. The parent terms occur only in the eliminated child
blocks; they do not change the original whole-source boundary convention.
These rank-one and Schur identities are intermediate matrix calculations.

For the finite perfect sources they yield

$$
g_0(\lambda)=\frac1\lambda,\qquad
g_{k+1}(\lambda)=f_\lambda(g_k(\lambda)),\qquad
f_\lambda(g)=\frac{1+g}{\lambda+2+\lambda g}.
\tag{93.4}
$$

The positive number in (93.1) is the positive root of
$\lambda b^2+(\lambda+1)b-1=0$ and satisfies $f_\lambda(b)=b$.
For $g\ge0$,

$$
0<f_\lambda'(g)=\frac2{(\lambda+2+\lambda g)^2}
 \le\frac2{(\lambda+2)^2}<1.
\tag{93.5}
$$

Thus
$|g_k(\lambda)-b_\lambda|
 \le[2/(\lambda+2)^2]^k|\lambda^{-1}-b_\lambda|$,
proving the perfect-tree limit purely from finite matrices.

Use the inclusive four-reply table $p_h$ of Continuation III, (91.1).
At every address of length at most $h$, $T_n$ is a branch when
$n\ge2h+2$: descending one edge decreases the Fibonacci index by
one or two, so the index at any such address is still at least two.
The same table consists entirely of branches on $B_k$ when $k\ge h+1$.
Thus $p_h(T_n)=p_h(B_k)$ under these two conditions.
The same-operator certificate of Theorem 91.2, with
$q_\lambda=3/(3+\lambda)$, is exactly

$$
|G_\lambda(T_n)-g_k(\lambda)|
 \le\lambda^{-1}q_\lambda^{2h+3}.
\tag{93.6}
$$

There is no factor two. Holding $h,n,\lambda$ fixed and taking the
already proved scalar limit $k\to\infty$ gives (93.2).
For any fixed positive $\lambda$, its right side tends to zero as
$h\to\infty$, and all $n\ge2h+2$ obey it. This proves the Fibonacci
limit. The locality input is precisely §91; its
[Benzi–Boito–Razouk reference](https://arxiv.org/abs/1203.3953) is
background for sparse-matrix locality, not an additional decay theorem
used in this argument. $\square$

## 94. The two centered limit orders

**Theorem 94.1 (noncommuting centered limits on the native Fibonacci family).**
For $R_\lambda$ in (92.2), both iterated limits exist, and

$$
\lim_{\lambda\downarrow0}\lim_{n\to\infty}R_\lambda(T_n)=1,
\qquad
\lim_{n\to\infty}\lim_{\lambda\downarrow0}R_\lambda(T_n)
 =\frac{\sqrt5}{2}.
\tag{94.1}
$$

In particular, zero-screening passage is not uniform on this source
family. Quantitatively, for every $\lambda>0$,

$$
\sup_{n\ge0}|C_n-R_\lambda(T_n)|
 \ge\frac{\sqrt5}{2}-b_\lambda,
\qquad
\liminf_{\lambda\downarrow0}
 \sup_{n\ge0}|C_n-R_\lambda(T_n)|
 \ge\frac{\sqrt5}{2}-1>0.
\tag{94.2}
$$

This failure coexists with the uniform prefix certificate at every
fixed strictly positive $\lambda$.

**Proof.**
For fixed $\lambda>0$, $N_n\to\infty$, so
$1/(N_n\lambda)\to0$. Theorem 93.2 consequently gives
$\lim_nR_\lambda(T_n)=b_\lambda$. Directly from (93.1),
$\lim_{\lambda\downarrow0}b_\lambda=1$.
In the reverse order the fixed-tree spectral calculation (92.7) gives
$\lim_{\lambda\downarrow0}R_\lambda(T_n)=C_n$ for each $n$,
including the two singleton sources. Theorem 92.3 then gives the
second limit in (94.1).

For fixed positive $\lambda$, (92.8) shows that the absolute
difference in (94.2) is $C_n-R_\lambda(T_n)\ge0$.
Its limit as $n\to\infty$ is $\sqrt5/2-b_\lambda$.
Every supremum is at least this limit, proving (94.2).
The supremum is finite, since $R_\lambda(T_n)\le C_n\le2$.
Also $b_\lambda<1$ for positive $\lambda$, so the limiting gap
is strictly positive. No uniform centered passage follows from (92.8),
and the fixed-positive estimates (91.6)–(91.7) are preserved.
Their parameter domain excludes $\lambda=0$.

The centering is essential to the statement: at each fixed $n$,
$G_\lambda(T_n)$ itself diverges like $1/(N_n\lambda)$.
The finite part solves a centered Poisson equation
$L_tu=\delta_r-N_t^{-1}\mathbf1$, as in the proof of Theorem 92.3.
It is not a solution of $L_tu=\delta_r$, whose right side has
nonzero total mass whereas every $L_tu$ has total mass zero.
Nor is it an isolated unscreened Green function on an unspecified
infinite source. $\square$

## 95. Unbounded centered response in one native prefix fibre

**Definition 95.1 (the combs, the grafts and the observed table).**
For $m,h\in\mathbb N_0$, let

$$
K_0=\alpha,\qquad K_{m+1}=\langle K_m,\alpha\rangle,
\qquad W_0(t)=t,\qquad W_{h+1}(t)=\langle W_h(t),\alpha\rangle.
\tag{95.1}
$$

The $W_h$ are exactly the finite binary grafts in Continuation III,
(91.8), now applied to these specified native sources. One $t$ is
retained once, not copied or identified with another occurrence.
$N_{K_m}=2m+1$, and $N_{W_h(t)}=N_t+2h$.
For every address $a\in\{L,R\}^*$ of length at most $h$, retain
the full four-reply observation

$$
p_h(t)(a)=
\begin{cases}
\alpha,&a\text{ is an alpha leaf},\\
\beta,&a\text{ is a beta leaf},\\
\mathsf{branch},&a\text{ is a pair occurrence},\\
\mathsf{absent},&a\text{ is not an occurrence}.
\end{cases}
\tag{95.2}
$$

This is the original-root table (91.1), including all addresses below
early terminal leaves and their absence replies. Its domain is
$\mathcal T$ with arbitrary finite source size unless an explicit
source cap or domain promise is imposed.

**Theorem 95.2 (infinite unrestricted error from a single prefix fibre).**
For every fixed $h\ge0$ there exists one table $p_h^*$ such that

$$
p_h(W_h(K_m))=p_h^*\quad(m\ge1),\qquad
\sup_{\{t\in\mathcal T:\ p_h(t)=p_h^*\}}C(t)=+\infty.
\tag{95.3}
$$

Consequently every real-valued estimator
$E:\{p_h(t):t\in\mathcal T\}\to\mathbb R$ has

$$
\sup_{t\in\mathcal T}|E(p_h(t))-C(t)|=+\infty.
\tag{95.4}
$$

The assertion has no common finite source-size bound.

**Proof.**
On $K_m$, the $m$ left-spine edges have below-edge masses
$1,3,\ldots,2m-1$, and the $m$ right leaf edges each have mass one.
Using (92.9), including the empty sums at $m=0$, gives

$$
C(K_m)=\frac{\sum_{j=0}^{m-1}(2j+1)^2+m}{(2m+1)^2}
      =\frac{4m^3+2m}{3(2m+1)^2},
\qquad
\lim_{m\to\infty}\frac{C(K_m)}m=\frac13.
\tag{95.5}
$$

For an arbitrary fixed native $t$ with $N=N_t$, its old internal
below-edge masses are unchanged by wrapping. The added spine edges
have masses $N,N+2,\ldots,N+2h-2$, and there are $h$ added
right leaf edges. Hence

$$
C(W_h(t))
 =\frac{N^2C(t)+\sum_{j=0}^{h-1}[(N+2j)^2+1]}{(N+2h)^2}
 \ge\left(\frac{N}{N+2h}\right)^2 C(t).
\tag{95.6}
$$

For fixed $h$, substitute $t=K_m$. The squared prefactor tends
to one and (95.5) diverges, so $C(W_h(K_m))\to+\infty$.

Every $K_m$ for $m\ge1$ has a branch root. The common table on
the wrapped sources is explicitly

$$
p_h^*(a)=
\begin{cases}
\mathsf{branch},&a=L^j,\ 0\le j\le h,\\
\alpha,&a=L^jR,\ 0\le j<h,\\
\mathsf{absent},&\text{every other }a\text{ with }|a|\le h.
\end{cases}
\tag{95.7}
$$

The branch at $L^h$ is the retained seed root. No strict descendant
of that root is within the observation depth. Every other reached
side leaf is the specified alpha leaf; all its strict extensions are
absent. The beta reply from the four-reply contract occurs nowhere
in this particular fibre, and no reply type is discarded or merged.
Thus (95.3) holds even at $h=0$, when the table contains only the
branch root. Finally $E(p_h^*)$ is one finite real number,
independent of $m$. The unbounded sequence of target values makes
its absolute errors unbounded, proving (95.4). $\square$

## 96. The separate obstruction with exact size and leaf word

**Definition 96.1 (the strengthened supplied data).**
Let $\operatorname{word}(t)$ be the left-to-right word of all
original leaf labels, retaining multiplicity. At a fixed depth $h$,
the strengthened observation is

$$
\eta_h(t)=(p_h(t),N_t,\operatorname{word}(t)).
\tag{96.1}
$$

Exact node count and the entire leaf word are supplied here as
additional data; they are not inferred as sensors from centering
or from the prefix service.

**Theorem 96.2 (infinite error even with the strengthened data).**
For every $h\ge0$ and every $k\ge1$, the two native sources
$W_h(B_k)$ and $W_h(K_{2^k-1})$ satisfy

$$
\begin{aligned}
\eta_h(W_h(B_k))&=\eta_h(W_h(K_{2^k-1})),\\
N_{W_h(B_k)}=N_{W_h(K_{2^k-1})}&=2^{k+1}-1+2h,\\
\operatorname{word}(W_h(B_k))
 =\operatorname{word}(W_h(K_{2^k-1}))&=\alpha^{\,2^k+h},\\
C(W_h(B_k))&\le1+h,\\
\lim_{k\to\infty}C(W_h(K_{2^k-1}))&=+\infty.
\end{aligned}
\tag{96.2}
$$

Consequently every real-valued
$E:\{\eta_h(t):t\in\mathcal T\}\to\mathbb R$ satisfies

$$
\sup_{t\in\mathcal T}|E(\eta_h(t))-C(t)|=+\infty.
\tag{96.3}
$$

This is a strengthened observation theorem separate from the
$p_h$-only theorem. It rules out a single uniform finite
worst-case absolute error on all finite sources, not bounds that
depend on the supplied size or on a common finite source cap.

**Proof.**
Both seeds have $2^k$ leaves, $2^{k+1}-1$ nodes, an all-alpha
leaf word and a branch root when $k\ge1$. Each wrap appends one
alpha leaf and two nodes. Formula (95.7) depends only on the
branch seed root, so both wrapped prefixes are $p_h^*$.
This proves the three data equalities with all four prefix replies.

Put $c_k=C(B_k)$ and $M_k=N_{B_k}$. Formula (92.10) gives

$$
c_0=0,\qquad
c_{k+1}=2\left(\frac{M_k}{2M_k+1}\right)^2(c_k+1).
\tag{96.4}
$$

The coefficient is less than $1/2$. If $c_k\le1$, then
$c_{k+1}<1$. Induction proves $0\le c_k\le1$ for every $k$.
For every native $t$ with $N=N_t$, the single-wrap formula is

$$
C(W_1(t))=\frac{N^2(C(t)+1)+1}{(N+2)^2}\le C(t)+1.
\tag{96.5}
$$

Indeed $C(t)\ge0$, and subtracting the numerator from
$(N+2)^2(C(t)+1)$ gives $(4N+4)(C(t)+1)-1>0$.
Iterating (96.5) proves $C(W_h(B_k))\le1+h$.
The divergence of the comb response follows from (95.5)–(95.6)
with $m=2^k-1\to\infty$ and fixed $h$.

For each $k$, the estimator has one common value $e_k$ on the
pair in (96.2), even though that value may depend arbitrarily on
their shared size and word. The triangle inequality gives

$$
\max\bigl\{
 |e_k-C(W_h(B_k))|,
 |e_k-C(W_h(K_{2^k-1}))|
\bigr\}
 \ge\frac12\left|C(W_h(K_{2^k-1}))-C(W_h(B_k))\right|.
\tag{96.6}
$$

The right side tends to infinity, proving (96.3).
The construction keeps the source, data and target of each member
on its own original occurrence tree, and supplies no operation
which changes one INITIAL into the other.

For completeness, the intermediate component-mass formula also gives,
for every $t\in\mathcal T$,

$$
0\le C(t)\le N_t-1.
\tag{96.7}
$$

Indeed there are $N_t-1$ edges, and each term of (92.9) is between
zero and one. Thus the constant-zero estimate has size-dependent
error at most $N_t-1$, and has uniform error at most $M-1$ on a
domain promised to have $N_t\le M$, for any fixed integer $M\ge1$.
This proves compatibility of the unrestricted obstruction with
both restricted claims; neither supplies a new source-size sensor.
$\square$

## 97. Positive approximation under the original Fibonacci domain promise

**Assumption 97.1 (supplied prefix and a Fibonacci-only original input).**
The original unknown finite source is promised to be exactly one
$T_n$ of Definition 92.2, with $n\ge0$, and its inclusive table
$p_h(T_n)$ is supplied. If interpreted as a native acquisition,
this supply has the additional source/version authentication,
epoch, refusal and absorbing Stop premises of Continuation III,
Assumption 91.6. The supplied data concern the original root of
the immutable source, not a current root after substitution.
The promise restricts the possible original inputs; it is not
a permission to prepare, compare or retain a family of new INITIALs.

**Theorem 97.2 (finite-index identification and uniform promised-tail response).**
Under Assumption 97.1, $p_h(T_n)$ determines the exact index whenever
$n\le2h+1$, and otherwise determines the alternative $n\ge2h+2$.
The following real-valued estimate is therefore well-defined on the
actual Fibonacci prefix image:

$$
\widehat C_h(p_h(T_n))=
\begin{cases}
C_n,&n\le2h+1,\\
\sqrt5/2,&n\ge2h+2.
\end{cases}
\tag{97.1}
$$

It obeys

$$
\sup_{n\ge0}|\widehat C_h(p_h(T_n))-C_n|
 =\epsilon_h:=
  \sup_{n\ge2h+2}|C_n-\sqrt5/2|,
\qquad
\lim_{h\to\infty}\epsilon_h=0.
\tag{97.2}
$$

For each fixed $\lambda>0$ there is also a well-defined
positive-screening centered-residual estimate

$$
\widehat R_{h,\lambda}(p_h(T_n))=
\begin{cases}
R_\lambda(T_n),&n\le2h+1,\\
b_\lambda,&n\ge2h+2,
\end{cases}
\tag{97.3}
$$

with the explicit bound

$$
\sup_{n\ge0}
 |\widehat R_{h,\lambda}(p_h(T_n))-R_\lambda(T_n)|
 \le\frac1\lambda\left[
 \left(\frac3{3+\lambda}\right)^{2h+3}
 +\frac1{2F_{2h+3}-1}\right]\longrightarrow0
 \quad(h\to\infty,\ \lambda>0\text{ fixed}).
\tag{97.4}
$$

These are response approximations under the domain promise.
They do not establish a new lawful acquisition operation, and
(97.4) asserts no uniformity as $\lambda\downarrow0$.

**Proof.**
Repeated right descent in (92.3) gives the first terminal on the
rightmost path at depth $j=\lfloor n/2\rfloor$. Its label is
alpha for $n=2j$, and beta for $n=2j+1$; all earlier rightmost
addresses are branches. If $j\le h$, the four-reply table therefore
determines $j$ and the parity, hence $n$. This includes $n=0,1$
at depth zero. When $n\ge2h+2$, every address through depth $h$
is a branch, by the proof of Theorem 93.2. The same table has no
leaf, whereas each $n\le2h+1$ has its rightmost terminal in the
table. The tail and all the identified indices are consequently
disjoint prefix classes.

The exact finite values in the first branches of (97.1) and (97.3)
are mathematical functions of the identified $n$: use (92.4) for
$C_n$ and (93.3) with initial values $1/\lambda$ for
$G_\lambda(T_0)=G_\lambda(T_1)$, and then (92.2).
This makes both estimates single-valued without adding an
observation field. In the unresolved tail, the estimates use
only the stated constants and require no exact node count.

All errors in (97.1) vanish for the identified indices, giving the
equality in (97.2). The convergence (92.5) says that for each
$\delta>0$ there exists $n_0$ with
$|C_n-\sqrt5/2|<\delta$ for every $n\ge n_0$.
Taking $2h+2\ge n_0$ proves $\epsilon_h\to0$.
Boundedness of $C_n$ makes every tail supremum finite.

For $n\ge2h+2$, (93.2) and the exact subtraction give

$$
|R_\lambda(T_n)-b_\lambda|
 \le|G_\lambda(T_n)-b_\lambda|+\frac1{N_n\lambda}
 \le\lambda^{-1}q_\lambda^{2h+3}
      +\frac1{\lambda N_{2h+2}}.
\tag{97.5}
$$

The counts are nondecreasing and
$N_{2h+2}=2F_{2h+3}-1\to\infty$, while $q_\lambda<1$
for each fixed positive $\lambda$. This proves (97.4).
The unrestricted comb witnesses in Theorems 95.2 and 96.2 are
outside the promised Fibonacci-only input domain; the estimates
do not extend those restricted guarantees to them. $\square$

**Assumption 97.3 (an additional source-to-space realization).**
A spatial or physical realization of these comparison responses
would require, for the same original source $t$, a specified map
from $V_t$ to spatial positions, a matching measure and edge law,
an operator and boundary correspondence, and a native realization
of the declared symmetric propagation with its permitted actions
and clock. Metric length and physical dimension would be further
data or conclusions of that additional model. The occurrence
vertices of Definition 92.1, the successive complete states of
Continuation III, §89, and the source quotients of §90 are distinct
carriers; a correspondence between them would require its own
map and proof.

Theorems 92.3–97.2 assume only the finite occurrence comparison
operator and their stated supplied-input promises. They assume
no such spatial realization, no isolated unscreened infinite-source
Green function and no recovery of the whole spectrum or its
multiplicities from the scalar response. The existence and
admissibility of the additional realization remain a separate
mathematical bridge.

## 97.99 追加锚（本行以下为增补区）
