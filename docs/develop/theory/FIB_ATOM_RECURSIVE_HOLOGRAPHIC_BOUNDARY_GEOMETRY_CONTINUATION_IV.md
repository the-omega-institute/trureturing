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

## 98. The all-occurrence measure and its addressed boundary trace

**Definition 98.1 (one address-edge space and the source measures).**
Retain precisely $T_n$, $N_n$, $L_n$ and $R_\lambda(T_n)$ of
Definitions 92.1–92.2. Each $T_n$ is a separately supplied original
finite source. Let $\mathcal E=\{L,R\}^{+}$: a nonempty word $p$
indexes the edge from $p^{-}$ to $p$, when that edge occurs.
All edge Hilbert spaces below are subspaces of the single real
$\mathscr H=\ell^2(\mathcal E)$, by extension by zero. Put

$$
s(p)=\#_L(p)+2\#_R(p),\qquad
a=\varphi^{-1},\quad b=\varphi^{-2},\quad a+b=1,
\qquad s(\varnothing)=0.
\tag{98.1}
$$

Let $\mu_n$ assign mass $1/N_n$ to every occurrence address in
$V_{T_n}$, including the root, every internal node and every terminal.
For a nonempty address $p$ define its reached-descendant mass by
$m_n(p)=\mu_n\{x:p\preceq x\}$; set $m_n(\varnothing)=1$.
Define the root-path increment map, with missing edges ignored, by

$$
J_n:\mathscr H\longrightarrow L^2(V_{T_n},\mu_n),\qquad
(J_nz)(x)=\sum_{\varnothing\ne p\preceq x}z_p.
\tag{98.2}
$$

The sum uses only actual edges of $T_n$. In particular $J_nz$ is
zero at the root. Set
$v_n=J_n^*\mathbf1$, $B_n=J_n^*J_n$ and
$\Sigma_n=B_n-v_n\otimes v_n$, where
$(u\otimes u)z=\langle u,z\rangle u$.
These operators act on $\mathscr H$; their node-space codomains
in (98.2) are not identified with one another.

Let $\Omega=\{L,R\}^{\mathbb N}$ and let $M$ be the Bernoulli
probability law with probabilities $(a,b)$, so its cylinders satisfy

$$
M([p])=a^{\#_L(p)}b^{\#_R(p)}=\varphi^{-s(p)}=:m(p).
\tag{98.3}
$$

For finitely supported $z\in\mathscr H$, define
$(Jz)(\omega)=\sum_{p\preceq\omega}z_p$.
Whenever this map has a bounded extension into $L^2(\Omega,M)$,
use $v=J^*\mathbf1$, $B=J^*J$ and
$\Sigma=B-v\otimes v$.

**Theorem 98.2 (source masses, compact trace and covariance convergence).**
For a nonempty $p$, put $d=n-s(p)$. The address is reached exactly
when $d\ge0$ and $n-s(p^{-})\ge2$. In that case its entire descendant
source is $T_d$, and

$$
m_n(p)=\frac{N_d}{N_n}.
\tag{98.4}
$$

Otherwise $m_n(p)=0$. A reached $d=0$ is an alpha terminal, a reached
$d=1$ is a beta terminal, and a reached $d\ge2$ is a branch.
Each reached node has point mass $1/N_n$; a terminal has no strict
descendant addresses. At the root the same label classification uses
$d=n$, including the singletons $n=0,1$.

For every fixed $p$, $m_n(p)\to m(p)$. There is a uniform bound
$m_n(p)\le K a^{|p|}$ with $K=2\varphi$, and $m(p)\le a^{|p|}$.
If $P_h$ is the coordinate projection onto $1\le |p|\le h$, then

$$
\begin{aligned}
\|J_n(I-P_h)\|&\le
 \left(\frac{K a^{h+1}}{1-a}\right)^{1/2},\\
\|J(I-P_h)\|&\le
 \left(\frac{a^{h+1}}{1-a}\right)^{1/2}.
\end{aligned}
\tag{98.5}
$$

Consequently $J$ has a unique bounded compact extension,
and, on the specified common edge space,

$$
v_n\longrightarrow v\text{ in }\ell^2,\qquad
B_n\longrightarrow B,\quad \Sigma_n\longrightarrow\Sigma
       \text{ in operator norm}.
\tag{98.6}
$$

For the actual counting-measure screening, including $n=0,1$,

$$
R_\lambda(T_n)
 =\left\langle v_n,(I+N_n\lambda\Sigma_n)^{-1}v_n\right\rangle
 \qquad(\lambda>0).
\tag{98.7}
$$

**Proof.**
Every left descent subtracts one from the residual source index;
every right descent subtracts two. A descent is permitted only from
an index at least two. The last parent has the smallest residual
index among the proper prefixes, so its branch condition, together
with nonnegative final index, is necessary and sufficient for the
whole path. This proves the reached-address criterion and (98.4).
Equivalently, a last left edge requires $d\ge1$, while a last right
edge permits $d=0$. This distinction accounts for early alpha
terminals and their absent extensions.

By (92.12), for fixed $s(p)$ the ratio in (98.4) tends to
$\varphi^{-s(p)}$; the address is eventually reached and is then
a branch. Its point mass tends to zero. For every integer $h\ge1$,

$$
\mu_n\{x:|x|<h\}\le\frac{2^h-1}{N_n}\longrightarrow0.
\tag{98.8}
$$

This bound includes any terminals at these depths. The first terminal
depth is $\lfloor n/2\rfloor$, as in Theorem 97.2, so fixed-depth
terminals eventually disappear. Thus (98.3) is the limiting law of
all-node descendant cylinders, not an assertion that $\mu_n$ was a
leaf measure or that it already lived on $\Omega$.

The elementary count bounds
$N_j\ge\varphi^{j-1}$ and $N_j\le2\varphi^j$ hold for $j=0,1$ and
then by the count recurrence and $F_{j+1}\le\varphi^j$.
For a reached address, they give
$N_{n-s(p)}/N_n\le2\varphi\,\varphi^{-s(p)}
 \le K a^{|p|}$; an absent address satisfies the same inequality.

The path-sum operator and its descendant-mass adjoint are the
classical tree Hardy operators; see
[*Potential theory on trees, graphs and Ahlfors-regular metric
spaces*, §5.1, (41)](https://arxiv.org/html/1010.4788v3),
with the root coordinate omitted here because the variables are
edge increments. Theorem 32 there supplies the general weighted
trace framework. The fair dyadic-law trace criterion in
[Bernicot–Maury–Salort, *A 2-adic approach of the human respiratory
tree*, Proposition 1](https://arxiv.org/html/1005.0445v1)
uses Haar cylinder masses $2^{-|p|}$; it does not identify that law
with the biased $M$ in (98.3).
For the present source law the required estimate follows directly.

At depth $k$, descendant sets of distinct reached addresses are
disjoint. For $z^{(k)}$ supported at that depth,

$$
\|J_n z^{(k)}\|_{L^2(\mu_n)}^2
 =\sum_{|p|=k}m_n(p)|z_p|^2
 \le K a^k\|z^{(k)}\|^2.
\tag{98.9}
$$

The analogous bound for $J$ has $K=1$, because its depth-$k$
cylinders partition $\Omega$. The triangle inequality followed
by Cauchy–Schwarz gives

$$
\left\|\sum_{k>h}J_nz^{(k)}\right\|
 \le\sum_{k>h}(K a^k)^{1/2}\|z^{(k)}\|
 \le\left(\sum_{k>h}K a^k\right)^{1/2}\|z\|.
\tag{98.10}
$$

This proves (98.5), including $h=0$ and the corresponding bound
for $J$. It establishes the bounded extension by completion.
Since $JP_h$ has finite rank and its norm distance to $J$ tends
to zero, $J$ is compact. This is an $L^2(M)$ trace; pointwise
continuity of arbitrary finite-energy traces has not been used.

Taking adjoints on individual coordinates gives

$$
(v_n)_p=m_n(p),\quad v_p=m(p),\qquad
(B_n)_{pq}=
 \begin{cases}
 m_n(q),&p\preceq q,\\
 m_n(p),&q\preceq p,\\
 0,&p,q\text{ incomparable}.
 \end{cases}
\tag{98.11}
$$

The formula for $B$ replaces $m_n$ by $m$.
It also holds when one address is absent, since its descendant
set is empty. Every fixed finite block therefore converges.
Uniform boundedness of $J_n$ and (98.5) imply

$$
\|B_n-P_hB_nP_h\|
 \le2\|J_n\|\|J_n(I-P_h)\|,\qquad
\|(I-P_h)v_n\|\le\|J_n(I-P_h)\|.
\tag{98.12}
$$

The same estimates hold for $B,v$.
First choose $h$ to make the uniform tails small, then use the
finite-block convergence. This proves the first two limits in
(98.6). The third follows from convergence of the rank-one
operators $v_n\otimes v_n$. No identification of changing node
$L^2$ spaces is required. Positivity follows from

$$
\langle z,\Sigma_n z\rangle
 =\operatorname{Var}_{\mu_n}(J_nz),\qquad
\langle z,\Sigma z\rangle
 =\operatorname{Var}_{M}(Jz).
\tag{98.13}
$$

Finally the finite quadratic variational identity for a
positive definite matrix $A$:
$\langle e,A^{-1}e\rangle
 =\sup_f(2\langle e,f\rangle-\langle f,Af\rangle)$,
obtained by completing the square at $f=A^{-1}e$.
On a finite tree every function is uniquely $f=c\mathbf1-J_nz$
on its actual edges, and its unit-edge energy is $\|z\|^2$.
Write $\tau=N_n\lambda$. The root resolvent is thus the supremum of

$$
2c-\|z\|^2-\tau
 \left(c^2-2c\langle v_n,z\rangle+\langle z,B_nz\rangle\right).
\tag{98.14}
$$

Maximizing over $c$ gives
$\tau^{-1}+2\langle v_n,z\rangle
 -\|z\|^2-\tau\langle z,\Sigma_nz\rangle$.
A second completion of the square proves (98.7), with the exact
constant-mode subtraction $\tau^{-1}$ of (92.2).
Coordinates of absent edges contribute only $-\|z\|^2$, so the
same maximization is valid on $\mathscr H$. For $n=0,1$ there
are no edges: $J_n=v_n=B_n=\Sigma_n=0$,
$G_\lambda=1/\lambda$ and $R_\lambda=0$.
The multiplier $N_n$ in (98.7) restores counting screening from
the uniform all-node normalization. $\square$

## 99. The constant-trace projection for the biased source law

**Theorem 99.1 (zero-variance constraints and the retained component).**
For the source-derived $J,v,\Sigma$ of §98, define

$$
q_p=2^{-|p|},\qquad w=v-q.
\tag{99.1}
$$

Then

$$
Jq=\mathbf1,\qquad \|q\|^2=1,\qquad
P_{\ker\Sigma}v=q,\qquad
\|w\|^2=\frac{\sqrt5}{2}-1>0.
\tag{99.2}
$$

More precisely, for $z\in\mathscr H$ let
$S_p=\sum_{\varnothing\ne u\preceq p}z_u$.
For a prefix $p$, let $z^p$ be its strict-descendant increment
vector, reindexed by nonempty suffixes. If $Jz=c$ $M$-almost
everywhere, then for every finite prefix $p$,

$$
Jz^p=c-S_p\quad M\text{-almost everywhere},\qquad
\langle v,z^p\rangle=c-S_p,\qquad
\langle z^p,\Sigma z^p\rangle=0.
\tag{99.3}
$$

All such $z$ obey

$$
\sum_{|p|=k}|c-S_p|^2
 \le\|J\|^2\sum_{|u|>k}|z_u|^2\longrightarrow0.
\tag{99.4}
$$

Conversely, (99.4)'s convergence to zero for some $c$ implies
$Jz=c$ $M$-almost everywhere. In particular,
$z\in\ker\Sigma$ exactly when this condition holds for some $c$,
and then $\langle q,z\rangle=\langle v,z\rangle=c$.

**Proof.**
The covariance identity (98.13) says that $z\in\ker\Sigma$ if
and only if $Jz$ is almost everywhere constant. Indeed
$\Sigma=J^*(I-\mathbf1\otimes\mathbf1)J$, with the middle factor
the orthogonal projection in the probability space $L^2(M)$.
Every cylinder has positive $M$ mass. Conditional on $[p]$,
the suffix law is again $M$, and the trace restricted to that
cylinder is $S_p+Jz^p$. This equality first holds for finite
partial sums and then in conditional $L^2$, by boundedness of
restriction to each fixed positive-mass cylinder. It proves
(99.3), rather than inferring trace continuity from full support.

Since $\|Jz^p\|=|c-S_p|$, boundedness of $J$ bounds its square
by $\|J\|^2\|z^p\|^2$. The strict-descendant sets of the
depth-$k$ prefixes partition all edges deeper than $k$,
so summation proves (99.4).
Conversely, the depth-$k$ path sum $JP_kz$ takes value $S_p$
on $[p]$, hence

$$
\|JP_kz-c\|_{L^2(M)}^2
 =\sum_{|p|=k}m(p)|S_p-c|^2
 \le\sum_{|p|=k}|S_p-c|^2\longrightarrow0.
\tag{99.5}
$$

As $JP_kz\to Jz$ in $L^2(M)$, the asserted converse follows.

For any such constant trace, the fair averages of the finite
level values satisfy

$$
2^{-k}\sum_{|p|=k}S_p
 =\sum_{j=1}^{k}2^{-j}\sum_{|u|=j}z_u
 =\langle P_kq,z\rangle.
\tag{99.6}
$$

By (99.4), their difference from $c$ is at most
$2^{-k/2}(\sum_{|p|=k}|S_p-c|^2)^{1/2}$ and tends to zero.
The vector $q$ lies in $\ell^2$, with
$\|q\|^2=\sum_{j\ge1}2^j4^{-j}=1$; thus (99.6) gives
$\langle q,z\rangle=c$. Independently
$\langle v,z\rangle=\int Jz\,dM=c$.
This calculation compares finite sums, not almost-everywhere
traces under two mutually different probability laws.

Along every infinite path,
$\sum_{j\ge1}2^{-j}=1$, so $Jq=\mathbf1$ and $q\in\ker\Sigma$.
The preceding equality shows that $v-q$ is orthogonal to the
entire kernel, proving the projection assertion.
The source cylinder formula gives, with $s=a^2+b^2=5-2\sqrt5$,

$$
\|v\|^2
 =\sum_{j\ge1}\sum_{|p|=j}m(p)^2
 =\sum_{j\ge1}s^j=\frac{s}{1-s}=\frac{\sqrt5}{2}.
\tag{99.7}
$$

Orthogonal decomposition now yields the stated norm of $w$.
The equal-split vector $q$ is also the classical unit-resistance
binary-tree flow: its outgoing values add to its incoming value
and its energy is one. The conditional trace calculation above establishes the projection
for this particular biased trace law independently of an electrical
boundary identification.
$\square$

## 100. The simultaneous source-size and screening crossover

**Definition 100.1 (the joint centered profile).**
For $0\le\tau<\infty$ set

$$
H(\tau)=\langle v,(I+\tau\Sigma)^{-1}v\rangle,
\qquad H(\infty)=1.
\tag{100.1}
$$

**Theorem 100.2 (every simultaneous sequence, including the unbounded
parameter).**
For every sequence $n\to\infty$, $\lambda_n>0$,
$\lambda_n\to0$ and $\tau_n=N_n\lambda_n\to\tau\in[0,\infty]$,

$$
R_{\lambda_n}(T_n)\longrightarrow H(\tau).
\tag{100.2}
$$

For every finite $T\ge0$, with the value at zero interpreted as
$R_0(T_n)=C_n$,

$$
\sup_{0\le t\le T}
 \left|R_{t/N_n}(T_n)-H(t)\right|\longrightarrow0.
\tag{100.3}
$$

The profile has the source-specific decomposition

$$
H(\tau)=1+\langle w,(I+\tau\Sigma)^{-1}w\rangle,\qquad
H(0)=\frac{\sqrt5}{2},\qquad
\lim_{\tau\to\infty}H(\tau)=1.
\tag{100.4}
$$

It is continuous, strictly decreasing, and $H(\tau)>1$ for every
finite $\tau\ge0$. The retained amount at zero joint parameter is
$\|w\|^2=\sqrt5/2-1$, and the nonconstant term in (100.4) is
strictly positive at every finite joint parameter.

**Proof.**
All the covariance operators are positive, so their resolvent
norms are at most one. For finite $t$, the resolvent identity gives

$$
\|(I+t\Sigma_n)^{-1}-(I+t\Sigma)^{-1}\|
 \le t\|\Sigma_n-\Sigma\|.
\tag{100.5}
$$

Together with (98.6), this proves uniform convergence on every
bounded $t$ interval. At $t=0$, (92.9) and (98.11) give
$C_n=\|v_n\|^2$, including the singletons. This proves (100.3)
and (100.2) when the joint parameter has a finite limit.

The orthogonal decomposition in Theorem 99.1 is invariant under
$\Sigma$, which vanishes on its kernel. It yields (100.4)'s
decomposition and its value at zero. Since $w\perp\ker\Sigma$,
$w$ is in the closure of the range of $\Sigma$:
the orthogonal complement of that range is exactly its kernel.
For a vector $\Sigma x$,

$$
\|(I+t\Sigma)^{-1}\Sigma x\|
 \le\frac{2}{t}\|x\|\quad(t>0),
\tag{100.6}
$$

by $t(I+t\Sigma)^{-1}\Sigma=I-(I+t\Sigma)^{-1}$.
Approximation by range vectors and the contraction bound prove
$(I+t\Sigma)^{-1}w\to0$. This establishes the endpoint of $H$.

For finite $t$ the inverse is positive definite and satisfies
$(I+t\Sigma)^{-1}\ge(1+t\|\Sigma\|)^{-1}I$.
Consequently the nonconstant term is positive because $w\ne0$.
Differentiating the bounded-operator inverse gives

$$
H'(t)=-\langle u_t,\Sigma u_t\rangle<0,\qquad
u_t=(I+t\Sigma)^{-1}w.
\tag{100.7}
$$

The inequality is strict: if its quadratic form vanished,
(98.13) would imply $u_t\in\ker\Sigma$, and then
$w=(I+t\Sigma)u_t=u_t$ would lie in that kernel, a contradiction.
This also gives continuity at finite parameters.

It remains to prove (100.2) for actual sequences
$\tau_n\to\infty$; (100.5) alone does not control them.
For any fixed $T>0$, monotonicity of the quadratic variational
supremum in (98.14), after subtracting $\tau_n^{-1}$, gives
eventually

$$
R_{\lambda_n}(T_n)
 \le\langle v_n,(I+T\Sigma_n)^{-1}v_n\rangle.
\tag{100.8}
$$

Its upper limit is at most $H(T)$, hence at most one after
$T\to\infty$.

For the lower bound fix a positive integer $d$ and use
$q^{[d]}=P_dq$ in that same variational supremum.
On every actual node $x$,

$$
(J_nq^{[d]})(x)=1-2^{-\min(|x|,d)},\qquad
\|q^{[d]}\|^2=1-2^{-d}.
\tag{100.9}
$$

All nodes of depth at least $d$ have the same displayed value;
this statement also respects terminals before depth $d$.
There are at most $2^d-1$ earlier nodes, each of mass $1/N_n$.
Using $1-2^{-d}$ as a comparison constant therefore gives

$$
\operatorname{Var}_{\mu_n}(J_nq^{[d]})
 \le\frac{2^d-1}{N_n},\qquad
\tau_n\operatorname{Var}_{\mu_n}(J_nq^{[d]})
 \le(2^d-1)\lambda_n\longrightarrow0.
\tag{100.10}
$$

Moreover (98.6) and the cylinder partition at each depth give

$$
\langle v_n,q^{[d]}\rangle
 \longrightarrow\sum_{j=1}^{d}2^{-j}\sum_{|p|=j}m(p)
 =1-2^{-d}.
\tag{100.11}
$$

The variational formula now yields
$\liminf_n R_{\lambda_n}(T_n)\ge1-2^{-d}$.
Letting $d\to\infty$ proves the lower bound one, completing
the unbounded-parameter sequence proof. The condition
$\lambda_n\to0$ was used in (100.10), separately from
$\tau_n\to\infty$. No endpoint rate or whole-spectrum
description is asserted. $\square$

## 101. The inherited capacity profile

**Definition 101.1 (uncentered response and capacity).**
For $0<\tau<\infty$ define

$$
U(\tau)=\frac1\tau+H(\tau),\qquad
Y(\tau)=\frac1{U(\tau)}
       =\frac{\tau}{1+\tau H(\tau)}.
\tag{101.1}
$$

Use the extended endpoints
$U(0)=+\infty$, $Y(0)=0$, $U(\infty)=Y(\infty)=1$.
On a finite original source write
$Y_n(\lambda)=G_\lambda(T_n)^{-1}$.

**Theorem 101.2 (capacity endpoints and the source-inherited
branch relation).**
Under the sequence hypotheses of Theorem 100.2,

$$
G_{\lambda_n}(T_n)\longrightarrow U(\tau),\qquad
Y_n(\lambda_n)\longrightarrow Y(\tau),
\tag{101.2}
$$

with the first limit extended-valued when $\tau=0$.
For every $0\le\tau\le\infty$,

$$
Y(\tau)=\frac{Y(a\tau)}{1+Y(a\tau)}
       +\frac{Y(b\tau)}{1+Y(b\tau)},
\tag{101.3}
$$

where $a\infty=b\infty=\infty$.
For finite $\tau$ it also has the boundary variational expression

$$
Y(\tau)=
 \inf_{z\in\mathscr H}
 \left\{\|z\|^2+\tau\|\mathbf1-Jz\|_{L^2(M)}^2\right\}.
\tag{101.4}
$$

In particular $H(0)=\sqrt5/2$ is a centered finite part, whereas
the uncentered endpoint is $+\infty$ and its capacity is zero.
For $0<\tau<\infty$, $0<Y(\tau)<1$.

**Proof.**
The exact decomposition (92.2), followed by Theorem 100.2, gives
(101.2) at positive finite and infinite parameters. At zero,
$\tau_n^{-1}\to+\infty$ and $R_{\lambda_n}\ge0$, proving the
extended uncentered limit and hence the zero capacity endpoint.

The finite root-pinned energy minimum equals reciprocal root
Green response by completing the same positive quadratic form
with the constraint $f(r)=1$. Writing $f=\mathbf1-J_nz$ gives

$$
Y_n(\lambda)
 =\inf_z\{\|z\|^2+N_n\lambda\|\mathbf1-J_nz\|_{L^2(\mu_n)}^2\}.
\tag{101.5}
$$

For $\lambda=\tau/N_n$, completion of the square makes this
$\tau-\tau^2\langle v_n,(I+\tau B_n)^{-1}v_n\rangle$.
By (98.6), it converges to
$\tau-\tau^2\langle v,(I+\tau B)^{-1}v\rangle$,
the infimum in (101.4); (101.2) identifies it with $Y(\tau)$.
At $\tau=0$ both the infimum and $Y(0)$ are zero.
For positive finite $\tau$ it is positive by (101.1).
Testing (101.4) with $z=tq$ gives
$t^2+\tau(1-t)^2$, whose minimum is $\tau/(1+\tau)<1$.
This proves the strict upper bound without imposing a new
boundary law on the finite matrices.

The finite Schur complement (93.3) says exactly

$$
Y_n(\lambda)=\lambda+
 \frac{Y_{n-1}(\lambda)}{1+Y_{n-1}(\lambda)}
 +\frac{Y_{n-2}(\lambda)}{1+Y_{n-2}(\lambda)}
 \quad(n\ge2),\qquad Y_0(\lambda)=Y_1(\lambda)=\lambda.
\tag{101.6}
$$

Fix $0<\tau<\infty$ and take $\lambda_n=\tau/N_n$.
The two child joint parameters tend to $a\tau$ and $b\tau$,
since $N_{n-1}/N_n\to a$ and $N_{n-2}/N_n\to b$.
Theorem 100.2 and (101.2) apply to each child sequence.
Letting $n\to\infty$ in (101.6) proves (101.3).
At zero the relation is $0=0+0$; at infinity it is
$1=1/2+1/2$, using the separately proved endpoint limits.
Thus the relation is inherited from the actual finite source
after convergence; no uniqueness assertion for its solutions
is needed. $\square$

## 102. Joint screening distinguishes originals with the same local reply

**Assumption 102.1 (the supplied data for response estimation).**
Fix $h\ge0$. An original source is promised to be some $T_n$,
and the supplied data are precisely $p_h(T_n)$ of (95.2) and
a declared positive screening parameter $\lambda$.
No source index, node count or observation of a prepared
comparison family is additionally supplied.
An estimator may be any family of real-valued functions
$E_{h,\lambda}$ on the Fibonacci prefix image.
Separate input instances have separate immutable originals;
they are not substitutions within one execution.

**Theorem 102.2 (a finite-parameter separation and a uniform
vanishing-screening obstruction on the promised family).**
For every fixed $h\ge0$, $\tau>0$ and integer $k\ge1$,
put $\lambda_j=\tau/N_j$. For all sufficiently large $j$,

$$
p_h(T_j)=p_h(T_{j+k}),\qquad
R_{\lambda_j}(T_j)-R_{\lambda_j}(T_{j+k})
 \longrightarrow H(\tau)-H(\varphi^k\tau)>0.
\tag{102.1}
$$

Thus even at a common declared $\lambda_j$, the identical local
table misses a nonzero difference of the global response.
More strongly, every estimator family of Assumption 102.1 obeys

$$
\limsup_{\lambda\downarrow0}
 \sup_{n\ge0}
 \left|E_{h,\lambda}(p_h(T_n))-R_\lambda(T_n)\right|
 \ge\frac12\left(\frac{\sqrt5}{2}-1\right).
\tag{102.2}
$$

The bound holds for every fixed $h$; it is compatible with
Theorem 97.2's exact identification when $n\le2h+1$,
its uniform approximation to $C_n$ as $h\to\infty$, and its
uniform approximation to $R_\lambda(T_n)$ as $h\to\infty$
for each fixed $\lambda>0$.

**Proof.**
For $j\ge2h+2$, both local tables consist entirely of branches,
by Theorem 97.2. From (92.12),
$N_{j+k}/N_j\to\varphi^k$.
The common $\lambda_j$ tends to zero, with joint parameters
$\tau$ and $\varphi^k\tau$ on the two original sources.
Theorem 100.2 and strict decrease of $H$ prove (102.1).
The estimator has the same real value on the two data sets,
so at least one of its absolute errors is at least half their
response difference.

For the full bound use instead the actual original pair
$T_j,T_{2j}$ and the common declared parameter

$$
\lambda_j=(N_jN_{2j})^{-1/2},\qquad
N_j\lambda_j=\sqrt{N_j/N_{2j}}\longrightarrow0,\qquad
N_{2j}\lambda_j=\sqrt{N_{2j}/N_j}\longrightarrow\infty.
\tag{102.3}
$$

Binet's formula proves both ratio limits and $\lambda_j\to0$.
Theorem 100.2 gives response limits $\sqrt5/2$ and one.
Their tables agree eventually at every fixed $h$.
Writing $e_j$ for the estimator's common value, the triangle
inequality gives

$$
\max\{|e_j-R_{\lambda_j}(T_j)|,\,
       |e_j-R_{\lambda_j}(T_{2j})|\}
 \ge\frac12|R_{\lambda_j}(T_j)-R_{\lambda_j}(T_{2j})|.
\tag{102.4}
$$

Taking the lower limit along this sequence yields (102.2).
The counts used to specify the mathematical counterexample
parameter in (102.3) are not data available to the estimator.

The retained vector $w$ in (100.4), determined by the limiting
all-node cylinder masses, supplies the positive finite-parameter
difference in (102.1). It records a global source contribution
left after removal of the constant trace; it is not obtained by
postprocessing the common fixed-depth table.
Neither (102.1) nor (102.2) changes the Fibonacci domain promise
or the quantifiers in (97.2) and (97.4): a fixed positive
$\lambda$ and a common range including $\lambda\downarrow0$
are different approximation problems. $\square$

**Assumption 102.3 (an additional same-source propagation realization).**
To interpret the comparison carrier as spatial or native
propagation, assume for each original $t$ the additional maps,
measure and edge-law compatibility, operator and boundary
correspondence, permitted source actions and lawful clock of
Assumption 97.3, all on that same immutable original.
A physically installed screening law and any source acquisition
cost must also have their own specified realization and bounds.
A scalar declared $\lambda$ by itself supplies none of those
maps, actions, clocks, costs or sensors.

Theorems 98.2–102.2 assume only the closed unit-edge counting
operator on occurrences and the stated input promises.
Their boundary is an addressed $L^2(M)$ trace of that comparison
carrier. They do not furnish a correspondence with complete
successive source states or observation quotients, a spatial
metric or dimension, a native transport law, a lawful acquired
clock, physical screening installation, or a reconstruction of
the entire spectrum. The existence and admissibility of a
realization satisfying this assumption remain unresolved
additional mathematical obligations.

## 102.99 追加锚（本行以下为增补区）

## 103. Complete finite occurrence states on the common edge carrier

**Definition 103.1 (the finite gradient transport).**
Retain exactly the ordered sources, all occurrences, counts and closed
unit-edge counting operators of Definitions 92.1–92.2. Let
$\mathcal V_n=\ell^2(V_{T_n})$ with counting inner product, let
$\mathscr E_n\subset\mathscr H$ consist of the actual edge coordinates,
and write $Q_n$ for the orthogonal projection onto $\mathscr E_n$.
Orient every edge away from the root and put

$$
(D_nf)_p=f(p)-f(p^-),\qquad L_n=D_n^*D_n,
\qquad K_n=D_nD_n^*\big|_{\mathscr E_n}.
\tag{103.1}
$$

Let $P_n=I-N_n^{-1}\mathbf1\otimes\mathbf1$ on $\mathcal V_n$,
$e_{n,0}=N_n^{-1/2}\mathbf1$, and $g_n=P_n\delta_r$. Define

$$
U_n=-D_nL_n^{+1/2}:P_n\mathcal V_n\longrightarrow\mathscr E_n,
\tag{103.2}
$$

where $L_n^{+1/2}$ is the positive square root of its pseudoinverse.
Extend $U_n$ by zero on constants and its adjoint by zero on
$\mathscr E_n^\perp$. Inverses of $\Sigma_n$ below mean inverses
on $\mathscr E_n$, extended by zero elsewhere. For $n=0,1$ these
are the unique maps on the zero-dimensional edge space.

**Theorem 103.2 (the complete finite operator and root weights).**
For $n\ge2$, $U_n$ is unitary between the displayed mean-zero node
and actual edge spaces, and

$$
\Sigma_n\big|_{\mathscr E_n}=\frac1{N_n}K_n^{-1},\qquad
U_nL_nU_n^*=K_n=\frac1{N_n}\Sigma_n^{-1}.
\tag{103.3}
$$

Every positive eigenvalue $x$ of $\Sigma_n$ corresponds to the
positive eigenvalue $(N_nx)^{-1}$ of $L_n$ with the same entire
eigenspace dimension. The complete state correspondence is

$$
f=c e_{n,0}+U_n^*z
\longleftrightarrow(c,z)\in\mathbb R\oplus\mathscr E_n,
\qquad L_n\longleftrightarrow0\oplus K_n.
\tag{103.4}
$$

Let $E_{n,\lambda}$ be the full projection onto the $\lambda$-eigenspace
of $L_n$, $d_{n,\lambda}=\operatorname{rank}E_{n,\lambda}$, and
$\rho_{n,\lambda}=\|E_{n,\lambda}\delta_r\|^2$. For every $t\ge0$
and every $f\in\mathcal V_n$,

$$
\begin{aligned}
e^{-tL_n}f
 &=\langle e_{n,0},f\rangle e_{n,0}
   +\sum_{\lambda>0}e^{-t\lambda}E_{n,\lambda}f,\\
(e^{-tL_n}f)(r)
 &=\frac1{N_n}\sum_xf(x)
   +\sum_{\lambda>0}e^{-t\lambda}
       \langle E_{n,\lambda}\delta_r,f\rangle,\\
p_n(t):=\langle\delta_r,e^{-tL_n}\delta_r\rangle
 &=\frac1{N_n}+\sum_{\lambda>0}\rho_{n,\lambda}e^{-t\lambda}.
\end{aligned}
\tag{103.5}
$$

The root-invisible subspace in the $\lambda$-eigenspace has dimension
$d_{n,\lambda}-\mathbf1_{\{\rho_{n,\lambda}>0\}}$. These directions
remain in the full operator, including when absent from the scalar
root spectral measure. For $n=0,1$, $L_n=0$, $p_n(t)=1$ and all
positive sums are empty; the labels remain respectively alpha and beta.

**Proof.**
Connectedness gives $\ker L_n=\mathbb R\mathbf1$. On actual edges
$D_nJ_nz=z$. With counting inner products on both spaces, set
$C_n^{\rm path}=P_nJ_n:\mathscr E_n\to P_n\mathcal V_n$.
Subtracting a constant changes no gradient, and
$P_nJ_nD_nu=u$ for mean-zero $u$. Thus $C_n^{\rm path}=D_n^{-1}$
between spaces of dimension $N_n-1$, and

$$
(C_n^{\rm path})^*C_n^{\rm path}
=K_n^{-1}=N_n\Sigma_n\big|_{\mathscr E_n}.
\tag{103.6}
$$

The last factor comes from the node inner product in §98 being
$N_n^{-1}$ times the counting inner product.
Also $U_n^*U_n=L_n^{+1/2}L_nL_n^{+1/2}=P_n$.
Equal dimensions give unitarity; $D_nL_n=K_nD_n$ gives (103.3).
Finite spectral calculus gives (103.4)–(103.5).
On one eigenspace the root functional has rank one precisely when
$E_{n,\lambda}\delta_r\ne0$, proving its invisible dimension.

Spectral and polar calculus are mature intermediate supplies; see
[Teschl, *Mathematical Methods in Quantum Mechanics*, §3.1,
Theorem 3.7 and Problem 3.11, and §6.2, Theorem 6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The scalar-versus-complete-spectrum distinction is retained in
[the boundary geometry, §52.4](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md).
Equation (103.6) connects those supplies to the closed counting
operator and source covariance of §98. $\square$

**Theorem 103.3 (relaxation scale and all transported positive states).**
Let $\mathscr K=(\ker\Sigma)^\perp$. For $s>0$ put
$F_s(x)=e^{-s/x}$ for $x>0$, $F_s(0)=0$, and
$\mathcal T(s)=F_s(\Sigma)$. Then, as operators on $\mathscr H$,

$$
\mathcal T_n(s):=U_ne^{-N_nsL_n}U_n^*
=F_s(\Sigma_n)\longrightarrow\mathcal T(s)
\quad\text{in operator norm}.
\tag{103.7}
$$

Convergence is uniform on compact subintervals of $(0,\infty)$.
If $c_n\to c$ and $z_n\in\mathscr E_n$ converge in $\mathscr H$ to $z$,
the complete states initialized at $c_ne_{n,0}+U_n^*z_n$ have
transported states at scaled time $s>0$ converging to
$(c,\mathcal T(s)z)$ in $\mathbb R\oplus\mathscr H$.
This includes arbitrary root-invisible modes.

For the smallest positive eigenvalue $\gamma_n$ of $L_n$,

$$
\gamma_n^{-1}=N_n\|\Sigma_n\|,\qquad
\frac{\gamma_n^{-1}}{N_n}\longrightarrow\|\Sigma\|>0.
\tag{103.8}
$$

The full comparison relaxation time is therefore asymptotic to a
positive constant times the actual source size.
On $\mathscr K$, $\mathcal T(s)=e^{-sA}$ is a strongly continuous
contraction semigroup, where $A=(\Sigma|_{\mathscr K})^{-1}$ is
positive self-adjoint on the dense domain
$\operatorname{ran}(\Sigma|_{\mathscr K})$; its generator is $-A$.
On the entire common space,

$$
\operatorname*{s-lim}_{s\downarrow0}\mathcal T(s)=P_{\mathscr K},
\qquad
\operatorname*{s-lim}_{n\to\infty}\mathcal T_n(0)
=\operatorname*{s-lim}_{n\to\infty}Q_n=I.
\tag{103.9}
$$

The two limits differ, since $q\ne0$ belongs to $\ker\Sigma$.
An identity-at-zero extension on all of $\mathscr H$ is false.

**Proof.**
Equation (103.3) gives the exact identity in (103.7).
By (98.6), choose $M_*>0$ bounding $\|\Sigma_n\|$ and $\|\Sigma\|$
for every $n$. For fixed $s>0$, $F_s$ is continuous on $[0,M_*]$;
polynomial approximation and covariance norm convergence prove
(103.7). Uniformity on $[\epsilon,S]$ follows from a finite parameter
net and $|\partial_sF_s(x)|\le(e\epsilon)^{-1}$.
Apply this operator limit to the convergent initial vectors.
Reciprocal extreme eigenvalues give (103.8).
The covariance is nonzero because the increment at $L$ has
variance $a(1-a)>0$.

Spectral calculus gives the inverse generator on $\mathscr K$.
Dominated convergence of its multipliers proves the first limit
in (103.9). Every fixed address is an actual edge for all sufficiently
large $n$ by (98.4), proving $Q_n\to I$ strongly.
Theorem 99.1 supplies the nonzero kernel vector $q$.
Changing node spaces have been transported only by the finite maps
specified in Definition 103.1. $\square$

**Corollary 103.4 (the root initial carrier and its positive-time state).**
Set

$$
\xi_n=\sqrt{N_n}\,U_ng_n=\Sigma_n^{-1/2}v_n,\qquad
h_n(s)=\sqrt{N_n}\,U_ne^{-N_nsL_n}g_n.
\tag{103.10}
$$

For $s>0$, define $f_s(x)=x^{-1/2}e^{-s/x}$ on $x>0$ and $f_s(0)=0$.
Then

$$
h_n(s)=f_s(\Sigma_n)v_n\longrightarrow
h(s)=f_s(\Sigma)v=f_s(\Sigma)w
\quad\text{in }\mathscr H,
\tag{103.11}
$$

and the exact root return obeys

$$
N_n[p_n(N_ns)-N_n^{-1}]=\|h_n(s/2)\|^2.
\tag{103.12}
$$

The root initial data are $g_n\in P_n\mathcal V_n$.
Their normalized transports satisfy $\|\xi_n\|^2=N_n-1\to\infty$,
so they have no vector limit in $\mathscr H$. The positive-time root
limit cannot be extended to zero by declaring an initial vector $v$
or by applying the identity to a limiting $\xi_n$.

**Proof.**
For $u=L_n^+\delta_r$, the flux calculation (92.9) gives $D_nu=-v_n$.
Since $U_n=-D_nL_n^{+1/2}$ and
$U_nL_n^{+1/2}=K_n^{-1/2}U_n$,
$K_n^{-1/2}U_ng_n=v_n$, giving (103.10) with its sign.
Continuity of $f_s$ on $[0,M_*]$ and (98.6) prove (103.11).
The semigroup identity and unitarity give
$\|h_n(s/2)\|^2=N_n\langle g_n,e^{-N_nsL_n}g_n\rangle$.
Finally $\|g_n\|^2=1-N_n^{-1}$. $\square$

## 104. Time measures, densities and simultaneous limits

**Definition 104.1 (scaled centered return and spectral mixtures).**
For $s\ge0$ define

$$
k_n(s)=N_n[p_n(N_ns)-N_n^{-1}],\qquad \nu_n(ds)=k_n(s)\,ds.
\tag{104.1}
$$

Let $\eta_n$ be the spectral measure of $\Sigma_n$ generated by $v_n$
and $\eta_w$ that of $\Sigma$ generated by $w$. Then
$\eta_n(\{0\})=0$, including the zero measure for the singletons.
By Theorem 99.1 the spectral measure generated by $v=q+w$ is
$\delta_0+\eta_w$, where $\eta_w(\{0\})=0$.
With the uniform spectral bound $M_*$ of Theorem 103.3, define

$$
k(s)=\int_{(0,M_*]}x^{-1}e^{-s/x}\,d\eta_w(x)\quad(s>0).
\tag{104.2}
$$

**Theorem 104.2 (the complete scaled time measure).**
The complete finite spectral projections of Theorem 103.2 give

$$
\begin{aligned}
k_n(s)
 &=\sum_{\lambda>0}N_n\rho_{n,\lambda}e^{-N_n\lambda s}
 =\int x^{-1}e^{-s/x}\,d\eta_n(x)\quad(s>0),\\
\nu_n([0,\infty))&=C_n=\|v_n\|^2,\\
\int_0^\infty e^{-\tau s}\,d\nu_n(s)
 &=R_{\tau/N_n}(T_n)\quad(\tau>0).
\end{aligned}
\tag{104.3}
$$

As finite Borel measures on $[0,\infty)$,

$$
\nu_n\Longrightarrow\nu:=\delta_0+k(s)\,ds.
\tag{104.4}
$$

The slow density is finite and strictly positive for every $s>0$, and

$$
\int_0^\infty k(s)\,ds=\frac{\sqrt5}{2}-1,\qquad
\nu(\{0\})=1,\qquad \nu([0,\infty))=\frac{\sqrt5}{2}.
\tag{104.5}
$$

No mass escapes to infinite scaled time. More precisely, for
$V_*=\sup_n\|v_n\|^2<\infty$,

$$
\nu_n([S,\infty))\le V_*e^{-S/M_*}\quad(S>0).
\tag{104.6}
$$

**Proof.**
Equations (103.5) and (103.10)–(103.12) give the first identity
in (104.3); integrate its nonnegative terms for the other identities.
For $n=0,1$ all centered terms vanish.
The heat interpretation uses exactly $-L_n$: off-diagonal
conductance rates are one on existing edges, diagonal rates are
minus the degree, and the stationary distribution is uniform.
This is the fluid model, not the degree-normalized continuization,
of [Aldous–Fill, *Reversible Markov Chains and Random Walks on Graphs*,
Chapter 3, §2, equation (3.16)](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch3.S2.html).
It provides mathematical comparison time, not a native clock.

For a bounded continuous function $\phi$ on $[0,\infty)$ put

$$
\Psi_\phi(x)=\int_0^\infty e^{-u}\phi(xu)\,du
\quad(0\le x\le M_*).
\tag{104.7}
$$

Dominated convergence makes $\Psi_\phi$ continuous, with
$\Psi_\phi(0)=\phi(0)$. Changing variables $s=xu$ in the positive
mixtures and using continuous functional calculus yields

$$
\begin{aligned}
\int\phi\,d\nu_n
 &=\langle v_n,\Psi_\phi(\Sigma_n)v_n\rangle\\
 &\longrightarrow\langle v,\Psi_\phi(\Sigma)v\rangle
 =\phi(0)+\int_0^\infty\phi(s)k(s)\,ds.
\end{aligned}
\tag{104.8}
$$

This proves weak convergence against all bounded continuous tests,
including the constant one. Tonelli gives
$\int k=\eta_w((0,M_*])=\|w\|^2$.
The bound $x^{-1}e^{-s/x}\le(es)^{-1}$ proves finiteness at positive
time; $w\ne0$ and $\eta_w(\{0\})=0$ prove strict positivity.
The mass-one atom comes precisely from $q$, by (99.2).
Finally integrating the mixtures over $[S,\infty)$ gives
$\int e^{-S/x}\,d\eta_n(x)\le\|v_n\|^2e^{-S/M_*}$,
proving the uniform no-escape bound. Spectral calculus and the
positive exponential-mixture construction are intermediate supplies
in this source-specific limit. $\square$

**Theorem 104.3 (density convergence and all three time regimes).**
For every $0<\epsilon<S<\infty$,

$$
\sup_{\epsilon\le s\le S}|k_n(s)-k(s)|\longrightarrow0.
\tag{104.9}
$$

For any sequence $s_n\ge0$ tending to a positive finite $s$,
$k_n(s_n)\to k(s)$. If $s_n\to\infty$, then $k_n(s_n)\to0$.
If $s_n\to0$, then $k_n(s_n)\to+\infty$, using the biased-source
endpoint of Theorem 105.1; this includes $k_n(0)=N_n-1$.
Weak measure convergence (104.4) and density convergence (104.9)
are different statements. There is no finite density at zero
representing the mass-one limiting atom.

**Proof.**
Put $G_s(x)=x^{-1}e^{-s/x}$ for $x>0$ and $G_s(0)=0$.
It is continuous on $[0,M_*]$, and
$k_n(s)=\langle v_n,G_s(\Sigma_n)v_n\rangle$.
A finite net and the bound
$|\partial_sG_s(x)|=x^{-2}e^{-s/x}\le4/(e^2\epsilon^2)$
give (104.9). Its limit is (104.2), since the kernel part contributes
zero. This also proves the positive finite sequence statement.
For unbounded times use $k_n(s)\le V_*/(es)$.
For zero times, $k_n$ is nonincreasing on $[0,\infty)$.
For every fixed $\epsilon>0$, eventually
$k_n(s_n)\ge k_n(\epsilon)$. Take the lower limit and then
$\epsilon\downarrow0$ in Theorem 105.1. This proves divergence
without asserting an endpoint rate. $\square$

**Corollary 104.4 (screening parameters remain distinct from times).**
If $\tau_n\ge0$, $\tau_n/N_n\to0$ and
$\tau_n\to\tau\in[0,\infty]$, then

$$
\int e^{-\tau_ns}\,d\nu_n(s)\longrightarrow
\begin{cases}
\sqrt5/2,&\tau=0,\\
H(\tau),&0<\tau<\infty,\\
1,&\tau=\infty.
\end{cases}
\tag{104.10}
$$

Here $\tau_n$ is a Laplace parameter, not the time $s_n$
of Theorem 104.3. The finite-source value at zero is $C_n$.

**Proof.**
For positive $\tau_n$ use (104.3) and Theorem 100.2 with
$\lambda_n=\tau_n/N_n$. At zero or on zero subsequences use
(92.5) and the uniform bounded-parameter assertion (100.3).
The simultaneous condition $\tau_n/N_n\to0$ is retained at the
unbounded Laplace endpoint; it is not needed for the density
statements. $\square$

## 105. The biased source forces an infinite slow-density endpoint

**Theorem 105.1 (the integrable singularity for the actual source law).**
For precisely $m(p)=a^{\#_L(p)}b^{\#_R(p)}$ with
$a=\varphi^{-1}$ and $b=\varphi^{-2}$, the density (104.2) satisfies

$$
\lim_{s\downarrow0}k(s)=+\infty,\qquad
\int_0^\infty k(s)\,ds=\frac{\sqrt5}{2}-1<\infty.
\tag{105.1}
$$

The endpoint conclusion imposes no power law or exponent and does
not identify a spatial or spectral dimension.

**Proof.**
Monotone convergence gives

$$
\lim_{s\downarrow0}k(s)=\int_{(0,M_*]}x^{-1}\,d\eta_w(x).
\tag{105.2}
$$

Let $A=(I-\mathbf1\otimes\mathbf1)J:\mathscr H\to L^2_0(M)$,
so $A^*A=\Sigma$. If (105.2) were finite, spectral calculus would
define $z=\Sigma^{-1/2}w\in\mathscr K$.
In the polar decomposition $A=V\Sigma^{1/2}$, set $h=Vz$.
Then $h\in L^2_0(M)$ and
$A^*h=\Sigma^{1/2}V^*Vz=w$.
Since $h$ has mean zero, $A^*h=J^*h$.
On each nonempty cylinder the adjoint relation and (99.1) give

$$
\int_{[p]}h\,dM=m(p)-2^{-|p|},\qquad
\mathbb E_M[h\mid[p]]=1-\frac{2^{-|p|}}{m(p)}.
\tag{105.3}
$$

For the depth-$d$ cylinder partition $\mathcal F_d$, conditional
expectation is an $L^2(M)$ contraction, but (105.3) would imply

$$
\begin{aligned}
\|\mathbb E_M[h\mid\mathcal F_d]\|_2^2
 &=\sum_{|p|=d}m(p)
       \left(1-\frac{2^{-d}}{m(p)}\right)^2\\
 &=4^{-d}\sum_{|p|=d}\frac1{m(p)}-1
 =\left(\frac1{4a}+\frac1{4b}\right)^d-1
 =\left(\frac1{4ab}\right)^d-1.
\end{aligned}
\tag{105.4}
$$

Because $a+b=1$ and $a\ne b$, $ab<1/4$, so this expression
diverges. It cannot be bounded by the fixed $\|h\|_2^2$.
This contradiction proves the infinite endpoint.
Integrability was proved separately in (104.5). In particular,
$\|h(s)\|^2=k(2s)\to\infty$ as $s\downarrow0$, by (103.11)
and (104.2), so the limiting root orbit itself has no strong
initial vector in $\mathscr H$.
The polar decomposition is the mature supply cited in Theorem 103.2;
the cylinder adjoint is the tree Hardy relation in
[Arcozzi et al., *Potential theory on trees, graphs and Ahlfors-regular
metric spaces*, §5.1, equation (41)](https://arxiv.org/html/1010.4788v3),
already instantiated in (98.11).
The divergence (105.4) uses the actual biased all-occurrence law.
Replacing it by the fair dyadic law changes its base to one and
removes this contradiction. $\square$

## 106. A comparison boundary-response consumer and its acquisition boundary

**Assumption 106.1 (forcing, centered readout and initial data).**
Let $f\in C_c([0,\infty))$ be a supplied scalar forcing.
On the declared scaled comparison clock initialize
$u_n(0)=0\in P_n\mathcal V_n$ and solve

$$
\frac{d}{dt}u_n(t)=-N_nL_nu_n(t)+N_nf(t)g_n,\qquad
y_n(t)=\langle g_n,u_n(t)\rangle=u_n(t)(r).
\tag{106.1}
$$

The input is the centered comparison root port $g_n$ and the
output its conjugate root readout. This specifies a mathematical
input-output experiment on the retained occurrence operator.
A native actuator, physical positions or physical clock require
the additional realization of Assumptions 97.3 and 102.3.
No such realization is assumed.

**Theorem 106.2 (the zero-initial limiting boundary response).**
Under Assumption 106.1, for every $t\ge0$,

$$
y_n(t)=\int_0^t k_n(s)f(t-s)\,ds.
\tag{106.2}
$$

At every fixed $t>0$,

$$
y_n(t)\longrightarrow y(t)
=f(t)+\int_0^t k(s)f(t-s)\,ds.
\tag{106.3}
$$

If $f(0)=0$, define $y(0)=0$; convergence is then uniform on
every compact interval $[0,T]$. In general convergence is uniform
on each $[\epsilon,T]\subset(0,\infty)$ and $y(0+)=f(0)$.
A continuous zero initial readout is compatible with the limiting
contract exactly when $f(0)=0$.
If $f(0)\ne0$, the limiting response has initial feedthrough $f(0)$,
while every finite zero-initial response has $y_n(0)=0$.
A nonzero prescribed initial state requires a separately retained
homogeneous root term.

**Proof.**
Variation of constants gives
$u_n(t)=N_n\int_0^te^{-N_nsL_n}g_nf(t-s)\,ds$.
Taking the readout and using (103.12) proves (106.2).
For fixed $t>0$, the bounded test
$\phi_t(s)=f(t-s)\mathbf1_{[0,t]}(s)$ has at most a discontinuity
at $s=t$, where $\nu$ has no atom.
Weak convergence (104.4) gives (106.3), with $f(t)$ supplied by
the mass-one atom at zero.

When $f(0)=0$, extend $f$ by zero to negative times.
The tests $s\mapsto f(t-s)$ for $t\in[0,T]$ form a uniformly
bounded equicontinuous family supported in $[0,T]$.
A finite time net, weak convergence and bounded measure masses
give uniform convergence of their integrals.
Otherwise split $f(u)=f(0)+(f(u)-f(0))$ on $[0,T]$.
The second part satisfies the preceding argument.
For the first use convergence of the distribution functions
$\nu_n([0,t])$ to $\nu([0,t])$ on $[\epsilon,T]$:
monotonicity and continuity of the limiting distribution there
give uniform convergence by a finite partition.
The slow convolution tends to zero as $t\downarrow0$ by
integrability of $k$, while $f(t)\to f(0)$.
A nonzero initial state adds
$\langle g_n,e^{-N_ntL_n}u_n(0)\rangle$ to (106.2);
the zero-initial assumption is precisely what omits it. $\square$

**Assumption 106.3 (original-reply acquisition and distinct times).**
When a native execution supplies an original reply or exact index
to this consumer, retain the existing authenticated stationary epoch,
original-presence guard, chronological original-address reads and
absorbing Stop conditions of Assumption 97.1 and
[Continuation III, Assumption 91.6](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md).
The existing guarded original-reply/index suppliers are used only
under their own original-source, guard and resource contracts:
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean),
[Atomic Boundary Trichotomy, §§12–17](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md),
[Acquired Intrinsic Depth Calibration, §6](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md)
and [Finite Frame Memory](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_FRAME_MEMORY.md),
together with
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean).
Actual address length, distinct-address fees, retained full control
memory, installed data, preparation, arithmetic and output remain
separate resources. Defining (104.1) grants no observation of $N_n$.

Comparison time in (106.1), source-substitution epoch, acquisition
chronology and physical time remain distinct.
Neither a duplicate search or decoder, a pointer walk nor an added
Poisson clock supplies a native occurrence-transport correspondence.
An optional acquired-query sampling law is an additional unverified
premise. The native occurrence actuator and physical-time realization
remain outside Assumption 106.1.

## 106.99 追加锚（本行以下为增补区）

## 107. Root readout, action closure and future memory

The preceding sections distinguish the complete finite occurrence state from
the scalar root response. This section makes the corresponding memory
boundary explicit. It is an ordinary finite-dimensional linear result. The
actions below are an abstract contract; they are not claimed to be native
original-root queries unless a separate realization supplies them.

**Definition 107.1 (multi-port future response).**
Let $V$ be a finite-dimensional real vector space, let
$A:V\to V$ be a linear evolution, let ${C_\ell:V\to Y_\ell\}_{\ell\in L}$ be
a finite family of linear readout ports, and let ${T_a:V\to V\}_{a\in A_0}$
be a finite family of admissible interventions. For a word
$w=a_1\cdots a_m$ put

$$
T_w=T_{a_m}\cdots T_{a_1},
\qquad T_\varepsilon=I.
$$

The unacted hidden subspace and the action-closed hidden subspace are

$$
\begin{aligned}
K_{\mathrm{stat}}
  &=\bigcap_{\ell\in L}\bigcap_{j\ge0}
      \ker(C_\ell A^j),\\
K_{\mathrm{fut}}
  &=\bigcap_{w\in A_0^*}\bigcap_{\ell\in L}\bigcap_{j\ge0}
      \ker(C_\ell A^jT_w).
\end{aligned}
\tag{107.1}
$$

The first space contains perturbations invisible to every declared port under
the passive evolution. The second contains perturbations invisible after every
finite intervention word as well.

**Theorem 107.2 (the maximal action-closed hidden subspace).**

The subspace $K_{\mathrm{fut}}$ satisfies

$$
K_{\mathrm{fut}}\subseteq K_{\mathrm{stat}},
\qquad
T_aK_{\mathrm{fut}}\subseteq K_{\mathrm{fut}}
\quad(a\in A_0).
\tag{107.2}
$$

Moreover, if $M\subseteq K_{\mathrm{stat}}$ is a linear subspace with

$$
T_aM\subseteq M\quad(a\in A_0),
\tag{107.3}
$$

then $M\subseteq K_{\mathrm{fut}}$. Consequently $K_{\mathrm{fut}}$ is the
largest subspace that is both passively invisible and closed under every
declared intervention.

### Proof

The empty word belongs to $A_0^*$, so the second intersection is contained
in the first. If $x\in K_{\mathrm{fut}}$, $a\in A_0$, and
$w\in A_0^*$, then

$$
C_\ell A^jT_w(T_ax)=C_\ell A^jT_{aw}x=0,
$$

where $aw$ denotes the word obtained by prefixing $a$, so
$T_{aw}=T_wT_a$. Hence $T_ax$ lies in
every factor of the second intersection, proving invariance.

Now let $x\in M$. By (107.3), $T_wx\in M$ for every word $w$. Since
$M\subseteq K_{\mathrm{stat}}$, each vector $T_wx$ is killed by every
$C_\ell A^j$. Thus $x$ belongs to every factor in the definition of
$K_{\mathrm{fut}}$. The maximality statement follows. $\square$

**Corollary 107.3 (when the static quotient is already safe).**

The following are equivalent:

$$
K_{\mathrm{fut}}=K_{\mathrm{stat}},
$$

and

$$
T_aK_{\mathrm{stat}}\subseteq K_{\mathrm{stat}}
\quad\text{for every }a\in A_0.
\tag{107.4}
$$

### Proof

If the spaces are equal, (107.2) gives invariance of $K_{\mathrm{stat}}$.
Conversely, if $K_{\mathrm{stat}}$ is invariant under every intervention,
it satisfies the hypotheses for $M$ in Theorem 107.2, so
$K_{\mathrm{stat}}\subseteq K_{\mathrm{fut}}$. The reverse inclusion was
already proved. $\square$

Thus a static observation quotient can be used as a future quotient exactly
when its hidden fiber is closed under all later actions. A current scalar
response does not acquire this property merely because it is exact for the
passive evolution.

**Proposition 107.4 (a two-dimensional leakage witness).**

Let $V=\mathbb R^2$,

$$
A=\begin{pmatrix}1&0\\0&2\end{pmatrix},
\qquad
C(x_1,x_2)=x_1,
\qquad
T(x_1,x_2)=(x_2,x_1).
\tag{107.5}
$$

Then

$$
K_{\mathrm{stat}}=\mathbb R(0,1),
\qquad
K_{\mathrm{fut}}=\{0\}.
\tag{107.6}
$$

In fact $q=(0,1)$ is invisible to every passive response,

$$
C e^{-tA}q=0\quad(t\ge0),
$$

but after one intervention it is visible:

$$
C e^{-tA}Tq=e^{-t}\ne0.
\tag{107.7}
$$

### Proof

For the passive evolution,
$C A^j(x_1,x_2)=x_1$ for every $j$, so its common kernel is
$\mathbb R(0,1)$. The swap sends $(0,1)$ to $(1,0)$, which the port sees;
therefore no nonzero vector in $K_{\mathrm{stat}}$ is action-closed. The
displayed exponential formulas give the same conclusion directly. $\square$

**Corollary 107.5 (the spectral boundary response is not by itself a
future memory state).**

For the occurrence carriers of §§103–106, the root scalar response and the
root spectral weights are passive-port data. The root-invisible directions in
Theorem 103.2 therefore belong to a static hidden fiber whenever they are
annihilated by that port. If a separately declared intervention or another
port acts nontrivially on such a direction, the correct memory quotient is
$K_{\mathrm{fut}}$, not $K_{\mathrm{stat}}$; the scalar quantity
$p_n(t)$, $R_\lambda(T_n)$, or their limiting analogues cannot serve as the
complete future state.

This is a statement about the declared linear comparison contract. It does
not install an actuator, identify an original-root query with $T_a$, or
provide a physical time, reset, or cost. A native FIB realization must still
prove that the proposed action and port are available on the same immutable
source and that their response-successor-cost kernel descends.

**Theorem 107.6 (finite-horizon stabilization of each fixed action family).**

Let $d=\dim V$. For every fixed intervention word $w$ and port $C_\ell$,

$$
\bigcap_{j\ge0}\ker(C_\ell A^jT_w)
=
\bigcap_{0\le j<d}\ker(C_\ell A^jT_w).
\tag{107.8}
$$

Consequently, the infinite time index in (107.1) is not the source of an
infinite-dimensional carrier; any non-finiteness of the exact future quotient
comes from the unbounded family of action words or from an unbounded source
family.

### Proof

By Cayley–Hamilton, every $A^j$ with $j\ge d$ is a linear combination of
$I,A,\ldots,A^{d-1}$. A vector annihilated by the first $d$ composed maps is
therefore annihilated by every later $C_\ell A^jT_w$. The reverse inclusion is
immediate. $\square$

The distinction is useful for the latest FIB boundary results. Under the
promised family $T_n$ and a fixed positive screening parameter, a finite prefix
can support a uniform approximation as in Theorem 97.2. Once the screening
parameter is allowed to scale toward zero with the source size, Theorem 102.2
shows that the same fixed-depth table can miss a nonzero response gap. The
obstruction is therefore a joint source–parameter boundary, not a failure of
the finite-dimensional spectral algebra.

## 107.99 追加锚（本行以下为增补区）

## 108. An all-source occupation clock for literal rho renewal

**Definition 108.1 (the closed successor and its old-set clock).**
Retain the free finite ordered sources, actual occurrence addresses and
closed unit-edge counting Laplacians of Definitions 92.1–92.2. For every
original $`t\in\mathcal T`$ and $`n\ge0`$, write

```math
s(t,n)=\rho^nt,\quad V(t,n)=V_{s(t,n)},\quad
N(t,n)=|V(t,n)|,\quad L(t,n)=L_{s(t,n)},\quad
r(t,n)=\frac{N(t,n+1)}{N(t,n)}.
\tag{108.1}
```

The old vertices keep their addresses. Exactly two new degree-one children
are attached to each actual old beta leaf; no other vertex or edge is born.
Let $`X_b`$ be the continuous-time comparison chain on $`V(t,n+1)`$ with
generator $`-L(t,n+1)`$, initially at any old vertex $`x\in V(t,n)`$. Its
rates are one on existing edges, rather than a degree-normalized walk.
Define old-set occupation time and its right-continuous inverse by

```math
B(b)=\int_0^b\mathbf1_{V(t,n)}(X_v)\,dv,\qquad
A(t,n)(a)=\inf\{b\ge0:B(b)>a\},\qquad
Y_a=X_{A(t,n)(a)}.
\tag{108.2}
```

The infimum equals $`\sup\{b:B(b)\le a\}`$. Finite recurrence gives
$`B(b)\to\infty`$ almost surely, so this inverse is finite at every finite
$`a`$. At a plateau value it selects the return endpoint of the entire
new-child excursion. At zero it equals zero almost surely because the
initial old holding time is strictly positive. The trace $`Y`$ has generator
$`-L(t,n)`$; the singleton trace is the constant chain. All these laws are
conditional mathematical comparisons on the specified finite sources.
The variable $`a`$ is old-set trace time, and $`b`$ is successor comparison
time. Neither is a duration assigned to a native substitution.

**Theorem 108.2 (uniform source-size clock fidelity and the uniform golden ratio).**
Put $`\varphi=(1+\sqrt5)/2`$, $`c=\varphi^{-1}`$ and
$`D_n=2F_{n+1}-1`$. Then

```math
\sup_{t\in\mathcal T}|r(t,n)-\varphi|
\le e_n:=\frac{c+2c^{n+1}}{D_n}\longrightarrow0.
\tag{108.3}
```

For every finite $`S\ge0`$ and every $`\varepsilon>0`$,

```math
\lim_{n\to\infty}\sup_{t\in\mathcal T}\sup_{x\in V(t,n)}
\mathbb P_x\!\left\{
\sup_{0\le u\le S}\left|
\frac{A(t,n)(N(t,n)u)}{N(t,n)}-r(t,n)u
\right|>\varepsilon\right\}=0.
\tag{108.4}
```

The same conclusion holds for every initial probability on the old set,
including probabilities depending on $`t,n`$. More explicitly, for $`n\ge2`$
and $`\eta>0`$, set

```math
d_n(S)=\frac{c+4(n+1)}{D_n}+2Sc^{n+1}+Se_n,
\qquad m_n=\lfloor n/2\rfloor.
\tag{108.5}
```

The probability in (108.4), with threshold $`d_n(S)+2\eta`$, is at most

```math
\frac{128S}{\eta^2D_n}
+\frac{c}{\eta}\left(\frac1{D_n}+S2^{-m_n}\right).
\tag{108.6}
```

Replacing the inverse in (108.2) by $`\inf\{b:B(b)\ge a\}`$, with value
zero at zero, preserves (108.4). The two conventions differ only by
complete excursion lengths at their corresponding plateau values.

**Proof.**
The literal birth identity is the same source identity used in
[Continuation I, §58.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).
Its grounded Hamiltonian and missing-child diagonals are not used here.
In the present closed operator, if $`\mathcal B`$ is the old beta-leaf set,
$`H_{\mathcal B}`$ its coordinate projection and $`C`$ has one column
$`\delta_p`$ for each of the two children born at each $`p\in\mathcal B`$,
the actual old/new blocks are

```math
L(t,n+1)=
\begin{pmatrix}L(t,n)+2H_{\mathcal B}&-C\\-C^*&I\end{pmatrix},
\qquad CC^*=2H_{\mathcal B}.
\tag{108.7}
```

The zero-parameter Schur complement is exactly $`L(t,n)`$. Equivalently,
every deleted excursion returns to its very own beta parent, so deletion
adds no old-to-old transition. This is the standard reversible trace
construction: Beltrán–Landim,
[*Tunneling and Metastability of Continuous Time Markov Chains*,
§6.1, Propositions 6.1 and 6.3](https://arxiv.org/abs/0910.4088).
Their nonempty-support, irreducibility and recurrence hypotheses hold
on each finite successor, with time-change weight $`\mathbf1_{V(t,n)}`$.
The inverse convention is theirs. A singleton old set has no off-diagonal
trace rate and is included directly. Counting measure on the successor
restricts to counting measure on the trace. The use of conductance rates
with counting mass is also precisely the fluid model in
[Aldous–Fill, Chapter 3, §2, (3.16)](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch3.S2.html).

In trace time, each beta parent has two excursion clocks of rate one.
Their independent marks $`E_i`$ are the new-child holding times, each with
law $`\operatorname{Exp}(1)`$, mean one and second moment two. Old-edge
clocks and the excursion clocks can be constructed independently while
the chain is at each old vertex. Consequently, with $`\theta_i`$ the
excursion times on the trace clock,

```math
\begin{aligned}
A(t,n)(a)&=a+\sum_{\theta_i\le a}E_i,\\ {}
M^{\rm exc}_a
&=\sum_{\theta_i\le a}E_i
  -\int_0^a2\mathbf1_{\mathcal B}(Y_v)\,dv,\\ {}
\langle M^{\rm exc}\rangle_a
&=\int_0^a4\mathbf1_{\mathcal B}(Y_v)\,dv\le4a.
\end{aligned}
\tag{108.8}
```

The formula includes the entire terminal excursion when $`a`$ is a
plateau value. It is a marked-clock representation of this exact
successor chain, not an additional law imposed on a source action.

It remains to control the beta occupation uniformly without assuming
uniform mixing of arbitrary source skeletons. Let $`a_0,b_0`$ be the
numbers of original alpha and beta leaves and $`\ell=a_0+b_0\ge1`$.
The original skeleton has $`\ell-1`$ internal vertices. Each original alpha
leaf carries its literal $`T_n`$ block after expansion, and each original
beta leaf its literal $`T_{n+1}`$ block. The source recurrence of
Definition 92.2 therefore gives

```math
\begin{aligned}
N:=N(t,n)&=2(a_0F_{n+1}+b_0F_{n+2})-1\ge D_n\ell,\\ {}
|\mathcal B|&=a_0F_n+b_0F_{n+1}.
\end{aligned}
\tag{108.9}
```

These formulas include $`n=0`$ and both singleton labels. On $`T_k`$, set
$`f_k=2\mathbf1_{\{\text{beta leaf}\}}-c`$. Its total charge is

```math
q_k:=\sum_{T_k}f_k
=2F_k-c(2F_{k+1}-1)
=c-2c(-c)^k=:c+\delta_k,
\qquad |q_k|\le2,\quad |\delta_k|=2c^{k+1}.
\tag{108.10}
```

The last equality is the exact Fibonacci identity
$`F_k-cF_{k+1}=-c(-c)^k`$, obtained from (92.12).
Summing $`f=2\mathbf1_{\mathcal B}-c`$ on the whole old source, including
its internal original skeleton, yields

```math
\sum_{V(t,n)}f=c+a_0\delta_n+b_0\delta_{n+1},\qquad
r(t,n)-\varphi=\frac{c+a_0\delta_n+b_0\delta_{n+1}}N.
\tag{108.11}
```

Equations (108.9)–(108.11) prove (108.3) for the whole source domain,
not only for the orbit $`T_n`$.

Construct a corrector $`h`$ on this same old tree. At each original
skeleton vertex $`p`$, including its original leaves, set $`h(p)=c|p|`$.
Within a block rooted at an original leaf, set its root value by this
rule and give each downward edge increment the total $`f`$-charge of
its actual below-edge subtree. That subtree is some $`T_k`$, so the
increment is exactly $`q_k`$ from (108.10). The elementary tree Poisson
flux calculation already used in (92.9) then gives, on a block rooted
at $`p`$, $`L_{\rm block}h=f-q_k\delta_p`$.
An original nonroot block root receives the additional parent-edge
contribution $`c`$; an original internal nonroot skeleton vertex has
$`Lh=-c=f`$; the original root, when internal, has $`Lh=-2c=f-c`$.
For a singleton original skeleton the block root has no parent edge.
Thus all cases give the single identity

```math
f=L(t,n)h+c\delta_r+e,\qquad
e=\sum_{p\text{ original alpha leaf}}\delta_n\delta_p
  +\sum_{p\text{ original beta leaf}}\delta_{n+1}\delta_p,
\quad \|e\|_\infty\le2c^{n+1}.
\tag{108.12}
```

Every edge increment of $`h`$ has modulus at most two. Every block has
height at most $`n+1`$, while the maximum original depth is at most
$`\ell-1`$. Therefore

```math
\frac{\operatorname{osc}h}{N}
\le\frac{c(\ell-1)+4(n+1)}N
\le\frac{c+4(n+1)}{D_n},\qquad
\sum_{y\sim x}|h(y)-h(x)|^2\le12.
\tag{108.13}
```

Large or highly unbalanced original skeletons are retained in these
bounds. Their depth is divided by their actual expanded size, rather
than bounded by the orbit depth.

For the trace generator $`Q=-L(t,n)`$, the finite-chain Dynkin martingale is

```math
M^h_a=h(Y_a)-h(x)+\int_0^a L(t,n)h(Y_v)\,dv,
\qquad \langle M^h\rangle_a\le12a.
\tag{108.14}
```

The bracket follows by summing rate times squared jump increment.
The usual $`L^2`$ maximal inequality gives
$`\mathbb E_x\sup_{v\le a}|M^h_v|^2\le48a`$ and, from (108.8),
$`\mathbb E_x\sup_{v\le a}|M^{\rm exc}_v|^2\le16a`$.
For reference, the discrete-time inequality is Durrett,
[*Probability: Theory and Examples*, fifth edition, Theorem 4.4.4](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf).
Apply it on successively finer deterministic time grids to these
square-integrable càdlàg martingales and use monotone convergence to
obtain the stated continuous-time bounds. No stationary initial law
is needed.

The root term in (108.12) also admits a source-uniform bound.
The minimum leaf depth of $`T_k`$ is $`\lfloor k/2\rfloor`$, directly by
the literal recursion. Every old source therefore contains the entire
binary tree through depth $`m=m_n`$. Put
$`b_m(p)=2^{-\min(|p|,m)}`$. At the actual root, internal vertices and
depth-$`m`$ vertices, respectively, direct application of the closed
Laplacian gives

```math
L(t,n)b_m=\delta_r-2^{-m}\mathbf1_{\{|p|=m\}}.
\tag{108.15}
```

Below depth $`m`$ it is zero. Since $`0\le b_m\le1`$, Dynkin's identity,
from every starting vertex, implies

```math
\mathbb E_x\int_0^{NS}\mathbf1_{\{r\}}(Y_v)\,dv
\le1+NS2^{-m}.
\tag{108.16}
```

Combine (108.8), (108.12) and (108.14), and use $`\varphi=1+c`$:

```math
\begin{aligned}
\sup_{0\le a\le NS}\frac{|A(t,n)(a)-\varphi a|}{N}
\le {}&\frac{\operatorname{osc}h}{N}+2Sc^{n+1}
 +\frac{\sup_{a\le NS}|M^h_a+M^{\rm exc}_a|}{N}\\ {}
&+\frac cN\int_0^{NS}\mathbf1_{\{r\}}(Y_v)\,dv.
\end{aligned}
\tag{108.17}
```

The two separate maximal bounds and $`|u+v|^2\le2|u|^2+2|v|^2`$
give expectation at most $`128NS`$ for the squared martingale supremum.
Chebyshev's inequality, (108.16), Markov's inequality and $`N\ge D_n`$
give (108.6), after adding $`S|r(t,n)-\varphi|\le Se_n`$.
Every displayed bound is independent of $`t,x`$. For $`S>0`$, choose
$`\eta=\varepsilon/3`$ and then $`n`$ with $`d_n(S)\le\varepsilon/3`$;
the right side of (108.6) tends to zero. For $`S=0`$ the claim is immediate.
Mixtures over starting vertices preserve the same bounds.

Finally, the two inverse conventions differ by at most the largest
excursion mark with $`\theta_i\le NS`$. The compensator in (108.8) is
continuous, so each mark is a jump of $`M^{\rm exc}`$ and is at most
$`2\sup_{a\le NS}|M^{\rm exc}_a|`$. Its size divided by $`N`$ tends to zero
uniformly in probability by the same maximal bound. This proves the
endpoint assertion. $`\square`$

## 109. A persistent centered defect for actual ancestry transport

**Definition 109.1 (ancestry in the original counting spaces).**
On the orbit $`T_n=\rho^n\alpha`$ only, let $`\pi_n:V_{T_{n+1}}\to V_{T_n}`$
fix every old vertex and send each new child to its actual old beta
parent. In this section $`J_n`$ denotes its ancestry pullback,
$`(J_nf)(y)=f(\pi_n(y))`$, rather than the path-summation map in §103.
Keep the same counting spaces $`\mathcal V_n`$, closed $`L_n`$ and centered
projections $`P_n=I-N_n^{-1}\mathbf1\mathbf1^*`$ as in Definition 103.1.
Put

```math
\begin{aligned}
\mathcal A_n&=\sqrt{\frac{N_n}{N_{n+1}}}\,P_{n+1}J_nP_n,\\ {}
\Delta_n(s)&=\left\|
e^{-N_{n+1}sL_{n+1}}\mathcal A_n
-\mathcal A_ne^{-N_nsL_n}\right\|_{\mathcal V_n\to\mathcal V_{n+1}}
\qquad(s>0).
\end{aligned}
\tag{109.1}
```

The notation $`\mathcal A_n`$ distinguishes this comparison map from the
scalar $`A_n`$ of Definition 92.2 and the random inverse in §108.
The constant mode is removed on both sides. The norms are the original
counting norms; no leaf-only or degree-weighted space is substituted.
An old beta fibre has size three and every other fibre size one, so
$`J_n^*J_n=I+2H_{\mathcal B_n}`$ and
$`\|\mathcal A_n\|\le\sqrt{3N_n/N_{n+1}}`$.

**Theorem 109.2 (a fixed-positive-time full-state obstruction).**
With $`c=\varphi^{-1}`$ and $`\kappa=c(2-c)`$, for every fixed $`s>0`$,

```math
\liminf_{n\to\infty}\Delta_n(s)
\ge c\sqrt{\kappa}
-\sqrt{s\sqrt5\,c(3-c)}.
\tag{109.2}
```

In particular this is a strictly positive lower bound whenever

```math
0<s<\frac{c^2(2-c)}{\sqrt5(3-c)}.
\tag{109.3}
```

It also proves the nominated, weaker bound

```math
\liminf_{n\to\infty}\Delta_n(s)
\ge\varphi^{-3/2}
-\sqrt{\frac{2s\sqrt5}{\varphi}}>0,
\qquad 0<s<\frac1{2\sqrt5\varphi^2}.
\tag{109.4}
```

At the $`n`$-independent time $`s=1/100`$, the exact bound in (109.2)
is greater than $`0.389`$. Thus full-state ancestry transport fails at
a strictly positive source-size-scaled comparison time, despite the
all-source occupation-clock theorem.

**Proof.**
The witness will be centered before transport and detected by a centered
unit successor test. It uses the actual beta mask, rather than a
constant-mode mismatch. For $`n\ge3`$, the old left and right root
subtrees are $`T_{n-1}`$ and $`T_{n-2}`$. Write their sizes as
$`M_L=N_{n-1}`$ and $`M_R=N_{n-2}`$, and $`N=N_n=1+M_L+M_R`$.
Define a real root contrast $`z_n`$ to be zero at the root and constant
on these two entire subtrees, with values

```math
\alpha_n=\sqrt{\frac{NM_R}{M_L(N-1)}},\qquad
\beta_n=-\sqrt{\frac{NM_L}{M_R(N-1)}}.
\tag{109.5}
```

Then $`\sum z_n=0`$, $`\|z_n\|^2=N`$ and its two constants stay bounded.
Define $`w_{n+1}`$ by the identical prescription on the successor's
actual subtrees $`T_n,T_{n-1}`$, and put
$`g_{n+1}=w_{n+1}/\sqrt{N_{n+1}}`$. This is a centered unit vector.
Only the two root edges contribute to its energy; hence, with
$`N'=N_{n+1}`$,

```math
N'\langle g_{n+1},L_{n+1}g_{n+1}\rangle
=\alpha_{n+1}^2+\beta_{n+1}^2
\longrightarrow\varphi+\varphi^{-1}=\sqrt5.
\tag{109.6}
```

Here and below the values of $`w_{n+1}`$ on old vertices are its actual
successor values. Every ancestry fibre stays in its own root subtree,
and the root fibre is just the root for $`n\ge3`$.

On the old vertices set

```math
f_n=2\mathbf1_{\mathcal B_n}-c,\qquad
d_n=\|P_n(z_nf_n)\|,\qquad
v_n=d_n^{-1}P_n(z_nf_n).
\tag{109.7}
```

Products in this proof are pointwise. On each actual $`T_k`$ block the
sum of $`f_n`$ is $`q_k=c+\delta_k`$ from (108.10). In particular,
$`\sum z_nf_n=\alpha_nq_{n-1}+\beta_nq_{n-2}`$ is bounded independently
of $`n`$. The fraction of beta leaves in either large subtree tends to
$`c/2`$. The two possible values of $`f_n`$ are $`2-c`$ and $`-c`$, so

```math
\begin{aligned}
\kappa&=\frac c2(2-c)^2+\left(1-\frac c2\right)c^2=c(2-c)>0,\\ {}
\frac{d_n^2}{N}&\longrightarrow\kappa.
\end{aligned}
\tag{109.8}
```

The centering subtraction has squared norm
$`N^{-1}(\sum z_nf_n)^2=O(N^{-1})`$ and does not affect this limit.
Consequently $`d_n>0`$ for all sufficiently large $`n`$, and $`v_n`$ is a
centered unit vector on the original counting space.

Its old heat state vanishes at every fixed scaled positive time. To
prove this rather than assume local equilibrium, on each of the two
root subtrees take the block corrector from the proof of (108.12),
with value zero at that subtree's root. Multiply it by its corresponding
constant $`\alpha_n`$ or $`\beta_n`$, and extend by zero at the global root.
Call the resulting vector $`H_n`$. The zero values at the two subtree
roots make the exterior root seams contribute zero. The exact identity
is therefore

```math
z_nf_n=L_nH_n+R_n,\qquad
R_n=\alpha_nq_{n-1}\delta_L+\beta_nq_{n-2}\delta_R,
\qquad \|R_n\|=O(1),\quad \|H_n\|=O(n\sqrt N).
\tag{109.9}
```

The corrector bounds use $`|q_k|\le2`$ and block height at most $`n`$.
Since $`P_nL_n=L_n`$ and positive spectral calculus gives
$`\|e^{-tL_n}L_n\|\le1/(et)`$, for fixed $`s>0`$,

```math
\|e^{-NsL_n}v_n\|
\le\frac{\|H_n\|}{eNs\,d_n}+\frac{\|R_n\|}{d_n}
=O\!\left(\frac n{Ns}+\frac1{\sqrt N}\right)
\longrightarrow0.
\tag{109.10}
```

This uses the finite spectral calculus already supplied in §103; it
requires no uniform gap over arbitrary sources.

Now compute how the same state couples through authentic ancestry
to the successor's low-energy root contrast. Write
$`m_n=1+2\mathbf1_{\mathcal B_n}=\varphi+f_n`$ for its actual fibre
multiplicity. Within either root subtree $`T_k`$, direct summation gives

```math
\begin{aligned}
\sum_{T_k}m_nf_n&=\kappa N_k+(3-c)q_k,\\ {}
\frac1{N_k}\sum_{T_k}m_nf_n^2
&\longrightarrow\kappa(3-c).
\end{aligned}
\tag{109.11}
```

For the first identity use $`2|\mathcal B(T_k)|=cN_k+q_k`$.
For the second, its two values and their actual limiting fractions give

```math
3\frac c2(2-c)^2+\left(1-\frac c2\right)c^2
=\kappa+c(2-c)^2=\kappa(3-c).
\tag{109.12}
```

The successor contrast is centered, so
$`\sum_{V_{T_n}}m_nw_{n+1}=\sum_{V_{T_{n+1}}}w_{n+1}=0`$ exactly.
Thus both centering projections disappear from the pairing, including
the mean subtraction in (109.7), and

```math
\langle g_{n+1},\mathcal A_nv_n\rangle
=\frac{\sqrt{N/N'}}{\sqrt{N'}d_n}
 \sum_{V_{T_n}}w_{n+1}z_nm_nf_n
\longrightarrow c\sqrt{\kappa}.
\tag{109.13}
```

Indeed both pairs of root-contrast constants tend to the same limits:
their left squared value tends to $`\varphi^{-1}`$ and their right
squared value to $`\varphi`$. Therefore
$`N^{-1}\sum w_{n+1}z_n\to1`$, and (109.11) makes the numerator sum
$`\kappa N+o(N)`$. Equations (109.8), $`N'/N\to\varphi`$ and the displayed
normalization yield (109.13), including its positive sign.

The norm of this actual transported state has the limit

```math
\|\mathcal A_nv_n\|^2\longrightarrow c(3-c).
\tag{109.14}
```

To verify all mass and projection terms, set
$`b_n=N^{-1}\sum z_nf_n=O(N^{-1})`$, so
$`v_n=(z_nf_n-b_n)/d_n`$. Then
$`\|J_nv_n\|^2=d_n^{-2}\sum m_n(z_nf_n-b_n)^2\to3-c`$
by (109.11)–(109.12), bounded multiplicities and
$`\sum z_n^2=N`$. Moreover

```math
\sum J_nv_n
=\frac{(3-c-r(T_0,n))\sum z_nf_n}{d_n}=O(N^{-1/2}).
\tag{109.15}
```

Here (109.11) and $`\sum z_n=0`$ give
$`\sum m_nz_nf_n=(3-c)\sum z_nf_n`$, while $`\sum m_n=N'`$.
The successor projection subtracts squared norm
$`N'^{-1}(\sum J_nv_n)^2`$, which tends to zero. Multiplication by
$`N/N'\to c`$ proves (109.14). No counting mass has been discarded.

For a positive self-adjoint finite $`L`$, the ordinary spectral inequality
$`(1-e^{-u})^2\le u`$ for $`u\ge0`$ gives

```math
\|(e^{-tL}-I)g\|^2\le t\langle g,Lg\rangle.
\tag{109.16}
```

Apply it to the centered unit $`g_{n+1}`$ and use self-adjointness of
the successor heat operator. Evaluation of the operator difference
on $`v_n`$ and pairing with $`g_{n+1}`$ yields

```math
\begin{aligned}
\Delta_n(s)\ge{}&\langle g_{n+1},\mathcal A_nv_n\rangle
-\sqrt{N's\langle g_{n+1},L_{n+1}g_{n+1}\rangle}
  \|\mathcal A_nv_n\|\\ {}
&-\sqrt{3N/N'}\,\|e^{-NsL_n}v_n\|.
\end{aligned}
\tag{109.17}
```

Taking the lower limit in (109.6), (109.10), (109.13) and (109.14)
proves (109.2). Squaring its two positive terms gives (109.3).
For (109.4), let $`s_0=c^2/(2\sqrt5)`$. Since $`0<c<1`$,

```math
\sqrt{2-c}>\sqrt{(3-c)/2}>1.
\tag{109.18}
```

For $`0<s\le s_0`$, the excess of the bound in (109.2) over
$`c^{3/2}-\sqrt{2s\sqrt5c}`$ is at least

```math
c^{3/2}\left(\sqrt{2-c}-\sqrt{(3-c)/2}\right)>0.
\tag{109.19}
```

This proves the nominated constants, rather than replacing that
conjecture by a derivative or a sequence of shrinking times.
For the stated decimal lower bound at $`s=1/100`$, elementary squared
rational comparisons give
$`0.61803398<c<0.61803399`$ and $`2.23606797<\sqrt5<2.23606798`$.
They imply $`c\sqrt{c(2-c)}>0.571`$ and
$`\sqrt{\sqrt5c(3-c)/100}<0.182`$; hence the exact difference exceeds
$`0.389`$. Its rounded value is $`0.3897393\ldots`$.

The state $`v_n`$ has rapidly alternating beta-multiplicity charge
within each entire root subtree. Old scaled heat erases it by
(109.9)–(109.10), while ancestry's three-versus-one fibres give it
the nonzero successor contrast (109.13). Successor heat cannot erase
that contrast on these fixed positive windows, by (109.6) and (109.16).
Both state and test have mean zero. This explains why the obstruction
coexists with (108.4): an inverse occupation clock compares time along
the old trace, whereas $`J_n`$ copies a function to every ancestry fibre.
They are different state comparisons. The norm-convergent transport
of §103 uses the gradient/polar maps $`U_n`$, and is consistent with
this failure of the expressly different ancestry maps. $`\square`$

**Assumption 109.3 (the separate operation-and-readout correspondence).**
To interpret either comparison as native propagation, one would additionally
need the same original source and actual accepted update, an available
occurrence-state preparation, an allowed actuator with generator $`-L`$,
the stated readouts and state-transfer map, and a verified conversion
from actual supplied durations to the respective comparison times.
An execution subject to a cap or refusal retains its original guard,
history and absorbing Stop; it is not enlarged by the mathematical
family $`\rho^nt`$. Source sizes in (108.1) and (109.1) are mathematical
parameters, not acquired size or index advice. These additional
correspondences are not premises proved by Theorems 108.2 and 109.2.

The original-source and permission conditions remain those of
[Continuation I, Definition 58.1 and §62](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md),
Assumptions 97.1, 102.3 and 106.3, and
[native leaf-depth/contact, Assumptions 1.2 and Definition 1.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md).
A joint stochastic interpretation must keep one common realization,
as in [common-source positivity, Definition C-30.1](AURIC_FIB_ATOM_COMMON_SOURCE_POSITIVITY_AND_HISTORICAL_PREFIXES.md),
[local-clock seam, Assumption 18 and Theorem 22](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)
and [pyramid correlation, Definition 21.10](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md).
The marked-output acquisition laws of
[Kbonacci acquisition, §§77–82](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md)
retain their own target and consumer; by their Theorem 82.1 they do not
recover the unchanged original target, and supply none of the occurrence
actuators here. A physical clock, physical spatial realization or a claim
of three spatial dimensions would require its own correspondence beyond
these assumptions.

## 109.99 追加锚（本行以下为增补区）

## 110. Root-visible ancestry memory of homogeneous occurrence states

**Definition 110.1 (comparison states and the normalized root port).**
Retain the complete original ordered sources $T_n$, all their occurrence
vertices, counting spaces $\mathcal V_n$, closed unit-edge operators $L_n$
and centering projections $P_n$ of §§92 and 103. Retain the actual ancestry
pullback $J_n$ and the comparison map $\mathcal A_n$ of Definition 109.1;
$J_n$ here is not the path-summation map of §98. Write

$$
S_n(s)=e^{-N_nsL_n},\qquad
\mathcal C_nf=\sqrt{N_n}\,f(r)\quad(f\in P_n\mathcal V_n),
\qquad c=\varphi^{-1},\quad \kappa=c(2-c),\quad \theta=c\kappa=3-4c.
\tag{110.1}
$$

The port $\mathcal C_n$ is distinct from the scalar centered finite part
$C(T_n)$ of §92. For $n\ge2$, define $z_n$ by (109.5), including its zero
root value, and put

$$
\chi_n=2\mathbf1_{\mathcal B_n}-c,\qquad
 d_n=\|P_n(z_n\chi_n)\|,\qquad
 x_n=d_n^{-1}P_n(z_n\chi_n).
\tag{110.2}
$$

Thus $x_n$ is the witness of (109.7), renamed to avoid confusion with
the edge vector $v_n$ of §98. Its definition also applies at $n=2$:
both root subtrees are singletons, $z_n\chi_n$ is zero at the root and
nonzero in the left subtree, so it is not constant and $d_n>0$.
The same argument gives $d_n>0$ for every $n\ge2$. Set $x_0=x_1=0$;
there is no centered unit state on either singleton counting space.
For $n\ge2$, $\|x_n\|=1$, and (109.8) gives $d_n^2/N_n\to\kappa$.

In formulas involving the common edge carrier, write $v_n^{\mathrm e}$
for the vector called $v_n$ in §98; retain its limit $v$, the covariance
$\Sigma_n$ and its limit $\Sigma$. Let

$$
b_n=\alpha_n\delta_L+\beta_n\delta_R
 \longrightarrow b=\sqrt c\,\delta_L-c^{-1/2}\delta_R,
\qquad
F_s(x)=\begin{cases}e^{-s/x},&x>0,\\0,&x=0,\end{cases}\quad(s>0),
\tag{110.3}
$$

where $\alpha_n,\beta_n$ are precisely (109.5). The vectors $\delta_L$
and $\delta_R$ in (110.3) are edge coordinates; node point masses below
are indicated by their occurrence addresses.

**Theorem 110.2 (the copied beta charge on every actual descendant).**
For every $k\ge0$, use the literal ancestry map from $T_k$ to $T_{k+1}$
and define on the entire successor

$$
\psi_k=J_k\chi_k-\theta\mathbf1,\qquad
q_k=\sum_{V_{T_k}}\chi_k=c-2c(-c)^k.
\tag{110.4}
$$

There is a real field $H_k$ on $T_{k+1}$, zero at its root, such that

$$
\psi_k=L_{k+1}H_k+3c q_k\delta_r,\qquad
\|H_k\|\le K(k+1)\sqrt{N_{k+1}},
\tag{110.5}
$$

with one constant $K$ independent of $k$. More precisely, every edge
increment of $H_k$ is its actual below-edge total $\psi_k$ charge.
At an old address whose old descendant is $T_j$, this total is $3c q_j$;
at either newly born leaf it is $\kappa$. These are counting totals,
including the descendant root and every internal and terminal occurrence.

For $n\ge2$ let $Z_n$ be zero at the successor root and have the old
constants $\alpha_n,\beta_n$ on its actual entire successor root subtrees
$T_n,T_{n-1}$, respectively. Then there are fields $\widetilde H_n$ and
$R_n^{\mathrm{new}}$ on the successor with

$$
\begin{aligned}
J_n(z_n\chi_n)&=\theta Z_n+L_{n+1}\widetilde H_n+R_n^{\mathrm{new}},\\
R_n^{\mathrm{new}}
 &=3c\bigl(\alpha_nq_{n-1}\delta_L+\beta_nq_{n-2}\delta_R\bigr),\\
\|\widetilde H_n\|&=O(n\sqrt{N_{n+1}}),\qquad
\|R_n^{\mathrm{new}}\|=O(1).
\end{aligned}
\tag{110.6}
$$

Here $\delta_L,\delta_R$ in (110.6) are node point masses at the two
actual successor subtree roots. Both root seams contribute zero to
the corrector energy flux.

Proof. The exact fibre multiplicity is
$m_k=1+2\mathbf1_{\mathcal B_k}=\varphi+\chi_k$.
Thus $N_{k+1}=\varphi N_k+q_k$. The two possible values $2-c,-c$ of
$\chi_k$ satisfy the pointwise identity

$$
m_k\chi_k=\kappa+(3-c)\chi_k.
\tag{110.7}
$$

For an old descendant $T_j$, literal substitution gives the complete
successor descendant $T_{j+1}$. Summing (110.7) on its old vertices
counts every new occurrence once through its own beta-parent fibre.
Its total copied charge is $\kappa N_j+(3-c)q_j$. Consequently its
$\psi_k$ charge is

$$
\kappa N_j+(3-c)q_j-\theta N_{j+1}
 =\bigl(3-c-\theta\bigr)q_j=3c q_j,
\tag{110.8}
$$

because $c\varphi=1$ and $c^2=1-c$. Both new children of an old beta
parent copy $2-c$, irrespective of their different beta and alpha labels.
Their successor $\psi_k$ charge is therefore
$2-c-\theta=\kappa$. No nonexistent descendant is assigned a charge.

This also checks the early sources without a branch approximation.
At $k=0$ the old alpha singleton becomes a beta singleton and
$\psi_0=-c-\theta=3c q_0$, with $q_0=-c$ and $H_0=0$.
At $k=1$ the old beta singleton becomes the three-node ordered source
$\langle\beta,\alpha\rangle$. Each of its three copied values is $2-c$,
each residual charge is $\kappa$, and the total is
$3\kappa=3c q_1$, with $q_1=2-c$. Give each of its two edges increment
$\kappa$; this gives (110.5) at the root and both new leaves.

For every larger successor, prescribe its root value to be zero and
its edge increment to be the total residual charge below that edge.
At a nonroot vertex the parent-edge increment minus the sum of the
child-edge increments is its own charge; at the root the missing
parent increment subtracts the entire charge $3c q_k$. This proves
(110.5) with the closed, rather than grounded, Laplacian. By (108.10),
$|q_j|\le2$, so every edge increment has modulus at most
$\max(6c,\kappa)$. Successor height is at most $k+1$, proving the norm
bound in (110.5).

For (110.6), place $\alpha_nH_{n-1}$ in the successor left subtree and
$\beta_nH_{n-2}$ in its right subtree, and put zero at the global root.
The three seam endpoint values of this corrector are all zero.
The internal subtree Laplacians therefore agree with the restrictions
of the global Laplacian, including at both subtree roots, and its
global root Laplacian value is zero. Apply (110.5) separately to these
two complete blocks. This proves (110.6), also for the old beta and
alpha singleton subtrees when $n=2$. Boundedness of the contrast
constants and of $q_k$ gives the displayed norms. $\square$

**Theorem 110.3 (a root-visible limit at fixed positive time).**
For every fixed $s>0$,

$$
\begin{aligned}
\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nx_n&\longrightarrow D(s),\\
\mathcal C_{n+1}\mathcal A_nS_n(s)x_n&\longrightarrow0,\\
\mathcal C_{n+1}\bigl[S_{n+1}(s)\mathcal A_n
                  -\mathcal A_nS_n(s)\bigr]x_n
 &\longrightarrow D(s)
   =-c\sqrt\kappa\,\langle F_s(\Sigma)v,b\rangle.
\end{aligned}
\tag{110.9}
$$

All three convergences are uniform on compact subintervals of
$(0,\infty)$. Their endpoint, in the stated order of limits, is

$$
\lim_{s\downarrow0}D(s)
 =-(c-1/2)\sqrt{2-c}=:-\eta<0.
\tag{110.10}
$$

There is an $s_*>0$, independent of $n$, such that
$D(s)\le-3\eta/4$ for every $0<s\le s_*$. On the fixed closed window
$[s_*/2,s_*]$, all sufficiently large $n$ have root commutator in
(110.9) at most $-\eta/2$, uniformly in $s$.
No value of $s_*$ or bound at $s=1/100$ is asserted.
For every finite $n$, the commutator at $s=0$ is zero; convergence
through zero is not uniform.

Proof. Positive-time smoothing is essential because
$\|\mathcal C_n\|=\sqrt{N_n-1}$ on the centered counting space.
Let $g_n=P_n\delta_r$ and use $h_n(s)$ of (103.10). Unitarity of
$U_n$ and (103.11) give the exact bound

$$
\|\mathcal C_nS_n(s)\|=\|h_n(s)\|
 \le \frac{V}{\sqrt{2es}}=:B_s,
\qquad V=\sup_n\|v_n^{\mathrm e}\|<\infty.
\tag{110.11}
$$

Indeed $\sup_{x>0}x^{-1/2}e^{-s/x}=(2es)^{-1/2}$, and (98.6)
bounds the edge vectors. The centered singleton spaces give zero
on both sides of the norm identity. Thus this is a bound on the
smoothed root port, not on $\mathcal C_n$ itself.

For the exact smooth root term, denote the path-summation map by
$\mathscr J_j$ to distinguish it from ancestry. On actual edges,
(103.3), (103.6) and the polar map give

$$
U_jP_j\mathscr J_j e
 =-\sqrt{N_j}\,\Sigma_j^{1/2}e,
\qquad
\bigl(S_j(s)P_j\mathscr J_j e\bigr)(r)
 =-\langle F_s(\Sigma_j)v_j^{\mathrm e},e\rangle.
\tag{110.12}
$$

For the first equality use
$U_j=-K_j^{-1/2}D_j$ and $D_j\mathscr J_j e=e$.
Pairing it with $h_j(s)=\Sigma_j^{-1/2}F_s(\Sigma_j)v_j^{\mathrm e}$
proves the second, with inverses restricted to actual edges.
The omitted coordinates contribute zero. On a singleton the actual
edge space is zero and the centered equation is also zero.

Here $Z_n=\mathscr J_{n+1}b_n$ exactly: its constants refer to the
successor's two complete subtrees, not just old vertices. Equation
(110.12), covariance norm convergence (98.6), vector convergence
$v_{n+1}^{\mathrm e}\to v$, and $b_n\to b$ imply

$$
\bigl(S_{n+1}(s)P_{n+1}Z_n\bigr)(r)
 \longrightarrow-\langle F_s(\Sigma)v,b\rangle.
\tag{110.13}
$$

The operator continuity here is the mature continuous functional
calculus used in Theorem 103.3; its uniformity away from zero is
already part of that theorem. Spectral and polar calculus are
`literature-attested` intermediate results; see
[Teschl, *Mathematical Methods in Quantum Mechanics*, §3.1,
Theorem 3.7 and Problem 3.11, and §6.2, Theorem 6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The source-specific copied-charge correspondence (110.6) supplies
an initial state to this calculus; it does not follow from a scalar
root resolvent.

Both centering projections are accounted for before using that
correspondence. If $\bar u_n=N_n^{-1}\sum z_n\chi_n$, then
$x_n=(z_n\chi_n-\bar u_n\mathbf1)/d_n$.
Since $J_n\mathbf1=\mathbf1$, the successor projection removes this
entire old mean exactly. Therefore

$$
\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nx_n
 =\frac{\sqrt{N_n}}{d_n}
 \bigl(S_{n+1}(s)P_{n+1}J_n(z_n\chi_n)\bigr)(r).
\tag{110.14}
$$

The successor mean of $Z_n$ is retained by $P_{n+1}$; the constants
$\alpha_n,\beta_n$ are not presumed to center that successor field.
For the corrector term in (110.6), self-adjointness, a heat split,
and $\|L_je^{-N_jsL_j/2}\|\le2/(eN_js)$ give

$$
\begin{aligned}
\left|\bigl(S_{n+1}(s)L_{n+1}\widetilde H_n\bigr)(r)\right|
 &\le\frac{B_{s/2}}{\sqrt{N_{n+1}}}
       \frac{2\|\widetilde H_n\|}{eN_{n+1}s}
   =O\left(\frac{nB_{s/2}}{N_{n+1}s}\right),\\
\left|\bigl(S_{n+1}(s)P_{n+1}R_n^{\mathrm{new}}\bigr)(r)\right|
 &\le\frac{B_s}{\sqrt{N_{n+1}}}\|R_n^{\mathrm{new}}\|.
\end{aligned}
\tag{110.15}
$$

The Laplacian term already has zero counting mean. Both bounds tend
to zero, uniformly on every compact positive-time interval.
Since $\sqrt{N_n}/d_n\to\kappa^{-1/2}$, equations (110.6) and
(110.13)--(110.15) prove the first line of (110.9), with coefficient
$\theta/\sqrt\kappa=c\sqrt\kappa$ and the displayed negative sign.

For the other order, (109.9)--(109.10) give, for every $a>0$,

$$
\|S_n(a)x_n\|
 =O\left(\frac{n}{N_na}+\frac1{\sqrt{N_n}}\right)\longrightarrow0,
\tag{110.16}
$$

uniformly for $a$ in compact positive-time intervals. This uses the
old closed blocks and their zero seam corrector values. It does not
assume a uniform spectral gap on arbitrary original sources.
For every centered old field $u$ and $n\ge2$, the actual root fibre
has size one. Summing all other fibres through $m_n=\varphi+\chi_n$
and retaining the successor projection gives exactly

$$
\mathcal C_{n+1}\mathcal A_nu
 =\mathcal C_nu-\frac{\sqrt{N_n}}{N_{n+1}}\langle\chi_n,u\rangle.
\tag{110.17}
$$

The multiplier
$\sqrt{N_n}\|\chi_n\|/N_{n+1}$ is bounded, since $|\chi_n|\le2$
and $N_{n+1}\ge N_n$. With $u=S_n(s)x_n$, its second term tends to
zero by (110.16). Its first term is bounded by
$B_{s/2}\|S_n(s/2)x_n\|$ and also tends to zero. This proves the
second and third lines of (110.9) and their positive-time uniformity.
For $n=0,1$ the centered input is zero, so the exceptional size-three
root fibre at the beta singleton adds no omitted term.

Finally, Theorems 99.1 and 103.3 give
$F_s(\Sigma)v\to P_{(\ker\Sigma)^\perp}v=v-q$ strongly as
$s\downarrow0$, where $q_p=2^{-|p|}$. The two first-edge coordinates
of $v-q$ are $c-1/2$ and $c^2-1/2=-(c-1/2)$. Thus

$$
c\sqrt\kappa\,\langle v-q,b\rangle
 =c\sqrt\kappa(c-1/2)(\sqrt c+c^{-1/2})
 =(c-1/2)\sqrt{2-c},
\tag{110.18}
$$

using $c(1+c)=1$. Strong spectral continuity and (110.18) prove
(110.10) and give an $s_*>0$ with
$|D(s)+\eta|\le\eta/4$ for $0<s\le s_*$. Uniform convergence in
(110.9) on $[s_*/2,s_*]$ then gives the finite lower discrepancy
$\eta/2$ for all sufficiently large $n$. This is one fixed window,
not a sequence $s_n\to0$. At $s=0$ each finite heat operator is the
identity, so each finite commutator vanishes exactly. In particular,
there cannot be a common finite threshold in $n$ enforcing a nonzero
bound all the way down to zero. $\square$

**Theorem 110.4 (passive forgetting is unsafe for the mixed comparison word).**
For uniformly bounded sequences of centered counting states, define

$$
f\sim_{\mathrm{pass}}g
 \quad\Longleftrightarrow\quad
 \forall a>0,\quad\|S_n(a)(f_n-g_n)\|\longrightarrow0.
\tag{110.19}
$$

Then $x\sim_{\mathrm{pass}}0$, and for every fixed $a>0$ the sequence
$\widehat x_n=S_n(a)x_n$ also satisfies
$x\sim_{\mathrm{pass}}\widehat x$. Nevertheless, for every fixed
$s>0$,

$$
\begin{aligned}
\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nx_n&\longrightarrow D(s),\\
\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nS_n(a)x_n&\longrightarrow0.
\end{aligned}
\tag{110.20}
$$

Consequently passive positive-time equivalence does not preserve
this mixed future root readout, on the fixed window of Theorem 110.3.
This is an asymptotic statement about homogeneous initial states;
it does not assert exact finite root blindness or compute an exact
native mixed-future kernel.

Proof. Equation (110.16) proves $x\sim_{\mathrm{pass}}0$.
Contraction and the semigroup law give, for every $t>0$,

$$
\|S_n(t)(x_n-S_n(a)x_n)\|
 \le\|S_n(t)x_n\|+\|S_n(t+a)x_n\|\longrightarrow0.
\tag{110.21}
$$

The first line of (110.20) is Theorem 110.3. For the second, root
smoothing (110.11) and $\|\mathcal A_n\|\le\sqrt{3N_n/N_{n+1}}$
give

$$
\left|\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nS_n(a)x_n\right|
 \le B_s\sqrt{3N_n/N_{n+1}}\,\|S_n(a)x_n\|\longrightarrow0.
\tag{110.22}
$$

Thus the words are, in actual chronological order, renewal then
successor heat then root readout, and old heat then renewal then
successor heat then root readout. The intermediate heat cannot be
moved across renewal under (110.19). The action-language distinctions
of [Fiber II, Definition 44.5](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md)
and [Fiber III, Definition 34.1](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_III.md)
retain their original exact finite scope. Here $x_n$ need not lie in
$K_{\mathrm{stat}}$ at any finite $n$; (110.19) is the precise weaker
equivalence refuted by the source-specific witness. $\square$

**Definition 110.5 (normalization and the operation bridge).**
The discrepancy (110.9) uses unit counting-norm inputs and a
$\sqrt{N_n}$-normalized root port. Equivalently, the pointwise fields
$X_n=\sqrt{N_n}x_n$ are uniformly bounded, have counting norm
$\sqrt{N_n}$, and satisfy

$$
\bigl(S_{n+1}(s)P_{n+1}J_nP_nX_n
      -P_{n+1}J_nP_nS_n(s)X_n\bigr)(r)
 =\mathcal C_{n+1}\bigl[S_{n+1}(s)\mathcal A_n
                     -\mathcal A_nS_n(s)\bigr]x_n.
\tag{110.23}
$$

Uniform pointwise boundedness follows from the bounded constants of
$z_n$, $|\chi_n|\le2$, and $d_n/\sqrt{N_n}\to\sqrt\kappa>0$.
The ordinary root discrepancy on $x_n$ with the map $\mathcal A_n$
is instead (110.9) divided by $\sqrt{N_{n+1}}$, and tends to zero.
Neither normalization supplies an acquired count or source index.

Theorems 110.2--110.4 are `repo-derived` ordinary source-specific
mathematics. Their reused intermediate supplies are the beta-charge
identity of §108, old-state relaxation of §109, full covariance and
root smoothing of §§98--103, and the spectral calculus cited in the
proof of Theorem 110.3. The added correspondence is the entire copied
charge with its new-leaf residual and both actual root seams, which
makes the full-state defect visible at the root after fixed positive
successor heat. The result concerns the homogeneous term omitted by
the zero-initial forcing assumption of §106. It is not a further
zero-initial convolution or a scalar-spectrum reconstruction.

A native interpretation would require a typed correspondence from the
complete original-source execution to these prepared signed occurrence
fields, heat actuators, ancestry transfer and real root ports, preserving
the same actual source, accepted actions, readouts and mixed order.
The literal $\mathsf{Read}$, $\mathsf{ApplyRho}$ and absorbing
$\mathsf{Halt}$ contract supplies none of those occurrence-state ports
by its definition. The additional correspondence remains unproved.
In particular, the two centering projections and signed witnesses here
are not a supplied positivity-preserving probability channel.

Any proposed bridge retains the entire original ordered source domain,
its immutable original target, one joint actual history, authenticated
current epoch, reached-address and presence guards, permission and
refusal rules, full accessible control and cached fields, absorbing
Stop and the declared vector of preparation, raw-call, address,
update, arithmetic, memory and output costs. These are the same-source
and whole-row obligations of
[Uniform Descriptor Boundary, Definitions 1.2 and Assumptions 1.3--1.5](RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_DESCRIPTOR_BOUNDARY.md)
and Assumptions 106.3 and 109.3; separate marginal realizations do not
satisfy them. Only actually allowed mixed words enter a native future
signature. Source-step, source-size-scaled comparison time, acquired
experiment chronology and physical duration remain separate parameters
until their operation-and-time correspondences are proved.

The family $T_n$ is a counterfamily inside the full original domain,
not a replacement for it. The comparison memory obstruction does not
supply a spatial metric or dimension, stable physical matter, a physical
clock, native propagation authority, full-spectrum recovery, or a
completion criterion for an unbounded source-to-spatial-propagation task.

## 110.99 追加锚（本行以下为增补区）

## 111. Source-biased boundary propagation and its direct-locality obstruction

**Definition 111.1 (the all-node fields and the free-root trace energy).**
Retain the literal ordered $T_n$, all occurrence vertices, the counts
$N_n$, and the closed unit-edge counting operators $L_n$ of §§92 and 103.
In this section $J_n$ and $J$ always denote the path-summation maps of
§98, not the ancestry pullback of §§109–110. Retain the actual law

$$
\Omega=\{L,R\}^{\mathbb N},\qquad
M([p])=\varphi^{-\#_L(p)-2\#_R(p)},\qquad
\mu_n=N_n^{-1}\sum_{x\in V_{T_n}}\delta_x,
\qquad S_n(s)=e^{-N_nsL_n}.
\tag{111.1}
$$

Thus $\mu_n$ includes the root, every interior occurrence and every leaf.
The variable $s$ is the comparison time in (110.1). Set
$\mathscr G=L^2(\Omega,M)$, $\Pi F=F-\int F\,dM$,
$C=\Pi J$, and $\mathscr K=(\ker\Sigma)^\perp$. Then
$C^*C=\Sigma$ by (98.13). Define

$$
\begin{aligned}
\mathcal D&=\{F\in\mathscr G:F=c\mathbf1+Jz
                  \text{ for some }c\in\mathbb R,\ z\in\mathscr H\},\\
\mathcal E(F)&=\inf\{\|z\|^2:F=c\mathbf1+Jz,
                                      \ c\in\mathbb R,\ z\in\mathscr H\}.
\end{aligned}
\tag{111.2}
$$

A pair $(c,z)$ specifies the finite-energy extension
$u(\varnothing)=c$ and
$u(p)=c+\sum_{\varnothing\ne q\preceq p}z_q$ on the complete binary
address tree. Its unit-edge energy is $\|z\|^2$ and its trace is
$c\mathbf1+Jz$ in the specified $L^2(M)$ sense. The root value is free
in (111.2); there is no root killing term. The infimum varies extensions
of the same trace, never the original $T_n$, its labels or its measure.
Let $\mathcal A$ be the real algebra of finite cylinder functions on
$\Omega$, with its product topology.

**Theorem 111.2 (the actual biased trace gives a regular conservative form).**
For every $F\in\mathcal D$ there is a unique $z_F\in\mathscr K$ with

$$
Cz_F=\Pi F,\qquad
c_F=\int F\,dM-\langle v,z_F\rangle,
\qquad F=c_F\mathbf1+Jz_F.
\tag{111.3}
$$

It attains (111.2). The polarization
$\mathcal E(F,G)=\langle z_F,z_G\rangle$ is a densely defined closed
Dirichlet form on $\mathscr G$. The cylinder algebra $\mathcal A$ is a
core both for the form norm and uniformly for $C(\Omega)$, so the form
is regular. Its zero-energy functions are precisely the constants.
For every 1-Lipschitz map $\chi:\mathbb R\to\mathbb R$,

$$
\chi\circ F\in\mathcal D,\qquad
\mathcal E(\chi\circ F)\le\mathcal E(F).
\tag{111.4}
$$

In particular $\mathbf1\in\mathcal D$ and $\mathcal E(\mathbf1)=0$.

**Proof.**
For any extension of $F$, $Cz=\Pi F$. The complete solution set is the
closed affine space $z+\ker C$, and
$\ker C=\ker\Sigma$ because $\|Cz\|^2=\langle z,\Sigma z\rangle$.
Its unique least-norm point is $z_F=P_{\mathscr K}z$; the constant
$c_F$ in (111.3) restores the mean. Conversely every solution of that
centered equation gives an extension with this choice of constant.
This proves attainment, uniqueness and polarization. It also shows
that zero energy is equivalent to $\Pi F=0$.

If $(F_j)$ is Cauchy for
$\|F\|_{\mathcal E,1}^2=\|F\|_{\mathscr G}^2+\mathcal E(F)$,
then $F_j\to F$ in $\mathscr G$ and $z_{F_j}\to z$ in the closed
space $\mathscr K$. Boundedness of the actual $C$ gives
$Cz=\Pi F$, proving $F\in\mathcal D$, $z_F=z$ and form-norm
convergence. This proves closedness without an inverse-range closure
assumption.

For contraction, start with any extension $(c,z)$ and its vertex
values $u(p)$. Put

$$
z^\chi_p=\chi(u(p))-\chi(u(p^-)),\qquad c^\chi=\chi(c).
\tag{111.5}
$$

The Lipschitz inequality gives $z^\chi\in\mathscr H$ and
$\|z^\chi\|\le\|z\|$. At level $h$, the cylinder function
$c\mathbf1+JP_hz$ has value $u(p)$ on $[p]$, $|p|=h$. The telescoping
identity on that level is therefore

$$
c^\chi\mathbf1+JP_hz^\chi
             =\chi(c\mathbf1+JP_hz).
\tag{111.6}
$$

The left side tends in $L^2(M)$ to $c^\chi\mathbf1+Jz^\chi$ by §98.
The right side tends to $\chi(F)$ by its Lipschitz property. This proves
trace compatibility and (111.4) by using the minimizing extension.
In particular clipping to $[0,1]$ gives the Markov property. This step
uses the actual $M$-trace, rather than transferring an almost-everywhere
trace from another law.

Every cylinder indicator is $J\delta_p$, hence belongs to $\mathcal D$.
The finite cylinder functions are dense in $L^2(M)$: cylinder sets
generate the Borel sigma algebra, and their finite partitions give the
usual dense simple functions. For $F=c_F\mathbf1+Jz_F$, let
$F_h=c_F\mathbf1+JP_hz_F$. Then $F_h\in\mathcal A$ and

$$
\|F_h-F\|_{\mathscr G}\le\|J\|\|(I-P_h)z_F\|,
\qquad
\mathcal E(F_h-F)\le\|(I-P_h)z_F\|^2\longrightarrow0.
\tag{111.7}
$$

Continuous functions on compact $\Omega$ are uniformly approximated
by constants on sufficiently long cylinders, by uniform continuity
in the product topology. Thus $\mathcal A\subset\mathcal D\cap C(\Omega)$
is both a form core and uniformly dense. The measure $M$ is a finite
Borel measure with full support, since every cylinder has positive mass;
it is Radon on this compact metrizable space. This proves regularity.
A constant has extension $(c,0)$ and zero energy.

The mature background is the trace-energy construction and its Markov
property: Woess, [*On the duality between jump processes on ultrametric
spaces and random walks on trees*, arXiv:1211.7216v1, §3.B,
(3.21)–(3.24) and §4](https://arxiv.org/pdf/1211.7216v1), and
Keller–Lenz–Schmidt–Schwarz, [*Boundary representation of Dirichlet forms
on discrete spaces*, arXiv:1711.08304v1, Theorems 2.4, 3.4 and
3.9](https://arxiv.org/pdf/1711.08304v1). Those statements use the
random walk's harmonic reference law or harmonic measures on the
Royden boundary. The fair end law of the unit-conductance binary tree
is not $M$: its first-cylinder masses are $1/2,1/2$, whereas those in
(111.1) are $a=\varphi^{-1}$ and $b=\varphi^{-2}$. No identification
of these reference laws is used here. The bounded trace from §98,
least-norm extension and (111.6) supply the needed hypotheses directly
on the source-derived probability space. The general trace construction
is a literature-attested intermediate supply; its relation to the
all-occurrence source covariance is the present repo-derived synthesis.
$\square$

**Theorem 111.3 (the source-biased boundary Markov semigroup).**
Let $H$ be the nonnegative self-adjoint operator associated with
$(\mathcal E,\mathcal D)$, and put $T(s)=e^{-sH}$, $s\ge0$.
There is a unitary $W:\mathscr K\to\mathbf1^\perp\subset\mathscr G$
from the polar decomposition
$C=W\Sigma^{1/2}$. Precisely,

$$
\begin{aligned}
\mathcal D\cap\mathbf1^\perp
     &=W\operatorname{ran}\bigl((\Sigma|_{\mathscr K})^{1/2}\bigr),\\
H|_{\mathbf1^\perp}
     &=W(\Sigma|_{\mathscr K})^{-1}W^*,\qquad H\mathbf1=0,\\
T(s)|_{\mathbf1^\perp}&=W\mathcal T(s)W^*\quad(s>0),
\qquad T(0)=I.
\end{aligned}
\tag{111.8}
$$

Here $\mathcal T(s)$ is exactly (103.7), restricted to $\mathscr K$.
The semigroup is strongly continuous, symmetric, positivity preserving
and conservative on $L^2(M)$; $0\le F\le1$ implies $0\le T(s)F\le1$,
and $T(s)\mathbf1=\mathbf1$. Hence it preserves the $M$-integral.
This is a boundary Markov law on the actual biased measure, not merely
a spectral contraction on the edge carrier.

**Proof.**
The closure of $\operatorname{ran}C$ is $\mathbf1^\perp$, since each
centered cylinder indicator is in its range and these are dense there.
Polar decomposition therefore gives the displayed unitary. If
$\Pi F=W\Sigma^{1/2}z_F$, then

$$
\mathcal E(F)=\|z_F\|^2
   =\|\Sigma^{-1/2}W^*\Pi F\|^2.
\tag{111.9}
$$

The spectral representation of this closed form yields (111.8), with
operator domain $W\operatorname{ran}(\Sigma|_{\mathscr K})$ on the
centered space. Constants supply the other summand. The representation
and spectral calculus are the mature intermediate supplies already
used in §103; no identity-at-zero on all of $\mathscr H$ is asserted.

For positivity one can use (111.4) directly. For $\alpha>0$ and
$0\le f\le1$, the unique minimizer in $\mathcal D$ of
$\mathcal E(u)+\alpha\|u-f\|^2$ is
$u=\alpha(H+\alpha)^{-1}f$. Clipping $u$ to $[0,1]$ decreases both
terms, so uniqueness forces $0\le u\le1$. Spectral calculus gives

$$
T(s)=\operatorname*{s-lim}_{k\to\infty}(I+sH/k)^{-k}.
\tag{111.10}
$$

Each factor preserves $[0,1]$, and the $L^2$-closedness of this order
interval proves the same for $T(s)$. Scaling and truncating nonnegative
$L^2$ functions gives positivity for all of them. Constants have zero
form energy and lie in the operator kernel, so $T(s)\mathbf1=\mathbf1$.
Symmetry then gives preservation of the integral; strong continuity
follows from the spectral theorem, including at zero. $\square$

**Theorem 111.4 (exact all-node correlations and the boundary limit).**
Fix $c,d\in\mathbb R$ and finitely supported $z,y\in\mathscr H$.
Use the corresponding fields on the actual finite nodes and their
boundary traces:

$$
f_n=c\mathbf1+J_nz,\quad g_n=d\mathbf1+J_ny,
\qquad F=c\mathbf1+Jz,\quad G=d\mathbf1+Jy.
\tag{111.11}
$$

Every field in (111.11) includes its declared root value and every
interior and terminal value. Put
$\bar f_n=c+\langle v_n,z\rangle$,
$\bar g_n=d+\langle v_n,y\rangle$,
$\bar F=c+\langle v,z\rangle$ and
$\bar G=d+\langle v,y\rangle$. Define the continuous multiplier

$$
h_s(x)=
\begin{cases}xe^{-s/x},&x>0,\\0,&x=0,\end{cases}
\quad(s\ge0),\qquad h_0(x)=x.
\tag{111.12}
$$

For every $n\ge0$ and $s\ge0$ the exact correspondence is

$$
\begin{aligned}
\langle g_n,S_n(s)f_n\rangle_{L^2(\mu_n)}
  &=\bar g_n\bar f_n+\langle y,h_s(\Sigma_n)z\rangle,\\
\langle G,T(s)F\rangle_{L^2(M)}
  &=\bar G\bar F+\langle y,h_s(\Sigma)z\rangle.
\end{aligned}
\tag{111.13}
$$

Moreover, for these fixed observables,

$$
\sup_{s\ge0}\left|
\langle g_n,S_n(s)f_n\rangle_{L^2(\mu_n)}
 -\langle G,T(s)F\rangle_{L^2(M)}\right|\longrightarrow0.
\tag{111.14}
$$

In particular it holds at $s=0$ and along every $s_n\to s\ge0$.
As $s\to\infty$ the boundary correlation tends to $\bar G\bar F$;
along $s_n\to\infty$ the finite correlations have the same limit as
$n\to\infty$. These claims are for the original Fibonacci family and
fixed finite-edge/cylinder observables. They assert no uniform recovery
over arbitrary original sources, no arbitrary changing finite-state
identification and no acquired node-count observation.

**Proof.**
Let $C_n=(I-\mathbf1\otimes\mathbf1)J_n$ with the projection taken
in $L^2(\mu_n)$. Then $C_n^*C_n=\Sigma_n$. On the actual edges it
is a bijection to the finite mean-zero node space: integration of
edge differences inverts it after centering. Its polar decomposition
is $C_n=W_n\Sigma_n^{1/2}$, with $W_n$ unitary between these spaces.
The finite form of $N_nL_n$ in the normalized node inner product is
exactly the original unit-edge energy:

$$
\langle u,N_nL_nu\rangle_{L^2(\mu_n)}
   =\sum_{\{p^-,p\}\in E_{T_n}}|u(p)-u(p^-)|^2.
\tag{111.15}
$$

For $u=C_nz$ this is $\|Q_nz\|^2$. Therefore, equivalently by
(103.3), its centered generator is
$W_n\Sigma_n^{-1}W_n^*$. Constants have generator zero, giving the
first equation in (111.13). Absent edge coordinates are annihilated
by $\Sigma_n$, as required. For $n=0,1$ there are no actual edges,
$f_n=c$, $g_n=d$, and the first equation reduces correctly to the
product of constants. The boundary equation remains the identity for
the fixed $F,G$ in (111.11). The boundary polar decomposition in
(111.8) gives the second equation. At zero, both equations use $h_0(\Sigma)=\Sigma$,
so they give the full inner products including their means.

Choose the uniform spectral bound $M_*>0$ from §103. On $[0,M_*]$,
$h_s$ is continuous for each $s\ge0$ and

$$
\|h_s-h_t\|_\infty\le|s-t|,\qquad
\|h_s\|_\infty\le M_*e^{-s/M_*}.
\tag{111.16}
$$

The first inequality follows by differentiating at $x>0$, where
$|\partial_sh_s(x)|=e^{-s/x}\le1$, and continuity at $x=0$.
The second is monotonicity of $xe^{-s/x}$ in $x$.
Norm convergence $\Sigma_n\to\Sigma$ in (98.6) and continuous
functional calculus give norm convergence of each $h_s(\Sigma_n)$.
A finite time net and the first bound in (111.16) make this uniform
on $[0,S]$, including zero. The second bound makes the remainder
$s\ge S$ uniformly small, proving uniformity for all $s\ge0$.
The means converge by $v_n\to v$. Substitution proves (111.14).
The spectral formula also gives continuity in $s$ and the asserted
infinite-time limits. The factor $N_n$ in (111.15) is essential;
no replacement of the counting carrier or closed operator occurs.
$\square$

**Theorem 111.5 (the exact first-cylinder energy and the two endpoint orders).**
Let $F_L=\mathbf1_{[L]}$, $F_R=\mathbf1_{[R]}=\mathbf1-F_L$.
Both are in $\mathcal A$, with means $a,b$ under the actual $M$.
Their exact energies are

$$
\mathcal E(F_L)=\mathcal E(F_R)=\frac14,
\qquad \mathcal E(F_L,F_R)=-\frac14.
\tag{111.17}
$$

On the finite original $T_n$ put
$f_{n,L}(x)=\mathbf1_{\{L\preceq x\}}$ and
$f_{n,R}(x)=\mathbf1_{\{R\preceq x\}}$. In particular both vanish
at the finite root. Write

$$
c_n(s)=\langle f_{n,R},S_n(s)f_{n,L}\rangle_{L^2(\mu_n)},
\qquad c(s)=\langle F_R,T(s)F_L\rangle_{L^2(M)}.
\tag{111.18}
$$

These are nonnegative. They satisfy $c_n(0)=c(0)=0$,
$c_n(s)\to c(s)$ uniformly for $s\ge0$, and

$$
\begin{aligned}
c(s)&=\frac{s}{4}+o(s)\quad(s\downarrow0),\\
\lim_{s\downarrow0}\lim_{n\to\infty}\frac{c_n(s)}s&=\frac14,\\
\lim_{n\to\infty}\lim_{s\downarrow0}\frac{c_n(s)}s&=0.
\end{aligned}
\tag{111.19}
$$

At each fixed $n\ge2$ the stronger finite endpoint is

$$
c_n'(0)=0,\qquad c_n''(0)=N_n,\qquad
c_n(s)=\frac{N_n}{2}s^2+O_n(s^3).
\tag{111.20}
$$

For $n=0,1$, $c_n$ is identically zero. The two ordered limits of
$c_n(s)$ itself are both zero; it is the normalized first-time
coefficient in (111.19) that fails to commute. Uniform convergence
of correlations in (111.14) does not imply uniform convergence of
their derivatives at zero.

**Proof.**
For any finite-energy extension $u$ of $F_L$, put
$x=u(\varnothing)$, $\ell=u(L)$ and $r=u(R)$. Conditional on $[L]$
and $[R]$, the suffix law is the same $M$. The descendant increments
therefore have constant traces $1-\ell$ and $-r$, respectively.
The constant-trace identity of Theorem 99.1 and $\|q\|=1$ give,
for any suffix increment vector $z$ with constant trace $d$,

$$
\|z\|^2\ge|\langle q,z\rangle|^2=d^2,
\qquad J(dq)=d\mathbf1.
\tag{111.21}
$$

Thus the complete extension energy obeys

$$
\begin{aligned}
\|Du\|^2
 &\ge(\ell-x)^2+(1-\ell)^2+(r-x)^2+r^2\\
 &\ge\frac{(1-x)^2}{2}+\frac{x^2}{2}\ge\frac14.
\end{aligned}
\tag{111.22}
$$

All inequalities are attained: choose $x=1/2$, $\ell=3/4$, $r=1/4$,
with strict-descendant increments $q/4$ in the left subtree and
$-q/4$ in the right subtree. The two root increments are $1/4$ and
$-1/4$. This specifies an actual $\ell^2$ increment vector, with
energy $1/4$, and trace $F_L$ on every end. It proves the first
energy; replacing $u$ by $1-u$ proves the right energy.
Linearity of minimizing increments gives $z_{F_R}=-z_{F_L}$,
because constants have zero increments, so their cross energy is
$-1/4$. The unit-resistance/equal-split calculation is the intermediate
supply of §99; (111.22) uses it on each declared biased cylinder,
without replacing the probability law by the equal-split law.

Apply (111.13) with $z=\delta_L$, $y=\delta_R$, $c=d=0$.
For $n\ge2$ their finite means are $N_{n-1}/N_n$ and $N_{n-2}/N_n$;
they add to $1-1/N_n$, not to one. The missing $1/N_n$ is precisely
the root outside the two finite cylinders. At the boundary the means
are $a,b$ and the two cylinders cover $\Omega$. In particular

$$
c(s)=ab+\langle\delta_R,h_s(\Sigma)\delta_L\rangle,
\qquad c(0)=ab+\langle\delta_R,\Sigma\delta_L\rangle=0.
\tag{111.23}
$$

For form-domain vectors the spectral theorem gives

$$
\lim_{s\downarrow0}\frac{\langle G,(I-T(s))F\rangle}{s}
       =\mathcal E(G,F).
\tag{111.24}
$$

Indeed the diagonal limit follows from
$(1-e^{-s\lambda})/s\to\lambda$, bounded above by $\lambda$,
with integrable form spectral mass; polarization gives the mixed
limit. Applying this to $F_L,F_R$, whose inner product is zero,
proves the first line of (111.19) and positivity for sufficiently
small positive time. Positivity at all times follows from the Markov
semigroup; the finite heat matrices have nonnegative entries as well.
Theorem 111.4 proves the uniform convergence and then the first
ordered limit.

For each actual $T_n$, $n\ge2$, write node point masses explicitly
as $e_{n,r}$, $e_{n,L}$ and $e_{n,R}$. The closed unit-edge law gives

$$
L_nf_{n,L}=e_{n,L}-e_{n,r},\qquad
L_nf_{n,R}=e_{n,R}-e_{n,r}.
\tag{111.25}
$$

Their first mixed energy is zero, since the two fields change on
different root edges. Their second mixed operator product is

$$
\langle f_{n,R},L_n^2f_{n,L}\rangle_{\rm counting}
 =\langle L_nf_{n,R},L_nf_{n,L}\rangle_{\rm counting}=1.
\tag{111.26}
$$

Taylor expansion of the finite $S_n(s)$, with the factor $1/N_n$
from $\mu_n$, gives (111.20). No bound uniform in $n$ is asserted
for the Taylor remainder. This yields the second ordered limit
in (111.19); the singleton cases follow directly. $\square$

**Definition 111.6 (a direct same-clock local-form realization).**
Such a realization consists of a locally compact separable metric
space $X$, a full-support Radon measure $m$, a regular symmetric
Dirichlet form $(\mathcal E_X,\mathcal D_X)$ on $L^2(X,m)$, and a
measure-space isomorphism from $(\Omega,M)$ to $(X,m)$ modulo null
sets. Let $U:L^2(M)\to L^2(X,m)$ be its pullback identification,
so it preserves products, order, integrals and $\mathbf1$. Require

$$
U\mathcal D=\mathcal D_X,\qquad
\mathcal E_X(UF,UG)=\mathcal E(F,G).
\tag{111.27}
$$

The form $\mathcal E_X$ is local in the following precise sense:
$\mathcal E_X(f,g)=0$ whenever $f,g\in\mathcal D_X$ have compact,
disjoint supports. Require in addition that $UF_L,UF_R$ have
representatives in $\mathcal D_X\cap C_c(X)$ with disjoint supports.
These are locality-applicable support and domain assumptions, not
consequences of disjoint measurable sets or of a unitary operator.
The propagation correspondence is the same-clock identity
$UT(s)=e^{-sH_X}U$ for every $s\ge0$, where $H_X$ is the operator
of $\mathcal E_X$. It follows from (111.27); if instead specified
as a premise, it must hold with this domain and support contract.
There is no additional interior carrier, elimination of interior
time, fitted metric, or change of the time parameter in this class.

**Theorem 111.7 (the cylinder cross term excludes that direct local class).**
No realization of Definition 111.6 exists. More generally, the same
obstruction holds for an isometric form-preserving identification
whose two images have domain and supports to which the stated locality
axiom applies, even without an onto measure-space isomorphism.

**Proof.**
The domain and support premises allow locality to be applied to the
two specified images, giving
$\mathcal E_X(UF_L,UF_R)=0$. Form preservation and (111.17) give
instead $\mathcal E_X(UF_L,UF_R)=-1/4$. This contradiction proves
the claim. If only same-clock semigroup intertwining is used to
express form preservation, isometry and (111.24) give the identical
cross-energy contradiction on those domain vectors. The nonzero
small-time transfer in (111.19) is the corresponding propagation
witness, after the actual source limit.

This obstruction does not apply when cylinder images have touching
supports, when their indicators are outside a proposed local form
domain, or when extra interior states or occupation-time changes
produce a nonlocal boundary trace. In particular an infinite tree
interior with the free-root energy is already used in (111.2) to
define the boundary trace; it is not a direct local form on the
boundary carrier. A local cable or spatial interior with such a
trace would require its own carrier, measure, trace, operation and
clock correspondence. The occupation trace in §108 concerns a
specified finite successor/old-set pair, with its own clock, and
does not supply that spatial correspondence. $\square$

**Assumption 111.8 (the distinct original-operation and physical bridges).**
A native interpretation of (111.13) retains the complete original
ordered source, its immutable INITIAL targets, same-source joint
histories, reached-address guards, full accessible state, permission
and refusal rules, and absorbing Stop of
[Native Leaf Depth Contact, Assumptions 1.2 and Definition 1.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md),
[Continuation I, Definitions 58.1 and 60.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md),
and Assumptions 106.3 and 109.3. All original whole-row targets,
including equality partitions and concrete exteriors when present,
are retained; a boundary amplitude or cylinder correlation is not
substituted for them. The law (111.1) specifies a comparison ensemble,
not permission to prepare it or to replace the unknown source by a
new INITIAL. The family $T_n$ remains a source-specific comparison
inside the full original domain.

Any additional execution realizing these fields and correlations
requires a typed same-source correspondence for preparation, action,
readout and joint chronology. Original-root $\mathsf{Read}$, forward
$\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$ do not provide a
heat actuator, probability preparation or cylinder amplitude port
by definition. The finite apparatus in Continuation I, §60 has its
own additional permissions and grounded Hamiltonian; it is not an
installed realization of the closed $L_n$ in (111.1). A command,
mathematical decoder or independent marginal realization does not
supply an actual accepted joint operation. Preparation, installation,
raw calls, actual address lengths, updates, arithmetic, authentication,
memory, retention and output remain separately charged under their
original contracts. Normalization by $N_n$ conveys no acquired source
size or index. Same-source legality and event costs in the ExactChart
contract of
[Fiber III, Definition 32.1](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_III.md)
and the immutable whole-target/own-endpoint distinction in
[Kbonacci, §§83–89](KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md)
retain their original scopes.

Theorems 111.2–111.5 establish the ordinary comparison boundary law
and its all-node correlation correspondence. They do not establish
the extra native-operation bridge just stated. Source-substitution
steps, $s$, acquired-experiment chronology and physical duration
remain distinct until their actual time correspondence is proved.
The existence of a spatial realization beyond Definition 111.6,
its metric or dimension, stable physical matter and physical-time
calibration remain unproved. No full-spectrum recovery or native
source-operation authority follows from (111.8).

## 111.99 追加锚（本行以下为增补区）

## 112. Exact native occurrence transport, coarse Apply nonclosure, and the INITIAL equality bill

This section fixes one complete acquired input on the full original branch
domain. It relates the actual source operations to their source-indexed
all-node occurrence objects, and distinguishes this relation from an
observer update on a coarse count/port response. The original task remains
the entire INITIAL row. Common-source lower bounds and paid epoch-zero
recovery compare actual read and literal-address coordinates on one run.

### 112.1 The complete acquired service, original row, and permission contract

**Definition 112.1 (the complete branch service).** Use the finite free ordered
source algebra and substitution of
[Native Leaf Depth Contact, Definitions 1.1--1.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md):
\[
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\]
The original root cut is \(P=\{\varepsilon\}\). Its actual complete row on
**every** \(u\in\mathcal T\) has reached list \((\varepsilon)\), exterior
\(\square_1\), and singleton partition \(\{\{1\}\}\). Denote this constant
row by \(R\). A root reply is a different object from this row.

Before entry, a public producer makes exactly one actual epoch-zero
\(\mathsf{Read}(\varepsilon)\) on every finite source and retains its literal
record. Consider its acquired output
\[
H_0=[(0,\varepsilon,\mathsf{branch})],\qquad H_{\rm rel}=[],\qquad N=0.
\]
The old row \(R\) is known from the root-cut definition and nonemptiness;
no whole-tree traversal is required to compute it. The producer's other
root outcomes retain alpha or beta rather than report branch. Under the
complete-cut premise of
[Acquired Relation History, Assumption 1.3](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md),
the entire entry state is a fixed recoverable encoding of
\((P,R,H_0,H_{\rm rel},N)\), common code and parameters. No source-bearing
cache, timing, address, length, count, control position, archive, permission,
or handle is omitted. The same original-root register is still at epoch zero.
Authentic entry and this complete access cut are premises, not a physical
erasure or preparation result.

Its exact original-source fiber is
\[
D=\{u\in\mathcal T:R_P(u)=R,\ r_u(\varepsilon)=\mathsf{branch}\}
 =\mathcal B:=\{\langle x,y\rangle:x,y\in\mathcal T\}.
\tag{112.1}
\]
Both directions hold: a source producing this retained output has branch
root; every branch source executes the same one-read schedule, gives that
output, and, conditional on the complete cut, has that same entry state.
There is no witness-family restriction or acquired size/index selector.
The pre-cut raw bill is one Read, zero updates and zero literal-address
length; its supplier paid-address set is \(\{\varepsilon\}\). Preparation,
certification, installation and access-cut prices are unspecified.

The original target cut is \(Q=\{L,R\}\). The entire target row is
\[
\mathsf{Row}(u)=R_Q(u)
 =\bigl((L,R),\ \langle\square_1,\square_2\rangle,\ \pi_Q(u)\bigr),
\quad
\pi_Q(u)=
\begin{cases}
\{\{1,2\}\},&u|_L=u|_R,\\
\{\{1\},\{2\}\},&u|_L\ne u|_R.
\end{cases}
\tag{112.2}
\]
Both addresses are reached on all of \(D\). The exterior has distinct
numbered holes in this reached order; the partition records equality of
their **entire ordered subtrees**. Subtree descriptions are possible acquired
evidence, not additional target fields. This is the full original row of
Acquired Relation History, Definition 1.1, equivalently the independent
exterior/partition record of `Observer.ActualCutPartitionDecoder` after
numbering its addresses. Absence supplies no fictitious hole.
The target is evaluated on INITIAL \(u\), after any later action too.

**Contract 112.1a (native actions and observed permissions).** The original
uncapped native contract, denoted \(G_{\rm nat}\), allows any finite-word
original-root \(\mathsf{Read}(p)\), serial same-register
\(\mathsf{Apply}\rho\), and absorbing \(\mathsf{Stop}\). Every Apply is
accepted and replaces the current register by its actual \(\rho\)-successor.
The four Read replies are alpha, beta, branch and absent; repeated and absent
Reads remain actual calls. This is the uncapped service of Native Leaf Depth
Contact, Definition 1.3, and Acquired Relation History, Assumption 1.3;
no refusal capability is inferred from that menu.

For a separately declared common guarded extension, fix a total effective
function
\[
G(\gamma,e,H)\in\{\mathsf{accepted},\mathsf{refused}\}.
\tag{112.2a}
\]
Here \(\gamma\) is a common source-independent parameter, \(e\) counts
actual accepted post-entry updates, and \(H\) is the complete chronological
native history of action addresses, four-valued replies, Apply statuses and
Stop. Every Apply attempt evaluates this function, logs its status as an
observation, and either executes exactly \(\rho\) and increases \(e\) by one,
or changes no register/epoch on refusal. Reads always return their actual
reply; Stop logs terminal and no suffix is executed. There are no other
status bits, source-dependent implementation/timing outputs or unlisted
scheduler states. In particular equal \((\gamma,e,H)\) entails equal status;
\(G\) has no access to the source or the mathematical occurrence object.
The all-accepted function is \(G_{\rm nat}\). A public fixed-cap guard
\(G_K=\mathsf{accepted}\) iff \(e<K\), including \(K=0\), is one extension;
it does not impose a cap on the original native contract. A history-dependent
guard may use already observed replies, and those replies remain observations.

The statements below hold for every fixed \(G\) satisfying this contract,
and therefore for the full original uncapped menu. They do not cover an
undisclosed source-dependent permission oracle. No original legal controller
is removed: a native controller sees acceptance on every actual Apply;
guarded controllers and their refusal observations have the separate scope
just declared. Local computation uses only common entry and actual history;
there is no equality, reset, clone, backward action, source-index, or limit
Read. The source-bearing occurrence metadata below is not free controller
advice.

The fixed coarse port set is
\[
\mathcal P=\{\varepsilon,L,R\}.
\tag{112.3}
\]
These addresses are reached on all of \(D\) and remain reached. The coarse
word scope uses exactly these three ports. The native equality controller
scope allows every finite address, including absent ones.

### 112.2 Exact all-node transport and the failure of coarse action descent

**Definition 112.2 (the source-indexed occurrence object).** For \(u\in D\)
and every integer \(e\ge0\), put
\[
s_e(u)=\rho^eu,\quad V_e(u)=V_{s_e(u)},\quad E_e(u)=E_{s_e(u)},
\quad \lambda_e(p)=s_e(u)|_p,\quad N_e(u)=|V_e(u)|.
\]
Every repeated occurrence is a distinct vertex. The exact object is
\[
\mathsf O_e(u)=\bigl(V_e,E_e,\lambda_e,N_e,L_e,\operatorname{port}_e\bigr).
\tag{112.4}
\]
Use counting inner products and the closed unit-edge operator
\(L_e=D_e^*D_e\) of §§92, 103 and 108. Let
\(R_e:\ell^2(V_e)\to\mathbb R^{\mathcal P}\) be restriction to the ordered
ports \((\varepsilon,L,R)\); \(R_e^*\) is zero extension from them. Define
\[
\operatorname{port}_e=
 \bigl(K_e:=R_eL_eR_e^*,\ (\deg_{E_e}(p))_{p\in\mathcal P},\ (1,1,1)\bigr).
\tag{112.4a}
\]
This is the actual principal compression, retaining degrees from **all**
edges, including edges leaving the port set. For every \(u\in D\),
\[
K_e=
\begin{pmatrix}
2&-1&-1\\
-1&1+2\mathbf1_{\{r_{s_e}(L)=\mathsf{branch}\}}&0\\
-1&0&1+2\mathbf1_{\{r_{s_e}(R)=\mathsf{branch}\}}
\end{pmatrix}.
\tag{112.4b}
\]
A reached nonroot leaf has degree one, a nonroot branch degree three,
and the branch root degree two. This compression is neither an induced
three-node star Laplacian nor a grounded or degree-normalized operator.

Old vertices retain their literal addresses:
\[
\iota_e:V_e\to V_{e+1},\quad p\mapsto p.
\tag{112.5}
\]
Distinguish the beta-**parent** set \(M_e\) from the born-**child** set \(B_e\):
\[
M_e=\{p\in V_e:\lambda_e(p)=\beta\},\quad
B_e=\{pL,pR:p\in M_e\},\quad \operatorname{par}_e(p\sigma)=p.
\tag{112.6}
\]
The actual disjoint unions are
\[
V_{e+1}=\iota_e(V_e)\sqcup B_e,\qquad
E_{e+1}=\iota_e^E(E_e)\sqcup\{(p,p\sigma):p\sigma\in B_e\}.
\tag{112.7}
\]
The old labels are not asserted unchanged: even an old leaf can become a
branch. Let \(J_e:\ell^2(V_e)\to\ell^2(V_{e+1})\) be zero extension;
\(J_e^*\) is old-coordinate restriction. Let \(I_e^E\) be old-edge zero
extension and \(T_e:\ell^2(B_e)\to\ell^2(E_{e+1})\) send a child coordinate
to its new parent-child edge. Orient edges away from the root. Let
\(H_e\) project onto \(M_e\), and
\(C_e:\ell^2(B_e)\to\ell^2(V_e)\) sum each child's value at its parent.
Thus \((C_e^*f)(p\sigma)=f(p)\). The typed gradient and adjoint squares are
\[
D_{e+1}J_e=I_e^ED_e-T_eC_e^*,\qquad
J_e^*D_{e+1}^*=D_e^*(I_e^E)^*-C_eT_e^*.
\tag{112.8}
\]
In the exact orders \(V_e\sqcup B_e\) and \(E_e\sqcup B_e\),
\[
D_{e+1}=
\begin{pmatrix}D_e&0\\-C_e^*&I\end{pmatrix},\quad
L_{e+1}=
\begin{pmatrix}L_e+2H_e&-C_e\\-C_e^*&I\end{pmatrix},
\quad C_eC_e^*=2H_e.
\tag{112.9}
\]
The zero-parameter old-set Schur complement is \(L_e\). If \(B_e\) is empty,
its identity block is the identity on the zero-dimensional space and the
same formulas hold. Likewise \(J_e^*J_e=I\) and \(R_{e+1}J_e=R_e\).
They do not say \(L_{e+1}J_e=J_eL_e\) or that ancestry intertwines heat.

**Definition 112.3 (words, exact execution, and coarse observation).** A finite
word has actions
\[
\mathsf{Read}(p)\ (p\in\mathcal P),\quad \mathsf{Apply}\rho,\quad
\mathsf{Stop}.
\tag{112.10}
\]
The word specifies an attempt, not its acceptance outcome. Execute from
\((0,\mathsf{alive},[])\) using Contract 112.1a; a suffix after Stop is
ignored. For the native unrestricted run replace \(p\in\mathcal P\) by any
finite address, with absent replies allowed. The chronological record is
\[
\mathsf{Run}_{u,G}(w)=(H,e,\mathsf{alive/terminal}),
\tag{112.11}
\]
including repeated calls, literal addresses, replies and every Apply status.
The **source-indexed** execution \((u,G,w)\) also determines \(\mathsf O_e(u)\)
and all birth/ancestry maps through accepted epochs. This is not a function
recovering \(u\) or \(\mathsf O_e(u)\) from \(H\) alone.

The endpoint coarse snapshot is
\[
\mathsf c_{u,G}(w)=
\bigl(e,N_e(u),|B_e(u)|,\operatorname{port}_e(u),
       \text{chronological Apply statuses and terminal flag}\bigr).
\tag{112.12}
\]
The complete coarse trace retains the entry snapshot, action tags/addresses
and this snapshot after each executed event; it erases the four-valued Read
labels and the INITIAL partition. In this three-port scope no absent reply
occurs. It retains repetitions and every acceptance, refusal and Stop.
Counts and operator snapshots are mathematical comparison observations;
no native count, operator, amplitude or extra address port is installed.

**Theorem 112.4 (source-indexed all-epoch and word correspondence).** For every
\(u\in D\), every \(e\ge0\), every fixed lawful \(G\), and every finite word,
(112.4)--(112.11) use precisely the actual same-source carrier and operations.
In particular, writing \(a_0,b_0\) for original alpha/beta leaf counts,
\[
\begin{aligned}
N_e&=2(a_0F_{e+1}+b_0F_{e+2})-1,\\
|M_e|&=a_0F_e+b_0F_{e+1},\qquad |B_e|=2|M_e|,\\
N_{e+1}&=N_e+|B_e|,\qquad |E_e|=N_e-1,\qquad |B_{e+1}|=N_e+1.
\end{aligned}
\tag{112.12a}
\]
All transport squares have the literal domains and adjoints displayed above;
projecting after an actual execution gives (112.12). No autonomous update
from the preceding coarse snapshot is asserted.

**Proof.** The three clauses of \(\rho\), by structural induction, retain
each branch edge and attach exactly the two children of each beta leaf.
Alpha becomes beta without a birth. Different leaf parents have disjoint
child addresses. This proves (112.5)--(112.7) at every finite iterate.
Old-edge differences of \(J_ef\) equal those of \(f\); on a new edge the
difference is \(-f(\operatorname{par}_e(p\sigma))\). This proves (112.8),
and taking adjoints proves its second square. On an arbitrary old/new field
\((f,g)\), the full incidence is \((D_ef,g-C_e^*f)\). Its adjoint product
is (112.9). Each beta parent has two columns of \(C_e\), hence
\(C_eC_e^*=2H_e\), and subtracting the new identity-block contribution
leaves \(L_e\). Degree counting gives (112.4b) without discarding edges.

The all-source leaf-block identities (108.9) give the first two counts,
including epoch zero and both singleton labels. The disjoint union gives
\(N_{e+1}=N_e+|B_e|\). A finite full binary tree has \((N_e+1)/2\) leaves;
each alpha or beta leaf produces exactly one beta leaf at the next epoch,
so \(|B_{e+1}|=N_e+1\). Connected tree edges number \(N_e-1\).
These structural facts also hold on singleton sources outside the service.

Induct on executed events of a word. Read records the actual current reply;
accepted Apply uses these source-indexed birth blocks and advances one epoch;
refused Apply leaves the object unchanged and logs refusal. Stop logs terminal
and executes no further suffix. Restricting the resulting actual object gives
the stated coarse trace. This induction carries the original source as a
parameter, not an inferred state supplied by the transcript. The finite
reversible old-set trace of §108 has this same Schur complement: every
new-child excursion returns to its own parent and adds no old-to-old edge.
Its time parameter is a comparison occupation clock, not native Apply duration.
\(\square\)

**Proposition 112.4a (faithful coarse Apply nonclosure).** On the unchanged
full \(D\) and uncapped \(G_{\rm nat}\), no function of (112.12) and an
accepted Apply determines its next coarse snapshot. Indeed take
\(x=\langle\alpha,\beta\rangle\), \(y=\langle\beta,\alpha\rangle\).
At entry they have the same \((e,N_e,|B_e|)=(0,3,2)\), degree vector
\((2,1,1)\), and matrix
\[
K_0(x)=K_0(y)=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix}.
\]
The same one accepted Apply has epoch/count/birth coordinates \((1,5,4)\)
on both, but the successor port diagonals are \((2,1,3)\) and \((2,3,1)\),
respectively. Both have the same observed accepted status. Thus one coarse
fiber splits under a genuine original operation. The same counterexample
works for a common guard accepting that attempt.

**Proof.** Alpha becomes a degree-one beta leaf; beta becomes a nonroot
branch with its parent and two children. Formula (112.4b) gives the two
different successor matrices. Equal inputs to a proposed function would
have to give equal outputs, a contradiction. The count pair alone does have
the update in (112.12a); its success does not repair the lost port labels.
A beta-port mask or source description could resolve the loss, but neither
belongs to (112.12) or is granted as an original operation. \(\square\)

### 112.3 All-word witness separation and its exact operator symmetry

**Theorem 112.5 (coarse traces miss the entire INITIAL equality row).** Put
\[
a=\langle\alpha,\beta\rangle,\quad b=\langle\beta,\alpha\rangle,
\quad u^\star=\langle a,a\rangle,\quad v^\star=\langle a,b\rangle.
\tag{112.13}
\]
These are actual members of the full fiber (112.1), with two leaves of each
label. Their target reached list and numbered exterior agree, but
\[
\pi_Q(u^\star)=\{\{1,2\}\},\qquad
\pi_Q(v^\star)=\{\{1\},\{2\}\}.
\tag{112.14}
\]
For all \(e\ge0\),
\[
N_e(u^\star)=N_e(v^\star)=4(F_{e+1}+F_{e+2})-1,\qquad
|B_e(u^\star)|=|B_e(v^\star)|=4(F_e+F_{e+1}),
\tag{112.15}
\]
and their exact principal port matrix and degrees are
\[
K_e=\begin{pmatrix}2&-1&-1\\-1&3&0\\-1&0&3\end{pmatrix},
\qquad (\deg(\varepsilon),\deg(L),\deg(R))=(2,3,3).
\tag{112.15a}
\]
For every fixed \(G\) of Contract 112.1a and every finite word (112.10),
their native histories and entire coarse traces coincide. This includes
repeated Reads, accepted and refused Apply attempts and terminal prefixes.
Their INITIAL rows remain different.

**Proof.** Apply (112.12a) with \(a_0=b_0=2\). Root and both child roots
remain branches, each nonroot child root having its parent and two children.
This gives (112.15a), retaining the exterior-edge degree contributions.
All three native Read replies are branch. Induct on events: common histories
and epochs give identical statuses by (112.2a); acceptance advances both,
refusal neither. Counts and matrices coincide at either resulting epoch.
Stop suppresses both suffixes. This proves all finite words, not merely a
fixed number of updates. The different original subtrees in (112.13) prove
(112.14). The statement is a witness separation, not the false all-domain
coarse successor law refuted by Proposition 112.4a. \(\square\)

There is also a genuine source-indexed comparison symmetry. At each epoch
let \(\psi_e:V_e(u^\star)\to V_e(v^\star)\) fix the ports and every
left-subtree address, and exchange \(RLs\) with \(RRs\) for each suffix
\(s\). The actual leaf expansions below those two prefixes are exchanged,
so this is a bijection preserving native root replies, oriented edges,
counting mass and unit conductance. It need not preserve the order at \(R\)
or the whole ordered subtree \(\lambda_e(R)\). Let \(S_e\) be its node
permutation, \(S_e^E\) its edge permutation, and \(W_e\) its born-child
permutation. Directly from unchanged suffixes and parents,
\[
\begin{aligned}
D_e(v^\star)S_e&=S_e^ED_e(u^\star),&
L_e(v^\star)S_e&=S_eL_e(u^\star),\\
S_{e+1}J_e(u^\star)&=J_e(v^\star)S_e,&
S_eC_e(u^\star)&=C_e(v^\star)W_e,\\
R_e(v^\star)S_e&=R_e(u^\star).&&
\end{aligned}
\tag{112.15b}
\]
For example a born child of a beta parent maps to the same suffix child of
the exchanged beta parent, which proves the parent and birth square; edges
prove the gradient square. Taking adjoints and products gives the operator
square. Finite matrix power series then give
\(e^{-tL_e(v^\star)}S_e=S_ee^{-tL_e(u^\star)}\) for every comparison
\(t\ge0\), including \(t=0\). This retains all-node states and masses.
It does not identify \(e^{-tK_e}\) with \(R_ee^{-tL_e}R_e^*\), give an
ancestry heat intertwiner, or add heat to the native alphabet.

This permutation is a mathematical witness, never a legal swap of ordered
sources. In particular the original \(\mathsf{Read}(RL)\) at epoch zero
distinguishes the two sources. Three-port indistinguishability does not
hold for all native addresses, nor acquire the exact operator from a run.

### 112.4 The universal same-run native equality bill

**Definition 112.6 (INITIAL leaf cones and coverage).** Let \(B_h\) be the
perfect ordered binary tree of depth \(h\), with every leaf alpha, and put
\[
U_h=\langle B_h,B_h\rangle,\qquad h\ge0.
\tag{112.16}
\]
The symbol \(B_h\) here is a tree, distinct from the epoch-indexed child set
\(B_e(u)\). Its INITIAL leaves have length \(h+1\). For any initial leaf
address \(x\), define its address cone as every finite word with prefix
\(x\), whether or not reached at the current epoch. A Read covers \(x\)
iff its literal requested address has that prefix. Distinct INITIAL leaf
cones are disjoint. An absent reply inside one cone still covers at most
that one leaf; it is not a fictional subtree.

**Lemma 112.7 (one-address locality).** For every finite original source,
initial leaf \(x\), every \(e\ge0\) and address \(p\) not prefixed by \(x\),
flipping the label at \(x\) leaves \(r_{\rho^eu}(p)\) unchanged. Each literal
address belongs to at most one INITIAL leaf cone.

**Proof.** Expansion acts independently below each original leaf, preserving
all original branch brackets and addresses. More explicitly \(\rho^eu\)
is the original branch skeleton with the leaf at \(z\) replaced by
\(\rho^e\alpha\) or \(\rho^e\beta\) at the same prefix \(z\); induction on
\(e\) proves this substitution description. A path strictly above \(x\)
ends at a fixed original branch; a path outside its cone follows another
fixed branch or another leaf block. If it exits that other block its absent
reply is fixed by that block too. Thus none depends on the flipped label.
Prefix-freedom of original leaves proves disjointness. \(\square\)

**Theorem 112.8 (universal same-equality-source lower bounds).** Fix any \(G\)
of Contract 112.1a. For **every** deterministic effective adaptive controller
\(A\) using the complete entry and unrestricted native address menu, if it
terminates with the exact full row (112.2) on every \(u\in D\), then, for
every integer \(h\ge0\), its one actual terminal run on \(U_h\) satisfies
\[
q_A(U_h)\ge2^{h+1},\qquad
\ell_A(U_h)\ge(h+1)2^{h+1}.
\tag{112.17}
\]
Here \(q_A\) counts all post-entry raw Reads, repeated and absent included;
\(\ell_A\) sums their literal lengths. The pre-cut root Read is accounted
separately and covers no INITIAL leaf. Apply attempts, statuses, accepted
updates and local computation are not Reads. This includes the uncapped
original contract without imposing any uniform finite update or work bound.

**Proof.** Fix the finite actual terminal run on \(U_h\). If some initial
leaf \(x\) is uncovered, flip only its alpha label to beta, giving
\(V_{h,x}\in D\). Its root reply and complete retained entry are the same;
exactly one of the two original subtrees differs from its mate, so its
INITIAL target partition differs from that of \(U_h\).

Induct on the actual transcript. The same common entry and equal histories
make deterministic computation choose the same next operation and address.
For any Read in this run, no requested address has prefix \(x\), so Lemma
112.7 gives the same reply at the common accepted epoch, even for repeated
or absent calls. Contract (112.2a), using these identical histories, gives
the same status on each Apply attempt. Both registers therefore advance
one actual epoch or neither does, and the status observations agree. Stop
has the same output and no executed suffix. This replays the whole finite
run on \(V_{h,x}\), contradicting correctness on both different rows.
There is no intervention executed on \(U_h\): the flipped tree is a second
actual member of the original competitor domain.

Every INITIAL leaf must consequently be covered on that one run. One Read
covers at most one leaf; all \(2^{h+1}\) leaves require distinct covering
addresses. Each such address has literal length at least \(h+1\). Sum their
costs within that same run to obtain both bounds, simultaneously. No freely
supplied count, source index, epoch advice, source-dependent permission,
inverse action, or separately selected coordinate maximizer is used.
\(\square\)

The endpoints include \(h=0\) and both parities. The original uncapped
claim quantifies over all its lawful controllers, not a sampled family.
The guarded-extension claim is conditional on its explicitly observed
history-only statuses; an unspecified physical guard is not certified here.

### 112.5 Epoch-zero acquisition, supplier attribution, and exact resource endpoints

**Definition 112.9 (the immutable supplier and its separate consumer).**
Reuse `ActualTreeReadoutAcquisition` only for its four-valued immutable
address readout, history-only `acquisitionStep`/`frontier`, actual
`acquisitionTrace`, report-only `restore`, and distinct-address charge
\[
\operatorname{paid}(h)=\{p:(p,r)\text{ occurs in }h\},\qquad
k(h)=|\operatorname{paid}(h)|.
\tag{112.18a}
\]
Its original `Policy` returns an address or a Boolean, and its `Strategy`
task is membership in the third actual substitution image. That Boolean
task, immutable source and payment rule remain unchanged. The acquisition
phase can be consumed separately under the native controller contract;
the equality row consumer below is not a supplier `Strategy` for a changed
task. No Apply, refusal, authentication or physical-duration supplier is
inferred from that immutable-query API. See also
[Continuation I, §58.11](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).

At the authentic \(N=0\) entry of Definition 112.1, keep the register static.
Start the supplier acquisition frontier from its **own empty phase history**
and pending root. Request the actual root, pop each requested address, and
push its left then right children only after an actual branch reply. Thus
the root is an actual later raw Read even though the pre-cut branch reply
is retained. Use the same reply-driven DFS preorder as `acquisitionTrace`;
no unacquired size, fuel or tree description is supplied to the controller.
At completion the phase history is
\[
\mathsf{Hist}(u)=((p,r_u(p)):p\in V_0(u)\text{ in preorder}).
\tag{112.18}
\]
Restore the description solely from these acquired reports, compare the
two finite ordered descriptions below \(L,R\), and return exactly (112.2).
This local comparison is purchased evidence, not an unknown equality port.

Put
\[
S(u)=|V_0(u)|,\qquad \Lambda(u)=\sum_{p\in V_0(u)}|p|.
\tag{112.19}
\]
The actual native post-entry coordinates and the supplier phase charge are
\[
(q,a,\ell,k_{\rm phase})(u)=(S(u),0,\Lambda(u),S(u)).
\tag{112.20}
\]
Here \(a=0\) means no Apply attempt or accepted update. All phase addresses
are fresh within that phase; this is why its distinct charge equals its raw
Read count. For arbitrary native repeated calls those coordinates differ,
and (112.17) is about raw calls and literal lengths, not the supplier's
original Boolean strategy cost.

Cache scope at the pre-cut/post-entry boundary is explicit. Let
\(h_{\rm pre}=[(\varepsilon,\mathsf{branch})]\) and
\(h_{\rm post}=\mathsf{Hist}(u)\). Then
\[
\begin{aligned}
q_{\rm pre}=1,&\quad q_{\rm post}=S,\quad q_{\rm total}=S+1,\\
\ell_{\rm pre}=0,&\quad \ell_{\rm post}=\ell_{\rm total}=\Lambda,\\
k(h_{\rm pre})=1,&\quad k(h_{\rm post})=S,\quad
k(h_{\rm pre}\mathbin{+\!+}h_{\rm post})=S.
\end{aligned}
\tag{112.20a}
\]
If one immutable-source paid-address cache spans both phases, the incremental
post-entry distinct charge is therefore \(S-1\), and the cumulative charge
is \(S\). If fees are assessed separately on the two empty logical phase
ledgers, the two phase charges are \(1,S\), totaling \(S+1\). These are
the two declared history scopes of the same paid-set formula, not a promise
of a supplier cache reset, refund, or interphase tariff. The supplier alone
does not choose between them. The retained pre-cut root report and the
later raw root call count twice as raw events in either scope. A cache hit
does not invent a second paid address; a locally simulated cache lookup is
not a raw native Read. Such a lookup could save that raw call, but is not
the root-first schedule being compared here. These scopes are lawful only
on the same authentic immutable \(N=0\) source; an old-version report is
not a cache for a later substituted version.

Post-entry record counts are \(S\) phase events. Retaining both complete
chronologies gives \(S+1\) events with the repeated root; a deduplicated
address-value archive has \(S\) entries. In the declared bookkeeping unit
of one push or pop per address, DFS makes \(2S\) stack operations including
the initial push; comparing paired constructors uses at most \(S\) visits.
These are record/operation counts, not byte, instruction, duration or monetary
prices. Source preparation, root/epoch authentication, access cut, archive
bytes/protection, address generation, local computation, output encoding,
physical duration and amplitude/actuator preparation remain **unpriced**
unless an actual separate supplier defines them. No matched physical resource
vector or clock follows from naming those quantities.

**Theorem 112.10 (full-domain recovery and matching read/address order).**
For every \(u\in D\) and every \(G\) of Contract 112.1a, the static schedule
of Definition 112.9 terminates, queries only reached nodes at authentic epoch
zero, and returns the entire original row (112.2). On the same sources
\(U_h\), for all \(h\ge0\),
\[
S(U_h)=2^{h+2}-1,\qquad \Lambda(U_h)=h\,2^{h+2}+2.
\tag{112.21}
\]
For every controller \(A\) satisfying Theorem 112.8 under that same entry,
target and contract,
\[
\begin{aligned}
2^{h+1}&\le q_A(U_h),& S(U_h)&<2\cdot2^{h+1},\\
(h+1)2^{h+1}&\le\ell_A(U_h),&
\Lambda(U_h)&\le2(h+1)2^{h+1}.
\end{aligned}
\tag{112.22}
\]
Thus the native upper schedule matches the universal lower orders in the
post-entry raw-read and literal-address coordinates, respectively
\(\Theta(2^h)\) and \(\Theta((h+1)2^h)\). No matching assertion is made
about unpriced coordinates or the supplier's different Boolean task.

**Proof.** Structural induction on a finite tree proves the history-only
frontier visits root, then the whole left subtree, then the whole right,
with each node exactly once. Only branches add children, so every queued
node is reached. The same induction shows that `restore` reads the retained
leaf labels and pairs the restored children to reconstruct the exact ordered
syntax. A depth/fuel bound may be calculated from acquired history length
for this restoration; it is not initial advice. Each node is pushed and
popped once, giving \(2S\) stack operations in the stated unit. The ordered
comparator visits each pair at a common relative address at most once,
stopping at the first label or constructor mismatch. Its visits are at most
\(\min(|V_{u|_L}|,|V_{u|_R}|)\le S\). Local comparison produces precisely
the partition, and the two reached holes and numbered exterior are unchanged.
Since no Apply is issued, the epoch-zero immutable supplier
and INITIAL native register are the same source throughout, independently
of any lawful guard. The finite histories give (112.19)--(112.20a).

The perfect tree \(U_h\) has nodes at depths \(0,\ldots,h+1\), hence
\[
S(U_h)=\sum_{j=0}^{h+1}2^j=2^{h+2}-1,\qquad
\Lambda(U_h)=\sum_{j=0}^{h+1}j2^j=h2^{h+2}+2.
\]
The depth sum follows by induction, including \(h=0\). The lower sides
of (112.22) are the same-run law (112.17). The upper Read ratio is
\(2-2^{-(h+1)}\); the literal ratio is
\(2h/(h+1)+2/((h+1)2^{h+1})\le2\), including the value one at \(h=0\).
For that endpoint the lower bill is \((2,2)\), DFS post-entry bill \((3,2)\),
total raw bill four, phase distinct charge three, and cumulative cached
charge three with post-entry increment two. The arithmetic compares the
same original source and preserves each unit separately. \(\square\)

Sourcewise termination is not a uniform finite profile:
\(\sup_{u\in D}S(u)=\sup_{u\in D}\Lambda(u)=\infty\), as (112.21) shows.
Neither comparison counts nor post-acquisition syntax grants free entry
advice or a native heat actuator.

### 112.6 Finite verification scope, reused owners, and remaining bridges

Finite exact checks of these literal definitions have the following scope:

- All 1,446 labelled trees of maximum INITIAL depth at most three, including
  both singleton leaves and all 1,444 branch sources: both input-fiber
  directions, full numbered-hole rows, actual DFS histories and restoration.
  Epochs zero through four give 7,230 successor cases, checking actual node
  and child sets, all 280,264 old-coordinate gradient/adjoint columns and
  degree entries, the full incidence/closed block, Schur complement and
  typed port squares, including empty born blocks.
- The witness pair at epochs zero through eight: nine full graph/operator,
  old-inclusion and birth-parent squares, with full-operator port moments
  of orders zero through four. All 19,531 action words of lengths zero
  through six over the exact five-letter alphabet (112.10) are checked
  under five fixed guards: all-accepted, caps zero and two, acceptance on
  an even number of prior Apply attempts, and refusal iff the last native
  event is a Read with branch reply. These are 97,655 paired word/guard
  executions, with statuses as outputs; 6,928 contain both acceptance and
  refusal, 63,525 have suppressed terminal suffixes and 41,775 have repeated
  Reads. The all-domain nonclosure example is checked separately.
- For every one-leaf flip of \(U_h\), \(h=0,\ldots,5\), epochs
  zero through six and all addresses of lengths zero through \(h+4\):
  126 competitors and 610,638 address/epoch/flip cases, including absent
  replies. Each competitor has the same entry and a different INITIAL row;
  every requested address outside its flipped cone has unchanged reply.
- Exact DFS/read/address/cache endpoints on \(U_h\), \(h=0,\ldots,10\),
  including both parities and the repeated pre/post-cut root. In addition,
  420 executions of two history-driven sample controllers use repeated
  and absent Reads, static or common capped Apply, and report-only recovery.
  These sample controllers do not enumerate the universal controller class.

The executed finite assertions have no failed case. The arithmetic bindings
for the general and witness counts and DFS sums are extracted from the
literal formulas (112.12a), (112.15) and (112.21); actual recursive sources,
edge incidences and report histories supply the comparison values. The
standalone check program is outside all repositories. Finite verification
is not a kernel certificate or a physical permission realization.

The general statements rely on the ordinary structural and same-run proofs
above: all finite sources/epochs in Theorem 112.4, all finite three-port
words for every fixed lawful guard in Theorem 112.5, all effective total
adaptive original controllers under the named entry/status contract in
Theorem 112.8, and all branch sources in Theorem 112.10. Finite tests do
not establish those universal quantifiers or a physical permission scheduler.

The row/service owners are Native Leaf Depth Contact and Acquired Relation
History. The immutable acquisition/frontier/restore and distinct-address
payment owner is ActualTreeReadoutAcquisition, with its original Boolean
task unchanged. The all-source occurrence/count/trace owners are §§92, 103
and 108. The reversible trace/conductance intermediates remain the cited
Beltrán--Landim, *Tunneling and Metastability of Continuous Time Markov
Chains*, §6.1, Propositions 6.1/6.3, and Aldous--Fill, Chapter 3, §2,
equation (3.16), with finite connected recurrent successors, nonempty old
support, unit edge rates and restricted counting mass. No independent
reproof, new literature priority or broader physical supply is attributed
to those intermediates.

The substantive ordinary synthesis is the source-indexed native occurrence
relation together with the faithful coarse Apply nonclosure, all-word
three-port equality separation, same-run adaptive INITIAL equality bill,
and its authentic epoch-zero read/address matching upper route. The exact
source-indexed projection is available only with its actual source parameter;
a coarse response fiber cannot silently supply that parameter. General
signed-fiber lifting, acquired full-state propagation and a native heat
operation remain separate missing bridges.

No Lean, Blueprint, Reg, ingestion, registration, freezing, judge, CI,
spatial dimension, stable matter, physical preparation/actuation, clock,
full-spectrum acquisition, global novelty or kernel truth is claimed.
The accepted source-step count \(e\), semigroup and occupation comparison
time, paid acquisition chronology and physical duration remain distinct.
The complete through-2027 why-three programme remains active; this finite
repair is not its completion criterion.

## 112.99 追加锚（本行以下为增补区）

## 113. The original-tree boundary kernel, acquired scale, and INITIAL cut rows

### 113.1 All occurrences of every original source

**Definition 113.1 (source, scale and descendant cylinders).** Retain the
entire free ordered algebra $\mathcal T$, the actual substitution $\rho$,
four-valued Reads and complete INITIAL rows of Definition 112.1 and
Contract 112.1a. Write $a(u),b(u)$ for the original alpha/beta leaf counts,
$\ell(u)=a(u)+b(u)$ and

$$
W(u)=a(u)+\varphi b(u),\qquad \varphi=(1+\sqrt5)/2,
\qquad T_k=\rho^k\alpha.
\tag{113.1}
$$

Thus $W(\alpha)=1$, $W(\beta)=\varphi$ and
$W(\langle x,y\rangle)=W(x)+W(y)$. Use the address space and
$s(p)=\#_L(p)+2\#_R(p)$ of (98.1), with $s(\varepsilon)=0$.
At each $n\ge0$, put mass $1/N_n(u)$ at **every** actual node of
$\rho^n u$, where $N_n(u)=|V_{\rho^n u}|$. Denote this finite counting
probability by $\mu_{u,n}$ and its reached-descendant mass by
$m_{u,n}(p)=\mu_{u,n}\{x:p\preceq x\}$. In particular
$m_{u,n}(\varepsilon)=1$. These probabilities are on finite addresses;
the boundary probabilities below are on $\Omega=\{L,R\}^{\mathbb N}$.

**Theorem 113.2 (exact finite masses and their pointwise boundary).** For
every $u\in\mathcal T$ and $n\ge0$, the supplier (108.9) gives

$$
N_n(u)=2\bigl(a(u)F_{n+1}+b(u)F_{n+2}\bigr)-1.
\tag{113.2}
$$

For an originally reached $p$, including any internal node or terminal,
write $u_p=u|_p$. Then

$$
m_{u,n}(p)=\frac{2(a(u_p)F_{n+1}+b(u_p)F_{n+2})-1}{N_n(u)},
\qquad \lim_{n\to\infty}m_{u,n}(p)=\frac{W(u_p)}{W(u)}.
\tag{113.3}
$$

If $p$ is originally absent, there is a unique original terminal $q$
strictly preceding $p$; write $p=qr$ with $r\ne\varepsilon$, and put
$j=0$ for an alpha at $q$, $j=1$ for a beta there. Define
$d=n+j-s(r)$. The exact birth/reach rule and mass are

$$
\begin{aligned}
p\in V_{\rho^n u}
&\iff d\ge0\ \text{and}\ n+j-s(r^-)\ge2,\\
m_{u,n}(p)
&=\begin{cases}(2F_{d+1}-1)/N_n(u),&p\text{ reached},\\
0,&p\text{ absent},\end{cases}\\
\lim_{n\to\infty}m_{u,n}(p)&=\frac{\varphi^{j-s(r)}}{W(u)}.
\end{aligned}
\tag{113.4}
$$

A reached such node is alpha for $d=0$, beta for $d=1$, and internal
for $d\ge2$. At an original terminal use the same classification with
$d=n+j$; original internal nodes remain internal. Every reached node,
including the root and each terminal, has point mass $1/N_n(u)$; absent
nodes have point mass zero. All fixed-address point masses tend to zero.
There is a unique boundary probability $\nu_u$ with cylinder masses
equal to the limits in (113.3)--(113.4), and $\nu_u([\varepsilon])=1$.

Proof. The original $\ell(u)-1$ internal nodes keep their addresses, and
each original terminal is replaced, at its own address, by $T_{n+j}$.
This is the original skeleton decomposition used in (108.9), not a
restriction to the single-leaf orbit. An original subtree is therefore
exactly $\rho^n u_p$, giving (113.3). Below a terminal the reached
criterion, residual labels and subtree $T_d$ are precisely Theorem 98.2;
its last-parent condition includes the asymmetric left/right birth
endpoints. Its actual subtree size is $2F_{d+1}-1$.
For a fixed original $u$, Binet's formula gives

$$
\varphi^{-n}N_n(u)\longrightarrow \frac{2\varphi}{\sqrt5}W(u)>0.
\tag{113.5}
$$

Taking ratios proves all displayed limits. This includes both singleton
sources, $n=0,1$, root mass one, every initially missing address, and the
first reached alpha/beta endpoints. For every fixed depth $h$,

$$
\mu_{u,n}\{x:|x|<h\}\le(2^h-1)/N_n(u)\longrightarrow0.
\tag{113.6}
$$

At each finite node the exact identity is
$m_{u,n}(p)=\mu_{u,n}(\{p\})+m_{u,n}(pL)+m_{u,n}(pR)$.
Consequently the limiting masses have no finite-address remainder.
The probability explicitly constructed in Definition 113.3 realizes
them; its values on cylinders determine it uniquely. The calculation
counts internal and terminal occurrences with the same actual divisor;
it never substitutes a terminal-only probability. $\square$

### 113.2 The measure value and the actual accepted substitution

**Definition 113.3 (boundary value without description syntax).** Reuse
the Bernoulli probability $M$ of (98.3), so $M([p])=\varphi^{-s(p)}$.
Let $\mathcal L(u)$ be the original terminal-address antichain, and
$j(q)\in\{0,1\}$ its terminal label as above. Define

$$
\nu_u=\sum_{q\in\mathcal L(u)}
 \frac{\varphi^{j(q)}}{W(u)}(\omega\mapsto q\omega)_*M,
\qquad
f_u=\frac{d\nu_u}{dM}
 =\frac{\varphi^{s(q)+j(q)}}{W(u)}\quad\text{on }[q].
\tag{113.7}
$$

The original leaves partition $\Omega$; their weights sum to $W(u)$.
Thus this is a probability and a positive finite cylinder density.
Above original leaves its cylinder masses sum the weights of that
original subtree; below one leaf they multiply by $M([r])$. These are
exactly (113.3)--(113.4). The retained object is the **measure value**,
or equivalently the density modulo $M$-almost-everywhere equality.
An unreduced list of original leaf cylinders is not additional retained
information. If a finite density description is used, identify equal
functions: two sibling cylinders with the same constant may merge,
recursively. The resulting maximal constant cylinders are unique, since
every cylinder has positive $M$ mass and the original density is finite.

**Theorem 113.4 (invariance and scale action).** On the full source domain,

$$
\nu_{\rho u}=\nu_u,\qquad W(\rho u)=\varphi W(u).
\tag{113.8}
$$

Proof. The actual leaf-count transformation is $(a,b)\mapsto(b,a+b)$;
$\varphi^2=\varphi+1$ gives the scale identity. An original alpha at
$q$ becomes beta at $q$: both the numerator and denominator of its
density multiply by $\varphi$. An original beta at $q$ becomes the
ordered beta/alpha pair at $qL,qR$. The two new numerators are
$\varphi^{s(q)+2}$ and $\varphi^{s(q)+2}$, while the denominator is
$\varphi W(u)$; both give the old value
$\varphi^{s(q)+1}/W(u)$ throughout $[q]$. The original branch skeleton
is unchanged. Hence the density functions agree, although their
unreduced syntax need not agree. $\square$

### 113.3 Exactly the lost phase and the scale that restores it

**Theorem 113.5 (injective source representation and exact kernel).** The map
$\mathcal J:u\mapsto(\nu_u,W(u))$ is injective, with the actual substitution
represented on its attained image by $(\nu,w)\mapsto(\nu,\varphi w)$.
For all original finite sources $u,v$,

$$
\nu_u=\nu_v
\iff \exists n,m\ge0:\rho^n u=\rho^m v.
\tag{113.9}
$$

More precisely, on equal-measure sources $W(v)/W(u)=\varphi^k$ for a
unique $k\in\mathbb Z$. If $k\ge0$ then $v=\rho^k u$; if $k<0$ then
$u=\rho^{-k}v$. Thus each boundary fiber is a single chain of actual
forward iterates, starting at a unique source with no predecessor.

Proof. A finite source has $W=1$ exactly for alpha, $W=\varphi$ exactly
for beta, and $W\ge2$ exactly for a branch. For a branch
$u=\langle x,y\rangle$, the measure and scale give

$$
W(x)=W(u)\nu_u([L]),\quad W(y)=W(u)\nu_u([R]),\quad
\nu_x([p])=\frac{\nu_u([Lp])}{\nu_u([L])},\quad
\nu_y([p])=\frac{\nu_u([Rp])}{\nu_u([R])}.
\tag{113.10}
$$

Both child masses are positive. Induction on the original finite tree
therefore proves that equal pairs have equal root constructor, equal
child pairs and equal children. This uses only measure values and scale,
not the leaf partition of a density description. It also gives a finite
reconstruction on the attained image: at an original reached $p$ the
subtree scale is $W(u)\nu_u([p])$, and reconstruction stops at scales
$1$ or $\varphi$. It makes no claim about arbitrary unattained pairs.

Suppose now that $\nu_u=\nu_v$. Choose a cylinder $[z]$ deeper than both
original trees. On it each density in (113.7) is a single constant,
say $\varphi^A/W(u)$ and $\varphi^B/W(v)$, with integer $A,B$.
Equal measures and $M([z])>0$ force those constants to agree, so
$W(v)/W(u)=\varphi^{B-A}$. Put $k=B-A$. For $k\ge0$, (113.8) gives
$\mathcal J(\rho^k u)=\mathcal J(v)$; injectivity gives $\rho^k u=v$.
For $k<0$ reverse the roles. Conversely, equality of any two actual
forward iterates implies equal measures by (113.8). This proves (113.9)
without an abstract substitution recognizability premise.
The same injective representation and scale action show that $\rho$ is
injective; predecessor steps, when they exist, divide $W$ by $\varphi$.
Since every finite source has $W\ge1$, their number is finite, and the
least predecessor is unique. Its forward chain is the whole fiber.
In particular $\alpha,\beta,T_2,T_3,\ldots$ all have measure $M$,
while their scales are $1,\varphi,\varphi^2,\varphi^3,\ldots$.
The measure erases source-step phase; its unreduced syntax cannot restore
that phase. The acquired original scale can. $\square$

### 113.4 Complete INITIAL rows on the two full domains

**Definition 113.6 (factorization of the authentic row).** For a finite
prefix-free $Q$, including $\varnothing$ and the root cut, let $R_Q(u)$
be exactly Sparse Literal History Transport, Definition 59.1, equivalently
Native Alpha Recut Memory, Definition 1.2. Its reached holes are
$I_Q(u)=Q\cap V_u$ in lexicographic order; its concrete exterior retains
all remaining ordered brackets and leaf labels; its complete partition
equates holes exactly when their entire original subtrees agree.
An absent address produces no hole. On $D=\mathcal T$ or on the entire
authentic branch domain $D=\mathcal B$ of (112.1), factorization means
there exists a value function $F_Q$ on the attained boundary measures
such that $R_Q(u)=F_Q(\nu_u)$ for **every** $u\in D$.
This target is always INITIAL $u$, regardless of later accepted updates.

**Theorem 113.7 (exhaustive INITIAL changed-cut classification).** The exact
classifications are

$$
\begin{array}{c|c}
D&Q\text{ for which the whole }R_Q\text{ factors through }\nu\\ \hline
\mathcal T&\{\varepsilon\}\\
\mathcal B&\{\varepsilon\}\ \text{or}\ \{L,R\}.
\end{array}
\tag{113.11}
$$

Empty cuts fail in both domains. On $\mathcal B$, the retained value for
$Q=\{L,R\}$ is the entire row (112.2), including its equality flag.
Writing $t=\nu_u([L])$ and using the two conditional measures in
(113.10), that flag is explicitly

$$
u|_L=u|_R\iff t=\tfrac12\ \text{and}\ \nu_{u|_L}=\nu_{u|_R}.
\tag{113.12}
$$

Proof. The root row is constant for every nonempty original source:
one reached root hole, exterior $\square_1$, and one class.
For any other prefix-free $Q$, the root is not in $Q$. On the full
domain the sources alpha and beta have equal measure $M$, every such
cut address is absent in both, and the concrete exteriors are the
different labelled singletons. This rejects every other $Q$, including
the empty cut.

On the branch domain, $u=\langle x,y\rangle$ always has both child
addresses reached. For $Q=\{L,R\}$ its reached list and exterior are
fixed, and (113.10) gives the child weights. If $t=1/2$, they agree;
equal conditional measures then give $x=y$ by Theorem 113.5. The reverse
implication is immediate. This proves (113.12) and the complete row
factorization, with distinct numbered holes even in the equal case.
Conditional measures alone would be insufficient: alpha and beta have
the same measure but unequal weights.

For every remaining $Q$ without the root, prefix-freeness implies that
at least one of $L,R$ is not in $Q$. Compare the actual branch sources
$u=\langle\alpha,\alpha\rangle$ and $v=\rho u=\langle\beta,\beta\rangle$.
Their measures agree. Each of $L,R$ belonging to $Q$ is a reached hole;
all deeper cut addresses are absent in both sources. An immediate child
not belonging to $Q$ remains a concrete alpha in the first exterior and
a concrete beta in the second. The complete rows therefore differ.
If both children belong to $Q$, prefix-freeness forces $Q=\{L,R\}$.
This rejects all other cuts and retains the complete branch domain,
rather than selecting a smaller family. In particular an empty cut
returns the full concrete source and is not invariant. $\square$

**Proposition 113.8 (births, equality and operations do not change the target).**
For $u=\langle\beta,\alpha\rangle$ and $Q=\{LL,LR,R\}$, the INITIAL
reached list is $(R)$, the exterior is $\langle\beta,\square_1\rangle$
and its partition has one class. The successor has reached list
$(LL,LR,R)$, exterior $\langle\langle\square_1,\square_2\rangle,
\square_3\rangle$, and partition $\{\{1,3\},\{2\}\}$.
These sources have equal boundary measures and different complete rows.
For $Q=\{L,R\}$ on a branch, every actual accepted update preserves
the reached list, exterior and whole-subtree equality partition.

Proof. The actual successor is
$\rho u=\langle\langle\beta,\alpha\rangle,\beta\rangle$.
Its born children give exactly the displayed lists and values;
absence at INITIAL $LL,LR$ creates no INITIAL holes. An accepted
update transports both original child subtrees by the same $\rho$;
its injectivity from Theorem 113.5 preserves equality and disequality.
The root remains branch and both original children remain reached.
Refusal changes neither source nor row; Stop permits no suffix.
These facts use precisely Contract 112.1a. They do not turn a successor
row into an INITIAL row at a changed cut. $\square$

### 113.5 Acquired scale and representation evaluation

**Proposition 113.9 (inherited paid acquisition, not a new optimum).**
Conditional on an authentic same-source epoch-zero immutable register and
the allowed four-valued Read service, the existing
`ActualTreeReadoutAcquisition` frontier, `acquisitionTrace` and report-only
`restore` supply the complete original $u$ on every finite source.
Using that acquired value to compute $\mathcal J(u)$ and any $R_Q(u)$
requires no extra native Read or Apply. From the supplier's empty phase
history the sufficient inherited coordinates are

$$
(q,a,\lambda,k_{\rm phase})=
\left(S(u),0,\sum_{p\in V_u}|p|,S(u)\right),\qquad S(u)=|V_u|.
\tag{113.13}
$$

Here $q$ counts raw Reads, $a$ counts Apply attempts, $\lambda$ sums
their Read-address lengths, and $k_{\rm phase}$ counts distinct acquired
addresses in the supplier phase.
On the branch entry of (112.1), its root-first schedule and repeated
pre/post-entry root have exactly the raw, literal-length and paid-cache
scopes (112.20a): total raw Reads $S+1$, total literal length
$\sum_{p\in V_u}|p|$, cumulative distinct charge $S$ under one
immutable-source cache, with incremental charge $S-1$; separate empty
phase ledgers instead charge $1$ and $S$. No new optimal bound for
acquiring the measure, scale or source is asserted.

Proof. Reuse the acquisition/restoration supply of Definition 112.9 and
Theorem 112.10; its structural argument applies also to the two singleton
leaves. Each branch report queues its actual children, each terminal
queues none, and the finite report history reconstructs the original
ordered labels and brackets. The reply-driven traversal does not receive
an initial size or fuel bound. Its nodes, depths and repetitions give
(113.13) and the inherited branch cache scopes. Leaf counting on this
acquired description supplies the exact integer pair $(a,b)$ for $W$;
(113.7) supplies a finite cylinder density, interpreted as a measure
value, and (113.10) supplies its inverse on the attained image.
This is a different consumer of the same lossless acquisition phase,
not a change to the supplier's original Boolean `Strategy` task.
The source-bearing description and its price have not been obtained
by merely writing a computable source-indexed function. $\square$

**Specification 113.10 (evaluation and retained permission boundary).**
The representation is an exact mathematical correspondence **on its
attained image**. Given its genuinely acquired value, an allowed Read
can be evaluated as the original four-valued readout of the reconstructed
source. An actual accepted Apply sends $(\nu,w)$ to $(\nu,\varphi w)$;
an actual refused Apply leaves it fixed. Acceptance is still determined
by the common $G(\gamma,e,H)$ of Contract 112.1a, with the real accepted
epoch and complete chronological Read/status history. Those fields and
absorbing Stop are not replaced by $\nu$ or by $W$. In particular an
invariant boundary cannot itself simulate arbitrary Reads: the two
singletons have equal boundary and different root replies, and the two
branch witnesses in Theorem 113.7 have different child replies.
Any history-dependent guard using those replies retains them under its
own contract. Locally computing a reply is not an actual Read event and
cannot be inserted into the authentic history as one.
Representation evaluation grants no new Read, equality
port, reset, backward action, actuator, status oracle or acquisition right.

On an actually supplied boundary value, Theorem 113.7 concerns only
factorization of the complete INITIAL **value**. It supplies neither a
native finite-measure oracle nor a certificate of exact measure equality
from approximations. Returning such a value does not perform its original
producer, erase accessible acquisition records, or establish a complete
new access cut. The access isolation and separate handoff remain those of
Sparse Literal History Transport, Assumptions 59.3 and 74.1, §§74--75,
and Native Alpha Recut Memory, Definition 4.3 and Theorem 8.2.
Source preparation, root/epoch authentication, address generation,
storage, local computation, duration and physical actuation retain the
unpriced boundaries of §112.5. Neither an unknown $u$, an unknown $W(u)$
nor its boundary measure is supplied for free.

### 113.6 Scope of the synthesis and the remaining correspondence

**Specification 113.11 (mature neighbors and precise unresolved bridges).**
The source-specific synthesis is (113.9), the scale-injective original
representation, and the exhaustive complete INITIAL row classification
(113.11), derived from the existing all-occurrence/count and authentic
row/acquisition suppliers. Bernoulli cylinder probabilities and the
Fibonacci asymptotics are mature intermediates, not new results.
[Bezuglyi--Kwiatkowski--Medynets--Solomyak, arXiv:0812.1088v2,
§§2--4](https://arxiv.org/html/0812.1088v2) classifies tail-invariant
path measures of stationary Bratteli diagrams using their incidence
matrix. [Akiyama--Tan--Yuasa, arXiv:1801.03536v1, §1 and Theorem
1.1](https://arxiv.org/html/1801.03536v1) assumes a primitive aperiodic
word substitution with a one-sided fixed point and concerns natural
cutting positions. [Cabezas--Leroy, arXiv:2403.11357v2,
§§2.3, 5--6](https://arxiv.org/html/2403.11357v2) concerns constant-shape
subshifts on an already specified $\mathbb Z^d$, support and expansion
matrix. None of those scopes is identified here with the original finite
ordered-tree kernel or a native acquisition contract. No world-novelty
or exhaustive literature-absence claim is made.

`NativeUniformAnalysis.materialize_analysis_exact` supplies the full
computable analysis serialization and its original $K_0$ from common
row/cut/history code; it is not an unknown-source value acquisition.
`NativePayloadHistoryInstallation.payload_history_exact` supplies a
same-source semantic equivalence for reached equality records under its
locator premise, not acquired equality ports. Their owning Blueprints
retain those boundaries. The complete Xi square-product/analytic-order,
symbolic residual prime-power and positive-orientation hyperideal
relabeling applications keep their respective analytic, arithmetic and
already supplied geometric inputs; they are not premises for (113.9).

The limits in Theorem 113.2 have the explicit quantifiers
$\forall u\ \forall p\ \lim_{n\to\infty}$, with $u,p$ fixed. They do
not assert a uniform rate over moving sources/addresses, nor a joint
normalized full-state/operator limit. Even on the common measurable
space of finite and infinite addresses, each $\mu_{u,n}$ gives the finite
addresses mass one while $\nu_u$ gives them mass zero: total variation
in the supremum-over-events convention is exactly one. Cylinder
convergence has a different topology and does not remove that fact.
The centered ancestry transport of Definition 109.1 moreover has the
strictly positive fixed-positive-time defect in Theorem 109.2 on the
actual single-leaf orbit. Its failure is not repaired by (113.8).
The different gradient/polar comparison of §103 retains its own scope;
an all-original-source uniform normalized full-state correspondence for
an actual supplied transport remains a separate obligation.

An occurrence probability is not an acquired signed occurrence field.
Preparation, an actual field-transfer map with its domains/norms and
readouts, and a native heat actuator with the closed unit-edge generator
$-L$ still require the correspondence of Assumption 109.3 and §112.6.
Accepted source-step count, semigroup/occupation comparison time,
paid acquisition chronology and physical duration remain distinct;
$(\nu,w)\mapsto(\nu,\varphi w)$ supplies no physical clock conversion.
The binary address boundary supplies neither a spatial dimension nor
stable physical matter. Those claims still require a spatial/physical
realization and the missing operation, preparation, transport and clock
bridges, rather than an already given support or fitted metric.
These are ordinary mathematical proofs; no new Lean/kernel verification,
formal registration or freezing is asserted. No finite result here
completes the active through-2027 host programme.

## 113.99 追加锚（本行以下为增补区）

## 114. A finite-depth source-to-carrier certificate and its first failures

The finite occurrence and transport constructions above can be assembled into
one typed test object. This does not supply a physical realization; it records
which bridge clauses are already exact on a finite source and which ones fail
before any continuum interpretation is attempted. The family below includes the
singleton labels and the branch-root sources to which the native three-port
contract applies.

**Definition 114.1 (the finite-depth candidate bridge).** Let

$$
\mathcal S_n=\{\alpha,\beta\}
  \cup\{t=\langle s,u\rangle:\operatorname{height}(t)\le n\}
$$

be the finite ordered source family of height at most $n$. For $t\in
\mathcal S_n$, use its occurrence vertices $V_t$, oriented edge set $E_t$,
and the closed unit-edge operator $L_t=D_t^*D_t$. Define

$$
\begin{aligned}
d_t(x,y)&=\text{the shortest-path length in }(V_t,E_t),\\
\mu_t(x)&=1,\\
\widehat\mu_t(x)&=N_t^{-1},\\
U_t&=-D_tL_t^{+1/2}:P_t\ell^2(V_t)\longrightarrow\ell^2(E_t),
\end{aligned}
\tag{114.1}
$$

where $P_t$ removes constants. The tagged carrier is

$$
\mathscr C_n
  =\bigsqcup_{t\in\mathcal S_n}
     \bigl(\{t\}\times V_t,\{t\}\times E_t,d_t,\mu_t,U_t\bigr).
\tag{114.2}
$$

The tag is part of the mathematical carrier in (114.2); it is not declared to
be a freely available observation. A coarse port projection instead retains
only the entry data

$$
\pi^{\rm port}_t
  =\bigl(N_t,\ |B_t|,\ K_t\bigr),
\qquad K_t=R_tL_tR_t^*,
\tag{114.3}
$$

with the three literal ports $(\varepsilon,L,R)$ whenever they are reached.
For the port projection and its matrix, restrict to the branch-root subfamily
where these three ports are present; the full tagged carrier continues to
include singleton sources and sources with other root labels.

**Proposition 114.2 (finite exactness and the first bridge failures).** The
candidate (114.1)--(114.3) has the following properties.

1. Every object is finite and typed. For the Fibonacci sources $T_n$, the
   maps $U_{T_n}$ are the unitaries of Theorem 103.2, including the full
   root-invisible eigenspaces. Thus a finite occurrence carrier can preserve
   the complete finite operator, rather than only its root spectral measure.

2. The recursive birth map is pointwise local: under the old/new decomposition,

   $$
   V_{\rho t}=\iota_t(V_t)\sqcup B_t,
   \qquad
   E_{\rho t}=\iota_t^E(E_t)\sqcup
      \{(p,p\sigma):p\sigma\in B_t\},
   \tag{114.4}
   $$

   so every new edge has unit distance from its parent. This is only a local
   incidence statement. The one-step action changes all beta-parent sites at
   once and

   $$
   |B_t|=2|M_t|,
   \tag{114.5}
   $$

   so there is no source-independent bound on the number of changed sites.

3. Coarse port data are not action-closed. The two sources

   $$
   x=\langle\alpha,\beta\rangle,
   \qquad y=\langle\beta,\alpha\rangle
   $$

   have the same (114.3) at entry, while the successor port matrices have
   diagonal entries $(2,1,3)$ and $(2,3,1)$, respectively. Hence no update
   map on $\pi^{\rm port}_t$ can represent the native Apply operation. This is
   the B1 failure for the coarse observation, already witnessed by
   Proposition 112.4a.

4. The literal zero-extension of node states is not operator-compatible. In
   the decomposition of (114.4), the exact block formula of (112.9) gives

   $$
   L_{\rho t}J_tf-J_tL_tf
     =(2H_tf)\oplus(-C_t^*f).
   \tag{114.6}
   $$

   If $M_t\ne\varnothing$, choosing $f$ nonzero at a beta parent makes the
   right-hand side nonzero. Therefore $J_t$ does not intertwine the closed
   Laplacians or their heat semigroups. The source recursion is exact, but the
   simplest ancestry extension fails the operator part of B6. This calculation
   does not by itself settle B7, whose separate requirement is that the graph
   edges arise from actual source seams and transport relations.

5. The literal unit-edge counting measure is not globally 3-Ahlfors regular on
   the Fibonacci family. The source height obeys

   $$
   \operatorname{height}(T_n)=n-1\quad(n\ge1),
   \qquad N_{T_n}=2F_{n+1}-1.
   \tag{114.7}
   $$

   Consequently $B_{d_{T_n}}(r,2n-2)=V_{T_n}$, and

   $$
   \mu_{T_n}\bigl(B_{d_{T_n}}(r,2n-2)\bigr)=2F_{n+1}-1.
   \tag{114.8}
   $$

   A uniform upper bound $\mu(B(r,R))\le CR^3$ for all $n$ and all radii
   reaching the source diameter would imply

   $$
   2F_{n+1}-1\le C(2n-2)^3,
   $$

   which is impossible because $F_{n+1}$ grows exponentially. Thus B5 fails
   for this literal metric and counting measure at global scales. A bounded
   small-radius window, a rescaled edge metric, or a different measure remains
   a separate bridge choice; none is supplied by (114.1).

**Proof.** Items 1--4 are Theorems 103.2 and 112.4 together with the block
identity (112.9) and the explicit two-source witness of Proposition 112.4a.
For item 5, the height recurrence follows from
$T_n=\langle T_{n-1},T_{n-2}\rangle$, with heights $0,0$ at $n=0,1$,
and the node-count recurrence is Theorem 92.3. The ball of radius $2n-2$
contains every occurrence because every root-to-node path has length at most
$n-1$. Finally $F_{n+1}$ dominates a geometric progression along every
other index, so it cannot be bounded by a cubic polynomial in $n$. $\square$

The certificate separates three different repairs. Preserving the source tag
or a sufficient history can repair B1; a corrected state-dependent transport,
if one exists under the declared permissions, is needed for B6, while B7 needs
separate source-seam provenance; and a scale window or renormalized
metric/measure is needed before a volume statement can be compared with
dimension three. The finite unitary $U_t$ alone repairs
none of these gaps and does not produce a smooth rank-three distribution.

Thus the first finite-depth bridge test has a concrete outcome: the native
occurrence carrier is an exact finite spectral object, pointwise births are
local, but coarse action descent, zero-extension heat compatibility and global
three-dimensional volume growth all fail under the literal choices above. The
remaining continuum bridge must choose which information and which scale are
preserved before B2--B7 can be evaluated jointly.

## 114.99 追加锚（本行以下为增补区）

## 115. Parent-copy form transport and the generator obstruction

The first failure in §114 does not mean that every transport across a birth
step is impossible. It separates two requirements that are often conflated:
preserving the edge-energy form and intertwining the node generator. The
block identities of §112 give an exact finite test of this distinction.

**Definition 115.1 (the parent-copy extension).** In the old/new decomposition
of (112.7), define

$$
T_e:\ell^2(V_e)\longrightarrow\ell^2(V_{e+1}),
\qquad
T_ef=\begin{pmatrix}f\\ C_e^*f\end{pmatrix},
\tag{115.1}
$$

so every newly born child receives the value of its parent. Let $J_e$ retain
only the old coordinates, as in (112.8). More generally, write a top-fixed
linear extension as

$$
S_Qf=\begin{pmatrix}f\\Qf\end{pmatrix},
\tag{115.2}
$$

where $Q:\ell^2(V_e)\to\ell^2(B_e)$ is arbitrary.

**Theorem 115.2 (unique form transport, but no generator descent).** For every
finite source step, the parent-copy map satisfies

$$
D_{e+1}T_e=
\begin{pmatrix}D_e\\0\end{pmatrix},
\qquad
T_e^*L_{e+1}T_e=L_e,
\tag{115.3}
$$

and it is the unique top-fixed linear extension $S_Q$ with
$S_Q^*L_{e+1}S_Q=L_e$. It also obeys

$$
L_{e+1}T_e=J_eL_e,
\qquad
T_eL_e-L_{e+1}T_e=
\begin{pmatrix}0\\C_e^*L_e\end{pmatrix}.
\tag{115.4}
$$

Consequently, whenever $C_e^*L_e\ne0$, no top-fixed form-preserving
extension can intertwine the node generators. In the witness source
$x=\langle\alpha,\beta\rangle$, taking $f=\delta_R$ gives
$C_e^*L_ef=(1,1)$, so the obstruction is already present at the first
nontrivial birth step.

The extension is also not an isometry for the counting node inner products:

$$
\|T_ef\|^2
=\|f\|^2+\|C_e^*f\|^2
=\|f\|^2+2\|H_ef\|^2.
\tag{115.5}
$$

Thus a parent-copy map preserves the edge form while changing node mass on
beta-parent coordinates. Positive child weights, a time change, or a different
state norm would have to be declared before it could represent the same heat
response.

**Proof.** For an arbitrary $S_Q$, (112.8) gives

$$
D_{e+1}S_Qf=
\begin{pmatrix}D_ef\\(Q-C_e^*)f\end{pmatrix}.
\tag{115.6}
$$

Therefore

$$
\langle S_Qf,L_{e+1}S_Qf\rangle
=\|D_ef\|^2+\|(Q-C_e^*)f\|^2.
\tag{115.7}
$$

Equality with the old form for every $f$ forces $Q=C_e^*$, proving
uniqueness and the first identity in (115.3). Applying the adjoint block in
(112.9) to (115.3) gives
$L_{e+1}T_e=(L_ef,0)=J_eL_ef$, and multiplication on the right by $L_e$
gives the second identity in (115.4). For the witness $x$, the old Laplacian
sends $\delta_R$ to $(-1,0,1)$, while $C_e^*$ duplicates the value at the
beta parent $R$, yielding $(1,1)$. Finally
$C_eC_e^*=2H_e$ proves (115.5). \(\square\)

The result gives a precise B6 split. A form-level recursive carrier can be
made exact by copying parent values, but the same map does not carry the
counting-measure heat semigroup forward. A successful continuum bridge must
therefore choose which response is preserved and supply the corresponding
measure, clock and boundary readout. This finite obstruction neither selects a
physical dimension nor proves that every state-dependent transport fails; it
only rules out the top-fixed, form-preserving, generator-intertwining choice.

## 115.99 追加锚（本行以下为增补区）

## 116. Positive-mass no-go for simultaneous form, norm, and generator transport

The parent-copy result leaves one possible repair question: can a positive
node measure make the same transport both norm-preserving and dynamically
compatible? The answer is negative if the old coordinates are fixed and the
clock is unchanged.

**Definition 116.1 (weighted node generators).** Let \(M_e\) and
\(M_{e+1}\) be positive diagonal mass matrices on \(V_e\) and \(V_{e+1}\).
Write

$$
A_e=D_e^*D_e,\qquad
\mathcal L_e=M_e^{-1}A_e,
\tag{116.1}
$$

and similarly for \(e+1\). Consider a top-fixed extension \(S_Q\) from (115.2).
The three requirements are:

$$
\begin{array}{ll}
\text{(F)}&S_Q^*A_{e+1}S_Q=A_e
     \quad\text{(edge-form preservation)},\\
\text{(N)}&S_Q^*M_{e+1}S_Q=M_e
     \quad\text{(node-norm preservation)},\\
\text{(G)}&\mathcal L_{e+1}S_Q=S_Q\mathcal L_e
     \quad\text{(same-clock generator intertwining)}.
\end{array}
\tag{116.2}
$$

**Theorem 116.2 (positive-mass obstruction).** Suppose the old tree is
connected and nontrivial, and \(B_e\ne\varnothing\). There is no top-fixed
linear extension \(S_Q\) and no positive diagonal \(M_{e+1}\) satisfying
all three conditions (F), (N), and (G).

**Proof.** Condition (F) and Theorem 115.2 force \(Q=C_e^*\), so
\(S_Q=T_e\). The block identity (115.4) gives

$$
A_{e+1}T_e=J_eA_e.
\tag{116.3}
$$

Taking the old-coordinate block of (G) yields

$$
(M_{e+1}^{-1})_{\mathrm{old}}A_e=M_e^{-1}A_e.
\tag{116.4}
$$

Every row of \(A_e\) is nonzero in a connected nontrivial tree; applying
(116.4) to a basis vector at each vertex therefore forces
\((M_{e+1})_{\mathrm{old}}=M_e\). But then the old/child block decomposition
of the norm in (N) gives

$$
T_e^*M_{e+1}T_e
 =M_e+C_e(M_{e+1})_{\mathrm{child}}C_e^*.
\tag{116.5}
$$

The second term is a nonzero positive diagonal matrix whenever
\(B_e\ne\varnothing\), contradicting (N). \(\square\)

For the witness \(x=\langle\alpha,\beta\rangle\), this contradiction is
visible without a general argument: the two new child masses add a strictly
positive contribution to the old beta-parent coordinate after the unique
form-preserving copy. A time-rescaled condition
\(\mathcal L_{e+1}S_Q=\lambda_eS_Q\mathcal L_e\), a non-top-fixed transport,
or a non-diagonal state metric is outside Theorem 116.2 and must be declared
as a new bridge choice. The theorem therefore closes one exact option while
leaving those relaxed options open; it does not prove a universal transport
no-go or select a physical dimension.

## 116.99 追加锚（本行以下为增补区）
