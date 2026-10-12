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
