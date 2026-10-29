# Fiedler–resistance bounds and boundary optimization on labelled complete tripartite graphs

## 1. Original vertices, independent conductances and cited inputs

**Definition 1.1 (The labelled positive domain).** Let $a,b,c$ be integers
with $2\le a\le b\le c$, and put $n=a+b+c$. Fix the disjoint labelled sets

$$
A=\{u_1,\ldots,u_a\},\qquad
B=\{v_1,\ldots,v_b\},\qquad
C=\{w_1,\ldots,w_c\}.
$$

The actual graph $K_{a,b,c}$ has vertex set $V=A\sqcup B\sqcup C$ and edge
set $E=E_{AB}\sqcup E_{AC}\sqcup E_{BC}$, where $E_{IJ}$ consists of all
unordered pairs with one endpoint in $I$ and one in $J$. Its conductance
vector ranges over

$$
\mathcal P_{a,b,c}=(0,\infty)^E=(0,\infty)^{ab+ac+bc}.
\tag{1.1}
$$

Each original edge coordinate is independent, finite and strictly
positive. Extend $g$ by zero on same-part pairs. Write

$$
d_x(g)=\sum_{y\ne x}g_{\{x,y\}},\qquad
(L(g)z)_x=\sum_{y\ne x}g_{\{x,y\}}(z_x-z_y),
\qquad
\langle z,z'\rangle=\sum_{x\in V}z_xz'_x.
\tag{1.2}
$$

Thus $L$ is the ordinary Laplacian with counting measure, and

$$
z^{\mathsf T}L(g)z=\sum_{\{x,y\}\in E}g_{\{x,y\}}(z_x-z_y)^2.
\tag{1.3}
$$

Its eigenvalues, including multiplicities on all $n$ original vertices,
are $0=\lambda_1(g)<\lambda_2(g)\le\cdots\le\lambda_n(g)$. For distinct
$p,q\in V$, take the harmonic voltage $h$ with $h_p=1$, $h_q=0$ and
$(L(g)h)_x=0$ for $x\notin\{p,q\}$, and set

$$
r_g(p,q)=\frac1{(L(g)h)_p},\qquad
R(g)=\sum_{\{p,q\}\subseteq V,\ p\ne q}r_g(p,q),\qquad
F(g)=\lambda_2(g)R(g).
\tag{1.4}
$$

Every unordered pair of distinct original vertices occurs once in $R$,
including pairs in a common part. There is no conductance budget,
symmetry restriction, vertex identification, or imposed trace or rank
condition in $\mathcal P_{a,b,c}$.

**Convention 1.2 (Resistance, scale and continuity).** The harmonic,
counting-Laplacian and unordered-pair conventions in Definition 1.1 are
those of Cruz Ortega–Menéndez-Conde,
[*Maximal Algebraic Connectivity for Paths with Fixed Effective
Resistance*, arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1),
§§2–4. Their §5, equation (3) and the following scale argument, supply the
fixed-resistance problem and its product formulation. The classical
matrix identities used here are

$$
r_g(p,q)=(e_p-e_q)^{\mathsf T}L(g)^+(e_p-e_q),\qquad
R(g)=n\operatorname{tr}L(g)^+
=n\sum_{k=2}^n\frac1{\lambda_k(g)}.
\tag{1.5}
$$

Here $L^+$ is inverse to $L$ on $\mathbf1^\perp$ and zero on constants.
The primary supplier is Ghosh–Boyd–Saberi,
[*Minimizing Effective Resistance of a Graph*, SIAM Review 50(1),
37–66, DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf),
§2.4, equation (8), and §2.5, equations (13)–(15).
Their conductance matrix $G$ is the $n$ by $n$ matrix $L(g)$ in (1.2),
their edge variable $g_l$ is our original coordinate $g_e$, and their
$R_{\mathrm{tot}}$ is the sum in (1.4). These identities apply whenever
the positive-conductance support is connected, including a connected
assignment with some zero edge coordinates.

Indeed, (1.3) gives $\ker L=\mathbb R\mathbf1$ on that support. The
Dirichlet matrix with two fixed boundary values is positive definite:
a zero-energy vector with zero boundary values would be constant on the
connected support and hence zero. Thus the harmonic voltage exists
uniquely. If $I=(Lh)_p$, row sums and harmonicity give
$Lh=I(e_p-e_q)$ and $I=h^{\mathsf T}Lh>0$. Applying $L^+$ and taking the
$p,q$ coordinate difference connects the harmonic definition to (1.5).
The all-pairs coefficient is fixed by

$$
\sum_{\{p,q\}\subseteq V,\ p\ne q}
(e_p-e_q)(e_p-e_q)^{\mathsf T}
=nI_n-\mathbf1\mathbf1^{\mathsf T}.
$$

In particular, for every $\alpha>0$,

$$
L(\alpha g)=\alpha L(g),\qquad
\lambda_k(\alpha g)=\alpha\lambda_k(g),\qquad
R(\alpha g)=\frac{R(g)}{\alpha},\qquad F(\alpha g)=F(g).
\tag{1.6}
$$

All eigenvalues are continuous in the finitely many original edge
coordinates: the symmetric-matrix min–max formula gives
$|\lambda_k(X)-\lambda_k(Y)|\le\|X-Y\|_{\mathrm{op}}$.
Formula (1.5) then gives continuity of $R$ at every connected
nonnegative assignment.

**Convention 1.3 (Whole suppliers and the additional inference).** The
[complete bipartite optimizer](FIEDLER_RESISTANCE_GENERAL_BIPARTITE_OPTIMIZER.md),
Theorem 4.1, supplies the whole labelled $K_{k,k}$ optimization for every
$k\ge4$: its product maximum is $k(4k-3)$, its unique normalized equality
assignment has every edge $1/k$, and that assignment has original-vertex
spectrum $0,1$ with multiplicity $2k-2$, and $2$.
For $c=a+b$, its actual-object map is the bijection from the first
bipartite class to $A\sqcup B$ and from the second class to $C$.
The edges of this $K_{c,c}$ are precisely $E_{AC}\sqcup E_{BC}$ on the
same $2c$ original vertices. Assigning zero to $E_{AB}$ gives exactly
its Laplacian and its full original-pair resistance. There is no
contraction or change of vertex measure. Since $c=a+b\ge4$, all the
hypotheses of that whole supplier hold, even when $a=2$ or $b=2$.

The [two-hub optimizer](FIEDLER_RESISTANCE_K2M_OPTIMIZER.md), Theorem 2.1,
and the [three-hub optimizer](FIEDLER_RESISTANCE_K3M_OPTIMIZER.md),
Theorems 2.2–4.1, concern the complete positive domains on $K_{2,m}$ and
$K_{3,m}$. Their vertices and edges are bipartite; the original edges
$E_{AB}$ in (1.1) are additional coordinates. Those whole conclusions
are therefore not comparisons for $\mathcal P_{a,b,c}$. The two-hub
Theorem 2.1 also supplies, within its proof, the elementary spectral
comparison $\sum q_k/(1+q_k)\ge S/(1+S)$ for nonnegative $q_k$ of sum $S$,
which is used as an intermediate step below.

Rosa–Harman,
[*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1), §2.3, define
$\Phi_A=(n-1)/\operatorname{tr}L^+$ and $\Phi_E=\lambda_2$ after reversing
their decreasing eigenvalue order to the increasing order here.
Consequently $F=n(n-1)\Phi_E/\Phi_A$. Their prescribed-edge-count
optimization and Ghosh–Boyd–Saberi's conductance-budget minimization
have different feasible sets from (1.1) or $R=R_0$.

The additional deductions here are the simultaneous trace constraint
from all three independent parts, its strict positive-domain bound,
the complete original-labelled boundary classification, the resulting
strict gap for each other fixed triple, and the characterization of
every maximizing sequence. The cited bipartite equality assignment is
used in full for the boundary sufficiency; it is not asserted to
optimize the tripartite positive domain by itself.

## 2. Simultaneous constraints from the three original independent parts

**Lemma 2.1 (Trace excess and its equality condition).** Let $g\in[0,\infty)^E$
have connected support, and put

$$
t=\lambda_2(g),\qquad
\widehat g=\frac gt,\qquad
P=I_n-\frac1n\mathbf1\mathbf1^{\mathsf T},\qquad
H=L(\widehat g)-P.
$$

Then $H\succeq0$, $H\mathbf1=0$, and, for every $I\in\{A,B,C\}$,

$$
D_I:=\sum_{x\in I}d_x(\widehat g)\ge |I|.
\tag{2.1}
$$

In particular,

$$
T:=\operatorname{tr}L(\widehat g)=D_A+D_B+D_C\ge n,\qquad
S:=\operatorname{tr}H=T-(n-1)\ge1.
\tag{2.2}
$$

If $S=1$, then $H$ annihilates each of the three spaces

$$
U_I=\{z\in\mathbb R^V:z_x=0\ (x\notin I),\
                         \sum_{x\in I}z_x=0\}.
\tag{2.3}
$$

*Proof.* Both $L(\widehat g)$ and $P$ vanish on constants. On
$\mathbf1^\perp$, $P$ is identity and all eigenvalues of $L(\widehat g)$
are at least $1$. This proves the two assertions about $H$.

Fix a part $I$ of size $m\ge2$ and take an orthonormal basis
$f_1,\ldots,f_{m-1}$ of $U_I$. Because $I$ is independent, the principal
block of $L(\widehat g)$ on $I$ is diagonal with entries
$d_x(\widehat g)$. The projection onto $U_I$ on those coordinates is
$I_m-\mathbf1_m\mathbf1_m^{\mathsf T}/m$. The Rayleigh lower bound,
applied to each basis vector, therefore gives

$$
m-1\le\sum_{\ell=1}^{m-1}f_\ell^{\mathsf T}L(\widehat g)f_\ell
=\frac{m-1}{m}D_I.
\tag{2.4}
$$

Since $m-1>0$, this is (2.1). In particular it holds for $m=2$;
no invariance of $U_I$ under $L$ is assumed. Summing (2.1) over the
partition of all original vertices proves (2.2).

If $S=1$, then $T=n$ and all three nonnegative gaps $D_I-|I|$ vanish.
For each fixed $I$, equality in (2.4) gives

$$
\sum_{\ell=1}^{m-1}f_\ell^{\mathsf T}Hf_\ell=0.
$$

Every summand is nonnegative. A zero quadratic form of a positive
semidefinite matrix is a kernel vector, as follows by orthogonal
spectral decomposition. Hence $Hf_\ell=0$ for every $\ell$, proving
that $H$ annihilates $U_I$. ∎

## 3. The universal ceiling and all normalized boundary equalities

**Definition 3.1 (Normalized domains and product supremum).** Set

$$
\begin{aligned}
\mathcal N_{a,b,c}
&=\{g\in\mathcal P_{a,b,c}:\lambda_2(g)=1\},\\
\mathcal C_{a,b,c}
&=\{g\in[0,\infty)^E:\lambda_2(g)=1\},\\
U_n&=n\left(n-\frac32\right),\qquad
M_{a,b,c}=\sup_{g\in\mathcal P_{a,b,c}}F(g).
\end{aligned}
\tag{3.1}
$$

Every member of $\mathcal C_{a,b,c}$ has connected support. This is
exactly the coordinatewise closure of $\mathcal N_{a,b,c}$: if
$g_j\in\mathcal N_{a,b,c}$ converges, continuity preserves
nonnegativity and $\lambda_2=1$; conversely for $g\in\mathcal C_{a,b,c}$,
the positive vectors
$(g+\varepsilon\mathbf1_E)/\lambda_2(g+\varepsilon\mathbf1_E)$ converge
to $g$ as $\varepsilon\downarrow0$. Resistance on $\mathcal C_{a,b,c}$
is defined on the same original vertices by (1.4)–(1.5).

**Theorem 3.2 (Universal strict bound and unique boundary equality).**
For every integer triple $2\le a\le b\le c$ and every
$g\in\mathcal P_{a,b,c}$,

$$
F(g)<U_n.
\tag{3.2}
$$

On the auxiliary normalized nonnegative domain,

$$
R(g)\le U_n\qquad(g\in\mathcal C_{a,b,c}).
\tag{3.3}
$$

Equality in (3.3) exists if and only if $c=a+b$. In that case its
unique original-labelled assignment is

$$
g^\star_e=
\begin{cases}
0,&e\in E_{AB},\\
1/c,&e\in E_{AC}\sqcup E_{BC}.
\end{cases}
\tag{3.4}
$$

This connected boundary assignment is not a member of
$\mathcal P_{a,b,c}$. The positive equality class in (3.2) is empty.

*Proof.* For any connected nonnegative $g$, normalize by
$t=\lambda_2(g)$ as in Lemma 2.1. Write

$$
q_k=\frac{\lambda_k(g)}t-1\ge0\quad(2\le k\le n),\qquad
\Delta=\sum_{k=2}^n\frac{q_k}{1+q_k}.
$$

The eigenvalues of $H$ are $0$ on constants and the $q_k$ on
$\mathbf1^\perp$, so their sum is $S\ge1$. The elementary comparison
cited in Convention 1.3 follows term by term from $q_k\le S$:

$$
\Delta\ge\sum_{k=2}^n\frac{q_k}{1+S}
=\frac S{1+S}\ge\frac12.
\tag{3.5}
$$

Using (1.5) gives

$$
\frac{F(g)}n
=\sum_{k=2}^n\frac1{1+q_k}
=n-1-\Delta\le n-\frac32.
\tag{3.6}
$$

Equality forces $S=1$, because $S/(1+S)$ is strictly increasing.
For each $q_k>0$, equality in the first comparison of (3.5) forces
$q_k=S$. Since $S>0$, precisely one $q_k$ is positive. Thus equality
in (3.6) requires

$$
S=1,\qquad \operatorname{rank}H=1.
\tag{3.7}
$$

Conversely (3.7) gives equality. These are consequences of equality,
not restrictions on competitors.

Suppose (3.7) holds. Factor $H=hh^{\mathsf T}$ with
$\|h\|^2=\operatorname{tr}H=1$. Since $H\mathbf1=0$ and $h\ne0$,
$\sum_xh_x=0$. Lemma 2.1 says that $H(e_x-e_y)=0$ whenever $x,y$
lie in one part. Hence $h_x=h_y$ on each part. For two distinct
vertices $x,y$ of that part, $L(\widehat g)_{xy}=0$, and therefore

$$
h_xh_y=H_{xy}=\frac1n.
$$

Each part contains at least two vertices, including all size-two
cases, so its common value is $\sigma_I/\sqrt n$ for a sign
$\sigma_I\in\{-1,1\}$. The zero-sum condition is

$$
a\sigma_A+b\sigma_B+c\sigma_C=0.
\tag{3.8}
$$

The signs cannot all agree. Thus one part size must equal the sum of
the other two; under $2\le a\le b\le c$ this is exactly $c=a+b$.
The only possible signs, up to simultaneous reversal, are then
$\sigma_A=\sigma_B=-\sigma_C$. For vertices in different parts,
$L(\widehat g)=P+hh^{\mathsf T}$ now gives

$$
\widehat g_{\{x,y\}}
=\frac1n-h_xh_y
=\frac{1-\sigma_I\sigma_J}{n}.
\tag{3.9}
$$

Since $n=2c$, these are exactly (3.4). In particular, the necessary
$AB$ coordinates are zero. This excludes equality for every strictly
positive original assignment, proving (3.2).

For sufficiency in the nonnegative domain, apply the whole balanced
bipartite theorem through the actual-object map in Convention 1.3.
The assignment (3.4) is the uniform normalized $K_{c,c}$ assignment
on the same $2c$ vertices, with connected support, $\lambda_2=1$,
and

$$
R(g^\star)=c(4c-3)=2c\left(2c-\frac32\right)=U_n.
\tag{3.10}
$$

Its full spectrum is $0$, $1$ with multiplicity $n-2$, and $2$.
Equations (3.8)–(3.9) show uniqueness of the actual edge coordinates,
rather than uniqueness only up to permutations. ∎

## 4. Positive approximation, the fixed-triple gap and every maximizing sequence

**Theorem 4.1 (Positive approximants with complete original-vertex spectrum).**
Assume $2\le a\le b$ and $c=a+b$. For every real $\varepsilon>0$ define

$$
g^{(\varepsilon)}_e=
\begin{cases}
\varepsilon,&e\in E_{AB},\\
1/c,&e\in E_{AC}\sqcup E_{BC}.
\end{cases}
\tag{4.1}
$$

This is a finite strictly positive original-edge assignment with
$\lambda_2(g^{(\varepsilon)})=1$. Its full $n=2c$ vertex spectrum,
as a multiset, is

$$
\begin{array}{c|c}
\text{eigenvalue}&\text{multiplicity}\\ \hline
0&1\\
1&c-1\\
1+b\varepsilon&a-1\\
1+a\varepsilon&b-1\\
1+c\varepsilon&1\\
2&1
\end{array}
\tag{4.2}
$$

Coincident entries have their displayed multiplicities added. Its
resistance is

$$
R_\varepsilon
=n\left(c-1+\frac{a-1}{1+b\varepsilon}
              +\frac{b-1}{1+a\varepsilon}
              +\frac1{1+c\varepsilon}+\frac12\right).
\tag{4.3}
$$

Consequently

$$
M_{a,b,a+b}=U_n,\qquad
F(g^{(\varepsilon)})=R_\varepsilon\longrightarrow U_n
\quad(\varepsilon\downarrow0).
\tag{4.4}
$$

The supremum is not attained in the positive domain.

*Proof.* All coordinates in (4.1) are finite and positive. Work in
$\mathbb R^V$ with its original counting inner product. For each part,
the space $U_I$ in (2.3) is invariant for this particular assignment:
cross-part coordinate sums vanish. Its eigenvalue is the common
degree of a vertex in that part. These degrees are
$1+b\varepsilon$ on $A$, $1+a\varepsilon$ on $B$, and $1$ on $C$.
Their dimensions are $a-1,b-1,c-1$.

The orthogonal complement of $U_A\oplus U_B\oplus U_C$ consists of
vectors constant on each part. On the three part-values
$(\alpha,\beta,\gamma)$, the same $n$ by $n$ Laplacian acts by

$$
\begin{aligned}
(Lz)|_A&=\alpha-\gamma+b\varepsilon(\alpha-\beta),\\
(Lz)|_B&=\beta-\gamma+a\varepsilon(\beta-\alpha),\\
(Lz)|_C&=\gamma-\frac{a\alpha+b\beta}{c}.
\end{aligned}
\tag{4.5}
$$

Three linearly independent vectors of part-values are

$$
(1,1,1),\qquad (b,-a,0),\qquad (1,1,-1).
$$

Equation (4.5), using $a+b=c$, gives their eigenvalues
$0,1+c\varepsilon,2$, respectively. These computations give all
$n$ eigenvalues and all the multiplicities in (4.2).
They are calculations in invariant subspaces of the original matrix,
not a replacement of the original vertices by three vertices.

Every displayed positive eigenvalue is at least $1$, and $1$ occurs
$c-1>0$ times. Thus $\lambda_2=1$. Substitution in (1.5) proves
(4.3). Its limit is

$$
n\left(c-1+(a-1)+(b-1)+1+\frac12\right)
=n\left(2c-\frac32\right)=U_n.
$$

Theorem 3.2 bounds every competing positive assignment strictly below
$U_n$; (4.1) approaches that bound within the positive domain.
This proves (4.4) and nonattainment. ∎

**Lemma 4.2 (Compactness of sequences approaching the ceiling).**
Fix any $2\le a\le b\le c$. If $g_j\in\mathcal P_{a,b,c}$ and
$F(g_j)\to U_n$, put $h_j=g_j/\lambda_2(g_j)$. Then

$$
\operatorname{tr}L(h_j)\longrightarrow n,\qquad
\sum_{e\in E}(h_j)_e\longrightarrow\frac n2.
\tag{4.6}
$$

In particular the sequence $(h_j)$ is bounded in every original
labelled edge coordinate. It has a convergent subsequence, and every
subsequential limit $h$ lies in $\mathcal C_{a,b,c}$ and satisfies
$R(h)=U_n$.

*Proof.* For $h_j$ use $S_j,\Delta_j$ from Lemma 2.1 and the proof of
Theorem 3.2. Equation (3.6) gives
$\Delta_j=n-1-F(g_j)/n\to1/2$. Since $S_j\ge1$ and
$\Delta_j\ge S_j/(1+S_j)$, eventually $\Delta_j<1$ and

$$
1\le S_j\le\frac{\Delta_j}{1-\Delta_j}\longrightarrow1.
\tag{4.7}
$$

It follows that $\operatorname{tr}L(h_j)=n-1+S_j\to n$.
Each original edge contributes twice to that trace, proving (4.6).
All coordinates of $h_j$ are nonnegative, so their bounded sum bounds
each coordinate. Finite-dimensional sequential compactness supplies a
convergent subsequence. At any such limit $h$, nonnegativity and
continuity of $\lambda_2$ give $\lambda_2(h)=1$. Hence the support is
connected, and (1.5) is continuous there. Since
$R(h_j)=F(g_j)$ by scaling, $R(h)=U_n$. ∎

**Theorem 4.3 (Exactly which fixed triples reach the ceiling).** For every
fixed integer triple $2\le a\le b\le c$,

$$
0<M_{a,b,c}\le U_n,\qquad
M_{a,b,c}=U_n\ \Longleftrightarrow\ c=a+b.
\tag{4.8}
$$

Thus every other fixed triple has $M_{a,b,c}<U_n$. On $c=a+b$, for
every sequence $(g_j)_{j\ge1}$ of arbitrary independent positive
original-edge assignments,

$$
F(g_j)\longrightarrow M_{a,b,c}
\quad\Longleftrightarrow\quad
\frac{g_j}{\lambda_2(g_j)}
\longrightarrow g^\star
\quad\text{in every original labelled edge coordinate}.
\tag{4.9}
$$

No symmetry is required of the sequence. For $c\ne a+b$, (4.8) makes
no assertion of an exact smaller value, attainment, or equality class.

*Proof.* A positive assignment exists, for example $g_e=1$ for all
$e\in E$, and it has $F(g)>0$. Theorem 3.2 gives the finite upper
bound. Theorem 4.1 proves $M=U_n$ when $c=a+b$.

If a fixed triple with $c\ne a+b$ had $M=U_n$, the definition of
supremum would give a positive sequence with $F(g_j)\to U_n$.
Lemma 4.2 would give a limit in $\mathcal C_{a,b,c}$ satisfying
$R=U_n$, contrary to Theorem 3.2. Hence $M<U_n$ for each such
fixed triple. This argument does not assume that the entire
normalized domain is compact.

For $c=a+b$, suppose first that the left side of (4.9) holds.
Lemma 4.2 bounds the normalized sequence. Every convergent
subsequence has limit $g^\star$ by Theorem 3.2. Therefore the whole
sequence converges to $g^\star$: otherwise a subsequence would stay
a positive Euclidean distance from $g^\star$, and boundedness
would give a further convergent subsequence with a different limit.

Conversely, if $h_j=g_j/\lambda_2(g_j)\to g^\star$, continuity of
$R$ at the connected assignment $g^\star$ and (1.6) give
$F(g_j)=R(h_j)\to R(g^\star)=U_n=M$. This proves both directions
for every positive sequence. ∎

## 5. Every resistance level and exact scaling correspondence

**Theorem 5.1 (Scaling and attainment for all triples).** Let
$2\le a\le b\le c$ and $R_0>0$. The set

$$
\mathcal F_{a,b,c,R_0}
=\{g\in\mathcal P_{a,b,c}:R(g)=R_0\}
$$

is nonempty. The maps

$$
\begin{aligned}
\Psi_{R_0}:\mathcal N_{a,b,c}&\longrightarrow\mathcal F_{a,b,c,R_0},
& h&\longmapsto\frac{R(h)}{R_0}h,\\
\Theta:\mathcal F_{a,b,c,R_0}&\longrightarrow\mathcal N_{a,b,c},
& g&\longmapsto\frac{g}{\lambda_2(g)}
\end{aligned}
\tag{5.1}
$$

are mutually inverse bijections, and

$$
\lambda_2(\Psi_{R_0}(h))=\frac{R(h)}{R_0},\qquad
\sup_{g\in\mathcal F_{a,b,c,R_0}}\lambda_2(g)
=\frac{M_{a,b,c}}{R_0}.
\tag{5.2}
$$

A product supremum is attained in $\mathcal P_{a,b,c}$ if and only
if the level supremum is attained for one, equivalently every,
$R_0>0$. Its positive maximizing rays correspond bijectively to
the normalized maximizers $\{h\in\mathcal N_{a,b,c}:R(h)=M_{a,b,c}\}$,
and $\Psi_{R_0}$ selects the unique point of each such ray on the
given level.

*Proof.* For any positive $g$, the assignment $R(g)g/R_0$ is positive
and has resistance $R_0$ by (1.6), proving nonemptiness.
For $h\in\mathcal N$, scaling gives
$R(\Psi_{R_0}(h))=R_0$ and the first formula in (5.2), and then
$\Theta(\Psi_{R_0}(h))=h$. For $g\in\mathcal F$, writing
$t=\lambda_2(g)$ gives
$\lambda_2(g/t)=1$ and $R(g/t)=tR_0$, so
$\Psi_{R_0}(\Theta(g))=t(g/t)=g$.

For every positive $g$, $F(g)=R(g/\lambda_2(g))$. Thus
$M=\sup_{h\in\mathcal N}R(h)$. The bijection and its first formula
in (5.2) prove the second, and show that either supremum is attained
precisely when a normalized vector has $R(h)=M$.
Each positive ray has exactly one member of $\mathcal N$ and one
member of $\mathcal F$, proving the claimed full correspondence
without evaluating $M$ for any other triple. ∎

**Theorem 5.2 (The boundary family on every exact resistance level).**
Assume $2\le a\le b$ and $c=a+b$. For every $R_0>0$,

$$
\sup_{g\in\mathcal F_{a,b,c,R_0}}\lambda_2(g)
=\frac{U_n}{R_0},
\qquad
\{g\in\mathcal F_{a,b,c,R_0}:\lambda_2(g)=U_n/R_0\}=\varnothing.
\tag{5.3}
$$

Explicit finite strictly positive approximants satisfying $R=R_0$
exactly are

$$
G^{(\varepsilon)}=\frac{R_\varepsilon}{R_0}g^{(\varepsilon)}
\qquad(\varepsilon>0),
\tag{5.4}
$$

with $R_\varepsilon$ and $g^{(\varepsilon)}$ given by (4.1)–(4.3).
Their entire original-vertex spectrum is (4.2) multiplied by
$R_\varepsilon/R_0$, with the same multiplicities, and
$\lambda_2(G^{(\varepsilon)})\to U_n/R_0$.

For every sequence $(g_j)_{j\ge1}$ in this exact level set,

$$
\lambda_2(g_j)\longrightarrow\frac{U_n}{R_0}
\quad\Longleftrightarrow\quad
g_j\longrightarrow g^\star_{R_0}
\quad\text{in every original labelled edge coordinate},
\tag{5.5}
$$

where the unique limiting assignment is

$$
(g^\star_{R_0})_e=
\begin{cases}
0,&e\in E_{AB},\\
(4c-3)/R_0,&e\in E_{AC}\sqcup E_{BC}.
\end{cases}
\tag{5.6}
$$

It has connected support and resistance $R_0$, but is not positively
feasible on $K_{a,b,c}$.

*Proof.* Theorem 4.1 gives $M=U_n$, and Theorem 5.1 gives the
supremum in (5.3). Any positive equality point would satisfy
$F(g)=U_n$, contradicting Theorem 3.2.
By (1.6) and Theorem 4.1, (5.4) has strictly positive finite
coordinates, resistance exactly $R_0$, the claimed scaled complete
spectrum, and $\lambda_2=R_\varepsilon/R_0\to U_n/R_0$.

If a level sequence is maximizing, then
$F(g_j)=R_0\lambda_2(g_j)\to U_n$.
Theorem 4.3 gives $g_j/\lambda_2(g_j)\to g^\star$, while
$\lambda_2(g_j)\to U_n/R_0$. Multiplication gives

$$
g_j\longrightarrow\frac{U_n}{R_0}g^\star.
$$

Since $U_n=c(4c-3)$, this is exactly (5.6).
Conversely, convergence to (5.6) implies convergence of $\lambda_2$
by continuity. The limit is $(U_n/R_0)g^\star$, whose
$\lambda_2$ is $U_n/R_0$ by (1.6), proving the reverse implication.
The same scaling gives resistance $R_0$ and connected support for
the limit. Its zero $AB$ coordinates exclude positive feasibility. ∎

## 6. A further unbalanced estimate and the complementary exact problem

**Proposition 6.1 (A strict estimate when the largest part exceeds the other two).**
If $d=c-a-b>0$, every $g\in\mathcal P_{a,b,c}$ satisfies

$$
F(g)<n\left(n-2+\frac1{d+2}\right),
\qquad
M_{a,b,c}\le n\left(n-2+\frac1{d+2}\right)<U_n.
\tag{6.1}
$$

This estimate does not assert sharpness.

*Proof.* Normalize to $h=g/\lambda_2(g)$. Let $W_{IJ}$ be the sum
of its original $IJ$ edge coordinates and $W=W_{AB}+W_{AC}+W_{BC}$.
Lemma 2.1 gives

$$
D_C=W_{AC}+W_{BC}\ge c,\qquad
W=D_C+W_{AB}>c,
$$

because all $ab$ original $AB$ conductances are strictly positive.
Thus $S=2W-(n-1)>2c-n+1=d+1$.
The comparison (3.5) is consequently strict at

$$
\Delta\ge\frac S{1+S}>\frac{d+1}{d+2}.
$$

Equation (3.6) gives the first inequality of (6.1).
Taking the supremum gives its non-strict bound; since $d>0$,
$1/(d+2)<1/2$, proving the last strict comparison. ∎

**Definition 6.2 (The complementary exact optimizer problem).** For each
fixed integer triple $2\le a\le b\le c$ with $c\ne a+b$, the
complementary exact problem is to determine $M_{a,b,c}$ and the set

$$
\mathcal E_{a,b,c}
=\{g\in\mathcal P_{a,b,c}:F(g)=M_{a,b,c}\},
$$

including whether this set is empty. Theorem 4.3 proves the strict
gap $M_{a,b,c}<U_n$, and Proposition 6.1 gives an additional upper
estimate when $c>a+b$. Neither determines the exact smaller value
or the positive attainment and equality classification for these
triples. Theorem 5.1 transfers precisely this remaining problem
to every positive resistance level.

## 追加锚（本行以下为增补区）
