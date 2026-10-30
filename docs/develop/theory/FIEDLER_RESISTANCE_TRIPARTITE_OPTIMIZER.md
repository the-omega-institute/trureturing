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

## 7. The unrestricted strict-triangle optimizer

**Definition 7.1 (Strict-triangle parameters and cited intermediates).**
Throughout this section let $a,b,c$ be integers with
$2\le a\le b\le c<a+b$, and retain the original labelled vertices,
independent positive conductances, counting-measure Laplacian and all-pairs
resistance of Definition 1.1. Put

$$
\begin{aligned}
\eta&=\frac{(a+b-c)(a+c-b)(b+c-a)}{4abc},\\
C_{a,b,c}&=n\left(n-3+\frac3{2+\eta}\right),\qquad n=a+b+c,\\
h^*_{AB}&=\frac{a+b-c}{2ab},\qquad
h^*_{AC}=\frac{a+c-b}{2ac},\qquad
h^*_{BC}=\frac{b+c-a}{2bc}.
\end{aligned}
\tag{7.1}
$$
The notation $h^*_{IJ}$ assigns that value to every original edge of
$E_{IJ}$; it places no restriction on competing assignments.

The classical all-pairs and scaling identities (1.5)–(1.6) are used with
exactly the correspondence in Convention 1.2 to Ghosh–Boyd–Saberi,
[*Minimizing Effective Resistance of a Graph*](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf),
§§2.4–2.5, equations (8), (13)–(15). The finite-list spectral comparison
from the proof of the [general bipartite theorem](FIEDLER_RESISTANCE_GENERAL_BIPARTITE_OPTIMIZER.md),
Theorem 3.1, equation (3.3), will be applied only as a matrix inequality.
The new comparison below concerns all three edge classes simultaneously.
Its part-sum determinant is the classical Gram-area, equivalently Heron,
identity, expanded explicitly in Lemma 7.2.

For the design correspondence, choose an $n$ by $(n-1)$ matrix $Q$ with
orthonormal columns spanning $\mathbf1^\perp$. With the original incidence
vectors $b_e=e_x-e_y$ and $x_e=Q^{\mathsf T}b_e$, the positive definite
information matrix is

$$
\mathcal I(g)=Q^{\mathsf T}L(g)Q=\sum_{e\in E}g_e x_e x_e^{\mathsf T}.
$$
Rosa–Harman, [*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1),
§§2.3–2.4 and Theorem 1, give the corresponding criteria
$\Phi_A=(n-1)/\operatorname{tr}\mathcal I^{-1}$ and
$\Phi_E=\lambda_{\min}(\mathcal I)$, so that
$F=n(n-1)\Phi_E/\Phi_A$.
Passing to $p_e=g_e/\sum_f g_f$ preserves this ratio and parametrizes every
positive conductance ray. Consequently a design theorem for this same
ratio, these same $x_e$, and the complete positive simplex would also
supply the present optimization; a budget parametrization alone does not
distinguish the problems. Their problem (1) selects a prescribed number
of edges with fixed edge weights, problem (2) and its approximate-design
relaxation optimize a chosen information criterion, and their Theorems
1–5 supply spectral reformulation, derivatives and matrix updates.
Those statements are used here at the specified intermediate identities,
not as a whole optimizer for this ratio. No theorem from Harman,
[*Minimal efficiency of designs under the class of orthogonally invariant
information criteria*, DOI:10.1007/s001840300301](https://link.springer.com/article/10.1007/s001840300301),
or from the [institutional article 16817](https://repository.uaeh.edu.mx/revistas/index.php/icbi/article/view/16817)
is a premise of the proofs below.

**Lemma 7.2 (A three-part second-excess comparison).** Let
$h\in\mathcal C_{a,b,c}$, and set

$$
\begin{gathered}
H=L(h)-P,\qquad S=\operatorname{tr}H,\qquad s=S-1,\\
z_A=D_A-a,\quad z_B=D_B-b,\quad z_C=D_C-c,\qquad
D_I=\sum_{x\in I}d_x(h).
\end{gathered}
\tag{7.2}
$$
Let $E(H)$ be the second elementary symmetric sum of the eigenvalues of
$H$, equivalently the sum of all its second-order principal minors.
Then $z_A,z_B,z_C\ge0$, $s=z_A+z_B+z_C\ge0$, and

$$
E(H)\ge\eta+
 \frac{a^2+b^2-c^2}{2abc}s-\frac n{4abc}s^2.
\tag{7.3}
$$
In particular,

$$
s=0\ \Longrightarrow\ E(H)\ge\eta,\qquad
0<s\le1\ \Longrightarrow\ E(H)>\eta-\frac s4.
\tag{7.4}
$$
No invariance of the within-part difference spaces is assumed.

*Proof.* Lemma 2.1 gives $H\succeq0$, $H\mathbf1=0$, $D_I\ge|I|$
and $S=D_A+D_B+D_C-(n-1)$, proving the first assertions.
Let $m_A=a,m_B=b,m_C=c$, and form the three orthonormal vectors
$f_I=\mathbf1_I/\sqrt{m_I}$. Let $K$ be the compression of $H$ to their
span, $K_{IJ}=f_I^{\mathsf T}Hf_J$, and put

$$
B_{IJ}=\sqrt{m_I m_J}\,K_{IJ}
       =\sum_{x\in I,\,y\in J}H_{xy},\qquad X_I=B_{II}.
$$
The letter $B$ here denotes a symmetric three by three matrix, not a
replacement graph. Since each original part is independent, its
principal block of $H$ has diagonal $d_x(h)-1+1/n$ and off-diagonal
$1/n$. Thus

$$
X_A=\frac{a^2}n+z_A,\quad
X_B=\frac{b^2}n+z_B,\quad
X_C=\frac{c^2}n+z_C.
\tag{7.5}
$$
Also $B\mathbf1_3=0$, because $H\mathbf1=0$. Solving these three row-sum
relations gives, for distinct $I,J,K'$ in $\{A,B,C\}$,

$$
B_{IJ}=\frac{X_{K'}-X_I-X_J}{2}.
$$
Consequently every numerator of a second-order principal minor of $K$
is the same number

$$
\begin{aligned}
\Omega(X)
&=X_I X_J-\frac{(X_{K'}-X_I-X_J)^2}{4}\\
&=\frac{2(X_A X_B+X_A X_C+X_B X_C)
              -X_A^2-X_B^2-X_C^2}{4},\\
E(K)&=\left(\frac1{ab}+\frac1{ac}+\frac1{bc}\right)\Omega(X)
     =\frac n{abc}\Omega(X).
\end{aligned}
\tag{7.6}
$$
For a Gram representation $H_{xy}=\langle v_x,v_y\rangle$, the vectors
$V_I=\sum_{x\in I}v_x$ satisfy $V_A+V_B+V_C=0$ and
$\|V_I\|^2=X_I$. Then $\Omega(X)=\|V_A\wedge V_B\|^2$.
This is precisely the squared-area identity for that actual triple of
part sums. In particular the three areas are evaluated in a common Gram
representation. The algebra in (7.5)–(7.6) uses only symmetry, the
within-part entries and zero row sums; it does not require positivity
once those entries are specified.

Complete $f_A,f_B,f_C$ to an orthonormal basis of $\mathbb R^V$.
In that basis every second-order principal minor of the positive
semidefinite matrix $H$ is nonnegative, and the three minors using only
the first three coordinates sum to $E(K)$. Since
$E(H)=((\operatorname{tr}H)^2-\operatorname{tr}(H^2))/2$ is unchanged by
this orthogonal change of basis, $E(H)\ge E(K)$. This inequality retains
all the other original coordinates.

Substitution of (7.5) into (7.6) gives the exact expression

$$
\begin{aligned}
E(K)=\eta
 &+\frac{b^2+c^2-a^2}{2abc}z_A
  +\frac{a^2+c^2-b^2}{2abc}z_B
  +\frac{a^2+b^2-c^2}{2abc}z_C\\
 &+\frac n{4abc}
  \left(2(z_Az_B+z_Az_C+z_Bz_C)-z_A^2-z_B^2-z_C^2\right).
\end{aligned}
\tag{7.7}
$$
For its constant term the elementary Heron expansion is

$$
2(a^2b^2+a^2c^2+b^2c^2)-a^4-b^4-c^4
=n(a+b-c)(a+c-b)(b+c-a).
$$
The smallest of the three linear coefficients in (7.7) is the one
multiplying $z_C$, because $c$ is the largest part. The parenthesis on
the second line is at least $-s^2$: adding $s^2$ to it gives
$4(z_Az_B+z_Az_C+z_Bz_C)\ge0$. These facts prove (7.3).

Here the integer hypotheses yield a useful strict coefficient estimate:

$$
\frac{a^2+b^2-c^2}{2abc}-\frac n{4abc}>-\frac14.
\tag{7.8}
$$
To prove it without discarding any size-two case, put
$J(c)=abc+2a^2+2b^2-2c^2-a-b-c$.
It is a concave quadratic in $c$ on $[b,a+b-1]$, so it is at least the
smaller of its endpoint values. Those values are

$$
\begin{aligned}
J(b)&=ab^2+2a^2-a-2b>0,\\
J(a+b-1)&=ab(a+b-5)+2(a+b)-1>0.
\end{aligned}
$$
For the first inequality, $ab^2-2b=b(ab-2)>0$ and $2a^2-a>0$.
For the second, if $a+b=4$ its value is $3$; if $a+b\ge5$ both the
nonnegative first term and the strictly positive last terms have the
indicated signs. Integrality and $c<a+b$ give $c\le a+b-1$, hence
$J(c)>0$. Division by $4abc$ proves (7.8).
If $0<s\le1$, then $s^2\le s$, so (7.3) and (7.8) give the strict
inequality in (7.4). The assertion at $s=0$ is immediate from (7.3). ∎

**Theorem 7.3 (All positive weights, exact maximum, rigidity and spectrum).**
For every integer triple $2\le a\le b\le c<a+b$,

$$
0<\eta\le\frac14,\qquad
\eta=\frac14\ \Longleftrightarrow\ a=b=c,
\qquad
M_{a,b,c}=C_{a,b,c}
=n\left(n-3+\frac3{2+\eta}\right).
\tag{7.9}
$$
For every one of the $ab+ac+bc$ independently positive finite original
edge assignments,

$$
F(g)\le C_{a,b,c},\qquad
F(g)=C_{a,b,c} \Longleftrightarrow\
g=\tau h^*\text{ for some }\tau>0.
\tag{7.10}
$$
This is a unique ray in the labelled coordinate space. On that ray the
actual Fiedler eigenvalue is $\lambda_2(g)=\tau$, the resistance is
$R(g)=C_{a,b,c}/\tau$, and the full original $n$-vertex spectrum is

$$
0\ \text{once},\qquad
\tau\ \text{with multiplicity }n-3,\qquad
\frac{\tau(3-\sqrt{1-4\eta})}{2},\qquad
\frac{\tau(3+\sqrt{1-4\eta})}{2}.
\tag{7.11}
$$
Each of the last two entries has multiplicity one, with multiplicities
added when they coincide. On the auxiliary domain
$\mathcal C_{a,b,c}$ the bound is $R(h)\le C_{a,b,c}$, with equality
exactly at $h=h^*$. Thus nonnegative competitors do not create further
normalized equality points.

*Proof.* Write $x=a+b-c$, $y=a+c-b$, $z=b+c-a$. These are positive,
$a=(x+y)/2$, $b=(x+z)/2$, $c=(y+z)/2$, and

$$
\eta=\frac{2xyz}{(x+y)(x+z)(y+z)}\le\frac14.
$$
The three arithmetic-geometric mean inequalities in the denominator
are simultaneous equalities exactly when $x=y=z$, equivalently
$a=b=c$. This proves the first assertions in (7.9).

Take any $h\in\mathcal C_{a,b,c}$ and the matrices in Lemma 7.2.
The nonzero-vertex spectral excesses
$q_k=\lambda_k(h)-1$ for $2\le k\le n$ are nonnegative; together with
one zero they are all the eigenvalues of $H$. Put

$$
\Delta=\sum_{k=2}^n\frac{q_k}{1+q_k},\qquad
\delta_* =\frac{1+2\eta}{2+\eta}.
$$
Then $S=\sum q_k\ge1$ and $R(h)/n=n-1-\Delta$.
The cited finite-list identity gives

$$
\Delta\ge\frac{S+2E(H)}{1+S+E(H)}.
\tag{7.12}
$$
Indeed, if $e_j$ are the elementary symmetric sums of the $q_k$,
$e_0=1$, its exact ratio is
$\Delta=(\sum_{j\ge1}j e_j)/(\sum_{j\ge0}e_j)$.
The ratio retaining only $e_0,e_1,e_2$ is strictly less than $2$, since
$2(1+S+E)-(S+2E)=2+S>0$; each omitted term has coefficient $j\ge3$.
Thus (7.12) applies with no rank premise.

If $1<S\le2$, set $s=S-1\in(0,1]$ and use Lemma 7.2. The numerator
in the difference between the right side of (7.12) and $\delta_*$ is

$$
\begin{aligned}
(1-\eta)(S-1)+3(E(H)-\eta)
&>\left(\frac14-\eta\right)s\ge0,
\end{aligned}
\tag{7.13}
$$
after multiplication by the positive denominator
$(1+S+E(H))(2+\eta)$. Hence $\Delta>\delta_*$ in this case.
If $S>2$, the trace comparison (3.5) gives

$$
\Delta\ge\frac S{1+S}>\frac23\ge\delta_*;
$$
the last inequality is equivalent to $\eta\le1/4$.
If $S=1$, Lemma 7.2 gives $E(H)\ge\eta$, and the right side of
(7.12) is increasing in $E(H)$, so $\Delta\ge\delta_*$.
Consequently every $h\in\mathcal C$ satisfies

$$
R(h)\le n(n-1-\delta_*)
=n\left(n-3+\frac3{2+\eta}\right)=C_{a,b,c},
\tag{7.14}
$$
and equality forces $S=1$.

We next determine the actual original edge coordinates when $S=1$.
Lemma 2.1 says $H$ annihilates each $U_I$ in (2.3), so
$L(h)(e_x-e_y)=e_x-e_y$ for distinct vertices of the same part.
At a vertex $r$ outside that part this equality reads
$-h_{\{r,x\}}+h_{\{r,y\}}=0$. At $x,y$ it gives
$d_x(h)=d_y(h)=1$, because $x,y$ are nonadjacent.
Every part has at least two vertices. Applying the outside-coordinate
identity to each part shows that each cross-part block is constant
in both endpoint labels, and every vertex degree is $1$.
Thus, if those three block values are $u,v,w$ on $AB,AC,BC$,

$$
bu+cv=1,\qquad au+cw=1,\qquad av+bw=1.
$$
Equivalently, the three block totals $ab u,ac v,bc w$ have pair sums
$a,b,c$. Their unique solution is exactly (7.1). Hence $h=h^*$.
Block constancy has followed from unrestricted equality, including
when one or more parts have size two.

It remains to show that this positive assignment has the stated scale
and attains the bound. All three values in (7.1) are finite and positive,
and its vertex degrees are all $1$. For this explicit assignment,
$U_A\oplus U_B\oplus U_C$ is invariant with eigenvalue $1$ and
dimension $n-3$: the cross-part sums of each difference vector vanish.
On its orthogonal complement the orthonormal basis
$f_A,f_B,f_C$ gives the restriction of the same original Laplacian as

$$
T=\begin{pmatrix}
1&-\sqrt{ab}\,h^*_{AB}&-\sqrt{ac}\,h^*_{AC}\\
-\sqrt{ab}\,h^*_{AB}&1&-\sqrt{bc}\,h^*_{BC}\\
-\sqrt{ac}\,h^*_{AC}&-\sqrt{bc}\,h^*_{BC}&1
\end{pmatrix},\qquad
\xi=(\sqrt a,\sqrt b,\sqrt c)^{\mathsf T},\qquad T\xi=0.
\tag{7.15}
$$
Let $K_*=T-I_3+\xi\xi^{\mathsf T}/n$. It is symmetric, annihilates
$\xi$, has trace $1$, and its diagonal entries are $a/n,b/n,c/n$.
The purely algebraic part of (7.5)–(7.7), with all $z_I=0$, gives
$E(K_*)=\eta$. Thus its other two eigenvalues are

$$
q_\pm=\frac{1\pm\sqrt{1-4\eta}}2>0.
$$
On $\xi^\perp$, $T=I_3+K_*$. Its two nonzero eigenvalues are
$1+q_-$ and $1+q_+$, and both exceed $1$. This proves (7.11) at
$\tau=1$, with $\lambda_2(h^*)=1$ on the original $n$ vertices.
The two remaining eigenvalues have sum $3$ and product $2+\eta$, so
(1.5) gives

$$
R(h^*)=n\left(n-3+\frac3{2+\eta}\right)=C_{a,b,c}.
$$
This proves attainment and the unique normalized equality on
$\mathcal C$. For arbitrary positive $g$, the normalization
$h=g/\lambda_2(g)$ belongs to $\mathcal C$ and has $R(h)=F(g)$.
Equation (7.14), the just-proved equality necessity and scaling (1.6)
give (7.9)–(7.11) with $\tau=\lambda_2(g)$. ∎

## 8. Coercivity, all sequences and every resistance level

**Lemma 8.1 (A coercive threshold on the original coordinates).** Fix
any integer triple $2\le a\le b\le c$. For every positive sequence
$(g_j)$ with

$$
\liminf_{j\to\infty}F(g_j)>n(n-2),
\tag{8.1}
$$
the sequence $h_j=g_j/\lambda_2(g_j)$ is bounded in every original
edge coordinate. More precisely, if $0<\epsilon<1$ and
$F(g_j)\ge n(n-2+\epsilon)$ eventually, then eventually

$$
S_j\le\frac{1-\epsilon}{\epsilon},\qquad
\sum_{e\in E}(h_j)_e\le\frac12\left(n-2+\frac1\epsilon\right).
\tag{8.2}
$$
Every cluster point $h$ belongs to $\mathcal C_{a,b,c}$ and has connected
support. If in addition $F(g_j)\to\ell$, then every such point satisfies
$R(h)=\ell$. Every $h\in\mathcal C_{a,b,c}$ satisfies
$R(h)\le M_{a,b,c}$ and is a limit of normalized positive assignments.
Thus if $\ell=M_{a,b,c}$, these cluster points are actual maximizers on
the connected nonnegative original domain.

*Proof.* For each $h_j$ let $q_{j,k},S_j,\Delta_j$ be as in the proof
of Theorem 3.2. The same original all-pairs identity and (3.5) give

$$
\Delta_j=n-1-\frac{F(g_j)}n\ge\frac{S_j}{1+S_j},\qquad S_j\ge1.
$$
The assumed eventual lower bound gives $\Delta_j\le1-\epsilon<1$,
so $S_j\le\Delta_j/(1-\Delta_j)\le(1-\epsilon)/\epsilon$.
Since $\operatorname{tr}L(h_j)=n-1+S_j=2\sum_e(h_j)_e$, this proves
(8.2). Such an $\epsilon$ exists under (8.1), and the finite preceding
part of the sequence also has bounded coordinates. Nonnegative
coordinates and the bound on their sum give boundedness individually.

There are finitely many original edges, hence every subsequence has a
further convergent subsequence. At its limit $h$, coordinate continuity
preserves $h\ge0$ and $\lambda_2(h)=1$. A nonnegative weighted
Laplacian has zero energy exactly on vectors constant on each component
of its positive support, by (1.3). Thus two or more components would
force $\lambda_2(h)=0$, which is impossible. The limit is connected.
All its nonzero eigenvalues are positive, so (1.5) and continuity of
the eigenvalues give $R(h)=\lim R(h_j)=\ell$ when that limit is assumed.
No resistance is assigned to a disconnected limit.

For completeness the bridge back to the positive domain is explicit.
For any fixed $h\in\mathcal C$ put

$$
p^{(\varepsilon)}=h+\varepsilon\mathbf1_E,\qquad
\widetilde p^{(\varepsilon)}
 =\frac{p^{(\varepsilon)}}{\lambda_2(p^{(\varepsilon)})}
 \quad(\varepsilon>0).
\tag{8.3}
$$
All original coordinates of $p^{(\varepsilon)}$ are positive and finite.
Continuity at the connected $h$ gives
$\lambda_2(p^{(\varepsilon)})\to1$ and
$\widetilde p^{(\varepsilon)}\to h$. Also
$F(p^{(\varepsilon)})=R(\widetilde p^{(\varepsilon)})\to R(h)$.
Each term is at most the positive-domain supremum $M$, proving
$R(h)\le M$. This also verifies that a connected nonnegative maximizer
with value $M$ is positively approximable on exactly the original
vertices and edge coordinates. ∎

**Theorem 8.2 (Complete sequence classification and all exact levels).**
Fix integers $2\le a\le b\le c<a+b$. For every sequence of arbitrary
positive original labelled assignments,

$$
F(g_j)\longrightarrow C_{a,b,c}
\quad\Longleftrightarrow\quad
\frac{g_j}{\lambda_2(g_j)}\longrightarrow h^*
\quad\text{in every original edge coordinate}.
\tag{8.4}
$$
For every $R_0>0$ the exact-resistance level has the attained maximum

$$
\max_{g\in\mathcal F_{a,b,c,R_0}}\lambda_2(g)
=\frac{C_{a,b,c}}{R_0},
\qquad
\operatorname*{argmax}_{g\in\mathcal F_{a,b,c,R_0}}\lambda_2(g)
=\left\{\frac{C_{a,b,c}}{R_0}h^*\right\}.
\tag{8.5}
$$
For every sequence in that exact level set,

$$
\lambda_2(g_j)\longrightarrow\frac{C_{a,b,c}}{R_0}
\quad\Longleftrightarrow\quad
g_j\longrightarrow\frac{C_{a,b,c}}{R_0}h^*
\quad\text{in every original edge coordinate}.
\tag{8.6}
$$
The full original-vertex spectrum at the maximum is (7.11) with
$\tau=C_{a,b,c}/R_0$.

*Proof.* By $\eta\le1/4$, and in particular $\eta<1$,

$$
\frac{C_{a,b,c}}n=n-3+\frac3{2+\eta}>n-2.
$$
Thus a sequence satisfying the left side of (8.4) meets Lemma 8.1.
Its normalized sequence is bounded, and every cluster point is connected
and has resistance $C_{a,b,c}$. Theorem 7.3 forces every such point
to be $h^*$. Hence the whole normalized sequence converges to $h^*$:
otherwise a subsequence stays a fixed positive distance from $h^*$,
and boundedness supplies a further cluster point at that distance,
a contradiction. Conversely, normalized convergence to $h^*$ and
continuity of $R$ there give
$F(g_j)=R(g_j/\lambda_2(g_j))\to R(h^*)=C_{a,b,c}$.
This proves both directions with no symmetry or boundedness premise
on the original $g_j$.

Theorem 5.1 supplies the exact scaling bijection for every positive
resistance level. Applying Theorem 7.3 to that bijection gives (8.5):
the unique point on its equality ray has scale $C/R_0$, all its original
conductances are finite and positive, and its resistance is exactly
$C/(C/R_0)=R_0$. Its spectrum follows from (7.11).

For an exact-level sequence, $F(g_j)=R_0\lambda_2(g_j)$.
If it is maximizing, (8.4) gives
$g_j/\lambda_2(g_j)\to h^*$ and its scalar multiplier tends to
$C/R_0$. Their product tends to $(C/R_0)h^*$, proving necessity in
(8.6). Conversely, this original-coordinate convergence implies
$\lambda_2(g_j)\to\lambda_2((C/R_0)h^*)=C/R_0$ by eigenvalue
continuity and the actual spectral scale in Theorem 7.3. ∎

**Corollary 8.3 (Balanced graphs with unrestricted competitors).** For
every integer $m\ge2$, on the labelled $K_{m,m,m}$ with all $3m^2$
original conductances independently positive,

$$
M_{m,m,m}=m(9m-5),\qquad h^*_e=\frac1{2m}.
\tag{8.7}
$$
Equality holds precisely on the unique constant ray
$g_e=\tau/(2m)$, $\tau>0$, with actual spectrum
$0$ once, $\tau$ with multiplicity $3m-3$, and $3\tau/2$ with
multiplicity two. Every arbitrary positive sequence is maximizing
exactly when $g_{j,e}/\lambda_2(g_j)\to1/(2m)$ for every original edge.
For every $R_0>0$ the unique exact-level maximizer has

$$
g_e=\frac{9m-5}{2R_0}\quad(e\in E),\qquad
\lambda_2(g)=\frac{m(9m-5)}{R_0},
\tag{8.8}
$$
and an exact-level sequence is maximizing exactly when all its original
edge coordinates tend to the values in (8.8).

*Proof.* Substitute $a=b=c=m$, $n=3m$, $\eta=1/4$ in Theorems 7.3
and 8.2. The two final spectral entries in (7.11) coincide and their
multiplicities add. The classical value at the uniform assignment is
already supplied by Bapat–Karimi–Liu,
[*Kirchhoff Index and Degree Kirchhoff Index of Complete Multipartite
Graphs*, arXiv:1611.09457v1](https://arxiv.org/pdf/1611.09457v1),
Proposition 3.3 and Corollary 3.5: on the unweighted $K_{m,m,m}$ their
positive spectrum is $2m$ with multiplicity $3m-3$ and $3m$ with
multiplicity two, and their unordered-pair Kirchhoff index is
$(9m-5)/2$. Their vertices and unit conductances are the same original
ones here, so multiplying that index by $2m$ gives (8.7)'s value at
uniform weights. The unrestricted upper comparison, equality necessity
and both sequence equivalences asserted here follow instead from
Theorems 7.3 and 8.2, which apply to every independent positive
assignment. ∎

## 9. Whole deletion faces and the remaining complementary problem

**Definition 9.1 (Deletion faces on the same original vertices).** For
any $2\le a\le b\le c$, let $\mathcal D_{IJ}$ consist of the connected
nonnegative assignments on the original $K_{a,b,c}$ whose entire $IJ$
edge class is zero. The other two edge classes are nonnegative; their
strictly positive subdomain is included. Deleting $AB$, $AC$ or $BC$
gives, respectively, the labelled bipartite graphs

$$
K_{a+b,c}\text{ on }(A\sqcup B,C),\quad
K_{a+c,b}\text{ on }(A\sqcup C,B),\quad
K_{b+c,a}\text{ on }(B\sqcup C,A).
\tag{9.1}
$$
These are actual vertex bijections with identical edge sets after
deletion. Their ordinary $n$ by $n$ Laplacians and all unordered
original-pair resistances coincide, including pairs lying in different
original parts that become nonedges. No vertices are identified and
no pair is removed from the resistance sum.

**Proposition 9.2 (Two strict failures of whole-deletion comparisons).**
For $K_{2,2,2}$ the attained positive maximum is $26$, while each of
the three whole-deletion faces has maximum $51/2<26$. For $K_{2,2,5}$,

$$
\max_{g\in\mathcal D_{AB}}F(g)=64,\qquad
\max_{g\in\mathcal D_{AC}}F(g)
=\max_{g\in\mathcal D_{BC}}F(g)=\frac{450}{7}>64,
\qquad M_{2,2,5}\ge\frac{450}{7}.
\tag{9.2}
$$
The last bound is obtained by strictly positive approximants on the
original tripartite graph. These statements refute, respectively, a
universal reduction to a best whole-deletion face and a universal
choice of the $AB$-deletion face. They assert neither the exact value
of $M_{2,2,5}$ nor that a best deletion face always gives the
tripartite supremum.

*Proof.* Theorem 7.3, or Corollary 8.3 with $m=2$, gives the positive
$K_{2,2,2}$ maximum $2(18-5)=26$. Every whole deletion is $K_{2,4}$
on the same six vertices, by (9.1). Apply the whole
[two-hub theorem](FIEDLER_RESISTANCE_K2M_OPTIMIZER.md), Theorem 2.1,
with its two hubs equal to one original part and its four
leaves equal to the union of the other two parts. Its unrestricted
positive product maximum is

$$
(4+2)\left(4+\frac14\right)=\frac{51}{2}.
$$
Its strictly positive bipartite equality assignments belong to the
specified deletion face, proving face attainment.

For $K_{2,2,5}$, deleting $AB$ gives $K_{4,5}$. The whole
[general bipartite theorem](FIEDLER_RESISTANCE_GENERAL_BIPARTITE_OPTIMIZER.md),
Theorem 4.1, applies with its smaller class of size $4$ mapped
bijectively onto $A\sqcup B$ and its larger class onto $C$.
Its hypotheses $4\le4\le5$ hold. Substitution of $n=9$ and $d=1$
into its constant gives

$$
9(9-3)+\frac{5(1+3)}{1+1}=64.
$$
Deleting $AC$ instead gives $K_{2,7}$ with hubs $B$ and leaves
$A\sqcup C$; deleting $BC$ gives the same graph with hubs $A$ and
leaves $B\sqcup C$. The whole two-hub Theorem 2.1 applies with $m=7$
and gives

$$
(7+2)\left(7+\frac17\right)=\frac{450}{7},\qquad
\frac{450}{7}-64=\frac27>0.
$$
All these are whole-domain bipartite optimizations, not uniform-weight
values. Their equality conductances are strictly positive on every
retained bipartite edge. If a face assignment has further zero
coordinates but connected support, add $\varepsilon$ to every retained
edge. This stays in that face and gives positive bipartite conductances
converging to the given connected assignment. Eigenvalue and resistance
continuity from Convention 1.2 transfer the same upper bound to it.
Thus the displayed positive bipartite optimizers attain the maxima on
the entire connected nonnegative faces as defined in Definition 9.1.

Finally take any bipartite optimizer on the $AC$-deletion face in the
$K_{2,2,5}$ example. Add $\varepsilon>0$ to every deleted $AC$ edge,
leaving the positive retained coordinates fixed. These are finite
strictly positive assignments on all original tripartite edges.
Their Laplacians tend to the connected face Laplacian on the same nine
vertices, so their products tend to $450/7$. This proves the last
inequality in (9.2) within the original positive domain. The two strict
comparisons prove the stated route failures and give no upper
comparison for every positive weighting of $K_{2,2,5}$. ∎

**Proposition 9.3 (A two-vertex part supplies partial coercivity).** For
every integer triple $2=a\le b\le c$, with $n=2+b+c$,

$$
M_{2,b,c}\ge n\left(n-2+\frac1{n-2}\right)>n(n-2).
\tag{9.3}
$$
Every positive maximizing sequence $g_j$, that is
$F(g_j)\to M_{2,b,c}$, is bounded after normalization by its own
$\lambda_2(g_j)$. Each cluster point of
$g_j/\lambda_2(g_j)$ is a connected nonnegative original assignment
with $\lambda_2=1$ and $R=M_{2,b,c}$. In particular at least one
such cluster point exists. For $c>b+2$, this gives no exact value of
$M_{2,b,c}$, no classification of these maximizers, and no assertion
of positive attainment.

*Proof.* Delete $BC$, identifying the retained graph by an actual
vertex bijection as $K_{2,n-2}$ with hubs $A$ and leaves $B\sqcup C$.
Here $m=n-2=b+c\ge4$, so the whole two-hub Theorem 2.1 applies.
At its equality assignment with scale $t=1$ it supplies finite positive
conductances on all retained edges, $\lambda_2=1$, and product

$$
(m+2)\left(m+\frac1m\right)
=n\left(n-2+\frac1{n-2}\right).
$$
Set the deleted coordinates to zero and then add $\varepsilon>0$ to
every $BC$ edge. The limiting support is connected. As in Proposition
9.2, continuity on the same original vertices and pairs proves the
lower bound by positive tripartite approximants. Its excess above
$n(n-2)$ is $n/(n-2)>0$.
The supremum $M$ is finite by Theorem 3.2. A maximizing sequence exists
by the definition of supremum on the nonempty positive domain.
Every such sequence satisfies (8.1), so Lemma 8.1 gives boundedness,
connectedness and the value of each normalized cluster point, as well
as a convergent subsequence. The positive-approximation bridge in that
lemma identifies its value as a maximum on the connected nonnegative
original domain. None of these steps determines its coordinates or
makes its zero coordinates positive. ∎

**Definition 9.4 (The remaining exact all-weight and sequence bridges).**
The strict-triangle part of Definition 6.2 is determined by Theorems
7.3 and 8.2. The case $c=a+b$ is supplied by Theorems 4.1, 4.3, 5.1
and 5.2, including its nonattainment and full sequence classification.
For every integer triple $2\le a\le b\le c$ with $c>a+b$, the
remaining complementary target is still the exact value of
$M_{a,b,c}$, the full positive equality set
$\mathcal E_{a,b,c}$, positive attainment or nonattainment, and a
classification of every positive maximizing sequence on the original
labelled coordinates, together with its exact-$R_0$ counterpart for
every $R_0>0$.

The all-weight bridge requires a sharp upper comparison for every
$g\in(0,\infty)^{ab+ac+bc}$, matching positive assignments or positive
approximants, and necessity of every claimed equality coordinate.
An optimum within block-constant weights, within a deletion face, or
under an additional trace or rank constraint does not provide that
comparison. Proposition 6.1 remains an upper estimate and Propositions
9.2–9.3 supply specified lower estimates; they do not identify this
exact value for $c>a+b$.

The sequence bridge requires controlling all normalized escape
sequences and identifying every connected nonnegative original
maximizer that can occur as a limit. If normalized coordinates are
bounded, Lemma 8.1's connected-limit and positive-approximation argument
is available; the actual limiting coordinates still have to be
determined. For $a=2$, Proposition 9.3 supplies boundedness and connected
maximizing cluster points but leaves their complete set and positive
attainment undetermined when $c>a+b$. For general $a$, a coercivity
argument or a complete treatment of unbounded normalization is also
required. Theorem 5.1 transfers an established product answer and its
positive equality rays to every exact resistance level; it does not
supply these missing all-weight or sequence conclusions.

## 追加锚（本行以下为增补区）

## 10. Exterior parameters and all escapes in original coordinates

**Definition 10.1 (Exterior parameters and mathematical inputs).** In
Sections 10–15 assume throughout that

$$
2\le a\le b\le c,\qquad m=a+b,\qquad c>m,\qquad
n=m+c,\qquad d=c-m\in\mathbb N_{>0}.
\tag{10.1}
$$

The labelled vertices, original edge coordinates, counting inner product,
all unordered original-pair resistance, and domains $\mathcal P$,
$\mathcal N$, $\mathcal C$ are exactly Definitions 1.1 and 3.1.
Write $M=M_{a,b,c}$ and set

$$
B_\infty=n(n-3)+m+1,\qquad
B_{\rm bip}=n(n-3)+\frac{c(d+3)}{d+1}.
\tag{10.2}
$$

Distances between conductance vectors are Euclidean distances in
$\mathbb R^E$, with the original labelled coordinates. For a nonempty
set $K$, $\operatorname{dist}(h,K)=\inf_{k\in K}\|h-k\|_2$.

The identity $R=n\operatorname{tr}L^+$, its connected nonnegative
extension and its scaling are the classical inputs in Convention 1.2.
In Ghosh–Boyd–Saberi,
[*Minimizing Effective Resistance of a Graph*, DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf),
§§2.4–2.6, equations (8), (13)–(15), the correspondence remains
$G=L(g)$, $g_l=g_e$, and $R_{\rm tot}=R(g)$, with all $n$ vertices
and all unordered pairs retained. Cruz Ortega–Menéndez-Conde,
[*Maximal Algebraic Connectivity for Paths with Fixed Effective
Resistance*, arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1),
§5, equation (3), supplies the fixed-resistance formulation and its
scale-invariant product correspondence.
The whole bipartite optimizers used below are the
[two-hub Theorem 2.1](FIEDLER_RESISTANCE_K2M_OPTIMIZER.md),
[three-hub Theorems 2.2–4.1](FIEDLER_RESISTANCE_K3M_OPTIMIZER.md), and
[general bipartite Theorems 3.1–4.1](FIEDLER_RESISTANCE_GENERAL_BIPARTITE_OPTIMIZER.md).
Their uses are whole-domain substitutions with the vertex maps specified
in the proofs, rather than new bipartite optimizations.
The escape estimate, its compactness consequences, the comparisons
between the three face values, the exhaustive rank-one classification
and the upper comparison in Section 14 are additional deductions here.

For the design interpretation, the matrix
$\mathcal I(g)=Q^{\mathsf T}L(g)Q$ in Definition 7.1 uses every original
incidence vector. Rosa–Harman,
[*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1),
§§2.3–2.4 and Theorem 1, supplies the correspondence
$F=n(n-1)\Phi_E/\Phi_A$. Every positive conductance ray has exactly
one representative $p_e=g_e/\sum_f g_f$ in the positive simplex, so
this same ratio on these design points is an equivalent formulation.
Optimizing an individual criterion or choosing a fixed number of edges
does not supply that ratio optimum. No theorem from Harman,
[*Minimal efficiency of designs under the class of orthogonally invariant
information criteria*, DOI:10.1007/s001840300301](https://link.springer.com/article/10.1007/s001840300301),
or the [Menéndez-Conde article 16817](https://repository.uaeh.edu.mx/revistas/index.php/icbi/article/view/16817)
is a premise below.

**Theorem 10.2 (A sufficient ceiling for every normalized escape).** Let
$(h_j)$ be any sequence in $\mathcal C_{a,b,c}$ such that
$\max_{e\in E}(h_j)_e\to\infty$. Then

$$
\limsup_{j\to\infty}R(h_j)\le B_\infty.
\tag{10.3}
$$

If any fixed $e\in E_{AB}$ satisfies $(h_j)_e\to\infty$, without
any boundedness assumption on the other coordinates, the stronger bound is

$$
\limsup_{j\to\infty}R(h_j)\le n(n-3)+m.
\tag{10.4}
$$

These are sufficient escape ceilings; no sharpness is asserted.

*Proof.* Throughout, normalization is the actual condition
$\lambda_2(L(h_j))=1$, so $L(h_j)\succeq P$ and
$R(h_j)\le n(n-1)$. Choose a subsequence along which $R(h_j)$ tends
to its limsup. After further subsequences, each of the finitely many
edge coordinates has a limit in $[0,\infty]$. At least one limit is
infinite. This selection preserves the resistance limit. It suffices
to handle every resulting possibility.

Suppose first that two distinct edges $e,f$ have infinite limits.
Their incidence vectors $b_e=e_x-e_y$ and $b_f=e_z-e_t$ are linearly
independent: proportional nonzero incidence vectors of unordered
simple-graph edges have the same two endpoints. The matrix
$b_e b_e^{\mathsf T}+b_f b_f^{\mathsf T}$ has two strictly positive
eigenvalues. Since

$$
L(h_j)\succeq
\min\{(h_j)_e,(h_j)_f\}
       (b_e b_e^{\mathsf T}+b_f b_f^{\mathsf T}),
$$

the min–max principle makes the largest two eigenvalues of $L(h_j)$
tend to infinity. Every other positive eigenvalue is at least $1$.
Consequently

$$
\limsup_j R(h_j)\le n(n-3)<B_\infty.
\tag{10.5}
$$

There is no assumption about the relative divergence rates.

It remains to consider exactly one edge $e=\{u,v\}$ with infinite
limit. All other coordinates now have finite limits. Put

$$
 b=e_u-e_v,\qquad t_j=(h_j)_e,\qquad
 L(h_j)=t_jbb^{\mathsf T}+L_j^0,\qquad L_j^0\longrightarrow L^0.
$$

Here $L_j^0$ is the actual original Laplacian with only coordinate $e$
set to zero; its support need not be connected. Let

$$
 W=\mathbf1^\perp\cap b^\perp,\qquad
 Q=P-\tfrac12bb^{\mathsf T},\qquad
 T=(QL^0Q)|_W.
\tag{10.6}
$$

The matrix $Q$ is the orthogonal projection onto $W$, whose dimension
is $n-2$. For $z\in W$, the divergent edge contributes zero energy,
and $z^{\mathsf T}L_j^0z=z^{\mathsf T}L(h_j)z\ge\|z\|^2$.
Passing to the limit proves $T\succeq I_W$.

In the orthogonal decomposition
$\mathbf1^\perp=\mathbb R(b/\sqrt2)\oplus W$, the original Laplacian
has block matrix

$$
\begin{pmatrix}2t_j+\alpha_j&v_j^{\mathsf T}\\
                 v_j&T_j\end{pmatrix},\qquad
\alpha_j,v_j\text{ bounded},\qquad T_j\to T\succeq I_W.
$$

Its inverse has Schur complement
$T_j-v_jv_j^{\mathsf T}/(2t_j+\alpha_j)\to T$.
The inverse therefore tends to $0\oplus T^{-1}$. In particular the
original all-pairs identity gives the exact limit

$$
\lim_j R(h_j)=n\operatorname{tr}_W T^{-1}.
\tag{10.7}
$$

This is an inverse limit in the original counting space; no contracted
graph resistance or replacement vertex measure has been substituted.

Choose an original independent set $I$ containing neither $u$ nor $v$,
and write $k=|I|\ge2$. Define on the full original space

$$
H_0=QL^0Q-Q\succeq0.
$$

It vanishes on $W^\perp$, in particular on $\mathbf1$.
For $i\in I$, $Qe_i=e_i-\mathbf1/n$. Since $L^0\mathbf1=0$ and
$I$ is independent, its $I$ block is

$$
(H_0)_{II}=\operatorname{diag}(d_i^0-1)_{i\in I}
                 +\frac1n\mathbf1_I\mathbf1_I^{\mathsf T}.
\tag{10.8}
$$

Taking the trace on the $k-1$ dimensional difference space supported
on $I$ gives
$0\le (k-1)(\sum_{i\in I}d_i^0-k)/k$.
Thus, for Gram vectors $v_x$ of $H_0$ and
$A_I=\sum_{i\in I}\|v_i\|^2$, (10.8) implies

$$
 A_I\ge\frac kn,\qquad
 \left\|\sum_{i\in I}v_i\right\|^2
 =A_I+\frac{k(k-1)}n\ge\frac{k^2}n.
$$

Also $\sum_{x\in V}v_x=0$, because the squared norm of this sum is
$\mathbf1^{\mathsf T}H_0\mathbf1=0$. Cauchy–Schwarz on the other
$n-k$ original vectors now yields

$$
 S_0:=\operatorname{tr}H_0
 \ge\frac kn+\frac{k^2}{n(n-k)}=\frac{k}{n-k}.
\tag{10.9}
$$

Let $q_1,\ldots,q_{n-2}\ge0$ be the eigenvalues of $T-I_W$.
They sum to $S_0$. Applying the finite-list comparison (3.5) to this
same list, not to separately optimized spectra, gives

$$
\begin{aligned}
\operatorname{tr}_W T^{-1}
 &=n-2-\sum_{r=1}^{n-2}\frac{q_r}{1+q_r}\\
 &\le n-2-\frac{S_0}{1+S_0}
 \le n-2-\frac kn.
\end{aligned}
\tag{10.10}
$$

If $e\in E_{AB}$, take $I=C$ and $k=c$. Equations (10.7)–(10.10)
give $n(n-2)-c=n(n-3)+m$.
If $e$ joins $C$ to either other part, take $I$ to be $C$ with that
endpoint removed. Then $k=c-1\ge2$, and the bound is
$n(n-2)-(c-1)=B_\infty$. These alternatives cover every original
edge. They prove (10.3) on the chosen limsup subsequence and hence on
the original sequence. Under the additional hypothesis of (10.4),
every such subsequence either has at least two infinite edge limits,
where (10.5) applies, or has just the stated $AB$ edge with infinite
limit, where the stronger choice $I=C$ applies. This proves (10.4)
even if other original coordinates are unbounded. ∎

## 11. Compact superlevels and the entire nonnegative optimizer set

**Theorem 11.1 (Existence above the escape ceiling).** For every exterior
triple (10.1),

$$
M\ge B_{\rm bip}>B_\infty.
\tag{11.1}
$$

For every real $\alpha>B_\infty$ the set

$$
\mathcal S_\alpha=\{h\in\mathcal C_{a,b,c}:R(h)\ge\alpha\}
\tag{11.2}
$$

is compact, with the empty set allowed. There is a nonempty compact set

$$
K=\{h\in\mathcal C_{a,b,c}:R(h)=M\},\qquad
M=\max_{h\in\mathcal C_{a,b,c}}R(h).
\tag{11.3}
$$

Here $K$ denotes the entire optimizer set, not a selected collection of
face suppliers. Its definition is implicit.

*Proof.* Use the whole general bipartite Theorem 4.1 with smaller class
of size $m=a+b\ge4$, larger class of size $c>m$, and its original
vertices mapped bijectively onto $(A\sqcup B,C)$. Its retained edges
are precisely $E_{AC}\sqcup E_{BC}$; set every $AB$ coordinate to zero.
For any chosen label $x_*\in A\sqcup B$, its normalized supplier is

$$
 h_{x_*w}=\frac{d+1}{c},\qquad
 h_{xw}=\frac1c\quad(x\in(A\sqcup B)\setminus\{x_*\},\ w\in C),
 \qquad h|_{E_{AB}}=0.
\tag{11.4}
$$

The supplier proves $\lambda_2(h)=1$, connectedness and
$R(h)=B_{\rm bip}$ on all $n$ original vertices. Its complete spectrum
is $0$, $1$ with multiplicity $n-3$, and $\mu_-,\mu_+$, where

$$
\mu_-+\mu_+=d+3,\qquad
\mu_-\mu_+=\frac{n(d+1)}c,\qquad 1<\mu_-\le\mu_+.
$$

Thus the map preserves the Laplacian, counting measure and every
unordered pair, including original $AB$ pairs which are now nonedges.
It is a whole optimizer on that bipartite face, not an upper comparison
for the tripartite domain. The positive approximants (8.3) on all
original edges give $M\ge B_{\rm bip}$. Direct subtraction gives

$$
B_{\rm bip}-B_\infty
 =d-1+\frac{2c}{d+1}>0.
\tag{11.5}
$$

The domain $\mathcal C$ is closed in $\mathbb R^E$: limits preserve
nonnegativity and $\lambda_2=1$. Such limits have connected support,
and $R$ is continuous there, by Convention 1.2. Hence
$\mathcal S_\alpha$ is closed. If it were unbounded, one could choose
$h_j\in\mathcal S_\alpha$ with $\max_e(h_j)_e\to\infty$.
Theorem 10.2 would give
$\alpha\le\limsup_jR(h_j)\le B_\infty$, a contradiction.
Finite-dimensional closedness and boundedness prove compactness.

A positive maximizing sequence exists by the definition of the finite
supremum $M$. Normalize each term by its own $\lambda_2$.
Choose $\alpha$ strictly between $B_\infty$ and $B_{\rm bip}$.
The normalized tail belongs to $\mathcal S_\alpha$, so it has a limit
point $h\in\mathcal C$ with $R(h)=M$. For every $h\in\mathcal C$,
the explicit positive approximation (8.3) gives $R(h)\le M$.
This proves the maximum assertion and nonemptiness of $K$.
Finally $K$ is a closed subset of the compact $\mathcal S_\alpha$,
so it is compact. ∎

**Theorem 11.2 (Every positive maximizing sequence).** For every sequence
$(g_j)$ of arbitrary independent positive original-edge assignments, put
$h_j=g_j/\lambda_2(g_j)$. Then

$$
F(g_j)\longrightarrow M
\quad\Longleftrightarrow\quad
\operatorname{dist}(h_j,K)\longrightarrow0.
\tag{11.6}
$$

Every maximizing sequence $(h_j)$ is bounded. Its cluster points all
belong to $K$. Conversely, every point of $K$ is the limit of a
normalized strictly positive maximizing sequence.

*Proof.* If $F(g_j)\to M$, take $\alpha$ as in the proof of
Theorem 11.1. The tail of $(h_j)$ lies in $\mathcal S_\alpha$; its
finitely many preceding terms do not affect boundedness. Every cluster
point has $\lambda_2=1$ and resistance $M$, hence belongs to $K$.
If the distances failed to tend to zero, a subsequence would have
distance at least some $\epsilon>0$ from $K$. Compactness supplies a
further subsequence converging to a point of $K$, a contradiction.

Conversely suppose the distances tend to zero. Compactness of $K$
allows a nearest $k_j\in K$ to be chosen for each $h_j$.
Then $\|h_j-k_j\|_2\to0$ and $(h_j)$ is bounded. If
$R(h_j)$ did not tend to $M$, some subsequence would stay a fixed
positive distance in resistance from $M$. Pass to a further subsequence
with $k_j\to k\in K$; then $h_j\to k$. Continuity at this connected
limit gives $R(h_j)\to R(k)=M$, a contradiction. Since
$F(g_j)=R(h_j)$, this proves the reverse implication for every positive
sequence, without any initial boundedness assumption.

For any fixed $k\in K$, the vectors
$(k+\epsilon\mathbf1_E)/\lambda_2(k+\epsilon\mathbf1_E)$ in (8.3)
are strictly positive, normalized, and converge to $k$ as
$\epsilon\downarrow0$. Their resistances tend to $R(k)=M$.
Choosing any positive sequence $\epsilon_j\downarrow0$ proves the
last assertion. ∎

## 12. Exact comparison of all three whole-deletion faces

**Definition 12.1 (Face-value notation).** For the fixed exterior triple,
define, for integers $2\le k<n/2$,

$$
\beta_n(k)=n(n-3)+\begin{cases}
 n+1+\dfrac2{n-2},&k=2,\\[4pt]
 n-k+1+\dfrac{n-1}{n-2k+1},&k\ge3.
 \end{cases}
\tag{12.1}
$$

All face values below refer to connected nonnegative assignments on
exactly the original vertices, as in Definition 9.1, and to the
scale-invariant product $F$. The smaller bipartite class has size $m$
for $\mathcal D_{AB}$, $b$ for $\mathcal D_{AC}$, and $a$ for
$\mathcal D_{BC}$; all are strictly less than $n/2$ by $c>a+b$.

**Theorem 12.2 (Whole-face maxima and labelled suppliers).** On the three
entire faces,

$$
 X:=\max_{\mathcal D_{AB}}F=\beta_n(m)=B_{\rm bip},\qquad
 Y:=\max_{\mathcal D_{AC}}F=\beta_n(b),\qquad
 Z:=\max_{\mathcal D_{BC}}F=\beta_n(a).
\tag{12.2}
$$

Each displayed value is attained by finite conductances positive on
every retained edge. Explicit normalized suppliers are as follows.
Map the smaller class onto a labelled set $S$ of size $k$, and the
larger onto its complement $T$ of size $\ell=n-k$. Set the deleted
original edge class to zero. If $k=2$, write $S=\{s_1,s_2\}$ and take

$$
 h_{s_1t}=\tfrac12\left(1+\epsilon\sqrt{\frac{n-4}{n}}\right),\qquad
 h_{s_2t}=\tfrac12\left(1-\epsilon\sqrt{\frac{n-4}{n}}\right)
 \quad(t\in T),\qquad \epsilon\in\{-1,1\}.
\tag{12.3}
$$

If $k\ge3$, choose any $s_*\in S$ and take

$$
 h_{s_*t}=\frac{\ell-k+1}{\ell},\qquad
 h_{st}=\frac1\ell\quad(s\in S\setminus\{s_*\},\ t\in T).
\tag{12.4}
$$

In these formulas $(S,T)$ is respectively
$(A\sqcup B,C)$, $(B,A\sqcup C)$ or $(A,B\sqcup C)$.
In particular $M\ge\max\{X,Y,Z\}$; this is a lower comparison for
$M$, not an assertion of equality with any face value.

*Proof.* Each indicated map is an actual vertex bijection of the
bipartite graph in (9.1). Its retained edges, ordinary Laplacian and all
unordered original-pair resistances are identical; no vertices are
identified. If $k=2$, the whole two-hub Theorem 2.1 applies with
$\ell=n-2\ge3$. It gives (12.3) and product
$n(n-2+1/(n-2))=\beta_n(2)$, using
$n/(n-2)=1+2/(n-2)$.
If $k=3$, the whole three-hub Theorems 2.2 and 3.1 apply with
$\ell=n-3>3$. Their normalized rows are
$(\ell-2)/\ell,1/\ell,1/\ell$, precisely (12.4), and their product is

$$
\ell n+\frac{\ell^2}{\ell-2}
 =n(n-3)+n-1+\frac4{n-5}=\beta_n(3).
$$

For $k\ge4$, the whole general bipartite Theorems 3.1–4.1 apply
with $4\le k<\ell$ and give (12.4). Their constant is

$$
 n(n-3)+\frac{\ell(\ell-k+3)}{\ell-k+1}
 =n(n-3)+n-k+1+\frac{n-1}{n-2k+1}=\beta_n(k).
$$

These whole theorems optimize every independent positive retained
coordinate, not just the displayed row-constant suppliers. Each
supplier has actual $\lambda_2=1$ and connected support.
For a face assignment with additional zero retained coordinates and
connected support, add $\epsilon>0$ to every retained edge. This
converges within the same face through strictly positive bipartite
assignments, so continuity extends the whole upper comparison to that
assignment. The displayed positive retained suppliers therefore attain
the maximum on the entire connected nonnegative face. This extension
does not assert that a positive-domain equality classification alone
classifies all further-zero face equalities.
Finally adding $\epsilon$ to the deleted original coordinates of any
supplier gives strictly positive tripartite assignments whose products
tend to its face value. This proves the lower comparison for $M$. ∎

**Theorem 12.3 (Every integer boundary and every face-value tie).** Retain
$X,Y,Z$ from (12.2).
If $a=b=2$, then $Y=Z>X$ for every $d\ge1$.
If $a=2<b$, then $Z>\max\{X,Y\}$ and the remaining comparison is

$$
\operatorname{sgn}(X-Y)
 =\operatorname{sgn}\bigl(4b-4(d-1)-d^2-3\bigr).
\tag{12.5}
$$

For $d=1,2$ this sign is positive. For $d\ge3$, it changes according
as $b$ is below, equal to, or above

$$
 b_0=d-1+\frac{d^2+3}{4}.
\tag{12.6}
$$

The equality $X=Y$ occurs exactly when $d\ge3$ is odd and $b=b_0$.
For even $d$ there is no integer tie.

If $a\ge3$, then $Z\ge Y$, with equality exactly when $a=b$, and

$$
\begin{aligned}
\operatorname{sgn}(X-Z)
 &=\operatorname{sgn}\bigl(4a-2b(d-1)-d^2-3\bigr),\\
\operatorname{sgn}(X-Y)
 &=\operatorname{sgn}\bigl(4b-2a(d-1)-d^2-3\bigr).
\end{aligned}
\tag{12.7}
$$

More explicitly, for $d=1$ one has $X>Z\ge Y$.
For $d=2$, one has $X>Z\ge Y$ if $b\le2a-4$.
If $d=2$ and $b\ge2a-3$, then $Z>X>Y$ except that
$(a,b)=(3,3)$ gives $Z=Y>X$.
For $d\ge3$ one always has $Z>X$, while the position of $X$
relative to $Y$ is decided by comparing $b$ to

$$
 b_0=\frac{a(d-1)}2+\frac{d^2+3}{4}:
 \quad b<b_0\Rightarrow X<Y,\quad
 b=b_0\Rightarrow X=Y,\quad
 b>b_0\Rightarrow X>Y.
\tag{12.8}
$$

Here $X=Y$ occurs exactly for odd $d\ge3$ and the integer $b=b_0$.
There is no $X=Z$ tie and no three-way tie. Together with $Y=Z$
exactly at $a=b$, the listed equalities exhaust all ties.

*Proof.* For real $k<n/2$ set

$$
 f(k)=n-k+1+\frac{n-1}{n-2k+1}.
$$

For integers $3\le r<s<n/2$, subtraction gives

$$
 f(s)-f(r)=(s-r)
 \left(-1+\frac{2(n-1)}{(n-2r+1)(n-2s+1)}\right),\qquad
 f''(k)=\frac{8(n-1)}{(n-2k+1)^3}>0.
\tag{12.9}
$$

For $a,b\ge3$ the denominator for $r=a,s=b$ exceeds $2(n-1)$,
because

$$
 (2b+d+1)(2a+d+1)-2(n-1)
 =4ab+2(a+b)(d-1)+d^2+3>0.
$$

Thus $f(a)>f(b)$ if $a<b$, and equality holds if $a=b$.
For $r=a,s=m$ and for $r=b,s=m$, the numerators of the parentheses
in (12.9), after multiplication by the positive denominators, are
respectively

$$
 J_a=4a-2b(d-1)-d^2-3,\qquad
 J_b=4b-2a(d-1)-d^2-3.
\tag{12.10}
$$

The factors $m-a=b$ and $m-b=a$ are positive. This proves (12.7).
For $d=1$, $J_a=4a-4>0$ and $J_b=4b-4>0$.
For $d=2$, $J_a=4a-2b-7$ is positive precisely when
$b\le2a-4$, and is negative precisely when $b\ge2a-3$;
it cannot vanish. Also $J_b=4b-2a-7$ is positive for all
$a\ge3,b\ge a$ except $(a,b)=(3,3)$, where it is $-1$.
For $d\ge3$,
$J_a\le4a-4b-d^2-3<0$.
The sign and zero of $J_b$ are exactly (12.8).
If $d$ is even its right-hand equation
$4b=2a(d-1)+d^2+3$ has an odd right side, so has no integer solution.
If $d\ge3$ is odd the value in (12.8) is an integer and is greater
than $a$, so it gives precisely the stated tie, strictly below $Z$.
These calculations also exclude $X=Z$ and three-way ties.

For $a=2$, compare the two-hub value $Z$ directly to $X$. Subtracting
$n(n-2)$ from each gives

$$
 X-n(n-2)=\frac{m-d(m-2)}{d+1},\qquad
 Z-n(n-2)=\frac n{n-2}>1.
\tag{12.11}
$$

At $d=1$ the first expression is $1$; at $d\ge2$ it is at most
$(4-m)/(d+1)\le0$, since $m\ge4$. Hence $Z>X$ always.
If also $b=2$, the $AC$ and $BC$ faces have the same two-hub value,
proving $Y=Z>X$.
If $b\ge3$, then $m=b+2\ge5$ and $n\ge11$. One has
$f(3)=n-1+4/(n-5)<n$, whereas
$Z-n(n-3)=n+1+2/(n-2)>n+1$.
The just-proved $X<Z$ gives the other endpoint inequality for $f(m)$.
Convexity in (12.9) bounds $f$ on $[3,m]$ by its endpoint maximum,
which is strictly below $Z-n(n-3)$. In particular $Y<Z$.
Both $b$ and $m$ are at least $3$, so (12.9) gives the sign (12.5)
by $J_b$ with $a=2$. It is positive for $d=1,2$ and $b\ge3$.
Solving $J_b=0$ for $d\ge3$ gives (12.6), with the same parity test
as above. All the face comparisons have now been covered. ∎

## 13. All normalized assignments with one-dimensional excess

**Theorem 13.1 (Exhaustive rank-one classification).** Among all
$h\in\mathcal C_{a,b,c}$ for an exterior triple, assignments with
$\operatorname{rank}(L(h)-P)=1$ exist if and only if $a=2$.
They are exactly the following assignments: choose an entire original
part $S=\{s_1,s_2\}$ of size two, apply (12.3) to every edge from
$S$ to $V\setminus S$, and set every original edge between the other
two parts to zero. There are exactly two such normalized assignments
when $a=2<b$, and exactly four when $a=b=2$. Their common product is

$$
T_n=n\left(n-2+\frac1{n-2}\right).
\tag{13.1}
$$

No strictly positive original assignment has rank-one excess after
normalization by its own $\lambda_2$. This classification imposes no
rank restriction on unrestricted maximizers.

*Proof.* Factor $L(h)-P=vv^{\mathsf T}$, where $v\ne0$ and
$\sum_xv_x=0$. At distinct vertices of the same original part,
nonadjacency gives

$$
 v_xv_y=\frac1n.
\tag{13.2}
$$

Thus all entries in any one part have the same nonzero sign. If the
part has at least three vertices, comparing (13.2) for three labels
shows that all its entries equal either $1/\sqrt n$ or $-1/\sqrt n$.
In particular this holds for $C$, since $c>a+b\ge4$. Reverse $v$
if necessary so that $v_w=-1/\sqrt n$ for every $w\in C$.

For $x\notin C$, original conductance nonnegativity gives
$0\le h_{xw}=1/n+v_x/\sqrt n$, hence $v_x\ge-1/\sqrt n$.
A negative size-two part must also have both entries $-1/\sqrt n$:
their absolute values are at most $1/\sqrt n$ and their product is
$1/n$ by (13.2). Thus every negative part is uniform at that value.
A positive part of size at least three is uniform at $1/\sqrt n$.
A positive size-two part has entries $t/\sqrt n$ and
$1/(t\sqrt n)$ for some $t>0$.

If both $A$ and $B$ are positive, then all their entries must actually
be $1/\sqrt n$. Indeed a nonuniform positive size-two pair has one
entry greater than $1/\sqrt n$, while any other positive part has an
entry at least $1/\sqrt n$; their cross conductance
$1/n-v_xv_y$ would be negative. With both parts uniform positive,
the sum of $v$ is $(a+b-c)/\sqrt n\ne0$, impossible.
If both parts are negative, the sum is negative, also impossible.
There is therefore exactly one positive part $S$. If it had size at
least three, its uniform value would give total sum
$(2|S|-n)/\sqrt n<0$, because $|S|\le a+b<c$.
It must have size two; all other entries are $-1/\sqrt n$.
The zero-sum condition is now

$$
 t+t^{-1}=n-2.
\tag{13.3}
$$

There are exactly two positive roots, interchanged by $t\mapsto t^{-1}$,
since $n>4$. The two conductances from these hubs to every other
vertex are $(1+t)/n$ and $(1+t^{-1})/n$. Their sum is $1$ and their
product is $1/n$, so they are exactly

$$
 \tfrac12\left(1+\sqrt{\frac{n-4}{n}}\right),\qquad
 \tfrac12\left(1-\sqrt{\frac{n-4}{n}}\right).
$$

Between any two vertices outside $S$, the rank-one formula gives
$h_{xy}=1/n-1/n=0$ whenever that pair is an original edge. This
proves necessity of every coordinate.

Conversely each listed assignment is exactly the whole two-hub
supplier on $K_{2,n-2}$, with the two hubs mapped to the entire
original part $S$ and every other original vertex a leaf. Its support
is connected. The supplier gives full spectrum $0$, $1$ with
multiplicity $n-2$, and $n-2$ once, so $\lambda_2=1$, excess rank one
and product (13.1). All retained coordinates are positive.
Only $A$ can have size two when $a=2<b$; when $a=b=2$, either $A$
or $B$ can be chosen. For each choice the two unequal hub values give
two distinct labelled assignments. Assignments with different chosen
parts also differ: an edge from the other size-two part to $C$ is
zero for one and positive for the other. This gives the stated counts
and proves nonexistence if $a>2$. Each listed assignment has a whole
nonempty original edge class zero, proving the positive-domain
exclusion. No step assumes or concludes that unrestricted optimizers
have rank-one excess. ∎

## 14. A quantitative upper comparison below the exterior trace estimate

**Theorem 14.1 (An explicit strict upper bound for the supremum).** Put

$$
 N=n(n-2),\qquad q=d+3,\qquad B=B_{\rm bip},\qquad
 U_{\rm ext}=
 \frac{B+qN+n+\sqrt{(B+qN+n)^2-4qBN}}{2q}.
\tag{14.1}
$$

For every exterior triple,

$$
 \max\{B,N\}<U_{\rm ext}
 <n\left(n-2+\frac1{d+2}\right),\qquad
 B\le M<U_{\rm ext}.
\tag{14.2}
$$

Every independently positive original assignment therefore satisfies
$F(g)\le M<U_{\rm ext}$; in fact $R(h)<U_{\rm ext}$ for every
$h\in\mathcal C$. The number $U_{\rm ext}$ is an upper bound,
not an evaluation of the unrestricted supremum.

*Proof.* Write $V=N+n/(d+2)$ for the estimate in Proposition 6.1.
A direct computation gives

$$
 V-B=\frac{d(m-1)(d+3)}{(d+1)(d+2)}>0.
\tag{14.3}
$$

Consider the polynomial

$$
 p(r)=(r-N)(qr-B)-nr
     =qr^2-(B+qN+n)r+BN.
\tag{14.4}
$$

One has $p(N)=-nN<0$, and

$$
 p(B)=B\bigl((d+2)(B-N)-n\bigr)<0,\qquad
 p(V)=\frac n{d+2}(V-B)>0.
$$

Since $q>0$, these signs imply two distinct real roots, with the larger
root strictly between $\max\{B,N\}$ and $V$. The quadratic formula
identifies that root as (14.1), proving its reality and the first
comparisons in (14.2).

Fix any $h\in\mathcal C$ and put

$$
 r=R(h),\qquad x=\sum_{e\in E_{AB}}h_e\ge0.
$$

By Lemma 2.1, $D_C\ge c$. The sum of all original conductances is
$D_C+x$, so the trace excess satisfies
$S=2(D_C+x)-n+1\ge d+1+2x$.
The finite-list comparison (3.5) gives

$$
 r\le N+\frac n{d+2+2x}.
\tag{14.5}
$$

Let $h^0$ be obtained from this same $h$ by setting only its $AB$
coordinates to zero, and let $D=L(h)-L(h^0)$. Since each incidence
vector has squared norm $2$ and lies in $\mathbf1^\perp$,

$$
 0\preceq D\preceq2xP,\qquad
 L(h^0)\succeq(1-2x)P.
\tag{14.6}
$$

If $x<1/2$, this original bipartite assignment has connected support
and actual $\lambda_2(h^0)\ge1-2x$. The whole bipartite bound,
extended to connected nonnegative assignments as in Theorem 12.2,
gives $\lambda_2(h^0)R(h^0)\le B$.
For $0<x<1/2$, adding the nonzero $D$ strictly decreases the trace
of the inverse on $\mathbf1^\perp$, hence

$$
 r<R(h^0)\le\frac B{1-2x}.
\tag{14.7}
$$

Here strictness can be seen directly: for positive definite
$A=L(h^0)|_{\mathbf1^\perp}$, the difference
$A^{-1}-(A+D)^{-1}$ is the congruence by $A^{-1/2}$ of
$I-(I+A^{-1/2}DA^{-1/2})^{-1}$. It is positive semidefinite and
nonzero when $D\ne0$, so has strictly positive trace.
This also proves the required strict total-resistance comparison on
the original vertices. The non-strict monotonicity is the classical
one in Ghosh–Boyd–Saberi, §2.6.

If $r\le B$, then $r<U_{\rm ext}$ already. Suppose $r>B$.
The case $x=0$ is excluded by the whole bipartite bound.
For $0<x<1/2$, (14.7) implies
$x>(1-B/r)/2$; for $x\ge1/2$ the same strict inequality holds because
$0<(1-B/r)/2<1/2$. Thus (14.5) yields

$$
 r<N+\frac n{d+3-B/r}.
$$

The denominator is positive since $r>B>0$. Multiplying by $qr-B>0$
gives $p(r)<0$. A quadratic with positive leading coefficient is
negative only between its two roots, so $r<U_{\rm ext}$.
This proves the pointwise strict assertion on the entire
$\mathcal C$, without a symmetry, trace or rank restriction.

For strictness of the supremum, take any positive maximizing sequence
and normalize each term by its own $\lambda_2$. Theorem 11.2 gives a
convergent subsequence with limit $k\in K$ and
$R(k)=\lim_jF(g_j)=M$. The pointwise strict result applied to this
actual connected limit gives $M=R(k)<U_{\rm ext}$.
This limiting argument, rather than pointwise strictness alone,
justifies the strict-supremum claim. The lower comparison is
Theorem 11.1. ∎

## 15. Every exact resistance level and the remaining optimizer coordinates

**Theorem 15.1 (Closed level optimizers and all positive level sequences).**
For every exterior triple and every real $R_0>0$, let

$$
\overline{\mathcal F}_{R_0}
 =\{g\in[0,\infty)^E:\text{the positive support is connected},
                         R(g)=R_0\},\qquad
 K_{R_0}=\frac M{R_0}K.
\tag{15.1}
$$

The scaling maps (5.1) extend to mutually inverse continuous maps
between $\mathcal C$ and $\overline{\mathcal F}_{R_0}$.
The entire closed level optimizer set is the nonempty compact set
$K_{R_0}$, and

$$
 \max_{g\in\overline{\mathcal F}_{R_0}}\lambda_2(g)
 =\sup_{g\in\mathcal F_{a,b,c,R_0}}\lambda_2(g)
 =\frac M{R_0},\qquad
 \frac{B_{\rm bip}}{R_0}\le\frac M{R_0}
 <\frac{U_{\rm ext}}{R_0}
 <\frac n{R_0}\left(n-2+\frac1{d+2}\right).
\tag{15.2}
$$

For every $\alpha>B_\infty$, the closed level superlevel

$$
 \{g\in\overline{\mathcal F}_{R_0}:\lambda_2(g)\ge\alpha/R_0\}
\tag{15.3}
$$

is compact. For every sequence $(g_j)$ in the closed level with
$\max_e(g_j)_e\to\infty$,

$$
 \limsup_j\lambda_2(g_j)\le B_\infty/R_0.
\tag{15.3a}
$$

If any fixed $AB$ coordinate tends to infinity, this improves to
$\limsup_j\lambda_2(g_j)\le(n(n-3)+m)/R_0$.
For every sequence $(g_j)$ of strictly positive assignments
with $R(g_j)=R_0$ exactly,

$$
 \lambda_2(g_j)\longrightarrow M/R_0
 \quad\Longleftrightarrow\quad
 \operatorname{dist}(g_j,K_{R_0})\longrightarrow0.
\tag{15.4}
$$

Every point of $K_{R_0}$ is the limit of strictly positive assignments
of resistance exactly $R_0$ whose Fiedler values tend to $M/R_0$.
Their terms are maximizing approximants; no assertion that an individual
positive term attains the supremum is included.
The three whole-face level maxima are respectively
$X/R_0,Y/R_0,Z/R_0$, with every comparison and tie in Theorem 12.3
unchanged. The normalized rank-one suppliers in Theorem 13.1 give
exact-level assignments with $\operatorname{rank}(L(g)-\lambda_2(g)P)=1$
by multiplication by $T_n/R_0$; these exhaust such assignments at that
level.

*Proof.* The scaling proof of Theorem 5.1 uses only connectedness,
positivity of $\lambda_2$, and (1.6), so it applies verbatim to
nonnegative connected assignments. In explicit terms,

$$
 \Psi_{R_0}(h)=\frac{R(h)}{R_0}h,\qquad
 \Theta(g)=\frac g{\lambda_2(g)},\qquad
 \lambda_2(\Psi_{R_0}(h))=\frac{R(h)}{R_0}.
\tag{15.5}
$$

Continuity holds throughout the two domains. The closed level set
in (15.1) is also closed in $\mathbb R^E$: at any connected level
point the spectral identity gives
$R_0\ge n/\lambda_2(g)$, so $\lambda_2(g)\ge n/R_0$.
A convergent sequence in that level therefore has a nonnegative limit
with positive $\lambda_2$, hence connected support and, by continuity,
resistance $R_0$. No disconnected assignment is added by taking limits.

Theorem 11.1 and (15.5) identify all closed level maximizers as
$\Psi_{R_0}(K)=(M/R_0)K$. This set is nonempty and compact.
The positive level supremum and the bounds are Theorem 5.1 and
Theorems 11.1, 14.1. Equation (15.5) identifies (15.3) exactly with
$\Psi_{R_0}(\mathcal S_\alpha)$, a continuous image of the compact
set in Theorem 11.1, proving its compactness.
The bounds $n/R_0\le\lambda_2(g)\le M/R_0$ on this closed level
show that $\max_e(g_j)_e\to\infty$ implies
$\max_e(\Theta(g_j))_e\to\infty$. A fixed diverging $AB$
coordinate has the same property after this normalization. Applying
Theorem 10.2 to $\Theta(g_j)$ and using
$R(\Theta(g_j))=R_0\lambda_2(g_j)$ proves (15.3a) and its
stronger $AB$ version.

If a positive exact-level sequence is maximizing, then
$F(g_j)=R_0\lambda_2(g_j)\to M$.
By Theorem 11.2 its normalizations $h_j=\Theta(g_j)$ are bounded
and have distance to $K$ tending to zero. Choose nearest $k_j\in K$.
Since $\lambda_2(g_j)\to M/R_0$, boundedness of $h_j,k_j$ gives

$$
 \left\|g_j-\frac M{R_0}k_j\right\|_2
 \le \lambda_2(g_j)\|h_j-k_j\|_2
       +\left|\lambda_2(g_j)-\frac M{R_0}\right|\|k_j\|_2
 \longrightarrow0.
$$

This proves necessity in (15.4). Conversely, if the distances in
(15.4) tend to zero, choose nearest points in the compact $K_{R_0}$.
Any subsequence on which the Fiedler values fail to tend to $M/R_0$
has a further subsequence converging in original coordinates to a
point of $K_{R_0}$. Eigenvalue continuity contradicts that failure.
This proves sufficiency for every positive exact-level sequence.

For an arbitrary $k\in K$, take

$$
 h^{(\epsilon)}=
 \frac{k+\epsilon\mathbf1_E}{\lambda_2(k+\epsilon\mathbf1_E)},\qquad
 G^{(\epsilon)}=
 \frac{R(h^{(\epsilon)})}{R_0}h^{(\epsilon)}.
\tag{15.6}
$$

Every original coordinate of $G^{(\epsilon)}$ is finite and strictly
positive, and its resistance is exactly $R_0$ by (1.6).
Moreover $h^{(\epsilon)}\to k$ and
$R(h^{(\epsilon)})\to M$, so
$G^{(\epsilon)}\to(M/R_0)k$ and
$\lambda_2(G^{(\epsilon)})\to M/R_0$.
This proves positive exact-level approximation of every closed
optimizer. Applying the same scaling to the whole face suppliers
and to the exhaustive rank-one classification gives the final claims.

In particular positive attainment is equivalent to
$K\cap(0,\infty)^E\ne\varnothing$, or equivalently
$K_{R_0}\cap(0,\infty)^E\ne\varnothing$. The results above determine
neither that intersection nor the exact value of $M$ nor the explicit
coordinates of all members of $K$. Thus the full exterior optimization
in Definitions 6.2 and 9.4 is not solved by these bounds, face comparisons
or the rank-one classification. Unbounded normalization is excluded
for every maximizing sequence by Theorems 10.2–11.2; the remaining
sequence description is the implicit distance to the entire compact
optimizer set, whose coordinates are still undetermined. ∎

## 追加锚（本行以下为增补区）
