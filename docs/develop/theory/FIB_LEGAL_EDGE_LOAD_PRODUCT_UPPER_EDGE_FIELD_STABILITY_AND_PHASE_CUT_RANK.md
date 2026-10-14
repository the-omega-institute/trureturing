# FIB legal-edge load: product upper-edge certificates, field stability and joint-phase cut spectra

## 1. A common legal law, generator and tensor order

**Definition 1.1 (Positive hard-core law).** Let $G=(V,E)$ be a finite
simple graph with nonempty vertex set, and let $\Omega_G$ be all its
independent sets. Fix finite activities $\lambda_i>0$ and site weights
$w_i>0$. Set

$$
p(S)=\frac{\prod_{i\in S}\lambda_i}{Z_G(\lambda)},\qquad
Z_G(\lambda)=\sum_{S\in\Omega_G}\prod_{i\in S}\lambda_i,\qquad
W=\sum_iw_i.
\tag{1.1}
$$

Every legal configuration has positive probability. Write $s_i$ for
its occupation indicator and $N(i)$ for its open graph neighborhood.
Define

$$
q_i=\frac{\lambda_i}{1+\lambda_i},\qquad
a_i=w_iq_i,\qquad d_i=w_i(1-q_i).
\tag{1.2}
$$

**Definition 1.2 (The same weighted heat-bath parent).** On
$L^2(p)$ let $E_i$ be conditional expectation over coordinate $i$
given every other coordinate, and put

$$
H_{\rm cl}=\sum_iw_i(I-E_i).
\tag{1.3}
$$

It deletes an occupied site at rate $d_i$ and inserts an unoccupied
site at rate $a_i$ exactly when all its neighbors are empty. Let
$D=\operatorname{diag}(\sqrt p)$ and $H=DH_{\rm cl}D^{-1}$.
The normalized coherent representative and its parent are

$$
|\psi_+\rangle=\sum_{S\in\Omega_G}\sqrt{p(S)}|S\rangle,
\qquad H|\psi_+\rangle=0.
\tag{1.4}
$$

The vectors $|S\rangle$ are physical occupation tensor basis vectors;
illegal basis entries have zero amplitude. The Hilbert space on
which $H$ is considered is the legal subspace. Let $\gamma$ be its
smallest positive eigenvalue and $\Lambda$ its largest eigenvalue.
Deletion to the vacuum connects the configuration graph, so the
zero eigenvalue is simple. These definitions retain one probability
law and one clock. A physical preparation, dimensional energy scale
and implementation of the operators are additional assumptions.

**Convention 1.3 (Path specialization and prior interfaces).** For
the open path on $1,\ldots,n$, legality is $s_is_{i+1}=0$ and
$s_0=s_{n+1}=0$. In the normalized clock $W=1$, these are the
activities, local projectors and spectral edges of
[Phase/Joint, Chapters 1 and 9–15][PJ]. Its joint covariance pencils
and matching certificate are retained as prior results. For the
positive coherent path, [Boundary Calculus, §15.17][BC] supplies
the exact rank-two continuous-cut spectrum. Its §15.26–15.34
instead uses a sparse encoded graph-state carrier; that carrier
is not substituted for the full-support law (1.1).

The inhomogeneous coherent blockade state and frustration-free
annihilators are established ingredients of [Ji et al., equations
(2), (4), (5)][Ji]. The correspondence is $\lambda_i=\xi_i^2$
with the occupation-dependent sign removed by onsite phases.
The local normalization and positive reweighting in (1.3) preserve
the common kernel; they do not assert the physical parameter
matching of that source.

## 2. Product certificates and the induced-three-path obstruction

### 2.1. An attained positive-vector bound

**Definition 2.1 (Product row profile).** For $x_i>0$ define

$$
g_x(S)=\prod_{i\in S}x_i,
\qquad
R_x(S)=\sum_{i\in S}d_i(1+x_i^{-1})
+\sum_{\substack{i\notin S\\S\cap N(i)=\varnothing}}
a_i(1+x_i).
\tag{2.1}
$$

Set

$$
L_{\rm prod}=\inf_{x>0}\max_{S\in\Omega_G}R_x(S),
\qquad B_{\rm prod}=W-L_{\rm prod}.
\tag{2.2}
$$

**Theorem 2.2 (Attainment and upper-edge certificate).** Under
Definition 1.1,

$$
\Lambda\le L_{\rm prod},\qquad
B_{\rm prod}\le W-\Lambda,
\tag{2.3}
$$

and the infimum in (2.2) is attained at a strictly positive vector.

Proof. Let $Jf(S)=(-1)^{|S|}f(S)$. Every permitted transition changes
parity, so $A=JH_{\rm cl}J$ is entrywise nonnegative. Its positive
off-diagonal entries connect the legal configuration graph, hence
it is irreducible. It has the same spectrum as $H_{\rm cl}$, and
Perron–Frobenius supplies positive left and right eigenvectors for
$\Lambda$. Directly applying $A$ to the product gives

$$
\frac{(Ag_x)(S)}{g_x(S)}=R_x(S).
\tag{2.4}
$$

Indeed, a deletion contributes $d_i/x_i$, an insertion contributes
$a_ix_i$, and the diagonal supplies the remaining $d_i$ or $a_i$.
If $R_x(S)\le L$ everywhere, multiplication of $Ag_x\le Lg_x$
by a positive left Perron vector gives $\Lambda\le L$.
This is the classical positive-vector bound, used here as an
ingredient for the graph-dependent obstruction below.

Choose any finite sublevel $\max_SR_x(S)\le C$ that contains a
candidate. The vacuum and site singleton respectively imply

$$
a_i(1+x_i)\le C,\qquad d_i(1+x_i^{-1})\le C.
\tag{2.5}
$$

Since every $a_i,d_i$ is positive, each coordinate is bounded
above and bounded away from zero on this sublevel. Its closure
is therefore a compact subset of the positive orthant. The
maximum of the finitely many continuous row ratios is continuous.
A minimizing sequence in one such sublevel has a positive
limit that attains the infimum. $\square$

### 2.2. A single profile dominates all matching certificates

**Theorem 2.3 (Matching domination).** For any matching
$\mathcal M$ of $G$, define

$$
b_{ij}=\frac{w_i+w_j-\sqrt{(w_i-w_j)^2+
4w_iw_jq_iq_j}}2.
\tag{2.6}
$$

Then

$$
0\le\sum_{ij\in\mathcal M}b_{ij}
\le B_{\rm prod}\le W-\Lambda.
\tag{2.7}
$$

Proof. Retain only the edges of $\mathcal M$, with all unmatched
sites isolated. For one matching edge the legal configuration
space consists of its vacuum and two singletons. Its parent has
eigenvalues zero and

$$
\frac{w_i+w_j\pm\sqrt{(w_i-w_j)^2+
4w_iw_jq_iq_j}}2.
\tag{2.8}
$$

For example, its trace is $w_i+w_j$, and the sum of its principal
two-by-two minors is $w_iw_j(1-q_iq_j)$, which yields (2.8).
The smaller positive eigenvalue is $b_{ij}>0$. Every positive
Perron vector on its three configurations has product form after
normalizing the vacuum coordinate to one. An isolated site's
Perron vector also has this form, and its top eigenvalue is $w_i$.

Take the tensor product of these actual component Perron vectors.
It is one product profile $g_x$ for the entire relaxed graph, with
constant row ratio

$$
W-\sum_{ij\in\mathcal M}b_{ij}.
\tag{2.9}
$$

Every configuration legal for $G$ is legal for this relaxed graph.
Restoring the omitted exclusion edges leaves every occupied-site
term in (2.1) unchanged and only removes positive insertion terms.
Thus the same vector, restricted to $\Omega_G$, has maximum row
ratio at most (2.9). Infimizing and using (2.3) proves (2.7).
The empty matching gives the first inequality as well. $\square$

The construction uses a common vector on a common configuration
space. It does not combine separately attained extrema without
a simultaneous realization.

### 2.3. Exact sharpness is characterized by exclusion geometry

**Theorem 2.4 (Product sharpness exactly on cluster graphs).**
For every strictly positive activity and weight vector,

$$
L_{\rm prod}=\Lambda
\quad\Longleftrightarrow\quad
G\text{ is a disjoint union of cliques}.
\tag{2.10}
$$

If $G$ has an induced path of three vertices, the inequality is
strict for every such parameter vector.

Proof. For distinct nonadjacent vertices $i,j$, the four sets
$\varnothing,\{i\},\{j\},\{i,j\}$ are actual legal
configurations. Put $A_v=a_v(1+x_v)$. Inclusion-exclusion in
the insertion contributions of (2.1) gives

$$
R_x(\{i,j\})-R_x(\{i\})-R_x(\{j\})+R_x(\varnothing)
=\sum_{v\in N(i)\cap N(j)}A_v.
\tag{2.11}
$$

The deletion terms cancel. The closed neighborhoods intersect
only in common neighbors, since $i,j$ are nonadjacent. If they
have a common neighbor, the right side is positive. Hence the
row ratios of every product vector are nonconstant.

Suppose nevertheless that $L_{\rm prod}=\Lambda$. By Theorem
2.2 choose an attaining vector with $Ag_x\le\Lambda g_x$.
Multiplying by a positive left Perron vector makes the total
defect zero. Every coordinate defect is nonnegative, so all
must vanish. The row ratios would then be constant, contrary
to (2.11). Thus an induced three-vertex path forces strictness.

A graph without an induced three-vertex path has every connected
component complete: if a component had two nonadjacent vertices,
the first three vertices on a shortest path between them would
induce such a path. Conversely a disjoint union of cliques has
no such path. On each clique the only independent configurations
are the vacuum and singletons. Any positive Perron vector is
therefore product-representable. Tensoring the actual clique
Perron vectors produces a product Perron vector for the whole
graph. Its constant ratio is $\Lambda$, proving equality.
$\square$

**Corollary 2.5 (Path strictness and cluster comparison).** Every
open path of length $n\ge3$ satisfies

$$
B_{\rm prod}<W-\Lambda.
\tag{2.12}
$$

For a disjoint union of cliques containing at least one edge,

$$
\gamma+\Lambda\le W.
\tag{2.13}
$$

Proof. A path of length at least three contains an induced
three-vertex path. For the second assertion, write $H_C$ for
the component parent of clique $C$. Its star-shaped legal
generator has trace

$$
\operatorname{tr}H_C=\sum_{i\in C}(a_i+d_i)=W_C.
\tag{2.14}
$$

All its nonzero eigenvalues are positive. Therefore
$W_C-\Lambda_C\ge0$. If $|C|\ge2$, it has at least two
positive eigenvalues and its smallest one satisfies
$\gamma_C\le W_C-\Lambda_C$. The tensor-sum spectrum gives
$\gamma=\min_C\gamma_C$ and $\Lambda=\sum_C\Lambda_C$.
Choose one nontrivial clique and sum the nonnegative component
deficits to obtain (2.13). $\square$

The edge hypothesis is necessary here. A graph consisting only
of isolated sites has $\Lambda=W$ and $\gamma=\min_iw_i>0$,
so it violates (2.13). Also, (2.12) is a strict failure of
product sharpness, not a refutation of the spectral comparison
on a connected path. In the quantum representation the relevant
positive vector is $Dg_x$, with parity applied to reach a top
eigenvector of $H$. The positive ground state (1.4) and this
top eigenvector are different objects.

### 2.4. Convex profiles and an exact three-state maximum

**Proposition 2.6 (Convex optimization and path row recurrence).**
With $y_i=\log x_i$, the function $\max_SR_x(S)$ is convex
and coercive in $y\in\mathbb R^V$. On a path its value for a
fixed $y$ is given by the following three-state recurrence.
Put

$$
A_i=a_i(1+e^{y_i}),\qquad D_i=d_i(1+e^{-y_i}),\qquad
T_i(a,b,c)=D_ib+A_i(1-a)(1-b)(1-c).
\tag{2.15}
$$

Use legal pair states $00,01,10$, and let $F_i(a,b)$ be the
maximum of $\sum_{r=1}^{i-1}T_r(s_{r-1},s_r,s_{r+1})$
over prefixes ending in $(s_{i-1},s_i)=(a,b)$, with $s_0=0$.
Impossible prefixes have value $-\infty$. Initialize
$F_1(0,0)=F_1(0,1)=0$, $F_1(1,0)=-\infty$. Then

$$
F_{i+1}(b,c)=\max_{\substack{a\in\{0,1\}\\ab=bc=0}}
\bigl(F_i(a,b)+T_i(a,b,c)\bigr),
\tag{2.16}
$$

and

$$
\max_SR_x(S)=\max_{\substack{a,b\in\{0,1\}\\ab=0}}
\bigl(F_n(a,b)+T_n(a,b,0)\bigr).
\tag{2.17}
$$

Proof. Each row ratio is a sum of positive exponential terms
and constants, so their finite maximum is convex. The sublevel
bounds (2.5), after taking logarithms, give coercivity.
For a legal path word, its occupied and insertible contributions
are exactly $\sum_iT_i(s_{i-1},s_i,s_{i+1})$. Appending a bit
settles precisely the previous position's triple contribution.
This proves (2.16) by induction, and the fixed terminal zero
settles the last contribution in (2.17). There are five legal
triples at each internal step. This bounds the number of real
arithmetic transitions for evaluating a fixed profile; it does
not bound the precision or iterations needed to minimize it.
$\square$

## 3. Explicit posterior stability for arbitrary positive path activities

### 3.1. A profile for every positive pinning

**Definition 3.1 (Decreasing field and propagation profile).**
For $\theta\in(0,1]$, multiply every activity by $\theta$.
A positive pinning conditions on $\tau\subseteq S$ for a
legal $\tau$. Write $p_\theta^\tau$ for the resulting law on
the unpinned coordinates, omitting forced-zero coordinates.
Set

$$
q_i(\theta)=\frac{\theta\lambda_i}{1+\theta\lambda_i},
\qquad M=\max_i\lambda_i,
\tag{3.1}
$$

$$
F_\lambda(\theta)=\max_i\left[
\sum_{j<i}\prod_{h=j}^{i-1}q_h(\theta)
+\sum_{j>i}\prod_{h=i+1}^{j}q_h(\theta)\right].
\tag{3.2}
$$

The profile has the continuous extension $F_\lambda(0)=0$.

**Theorem 3.2 (Mean-normalized pinning stability).** Every law
in Definition 3.1 satisfies

$$
\operatorname{Cov}_{p_\theta^\tau}(s)
\preceq [1+F_\lambda(\theta)]
\operatorname{Diag}(\mathbb E_{p_\theta^\tau}s),
\qquad F_\lambda(\theta)\le2\theta M.
\tag{3.3}
$$

For $C(t)=1+F_\lambda(1-t)$, $0\le t<1$, the rate is
nonincreasing, at least one, and has finite integral

$$
I_\lambda=\int_0^1\frac{C(t)-1}{1-t}\,dt
=\int_0^1\frac{F_\lambda(\theta)}\theta\,d\theta
\le2M.
\tag{3.4}
$$

Proof. A positive pinning deletes its occupied sites and their
neighbors. The remaining sites form disjoint path intervals,
independent under the same conditional law, with activities
$\theta\lambda_i$. Thus it suffices to treat one interval.
Let $Z_h$ be its suffix partition function starting at $h$.
At its terminal end set both empty suffix partition functions
to one. Then

$$
Z_h=Z_{h+1}+\theta\lambda_hZ_{h+2},\qquad
u_h=\frac{\theta\lambda_hZ_{h+2}}{Z_h}
\le q_h(\theta).
\tag{3.5}
$$

The last inequality uses $Z_{h+1}\ge Z_{h+2}>0$.
Given its preceding bit, the probability that site $h$ is
occupied is $u_h(1-s_{h-1})$. The coefficient of $s_i$ in
$\mathbb E(s_j\mid s_i)$ is consequently
$(-1)^{j-i}\prod_{h=i+1}^ju_h$. Hence, for $i<j$,

$$
\operatorname{Cov}(s_i,s_j)
=(-1)^{j-i}\operatorname{Var}(s_i)
\prod_{h=i+1}^ju_h.
\tag{3.6}
$$

Reversing the interval gives the corresponding formula to the
left. Put $m_i=\mathbb E s_i>0$ on retained coordinates and
$D_m=\operatorname{Diag}(m)$. The diagonal entry of
$D_m^{-1}\operatorname{Cov}(s)$ is $1-m_i\le1$.
The absolute off-diagonal row sums, using (3.5)–(3.6), are
bounded by (3.2): truncated interval sums are no larger than
the full path sums. Thus the absolute row sums of this matrix
are at most $1+F_\lambda(\theta)$.

The matrix is similar to the symmetric positive semidefinite
$D_m^{-1/2}\operatorname{Cov}(s)D_m^{-1/2}$. Its largest
eigenvalue is bounded by the absolute row norm, proving the
first part of (3.3). Independent residual intervals add blocks;
an empty residual space imposes no condition.

Every factor $q_h(\theta)$ is at most
$r=\theta M/(1+\theta M)<1$. Each directional sum is at most
$\sum_{\ell\ge1}r^\ell=\theta M$. This proves the second
part of (3.3). The factors are nondecreasing in $\theta$,
so $C(t)$ is nonincreasing. Integrating gives (3.4). $\square$

The normalization in (3.3) uses the means $m_i$, not the
variances $m_i(1-m_i)$. All positive pinnings are included;
no claim depends on conditioning a zero-probability event at
$\theta=0$.

### 3.2. Polynomial approximation in the actual deletion clock

**Corollary 3.3 (Parameter-dependent degree coercivity).** Let
$\Pi_d$ be orthogonal projection in the original $L^2(p)$
onto restrictions of multilinear polynomials of degree at most
$d$. Write

$$
d_* = \min_i\frac{w_i}{1+\lambda_i}.
\tag{3.7}
$$

For every real $f$ and integer $0\le d<\lceil n/2\rceil$,

$$
\langle f,H_{\rm cl}f\rangle_p
\ge d_*(d+1)e^{-I_\lambda}\|f-\Pi_df\|_p^2,
\qquad \gamma\ge d_*e^{-I_\lambda}.
\tag{3.8}
$$

Proof. The maximal cardinality of a legal path configuration is
$r=\lceil n/2\rceil$. Apply the published auxiliary estimate
of [Miao–Yin, §3.2, equation (11)][MY] to (3.3)–(3.4).
It uses the mean-normalized covariance condition for every
positive pinning and only spectral stability and integrability
to obtain

$$
\mathcal E_1(f,f)\ge(d+1)e^{-I_\lambda}\|f-\Pi_df\|_p^2,
\qquad
\mathcal E_1(f,f)=\sum_Sp(S)\sum_{i\in S}
\bigl(f(S)-f(S\setminus\{i\})\bigr)^2.
\tag{3.9}
$$

The actual form instead weights each deletion by $d_i$.
It is therefore at least $d_*\mathcal E_1(f,f)$.
This proves (3.8), with $d=0$ giving the gap bound.
The unit-deletion estimate is an attributed intermediate
ingredient; the path profile and clock comparison specify
its application here. $\square$

The source's later occupied-marginal lower bound is used for
its polynomial norm and logarithmic-Sobolev estimates, not
for the auxiliary equation (11). The insertion-ratio comparison
in its equation (10) is also unnecessary once the actual
minimum deletion rate is used in (3.8). The constants depend
on the supplied activities and weights. No uniform constant
over unrestricted positive vectors follows from $I_\lambda\le2M$,
and a lower bound on $\gamma$ does not prove
$\gamma\le W-\Lambda$.

## 4. Full-support joint phase and the exact two-three-four cut classification

### 4.1. Classical probabilities and actual sector matrices

**Definition 4.1 (One joint phase).** On the path, for distinct
sites $i,j$ and $z\in\mathbb C$ with $|z|=1$, let

$$
U_z|S\rangle=z^{s_is_j}|S\rangle,\qquad
|\psi_z\rangle=U_z|\psi_+\rangle.
\tag{4.1}
$$

Every complete occupation probability remains exactly $p(S)$.
In particular all classical events, marginals and joint
occupation moments agree for every $z$. This statement concerns
the diagonal occupation algebra, not full quantum reduced states.

**Definition 4.2 (The cut sectors).** Fix $1\le k<n$ and a
cross-cut pair $i\le k<j$. For an internally legal left word
$\ell$ put $(x,u)=(\ell_k,\ell_i)$; for an internally legal
right word $r$ put $(y,v)=(r_{k+1},r_j)$. The actual sector
masses are

$$
L_{xu}=\sum_{\substack{\ell\text{ internally legal}\\
(\ell_k,\ell_i)=(x,u)}}\prod_{h\le k}\lambda_h^{\ell_h},
\qquad
R_{yv}=\sum_{\substack{r\text{ internally legal}\\
(r_{k+1},r_j)=(y,v)}}\prod_{h>k}\lambda_h^{r_h}.
\tag{4.2}
$$

Retain only sectors realized by legal words, so all retained
masses are positive. The full coefficient matrix has entries

$$
A_z(\ell,r)=\frac{\sqrt{\prod_{h\le k}\lambda_h^{\ell_h}
\prod_{h>k}\lambda_h^{r_h}}}{\sqrt{Z_G(\lambda)}}
(1-xy)z^{uv}.
\tag{4.3}
$$

**Theorem 4.3 (Exact spectrum on at most four coordinate sectors).**
The nonzero singular values of $A_z$ are exactly those of

$$
B_z[(x,u),(y,v)]
=\frac{\sqrt{L_{xu}R_{yv}}}{\sqrt{Z_G(\lambda)}}
(1-xy)z^{uv}.
\tag{4.4}
$$

Thus the full squared Schmidt spectrum is the nonzero spectrum
of $B_zB_z^\ast$.

Proof. In each retained left sector, normalize the vector of
positive square-root activity amplitudes by $\sqrt{L_{xu}}$.
Different sectors have disjoint tensor basis support and are
orthonormal. Do the same on the right. Grouping every entry
of (4.3) in these two orthonormal families gives (4.4).
The two grouping maps are local isometries, so they preserve
nonzero singular values. No legal string is removed. This is
the positive block-factorization ingredient of Boundary Calculus
§15.17 applied to the additional two selected coordinates.
$\square$

The representation is a correlator-product state in the
established sense of [Changlani et al., equation (2)][CPS]:
onsite factors $\lambda_h^{s_h/2}$, adjacent blockade factors
$1-s_hs_{h+1}$, and one factor $z^{s_is_j}$. That general
representation framework does not supply the following
blockade-dependent branch calculation.

### 4.2. Exact rank from legal vacuum and singleton witnesses

**Theorem 4.4 (Full-support joint-phase cut rank).** Under
Definitions 4.1–4.2, for $z\ne1$,

$$
\operatorname{rank}A_z
=2+\mathbf1_{\{i<k,\ j>k+1\}}
+\mathbf1_{\{i\le k-2,\ j\ge k+3\}}.
\tag{4.5}
$$

For $z=1$ the rank is two. A gate whose two sites are on the
same side preserves the entire cut Schmidt spectrum. If
$(i,j)=(k,k+1)$, it is the identity on the legal space.

Proof. Remove the nonzero row and column amplitude factors
in (4.3). Its core is

$$
M_z=(1-xy)[1+(z-1)uv]
=1-xy+(z-1)uv-(z-1)uxvy.
\tag{4.6}
$$

The number of actual $(x,u)$ patterns is respectively two,
three or four according as $i=k$, $i=k-1$ or $i\le k-2$.
For coincident coordinates they are $00,11$; for adjacent
coordinates they are $00,10,01$; otherwise all four occur
by taking the vacuum, the two singletons and their legal pair.
The same count holds for $(y,v)$ with $j=k+1,k+2$ or
$j\ge k+3$. Equal patterns give equal rows or columns in
the core, bounding rank by the smaller pattern count.

For every placement, left and right vacuum and cut-boundary
singletons give the actual two-by-two minor

$$
C=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad\det C=-1.
\tag{4.7}
$$

If both selected sites differ from the cut-boundary sites,
take left vacuum/selected singleton/boundary singleton and
right vacuum/boundary singleton/selected singleton. Their
minor is

$$
\begin{pmatrix}1&1&1\\1&1&z\\1&0&1\end{pmatrix},
\qquad\det=z-1\ne0.
\tag{4.8}
$$

It proves rank at least three even when either selected site
is adjacent to its own cut boundary. When both selected sites
are at least two positions from those boundaries, all four
patterns occur on each side. Order them lexicographically as
$(x,u)$ and $(y,v)$. Their four-by-four minor is

$$
C\otimes\begin{pmatrix}1&1\\1&z\end{pmatrix},
\qquad \det=(z-1)^2\ne0.
\tag{4.9}
$$

These are genuine legal strings with all other bits zero;
no independent pattern realization is invented. The minors
attain each upper bound and prove (4.5). If $z=1$, (4.6)
has rank at most two, while (4.7) still supplies the lower bound.
A same-side gate acts as a local unitary for this bipartition.
Finally the cross-boundary adjacent occupation is forbidden,
so its phase exponent is identically zero. $\square$

**Corollary 4.5 (A four-site weighted rank-three witness).** For
$n=4,k=2,i=1,j=4$, the left orders $00,10,01$ and right
orders $00,10,01$ give

$$
A_z=\frac1{\sqrt Z}
\begin{pmatrix}
1&\sqrt{\lambda_3}&\sqrt{\lambda_4}\\
\sqrt{\lambda_1}&\sqrt{\lambda_1\lambda_3}
&z\sqrt{\lambda_1\lambda_4}\\
\sqrt{\lambda_2}&0&\sqrt{\lambda_2\lambda_4}
\end{pmatrix},
\qquad
\det A_z=(z-1)\frac{\sqrt{\lambda_1\lambda_2\lambda_3\lambda_4}}
{Z^{3/2}}.
\tag{4.10}
$$

In particular its rank is three for every nontrivial unit phase
and every strictly positive activity vector.

Proof. The three-by-three matrix lists every internally legal
word on each side. Expanding its determinant gives (4.10),
whose activity prefactor is positive. $\square$

## 5. Entropy changes require the positive-reference comparison

### 5.1. Strict majorization even when rank remains two

**Theorem 5.1 (Strict entropy increase for a legal cross-cut phase).**
For the full-support positive path state, the von Neumann cut
entropy satisfies

$$
S(\psi_z)>S(\psi_+)
\quad\Longleftrightarrow\quad
z\ne1,\quad i\le k<j,\quad j-i\ge2,
\tag{5.1}
$$

where sites are ordered $i<j$. In the nontrivial case the
eigenvalue probability vector of the reduced state of $\psi_z$
is strictly majorized by that of $\psi_+$, after padding with
zeros.

Proof. Let $\rho_z=A_zA_z^\ast$, and put $\rho_+=A_+A_+^\ast$.
Since $A_+=|A_z|$ entrywise,

$$
|\rho_z|\le\rho_+
\tag{5.2}
$$

entrywise. Every entry of $\rho_+$ on the internally legal
left words is strictly positive: the right vacuum alone gives
a positive summand. For the left vacuum and the left
$i$-singleton, the right vacuum has phase one and the right
$j$-singleton has phase $\bar z$ in their reduced-matrix
entry. Both are legal for this pair of left words exactly
when the selected cross pair is nonadjacent. Grouping the
other right words according to $s_j$ therefore gives an
entry $a+b\bar z$ with $a,b>0$. For $z\ne1$,

$$
|a+b\bar z|<a+b.
\tag{5.3}
$$

Thus (5.2) is strict in at least one entry. The standard
Perron comparison for a positive matrix, together with the
spectral-radius bound for entrywise absolute values, yields

$$
\lambda_{\max}(\rho_z)
\le r(|\rho_z|)<r(\rho_+)=\lambda_{\max}(\rho_+).
\tag{5.4}
$$

For completeness, the strict comparison uses the positive
Perron vector $v$ of $\rho_+$. The defect
$\rho_+v-|\rho_z|v$ is nonnegative and nonzero. Positivity
of $\rho_+$ spreads this defect to every coordinate in the
comparison of squared matrices, giving
$|\rho_z|^2v<r(\rho_+)^2v$. The positive-vector bound then
gives $r(|\rho_z|)<r(\rho_+)$. The first inequality in
(5.4) follows by taking absolute values in a complex
eigenvector equation, or by the induced power norm bound.

The reference reduced state has exactly two positive
eigenvalues $\alpha,1-\alpha$ with $\alpha\ge1/2$.
By (5.4), the largest eigenvalue of $\rho_z$ is smaller
than $\alpha$. Both spectra are nonnegative and sum to one.
The first sorted partial sum is consequently smaller; every
partial sum from the second onward is at most one, the
corresponding reference sum. This proves strict majorization.
Strict Schur concavity of von Neumann entropy proves (5.1)
in the nontrivial case. A same-side gate preserves spectrum,
and an adjacent cross pair is the identity. These establish
the remaining cases. $\square$

The comparison uses positivity of the reference, its rank two
and actual cross-side interference. Rank increase by itself
is not the reason for the entropy conclusion.

### 5.2. Quantitative limits and a rank-preserving example

**Proposition 5.2 (Three-site rank two with changing spectrum).**
Take $n=3,k=1,i=1,j=3$ and $\lambda_h=1$ for all sites.
Writing $z=e^{i\theta}$, the coefficient matrix and squared
Schmidt spectrum are

$$
A_z=\frac1{\sqrt5}
\begin{pmatrix}1&1&1\\1&0&z\end{pmatrix},
\qquad
\left(\frac{5+\sqrt{9+8\cos\theta}}{10},
\frac{5-\sqrt{9+8\cos\theta}}{10}\right).
\tag{5.5}
$$

Its rank is always two. At $z=1$ the spectrum is
$(5+\sqrt{17},5-\sqrt{17})/10$; at $z=-1$ it is
$(3/5,2/5)$ and has strictly greater entropy.

Proof. In the right basis $00,10,01$, the five legal words
give the displayed matrix. Its reduced state is

$$
\rho_z=\frac15\begin{pmatrix}3&1+\bar z\\1+z&2\end{pmatrix}.
\tag{5.6}
$$

The trace is one and the determinant is
$(4-2\cos\theta)/25$. Solving the characteristic quadratic
gives (5.5). The two eigenvalues are positive for every unit
phase, and Theorem 5.1 gives the strict entropy comparison.
$\square$

**Proposition 5.3 (Rank has no uniform positive entropy bound here).**
Fix any placement of rank three or four in Theorem 4.4 and
any $z\ne1$. Setting all activities to $\varepsilon>0$ keeps
that exact rank for every $\varepsilon$, while its entropy
tends to zero as $\varepsilon\downarrow0$. At fixed positive
activities, letting $z\to1$ keeps the same elevated rank
until $z=1$, while the entropy tends to the reference entropy.

Proof. In the first limit the coherent states tend in norm to
the vacuum, because every nonvacuum activity monomial vanishes
and the partition function tends to one. The reduced state
then tends to a pure vacuum projector. In the second limit
the finite-dimensional coefficient matrix tends entrywise to
$A_+$. Entropy is continuous on the finite-dimensional
probability spectrum, whereas the exact nonzero minors in
(4.8)–(4.9) persist for every nontrivial phase and positive
activity. $\square$

Strict positivity is essential to these rank statements. For
example, allowing $\lambda_2=0$ on a two-site path removes
one occupied sector and leaves a product coherent state.
That excluded boundary does not have the baseline rank two.

## 6. Finite-angle energy and the distinction between fixed and moved parents

**Theorem 6.1 (Exact fixed-parent joint-phase energy).** On the
same law and parent of Definitions 1.1–1.2, put
$\mu_{ij}=\mathbb E_p(s_is_j)$. Then

$$
\langle\psi_z,H\psi_z\rangle
=|z-1|^2\mu_{ij}
\left(\frac{w_i}{1+\lambda_i}+
\frac{w_j}{1+\lambda_j}\right).
\tag{6.1}
$$

For an adjacent pair it vanishes. For a nonadjacent pair
it is positive exactly when $z\ne1$.

Proof. For any complex function $f$ on legal configurations,
write $\Psi_f=\sum_S\sqrt{p(S)}f(S)|S\rangle$.
Detailed balance and the ground-state transform give the
occupied-endpoint form

$$
\langle\Psi_f,H\Psi_f\rangle
=\sum_Sp(S)\sum_{h\in S}\frac{w_h}{1+\lambda_h}
\left|f(S)-f(S\setminus\{h\})\right|^2.
\tag{6.2}
$$

Each undirected edge is counted once, so no extra factor
one half occurs. The unit-deletion occupied-endpoint and
joint-monomial computations are established ingredients of
[Miao–Yin, §3.2, equations (13), (21), (22)][MY]; (6.2)
uses the actual coordinate deletion rates.

For $f(S)=z^{s_is_j}=1+(z-1)s_is_j$, only deletion of
$i$ or $j$ from a set containing both changes $f$.
The squared change is $|z-1|^2$. Summing those occupied
configurations gives (6.1). Equivalently, for the projector
$F=n_in_j$, use $U_z=I+(z-1)F$ and $H\psi_+=0$ to get
$|z-1|^2\langle F\psi_+,HF\psi_+\rangle$.
Adjacent joint occupation is forbidden; a nonadjacent legal
pair has positive mass. $\square$

This finite-angle formula is an application of the known
Dirichlet mechanism, not a new general energy principle.
Its relation to the full-support cut classification keeps
the preparation, law, control and parent fixed simultaneously.

**Proposition 6.2 (Energy and cut entanglement do not coincide).**
A nontrivial joint phase on two nonadjacent sites lying on
the same side of a cut has positive fixed-parent energy
but unchanged cut Schmidt spectrum. For any placement,
the conjugated parent

$$
H_z=U_zHU_z^\ast
\tag{6.3}
$$

has the same spectrum as $H$ and annihilates $\psi_z$.
In particular a legal cross-cut phase can have the strictly
larger entropy of Theorem 5.1 and zero energy relative to
$H_z$.

Proof. The first assertion combines (6.1) with cut-local
unitary invariance. For the second,
$H_z\psi_z=U_zH\psi_+=0$, and unitary conjugation
preserves the full spectrum. $\square$

The normalized energy in (6.1) has the clock units supplied
by $w$. It is not a spacetime energy density or a gravitational
source. Neither the exact rank nor the finite-angle energy
provides a physical phase-control protocol or a preparation
cost.

## 7. The remaining spectral joint condition

**Definition 7.1 (Product-certified comparison target).** For
the normalized positive path $W=1$, let $r_-(v,T)$ denote
the same-law vacancy/central-occupation pencil minimum of
[Phase/Joint, Theorem 15.2][PJ]. A sufficient relation for
the unrestricted two-edge comparison is

$$
\min_{v,\ \varnothing\ne T\subseteq N(v)}r_-(v,T)
\le B_{\rm prod}.
\tag{7.1}
$$

**Proposition 7.2 (What the sufficient target would imply).**
If (7.1) holds for a given positive path, then
$\gamma+\Lambda\le1$ for that same path.

Proof. The pencil variational principle gives
$\gamma\le\min r_-$, while Theorem 2.2 gives
$B_{\rm prod}\le1-\Lambda$. Compose these inequalities
under (7.1). $\square$

No all-parameter proof of (7.1) is supplied. The strictness
in (2.12), the coercivity in (3.8), and the quantum phase
classification concern different inequalities and cannot
replace this missing upper bound on a realizable gap probe.
Failure of (7.1) for this menu would not refute the original
spectral comparison: the product certificate can be nonsharp
and higher-degree phase probes remain available.

The graph-dependent product sharpness criterion, explicit
path posterior profile, and full-support phase/rank/entropy
relations are deductions for the defined models. Their
literature priority is not asserted. Positive-vector bounds,
Perron comparison, Markov propagation, Schmidt decomposition,
Schur concavity and correlator-product representations are
established intermediate methods. The cited monomial energy
and unit-deletion coercivity remain attributed to their
published owner.

[PJ]: https://github.com/the-omega-institute/trureturing/blob/c8daa37c66e7b2bf32c475bd2967ccbeac34f0e5/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_PHASE_PARENT_AND_JOINT_OCCUPATION_DESIGN.md
[BC]: AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md
[Ji]: https://arxiv.org/abs/1304.5182v1
[CPS]: https://arxiv.org/abs/0907.4646v2
[MY]: https://arxiv.org/abs/2609.21936v1

## 追加锚（本行以下为增补区）
