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

## 8. The complete phase fiber and its entropy minimizers

### 8.1. Actual vacuum rectangles determine cut-local phases

**Definition 8.1 (Full-support phase fiber).** Keep the path law,
tensor order and cut of §§1 and 4. Let $\chi:\Omega_G\to U(1)$
be arbitrary, and put

$$
|\psi_\chi\rangle=\sum_S\sqrt{p(S)}\chi(S)|S\rangle.
\tag{8.1}
$$

This entire fiber has the same complete occupation law. For an
internally legal left word $\ell$ and right word $r$ with legal
concatenation, define the canonical phase rectangle

$$
\mathfrak h_\chi(\ell,r)
=\frac{\chi(\ell,r)\chi(0,0)}{\chi(\ell,0)\chi(0,r)}.
\tag{8.2}
$$

All four entries are actual legal configurations and every
denominator is a nonzero unit phase. A cut-local phase has
the form $\chi(\ell,r)=a(\ell)b(r)$ on all legal
concatenations, with $|a|=|b|=1$.

**Theorem 8.2 (Exact minimum-entropy orbit in the phase fiber).**
The reference Schmidt probability vector majorizes the vector
of every $\psi_\chi$. Moreover, the following are equivalent:

$$
\begin{aligned}
S(\psi_\chi)&=S(\psi_+),\\
\mathfrak h_\chi(\ell,r)&=1
\quad\text{for every legal concatenation},\\
\chi(\ell,r)&=a(\ell)b(r)
\quad\text{for cut-local unit phases}.
\end{aligned}
\tag{8.3}
$$

If any canonical rectangle is nontrivial, the majorization
compares unequal spectra with a strictly smaller first
partial sum, and the entropy inequality is strict. This
does not mean every majorization partial sum is strict.

Proof. Write $A_\chi(\ell,r)=A_+(\ell,r)\chi(\ell,r)$
and $\rho_\chi=A_\chi A_\chi^\ast$. As in Theorem 5.1,
$|\rho_\chi|\le\rho_+$ entrywise, and every entry of
$\rho_+$ is positive because the right vacuum contributes.
Perron comparison bounds the largest eigenvalue of
$\rho_\chi$ by the largest reference eigenvalue. Since
$\rho_+$ has rank two and both matrices have trace one,
that single eigenvalue bound gives majorization.

Suppose some rectangle $(\ell,r)$ in (8.2) is nontrivial.
Consider the reduced entry between left rows $\ell$ and
the left vacuum. The right vacuum and $r$ both contribute
with positive amplitudes. Their phase ratios differ exactly
by $\mathfrak h_\chi(\ell,r)$. Hence the triangle
inequality in this entry is strict. The positive-reference
Perron comparison is then strict, as proved in (5.4).
The two spectra differ, and strict Schur concavity gives
$S(\psi_\chi)>S(\psi_+)$.

If instead every rectangle is one, set

$$
a(\ell)=\chi(\ell,0),\qquad
b(r)=\frac{\chi(0,r)}{\chi(0,0)}.
\tag{8.4}
$$

Equation (8.2) reconstructs $\chi(\ell,r)=a(\ell)b(r)$
on every legal concatenation. Thus $A_\chi$ differs from
$A_+$ by diagonal unitary matrices on its two sides and
has exactly the same singular values. A cut-local phase
also makes every rectangle one by cancellation. These
facts prove all equivalences. $\square$

This is a statement about the specified rank-two positive
reference. A bound on the largest eigenvalue alone would
not provide complete majorization for an arbitrary reference
of larger rank. Complete classical probabilities determine
the reference in (8.1), but do not determine its phase
rectangles or the orbit in (8.3).

### 8.2. Legal occupation phases give the complete hierarchy

**Definition 8.3 (Multiplicative occupation coefficients).** For
every legal marked set $I$, define

$$
\eta_\chi(I)=\prod_{T\subseteq I}
\chi(T)^{(-1)^{|I|-|T|}}.
\tag{8.5}
$$

Exponents are $1$ or $-1$ in $U(1)$. Every subset of $I$
is legal, so this expression stays on the original carrier.
It is the usual Boolean-interval Möbius inversion, used as
an intermediate coordinate system for the phase fiber.

**Theorem 8.4 (Cross-cut occupation coefficients classify entropy equality).**
For every legal configuration $S$,

$$
\chi(S)=\prod_{I\subseteq S}\eta_\chi(I),
\qquad
\mathfrak h_\chi(\ell,r)
=\prod_{\substack{I\subseteq\ell\cup r\\
I\cap[1,k]\ne\varnothing\\I\cap[k+1,n]\ne\varnothing}}
\eta_\chi(I).
\tag{8.6}
$$

Consequently entropy equals the reference value if and only
if every legal marked set meeting both sides has
$\eta_\chi(I)=1$.

Proof. Expand the first product using (8.5). The exponent
of a fixed $\chi(T)$ is

$$
\sum_{T\subseteq I\subseteq S}(-1)^{|I|-|T|}
=(1-1)^{|S\setminus T|}.
\tag{8.7}
$$

It is one for $T=S$ and zero otherwise, proving
reconstruction. Substitution into (8.2) cancels the global,
left-only and right-only coefficients, leaving precisely
the crossing product in (8.6).

If all crossing coefficients are one, every rectangle is
one. Conversely suppose all rectangles are one. Induct on
the size of a legal crossing set $I$, evaluating its
rectangle with all unmarked sites empty. Every proper
crossing coefficient has already been shown to be one,
so (8.6) forces $\eta_\chi(I)=1$. Theorem 8.2 proves
the entropy criterion. $\square$

There is no occupation coefficient for an illegal marked
set. In particular the adjacent boundary pair does not
create a phase coordinate. For a real phase polynomial
$f(S)=\sum_I\theta_I\mathbf1_{\{I\subseteq S\}}$
and $\chi=e^{if}$, the coefficients in (8.5) are
$e^{i\theta_I}$ for its legal marked sets. This specifies
phase coordinates modulo $2\pi$, without requiring a
choice of logarithm for arbitrary $\chi$.

## 9. Mirror pair phases attain the full Fibonacci cut rank

### 9.1. One common matching on the full legal carrier

**Definition 9.1 (Boundary-aligned mirror matching).** Put
$m=\min\{k,n-k\}\ge1$. For $2\le h\le m$ let

$$
i_h=k+1-h,\qquad j_h=k+h,
\qquad
\chi_z(S)=\prod_{h=2}^m z_h^{s_{i_h}s_{j_h}},
\quad |z_h|=1.
\tag{9.1}
$$

The pairs have disjoint endpoints. The omitted $h=1$
pair is the forbidden adjacent boundary pair. All other
gates are diagonal and preserve the entire legal support.

Index the $m$ near-cut positions on each side in opposite
boundary-aligned orders, so index $m$ is each cut-boundary
position. Internally legal near-cut patterns correspond
to independent sets of the same path $P_m$. Let
$\mathcal I_m$ be that family. For $i<m$ set
$c_i=z_{m+1-i}-1$, and set $c_m=-1$. Define

$$
A=\{m\}\cup\{i<m:c_i\ne0\}.
\tag{9.2}
$$

**Theorem 9.2 (Exact rank stratification by active mirror sites).**
The Schmidt rank of $\psi_{\chi_z}$ at the original cut is

$$
\operatorname{rank}A_{\chi_z}
=|\mathcal I(P_m[A])|
=\prod_{R}F_{|R|+2},
\tag{9.3}
$$

where $R$ ranges over the maximal nonempty runs of active
sites in $A$, and $F_0=0,F_1=1$. If every supplied
$z_h\ne1$, this equals $F_{m+2}$, the maximum possible
rank at that cut.

Proof. Group all internally legal words on each side by
their near-cut $m$-site pattern. Each pattern has positive
activity mass: setting all farther sites to zero realizes
it. The normalized positive amplitude vectors of different
patterns are orthonormal because their supports are disjoint.
They retain every internally legal word, including those
on the longer side. As in Theorem 4.3, the full coefficient
matrix therefore has the same nonzero singular values as
a square sector matrix with nonzero row and column factors.
Its unweighted core is

$$
K_z(S,T)=(1-s_mt_m)
\prod_{i<m}[1+c_is_it_i],\qquad S,T\in\mathcal I_m.
\tag{9.4}
$$

Expand this finite product, writing $c_I=\prod_{i\in I}c_i$.
Only subsets of $S\cap T$ occur, and all such subsets are
legal. Thus

$$
K_z(S,T)=\sum_{I\subseteq S\cap T}c_I
=(Z\operatorname{Diag}(c_I)Z^{\mathsf T})(S,T),
\qquad Z_{S,I}=\mathbf1_{\{I\subseteq S\}}.
\tag{9.5}
$$

The finite inclusion matrix $Z$ is unit triangular when
independent sets are ordered by size, with an arbitrary
order within each size. It is invertible. This standard
incidence-matrix factorization is an intermediate ingredient;
the actual sector construction places it on the full
inhomogeneous legal phase carrier.

Multiplication by the two invertible inclusion matrices
and the nonzero activity factors preserves rank. Hence
the rank is the number of nonzero diagonal entries $c_I$.
Such entries are exactly the independent sets $I\subseteq A$.
The induced graph $P_m[A]$ is the disjoint union of its
active runs. A run of length $r$ has $F_{r+2}$ independent
sets, from the recurrence that separates its empty and
occupied final site. Independent sets of disjoint runs
combine freely, proving the product in (9.3).

If all phases are nontrivial, every site is active and
the rank is $F_{m+2}$. The two full half-chain dimensions
are $F_{k+2}$ and $F_{n-k+2}$, whose smaller value is
$F_{m+2}$. This proves maximality. $\square$

With no active pair only the boundary site remains active,
so the rank is two. One pair adjacent inside each boundary
leaves an active run of length two and gives rank three.
One farther mirror pair leaves two isolated active sites
and gives rank four. These recover the applicable branches
of Theorem 4.4. The rule for several phases depends on
active runs, not just the number of nontrivial gates.

### 9.2. The determinant and the six-site rank-five witness

**Corollary 9.3 (Core determinant).** Under Definition 9.1,

$$
\det K_z=\prod_{I\in\mathcal I_m}c_I.
\tag{9.6}
$$

It is nonzero exactly when every $z_h\ne1$. Positive
inhomogeneous activity factors cannot change this condition.

Proof. In (9.5), $\det Z=1$, so determinant multiplicativity
gives (9.6). Each singleton belongs to $\mathcal I_m$;
therefore a zero coefficient $c_i$ makes the product zero,
while nonzero coefficients make every $c_I$ nonzero.
$\square$

**Proposition 9.4 (Two mirror phases exceed the single-pair rank ceiling).**
For $n=6,k=3$, give pairs $(2,5)$ and $(1,6)$ phases
$z_2,z_3$. In the actual pattern order
$\varnothing,\{1\},\{2\},\{3\},\{1,3\}$ the core is

$$
K_z=\begin{pmatrix}
1&1&1&1&1\\
1&z_3&1&1&z_3\\
1&1&z_2&1&1\\
1&1&1&0&0\\
1&z_3&1&0&0
\end{pmatrix},\qquad
\det K_z=(z_3-1)^2(z_2-1).
\tag{9.7}
$$

Both phases nontrivial give rank five on the full positive
six-site support. A single pair phase has rank at most four
by Theorem 4.4. At $z_2=z_3=-1$, the determinant is $-8$.

Proof. The five actual three-site patterns give the listed
matrix. Their inclusion matrix has rows
$(1,0,0,0,0)$, $(1,1,0,0,0)$, $(1,0,1,0,0)$,
$(1,0,0,1,0)$ and $(1,1,0,1,1)$. Its diagonal factor
in (9.5) is
$[1,z_3-1,z_2-1,-1,-(z_3-1)]$. Multiply these entries
to obtain (9.7), and use the positive activity factors
to transfer its rank to the actual state. $\square$

The maximum rank $F_{m+2}$ is attained by $m-1$ supplied
pair phases with disjoint endpoints. This is an exact
representation statement. It does not assert physical
availability of the long-range gates, their duration or
an entropy lower bound proportional to $m$.

## 10. Matching-phase energy and maximal rank at arbitrarily small energy

**Theorem 10.1 (Exact energy for a disjoint phase matching).**
On the same positive law and fixed parent, let $\mathcal M$
be any matching of distinct mode pairs, and define
$\chi(S)=\prod_{ij\in\mathcal M}z_{ij}^{s_is_j}$,
with $|z_{ij}|=1$. The pairs need not be edges of the
exclusion graph. Then

$$
\langle\psi_\chi,H\psi_\chi\rangle
=\sum_{ij\in\mathcal M}|z_{ij}-1|^2
\mu_{ij}(d_i+d_j).
\tag{10.1}
$$

Proof. A deletion at site $i$ touches at most one phase
factor, because the supplied pairs have disjoint endpoints.
When its partner is occupied, the squared phase increment
is $|z_{ij}-1|^2$; otherwise it is zero. All other factors
have modulus one and disappear from the squared increment.
Summing the occupied-endpoint form (6.2) proves (10.1).
No independence between occupation events is assumed.
$\square$

Disjointness is material. If several pair phases share an
endpoint, deleting it changes their product simultaneously;
the squared increment then contains interference and is
not the sum of the separate increments.

**Proposition 10.2 (A full-support rank-five state with rational energy).**
For the six-site example of Proposition 9.4, set every
activity to one, every weight to $1/6$, and both phases
to $-1$. There are 21 legal words, and

$$
\mu_{1,6}=\frac17,\qquad \mu_{2,5}=\frac1{21},\qquad
\langle\psi_\chi,H\psi_\chi\rangle=\frac8{63}.
\tag{10.2}
$$

All 21 original probabilities are unchanged and nonzero.
Its cut rank is five. The two joint occupation events
are mutually exclusive, so on this carrier

$$
\chi(S)=1-2s_1s_6-2s_2s_5.
\tag{10.3}
$$

Proof. The independent-set count is $F_8=21$. Occupying
both endpoints $1,6$ leaves the legal two-site interval
$3,4$, which has three configurations. Occupying $2,5$
forces all their neighbors empty and leaves only one
configuration. Each deletion rate is $1/12$, so (10.1)
gives $4(1/7+1/21)/6=8/63$. The joint events cannot
coexist, because that would occupy both $1,2$ and both
$5,6$. Expanding their two sign factors yields (10.3).
Proposition 9.4 gives the rank. $\square$

**Proposition 10.3 (No positive energy or entropy floor from maximal rank).**
Fix $m\ge2$ and the mirror matching. With all phases
nontrivial, its cut rank is maximal. If all activities
are $\varepsilon>0$, that rank persists as
$\varepsilon\downarrow0$, whereas the state tends to
the vacuum, its entropy tends to zero and its associated
reference-parent energy tends to zero. The activity limit
varies that parent with the law. At fixed positive activities,
letting every nontrivial $z_h\to1$ also keeps maximal
rank before the limit, while energy tends to zero and
entropy tends to the positive-reference value.

Proof. Rank follows from Theorem 9.2 at every strictly
positive parameter value. The vacuum and phase limits
are norm limits of finite-dimensional coefficient matrices.
Entropy is continuous. Every joint occupation probability
tends to zero in the vacuum limit, and the factors
$|z_h-1|^2$ tend to zero in the phase limit. Formula
(10.1) proves both energy limits for fixed finite weights.
$\square$

The mirror rank formula, full phase-fiber entropy orbit
and their fixed-parent energy consequences are deductions
for this full-support model. Boolean Möbius inversion,
unit-triangular inclusion matrices and determinant
congruence are established intermediate ingredients,
not new general principles. Classical occupation,
quantum phase, matrix rank, entropy and dimensional
physical energy retain their separate meanings.

## 追加锚（本行以下为增补区）


## 11. Purity loss quantitatively controls the phase orbit

### 11.1. Complete legal rectangles give a nonnegative identity

**Definition 11.1 (Anchored phase distance and purity deficit).**
Use the full-support path law and a proper cut from Definition
8.1. Entropies use natural logarithms. Put

$$
\begin{aligned}
\mathcal W(\chi)
&=\sum_{(\ell,r)\text{ legal}}p(\ell,r)
|1-\mathfrak h_\chi(\ell,r)|^2,\\
\Delta_2(\chi)
&=\operatorname{Tr}(\rho_+^2)-\operatorname{Tr}(\rho_\chi^2).
\end{aligned}
\tag{11.1}
$$

The distance uses the actual complete occupation law, not
a replacement law on phase coordinates. Write
$a_{\ell r}=\sqrt{p(\ell,r)}$, extended by zero at illegal
concatenations. For a rectangle with all four corners legal,
set

$$
Q_{\ell\ell';rr'}
=\chi(\ell,r)\overline{\chi(\ell',r)}
\chi(\ell',r')\overline{\chi(\ell,r')}.
\tag{11.2}
$$

**Theorem 11.2 (Vacuum rectangle stability bound).**
For every full-support phase in Definition 8.1,

$$
S(\psi_\chi)-S(\psi_+)
\ge\Delta_2(\chi)
\ge 2p(\varnothing)\mathcal W(\chi)
=\frac{2}{Z}\mathcal W(\chi).
\tag{11.3}
$$

Moreover, using the canonical phases $a,b$ of (8.4),

$$
\mathcal W(\chi)
=\bigl\|\psi_\chi-(D_a\otimes D_b)\psi_+\bigr\|^2.
\tag{11.4}
$$

Proof. Expanding the two purities on the same carrier gives

$$
\Delta_2(\chi)
=\frac12\sum_{\substack{\ell,\ell',r,r'\\\text{all four corners legal}}}
a_{\ell r}a_{\ell'r}a_{\ell'r'}a_{\ell r'}
|1-Q_{\ell\ell';rr'}|^2.
\tag{11.5}
$$

Terms with an illegal corner have zero coefficient and can
be omitted. For the other terms, the reference phase is
one and the phase-dependent contribution is the real part
of (11.2); the identity
$|1-Q|^2=2(1-\operatorname{Re}Q)$ proves (11.5).
Every summand is nonnegative. This expansion is the
established four-amplitude purity or SWAP decomposition;
the anchored estimate below specializes it to the actual
positive hard-core law.

For a legal nonvacuum pair $(\ell,r)$, retain the rectangle
with the other left and right corners equal to the vacuum.
Its coefficient satisfies

$$
a_{\ell r}a_{0r}a_{00}a_{\ell0}
=p(\varnothing)p(\ell,r),
\tag{11.6}
$$

because the law is the product of the occupied activities,
restricted to legal configurations and divided by $Z$.
The four ordered orientations of this rectangle contribute
$2p(\varnothing)p(\ell,r)|1-\mathfrak h_\chi(\ell,r)|^2$.
Distinct nonvacuum pairs select disjoint sets of orientations.
If either side is vacuum, its anchored phase is one and its
contribution to $\mathcal W$ is zero. Keeping precisely
these terms of (11.5) proves the second inequality in
(11.3).

For the first inequality, the symmetric function

$$
q\longmapsto H(q)+\sum_jq_j^2
\tag{11.7}
$$

is Schur-concave on each probability simplex. The usual
Schur--Ostrowski differential criterion reduces this to,
for $x>y>0$ with $x+y\le1$,

$$
\log(x/y)\ge\frac{2(x-y)}{x+y}\ge2(x-y).
\tag{11.8}
$$

The first inequality follows by integrating $1/u$ between
y and x, or by differentiating
$\log t-2(t-1)/(t+1)$ for $t\ge1$; its derivative is
$(t-1)^2/[t(t+1)^2]\ge0$. Boundary values follow by
continuity with $0\log0=0$. Apply (11.7) to the
majorization of Theorem 8.2. Rearranging gives
$H(s_\chi)-H(s_+)\ge\sum_js_{+,j}^2-\sum_js_{\chi,j}^2$,
which is the first inequality in (11.3).

Finally, $\chi(\ell,r)=a(\ell)b(r)
\mathfrak h_\chi(\ell,r)$ and $|a(\ell)b(r)|=1$.
Squaring the coefficientwise difference of the two states
proves (11.4). $\square$

Thus a measured entropy excess at most $\delta$ implies
squared distance at most $Z\delta/2$ from this canonical
cut-local phase image. This is an explicit finite-model
estimate. Its constant depends on the original partition
function; it is not a bound uniform in chain length or
activities, and it does not identify the closest image
under all cut-local unitaries.

Every occupation observable is constant throughout the
phase fiber. A two-copy SWAP measurement on the selected
subsystem could supply its purity, if that preparation and
measurement capability were supplied. The law and phase
notation alone supply neither copies nor a SWAP apparatus.
The pure-state partial trace in (11.1) is also not an
absolute-PPT claim about a mixed bipartite state under all
global unitary conjugations.

### 11.2. A positive rank-three reference reverses the entropy comparison

**Proposition 11.3 (Larger reference rank invalidates phase entropy minimality).**
Put $D_\delta=6+3\delta^2$ and define coefficient matrices

$$
B_\delta=\frac1{\sqrt{D_\delta}}
\begin{pmatrix}
\delta&1&1\\1&\delta&1\\1&1&\delta
\end{pmatrix},\qquad
A_\delta=\frac1{\sqrt{D_\delta}}
\begin{pmatrix}
\delta&1&-1\\-1&\delta&1\\1&-1&\delta
\end{pmatrix}.
\tag{11.9}
$$

For all sufficiently small $\delta>0$, the reference
$B_\delta$ is strictly positive and has rank three,
$|A_\delta|=B_\delta$ entrywise, and the phase-perturbed
state has strictly smaller von Neumann entropy.

Proof. Their squared singular-value lists are

$$
p_\delta=
\frac{((2+\delta)^2,(1-\delta)^2,(1-\delta)^2)}{D_\delta},
\qquad
q_\delta=
\frac{(3+\delta^2,3+\delta^2,\delta^2)}{D_\delta}.
\tag{11.10}
$$

Indeed the unnormalized reference is
$(\delta-1)I+\mathbf1\mathbf1^{\mathsf T}$. The other
matrix is $\delta I$ plus a real skew-symmetric matrix
whose square is $\mathbf1\mathbf1^{\mathsf T}-3I$.
These give (11.10). At $\delta=0$,

$$
H(p_0)=\log3-\frac13\log2>\log2=H(q_0),
\tag{11.11}
$$

where the strict inequality is equivalent to $3^3>2^4$.
Finite-dimensional entropy is continuous, so the inequality
persists for all sufficiently small positive $\delta$.
At $0<\delta<1$, the reference eigenvalues $2+\delta$
and $\delta-1$ are all nonzero, and every entry is
positive. This proves the claimed full-support example.
$\square$

In this example the top reduced eigenvalue decreases, but
for $0<\delta<1/2$ the second partial sum increases.
Consequently the positive-matrix Perron bound survives while
full majorization fails. The rank-two path reference in
Theorems 8.2 and 11.2 is a substantive hypothesis.

## 12. Exact resource bounds within the diagonal pair-phase model

**Proposition 12.1 (Minimum number of cross-cut pair factors for maximal rank).**
Let $m=\min\{k,n-k\}$. Restrict operations to occupation
pair phases, allowing arbitrary cut-local diagonal phases.
At least $m-1$ nontrivial cross-cut pair factors are needed
to attain the maximal rank $F_{m+2}$. The mirror matching
of Definition 9.1 attains this bound.

Proof. On the smaller side, every nonboundary site must
occur in a nontrivial cross-cut pair. If a site is missing,
its singleton row and the vacuum row have exactly the same
allowed right support and cross-cut phase function. The
positive product amplitudes and any cut-local diagonal
phase change them only by a nonzero row scalar, so they
are proportional. They are distinct actual rows of the
$F_{m+2}$-dimensional smaller-side space; hence full row
rank is impossible. There are $m-1$ nonboundary sites,
and a cross-cut pair meets only one of them. This proves
the lower bound. Theorem 9.2 supplies attainment with
$m-1$ nontrivial mirror factors. $\square$

**Proposition 12.2 (Support diameter obstructs exact diagonal synthesis).**
Suppose $m\ge2$. Within circuits made exclusively of diagonal occupation
gates, a target with the outermost mirror phase $z_m\ne1$
cannot be synthesized, even up to cut-local diagonal phases,
by gates whose support diameters are all smaller than
$2m-1$.

Proof. A diagonal gate supported on a set $J$ has
$\eta(I)=1$ whenever $I\nsubseteq J$. In (8.5), choose
$i\in I\setminus J$ and pair each subset not containing
i with its union with i. The gate values are equal and
the exponents opposite. Multiplicative occupation
coefficients multiply under composition. Therefore gates
of the stipulated support cannot create the nontrivial
coefficient on $I=\{i_m,j_m\}$, whose endpoints are
$2m-1$ apart. Cut-local phases have no crossing
coefficient by Theorem 8.4 and cannot repair this deficit.
$\square$

These bounds price only the stipulated diagonal operation
class. They do not apply to general non-diagonal circuits,
ancilla-assisted synthesis, routing, hardware controls or
preparation work. Classical support, an exact phase target
and physical acquisition remain different inputs.

## 追加锚（本行以下为增补区）


## 13. Predecessors and the scope of the phase continuation

The multiplicative coordinates in §8 use ordinary incidence
algebra on Boolean intervals. Rota, *On the Foundations of
Combinatorial Theory I. Theory of Möbius Functions*,
[DOI:10.1007/BF00531932](https://doi.org/10.1007/BF00531932),
is the classical source of that framework. The restricted
inclusion-matrix factorization in (9.5) belongs to established
meet-matrix methods; Altınışık, Sagan and Tuğlu, *GCD
Matrices, Posets, and Nonintersecting Paths*,
[DOI:10.1080/03081080500054612](https://doi.org/10.1080/03081080500054612),
provides a nearby general treatment. These are attribution
boundaries for known ingredients. Equations (8.7) and (9.5)
provide the complete finite calculations used here; the
original Wilf and Lindström full texts are not treated as
verified theorem inputs.

Zhang, Grover and Vishwanath, *Entanglement Entropy of
Critical Spin Liquids*,
[arXiv:1102.0350v2](https://arxiv.org/abs/1102.0350v2),
equations (2)–(3) and the following sign-trick decomposition,
write purity using two-copy subsystem SWAP and separate
amplitude and phase contributions. Grover and Fisher,
*Entanglement and the Sign Structure of Quantum States*,
[arXiv:1412.3534v1](https://arxiv.org/abs/1412.3534v1),
equations (11)–(12), gives the related second-Rényi sign
and modulus decomposition, explicitly discussing the
complex-wavefunction continuation. These primary formulas
supply the established four-amplitude framework of (11.5).
They are not attributed the arbitrary-phase rank-two
von Neumann equality theorem or the vacuum-weight bound
(11.3).

The full-support path application combines its unchanged
legal Gibbs carrier, a rank-two positive reference, actual
vacuum rectangles and incidence compression. The mirror
construction also stays within the established class of
matrix-product states enhanced by commuting pair phases
cited in §7. The model-specific deductions are the complete
entropy-minimizing orbit, the active-run Fibonacci rank
stratification, the anchored purity estimate and the stated
restricted diagonal resource bounds. No literature-priority
claim is made for these deductions or their ingredients.
The unrestricted spectral comparison remains unresolved.

## 追加锚（本行以下为增补区）


## 14. Boundary-vacancy anchors give stability independent of chain length

### 14.1. Average actual anchors rather than one rare vacuum

**Definition 14.1 (Boundary-vacant anchor sectors).** Keep the
positive path law, proper cut and arbitrary phase of §§8
and 11. Let $L_0$ be the internally legal left words with
site k empty, and let $R_0$ be the internally legal right
words with site $k+1$ empty. Put

$$
B_{00}=\Pr_p(s_k=s_{k+1}=0)>0.
\tag{14.1}
$$

For $u\in L_0,v\in R_0$, all pairs $(\ell,v)$,
$(u,r)$ and $(u,v)$ are legal for every internally legal
$\ell,r$. Define

$$
\begin{aligned}
\mathfrak h_{u,v}(\ell,r)
&=\frac{\chi(\ell,r)\chi(u,v)}{\chi(\ell,v)\chi(u,r)},\\
W_{u,v}
&=\sum_{(\ell,r)\text{ legal}}
p(\ell,r)|1-\mathfrak h_{u,v}(\ell,r)|^2,\\
a_{u,v}(\ell)&=\chi(\ell,v),\qquad
b_{u,v}(r)=\frac{\chi(u,r)}{\chi(u,v)}.
\end{aligned}
\tag{14.2}
$$

Every term and phase belongs to the original legal carrier.
The anchor sectors retain all words with the stated boundary
vacancies; they do not replace the Gibbs law by a law on
sectors. Let

$$
\delta_{\mathrm{local}}(\chi)
=\inf_{|a|=|b|=1}
\bigl\|\psi_\chi-(D_a\otimes D_b)\psi_+\bigr\|^2,
\tag{14.3}
$$

where a and b range over arbitrary phases on the actual
internally legal half-chain words.

**Theorem 14.2 (Common-law boundary-vacancy stability).**
There is an actual anchor pair $u\in L_0,v\in R_0$ such
that

$$
W_{u,v}\le\frac{2\Delta_2(\chi)}{B_{00}}.
\tag{14.4}
$$

Consequently,

$$
S(\psi_\chi)-S(\psi_+)
\ge\Delta_2(\chi)
\ge\frac{B_{00}}2\delta_{\mathrm{local}}(\chi).
\tag{14.5}
$$

Proof. Keep in (11.5) only ordered rectangles whose second
left and right corners satisfy $\ell'=u\in L_0$ and
$r'=v\in R_0$. For every legal $(\ell,r)$ all four
corners are legal, and product activity weights give

$$
a_{\ell r}a_{ur}a_{uv}a_{\ell v}
=p(\ell,r)p(u,v).
\tag{14.6}
$$

Unlike the four-orientation vacuum estimate, this selection
keeps exactly one ordered-position condition. It is a subset
of the full nonnegative rectangle sum, even when other
corners are themselves boundary-vacant. Therefore

$$
\Delta_2(\chi)
\ge\frac12\sum_{u\in L_0,v\in R_0}p(u,v)W_{u,v}.
\tag{14.7}
$$

These anchor weights sum to $B_{00}$. The minimum of the
finite nonempty family $W_{u,v}$ is no larger than its
weighted average. Hence some actual pair satisfies (14.4).
Its phases in (14.2) give
$W_{u,v}=\|\psi_\chi-(D_{a_{u,v}}\otimes D_{b_{u,v}})
\psi_+\|^2$, by the same coefficientwise calculation as
(11.4). The infimum in (14.3) is at most this distance.
Rearranging (14.4) and applying Theorem 11.2 proves (14.5).
$\square$

The anchor probabilities, phase increments and reduced
purity belong to the same actual state family and law.
No independently attainable local optimum is treated as
jointly attainable, and no anchor phase is inferred from
occupation data. The existence of a good anchor does not
supply a measurement procedure for finding it.

### 14.2. The original conditional law controls the constant

**Proposition 14.3 (A local activity bound for the anchor mass).**
On the positive hard-core path law,

$$
B_{00}\ge\frac1{1+\lambda_k+\lambda_{k+1}}.
\tag{14.8}
$$

In particular,

$$
\Delta_2(\chi)
\ge\frac{\delta_{\mathrm{local}}(\chi)}
{2(1+\lambda_k+\lambda_{k+1})}.
\tag{14.9}
$$

If both cut activities are at most M, the coefficient is
at least $1/[2(1+2M)]$, independent of n and of activities
far from the cut.

Proof. Condition on any outside word having positive
probability. The two boundary sites allow only 00, 10 and
01. Neighboring outside occupations may suppress 10 or
01; they cannot suppress 00. The three relative weights
are $1,\epsilon_L\lambda_k,\epsilon_R\lambda_{k+1}$,
where each $\epsilon$ is zero or one according to actual
outside compatibility. Thus

$$
\Pr(00\mid\text{outside word})
=\frac1{1+\epsilon_L\lambda_k+
\epsilon_R\lambda_{k+1}}
\ge\frac1{1+\lambda_k+\lambda_{k+1}}.
\tag{14.10}
$$

Average over the original outside-word law to get (14.8),
and use (14.5) to obtain (14.9). $\square$

The reference rank two is required for the entropy step
in (14.5), while the weighted-anchor purity calculation
uses the actual blockaded product amplitudes. The constant
improves the full-vacuum factor $1/Z$ by summing an entire
compatible anchor sector. It does not price the diagonal
controls needed to realize the selected phases, give a
spectral gap bound for the update parent, or extend to a
Gibbs law with extra crossing interactions without a new
proof of (14.6).

## 追加锚（本行以下为增补区）


## 15. The five-mode closed-loop controls preserve the phase orbit

The fixed-preparation transport source
[AURIC probability, phase transport and holonomy](https://github.com/the-omega-institute/trureturing/blob/146d456b13542a1bd49e9278c162bf2588f183e1/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
Definition 3.1 and §3.8, already supplies the endpoint
position-locality result. Use its literal tensor order
low, middle, high, identifying modes $0,1,2,3,13$ with
$000,100,010,001,101$. Its negative-phase convention and
closed-loop relation give

$$
h_0-h_1-h_3+h_{13}=2\pi m,\qquad
\frac{e^{-ih_0}e^{-ih_{13}}}{e^{-ih_1}e^{-ih_3}}=1.
\tag{15.1}
$$

Its endpoint unitary is therefore a restriction of a product
of three position phase unitaries, up to one common phase.
The source establishes that it preserves every Schmidt
spectrum for bipartitions of these positions, comparing
initial and final states at the same probability vector.
Intervening probability legs are not asserted to preserve
that spectrum.

Thus the closed-loop histories belong to the entropy-neutral
phase orbit of §8 under this tensor identification. For a
joint occupation phase supported only at $101$, its
rectangle value is $e^{i\theta}$, so a nontrivial such gate
is outside this endpoint control class. The phase family
considered in §§4–14 is a representation of candidate
states; closed-loop histories alone do not acquire this
nontrivial rectangle.

Definition 3.1 also permits open phase legs. At fixed
probability, choose a phase-base increment $-\theta$;
its lift has residual $h_s=-\theta w_s$, with
$w_0-w_1-w_3+w_{13}=1$ and $w_2=0$. Under the source's
negative convention its endpoint multiplier is
$e^{i\theta w_s}$. Its crossing rectangle is therefore
$e^{i\theta}$, exactly that of the joint gate. Their
quotient has trivial crossing rectangle and is a product
of position-local phases by the algebra of §3.8. Thus the
declared fixed-probability open phase control acquires the
same Schmidt spectra as the three-site joint gate, up to
position-local phases. This applies at the symmetry walls
as well: it does not require a closed loop that can cancel
every local residue there. It identifies an admissible
mathematical control already in the source, while physical
preparation, implementation and calibrated energy remain
separate requirements. No corresponding control on the
full longer-chain mirror family is supplied by this
five-mode construction.

The same transport source, §4, establishes affine capacity
6 in generic position for its five-edge ideal coherence
menu. That number counts three circle characters through
two real quadratures each. It can coexist with unchanged
Schmidt spectra because fixed-reference coherence readings
are not invariant under position-local phases. The source
also establishes smaller capacities on its symmetry walls
and an anisotropic realized response Gram; none supplies a
spatial dimension, a triplet rotation action or longer-chain
joint phase controls.

For the three-site Gibbs specialization used here,
$p_{13}/p_0=\lambda_1\lambda_3$ and
$p_1/p_3=\lambda_1/\lambda_3$. The source walls
$X+Y=1-Z$ and $X=Y$ become, respectively,
$\lambda_1\lambda_3=1$ and $\lambda_1=\lambda_3$.
Consequently the uniform-activity example is on both walls,
rather than in the generic six-coordinate regime. This is
a parameter correspondence to the existing source result,
not a new capacity theorem.

## 16. Dependent-part reduction already supplies qualitative entropy minimality

Salvail, Schaffner and Sotáková,
[*Quantifying the Leakage of Quantum Protocols for Classical
Two-Party Cryptography*, arXiv:1501.01549v1](https://arxiv.org/abs/1501.01549v1),
§4.1, Theorem 4.5 and its proof, supplies a precise predecessor
for qualitative minimum entropy. For deterministic maps
$L'=f(L),R'=g(R)$ satisfying

$$
L\leftrightarrow L'\leftrightarrow R,
\qquad L\leftrightarrow R'\leftrightarrow R,
\tag{16.1}
$$

minimum regular-embedding leakage for the full classical
law is no smaller than that for the reduced law. In a
regular embedding leakage is the reduced-state entropy
minus the fixed classical mutual information; the proof
also establishes that this mutual information is unchanged
under (16.1).

For the present path Gibbs law, the left and right boundary
occupations are the dependent parts. Full words with the
same boundary bit give the same opposite-side conditional
law, and the two different bits give distinct conditional
laws under strict positive support. Their joint law has
only three positive sectors, $00,01,10$. Its bipartite
support graph is a tree, so every phase on these three
entries is removable by row and column phases. The positive
full-word reference is a local isometric image of this
positive two-by-two sector coefficient matrix.

These correspondences instantiate the cited reduction:
all reduced embeddings have the same entropy as the positive
reduced reference, and that entropy equals the full positive
reference entropy. Thus the source theorem already implies
qualitative entropy minimality for the full-word phase
family. The equality-orbit classification, full spectral
majorization, mirror rank stratification and quantitative
orbit estimates retain their separate deductions above.
The general dependent-part principle and this qualitative
consequence are not claimed as new results.

The same primary source, §6, Conjecture 6.1, proposes
canonical-embedding minimum leakage for every classical
joint law, while explicitly warning that pairwise overlap
ordering need not order entropy in dimension at least three.
Proposition 11.3 maps to its stated general claim: the two
coefficient matrices have identical classical probabilities,
so their classical mutual information cancels in the leakage
difference. This is a mathematical correspondence to the
published formulation. The subsequent literature status of
that conjecture and priority for its counterexamples are not
established here; no new external open-problem settlement is
claimed.

## 追加锚（本行以下为增补区）


## 17. Two-arm phase gluing gives bidirectional orbit stability

**Definition 17.1 (The actual three-sector rectangle averages).**
Partition the full internally legal half-chain words into
$L_a,R_b$ by their cut-boundary occupations. Write the
same original law as

$$
p(\ell,r)=p_{ab}\mu_a(\ell)\nu_b(r),\qquad
\alpha=p_{00},\quad\beta=p_{01},\quad\zeta=p_{10},
\quad\alpha+\beta+\zeta=1.
\tag{17.1}
$$

All three masses are positive; the sector $11$ is absent.
The measures $\mu_a,\nu_b$ are the normalized product
weights on actual words with the specified boundary bit.
They do not depend on the opposite boundary bit. Retain an
arbitrary unit phase $\chi(\ell,r)$ on every legal pair,
without requiring it to be constant within a sector.

For four legal corners put

$$
Q(\ell,\ell';r,r')=
\frac{\chi(\ell,r)\chi(\ell',r')}
{\chi(\ell',r)\chi(\ell,r')}.
\tag{17.2}
$$

Let $T_{ab}$ be the mean of $|1-Q|^2$ for two independent
rows sampled from $\mu_a$ and two independent columns
from $\nu_b$. Let $T_L$ sample row types $0,1$ and two
columns from $\nu_0$; let $T_R$ sample two rows from
$\mu_0$ and column types $0,1$. Every mean uses the
original conditional laws in (17.1).

**Theorem 17.2 (Three-sector orbit comparison).**
For the purity deficit and cut-local diagonal orbit distance
of §§11 and 14,

$$
C_{\rm cut}\,\delta_{\rm local}(\chi)
\le\Delta_2(\chi)\le2\delta_{\rm local}(\chi),
\qquad
C_{\rm cut}=\frac12\max\{\alpha,\min(\beta,\zeta)\}.
\tag{17.3}
$$

If $s_-$ is the smaller positive reference Schmidt
probability, then

$$
s_-=rac{1-\sqrt{1-4\beta\zeta}}2,
\qquad C_{\rm cut}\ge\frac{s_-}{2}.
\tag{17.4}
$$

Consequently the entropy excess is at least
$C_{\rm cut}\delta_{\rm local}$. No optimality of the
constant is asserted.

Proof. Sorting the full rectangle identity (11.5) by its
boundary-bit types gives exactly

$$
\Delta_2=
\frac{\alpha^2}{2}T_{00}
+\frac{\beta^2}{2}T_{01}
+\frac{\zeta^2}{2}T_{10}
+\alpha\zeta T_L+\alpha\beta T_R.
\tag{17.5}
$$

Mixed row types have two orientations, as do mixed column
types. A rectangle mixing both row and column types would
contain a forbidden $11$ corner and is absent. The four
amplitude product in each remaining sector equals the
product of its conditional sampling weights and the
corresponding sector masses. This proves (17.5) without
compressing $\chi$ to sector constants.

Theorem 14.2 already gives
$\Delta_2\ge\alpha\delta_{\rm local}/2$.
For a second construction sample independently

$$
u\sim\mu_0,\quad s\sim\mu_1,\quad
v\sim\nu_0,\quad t\sim\nu_1,
\qquad
c=\frac{\chi(u,v)}{\chi(u,t)\chi(s,v)}.
\tag{17.6}
$$

Define phases on all actual half-chain words by

$$
a(\ell)=
\begin{cases}
\chi(\ell,t),&\ell\in L_0,\\
\chi(\ell,v)/(c\chi(s,v)),&\ell\in L_1,
\end{cases}
\qquad
b(r)=
\begin{cases}
c\chi(s,r),&r\in R_0,\\
\chi(u,r)/\chi(u,t),&r\in R_1.
\end{cases}
\tag{17.7}
$$

The $01$ and $10$ residuals are their same-sector
rectangle phases. Their mean squared errors are
$\beta T_{01}$ and $\zeta T_{10}$. On $00$ the residual
factorizes as

$$
\frac{\chi(\ell,r)}{a(\ell)b(r)}
=
\frac{\chi(\ell,r)\chi(u,t)}
{\chi(\ell,t)\chi(u,r)}
\frac{\chi(u,r)\chi(s,v)}
{\chi(u,v)\chi(s,r)}.
\tag{17.8}
$$

These two factors are a $T_R$ rectangle and a $T_L$
rectangle. They share sampled corners; independence of
these factors is neither used nor asserted. For unit
$q,q'$ the triangle inequality gives

$$
|1-qq'|^2\le2|1-q|^2+2|1-q'|^2.
\tag{17.9}
$$

Each candidate gauge has error at least the orbit infimum.
Average (17.7) over its finite anchor family to obtain

$$
\delta_{\rm local}
\le\beta T_{01}+\zeta T_{10}
+2\alpha(T_L+T_R).
\tag{17.10}
$$

Multiplying this right side by
$\min(\beta,\zeta)/2$ and comparing each nonnegative
term with (17.5) proves the second lower coefficient.
Combining the two constructions proves the lower bound
in (17.3).

For the upper bound let $B_{\ell r}=\sqrt{p(\ell,r)}$
and, for any candidate gauge, let
$A_{\ell r}=B_{\ell r}\chi(\ell,r)/(a(\ell)b(r))$.
Both matrices vanish on forbidden pairs. Use the established
Schatten norm, as defined by Watrous,
[*The Theory of Quantum Information*, §1.1.3,
equations (1.165)–(1.167) and (1.173)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf).
The function $F(M)=\|M\|_4^4=\operatorname{Tr}(MM^*)^2$
is convex: norm convexity followed by convexity and
monotonicity of the fourth power proves this. Its real
directional derivative at $B$ gives

$$
F(B)-F(A)\le4\operatorname{Re}
\langle BB^*B,B-A\rangle.
\tag{17.11}
$$

The positive reference is the local isometric image of
$B_0=\left(\begin{smallmatrix}\sqrt\alpha&\sqrt\beta\\
\sqrt\zeta&0\end{smallmatrix}\right)$.
On its three legal sectors direct multiplication gives

$$
\frac{(BB^*B)_{\ell r}}{B_{\ell r}}=
\begin{cases}
1,&00,\\
\alpha+\beta,&01,\\
\alpha+\zeta,&10.
\end{cases}
\tag{17.12}
$$

Every coefficient lies in $[0,1]$, and
$|1-e|^2=2(1-\operatorname{Re}e)$ for a unit phase $e$.
Thus (17.11) is at most twice this candidate gauge's
weighted squared error. Its left side is $\Delta_2$,
because row and column phase multiplication preserves
purity. Take the infimum over all candidate gauges to get
the upper bound in (17.3).

Finally $s_-(1-s_-)=\beta\zeta$ and $s_-\le1/2$.
For either $b=\beta$ or $b=\zeta$, the other mass is
at most $1-b$, so $s_-(1-s_-)\le b(1-b)$.
If $b<s_-$, both factors in
$(s_--b)(1-s_--b)$ are positive, contradicting that
inequality. Hence $\min(\beta,\zeta)\ge s_-$,
proving (17.4). Apply Theorem 11.2 for the entropy
consequence. $\square$

The coefficient uses the realized law rather than a full
vacuum probability. If the adjacent activities are bounded,
Theorem 14.3 already supplies a size-independent lower
bound. Alternatively a nondegenerate reference Schmidt
probability controls it through (17.4). This is distance
to diagonal row/column phases, not to the orbit under all
local unitaries.

**Proposition 17.3 (Full-support degeneration and inefficient vacuum anchoring).**
On $P_3$ with the cut after site 2, choose
$(\lambda_1,\lambda_2,\lambda_3)=(1,t^2,t)$,
$t>0$, and $\chi(S)=(-1)^{s_1s_3}$. Then

$$
Z=t^2+2t+2,\quad
\alpha=2/Z,\quad\beta=2t/Z,\quad\zeta=t^2/Z,
\tag{17.13}
$$

and the exact orbit quantities are

$$
\Delta_2=2\alpha\beta,\qquad
\delta_{\rm local}
=2\left(\alpha+\beta-\sqrt{\alpha^2+\beta^2}\right),
\qquad W=4t/Z.
\tag{17.14}
$$

Every finite $t$ has full legal support, but

$$
\frac{\Delta_2}{\delta_{\rm local}}
=\frac{\alpha+\beta+\sqrt{\alpha^2+\beta^2}}2
\sim s_-\sim\frac2t\longrightarrow0,
\qquad
\frac{W}{\delta_{\rm local}}\sim t.
\tag{17.15}
$$

Proof. The only nontrivial rectangle uses the two $L_0$
rows and the two right words, giving $\Delta_2=8t/Z^2$.
For the exact gauge optimization choose the relative column
phase $e^{i\varphi}$. Optimizing each row phase separately
gives overlap

$$
\zeta+\frac{|1+te^{i\varphi}|+|1-te^{i\varphi}|}{Z}.
\tag{17.16}
$$

The sum is at most $2\sqrt{1+t^2}$ by the scalar
Cauchy inequality, attained when $\cos\varphi=0$.
The orbit distance is twice one minus the maximal overlap,
which gives (17.14). The vacuum gauge differs only on
$101$, proving the formula for $W$. Rationalizing the
distance proves (17.15). Also
$\Delta_2=2W/Z$ exactly. $\square$

Thus activity or cut-spectrum degeneration cannot be removed
from every positive lower comparison. The canonical vacuum
bound can be attained even when its chosen gauge is
arbitrarily worse than the closest diagonal local gauge.

## 18. Extended mirror signs have extensive energy after every local phase gauge

**Definition 18.1 (The actual parent energy on a phase orbit).**
Retain the parent $H$ of Definition 1.2 and its occupied
endpoint form (6.2). Put

$$
E_{\rm orb}(\chi)=\inf_{|a|=|b|=1}
\sum_Sp(S)\sum_{i\in S}\frac{w_i}{1+\lambda_i}
\left|\frac{\chi(S)}{a(\ell_S)b(r_S)}-
\frac{\chi(S\setminus\{i\})}
{a(\ell_{S\setminus\{i\}})b(r_{S\setminus\{i\}})}\right|^2.
\tag{18.1}
$$

The infimum changes only the phase representative. It
retains the original law, weighted parent and deletion
clocks, and does not conjugate the parent with the phase.

**Theorem 18.2 (Robust extensive mirror obstruction).**
On $P_{2m}$, $m\ge2$, cut after site $m$. Assume
$0<\ell_0\le\lambda_i\le M$ and $w_i>0$, and define

$$
\chi(S)=(-1)^{\sum_{h=2}^m s_{m+1-h}s_{m+h}},
\qquad
\eta=\frac{\ell_0}{(1+M)^2+\ell_0}.
\tag{18.2}
$$

Then

$$
E_{\rm orb}(\chi)\ge
\frac{4\eta^2}{1+M}
\sum_{h=2}^m(w_{m+1-h}+w_{m+h}).
\tag{18.3}
$$

In particular, for uniform activities and weights equal to
one, with the actual deletion rates $d_i=1/2$,

$$
E_{\rm orb}(\chi)\ge\frac{4(m-1)}{25}.
\tag{18.4}
$$

Proof. On any path segment with activities in the stated
range, the occupation odds at a free site are its activity
times the vacancy probabilities at the endpoints of the
two adjacent segments. Each such endpoint vacancy is at
least $1/(1+M)$; an absent segment contributes one.
Thus its occupation probability $u$ satisfies

$$
\eta\le u\le\frac{M}{1+M},\qquad
1-u\ge\frac1{1+M}\ge\eta.
\tag{18.5}
$$

The same assertion holds if an end site is forced vacant,
after deleting that site and considering the remaining
segment. The final inequality follows from
$\ell_0\le M$.

Fix any complete left word containing a matching endpoint
$i=m+1-h$, $h\ge2$, with partner $j=m+h$.
Conditionally on that left word the right side is its
original Gibbs path, with at most its first site forced
vacant. The partner $j\ge m+2$ is free, so its conditional
occupation probability satisfies (18.5).

Deleting $i$ changes only its matched sign. For any chosen
row and column gauge, the column gauge cancels in the
phase increment, and the row-gauge ratio is one unit
complex number fixed by the left word. For a Bernoulli
occupation with parameter $u$, and every unit $z$,

$$
\mathbb E\left|(-1)^{s_j}-z\right|^2
\ge\min_{|z'|=1}\mathbb E\left|(-1)^{s_j}-z'\right|^2
=4\min(u,1-u)\ge4\eta.
\tag{18.6}
$$

The unconditional probability that $i$ is occupied is at
least $\eta$, and its actual deletion rate is at least
$w_i/(1+M)$. Its energy contribution is therefore at
least $4\eta^2w_i/(1+M)$ for every gauge. The symmetric
argument applies to the right endpoint. All matching
endpoints are distinct, so their nonnegative contributions
add without counting an update twice. This proves (18.3)
for every gauge and hence for the infimum. With
$\ell_0=M=1$, $\eta=1/5$, giving (18.4). $\square$

For the uniform family, $\alpha\ge1/3$ by Theorem 14.3,
and $\beta,\zeta\ge1/5$ by (18.5). In particular the
reference cut spectrum stays nondegenerate. Nevertheless
$\delta_{\rm local}\le2$ and $\Delta_2\le1$, while
(18.4) grows with $m$. Thus bounded activities, bounded
actual update rates and a nondegenerate cut spectrum do not
supply any size-independent constant C for either
$E_{\rm orb}\le C\delta_{\rm local}$ or
$E_{\rm orb}\le C\Delta_2$. Rescaling all weights changes
the parent and the energy bound and must be stated explicitly.

The established spectral comparison remains valid with its
actual global scale. Write $\Omega_H=\|H\|=\Lambda$
and retain the gap $\gamma$ of Definition 1.2. For any
unit phase $f$, the simple zero eigenspace gives

$$
\gamma\left(1-|\mathbb E_pf|^2\right)
\le\langle\Psi_f,H\Psi_f\rangle
\le\Omega_H\left(1-|\mathbb E_pf|^2\right),
\qquad\Omega_H\le\sum_iw_i.
\tag{18.7}
$$

Overall phase is an allowed local gauge. Compactness of the
finite phase tori gives the maximal absolute overlap
$M_\chi=\max_{|a|=|b|=1}|\mathbb E_p[\chi/(ab)]|
=1-\delta_{\rm local}/2$. Applying the lower
bound to every gauge and the upper bound at a
maximum-overlap gauge yields

$$
\gamma\left(\delta_{\rm local}-
\frac{\delta_{\rm local}^2}{4}\right)
\le E_{\rm orb}\le
\Omega_H\left(\delta_{\rm local}-
\frac{\delta_{\rm local}^2}{4}\right).
\tag{18.8}
$$

This reuses the spectral theorem; it does not equate the
energy and distance optimizers. Combining it with the new
same-law estimate (17.3), and monotonicity of
$x-x^2/4$ on $[0,2]$, gives

$$
\gamma\left(\frac{\Delta_2}{2}-\frac{\Delta_2^2}{16}\right)
\le E_{\rm orb}\le\frac{\Omega_H}{C_{\rm cut}}\Delta_2.
\tag{18.9}
$$

The global factor in this upper comparison cannot be
replaced by only the cut activities and reference spectrum,
as (18.4) proves. None of these parent expectations assigns
a physical energy unit or the work of acquiring the phases.

## 追加锚（本行以下为增补区）


## 19. Four classical hidden states do not bound coherent Schmidt rank

**Definition 19.1 (One fixed stationary mixture on the original no11 shift).**
For $0<r<1$ let $P_r$ be the stationary binary Markov law
with transition and stationary row

$$
T_r=
\begin{pmatrix}1-r&r\\1&0\end{pmatrix},\qquad
\pi_r=\frac{(1,r)}{1+r}.
\tag{19.1}
$$

Fix once and for all $0<p<q<1$ and $0<a<1$, and put
$P=aP_p+(1-a)P_q$. These parameters do not depend on
window length or desired rank. For every finite window,
let $P_n$ be its actual marginal and prescribe the positive
coherent representative

$$
|\Psi_n\rangle=\sum_{w\in B_n}\sqrt{P_n(w)}|w\rangle.
\tag{19.2}
$$

The classical law is one stationary law on the whole
no11 shift. Equation (19.2) specifies separate finite-window
pure-state embeddings; it does not assert that they are
compatible reduced states of one infinite quantum pure state.

The two-state edge-emission matrices of each component are

$$
E_0(r)=\begin{pmatrix}1-r&0\\1&0\end{pmatrix},\qquad
E_1(r)=\begin{pmatrix}0&r\\0&0\end{pmatrix}.
\tag{19.3}
$$

Use the four-state matrices
$M_x=E_x(p)\oplus E_x(q)$ and initial stationary row
$(a\pi_p,(1-a)\pi_q)$. They are nonnegative,
$M_0+M_1$ is stochastic, the displayed row is stationary,
and $M_1^2=0$. Their cylinder formula is exactly $P_n$.
Thus they belong to the entire four-state domain of the
[uniform renewal and three-state separation source](https://github.com/the-omega-institute/trureturing/blob/f0babd0c3289992dff4b7704c6465bfeda6bef07/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_UNIFORM_RENEWAL_NONATTAINMENT_AND_THREE_STATE_SEPARATION.md),
Definition 1.2, including its permission for reducible
presentations. This mixture is not the source's irreducible
four-state example of §12.

**Theorem 19.2 (Unbounded positive coherent rank with fixed classical producer).**
The law P has full support on every finite legal word,
and has one classical edge-emission representation with four
hidden states. For every integer $d\ge1$, the positive
coherent state $\Psi_{4d+2}$ has Schmidt rank at least
$d+1$ across the cut after site $2d+1$. Consequently no
fixed exact matrix-product bond dimension represents all
these prescribed positive coherent states.

Proof. The finite stationary word probability is
$\pi_r(w_1)\prod_{j=1}^{n-1}T_r(w_j,w_{j+1})$.
Every legal word has positive weight, so every $P_n$ has
full legal support. The matrices in (19.3) give the claimed
fixed classical representation. At any cut its classical
probability matrix factors as

$$
P_n(\ell,r)=\sum_{h=1}^4
(\lambda M_\ell)_h(M_r\mathbf1)_h,
\tag{19.4}
$$

so its nonnegative rank is at most four. Here $\lambda$
is the stationary row of Definition 19.1, not a Gibbs
activity.

Set $L=2d+1$ and choose complete half-window words

$$
u_i=0(10)^i0^{2(d-i)},\qquad 0\le i\le d.
\tag{19.5}
$$

Every $u_i$ has length L, starts and ends in zero, and
has exactly i ones. Each concatenation $u_iu_j$ is legal
in the original carrier, with $i+j$ transitions $0\to1$,
$i+j$ transitions $1\to0$ and $4d+1-2(i+j)$
transitions $0\to0$. Therefore, writing $n=4d+2$,

$$
P_r(u_iu_j)=A_r(n)b_r^{i+j},\qquad
A_r(n)=\frac{(1-r)^{n-1}}{1+r},\qquad
b_r=\frac{r}{(1-r)^2}.
\tag{19.6}
$$

The function $b_r$ is strictly increasing on $(0,1)$.
Thus $t=b_q/b_p>1$. Put
$c_n=(1-a)A_q(n)/(aA_p(n))>0$.
The corresponding full coefficient submatrix of (19.2) is

$$
\sqrt{P_n(u_iu_j)}=
\sqrt{aA_p(n)}\,b_p^{i/2}b_p^{j/2}
\sqrt{1+c_nt^{i+j}}.
\tag{19.7}
$$

All row and column factors are nonzero. Invoke the existing
matrix theorem of Jain,
[*Hadamard powers of rank two, doubly nonnegative matrices*,
arXiv:2004.03909v1, Corollary 5, p. 8](https://arxiv.org/abs/2004.03909v1).
It states that $[(1+y_ix_j)^s]$ is nonsingular for distinct
real $x_j,y_i$ with all $1+y_ix_j>0$, when
$s\notin\{0,1,\ldots,N-2\}$. Here choose
$N=d+1$, $x_i=y_i=\sqrt{c_n}t^i$ and $s=1/2$.
These are distinct positive coordinates and satisfy all
hypotheses. The square-root kernel in (19.7) is therefore
nonsingular, so this actual $(d+1)$-dimensional minor has
rank $d+1$. The reduced density matrix is $AA^*$ and is
positive semidefinite regardless of the coefficient matrix's
eigenvalue signs. The full coefficient matrix, on every legal
word and with zero entries on forbidden pairs, has at least
that rank. Pure-state Schmidt rank equals coefficient-matrix
rank, proving the theorem. $\square$

The scalar $c_n$ depends on window length; the law's
parameters $a,p,q$ remain fixed. The cited nonsingularity
holds for every positive $c_n$, so no length-dependent
choice of law, limiting genericity argument or unproved
avoidance of determinant zeros is used. The matrix theorem
and the distinction between ordinary and entrywise-power
ranks are existing results. The displayed stationary no11
construction identifies their exact interface to the
finite-hidden domains; it makes no literature-priority claim.

**Proposition 19.3 (One occupation law permits different quantum carriers).**
For the same finite marginal $P_n$, $n\ge2$, put

$$
|\psi_{r,n}\rangle=\sum_{w\in B_n}\sqrt{P_{r,n}(w)}|w\rangle,
\qquad
\sigma_n=a|\psi_{p,n}\rangle\langle\psi_{p,n}|
+(1-a)|\psi_{q,n}\rangle\langle\psi_{q,n}|.
\tag{19.8}
$$

The mixed state $\sigma_n$ and the pure state
$|\Psi_n\rangle\langle\Psi_n|$ have identical occupation
probabilities. Schmidt number is the minimum, over pure-state
ensembles of a mixed state, of their largest cut Schmidt rank.
At each proper cut $\sigma_n$ has Schmidt
number at most two through its displayed ensemble, whereas
Theorem 19.2 gives arbitrarily large pure-state Schmidt
rank for $\Psi_n$.

Proof. Both diagonals are exactly
$aP_{p,n}(w)+(1-a)P_{q,n}(w)=P_n(w)$.
The two component vectors are not proportional: their
one-site occupation probabilities are $p/(1+p)$ and
$q/(1+q)$, which differ. With both mixture weights positive,
$\sigma_n$ is therefore mixed.
For a legal word with k ones and endpoint bits $s_1,s_n$,
transition counting gives

$$
P_{r,n}(w)=\frac{(1-r)^{n-1}}{1+r}
\left(\frac{r}{(1-r)^2}\right)^k
(1-r)^{s_1+s_n}.
\tag{19.9}
$$

Thus each component is precisely a positive hard-core
product-activity law: internal activities are
$r/(1-r)^2$, and the two endpoint activities are
$r/(1-r)$. Its positive coherent state has Schmidt rank
two at every proper cut by the positive-reference
factorization of §4. The ensemble in (19.8) therefore
bounds the mixed-state Schmidt number by two. No rank
bound is inferred for the coherent square root of the
mixture; its explicit larger minor is (19.7). $\square$

This supplies a paired same-observation example. Classical
probability data specify neither the positive coherent
preparation (19.2) nor the mixed preparation (19.8).
Unbounded exact Schmidt rank gives no conclusion here about
entropy divergence, approximate bond dimension, minimal
quantum statistical memory or physical preparation work.

Under the uniform renewal source's stated Universal and
Direct premises, its Lemma 11.1 and Theorem 11.4 also give

$$
d(P)=a\,d(P_p)+(1-a)\,d(P_q)
\le C_2\le C_3<c_\star.
\tag{19.10}
$$

The two positive closed hidden components each have two
states and are the irreducible chains (19.1), so the
source's actual-component affinity applies with weights
a and $1-a$. This uses its classical conclusions only
under their supplier premises. The coherent embedding
keeps the exact same visible probabilities and hence the
same harmonic-edge objective. Its large Schmidt rank
does not turn this classical mixture into an attainer or
settle the original all-dimension question.

## 追加锚（本行以下为增补区）


## 20. Unbounded exact rank coexists with exponential bond-four approximation

**Definition 20.1 (Overlap and a coherent sum of the two components).**
Retain the single fixed stationary mixture of Definition 19.1.
All vectors below have nonnegative real coefficients. Define

$$
\mathcal B_n=\langle\psi_{p,n},\psi_{q,n}\rangle
=\sum_{w\in B_n}\sqrt{P_{p,n}(w)P_{q,n}(w)},\qquad
C_n=2\sqrt{a(1-a)}\,\mathcal B_n,
\tag{20.1}
$$

and prescribe another pure state

$$
v_n=\sqrt a\,\psi_{p,n}+\sqrt{1-a}\,\psi_{q,n},\qquad
\Phi_n=\frac{v_n}{\sqrt{1+C_n}}.
\tag{20.2}
$$

Unlike the mixed state $\sigma_n$, the state $\Phi_n$ is a
coherent sum. Its occupation law need not equal $P_n$.
It is used only as an approximation to $\Psi_n$.

**Lemma 20.2 (Exponential classical Hellinger overlap).**
Put

$$
x=\sqrt{(1-p)(1-q)},\quad y=\sqrt{pq},\quad
\gamma=x+y.
\tag{20.3}
$$

Then $0<\gamma<1$ and, for every $n\ge1$,

$$
0<\mathcal B_n\le\gamma^{\lfloor(n-1)/2\rfloor},\qquad
0<C_n\le\mathcal B_n.
\tag{20.4}
$$

Proof. The two distinct unit vectors
$(\sqrt{1-p},\sqrt p)$ and $(\sqrt{1-q},\sqrt q)$
have positive inner product $\gamma<1$. This is the
strict scalar Cauchy inequality; equality would force
$p=q$. Entrywise square roots of the two Markov word
weights give the exact transfer formula

$$
\mathcal B_n=bK^{n-1}\mathbf1,\qquad
b=\left(\sqrt{\pi_p(0)\pi_q(0)},
\sqrt{\pi_p(1)\pi_q(1)}\right),\quad
K=\begin{pmatrix}x&y\\1&0\end{pmatrix}.
\tag{20.5}
$$

No hidden-path sum is placed inside a square root: each
component is itself a visible first-order Markov law.
The row b is nonnegative with $b\mathbf1\le1$.
Coordinatewise,

$$
K\mathbf1=(\gamma,1)^{\mathsf T}\le\mathbf1,\qquad
K^2\mathbf1=(x\gamma+y,\gamma)^{\mathsf T}
\le\gamma\mathbf1.
\tag{20.6}
$$

Positivity of K permits iteration of the second inequality;
for an odd remaining power also use the first. Thus
$K^{n-1}\mathbf1\le\gamma^{\lfloor(n-1)/2\rfloor}\mathbf1$,
proving the first bound. The second follows from
$2\sqrt{a(1-a)}\le1$. $\square$

**Theorem 20.3 (One rank-four approximation works across all cuts).**
For every $n\ge2$, the single state $\Phi_n$ has Schmidt
rank at most four at every cut and hence an exact open-chain
matrix-product representation with bond dimensions at most
four. It satisfies

$$
\langle\Psi_n,\Phi_n\rangle\ge\frac1{\sqrt{1+C_n}},\qquad
\|\Psi_n-\Phi_n\|^2\le
2-\frac2{\sqrt{1+C_n}}\le C_n.
\tag{20.7}
$$

For the trace distance, with the factor-one-half convention,

$$
\begin{aligned}
T_n&=\tfrac12\big\|
|\Psi_n\rangle\langle\Psi_n|
-|\Phi_n\rangle\langle\Phi_n|\big\|_1\\
&\le t_n:=\sqrt{\frac{C_n}{1+C_n}}
\le\sqrt{2\sqrt{a(1-a)}}\,
\gamma^{\lfloor(n-1)/2\rfloor/2}.
\end{aligned}
\tag{20.8}
$$

The parameters $a,p,q$ and the bound four do not depend on
n or on a chosen cut.

Proof. Each component coefficient matrix has rank two by
Proposition 19.3. At every cut the coefficient matrix of
$v_n$ is their weighted sum, with rank at most four;
normalization preserves that bound. Sequential Schmidt
decompositions of this same vector give the stated
matrix-product representation. Independent choices of
approximant at different cuts are unnecessary.

The norm of $v_n$ is $\sqrt{1+C_n}$. For every legal word,

$$
v_n(w)=\sqrt{aP_{p,n}(w)}+\sqrt{(1-a)P_{q,n}(w)}
\ge\sqrt{aP_{p,n}(w)+(1-a)P_{q,n}(w)}=\Psi_n(w).
\tag{20.9}
$$

Multiplying by $\Psi_n(w)$ and summing gives
$\langle\Psi_n,v_n\rangle\ge1$, proving the overlap
and the first distance bound. For $c\ge0$,
$2-2/\sqrt{1+c}\le c$: with $s=\sqrt{1+c}\ge1$,
$cs-2s+2=(s-1)^2(s+2)\ge0$. This proves (20.7).

For normalized pure vectors u,v, diagonalizing the difference
of the two projectors on their two-dimensional span gives
$\tfrac12\||u\rangle\langle u|-|v\rangle\langle v|\|_1
=\sqrt{1-|\langle u,v\rangle|^2}$.
Apply (20.7), then Lemma 20.2, to obtain (20.8). $\square$

**Corollary 20.4 (No entropy divergence for this exact-rank example).**
Use natural logarithms, and let $S_{n,k}$ be the cut
entanglement entropy of $\Psi_n$ after site k. For all
sufficiently large n, uniformly in $1\le k<n$,

$$
S_{n,k}\le\log4+n(\log2)t_n+h(t_n),\qquad
h(t)=-t\log t-(1-t)\log(1-t).
\tag{20.10}
$$

In particular

$$
\limsup_{n\to\infty}\max_{1\le k<n}S_{n,k}\le\log4,
\qquad
\sup_{n\ge2}\max_{1\le k<n}S_{n,k}<\infty.
\tag{20.11}
$$

Proof. Partial trace contracts trace distance. For example,
its variational characterization tests an operator Q with
$0\le Q\le I$ on the subsystem by the allowed operator
$Q\otimes I$ on the full system. Thus every cut reduction
of $\Psi_n$ is within trace distance $t_n$ of that of
$\Phi_n$. The latter has rank at most four and entropy at
most $\log4$.

Use the existing sharp entropy-continuity inequality of
[Audenaert, *A Sharp Fannes-type Inequality for the von
Neumann Entropy*, arXiv:quant-ph/0610146v1, Theorem 1,
p. 2, equation (6)](https://arxiv.org/abs/quant-ph/0610146v1).
After multiplying its base-two form by $\log2$, its bound
is $T\log(d-1)+h(T)$. The subsystem dimension is at most
$2^n$. For all sufficiently large n, $t_n\le1/2$;
h is then increasing on $[0,t_n]$, so replacing the actual
reduced-state distance T by $t_n$ gives (20.10).
Exponential decay in (20.8) implies $nt_n\to0$ and
$h(t_n)\to0$. The remaining finitely many n have finite
dimension, proving both assertions. $\square$

The unbounded exact ranks of Theorem 19.2 and the fixed-bond
approximation of Theorem 20.3 concern the same fixed law
and the same prescribed positive coherent vectors. The
rank lower bound detects nonzero Schmidt coefficients,
including arbitrarily small ones. It supplies neither
approximate bond-dimension growth nor entropy divergence.
The low-bond approximation need not reproduce the diagonal
law exactly and is not the mixed carrier of Proposition
19.3. No physical preparation, efficient parameter-learning
procedure, common infinite pure state or minimal quantum
statistical memory is inferred. Hellinger transfer, rank
subadditivity, sequential Schmidt decomposition and entropy
continuity are reused methods; this stationary no11
application makes no priority claim.

## 追加锚（本行以下为增补区）


## 21. An extensive phase energy with exactly fixed reference cut spectrum

In Proposition 17.3, the vacuum error written W in
(17.14)–(17.15) and their proof means $\mathcal W(\chi)$
of Definition 11.1. It is distinct from the total update
weight $W=\sum_iw_i$ of Definition 1.1. In §§17–18 the
local anchor estimate numbered 14.3 is Proposition 14.3.

**Proposition 21.1 (Fixed cut data do not control the global orbit energy).**
Let $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$. On $P_{2m}$,
$m\ge3$, cut after site m and use the mirror phase of
(18.2). Choose all update weights $w_i=1$ and activities

$$
\lambda_m=\lambda_{m+1}=1,\qquad
\lambda_{m-1}=\lambda_{m+2}=\frac{F_m}{F_{m-1}},\qquad
\lambda_i=1\ \text{at every other site}.
\tag{21.1}
$$

Every activity belongs to $[1,2]$, all actual deletion
clocks belong to $[1/3,1/2]$, and the three reference
boundary sectors and the smaller Schmidt probability are
exactly

$$
\alpha=\tfrac12,\qquad\beta=\zeta=\tfrac14,\qquad
s_-=\frac{2-\sqrt3}{4},
\tag{21.2}
$$

independent of m. Nevertheless

$$
E_{\rm orb}(\chi)\ge\frac{2(m-1)}{75}.
\tag{21.3}
$$

Consequently there is no finite constant determined only
by the two cut activities and the exact positive-reference
Schmidt spectrum that bounds $E_{\rm orb}$ above by a
constant times $\delta_{\rm local}$ or $\Delta_2$ on this
family. The update weights, their uniform bounds and the
global activity bounds are fixed as well.

Proof. For one unjoined half-chain let $Z_0,Z_1$ be its
partition sums with its cut endpoint vacant or occupied.
The endpoint activity is one; occupation forces its neighbor
vacant and leaves a unit-activity path of length $m-2$.
Thus, putting $t=F_m/F_{m-1}$,

$$
Z_1=F_m,\qquad
Z_0=F_m+tF_{m-1}=2F_m.
\tag{21.4}
$$

The right half is its reflection. Gluing the two endpoints
retains sectors $00,01,10$, with unnormalized weights
$4F_m^2,2F_m^2,2F_m^2$. This proves the three sector
masses in (21.2). The rank-two reference formula gives
$s_-=(1-\sqrt{1-4\beta\zeta})/2=(2-\sqrt3)/4$.
No limiting replacement of the exact spectrum is used.

The Fibonacci recurrence gives $1\le t\le2$. Apply
Theorem 18.2 with $\ell_0=1,M=2$, so $\eta=1/10$.
There are $2(m-1)$ matched endpoints, each of weight one;
(18.3) yields (21.3). The actual deletion clock at site i
is $1/(1+\lambda_i)$ as asserted. Finally
$\delta_{\rm local}\le2$ and $\Delta_2\le1$ while
(21.3) is unbounded. All the proposed arguments of such
a constant are identical for every member of this family,
so no such finite constant exists. $\square$

This fixed-spectrum family supplies the global-scale
obstruction in the last paragraph of §18 with identical
cut data, including the exact spectrum. The norm factor
in (18.8) remains the actual global parent norm, and none
of these dimensionless expectations determines a physical
energy unit.

## 追加锚（本行以下为增补区）


## 22. An irreducible two-state renewal source already has unbounded positive coherent rank

**Definition 22.1 (A fixed equal-parameter simple nonunifilar source).**
For the rest of this section fix permanently

$$
M_0=\frac12\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
M_1=\frac12\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad
\lambda=(1/2,1/2),\qquad
P(w)=\lambda M_w\mathbf1.
\tag{22.1}
$$

This is the equal-parameter simple nonunifilar source
(SNS). Its renewal law is an existing model: see
[Marzen–Crutchfield, *Informational and Causal Architecture
of Discrete-Time Renewal Processes*, arXiv:1408.6876,
§V, Figure 7 and equation (15)](https://arxiv.org/abs/1408.6876).
Equation (15) at the equal parameter $1/2$ gives the
interevent zero-count probabilities below. The model and
the general distinction between generating and predictive
hidden states are not new here.

The total transition matrix has every entry $1/2$.
Thus it is stochastic, irreducible and aperiodic;
$\lambda(M_0+M_1)=\lambda$ and $M_1^2=0$.
The cylinder formula in (22.1) therefore defines one
stationary law on the original no11 shift. All its
parameters and hidden matrices are independent of length.
As in (19.2), define the prescribed finite-window positive
coherent state by
$\Psi_n(P)=\sum_{w\in B_n}\sqrt{P(w)}|w\rangle$.
No quantum marginal consistency is imposed on this family.

**Lemma 22.2 (Actual word probabilities and the reset interface).**
Write $M_1=\beta\alpha$ with
$\beta=(0,1/2)^{\mathsf T}$ and $\alpha=(1,0)$.
The zero-run transition powers and gap probabilities are

$$
M_0^k=2^{-k}\begin{pmatrix}1&k\\0&1\end{pmatrix},\qquad
\gamma_k=\alpha M_0^k\beta=\frac{k}{2^{k+1}},
\quad k\ge0.
\tag{22.2}
$$

In particular $\gamma_0=0$, all $\gamma_k$ for $k\ge1$
are positive and their sum is one. A one-emission resets
the hidden state to $\alpha$, so these are the independent
successive interevent zero-count probabilities. Moreover
$P(0^n)=(n+2)/2^{n+1}\to0$; stationarity then excludes
an infinite zero tail on either side. This is a proper
stationary renewal law, with no adjacent ones.

For any legal length-n word with at least one one, let
A and B be the zero counts before its first and after
its last one, and let $g_1,\ldots,g_{k-1}$ be the zero
counts between its k ones. Then

$$
P(w)=\frac{(A+1)(B+1)\prod_{h=1}^{k-1}g_h}{2^{n+1}},
\qquad
P(0^n)=\frac{n+2}{2^{n+1}}.
\tag{22.3}
$$

Thus every legal word has strictly positive probability.
For complete half-words
$u_i=0^{A_i}1\,0^{r_i}$ and
$v_j=0^{s_j}1\,0^{B_j}$ of fixed respective lengths,
the same original word probability factorizes as

$$
P(u_iv_j)=
(\lambda M_0^{A_i}\beta)\,
\gamma_{r_i+s_j}\,
(\alpha M_0^{B_j}\mathbf1).
\tag{22.4}
$$

Proof. Induction on k gives the power formula. After an
emitted one, the rank-one factor $\beta\alpha$ leaves
the normalized row $\alpha$. Repeated substitution gives
the renewal gaps and, using

$$
\lambda M_0^A\beta=\frac{A+1}{2^{A+2}},\qquad
\alpha M_0^B\mathbf1=\frac{B+1}{2^B},
\tag{22.5}
$$

the exact formula (22.3). Its exponents add to n+1,
including all one-emissions. Normalization and both
cylinder consistencies already follow from the stochastic
matrix and its stationary row. Twice substituting
$M_1=\beta\alpha$ in the complete ordered word product
gives (22.4), without aggregating words or changing the
probability law. $\square$

**Theorem 22.3 (Minimal classical hidden dimension does not bound positive coherent rank).**
The single law (22.1) has minimal nonnegative classical
edge-emission dimension two. For every $m\ge1$,

$$
\operatorname{SR}_{m+2\,|\,m+2}\Psi_{2m+4}(P)\ge m.
\tag{22.6}
$$

Consequently even fixed minimal classical hidden dimension
two, irreducibility, aperiodicity, renewal structure and
full legal support do not bound the exact bond dimension
of these prescribed positive coherent embeddings.

Proof. Put $L=m+2$ and select actual complete half-words

$$
u_i=0^{L-1-i}1\,0^i,\qquad
v_j=0^j1\,0^{L-1-j},\qquad 1\le i,j\le m.
\tag{22.7}
$$

Each starts and ends in zero. Formula (22.3) gives

$$
P(u_iv_j)=\frac{(L-i)(L-j)(i+j)}{2^{2L+1}}.
\tag{22.8}
$$

The corresponding positive coherent submatrix is

$$
2^{-(2L+1)/2}
\operatorname{diag}(\sqrt{L-i})\,
[\sqrt{i+j}]_{i,j=1}^m\,
\operatorname{diag}(\sqrt{L-j}).
\tag{22.9}
$$

All displayed diagonal factors are positive. Invoke the
existing additive-kernel theorem of
[Jain, *Hadamard powers of some positive matrices*,
arXiv:1803.06803v1, Theorem 2.2, equation (2.3)](https://arxiv.org/abs/1803.06803v1).
For two strictly increasing positive coordinate lists,
$[(q_i+p_j)^r]$ is strictly sign regular, hence nonsingular,
when $r\ge0$ avoids $0,\ldots,m-2$.
Here $p_j=j$, $q_i=i$, $r=1/2$ satisfy those hypotheses;
$m=1$ is immediate. Thus (22.9) has rank m and is an
actual minor of the full coefficient matrix. This proves
(22.6) and the exact MPS consequence.

The two-state representation is (22.1). A one-state
nonnegative stochastic edge-emission model has scalar
$M_1\ge0$; the no11 condition forces $M_1^2=0$, hence
$M_1=0$. It cannot give positive probability to the word
one. Therefore no one-state presentation realizes P.
$\square$

A two-state visible first-order no11 Markov chain still
has coherent rank exactly two at every proper cut, by
Proposition 19.3. The SNS is a two-state generating model
with a different predictive structure. Equality of minimal
classical hidden dimensions therefore does not identify
their coherent ranks. This strengthens the fixed-producer
application of §19 without relying on reducibility or a
latent branch kept forever. It remains an application of
existing SNS and entrywise-power results, with no claim of
literature priority, quantum memory advantage, preparation
protocol or harmonic-edge optimality.

## 追加锚（本行以下为增补区）


## 23. The two-state renewal example has bounded entropy and exponential single-cut tails

**Proposition 23.1 (The stationary age controls the coherent Schmidt tail).**
For the same fixed law (22.1), let K be the number of
zeros since the last one at the left endpoint of a cut.
Its stationary age probabilities and tails are

$$
\Pr(K=k)=\frac{k+1}{2^{k+2}},\qquad
\mathbb EK=2,\qquad
\Pr(K\ge r)=\frac{r+2}{2^{r+1}},\quad k,r\ge0.
\tag{23.1}
$$

For every finite length n and proper cut after $\ell$,
the positive coherent cut entropy, in bits, obeys

$$
S(\rho_{n,\ell})\le H(\min(K,\ell))\le H(K)\le4.
\tag{23.2}
$$

If $\sigma_1\ge\sigma_2\ge\cdots$ are its Schmidt
coefficients, then, for every integer $r\ge1$,

$$
\sum_{j>r}\sigma_j^2\le\frac{r+2}{2^{r+1}}.
\tag{23.3}
$$

These bounds concern every window and cut of one stationary
law, with constants independent of both.

Proof. The event $K=k$ is the actual cylinder
$1\,0^k$ ending at the cut. By stationarity and (22.2),

$$
\Pr(K=k)=\lambda M_1M_0^k\mathbf1
=\frac{k+1}{2^{k+2}}.
\tag{23.4}
$$

The zero-tail limit in Lemma 22.2 ensures that K is finite
almost surely. Summing the geometric series and its first
two moments gives (23.1).

Partition the actual left words by trailing zero count k,
using k=$\ell$ for the unique all-zero left word. For a
left word u containing a one and ending in k zeros,
the reset gives $\lambda M_u=c_u\alpha M_0^k$, with
$c_u>0$. Consequently all coefficient-matrix rows in
one group are proportional with positive factors
$\sqrt{c_u}$. Each group can be compressed to a single
normalized left vector. Groups have disjoint computational
supports, so these left vectors are orthonormal. The
all-zero group is already one row.

The diagonal probabilities of the left reduction in this
orthonormal basis are exactly the group masses, namely the
distribution of $K_\ell=\min(K,\ell)$, since summing
squared row coefficients recovers the actual marginal.
Dephasing in this finite orthonormal basis cannot decrease
entropy, giving the first inequality of (23.2).
Deterministic coarse-graining gives $H(K_\ell)\le H(K)$.
Finally

$$
H(K)=\sum_{k\ge0}\frac{k+1}{2^{k+2}}
\bigl(k+2-\log_2(k+1)\bigr)\le\mathbb EK+2=4.
\tag{23.5}
$$

For (23.3), if $\ell\ge r$, retain only the r groups
$k=0,\ldots,r-1$. The resulting coefficient matrix has
rank at most r and discarded squared Frobenius norm
$\Pr(K_\ell\ge r)=\Pr(K\ge r)$.
The best rank-r singular-value truncation has no larger
error, proving the bound. If $\ell<r$, the full matrix
already has at most $\ell+1\le r$ such groups, so the
Schmidt tail is zero. $\square$

Equations (22.6) and (23.3) refer to the same positive
coherent state. Exact rank grows, while a fixed cut's
squared Schmidt tail decays exponentially with retained
rank. This single-cut estimate alone does not identify
one globally accurate MPS with that same fixed bond at
every cut; a simultaneous approximation requires an
additional truncation theorem and its length-dependent
error accounting.

The broader probability/tensor separation is also existing
literature. [Glasser–Sweke–Pancotti–Eisert–Cirac,
*Expressive power of tensor-network factorizations for
probabilistic modeling, with applications from hidden
Markov models to quantum machine learning*,
arXiv:1907.03741v2, §3.1 (HMM correspondence), §4,
Proposition 5 and supplementary
Lemma 13](https://arxiv.org/abs/1907.03741v2) already
construct nonnegative tensor families with nonnegative
TT rank two and unbounded real Born rank, using prime
matrices. Their real Born rank optimizes over sign choices;
the present theorem treats the prescribed positive square
root. Their general family does not by itself supply the
same stationary no11 cylinder law or its boundary factors.
Here those interfaces are (22.3)–(22.9), not a new general
tensor-rank separation theorem.

A classical nonnegative rank bound, a fixed positive-root
rank, a rank minimized over real signs, a rank minimized
over complex phases, mixed-state Schmidt number and a
quantum instrument's memory cost remain different
quantities. None of §§19–23 equates them, or turns an
occupation-law representation into a specified quantum
preparation.

## 追加锚（本行以下为增补区）
