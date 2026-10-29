# Sharp Fiedler–resistance optimization on labelled complete bipartite graphs

## 1. Independent conductances, counting measure and mathematical sources

**Definition 1.1 (The labelled positive domain).** Let $a,b$ be integers with
$4\le a\le b$, and put $n=a+b$ and $d=b-a$. The vertices of the actual
complete bipartite graph $K_{a,b}$ are

$$
A=\{u_1,\ldots,u_a\},\qquad B=\{v_1,\ldots,v_b\}.
$$

Its edges are exactly $\{u_i,v_j\}$, and their conductances vary independently
as $c=(c_{ij})\in(0,\infty)^{ab}$. Write

$$
C=(c_{ij}),\quad r_i=\sum_{j=1}^b c_{ij},\quad
s_j=\sum_{i=1}^a c_{ij},\quad W=\sum_{i,j}c_{ij}.
$$

The ordinary Laplacian, with counting inner product, is

$$
L(c)=\begin{pmatrix}\operatorname{diag}(r_i)&-C\\
-C^{\mathsf T}&\operatorname{diag}(s_j)\end{pmatrix},\qquad
\langle x,y\rangle=\sum_{z\in A\cup B}x_zy_z.
\tag{1.1}
$$

List its eigenvalues with multiplicities as
$0=\lambda_1<\lambda_2\le\cdots\le\lambda_n$. For distinct original
vertices $p,q$, let $h_p=1$, $h_q=0$ and $(Lh)_z=0$ at every other
vertex. Define effective resistance and total resistance by

$$
r(p,q)=\frac1{(Lh)_p},\qquad
R(c)=\sum_{\{p,q\}\subseteq A\cup B,\ p\ne q}r(p,q).
\tag{1.2}
$$

Every unordered original vertex pair occurs once, including nonedges.
No constraint on $W$, permutation symmetry, rank or vertex identification
is imposed on this conductance domain.

**Convention 1.2 (The resistance identity and scale).** The harmonic and
counting conventions in (1.1)–(1.2) are those of Cruz Ortega–Menéndez-Conde,
[*Maximal Algebraic Connectivity for Paths with Fixed Effective Resistance*,
arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1), §§2–4.
The classical identities used as intermediate steps are

$$
r(p,q)=(e_p-e_q)^{\mathsf T}L^+(e_p-e_q),\qquad
R(c)=n\operatorname{tr}L^+=n\sum_{k=2}^n\lambda_k^{-1}.
\tag{1.3}
$$

Here $L^+$ is inverse to $L$ on $\mathbf1^\perp$ and zero on constants.
The primary supplier for (1.3) is Ghosh–Boyd–Saberi,
[*Minimizing Effective Resistance of a Graph*, SIAM Review 50(1), 37–66,
DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf),
§2.4, equation (8), and §2.5, equations (13)–(15): their $G$, $g$ and
$R_{\rm tot}$ are respectively our $L$, $c$ and $R$.

For the connection with (1.2), the energy identity is

$$
x^{\mathsf T}Lx=\sum_{i,j}c_{ij}(x_{u_i}-x_{v_j})^2.
\tag{1.4}
$$

Positive conductances and connectedness give $\ker L=\mathbb R\mathbf1$.
The Dirichlet quadratic form with zero values at $p,q$ is positive definite,
since zero energy would force a constant vector with zero boundary values.
Thus the harmonic extension exists uniquely. If $I=(Lh)_p$, zero row sums
and harmonicity give $Lh=I(e_p-e_q)$ and
$I=h^{\mathsf T}Lh>0$. Applying $L^+$ and taking the $p,q$ coordinate
difference proves the first identity in (1.3). Summing it uses

$$
\sum_{\{p,q\}\subseteq A\cup B,\ p\ne q}
(e_p-e_q)(e_p-e_q)^{\mathsf T}=nI_n-\mathbf1\mathbf1^{\mathsf T},
$$

which proves the second identity. In particular, for every $\gamma>0$,

$$
L(\gamma c)=\gamma L(c),\quad
\lambda_2(L(\gamma c))=\gamma\lambda_2(L(c)),\quad
R(\gamma c)=R(c)/\gamma.
\tag{1.5}
$$

**Convention 1.3 (Suppliers and their precise scopes).** Cruz
Ortega–Menéndez-Conde, §5, equation (3) and its following paragraph, supply
the fixed-total-resistance problem and its equivalent scale-invariant
product formulation; the explicit graph optimizations there concern
$P_3,P_4$. The [path optimizer](FIEDLER_RESISTANCE_PATH_OPTIMIZER.md),
Theorem 2.1 and Corollary 3.1, supplies the whole path family with the
original-pair convention (1.3), including the corrected $P_4$ conductances.
Neither path result is a comparison for $K_{a,b}$.

The [two-hub optimizer](FIEDLER_RESISTANCE_K2M_OPTIMIZER.md), Theorems
2.1 and 3.1, supplies the whole $K_{2,m}$ optimization for $m\ge3$. Its two equality
rays are described by
$c_{1j}=t(1+\varepsilon\sqrt{(m-2)/(m+2)})/2$ and
$c_{2j}=t(1-\varepsilon\sqrt{(m-2)/(m+2)})/2$.
The [three-hub optimizer](FIEDLER_RESISTANCE_K3M_OPTIMIZER.md), Lemma 2.1,
Theorem 2.2 and Theorems 3.1–4.1, supplies the complete $K_{3,m}$ comparison,
labelled equality class and every positive resistance level for $m\ge3$.
Its rows have conductances $t(m-2)/m,t/m,t/m$, with the first displayed
row assigned to a chosen hub label. For $m=3$ all choices give the same
uniform ray; for $m>3$ they give three distinct rays. Its product constant
is $m(m+3)+m^2/(m-2)$.
These whole results apply to their stated numbers of hubs. In particular,
the three-hub theorem is not assumed for arbitrary $a$.
Its proof supplies the one-sided Gram-area calculation, the
three-coordinate diagonal-plus-constant calculation, and the elementary
symmetric-sum comparison used as intermediate steps below.

The [labelled $K_{2,3}$ refutation](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md),
Theorem 1.14, supplies conductances $32/23,16/23$ on the two hub rows,
with $R=23/3$ and $\lambda_2=48/23$; invariant feasible weights have $\lambda_2=2$.
Its underlying harmonic formulas, total-resistance formula and Rayleigh
identities have exactly two hubs and three leaves. They provide the existing
refutation and normalization, rather than the all-family maximum here.

Ghosh–Boyd–Saberi, problem (2), minimizes $R_{\rm tot}$ subject to
$\mathbf1^{\mathsf T}g=1$ and $g\ge0$. Its conductance budget is a
different feasible set from (1.2) at fixed $R$. Rosa–Harman,
[*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1), §§2.3–2.4, use
$\Phi_A=(n-1)/\operatorname{tr}L^+$ and $\Phi_E=\lambda_2$ in the
increasing eigenvalue convention here. Thus
$\lambda_2R=n(n-1)\Phi_E/\Phi_A$; their prescribed-edge-count problem
and linear-allocation relaxation have different constraints.
These classical identities and interpretations are cited intermediates.
The simultaneous two-sided comparison in Lemma 2.1, its strict global
consequence in Theorem 3.1, and the unrestricted labelled classification
in Theorem 4.1 are repo-derived deductions proved below.

## 2. Simultaneous excess from both independent vertex sets

**Lemma 2.1 (A two-sided second-excess bound).** For every conductance
in Definition 1.1, set

$$
t=\lambda_2(L),\quad w=W/t,\quad
P=I_n-\frac1n\mathbf1\mathbf1^{\mathsf T},\quad H=L/t-P.
$$

Then $H$ is positive semidefinite, $H\mathbf1=0$, and

$$
w\ge b,\qquad S:=\operatorname{tr}H=2w-n+1.
\tag{2.1}
$$

The second elementary symmetric sum $E$ of the eigenvalues of this same
matrix satisfies

$$
E\ge K(w):=\frac{a-1}{b}(w-a)+\frac{b-1}{a}(w-b).
\tag{2.2}
$$

If equality holds in (2.2), all normalized $A$-degrees $r_i/t$ are $1$
except possibly one, which is $w-a+1$. All normalized $B$-degrees $s_j/t$
are likewise $1$ except possibly one, which is $w-b+1$.

*Proof.* On $\mathbf1^\perp$, $P$ is identity and the eigenvalues of
$L/t$ are at least $1$; both matrices vanish on constants. Hence $H\succeq0$
and $H\mathbf1=0$. Let $U_B$ be the space supported on $B$ with coordinate
sum zero, and take an orthonormal basis $f_1,\ldots,f_{b-1}$ there.
Its projection on the $B$ coordinates is $I_b-\mathbf1_b\mathbf1_b^{\mathsf T}/b$.
The Rayleigh bound gives

$$
b-1\le\sum_{\ell=1}^{b-1}f_\ell^{\mathsf T}(L/t)f_\ell
=\frac{b-1}{b}\sum_j\frac{s_j}{t}=\frac{b-1}{b}w.
\tag{2.3}
$$

Thus $w\ge b$. No invariance of $U_B$ has been assumed. Taking traces
and using $\operatorname{tr}L=2W$ proves (2.1).

Put $\rho=1/n$, $z_i=r_i/t-1$ and $\eta_j=s_j/t-1$. The two principal
blocks of $H$ are

$$
H_A=\operatorname{diag}(z_i)+\rho\mathbf1_a\mathbf1_a^{\mathsf T},\qquad
H_B=\operatorname{diag}(\eta_j)+\rho\mathbf1_b\mathbf1_b^{\mathsf T}.
\tag{2.4}
$$

In particular $\sum_i z_i=w-a=:Z$ and $\sum_j\eta_j=w-b=:Q$.
Write $e_2(z)=\sum_{i<k}z_i z_k$ and similarly for $\eta$.
Both these quantities are nonnegative. Here is the arbitrary-size
extension of the three-coordinate calculation in the proof of the cited
three-hub Lemma 2.1. If
$D=\operatorname{diag}(x_1,\ldots,x_r)+\rho\mathbf1_r\mathbf1_r^{\mathsf T}
\succeq0$ with $r\ge3$, testing $e_i-e_j$ shows that at most one $x_i$
can be negative. If one is negative, every other $x_j$ is strictly
positive. On a triple containing the negative entry,

$$
0\le\det D_{\{i,j,k\}}
=x_i x_j x_k+\rho(x_i x_j+x_i x_k+x_j x_k)
$$

forces the parenthesized expression to be strictly positive. On every
other triple it is nonnegative. Summing over triples gives

$$
(r-2)\sum_{i<j}x_i x_j
=\sum_{i<j<k}(x_i x_j+x_i x_k+x_j x_k)>0
$$

if a negative entry occurs. If all entries are nonnegative, their pair
sum is nonnegative and vanishes precisely when at most one is positive.
Consequently

$$
e_2(z)\ge0,\quad e_2(\eta)\ge0,
\tag{2.5}
$$

and equality for either list means all its entries are nonnegative with
at most one nonzero entry. This argument applies since both $a,b\ge4$.

Choose Gram vectors $v_i,y_j\in\mathbb R^n$ for $H$, for example its
positive semidefinite square-root columns. Then

$$
\begin{gathered}
\langle v_i,v_k\rangle=\rho\quad(i\ne k),\qquad
\|v_i\|^2=z_i+\rho,\\
\langle y_j,y_\ell\rangle=\rho\quad(j\ne\ell),\qquad
\|y_j\|^2=\eta_j+\rho,\qquad
\sum_i v_i+\sum_j y_j=0.
\end{gathered}
\tag{2.6}
$$

The last equality follows by taking the squared norm and using
$\mathbf1^{\mathsf T}H\mathbf1=0$.
For vectors $u,v$, use the exterior product with coordinates
$(u\wedge v)_{pq}=u_pv_q-u_qv_p$ for $p<q$; expansion gives
$\|u\wedge v\|^2=\|u\|^2\|v\|^2-\langle u,v\rangle^2$.
Thus squared Gram areas are second-order principal minors, and their sum
is $E=((\operatorname{tr}H)^2-\operatorname{tr}(H^2))/2$.
Split this sum as

$$
E=E_A+E_B+E_C,\quad
E_A=\sum_{i<k}\|v_i\wedge v_k\|^2,\quad
E_B=\sum_{j<\ell}\|y_j\wedge y_\ell\|^2,\quad
E_C=\sum_{i,j}\|v_i\wedge y_j\|^2.
$$

The block formulas (2.4) give

$$
E_A=e_2(z)+(a-1)\rho Z,\qquad
E_B=e_2(\eta)+(b-1)\rho Q.
\tag{2.7}
$$

To retain the contributions from both sides simultaneously, put
$V=\sum_i v_i=-\sum_j y_j$ and define centered vectors
$\widetilde v_i=v_i-V/a$, $\widetilde y_j=y_j+V/b$.
Their respective sums vanish. Bilinearity gives

$$
v_i\wedge y_j
=\frac1a V\wedge\widetilde y_j
 +\frac1b V\wedge\widetilde v_i
 +\widetilde v_i\wedge\widetilde y_j.
$$

When squared and summed over $i,j$, every mixed inner product vanishes:
for the first two terms use the two zero sums, for the first and third
sum over $i$, and for the second and third sum over $j$. Since
$V\wedge\widetilde v_i=V\wedge v_i$ and
$V\wedge\widetilde y_j=V\wedge y_j$, the exact identity is

$$
E_C=\frac1b\sum_i\|v_i\wedge V\|^2
    +\frac1a\sum_j\|y_j\wedge V\|^2
    +T,\qquad
T=\sum_{i,j}\|\widetilde v_i\wedge\widetilde y_j\|^2\ge0.
\tag{2.8}
$$

For explicit evaluation, write $h_i=\|v_i\|^2$ and
$D_A=\sum_i h_i=Z+a\rho$. Equations (2.6) imply
$\|V\|^2=D_A+a(a-1)\rho$ and
$\langle v_i,V\rangle=h_i+(a-1)\rho$. Therefore

$$
\begin{aligned}
\sum_i\|v_i\wedge V\|^2
&=D_A(D_A+a(a-1)\rho)-\sum_i(h_i+(a-1)\rho)^2\\
&=2E_A+(a-1)(a-2)\rho Z.
\end{aligned}
\tag{2.9}
$$

Indeed $2E_A=D_A^2-\sum_i h_i^2-a(a-1)\rho^2$, so the final equality
follows by substitution. Replacing $a,v_i,Z,V$ by
$b,y_j,Q,-V$ gives, on the same Gram representation,

$$
\sum_j\|y_j\wedge V\|^2=2E_B+(b-1)(b-2)\rho Q.
\tag{2.10}
$$

Combining (2.7)–(2.10), and using $\rho(a+b)=1$, yields the exact
nonnegative-gap decomposition

$$
\begin{aligned}
E-K(w)
&=\left(1+\frac2b\right)e_2(z)
 +\left(1+\frac2a\right)e_2(\eta)+T\ge0.
\end{aligned}
\tag{2.11}
$$

For example, the coefficient of $Z$ before simplification is
$(a-1)\rho[1+2/b+(a-2)/b]=(a-1)/b$;
the coefficient of $Q$ is $(b-1)/a$.
This proves (2.2) without optimizing different matrices separately.
If equality holds, both pair sums in (2.11) vanish. Their equality
characterization following (2.5), together with their sums $Z=w-a$ and
$Q=w-b$, proves the stated degree concentration. ∎

## 3. Strict comparison on the unrestricted positive domain

**Theorem 3.1 (The global product bound).** For $4\le a\le b$, define

$$
M_{a,b}=n(n-3)+\frac{b(d+3)}{d+1},\qquad
F(w)=\frac{S(w)+2K(w)}{1+S(w)+K(w)},\quad S(w)=2w-n+1,
\tag{3.1}
$$

where $K$ is (2.2). Every conductance in Definition 1.1 satisfies

$$
\frac{\lambda_2(L)R(c)}n\le n-1-F(w)\le\frac{M_{a,b}}n,
\qquad w=W/\lambda_2(L)\ge b.
\tag{3.2}
$$

The second inequality is strict if $w>b$. If $\lambda_2R=M_{a,b}$,
then $w=b$, $E=K(b)=(a-1)d/b$, and $\operatorname{rank}H\le2$;
in particular the $A$-degrees have the concentration specified in Lemma 2.1.

*Proof.* Put $q_k=\lambda_k/t-1\ge0$ for $2\le k\le n$.
Together with the zero eigenvalue on constants these are the eigenvalues
of $H$. Let $e_j$ be their elementary symmetric sums, with $e_0=1$.
Then $e_1=S$, $e_2=E$, and every $e_j\ge0$.
The elementary symmetric-sum identity used in the three-hub Theorem 2.2,
proved by differentiating $\prod_k(1+xq_k)$ at $x=1$, is

$$
\sum_{k=2}^n\frac{q_k}{1+q_k}
=\frac{\sum_{j=1}^{n-1}j e_j}{\sum_{j=0}^{n-1}e_j}
\ge\frac{S+2E}{1+S+E}.
\tag{3.3}
$$

For completeness the final ratio is strictly less than $2$, since
$2(1+S+E)-(S+2E)=2+S>0$. Every omitted denominator term $e_j$,
$j\ge3$, has numerator coefficient $j>2$, so adding them cannot decrease
the ratio. Equality is equivalent to all $e_j=0$ for $j\ge3$, or,
since the $q_k$ are nonnegative, to at most two positive $q_k$.
This is an equality consequence, not a rank restriction on competitors.

For fixed $S\ge0$, the derivative of $(S+2E)/(1+S+E)$ with respect to
$E$ is $(S+2)/(1+S+E)^2>0$. Lemma 2.1 therefore gives

$$
\sum_{k=2}^n\frac{q_k}{1+q_k}\ge F(w).
\tag{3.4}
$$

By (1.3), $tR/n=n-1-\sum_k q_k/(1+q_k)$, proving the first
inequality in (3.2).

It remains to compare every allowed $w$ on this same conductance domain.
For $w\ge b$, both $S(w)\ge d+1$ and $K(w)\ge0$, so all displayed
denominators are positive. Put

$$
h=\frac{a-1}{b}+\frac{b-1}{a},\qquad
k=\frac{a(a-1)}b+\frac{b(b-1)}a,
\qquad K(w)=hw-k.
$$

Direct differentiation gives

$$
\begin{aligned}
F'(w)
&=\frac{2+(3-n)h+2k}{(1+S(w)+K(w))^2}\\
&=\frac{n(d^2+2n-3)}{ab(1+S(w)+K(w))^2}>0.
\end{aligned}
\tag{3.5}
$$

To verify the simplification, multiplying the numerator by $ab$ gives
$2ab+a(a-1)(3-d)+b(b-1)(3+d)$;
using $b-a=d$ reduces this to $n(d^2+2n-3)$.
Thus $F(w)\ge F(b)$, strictly if $w>b$. At $w=b$,

$$
S(b)=d+1,\qquad K(b)=\frac{(a-1)d}{b},\qquad
1+S(b)+K(b)=\frac{n(d+1)}b.
$$

Using $(S+2K)/(1+S+K)=2-(S+2)/(1+S+K)$ now gives

$$
n-1-F(b)=n-3+\frac{b(d+3)}{n(d+1)}=\frac{M_{a,b}}n.
\tag{3.6}
$$

This proves the second inequality in (3.2) with its strictness.
If the product equals $M_{a,b}$, equality throughout first forces $w=b$,
then $E=K(b)$ by the strictly increasing dependence on $E$ in (3.4),
and finally $\operatorname{rank}H\le2$ by (3.3). Lemma 2.1 then
supplies the degree equality implications. ∎

## 4. All labelled equality rays and every resistance level

**Theorem 4.1 (Sharp attainment and complete equality necessity).** For
every integer pair $4\le a\le b$,

$$
\max_{c\in(0,\infty)^{ab}}\lambda_2(L(c))R(c)=M_{a,b}.
\tag{4.1}
$$

If $a<b$, equality holds exactly as follows: choose a labelled vertex
$u_{i_*}\in A$ and a real number $\tau>0$, and assign

$$
c_{i_*j}=\frac{\tau(d+1)}b\quad(1\le j\le b),\qquad
c_{ij}=\frac\tau b\quad(i\ne i_*,\ 1\le j\le b).
\tag{4.2}
$$

These are precisely $a$ distinct rays in labelled edge-conductance space.
Each has $\lambda_2=\tau$ and $R=M_{a,b}/\tau$.
If $a=b=k$, the equality class is the unique uniform ray
$c_{ij}=\tau/k$, $\tau>0$, and

$$
M_{k,k}=k(4k-3),\qquad \lambda_2=\tau,\qquad R=k(4k-3)/\tau.
\tag{4.3}
$$

*Proof.* The upper bound is Theorem 3.1. Suppose equality holds for any
of the independent positive assignments, and set $t=\lambda_2(L)$.
That theorem forces $w=b$ and equality in Lemma 2.1. By the degree
condition there, the $A$-degrees are $t$ except possibly one degree
$(b-a+1)t=(d+1)t$. For $d=0$ they are all $t$.

Equality $w=b$ in (2.3) makes
$\sum_{\ell=1}^{b-1}f_\ell^{\mathsf T}Hf_\ell=0$.
Each summand is nonnegative. For a positive semidefinite symmetric
matrix, zero quadratic form implies a kernel vector by orthogonal
spectral decomposition. Consequently $H$ annihilates $U_B$, and
$Lx=tx$ for all $x\in U_B$. In particular, for any $j\ne\ell$, apply
this to $e_{v_j}-e_{v_\ell}$. Its $A$ coordinates and its two nonzero
$B$ coordinates give respectively

$$
c_{ij}=c_{i\ell}\quad\text{for every }i,\qquad s_j=s_\ell=t.
\tag{4.4}
$$

Thus every one of the $a$ rows is constant over all $b$ original leaves.
Dividing the already determined row degrees by $b$ proves (4.2) with
$\tau=t$. This derives the required symmetry from the unrestricted
equality conditions. For $d>0$ the degree $(d+1)t$ occurs in exactly
one row, so it also determines the actual label $i_*$.
For $d=0$ every row has degree $t$, hence every edge is $t/k$.

To prove sufficiency and the claimed spectral scale, use (1.5) to set
$\tau=1$ and put $q=d+1\ge1$. Choose $u_{i_*}$ as the first basis
vector only for the calculation. The $B$-difference space has eigenvalue
$1$ and dimension $b-1$, since each column sum in (4.2) is
$(q+a-1)/b=1$. Differences of the remaining $a-1$ hub coordinates,
supported on those hubs and with sum zero, have eigenvalue $1$ and
dimension $a-2$. These two spaces are orthogonal, invariant subspaces
of the original counting-measure Laplacian.

Their orthogonal complement has the orthonormal basis

$$
e_{u_{i_*}},\qquad
\frac1{\sqrt{a-1}}\sum_{i\ne i_*}e_{u_i},\qquad
\frac1{\sqrt b}\sum_{j=1}^b e_{v_j}.
$$

In this basis the restriction of the same $n\times n$ matrix is

$$
T_{a,b}=\begin{pmatrix}
q&0&-q/\sqrt b\\
0&1&-\sqrt{(a-1)/b}\\
-q/\sqrt b&-\sqrt{(a-1)/b}&1
\end{pmatrix}.
\tag{4.5}
$$

The square-root factors come from the counting inner product. No vertices
or pair terms in $R$ have been removed. The constant vector is represented
by $(1,\sqrt{a-1},\sqrt b)^{\mathsf T}$ and is in its kernel.
Its two other eigenvalues $\alpha\le\beta$ are strictly positive by
(1.4), and their sum and product are

$$
\begin{gathered}
\alpha+\beta=q+2=d+3,\\
\alpha\beta=q+\left(q-\frac{q^2}b\right)
 +\left(1-\frac{a-1}b\right)
 =\frac{n(d+1)}b.
\end{gathered}
\tag{4.6}
$$

The product is the sum of the three second-order principal minors of
(4.5); the final equality follows from $q=b-a+1$. The quadratic with
roots $\alpha,\beta$ satisfies

$$
(1-\alpha)(1-\beta)
=1-(d+3)+\frac{n(d+1)}b=\frac{(a-1)d}{b}\ge0.
\tag{4.7}
$$

Both roots are real since (4.5) is symmetric. They cannot both be at
most $1$, since their sum is $d+3\ge3$. Hence (4.7) implies
$1\le\alpha\le\beta$, strictly $1<\alpha$ if $d>0$.
When $d=0$, (4.6) gives precisely $\alpha=1$, $\beta=2$.
The full spectrum, with multiplicities retained, is therefore

$$
0,\qquad 1\ \text{($n-3$ times)},\qquad\alpha,\beta.
\tag{4.8}
$$

In particular $\lambda_2=1$ and (1.3), (4.6) give

$$
R=n\left(n-3+\frac1\alpha+\frac1\beta\right)
=n(n-3)+\frac{b(d+3)}{d+1}=M_{a,b}.
$$

All conductances in (4.2) are finite and strictly positive. Scaling back
by $\tau$ proves their asserted values and attainment. It also shows
that equality has $\operatorname{rank}H=2$ if $d>0$, and rank $1$ if
$d=0$, as a consequence of the computed spectrum.

For $d>0$, two choices of $i_*$ give different assignments at
$\lambda_2=1$, because the unique row of degree $d+1>1$ changes its
label. Scalar-proportional assignments must have the same normalization
$\lambda_2=1$, so these are distinct rays, exactly $a$ in number.
For $d=0$ the choice of row has no effect and gives one uniform ray.
Finally substitution $n=2k,d=0$ into (4.1) gives
$2k(2k-3)+3k=k(4k-3)$, proving (4.3). ∎

**Corollary 4.2 (Every positive resistance level and every optimizer).**
For every integer pair $4\le a\le b$ and every real $R_0>0$, the level set

$$
\mathcal F_{a,b,R_0}
=\{c\in(0,\infty)^{ab}:R(c)=R_0\}
$$

is nonempty and has the finite attained optimum

$$
\max_{c\in\mathcal F_{a,b,R_0}}\lambda_2(L(c))=\frac{M_{a,b}}{R_0}.
\tag{4.9}
$$

Its labelled optimizers are exactly (4.2) with
$\tau=M_{a,b}/R_0$. There are exactly $a$ such assignments when $a<b$.
For $a=b=k$ there is exactly one, with every edge conductance
$(4k-3)/R_0$.

*Proof.* Theorem 4.1 bounds $\lambda_2R_0$ by $M_{a,b}$ at every
feasible point. Take $\tau=M_{a,b}/R_0>0$ in its equality assignment.
All edges have finite strictly positive conductance, and that theorem
gives $R=M_{a,b}/\tau=R_0$ and $\lambda_2=\tau$. This proves both
nonemptiness and attained finiteness inside the stated domain.
Any optimizer must attain product equality, so Theorem 4.1 gives its
labelled ray; the identity $R=M_{a,b}/\tau$ fixes the scale uniquely.
In the balanced case $\tau/k=k(4k-3)/(kR_0)=(4k-3)/R_0$.
The label counts follow from the distinct-ray classification. ∎

## 追加锚（本行以下为增补区）
