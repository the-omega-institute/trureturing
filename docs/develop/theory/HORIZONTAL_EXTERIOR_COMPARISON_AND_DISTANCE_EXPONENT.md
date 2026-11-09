# Horizontal exterior comparison and the projective-distance exponent

## 1. Exterior coordinates and Hermitian contraction

**Definition 1.1 (coordinate Hilbert structure).** Let $\mathbb K=\mathbb R$ or $\mathbb C$, let $H=\mathbb K^n$, and use the inner product

$$
\langle v,w\rangle=\sum_{i=1}^n\overline{v_i}w_i,
$$

conjugate-linear in the first variable and linear in the second. Complex conjugation is the identity over $\mathbb R$. The induced inner product on $\Lambda^hH$ makes the increasing coordinate wedges $e_S=e_{i_1}\wedge\cdots\wedge e_{i_h}$, $S=\{i_1<\cdots<i_h\}$, orthonormal. Thus $u=\sum_{|S|=h}u_Se_S$ has $\|u\|^2=\sum_{|S|=h}|u_S|^2$. Every subset is counted once; there are no ordered-tuple factorials. For $z\in H$, write $L_z u=z\wedge u$ and $\iota_z=L_z^*$, the Hilbert adjoint. A form is horizontal to $z$ when it lies in $\Lambda^h(z^\perp)$, equivalently when $\iota_z u=0$.

The mathematical source for the general horizontal-form comparison is Haobo Ma and Wenlin Zhang, *Proof of the weighted-minor inequality in MathOverflow 469781*, revision 2, 3 November 2026, sections “Contraction and pair families”, “From families to weights”, and “All exterior degrees and repeated lifts”; adapted with attribution under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The original orthonormal-triple question is by `meler`, [MathOverflow 469781](https://mathoverflow.net/q/469781), with the identical [Mathematics Stack Exchange 4902019](https://math.stackexchange.com/q/4902019). Its orthonormal comparison is already a consequence of Russell Lyons, *Determinantal probability measures*, [doi:10.1007/s10240-003-0016-0](https://doi.org/10.1007/s10240-003-0016-0), Theorem 6.2. Miller and Bistroń give a direct two-sided complex proof for nonnegative weights in [arXiv:2509.14727v1](https://arxiv.org/abs/2509.14727v1), Lemma 10, equation (27); in [v4](https://arxiv.org/abs/2509.14727v4) the locators are Lemma 13, equation (34). These prior results retain their authorship; the arbitrary horizontal forms below need not be decomposable or probability-normalized.

**Lemma 1.2 (unit contraction and recovery in every degree).** If $\|z\|=1$, then $\|\iota_z b\|\le\|b\|$ for every exterior form $b$. If $u\in\Lambda^h(z^\perp)$, then

$$
\iota_z(z\wedge u)=u,\qquad \|z\wedge u\|^2=\|u\|^2.
$$

These statements hold for arbitrary forms, including nondecomposable ones. In increasing coordinates,

$$
(\iota_z b)_S=
\sum_{j\notin S}(-1)^{|\{i\in S:i<j\}|}\overline{z_j}\,b_{S\cup\{j\}}.
$$

Proof. Extend $z$ to an orthonormal basis of $H$. The wedges in this basis give the orthogonal decomposition

$$
\Lambda^{h+1}H=
\bigl(z\wedge\Lambda^h(z^\perp)\bigr)\ \mathbin{\perp}\ \Lambda^{h+1}(z^\perp).
$$

Thus each $b$ is uniquely $z\wedge c+d$ with $c\in\Lambda^h(z^\perp)$ and $d\in\Lambda^{h+1}(z^\perp)$. Wedging by $z$ maps the increasing wedges of the complementary basis isometrically to the wedges containing $z$, up to signs, so $\|b\|^2=\|c\|^2+\|d\|^2$. The adjoint sends $z\wedge c+d$ to $c$, proving the bound and both identities. It also proves the horizontal equivalence in Definition 1.1 by applying the same decomposition to a degree-$h$ form. Finally expand $L_ze_S=\sum_{j\notin S}(-1)^{|\{i\in S:i<j\}|}z_je_{S\cup\{j\}}$ and take its adjoint with the stated inner-product convention. This supplies the conjugate in the coordinate formula; an unconjugated contraction over $\mathbb C$ would not be this adjoint.

## 2. Arbitrary horizontal forms and repeated orthogonal lifts

**Theorem 2.1 (signed two-sided exterior comparison).** Let $1\le k$, $1\le r$, $k+r\le n$, let $z_1,\ldots,z_r\in\mathbb K^n$ be orthonormal, and put

$$
V=\operatorname{span}_{\mathbb K}(z_1,\ldots,z_r)^\perp,
\qquad u\in\Lambda^k V,
\qquad b=z_r\wedge\cdots\wedge z_1\wedge u.
$$

The form $u$ is arbitrary and may be zero or nondecomposable. For every family of real, possibly signed weights $(a_S)_{S\in\binom{[n]}k}$, define

$$
m_T=\min_{\substack{S\subset T\\|S|=k}}a_S,
\qquad M_T=\max_{\substack{S\subset T\\|S|=k}}a_S
\quad (|T|=k+r).
$$

All these minima and maxima are over nonempty finite sets. Then

$$
\sum_{|T|=k+r}m_T|b_T|^2
\ \le\ \sum_{|S|=k}a_S|u_S|^2
\ \le\ \sum_{|T|=k+r}M_T|b_T|^2,
\qquad
\sum_{|T|=k+r}|b_T|^2=\sum_{|S|=k}|u_S|^2.
$$

In particular constant weights, including negative and zero constants, give equality in both comparisons. For nonnegative weights the coefficient $1$ in the upper comparison is sharp.

Proof. First suppose $r=1$ and write $z=z_1$, $b=z\wedge u$. For a family $F\subseteq\binom{[n]}k$, let

$$
N(F)=\{T\in\tbinom{[n]}{k+1}:\exists S\in F,\ S\subset T\}.
$$

Let $P_F$ and $P_{N(F)}$ be the orthogonal coordinate projections in degrees $k$ and $k+1$. The coefficient formula in Lemma 1.2 shows that a coefficient of $\iota_zb$ at $S\in F$ only uses $b_T$ with $S\subset T$. Hence, as an operator identity,

$$
P_F\iota_z=P_F\iota_zP_{N(F)}.
$$

Using recovery and the two contraction bounds gives

$$
\|P_Fu\|=\|P_F\iota_zP_{N(F)}b\|
\le\|\iota_zP_{N(F)}b\|
\le\|P_{N(F)}b\|.
$$

After squaring this is the family comparison

$$
\sum_{S\in F}|u_S|^2\le\sum_{T\in N(F)}|b_T|^2.
$$

No decomposable representation of $u$ was used.

For nonnegative weights, list their distinct positive values as $0<t_1<\cdots<t_q$ and put $t_0=0$, $F_\ell=\{S:a_S\ge t_\ell\}$. Exact finite threshold expansions give

$$
a_S=\sum_{\ell=1}^q(t_\ell-t_{\ell-1})\mathbf1_{S\in F_\ell},
\qquad
\max_{\substack{S\subset T\\|S|=k}}a_S
=\sum_{\ell=1}^q(t_\ell-t_{\ell-1})\mathbf1_{T\in N(F_\ell)}.
$$

Multiply each family comparison by $t_\ell-t_{\ell-1}\ge0$ and sum. This proves the upper bound. If all weights are zero the level sum is empty and both sides vanish.

For arbitrary real weights let $a_*=\min_{|S|=k}a_S$ and apply the nonnegative result to $a'_S=a_S-a_*$. Each target maximum also decreases by $a_*$. Lemma 1.2 gives equal source and target masses, so the two weighted sums each decrease by the same $a_*\|u\|^2$; cancelling this term proves the upper bound with signed weights. Apply that upper bound to $-a_S$, use $\max_{S\subset T}(-a_S)=-\min_{S\subset T}a_S$, and multiply by $-1$ to obtain the lower bound. This proves the full one-lift assertion over both fields.

For $r>1$ put $b_0=u$ and $b_j=z_j\wedge b_{j-1}$ for $1\le j\le r$. For each $j$, all the vectors in $V$ and the earlier $z_i$, $i<j$, lie in $z_j^\perp$. The linear span of their degree-$k+j-1$ wedges therefore contains $b_{j-1}$ and is a subspace of $\Lambda^{k+j-1}(z_j^\perp)$. This verifies horizontality even when $b_{j-1}$ is not a simple wedge. Lemma 1.2 consequently yields $\iota_{z_j}b_j=b_{j-1}$ and $\|b_j\|=\|b_{j-1}\|$ at every step. In particular the total source and final masses are equal.

For the upper weights set $A^{(0)}_S=a_S$ and recursively

$$
A^{(j)}_T=\max_{\substack{Q\subset T\\|Q|=k+j-1}}A^{(j-1)}_Q.
$$

The one-lift upper bound gives

$$
\sum_{|Q|=k+j-1}A^{(j-1)}_Q|(b_{j-1})_Q|^2
\le\sum_{|T|=k+j}A^{(j)}_T|(b_j)_T|^2.
$$

Every $k$-subset $S$ of a $(k+j)$-set $T$ can be extended through a chain of subsets adding one element at each step. Conversely every subset encountered in such a chain remains contained in $T$. Induction therefore identifies $A^{(j)}_T=\max_{S\subset T,|S|=k}a_S$. Chaining the inequalities gives the desired final upper bound. The same recursion with minima gives the lower bound, or it follows by applying the final upper bound to $-a$. This also covers the endpoint $k+r=n$, where there is just one final subset.

For a constant weight $a_S=C\in\mathbb R$, every minimum and maximum is $C$, and all three sums equal $C\|u\|^2$. Sharpness follows from the nonzero example $u=e_1\wedge\cdots\wedge e_k$, $z_j=e_{k+j}$ with constant positive weights: an upper coefficient smaller than $1$ would fail. The zero form separately gives zero throughout. No assertion that all equality cases must have constant weights is needed.

## 3. Parameter bridge to pair and triple minors

**Corollary 3.1 (signed complex pair-minor comparison).** Let $n\ge3$, $x,y,z\in\mathbb K^n$, $\|z\|=1$ and $\langle z,x\rangle=\langle z,y\rangle=0$. No normalization, independence or mutual orthogonality of $x,y$ is required. Set

$$
p_{ij}=x_iy_j-x_jy_i,
\qquad
q_{ijk}=\det\begin{pmatrix}
x_i&x_j&x_k\\y_i&y_j&y_k\\z_i&z_j&z_k
\end{pmatrix}.
$$

For any real symmetric off-diagonal array $a_{ij}=a_{ji}$,

$$
\sum_{i<j<k}\min\{a_{ij},a_{ik},a_{jk}\}|q_{ijk}|^2
\le\sum_{i<j}a_{ij}|p_{ij}|^2
\le\sum_{i<j<k}\max\{a_{ij},a_{ik},a_{jk}\}|q_{ijk}|^2.
$$

Proof. Apply Theorem 2.1 with $k=2,r=1,u=x\wedge y$. Hermitian orthogonality puts $x,y$ in $z^\perp$. The increasing coefficients of $u$ are $p_{ij}$, while $z\wedge x\wedge y=x\wedge y\wedge z$ has increasing coefficients $q_{ijk}$; moving $z$ past two degree-one factors changes no sign. The three two-element subsets of each triple give exactly the displayed extrema. This is the full parameter substitution, including dependent or zero $x,y$.

The original real orthonormal-triple upper bound with strictly positive symmetric entries is already [AlternatingArrayContraction.weighted_minors](../../../D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.lean). Its same-module helpers `recover_minors`, `family_domination`, `energy`, `contraction` and `weighted_minors_all_tuples` already supply the real degree-two recovery, locality, energy and nonnegative-weight comparison with arbitrary perpendicular $x,y$. The general theorem above extends the carrier and signed comparison; the weaker real $x,y$ hypotheses alone are already present in those helpers. This corollary uses the general theorem rather than repeating the existing core array proof. In the orthonormal dimension-three case $|q_{123}|^2=\sum_{i<j}|p_{ij}|^2=1$, recovering the elementary maximum bound already in the posing questions.

## 4. The linked distance and its sharp exponent boundary

**Definition 4.1 (weighted projective separation).** Let $n\ge2$, let $(d_{ij})$ be a finite metric on the index set $[n]$, and let $p>0$. Thus $d_{ii}=0$, $d_{ij}=d_{ji}>0$ for $i\ne j$, and the index distances satisfy their triangle inequalities. For unit representatives $x,y\in\mathbb C^n$ define

$$
D_p([x],[y])=
\left(\sum_{i<j}d_{ij}^{\,p}|x_iy_j-x_jy_i|^2\right)^{1/p}.
$$

Here $[x]$ is the complex line represented by $x$. Multiplication of either unit representative by a unit scalar multiplies each minor by the same unit scalar, so the expression is well-defined on projective space. It is symmetric and nonnegative. Since all off-diagonal weights are positive, it vanishes exactly when all minors vanish, equivalently when $x,y$ are linearly dependent, which for unit representatives is exactly $[x]=[y]$. For example, this equivalence follows by choosing $i$ with $x_i\ne0$ and using each vanishing minor to obtain $y_j=(y_i/x_i)x_j$. The remaining metric axiom is the triangle inequality.

The following exponent obstruction and constant-metric argument retain the prior attribution to Miller–Bistroń, [arXiv:2509.14727v1](https://arxiv.org/abs/2509.14727v1), Remark 4, and the corresponding Remark 4 in [v4](https://arxiv.org/abs/2509.14727v4). They are the boundary argument attached to the exterior comparison, not a new priority claim for that prior observation.

For **every** such finite metric, the triangle inequality fails whenever $0<p<2$. Indeed choose $0<\theta<\pi/4$ and the three unit vectors

$$
x=\cos\theta\,e_1+\sin\theta\,e_2,
\quad y=\cos\theta\,e_1-\sin\theta\,e_2,
\quad z=e_1.
$$

All minors outside the pair $\{1,2\}$ vanish. The remaining absolute minors are $\sin(2\theta)$ for $x,y$ and $\sin\theta$ for each pair with $z$. Thus

$$
D_p([x],[y])=d_{12}\sin^{2/p}(2\theta),
\qquad
D_p([x],[z])+D_p([z],[y])=2d_{12}\sin^{2/p}\theta.
$$

Both $d_{12}$ and $\sin\theta$ are positive, so the triangle inequality for this triple would be equivalent to

$$
(2\cos\theta)^{2/p}\le2,
\quad\text{or equivalently}\quad
\cos\theta\le2^{p/2-1}.
$$

For $p<2$ the right side is strictly less than $1$. Choose $0<\theta<\min\{\pi/4,\arccos(2^{p/2-1})\}$. Then the reverse strict inequality holds. This constructs a violating triple for each $p$ and every metric, using only the positive edge $d_{12}$, in every dimension $n\ge2$.

For a **constant positive off-diagonal metric**, $d_{ij}=c>0$ for $i\ne j$, $D_p$ is a projective distance if and only if $p\ge2$. Necessity is the obstruction just proved. For sufficiency let $P_x=xx^*$ be the rank-one orthogonal projector associated to the unit vector $x$. Expansion gives the Gram identity

$$
\sum_{i<j}|x_iy_j-x_jy_i|^2
=\|x\|^2\|y\|^2-|\langle x,y\rangle|^2
=1-|\langle x,y\rangle|^2.
$$

To see the first equality directly, sum $|x_iy_j-x_jy_i|^2$ over all ordered pairs: the two diagonal products each total $\|x\|^2\|y\|^2$, the cross terms total $2|\langle x,y\rangle|^2$, and division by $2$ removes the ordering multiplicity. Also, by $P_x^2=P_x$, $\operatorname{tr}P_x=1$ and $\operatorname{tr}(P_xP_y)=|\langle x,y\rangle|^2$,

$$
\|P_x-P_y\|_{\mathrm{HS}}^2
=\operatorname{tr}\bigl((P_x-P_y)^*(P_x-P_y)\bigr)
=2(1-|\langle x,y\rangle|^2).
$$

Consequently

$$
D_p([x],[y])
=c\left(\frac{\|P_x-P_y\|_{\mathrm{HS}}}{\sqrt2}\right)^{2/p}.
$$

The map $[x]\mapsto P_x$ is well-defined and injective, so $\delta([x],[y])=\|P_x-P_y\|_{\mathrm{HS}}/\sqrt2$ is a distance: its triangle inequality is that of a norm on matrices. If $p\ge2$, put $\alpha=2/p\in(0,1]$. For $a,b\ge0$, $(a+b)^\alpha\le a^\alpha+b^\alpha$. One proof for $0<\alpha<1$ and $a>0$ is to set $t=b/a$ and differentiate $1+t^\alpha-(1+t)^\alpha$: its derivative $\alpha(t^{\alpha-1}-(1+t)^{\alpha-1})$ is nonnegative for $t>0$, and the function tends to $0$ as $t\downarrow0$. The cases $a=0$ or $\alpha=1$ are immediate. Raising the triangle inequality for $\delta$ to $\alpha$ and then applying this scalar inequality proves the triangle inequality for $c\delta^\alpha=D_p$. Its other distance axioms follow from Definition 4.1. This includes the exact endpoint $p=2$.

For general finite metrics and $p\ge2$, the full projective-distance theorem is imported prior work of Miller and Bistroń, [v1 Theorem 2](https://arxiv.org/abs/2509.14727v1), or [v4 Theorem 1](https://arxiv.org/abs/2509.14727v4). Theorem 2.1 alone does not prove that full triangle inequality. The earlier linked conjecture is Bistroń, Eckstein, Friedland, Miller and Życzkowski, *A new class of distances on complex projective spaces*, [arXiv:2312.02583v1](https://arxiv.org/abs/2312.02583v1), Conjecture 2.1; its published bibliographic record is [doi:10.1016/j.laa.2024.10.017](https://doi.org/10.1016/j.laa.2024.10.017). In the $p=2$ comparison the exterior weights are $a_{ij}=d_{ij}^2$, and the distance uses a square root. The original dimension-three, Euclidean and multiplicative-distance results retain that paper's respective Corollary 4.2 and Theorems 6.4 and 6.8; the multiplicative construction still requires a distance matrix. None of these imported prior results is asserted as a consequence proved merely by the single weighted-minor comparison.

## 追加锚（本行以下为增补区）
