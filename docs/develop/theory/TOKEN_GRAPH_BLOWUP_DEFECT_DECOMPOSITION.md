# Token-graph blow-ups and a full-state defect certificate

## 1. Graphs, Boolean states and defects

**定义 1.1（Uniform independent blow-up and token adjacency）。** Let $H$ be a finite simple graph on $[m]=\{1,\ldots,m\}$, where $m\geq2$, and suppose that $H$ has an edge. Every edge has weight one. Write

$$
a=A(H),\qquad \lambda=\lambda_{\min}(a)<0.
\tag{1.1}
$$

For an integer $s\geq1$, let $B_i=\{i\}\times[s]$, $\Omega=\bigsqcup_i B_i$ and $N=ms$. The graph $G_s=H[\overline{K_s}]$, also written $H[\mathrm{empty}_s]$, has vertex set $\Omega$; two vertices are adjacent exactly when their block indices are adjacent in $H$. Thus there are no edges inside a block. For every integer $0\leq k\leq N$, let $\mathcal H_k$ have the orthonormal basis $\{|S\rangle:S\subseteq\Omega,\ |S|=k\}$. The ordinary token adjacency $K_k$ has matrix entry one between $S,T$ exactly when $S\setminus T=\{u\}$, $T\setminus S=\{v\}$ and $\{u,v\}\in E(G_s)$, and has all other entries zero. Define

$$
E(s,k)=\lambda_{\min}(K_k)
=\min_{0\ne w\in\mathcal H_k}
\frac{\langle w,K_kw\rangle}{\langle w,w\rangle}.
\tag{1.2}
$$

Inner products are conjugate-linear in the first variable. All vectors may have arbitrary complex coordinates. The endpoint spaces $\mathcal H_0,\mathcal H_N$ each have dimension one, with zero adjacency.

These are the token-graph conventions of Apte–Parekh–Sud, [*Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*, v2, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v2), and of the supplied [token-graph definition](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean). Here $K_k$ is adjacency itself; the shifted XY block $W(G_s)I/2-K_k$ in Fact 2 is a different operator.

**定义 1.2（Boolean lowering and block symmetrization）。** On $\mathcal B=\bigoplus_{q=0}^N\mathcal H_q$, set

$$
\begin{aligned}
\sigma^-_u|S\rangle&=
\begin{cases}|S\setminus\{u\}\rangle,&u\in S,\\0,&u\notin S,\end{cases}
&\sigma^+_u&=(\sigma^-_u)^*,\\
n_u|S\rangle&=\mathbf1_{u\in S}|S\rangle,
&L_i&=\sum_{u\in B_i}\sigma^-_u,
&n_i&=\sum_{u\in B_i}n_u.
\end{aligned}
\tag{1.3}
$$

Let $\tau_{uv}$ interchange the two Boolean coordinates $u,v$ in the same block. Let $P_i$ be the orthogonal projection onto the vectors invariant under all permutations of $B_i$, and put $P_{\mathrm{sym}}=\prod_iP_i$. These projections preserve total occupancy. At a fixed block occupancy $q$, $P_i$ projects onto the constant vector on the $q$-subsets of that block, with the other coordinates left intact. No invariance under $P_i$ is imposed on an input state.

The lowering algebra and its symmetric Dicke vectors are classical intermediates: see Feinsilver, [*Representations of sl(2) in the Boolean lattice, and the Hamming and Johnson schemes*, §§2–4, Proposition 4.1](https://arxiv.org/pdf/1102.0368v2), and Srinivasan, [*Symmetric chains, Gelfand–Tsetlin chains, and the Terwilliger algebra of the binary Hamming scheme*, Theorem 1.2](https://arxiv.org/pdf/1001.0280v2). The supplied [collective-oscillator theory, Definitions 1.1–1.2 and Theorem 2.1](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md), uses the same lowering algebra on a chosen two-state tensor code and its symmetric subspace. The space $\mathcal H_k$ here includes every Boolean state at occupancy $k$.

**定义 1.3（Particle–hole convention）。** Fix $0\leq k\leq N$ and a unit vector $\varphi\in\mathcal H_k$. Set

$$
r=\min(k,N-k),\qquad b=\frac{k(N-k)}m=\frac{r(N-r)}m.
\tag{1.4}
$$

The complement unitary is $C|S\rangle=|\Omega\setminus S\rangle$. Use $\psi=\varphi$ when $k\leq N/2$, and $\psi=C\varphi$ otherwise. Thus $\psi\in\mathcal H_r$. Write $Q=\langle\varphi,K_k\varphi\rangle$. For an operator $X$ on $\mathcal H_r$, write $\langle X\rangle_\psi=\langle\psi,X\psi\rangle$. Define

$$
\begin{aligned}
F&=\sum_{i=1}^m e_i\otimes L_i\psi
\in\mathbb C^m\otimes\mathcal H_{r-1},\\
V&=\sum_{i=1}^m\left(n_i-\frac rm I\right)^2,\\
D_i&=n_i(sI-n_i+I)-L_i^*L_i,\qquad
T_\psi=\left\langle V+\sum_iD_i\right\rangle_\psi.
\end{aligned}
\tag{1.5}
$$

For $r=0$, the target $\mathcal H_{-1}$ means the zero Hilbert space, and $F=0$. Identity operators in polynomials in $n_i$ will also be suppressed. All defects refer to this same state $\psi$.

## 2. The full-state certificate

**定理 2.1（Spectral, occupancy and Johnson defect identity）。** For every $H,s,k,\varphi$ of Definitions 1.1–1.3,

$$
\boxed{
Q-\lambda(b+r)
=\left\langle F,\bigl((a-\lambda I)\otimes I\bigr)F\right\rangle
+|\lambda|\left\langle V+\sum_iD_i\right\rangle_\psi .
}
\tag{2.1}
$$

Every term on the right is nonnegative. More precisely,

$$
(a-\lambda I)\otimes I\succeq0,\qquad
\left(n_i-\frac rm I\right)^2\succeq0,\qquad
D_i=\sum_{\{u,v\}\subseteq B_i}(I-\tau_{uv})
\succeq s(I-P_i)\succeq0.
\tag{2.2}
$$

The statements hold on the complete Boolean space at occupancy $r$, including nonsymmetric states. In particular, without any flat-eigenvector hypothesis,

$$
E(s,k)\geq\lambda(b+r).
\tag{2.3}
$$

Proof. The finite real symmetric spectral theorem supplies (1.1): if $\{i,j\}$ is an edge, the vector $e_i-e_j$ has quadratic form $-2$ and squared norm $2$, so $\lambda\leq-1$. Complementing both token configurations preserves their adjacency, hence $CK_kC^*=K_{N-k}$ and $Q=\langle\psi,K_r\psi\rangle$.

Expand the lowering operators on a basis vector $|S\rangle$. For $i\ne j$, each term in $L_i^*L_j$ removes one occupied vertex from $B_j$ and adds one unoccupied vertex in $B_i$, with coefficient one. The removed and added vertices are determined by the resulting pair of configurations. Since $a_{ii}=0$, this gives, with no diagonal shift or factor of two,

$$
K_r=\sum_{i,j}a_{ij}L_i^*L_j,\qquad
Q=\sum_{i,j}a_{ij}\langle L_i\psi,L_j\psi\rangle
=\langle F,(a\otimes I)F\rangle.
\tag{2.4}
$$

To identify each $D_i$, fix the occupied set $R$ outside $B_i$ and let $q=r-|R|$. On the resulting $q$-subset space inside $B_i$, removing and replacing the same vertex gives $q$ diagonal contributions; removing and replacing distinct vertices gives the adjacency of the Johnson graph $J(s,q)$. Consequently

$$
L_i^*L_i=qI+A(J(s,q)),\qquad
D_i=q(s-q)I-A(J(s,q))=L(J(s,q)).
\tag{2.5}
$$

Each $q$-subset has $q(s-q)$ Johnson neighbors. If $c_S$ are the coordinates of $\psi$ on $\mathcal H_r$, the exact quadratic form is

$$
\langle D_i\rangle_\psi
=\sum_{R\subseteq\Omega\setminus B_i}
\ \sum_{\{S,T\}\in E(J(s,r-|R|))}
|c_{R\cup S}-c_{R\cup T}|^2\geq0,
\tag{2.6}
$$

where summands with $r-|R|\notin[0,s]$ are omitted. The cases $q=0,s$ have no Johnson edges. Equivalently, each transposition contributes $I-\tau_{uv}$, proving the equality in (2.2). Since $\tau_{uv}$ is a self-adjoint involution, its contribution has quadratic form $\tfrac12\|(I-\tau_{uv})\psi\|^2$. Thus its kernel consists precisely of invariant vectors; taking all transpositions gives $\ker D_i=\operatorname{ran}P_i$.

For completeness the spectral inequality $D_i\succeq s(I-P_i)$ can be obtained directly from the classical Johnson calculation. On functions of the $q$-subsets, first take $q\leq s/2$ and let $f_U(S)=\mathbf1_{U\subseteq S}$ for $|U|=t\leq q$. Let $\mathcal U_t$ be their span and $\mathcal U_{-1}=0$. The relation

$$
\sum_{\substack{U\supset R\\|U|=t}}f_U=(q-t+1)f_R
\qquad(|R|=t-1)
$$

shows $\mathcal U_{t-1}\subseteq\mathcal U_t$, and $\mathcal U_q$ is the whole function space. Counting neighbors according to $|U\setminus S|$ gives

$$
L(J(s,q))f_U
=t(s+1-t)f_U-(q-t+1)\sum_{u\in U}f_{U\setminus\{u\}}.
\tag{2.7}
$$

Indeed, for $U\subseteq S$ the adjacency count is $(q-t)(s-q)$, for $|U\setminus S|=1$ it is $q-t+1$, and for larger differences it is zero. On $\mathcal U_t/\mathcal U_{t-1}$, (2.7) is the scalar $t(s+1-t)$. Self-adjointness makes $\mathcal U_t\cap\mathcal U_{t-1}^{\perp}$ invariant, so it has this same scalar action. These mutually orthogonal spaces exhaust the layer. The $t=0$ space consists of constants, and for $1\leq t\leq q$,

$$
t(s+1-t)-s=(t-1)(s-t)\geq0.
$$

For $q>s/2$ use the graph isomorphism $S\mapsto B_i\setminus S$ to the $(s-q)$-layer. This proves the claimed inequality on every layer, including the zero-dimensional nonconstant part at $q=0,s$ or $s=1$. Formula (2.5) is Feinsilver's Proposition 4.1 with $T=L_i^*$ and $T^*=L_i$; the Johnson eigenvalues used in this calculation are also recorded in Apte–Parekh–Sud v2, Appendix A.3, Lemma 15. These are attributed intermediate identities, not separate new spectral assertions.

On $\mathcal H_r$ one has $\sum_i n_i=rI$. Expanding the squares in $V$ therefore gives $\sum_i n_i^2=V+(r^2/m)I$. Using the definition of $D_i$ now yields the exact norm accounting

$$
\begin{aligned}
\|F\|^2
&=\left\langle\sum_iL_i^*L_i\right\rangle_\psi\\
&=(s+1)r-\left\langle\sum_i n_i^2\right\rangle_\psi
-\left\langle\sum_iD_i\right\rangle_\psi\\
&=b+r-T_\psi.
\end{aligned}
\tag{2.8}
$$

The unit normalization is used in the scalar terms in this equality. For an orthonormal eigenbasis $u_\alpha$ of $a$, write $F=\sum_\alpha u_\alpha\otimes f_\alpha$. If $a u_\alpha=\theta_\alpha u_\alpha$, then

$$
\left\langle F,\bigl((a-\lambda I)\otimes I\bigr)F\right\rangle
=\sum_\alpha(\theta_\alpha-\lambda)\|f_\alpha\|^2\geq0.
\tag{2.9}
$$

This is an aggregate quadratic-form statement on all tuple components, without componentwise sign assumptions. Combining (2.4) and (2.8), and using $-\lambda=|\lambda|$, proves (2.1). Each occupancy square is positive because $n_i$ is self-adjoint; (2.6) proves the individual Johnson positivity. Minimizing over unit vectors proves (2.3). If $r=0$, $Q=b=V=D_i=0$ on the vacuum, so the same argument and identity include both endpoint sectors.

The spectral quadratic-form method is a classical intermediate also present in Schmidt–Schnack–Luban, [*Bounding and approximating parabolas for the spectrum of Heisenberg spin systems*, Theorem 1](https://arxiv.org/pdf/cond-mat/0101228v1), DOI [10.1209/epl/i2001-00388-9](https://doi.org/10.1209/epl/i2001-00388-9), and Bärwinkel–Schmidt–Schnack, [*Improved upper and lower energy bounds for antiferromagnetic Heisenberg spin systems*, §3](https://arxiv.org/pdf/cond-mat/0210458v2), DOI [10.1140/epjb/e2003-00168-5](https://doi.org/10.1140/epjb/e2003-00168-5). The former's displayed bounds concern isotropic coupling, constant row sums and total spin; the latter's lower bounds add homogeneity assumptions. Here the inference is the particular identity (2.1), with the occupancy and Johnson defects retained on the full Boolean carrier, and its joint consequences below. No constant-row-sum or fixed local-spin irreducibility assumption enters (2.4)–(2.9). $\square$

## 3. A flat least mode and every density

**假设 3.1（Flat complex least mode）。** In addition to Definition 1.1, suppose there is a vector $z\in\mathbb C^m$ satisfying

$$
az=\lambda z,\qquad |z_i|=1\quad(1\leq i\leq m).
\tag{3.1}
$$

This is a separate hypothesis on $H$. Its normalization is $\|z\|^2=m$. In particular it is stronger than the mere existence of a least eigenvector.

**定理 3.2（Uniform density estimate from the certificate）。** Under Assumption 3.1, simultaneously for every integer $s\geq1$ and every $0\leq k\leq N=ms$,

$$
\lambda(b+r)\leq E(s,k)\leq\lambda b\frac N{N-1}.
\tag{3.2}
$$

Writing $\rho=k/N$, one has the uniform finite-scale estimate

$$
0\leq\lambda m\rho(1-\rho)-\frac{E(s,k)}{s^2}
\leq\frac{|\lambda|r}{s^2}
\leq\frac{|\lambda|m}{2s}.
\tag{3.3}
$$

For every sequence of integers $0\leq k_s\leq ms$ such that $k_s/(ms)\to\rho\in[0,1]$,

$$
\lim_{s\to\infty}\frac{E(s,k_s)}{s^2}
=\lambda m\rho(1-\rho).
\tag{3.4}
$$

Proof. The lower bound is Theorem 2.1. For the upper bound use the phase-product trial, an attributed intermediate: the same subset-counting mechanism is supplied by `counting_identity`, `W_move` and `phi40_energy` in [CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean). Phase-twisted fixed-magnetization trials also occur in Bärwinkel–Schmidt–Schnack, §§2.2–2.3, Eqs. (14)–(21), for their cyclic coupling assumptions. Here the required count for arbitrary $H$ satisfying (3.1) is as follows.

For $u\in B_i$ put $\zeta_u=z_i$, and for a $k$-subset set

$$
w(S)=\prod_{u\in S}\zeta_u,\qquad
\Phi(S)=\binom Nk^{-1/2}w(S).
\tag{3.5}
$$

The modulus-one condition gives

$$
\langle w,w\rangle=\binom Nk>0,\qquad\|\Phi\|=1.
\tag{3.6}
$$

If $u\in S$, $v\notin S$ and $T=S\setminus\{u\}\cup\{v\}$, then $\overline{w(S)}w(T)=\overline{\zeta_u}\zeta_v$. For any ordered distinct $u,v$, precisely $\binom{N-2}{k-1}$ of the $k$-subsets contain $u$ and omit $v$. Thus for $1\leq k\leq N-1$,

$$
\begin{aligned}
\langle\Phi,K_k\Phi\rangle
&=\frac{\binom{N-2}{k-1}}{\binom Nk}
\sum_{u,v\in\Omega} A(G_s)_{uv}\overline{\zeta_u}\zeta_v\\
&=\frac{k(N-k)}{N(N-1)}\,s^2 z^*az\\
&=\frac{k(N-k)}{N(N-1)}\,s^2\lambda m
=\lambda b\frac N{N-1}.
\end{aligned}
\tag{3.7}
$$

Both orientations are included in the sum over $u,v$, just as in adjacency's quadratic form. For a real symmetric matrix $K$ and $w=x+iy\ne0$, symmetry cancels the imaginary cross terms and gives

$$
w^*Kw=x^{\mathsf T}Kx+y^{\mathsf T}Ky,\qquad
w^*w=\|x\|^2+\|y\|^2>0.
$$

Each real quadratic form is at least $\lambda_{\min}(K)$ times its squared norm, so the complex quotient is subject to the same Rayleigh minimum. A real least eigenvector attains that minimum. This proves the upper bound with its complex normalization. At $k=0,N$, both sides of the upper bound are zero; no binomial coefficient with lower index $-1$ is used.

Since $N\geq2$, the factor $N/(N-1)$ is defined. Since $\lambda b\leq0$, (3.2) implies $E(s,k)\leq\lambda b$. Also $b/s^2=m\rho(1-\rho)$, and the lower bound gives $\lambda b-E(s,k)\leq|\lambda|r$. Dividing by $s^2$ and using $r\leq ms/2$ proves (3.3), including $s=1$ and both endpoints. Continuity of $\rho(1-\rho)$ and the uniform remainder in (3.3) prove (3.4) for every stated sequence, with no fixed-density rounding restriction. $\square$

## 4. One budget for all near-minimal-state defects

**定理 4.1（Joint stability on the actual state）。** Assume (3.1). Let $\delta\geq0$ and let the same arbitrary unit state $\varphi\in\mathcal H_k$ satisfy $Q\leq E(s,k)+\delta$. Let $\Pi$ be the orthogonal projector onto the entire eigenspace $\ker(a-\lambda I)$ and let

$$
\begin{aligned}
\gamma&=\min\{\theta-\lambda:\theta\in\operatorname{spec}(a),\ \theta>\lambda\}>0,\\
h_{s,k}&=r-\frac b{N-1},\qquad
B_{s,k,\delta}=|\lambda|h_{s,k}+\delta,\\
\ell_\psi&=\|((I-\Pi)\otimes I)F\|^2.
\end{aligned}
\tag{4.1}
$$

The gap exists because $a$ has an edge, negative least eigenvalue and trace zero. Then

$$
\boxed{\quad\gamma\ell_\psi+|\lambda|T_\psi
\leq B_{s,k,\delta}.\quad}
\tag{4.2}
$$

In particular,

$$
\begin{aligned}
0\leq\left\langle V+\sum_iD_i\right\rangle_\psi
&\leq r-\frac b{N-1}+\frac\delta{|\lambda|},\\
\|((I-\Pi)\otimes I)F\|^2
&\leq\frac{|\lambda|(r-b/(N-1))+\delta}{\gamma}.
\end{aligned}
\tag{4.3}
$$

Proof. On the full least eigenspace $a-\lambda I$ is zero; on its orthogonal complement each eigenvalue is at least $\gamma$. Formula (2.9) therefore bounds the first term of (2.1) below by $\gamma\ell_\psi$. On the other hand the trial bound in (3.2) gives

$$
\begin{aligned}
Q-\lambda(b+r)
&\leq E(s,k)+\delta-\lambda(b+r)\\
&\leq\lambda b\frac N{N-1}-\lambda(b+r)+\delta\\
&=|\lambda|\left(r-\frac b{N-1}\right)+\delta.
\end{aligned}
$$

This proves (4.2). Positivity of both summands gives (4.3). The budget is nonnegative: for $r>0$, $b/(N-1)=r(N-r)/(m(N-1))\leq r$, and for $r=0$ it is zero. Nothing here replaces $\Pi$ by the rank-one projection onto the particular trial vector $z$; degeneracy of $\lambda$ is allowed. $\square$

**推论 4.2（Occupancy, permutation defects and tuple leakage）。** Under Theorem 4.1, let $\mu_i=\langle n_i\rangle_\psi$ and $\operatorname{Var}_\psi(n_i)=\langle n_i^2\rangle_\psi-\mu_i^2$. Then the following quantities share the single budget (4.2):

$$
T_\psi=
\sum_i\operatorname{Var}_\psi(n_i)
+\sum_i\left(\mu_i-\frac rm\right)^2
+\sum_i\langle D_i\rangle_\psi.
\tag{4.4}
$$

Moreover,

$$
\|(I-P_{\mathrm{sym}})\psi\|^2
\leq\frac1s\sum_i\langle D_i\rangle_\psi
\leq\frac{h_{s,k}+\delta/|\lambda|}{s}.
\tag{4.5}
$$

When $bN/(N-1)-\delta/|\lambda|>0$, the normalized tuple satisfies

$$
\frac{\ell_\psi}{\|F\|^2}
\leq
\frac{B_{s,k,\delta}}
{\gamma\bigl(bN/(N-1)-\delta/|\lambda|\bigr)}.
\tag{4.6}
$$

In particular, for fixed $H$ satisfying (3.1), every sequence of these states with $s\to\infty$ and $\delta_s=o(s^2)$ has $T_{\psi_s}/s^2\to0$ and $\ell_{\psi_s}/s^2\to0$. If also $k_s/(ms)\to\rho\in(0,1)$, then $\ell_{\psi_s}/\|F_s\|^2\to0$. These conclusions do not assert vanishing nonsymmetric-state mass for general density sequences.

Proof. Expand $\langle(n_i-r/m)^2\rangle_\psi$ around the real mean $\mu_i$ to obtain the variance plus squared mean imbalance; sum over $i$ to get (4.4). Every variance is a squared norm, $\|(n_i-\mu_i)\psi\|^2$. The third sum is exactly the collection of within-block Dirichlet forms (2.6), hence measures failure of permutation invariance, including phases of coefficients and not just their probabilities.

The commuting projections $P_i$ have joint eigenvalues in $\{0,1\}^m$, on which $1-\prod_i p_i\leq\sum_i(1-p_i)$. Thus $I-P_{\mathrm{sym}}\preceq\sum_i(I-P_i)$; (2.2) and (4.3) give (4.5). From (2.8) and (4.3),

$$
\|F\|^2\geq b+r-h_{s,k}-\frac\delta{|\lambda|}
=\frac{bN}{N-1}-\frac\delta{|\lambda|}.
$$

Under its stated positivity condition division of (4.3) by this lower bound proves (4.6). The leakage is therefore a statement about the lowering tuple $F$ in the base eigenbasis, with target space $\mathcal H_{r-1}$ left untouched. It is not a projection of $\psi$ onto one many-body eigenvector.

Finally $0\leq h_{s,k}\leq r\leq ms/2$. The right side of (4.2) is $O(s)+\delta_s$, proving both estimates divided by $s^2$. At an interior limiting density, $b/s^2\to m\rho(1-\rho)>0$, so (4.6) applies for sufficiently large $s$ and tends to zero. For any sequence with $\rho_s=k_s/(ms)\to\rho\in(0,1)$, the exact budget gives

$$
\begin{aligned}
\frac{h_{s,k_s}}s
&=m\min(\rho_s,1-\rho_s)
-\frac{ms}{ms-1}\rho_s(1-\rho_s)\\
&\longrightarrow m\min(\rho,1-\rho)-\rho(1-\rho).
\end{aligned}
\tag{4.7}
$$

Writing $t=\min(\rho,1-\rho)>0$, this limit is $t(m-1+t)>0$ because $m\geq2$. Hence even for $\delta=0$, (4.5) supplies no conclusion that the nonsymmetric mass tends to zero in this regime. The spectral and occupancy/Johnson allowances also cannot each be spent independently at their individual maxima: (4.2) is the joint constraint.

For $k>N/2$, $n_i$ in these formulas counts holes. Original particle occupancy is $sI-n_i$, so its variance is identical and its mean deviation from $k/m$ is the negative of the hole deviation from $r/m$. Complementation preserves the Johnson Laplacian in (2.5) and commutes with block symmetrization. The same interpretations therefore apply to the original state. At $r=0$, $F=T_\psi=\ell_\psi=0$; no relative tuple quotient is asserted. At $s=1$, every block permutation is trivial and $D_i=0$, as required by (2.2) and (4.5). $\square$

## 5. Signed cut-bound violations and the pentagon

**定义 5.1（Cut, restricted matching and signed violation）。** For a finite unit-weight graph $G$, let $C(G)$ be the maximum number of edges crossing a vertex cut. Let $M_k(G)$ be the maximum cardinality of a matching with at most $k$ edges. In the convention of Apte–Parekh–Sud v2, Appendix D.2, Conjecture 7, the proposed inequality is

$$
E(s,k)\geq-\frac{C(G_s)+M_k(G_s)}2,
\qquad 1\leq k\leq\left\lfloor\frac{ms}{2}\right\rfloor.
\tag{5.1}
$$

The signed violation of this particular inequality at $(s,k)$ is

$$
\mathcal V(s,k)=-\frac{C(G_s)+M_k(G_s)}2-E(s,k).
\tag{5.2}
$$

Thus positive sign means failure of (5.1), negative sign means strict validity at that instance, and zero means equality.

**定理 5.2（Density limit of the signed violation）。** Suppose (3.1). For every integer sequence $1\leq k_s\leq\lfloor ms/2\rfloor$ with $k_s/(ms)\to\rho\in[0,1/2]$,

$$
\lim_{s\to\infty}\frac{\mathcal V(s,k_s)}{s^2}
=\Delta_H(\rho)
=-\frac{C(H)}2-\lambda m\rho(1-\rho).
\tag{5.3}
$$

If $\Delta_H(\rho)>0$, every such sequence eventually violates (5.1). If $\Delta_H(\rho)<0$, every such sequence eventually satisfies (5.1) strictly. The case $\Delta_H(\rho)=0$ has no sign conclusion from this limit.

Proof. The required cut calculation is an intermediate already supplied for the pentagon in [the cut-bound source](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean), through `cut_occupancy` and `cutPoly_endpoint`, and in [its uniform half-filled family](../../../Problems/apte-parekh-sud-2025-token-graph-cut-bound.md). For general $H$, a cut having $x_i$ vertices on its chosen side in block $i$ has size

$$
\sum_{\{i,j\}\in E(H)}
\bigl[x_i(s-x_j)+x_j(s-x_i)\bigr].
$$

This polynomial is affine in each coordinate $x_i\in[0,s]$. Keeping all other coordinates fixed, an endpoint $0$ or $s$ has value at least the value at $x_i$. Rounding coordinates successively produces a block cut with no decrease. At an endpoint vector the value is $s^2$ times the size of a cut of $H$. A maximum cut of $H$ itself lifts to such a block cut. Consequently, exactly,

$$
C(G_s)=s^2C(H).
\tag{5.4}
$$

Also $0\leq M_{k_s}(G_s)\leq k_s\leq ms/2$, so $M_{k_s}(G_s)/s^2\to0$. Combine this with (3.4), (5.2) and (5.4) to prove (5.3). If its limit is strictly positive or strictly negative, the same strict sign holds for all sufficiently large terms of the sequence. At zero limit, a quantity of order smaller than $s^2$ may have either sign; a lower-order estimate is required. $\square$

**命题 5.3（The two sides of the pentagon threshold）。** Let $H=C_5$, with vertices $j\in\mathbb Z/5\mathbb Z$. Put $\phi=(1+\sqrt5)/2$. Then

$$
m=5,\qquad \lambda=-\phi,\qquad
z_j=e^{4\pi i j/5},\qquad C(C_5)=4,
\tag{5.5}
$$

and (3.1) holds. For every admissible sequence in Theorem 5.2,

$$
\Delta_{C_5}(\rho)=-2+5\phi\rho(1-\rho),\qquad
\begin{cases}
\Delta_{C_5}(\rho)<0,&0\leq\rho<1/\sqrt5,\\
\Delta_{C_5}(\rho)=0,&\rho=1/\sqrt5,\\
\Delta_{C_5}(\rho)>0,&1/\sqrt5<\rho\leq1/2.
\end{cases}
\tag{5.6}
$$

Thus the first interval gives eventual validity of (5.1), and the last gives eventual failure. In particular,

$$
\Delta_{C_5}(2/5)=\frac{3\sqrt5-7}{5}<0,\qquad
\Delta_{C_5}(1/2)=\frac{5\sqrt5-11}{8}>0.
\tag{5.7}
$$

Proof. The five Fourier vectors $j\mapsto e^{2\pi itj/5}$ form an eigenbasis of cycle adjacency with eigenvalues $2\cos(2\pi t/5)$. To evaluate them, put $u=2\cos(2\pi/5)>0$. The sum of the fifth roots of unity gives $1+u+(u^2-2)=0$, so $u=(\sqrt5-1)/2$ and $u^2-2=-\phi$. The least eigenvalue is therefore $-\phi$, and the displayed $z$ is a modulus-one vector in that eigenspace. Any cut crosses an even number of edges of a cycle, so it crosses at most four edges of $C_5$; alternating around four edges attains four. This proves (5.5).

On $[0,1/2]$, the function $\rho(1-\rho)$ is strictly increasing. The equation $5\phi\rho(1-\rho)=2$ has its smaller root at $\rho=1/\sqrt5$, since

$$
\frac1{\sqrt5}\left(1-\frac1{\sqrt5}\right)
=\frac{\sqrt5-1}{5}=\frac2{5\phi}.
$$

This proves (5.6). Substitution proves (5.7); their strict signs follow respectively from $45<49$ and $125>121$. Theorem 5.2 supplies the assertions for every converging admissible sequence. Particle–hole symmetry gives the complementary sign intervals on the upper half of the full occupancy range, if the signed expression (5.2) is considered there; (5.1) itself has the stated half-range domain.

The half-filled counterexample is an attributed supplied result: [CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean), `phi40_quotient` and `result`, supplies the phase quotient $-646912/199<-3250$ at $s=40,k=100$, and [the corresponding family derivation](../../../Problems/apte-parekh-sud-2025-token-graph-cut-bound.md) supplies refutations for every even $s\geq40$. [Apte–Parekh–Sud v3, Appendix D.2](https://arxiv.org/html/2506.03441v3), attributes a refutation to Wenlin Zhang and Haobo Ma. These half-filled refutations, the classical phase trial and the cut rounding are supplied inputs. The repo-derived inference here is the full-state defect certificate together with its uniform density limit, common near-minimal-state budget and the signed-violation limit; it carries no priority assertion or new settlement claim for Conjecture 7.

At the critical density $1/\sqrt5$, the quadratic coefficient vanishes. The sign then depends on lower-order energies, matching terms and the approach of $k_s/(5s)$ to that density; (3.2)–(3.3) do not determine it. The results give bounds rather than a general formula for exact finite-$s$ energies or optimal remainder constants. All statements use equal block sizes, unit weights and empty intrablock graphs; weighted, unequal-block and intrablock-interaction extensions require additional arguments. $\square$

## 追加锚（本行以下为增补区）

## 6. Half-filled block-spin sectors and a separation obstruction

**定义 6.1（Spin-chain sectors）。** Assume (3.1), let $s$ be even, and put
$r=ms/2$. For $t=(t_1,\ldots,t_m)\in\mathbb N^m$ with
$0\leq t_i\leq s/2$, write

$$
d_i=s-2t_i,\qquad T(t)=\sum_i t_i,\qquad D(t)=\sum_i d_i=ms-2T(t).
$$

Let

$$
\mathcal Q_{s,t}=\left\{q\in\mathbb Z^m:0\leq q_i\leq d_i,
\sum_iq_i=D(t)/2\right\}.
$$

For $q\in\mathcal Q_{s,t}$ set

$$
u_i^+(q)=\sqrt{(q_i+1)(d_i-q_i)},\qquad
u_i^-(q)=\sqrt{q_i(d_i-q_i+1)},
$$

and interpret a term with an index outside $\mathcal Q_{s,t}$ as zero. The
Hermitian matrix $\mathsf K_{s,t}$ on $\mathbb C^{\mathcal Q_{s,t}}$ is

$$
\begin{aligned}
(\mathsf K_{s,t}f)(q)=\sum_{\{i,j\}\in E(H)}
&u_i^+(q)u_j^-(q)f(q+e_i-e_j)\\
&+u_j^+(q)u_i^-(q)f(q-e_i+e_j).
\end{aligned}
\tag{6.1}
$$

Write $\mu_{s,t}=\lambda_{\min}(\mathsf K_{s,t})$. The sector $t=0$ is
called the block-symmetric sector.

**命题 6.2（The supplied identities do not prove the proposed separation）。**
The chain decomposition in Feinsilver,
[Proposition 4.1](https://arxiv.org/pdf/1102.0368v2), and Srinivasan,
[Theorem 1.2](https://arxiv.org/pdf/1001.0280v2), does give (6.1): a chain
starting at rank $t_i$ has length $d_i+1$, and in its unit basis

$$
L_i|t_i,q_i\rangle=u_i^-(q)|t_i,q_i-1\rangle,
\qquad
L_i^*|t_i,q_i\rangle=u_i^+(q)|t_i,q_i+1\rangle.
\tag{6.2}
$$

Tensoring the chains and imposing total occupancy $r$ gives an orthogonal sum
of copies of $\mathsf K_{s,t}$ over the chain multiplicity labels. The
following two calculations are obstructions to the claimed proof of a uniform
positive separation.

First, the estimate

$$
\sum_i t_i(s+1-t_i)\geq sT(t)
\tag{6.3}
$$

is false on the stated domain. If $s\geq4$ and
$t=(2,0,\ldots,0)$, its two sides are respectively $2(s-1)$ and $2s$.
The valid uniform bound from $0\leq t_i\leq s/2$ is only

$$
\sum_i t_i(s+1-t_i)\geq\left(\frac{s}{2}+1\right)T(t).
\tag{6.4}
$$

Second, the asserted equality-condition step fails when the least eigenvalue
is degenerate. Let $m=4$ and let $H$ be the disjoint union of the edges
$\{1,2\}$ and $\{3,4\}$. Then

$$
a=\begin{pmatrix}0&1&0&0\\1&0&0&0\\0&0&0&1\\0&0&1&0\end{pmatrix},
\qquad \lambda=-1,
\qquad z=(1,-1,1,-1),
$$

so (3.1) holds and
$\ker(a-\lambda I)=\{(x,-x,y,-y):x,y\in\mathbb C\}$.
For every even $s\geq2$, take $t=(1,1,0,0)$, so
$d_1=d_2=s-2$ and $d_3=d_4=s$. For an integer $d\geq0$ define the unit
vector in two equal chains

$$
\eta_d=\frac1{\sqrt{d+1}}\sum_{q=0}^d(-1)^q|q,d-q\rangle .
\tag{6.5}
$$

The lowering coefficients in (6.2) give, by reindexing the first sum,

$$
\begin{aligned}
L_1\eta_d
 &=\frac1{\sqrt{d+1}}\sum_{r=0}^{d-1}(-1)^{r+1}
   \sqrt{(r+1)(d-r)}\,|r,d-1-r\rangle,\\
L_2\eta_d
 &=\frac1{\sqrt{d+1}}\sum_{r=0}^{d-1}(-1)^r
   \sqrt{(r+1)(d-r)}\,|r,d-1-r\rangle .
\end{aligned}
$$

Consequently $L_1\eta_d+L_2\eta_d=0$. Set

$$
 f=\eta_{s-2}^{(1,2)}\otimes\eta_s^{(3,4)}.
$$

Each factor has total chain occupancy equal to its chain length, so $f$ lies
in the $t$-sector at total occupancy
$$(s-2)+s=2s-2=D(t)/2,$$
which is the half-filled layer for $m=4$. If
$y=(L_1f,L_2f,L_3f,L_4f)$, the two cancellation identities give
$y_2=-y_1$ and $y_4=-y_3$. Therefore

$$
ay=-y,
\qquad\text{hence}\qquad
(I-\Pi)y=0,
\tag{6.6}
$$

where $\Pi$ is the coordinate projection onto
$\ker(a-\lambda I)$. Here $t\neq0$. Thus vanishing of the projected leakage
in the quadratic-form bound

$$
\langle f,\mathsf K_{s,t}f\rangle\geq
\lambda\sum_i\|L_if\|^2+
\gamma_H\|(I-\Pi)(L_1f,\ldots,L_mf)\|^2
$$

does not force the sector label to be $t=0$.

The requested constants $c_H>0$ and $s_H$ therefore do not follow from the
published decomposition, the lowering identity, and the spectral projection
bound alone. In particular, (6.3)–(6.12) are not asserted here: the additional
coercive estimate controlling nonzero $t$ inside the least-eigenspace kernel is
still an open mathematical obligation under Assumption 3.1. The existing
full-state certificate (Theorem 2.1) and its near-minimal-state budget
(Theorem 4.1) remain valid, but they do not imply the requested
$\|(I-P_{\rm sym})\phi\|^2=O(\delta/s)$ confinement. Consequently no
unconditional symmetry/confinement statement is transferred to the fixed-code
oscillator result.

## 追加锚（本行以下为增补区）
