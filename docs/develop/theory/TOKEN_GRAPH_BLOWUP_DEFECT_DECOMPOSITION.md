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

## 6. Half-filled energy separation of all nonsymmetric sectors

**定义 6.1（Half filling and graph constants）。** Assume Definition 1.1 and
Assumption 3.1. Write

$$
\ell=-\lambda,\qquad \Delta=\max_i\deg_H(i),\qquad T=m+2,
\qquad c_H=\frac\ell2,\qquad
s_H=2\left\lceil 2^{18}(\Delta/\ell)^2T^3\right\rceil.
\tag{6.1}
$$

For an even positive integer $s$, put $S=s/2$, $k=mS$,
$K=K_k$ and $E=E(s,k)$. Restrict $K$ and $P_{\mathrm{sym}}$ to the
complete space $\mathcal H_{mS}$ of Definition 1.1. Define

$$
g_s=\lambda_{\min}\bigl(K|_{\operatorname{ran}(I-P_{\mathrm{sym}})}\bigr)-E.
\tag{6.2}
$$

The restriction is well defined because $K$ commutes with all block
permutations. Its space is nonzero for even $s\geq2$: in one block a
nonconstant vector on the one-particle layer can be tensored with suitable
occupancy vectors in the other blocks to reach $mS$. For example, take
occupancy $s-1$ in a second block and occupancy $S$ in the remaining blocks.
The edge test in the proof of Theorem 2.1 and the maximum-degree bound for
adjacency give $1\leq\ell\leq\Delta$, so (6.1) specifies finite positive
constants. Indeed, for a complex vector $v$,

$$
|v^*av|\leq\sum_{\{i,j\}\in E(H)}2|v_i||v_j|
\leq\sum_i\deg_H(i)|v_i|^2\leq\Delta\|v\|^2.
$$

**定理 6.2（Uniform half-filled gap and arbitrary-state confinement）。**
With Definition 6.1, for every even integer $s\geq4T$,

$$
g_s\geq\ell s-64\Delta T^{3/2}\sqrt{s/2}-64\Delta T^2.
\tag{6.3}
$$

For every even integer $s\geq s_H$, one has the operator inequality

$$
\boxed{\quad K-EI\succeq c_Hs(I-P_{\mathrm{sym}}).\quad}
\tag{6.4}
$$

Consequently, for every such $s$, every unit vector
$\phi\in\mathcal H_{mS}$, and every real $\delta\geq0$ satisfying
$\langle\phi,K\phi\rangle\leq E+\delta$,

$$
\|(I-P_{\mathrm{sym}})\phi\|^2\leq\frac{\delta}{c_Hs}
=\frac{2\delta}{\ell s}.
\tag{6.5}
$$

In particular, along every sequence of these even integers tending to
infinity, $\delta_s=o(s)$ implies
$\|(I-P_{\mathrm{sym}})\phi_s\|\to0$. Every ground state belongs to
$\operatorname{ran}P_{\mathrm{sym}}$ when $s\geq s_H$.
Disconnected $H$ and arbitrary multiplicity of its least eigenvalue are
included.

Proof. We first express the full Boolean space as an orthogonal sum of
finite spin chains. This is the classical Boolean representation used as an
intermediate here: Srinivasan,
[Theorem 1.2 and the representation derivation on pp. 3–5](https://arxiv.org/pdf/1001.0280v2),
and Feinsilver,
[§§3–4, particularly (8), (10), (16), Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2).
Their parameters are respectively $n=s$, starting rank $t$, and principal
number $s-2t$; their raising operator is our $L_i^*$ and their lowering
operator is our $L_i$. The construction and normalization needed on every
multiplicity space are as follows.

On one block write $U=L_i^*$, $L=L_i$ and $n=n_i$. Directly on Boolean
basis vectors,

$$
[L,U]=sI-2n,\qquad [n,U]=U,\qquad [n,L]=-L.
\tag{6.6}
$$

Choose an orthonormal basis of the space $\ker L$ at each rank $t$.
There are no nonzero such vectors with $t>S$, since (6.6) gives
$\|Uv\|^2=(s-2t)\|v\|^2$. For a unit vector $v$ in that space, put
$d=s-2t\geq0$. Induction in (6.6) gives

$$
\begin{aligned}
LU^qv&=q(s-2t-q+1)U^{q-1}v &&(1\leq q\leq s-2t+1),\\
\|U^qv\|^2&=q!\frac{(s-2t)!}{(s-2t-q)!} &&(0\leq q\leq s-2t).
\end{aligned}
\tag{6.7}
$$

$U^{d+1}v=0$: its squared norm is obtained by applying the first identity
with $q=d+1$ and is zero. Normalize the vectors in (6.7).
Vectors at different ranks are orthogonal. For two chains starting at
different ranks $t<t'$, at a common rank $n$ move $U^{n-t}$ across the
inner product; the resulting $L^{n-t}U^{n-t'}v'$ is zero. For two vacua at
the same rank, (6.7) makes the inner product at every common rank a positive
scalar times their original inner product. Thus these chains are mutually
orthogonal and invariant under $L,U,n$.

They exhaust the block space: their orthogonal complement is invariant
under all three operators; a nonzero vector of its smallest occupied rank
would be in $\ker L$ and hence in the already included chains. The number
of chains starting at $t$ is therefore

$$
r_s(t)=\binom st-\binom s{t-1},\qquad 0\leq t\leq S,
\quad\binom s{-1}=0.
\tag{6.8}
$$

To see the count, the rank-$t$ space, for $t\leq S$, has one vector from
each chain starting at ranks $0,\ldots,t$ and dimension $\binom st$;
subtract the rank-$t-1$ count. The chain starting at rank zero is unique
and consists of the normalized constant vectors on the block's occupancy
layers. These are exactly its permutation-invariant vectors. Formula
(6.8) includes the length-one chains at $t=S$.

For $t=(t_1,\ldots,t_m)\in\{0,\ldots,S\}^m$, put

$$
J_i=S-t_i,\qquad \tau=\sum_i t_i,\qquad
\mathcal X_t=\{x\in\mathbb Z^m:|x_i|\leq J_i,\ \sum_i x_i=0\}.
\tag{6.9}
$$

A tensor of block chains has occupancies
$n_i=t_i+q_i=S+x_i$, where $q_i=J_i+x_i$. In its orthonormal basis,

$$
\begin{aligned}
L_i|x\rangle&=b_{J_i}^-(x_i)|x-e_i\rangle,&
b_J^-(x)&=\sqrt{(J+x)(J-x+1)},\\
L_i^*|x\rangle&=b_{J_i}^+(x_i)|x+e_i\rangle,&
b_J^+(x)&=\sqrt{(J-x)(J+x+1)}.
\end{aligned}
\tag{6.10}
$$

The first and second maps go to total centered occupancy $-1$ and $1$,
respectively; zero coefficients at the endpoints mean zero vectors.
By (2.4), the matrix $K_t$ on $\ell^2(\mathcal X_t)$ is specified on kets
by

$$
K_t|x\rangle=\sum_{i,j}a_{ij}
b_{J_i}^+(x_i)b_{J_j}^-(x_j)|x+e_i-e_j\rangle,
\tag{6.11}
$$

omitting terms outside $\mathcal X_t$. Reverse moves have the same
coefficient, so this matrix is Hermitian. Tensoring the entire block
decompositions proves the exact orthogonal decomposition

$$
\mathcal H_{mS}\cong
\bigoplus_{t\in\{0,\ldots,S\}^m}
\ \bigoplus_{\alpha_i=1,\ldots,r_s(t_i)}
\ell^2(\mathcal X_t),\qquad
K\cong\bigoplus_{t,\alpha}K_t.
\tag{6.12}
$$

Here the inner sum ranges over all tuples of multiplicity indices.
$P_{\mathrm{sym}}$ is the projection onto precisely $t=0$; no other chain
has permutation-invariant vectors. Every $\mathcal X_t$ contains $0$.
All sector minima $\mu_t=\lambda_{\min}(K_t)$ consequently exist.

For a unit vector $f$ in one such sector let

$$
\begin{aligned}
F&=(L_1f,\ldots,L_mf),&
A&=a+\ell I,& R&=\langle F,(A\otimes I)F\rangle,\\
X_i&=\langle f,x_i^2f\rangle,&\nu_i&=\langle f,x_if\rangle,& X&=\sum_iX_i,\\
d(t)&=\sum_i t_i(2S+1-t_i).
\end{aligned}
\tag{6.13}
$$

The symbols $x_i$ inside inner products denote diagonal multiplication
operators. Thus $X_i\geq0$, $|\nu_i|\leq\sqrt{X_i}$ and
$\sum_i\nu_i=0$. The norm identity in (6.10) gives

$$
\|L_if\|^2=J_i(J_i+1)-X_i+\nu_i,\qquad
\langle f,K_tf\rangle
=-\ell mS(S+1)+\ell d(t)+\ell X+R.
\tag{6.14}
$$

This is the restriction of the full-state certificate (2.1): on this chain
$D_i=t_i(2S+1-t_i)I$ and $V=\sum_i x_i^2$. In particular $R\geq0$.
Neither (6.13) nor (6.14) projects onto a particular vector in the least
eigenspace.

The flat-phase trial (3.5)–(3.7), with $N=2mS$, $k=mS$ and $b=mS^2$,
supplies the upper bound

$$
E\leq-\ell mS^2\frac{2mS}{2mS-1}\leq-\ell mS^2.
\tag{6.15}
$$

The subset count and complex Rayleigh normalization used there are supplied
also by `counting_identity`, `W_move`, `Test.token_energy`, `phi40_energy`,
`phi40_norm` and `real_complex_rayleigh` in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean).
Only their counting and Rayleigh mechanisms are used, not a pentagon-specific
energy value. Ordinary adjacency is essential in (6.11) and (6.15): in
[Apte–Parekh–Sud v3, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v3),
the XY block is the different operator $W I/2-K$.

We prove (6.3) sector by sector. Since $t_i\leq S$,
$d(t)\geq(S+1)\tau$. If $\tau\geq T=m+2$, (6.14) and (6.15) immediately
give

$$
\mu_t-E\geq\ell\bigl((S+1)\tau-mS\bigr)\geq2\ell S.
\tag{6.16}
$$

This includes every sector with any zero local spin that meets this deficit
condition; there is no restriction on its multiplicity indices.
It remains to consider $1\leq\tau<T$ and $S\geq2T$. If
$\mu_t\geq E+2\ell S$, (6.3) already follows. Otherwise choose a unit
least eigenvector $f$ of $K_t$. By (6.14)–(6.15),

$$
R+\ell X+\ell d(t)
=\mu_t+\ell mS(S+1)<\ell(m+2)S=\ell TS.
$$

In particular,

$$
X\leq TS,\qquad R\leq\ell TS,\qquad
J_i\geq S-T\geq S/2.
\tag{6.17}
$$

Embed this same vector isometrically into the $t=0$ sector by leaving its
centered coordinates unchanged: $g(x)=f(x)$ on $\mathcal X_t$ and $g(x)=0$
on $\mathcal X_0\setminus\mathcal X_t$. Then $\|g\|=1$, $g$ is still
half filled, and $E\leq\langle g,K_0g\rangle$. We estimate this last
quadratic form, including its boundary coefficients.

Put

$$
p=S+\tfrac12,\qquad p_i=J_i+\tfrac12=p-t_i,\qquad
h_i=p/p_i=1+\beta_i,\qquad \beta_i=t_i/p_i,
\qquad B=\operatorname{diag}(\beta_1,\ldots,\beta_m).
\tag{6.18}
$$

For either sign and every $|x|\leq J_i$, write

$$
b_S^\pm(x)=h_i b_{J_i}^\pm(x)+r_i^\pm(x).
$$

If $t_i=0$, this remainder is zero. If $t_i>0$, take
$y=x\pm\tfrac12$ for $b^\pm$. Then $|y|\leq p_i$, and
$b_S^\pm=\sqrt{p^2-y^2}$, $b_{J_i}^\pm=\sqrt{p_i^2-y^2}$. Rationalization
gives

$$
\begin{aligned}
0\leq r_i^\pm(x)
&=\frac{(h_i^2-1)y^2}{\sqrt{p^2-y^2}+h_i\sqrt{p_i^2-y^2}}\\
&\leq\frac{\sqrt{p^2-p_i^2}}{p_i^2}\,y^2
\leq\frac{7\sqrt{t_i}}{S^{3/2}}\,y^2
\leq\frac{14\sqrt{t_i}}{S^{3/2}}(x^2+1).
\end{aligned}
\tag{6.19}
$$

Indeed $p^2-p_i^2=t_i(2p-t_i)\leq3St_i$ and $p_i\geq S/2$; hence the
penultimate coefficient is at most $4\sqrt3\sqrt{t_i}/S^{3/2}$.
The denominator is positive even at $|y|=p_i$ when $t_i>0$.
Thus the estimate includes both ladder endpoints, without division by a
vanishing deficient-spin coefficient. Also
$h_i b_{J_i}^\pm(x)\leq b_S^\pm(x)\leq p$.

For a directed allowed move $x'=x+e_i-e_j$ with both endpoints in
$\mathcal X_t$, its coefficient difference is

$$
\begin{aligned}
\mathcal R_{ij}(x)
&=b_S^+(x_i)b_S^-(x_j)
-h_ih_jb_{J_i}^+(x_i)b_{J_j}^-(x_j)\\
&=r_i^+(x_i)b_S^-(x_j)
+h_i b_{J_i}^+(x_i)r_j^-(x_j)\\
&\geq0,\\
\mathcal R_{ij}(x)
&\leq\frac{24}{\sqrt S}
\bigl[\sqrt{t_i}(x_i^2+1)+\sqrt{t_j}(x_j^2+1)\bigr].
\end{aligned}
\tag{6.20}
$$

Here (6.19) and $p\leq3S/2$ actually give the smaller coefficient $21$.
The reverse move has exactly the same $\mathcal R$.
Moves leaving $\mathcal X_t$ contribute zero to the quadratic form of
$g$, since $g$ vanishes at their other endpoint. Therefore

$$
\langle g,K_0g\rangle
=\langle F,((I+B)a(I+B)\otimes I)F\rangle+\varepsilon,
\tag{6.21}
$$

where $\varepsilon$ is the sum of
$a_{ij}\mathcal R_{ij}(x)\overline{f(x')}f(x)$ over directed allowed moves.
All these formulas are valid for complex $f$. Taking absolute values,
using $2|f(x')f(x)|\leq|f(x')|^2+|f(x)|^2$, and pairing reverse moves,
we obtain

$$
\begin{aligned}
|\varepsilon|
&\leq\sum_{i,j,x}a_{ij}\mathcal R_{ij}(x)|f(x)|^2\\
&\leq\frac{48\Delta}{\sqrt S}
\left(\sum_i\sqrt{t_i}X_i+\sum_i\sqrt{t_i}\right)\\
&\leq48\Delta T^{3/2}\sqrt S+\frac{48\Delta T}{\sqrt S}.
\end{aligned}
\tag{6.22}
$$

The first sum ranges only over allowed moves; enlarging the nonnegative
upper bound to all $x$ gives the second line. For the last line,
$\sqrt{t_i}\leq\sqrt\tau$, and $\sum_i\sqrt{t_i}\leq\tau$ because each
$t_i$ is an integer. Apply (6.17) and $\tau<T$. This is a bound for the
actual state and its boundary mass, not a pointwise small-occupancy
assumption.

For the scaled quadratic form in (6.21), use $a=-\ell I+A$. Since
$\|A\|\leq2\Delta$, positivity and (6.17) give

$$
\|(A\otimes I)F\|^2\leq2\Delta R\leq2\Delta\ell TS.
\tag{6.23}
$$

Furthermore $\|L_if\|\leq p_i$ by (6.10), so

$$
\|(B\otimes I)F\|^2
=\sum_i\beta_i^2\|L_if\|^2\leq\sum_i t_i^2\leq\tau^2.
\tag{6.24}
$$

We also need the sign of the first-order energy change. From (6.14),
$\beta_i\leq2t_i/S$, and $|\nu_i|\leq\sqrt{X_i}$,

$$
\begin{aligned}
\sum_i\beta_i\|L_if\|^2
&=\sum_i\left[t_ip_i-\frac{t_i}{4p_i}
-\beta_iX_i+\beta_i\nu_i\right]\\
&\geq S\tau-\sum_i t_i^2
-\frac{2\tau}{S}(X+\sqrt X)\\
&\geq S\tau-5T^2.
\end{aligned}
\tag{6.25}
$$

For the second line, $t_ip_i-t_i/(4p_i)
=St_i-t_i^2+t_i/2-t_i/(4p_i)\geq St_i-t_i^2$, since $p_i\geq1/2$.
Also $\sum_i t_iX_i\leq\tau X$ and
$\sum_i t_i\sqrt{X_i}\leq\tau\sqrt X$.
For the third line, the total loss is at most
$\tau^2+2\tau T+2\tau\sqrt{T/S}\leq5T^2$ for $S\geq2T$ and $\tau<T$.

Expanding $(I+B)a(I+B)$, applying Cauchy–Schwarz to the term containing
$A$, and using (6.23)–(6.25), we conclude

$$
\begin{aligned}
&\langle F,((I+B)a(I+B)\otimes I)F\rangle-\mu_t\\
&\quad=-2\ell\sum_i\beta_i\|L_if\|^2
+2\operatorname{Re}\langle(B\otimes I)F,(A\otimes I)F\rangle
+\langle(B\otimes I)F,(a\otimes I)(B\otimes I)F\rangle\\
&\quad\leq-2\ell S\tau+10\ell T^2
+2\tau\sqrt{2\Delta\ell TS}+\Delta\tau^2\\
&\quad\leq-2\ell S\tau+3\Delta T^{3/2}\sqrt S+11\Delta T^2.
\end{aligned}
\tag{6.26}
$$

In the last line we used $\ell\leq\Delta$, $\tau<T$, and $2\sqrt2<3$.
Combining (6.21), (6.22) and (6.26), using
$48\Delta T/\sqrt S\leq48\Delta T^2$, gives

$$
\begin{aligned}
E\leq\langle g,K_0g\rangle
&\leq\mu_t-2\ell S\tau
+51\Delta T^{3/2}\sqrt S+59\Delta T^2\\
&\leq\mu_t-2\ell S\tau
+64\Delta T^{3/2}\sqrt S+64\Delta T^2.
\end{aligned}
\tag{6.27}
$$

Since $\tau\geq1$, this proves (6.3) for the remaining sectors.
Together with (6.16) and the case $\mu_t\geq E+2\ell S$, it proves
(6.3) simultaneously for every nonzero $t$, every multiplicity copy and
all even $s\geq4T$. The comparison used the actual full-sector $E$
through (6.15) and Rayleigh's inequality; a symmetric ground state was
not an assumption.

Finally let $q=\Delta/\ell\geq1$ and $s\geq s_H$ be even. Then
$S\geq2^{18}q^2T^3\geq2T$ and

$$
\frac{64\Delta T^{3/2}\sqrt S}{\ell S}\leq\frac18,
\qquad
\frac{64\Delta T^2}{\ell S}\leq\frac1{4096qT}.
\tag{6.28}
$$

The sum is less than one. Thus (6.3) gives $\mu_t-E\geq\ell S=c_Hs$
for every $t\ne0$. On $t=0$, $K_0-EI\succeq0$ because $E$ is the least
eigenvalue on the entire space. For an arbitrary vector, decompose it
orthogonally as in (6.12). There are no cross terms for $K$ or for
$P_{\mathrm{sym}}$. Sum these sector inequalities, multiplied by the
squared norms of their components, to get (6.4) for arbitrary
superpositions. Apply its quadratic form to a unit $\phi$ to obtain
(6.5). Setting $\delta=0$ gives the ground-state assertion, and taking
square roots in (6.5) proves the stated norm limit. $\square$

**命题 6.3（Product Dicke code and its energy-confinement correspondence）。**
In the notation of [the collective-oscillator theory, Definitions 1.1–1.2
and Assumption 1.3](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
take $d=m$, $N=s$, $B=a$ and $\hbar>0$. Identify the two single-cell
states $g,e$ with Boolean occupations $0,1$. On this complete two-state
tensor space,

$$
\mathcal D_s^{\otimes m}=\operatorname{ran}P_{\mathrm{sym}},\qquad
H_s(a)|_{\mathcal H_{mS}}=\frac{\hbar}{s}K.
\tag{6.29}
$$

For every even $s\geq s_H$, its actual half-filled least energy is
$\mathcal E_s=\hbar E/s$, and every unit half-filled state $\phi$ with
$\langle\phi,H_s(a)\phi\rangle\leq\mathcal E_s+\epsilon$, $\epsilon\geq0$,
satisfies

$$
\|(I-P_{\mathrm{sym}})\phi\|^2\leq\frac{2\epsilon}{\hbar\ell}.
\tag{6.30}
$$

The fixed-low-excitation oscillator comparison in that volume's Theorem
2.1 retains its own hypotheses and fixed excitation cutoff $M$;
(6.29)–(6.30) assert symmetry and energy confinement only.

Proof. At occupancy $n$ in one block, a permutation-invariant vector has
one common coefficient on the $n$-subsets. Its unit basis vector is
$\binom sn^{-1/2}\sum_{|U|=n}|U\rangle=|D_n^{(s)}\rangle$.
These vectors at all occupancies span precisely the invariant subspace.
Their normalization and orthogonality are the two-letter specialization
of `sector_words_card_multinomial` and `sector_gram` in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean),
with occupation counts $(s-n,n)$, including $n=0,s$.
Taking the product over blocks gives the first equality in (6.29).
At half filling it means the intersection with $\mathcal H_{mS}$.
The consumer's operator $a_{i,s}$ is $L_i/\sqrt s$; its Hamiltonian with
$B=a$ is therefore $\hbar\sum_{i,j}a_{ij}L_i^*L_j/s$, giving the second
equality by (2.4). Apply (6.5) with $\delta=s\epsilon/\hbar$ to obtain
(6.30).

The oscillator comparison uses only the part with total excitation at
most a fixed $M$, through its map $J_s$ to these same product Dicke
vectors. Here the total excitation is $ms/2$, which grows with $s$.
Membership in the product Dicke code does not put that sector in a fixed
$M$ window, so the symmetry conclusion supplies no oscillator
approximation on this growing window. Other densities, odd $s$, the
even integers below $s_H$, and an optimal threshold are not assertions of
Theorem 6.2. $\square$

## 追加锚（本行以下为增补区）

## 7. Strict symmetry at every even scale with bipartite neighborhoods

**定义 7.1（Locally bipartite graphs and the unrestricted half-filled gap）。**
Let $H$ be a finite simple unit-weight graph on $[m]$, $m\geq2$, with
no isolated vertices. Assume that the induced graph $H[N_H(p)]$ is
bipartite for every vertex $p$. Neighborhoods and $H$ may be disconnected;
an edgeless neighborhood is bipartite. For every integer $S\geq1$, put
$s=2S$, $k=mS$, and use exactly the complete complex Boolean space
$\mathcal H_{mS}$, ordinary positive adjacency $K=K_{mS}$, and original
block-permutation projection $P_{\mathrm{sym}}$ of Definitions 1.1–1.2.
Set, independently of Definition 6.1,

$$
\begin{aligned}
E_H(2S)&=\lambda_{\min}(K),\\
g(H,2S)&=\lambda_{\min}\bigl(K|_{\ker P_{\mathrm{sym}}}\bigr)-E_H(2S).
\end{aligned}
\tag{7.1}
$$

Both subspaces reduce $K$. The nonsymmetric subspace is nonzero: take
a nonconstant one-particle vector in one block, occupancy $2S-1$ in a
second block, and occupancy $S$ in each remaining block. Their total
occupancy is $mS$. This construction also applies to $S=1$.
No flat least mode, regularity, or connectedness is assumed.

**定理 7.2（Strict all-even local-neighborhood separation）。**
For every $H$ and every integer $S\geq1$ of Definition 7.1,

$$
\ker(K-E_H(2S)I)\subseteq\operatorname{ran}P_{\mathrm{sym}},
\qquad g(H,2S)>0.
\tag{7.2}
$$

Proof. Write $E=E_H(2S)$. Use the complete orthogonal decomposition
(6.6)–(6.12), which did not use the flat-mode hypothesis: a local chain
has integer spin $J_i=S-t_i$, $0\leq J_i\leq S$, magnetic coordinate
$x_i=n_i-S$, and multiplicity $r_{2S}(t_i)$. Its spin operators are

$$
Z_i|x_i\rangle=x_i|x_i\rangle,\qquad
J_i^\pm|x_i\rangle=b_{J_i}^\pm(x_i)|x_i\pm1\rangle,
\qquad
K_{\boldsymbol J}=\sum_{\{i,j\}\in E(H)}
(J_i^+J_j^-+J_i^-J_j^+).
\tag{7.3}
$$

Here $b_J^\pm$ are exactly (6.10), and the total magnetic coordinate
is zero. The Cartesian operators are $X_i=(J_i^++J_i^-)/2$ and
$Y_i=(J_i^+-J_i^-)/(2i)$. Thus each edge in (7.3) is
$2(X_iX_j+Y_iY_j)$, with no diagonal shift. The parameter correspondence
with Srinivasan, [Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
is Boolean rank $n=2S$, starting rank $t_i$, and up operator $J_i^+$;
with Feinsilver, [§3, (8)–(10), Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
the principal number is $2J_i=2S-2t_i$. These classical representations
supply all chains, including spin zero, and all multiplicity copies.
Positive token adjacency and its factor in (7.3) agree with
Apte–Parekh–Sud, [v3, Definition 1 and §3.2](https://arxiv.org/pdf/2506.03441v3);
their shifted XY operator $WI/2-K$ is different.

We first use the known nonstrict local-spin comparison, with its
fixed-magnetization argument made explicit. Its source is
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[*Scalable Implementation of Mean-Field and Correlation Methods Based
on Lie-Algebraic Similarity Transformation of Spin Hamiltonians in the
Jordan–Wigner Representation*, Appendix A4, (A34)–(A54) and the final
fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
In that source's notation, the maximal on-site spin is $s_p=S$, the
variable on-site spin $t_p$ is our $J_p$, the magnetization is $M=0$,
and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
We need its nonstrict conclusion, not an exclusion of equality.

Fix the other local spins and let $\eta_j$ be the minimum of (7.3)
with spin $j$ at $p$ and total magnetic coordinate zero. These spaces
are nonempty because all spins are integers. Realize spin $j$ as the
symmetric space of $2j$ auxiliaries and adjoin a pair in the normalized
spin-one state $|1,0\rangle$. This is the source's singlet-release trial
with zero projection along the conserved $z$ axis. All three Cartesian
expectations of that pair vanish. If $f_j$ is a normalized ground vector
for $\eta_j$, the trial $f_j\otimes|1,0\rangle$ therefore has energy
$\eta_j$ and still has total magnetic coordinate zero.

The classical spin decomposition of $j\otimes1$ is $1$ for $j=0$,
and $(j+1)\oplus j\oplus(j-1)$ for integer $j\geq1$. For example,
subtracting the weight multiplicities of a spin-$(j+1)$ chain and then
of a spin-$j$ chain leaves precisely a spin-$(j-1)$ chain; orthogonal
invariant complements give this decomposition. It is the same
finite-spin representation algebra underlying (6.6)–(6.12).
The spin-$(j+1)$ projection of the trial is nonzero for every nonzero
$f_j$, including endpoint magnetic coordinates. Indeed, on
$|j,x\rangle\otimes|1,0\rangle$ its squared coefficient is

$$
\left\|P_{j+1}(|j,x\rangle\otimes|1,0\rangle)\right\|^2
=\frac{2\binom{2j}{j+x}}{\binom{2j+2}{j+x+1}}
=\frac{(j+1)^2-x^2}{(j+1)(2j+1)}>0
\quad(-j\leq x\leq j).
\tag{7.4}
$$

For the first equality, project the normalized constant vector on
$(j+x)$-subsets of the first $2j$ coordinates, tensored with the
normalized one-particle vector of the pair, onto the constant vector
on $(j+x+1)$-subsets of all $2j+2$ coordinates. There are
$2\binom{2j}{j+x}$ contributing subsets. Distinct $x$ have orthogonal
images, so (7.4) also applies to entangled $f_j$ by summing squared norms.
For $j=0$ the coefficient is one.

Consequently $\eta_1\leq\eta_0$. Inductively assume
$\eta_0\geq\cdots\geq\eta_j$. The normalized projections of the trial
onto spins $j-1$ and $j$, when nonzero, have energies at least
$\eta_{j-1}\geq\eta_j$ and $\eta_j$. Since their weighted average with
the nonzero spin-$(j+1)$ contribution is $\eta_j$, that last
contribution has energy at most $\eta_j$. Hence

$$
\eta_{j+1}\leq\eta_j\qquad(0\leq j<S).
\tag{7.5}
$$

This is the cited comparison used as an intermediate. It proves existence
of a ground vector with increased local spin when equality holds; it
does not say that every ground vector already has maximal local spins.
It applies with arbitrary other integer spins, zero spins included.

We next establish the local obstruction needed for strictness. Let $G$
be a finite bipartite graph carrying spin $S\geq1$ at each vertex, and
put $K_G=\sum_{\{i,j\}\in E(G)}(J_i^+J_j^-+J_i^-J_j^+)$. If $G$ has
an edge, no ground vector of $K_G$ on total magnetic coordinate zero
is a singlet for the total spin of all vertices of $G$.
To prove this, suppose a normalized $v$ is both such a ground vector,
with eigenvalue $e$, and a total singlet. Define

$$
T_\alpha=\sum_{\{i,j\}\in E(G)}J_i^\alpha J_j^\alpha
\quad(\alpha=x,y,z),\qquad
K_G=2(T_x+T_y).
\tag{7.6}
$$

A total singlet is fixed by all simultaneous spin rotations. Rotate
$K_Gv=ev$ to obtain also $2(T_x+T_z)v=ev$ and
$2(T_y+T_z)v=ev$. Adding the last two equations and subtracting the
first gives

$$
T_zv=\frac e4v,\qquad
T_z|x\rangle=\left(\sum_{\{i,j\}\in E(G)}x_ix_j\right)|x\rangle.
\tag{7.7}
$$

Choose a connected component $C$ with an edge and let $D=V(G)\setminus C$.
The reduced density of $v$ on $C$ is invariant under every simultaneous
spin rotation on $C$, because $v$ is a total singlet. Decompose the
spin representation on $C$ into irreducibles $V_q$ and their
multiplicity spaces. All $q$ are nonnegative integers: the weights of
a tensor product of integer spins are integers. An invariant density
has the form $\bigoplus_q I_{V_q}\otimes A_q$, $A_q\succeq0$.
Every $V_q$ contains its zero-weight vector, so

$$
\operatorname{tr}(\rho_C\,\mathbf1_{Z_C=0})
=\sum_q\operatorname{tr}A_q>0,
\qquad Z_C=\sum_{i\in C}Z_i.
\tag{7.8}
$$

The inequality follows from $\operatorname{tr}\rho_C
=\sum_q(2q+1)\operatorname{tr}A_q=1$. Thus the projection $w$ of $v$
onto $Z_C=0$ is nonzero. It also has $Z_D=0$.

On $C$, a sign change
$|x\rangle\mapsto(-1)^{\sum_{i\in A}(S+x_i)}|x\rangle$, where
$A$ is one side of a bipartition of $C$, conjugates $K_C$ to $-K_C$.
The configuration graph on $Z_C=0$ is connected. To see this on the
original carrier, the independent $2S$-blow-up of a connected graph
with an edge is connected. Its edge transpositions generate all vertex
permutations, since transpositions along a path generate a
transposition of its endpoints. They therefore connect all subsets
of a fixed cardinality. Passing to their block occupancies gives the
connected graph of the allowed moves in (7.3). Every such move has a
strictly positive coefficient. Perron–Frobenius applied to the
nonnegative irreducible matrix $K_C$ shows that $-K_C$ has a unique
least eigenvector with all coordinates strictly positive. Undoing the
sign change, the least eigenspace of $K_C$ on $Z_C=0$ is a line spanned
by a vector $u_C$ with every coordinate nonzero.

Let $e_C,e_D$ be the minima on $Z_C=0,Z_D=0$ respectively. If $D$ is
empty, its space is $\mathbb C$, $K_D=0$ and $e_D=0$. Because $v$ is a
ground vector at total zero and $w\ne0$, the spectral minimum of
$K_C\otimes I+I\otimes K_D$ on this subspace is both at least $e$
and at most the eigenvalue $e$ of $w$. Therefore
$e=e_C+e_D$, and
$w=u_C\otimes w_D$ for some nonzero $w_D$. Projection onto $Z_C=0$
commutes with $T_z$, so (7.7) still holds on $w$.
Choose any configuration $y$ of $D$ with $w_D(y)\ne0$. For every
zero-sum configuration $x$ on $C$, its coefficient in $w$ is nonzero,
and (7.7) requires

$$
\sum_{\{i,j\}\in E(C)}x_ix_j
+\sum_{\{i,j\}\in E(D)}y_iy_j=\frac e4.
\tag{7.9}
$$

Take first $x_i=0$ for every $i\in C$, and then $x_i=1,x_j=-1$
on the two endpoints of one edge, all other coordinates zero. Both
are allowed because $S\geq1$, but their first sums in (7.9) are $0$
and $-1$. This contradiction proves the obstruction, even when $G$
has isolated vertices or several components. The use of integer spin
in (7.8) and of the zero and $\pm1$ configurations is essential.
If $G$ has vertices but no edges, its zero-magnetization ground space
instead contains

$$
u_G=\bigotimes_{i\in V(G)}|S,0\rangle,
\qquad
\left\|\sum_{i\in V(G)}J_i^+u_G\right\|^2
=|V(G)|S(S+1)>0.
\tag{7.10}
$$

Thus every nonempty bipartite $G$ has a zero-magnetization ground
vector $u_G$ which is not annihilated by both total ladder operators:
for an edged $G$ this follows from the obstruction, and for an
edgeless $G$ use (7.10).

Now suppose that a nonsymmetric sector of the full problem has minimum
$E$. There is a site $p$ with $J_p<S$. Repeatedly applying (7.5) at
all other sites gives a ground vector with spin $J_p$ at $p$ and spin
$S$ everywhere else: no resulting energy can fall below the actual
full-space minimum $E$. Multiplicity does not restrict this step,
since every spin $0,\ldots,S$ occurs in the complete Boolean block.

Realize the spin-$J_p$ factor using a symmetric group of $2J_p$
auxiliaries and $S-J_p$ disjoint singlet pairs at $p$. This realizes an
actual copy of that spin in the original block of $2S$ Boolean
coordinates. The collective operators annihilate each singlet pair;
thus this realization intertwines (7.3), preserves $Z_p$ and all
energies, and allows arbitrary entanglement of the remaining $2J_p$
auxiliaries with the other sites. In particular choose one such pair
and write a normalized ground vector as
$\Psi=|0,0\rangle\otimes f$. Keep all other singlet pairs fixed.
Put

$$
A=N_H(p),\qquad R=[m]\setminus(\{p\}\cup A),\qquad
B^\pm=\sum_{i\in A}J_i^\pm.
\tag{7.11}
$$

There are no edges between $p$ and $R$, and $A$ is nonempty.
Replace only the chosen pair by $|1,0\rangle$, giving
$\Theta=|1,0\rangle\otimes f$. Its total magnetic coordinate is still
zero. Since the pair has zero spin expectation and there is no
intrablock interaction, $\langle\Theta,K\Theta\rangle=E$.
For a finite Hermitian matrix with minimum $E$, equality in the
Rayleigh bound implies the eigenvector equation: expand the vector
in an orthonormal eigenbasis and sum
$(\lambda-E)|c_\lambda|^2$. Hence both $\Psi$ and $\Theta$ are ground
vectors of the actual original operator.

Let $K^{\mathrm{rem}}$ denote the operator acting on $f$ after the
chosen pair is omitted. Its spin at $p$ consists of the other
auxiliaries, and $K^{\mathrm{rem}}f=Ef$. The spin-one ladder
coefficients at magnetic coordinate zero are $\sqrt2$, so

$$
(K-E)\Theta
=\sqrt2\,|1,1\rangle\otimes B^-f
+\sqrt2\,|1,-1\rangle\otimes B^+f=0.
\tag{7.12}
$$

The two pair states are orthogonal, proving $B^-f=B^+f=0$.
Their commutator also gives $Z_Af=0$, where
$Z_A=\sum_{i\in A}Z_i$. In the spin representation of $A$, the common
kernel of the two ladders is exactly its spin-zero subspace: in a
spin-$q$ irreducible, both squared ladder norms can vanish only when
$q=0$. Therefore $f$ lies in
$\mathcal S_A\otimes\mathcal H_{pR}$, with $\mathcal S_A$ the total
singlet space on $A$, and its $pR$ part has total magnetic coordinate
zero.

All spin-one components at a site $i\in A$ have zero matrix elements
between total singlets on $A$. Indeed, a simultaneous rotation of $A$
fixes both singlets and rotates these three matrix elements as a vector;
the only vector fixed by all three-dimensional rotations is zero.
Equivalently, sandwiching $X_i,Y_i,Z_i$ between the singlet projections
gives zero. This statement holds with arbitrary operators on $pR$
tensored alongside it. Consequently the interactions joining $A$ to
$p$ or to $R$ have zero expectation in $f$. If $K_A,K_R$ denote the
induced operators on $A,R$, then

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{7.13}
$$

For $R=\varnothing$, $\mathcal H_R=\mathbb C$ and $K_R=0$;
no argument requires a vertex or an edge in $R$.

Let $e_A$ be the minimum of $K_A$ on its total-zero subspace, with
spin $S$ at every vertex. Choose a normalized ground vector $u_A$
there which is not annihilated by both $B^\pm$. Such a choice exists
by (7.9)–(7.10), because $H[A]$ is bipartite and $A\ne\varnothing$.
Let $\rho_{pR}$ be the reduced density of $f$ on the other factors,
including all the remaining auxiliaries at $p$. It is supported at
total magnetic coordinate zero. Form the state

$$
\rho=|0,0\rangle\langle0,0|\otimes
|u_A\rangle\langle u_A|\otimes\rho_{pR}
\tag{7.14}
$$

in the original half-filled space, retaining the same fixed other
singlet pairs at $p$. As $u_A$ has definite magnetic coordinate zero,
each $\langle u_A,J_i^\pm u_A\rangle=0$. Hence every crossing edge
has zero expectation in this product state, and

$$
\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{7.15}
$$

All comparisons use the same half-filled carrier. Its minimum is $E$,
so equality holds. Decompose $\rho_{pR}$ spectrally into normalized
vectors $h$ with positive weights, each still in its total-zero
subspace. Every resulting vector
$|0,0\rangle\otimes u_A\otimes h$ has Rayleigh quotient at least $E$;
their average equals $E$, so each is a ground vector. Apply the same
pair replacement and (7.12) to any one of them. It forces
$B^-u_A=B^+u_A=0$, contradicting the choice of $u_A$.
This rules out every nonsymmetric sector at energy $E$.

The strict step is the neighborhood obstruction and the product
replacement (7.7)–(7.15), beyond the cited nonstrict comparison.
For context, partial ferromagnetic strictness is prior mathematics:
Benassi–Lees–Ueltschi,
[*Correlation inequalities for the quantum XY model*, v3, §4.3,
Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2),
prove strict ground-energy decrease for their negative Hamiltonian with
nonnegative product couplings in the 1 and 3 directions and use it
for the two-auxiliary triplet construction. Their $R^i$ in (4.2) is
the spin-one sum of two spin-half auxiliaries, corresponding here to
the chosen pair, not to an arbitrary full spin-$S$ block.
The positivity and zero-expectation alternatives in that proof are
intermediate precedents; they do not supply (7.2) for positive
adjacency on a possibly nonbipartite $H$. Here bipartiteness is used
only for the induced neighborhood components. No global sign change
of $K$ is asserted.

Finally (6.12) is an orthogonal decomposition reducing both $K$ and
$P_{\mathrm{sym}}$. Its $t=0$ summands are precisely
$\operatorname{ran}P_{\mathrm{sym}}$. We have excluded energy $E$ from
every $t\ne0$ summand, without discarding any multiplicity copy.
An arbitrary ground vector, including a superposition of such copies,
therefore has only $t=0$ components. The restriction to
$\ker P_{\mathrm{sym}}$ is a nonempty finite-dimensional Hermitian
operator whose eigenvalues are all strictly above $E$. Its minimum
is consequently strictly above $E$, proving (7.2). $\square$

**推论 7.3（Confinement on the complete complex half-filled space）。**
Under Definition 7.1, for every integer $S\geq1$,

$$
\boxed{\quad K-E_H(2S)I\succeq
 g(H,2S)(I-P_{\mathrm{sym}}).\quad}
\tag{7.16}
$$

For every normalized complex vector $\phi\in\mathcal H_{mS}$,

$$
\|(I-P_{\mathrm{sym}})\phi\|^2
\leq\frac{\langle\phi,K\phi\rangle-E_H(2S)}{g(H,2S)}.
\tag{7.17}
$$

Proof. On $\operatorname{ran}P_{\mathrm{sym}}$, the left side of
(7.16) is nonnegative by the definition of the actual full-space
minimum. On $\ker P_{\mathrm{sym}}$, it is at least $g(H,2S)I$
by (7.1). These orthogonal reducing subspaces have no cross terms.
Adding their quadratic forms proves (7.16) for arbitrary complex
superpositions, equivalently for all the local-spin sectors and every
multiplicity copy in (6.12). Taking its quadratic form on $\phi$ and
dividing by the positive number in (7.2) gives (7.17).

The graph and scale hypotheses of this conclusion differ from those
of Theorem 6.2: no flat mode is required here, while every induced
open neighborhood must be bipartite. Theorem 6.2 retains its eventual
explicit linear bound under its separate flat-mode assumption, without
this neighborhood restriction. No quantitative rate in $S$ follows
from the finite-spectrum strictness argument above. The present
statements concern equal even block sizes, unit weights and half
filling; the proof gives no corresponding theorem for odd block sizes,
other fillings, weights or unequal blocks. Strictness beyond the
locally bipartite graph class requires a further argument. $\square$

## 追加锚（本行以下为增补区）
## 8. Strict symmetry for odd blocks at exact half filling

**定义 8.1（Odd blocks and the unchanged carrier）。** Let $H$ satisfy
Definition 7.1's graph hypotheses, and require its order $m\geq2$ to be
even. Let $s=2S\geq3$ be odd, so $S\in\tfrac12+\mathbb Z$ and
$S\geq3/2$. Use $B_i,\Omega,G_s$, the complete complex Boolean space
$\mathcal H_k$, positive token adjacency $K=K_k$, and the original
$P_{\mathrm{sym}}$ of Definitions 1.1–1.2, with the integer
$k=ms/2=mS$. Define

$$
E_H(s)=\lambda_{\min}(K),\qquad
g(H,s)=\lambda_{\min}(K|_{\ker P_{\mathrm{sym}}})-E_H(s).
\tag{8.1}
$$

These are full-space energies. Block permutations commute with $K$,
so the two projection subspaces reduce it. No flat-mode hypothesis is
imposed. The nonsymmetric space is nonempty, as also follows from the
spin sectors in the proof below.

**定理 8.2（All odd scales on the full complex half-filled space）。**
Under Definition 8.1,

$$
\begin{aligned}
\ker(K-E_H(s)I)&\subseteq\operatorname{ran}P_{\mathrm{sym}},
&g(H,s)&>0,\\
K-E_H(s)I&\succeq g(H,s)(I-P_{\mathrm{sym}}).
\end{aligned}
\tag{8.2}
$$

Consequently every normalized complex $\phi\in\mathcal H_{mS}$ satisfies

$$
\|(I-P_{\mathrm{sym}})\phi\|^2
\leq\frac{\langle\phi,K\phi\rangle-E_H(s)}{g(H,s)}.
\tag{8.3}
$$

Proof. Write $E=E_H(s)$. The Boolean chain construction
(6.6)–(6.8) applies to every integer block size $s$: its starting rank
$t$ is an integer in $0,\ldots,\lfloor S\rfloor$, while its spin is
$J=S-t$. Thus here every local spin belongs to
$\{1/2,3/2,\ldots,S\}$, with multiplicity
$r_s(t)=\binom st-\binom s{t-1}$. Retaining all these copies gives

$$
\begin{aligned}
\mathcal X_t&=\left\{x\in(\tfrac12+\mathbb Z)^m:
 |x_i|\leq S-t_i,\ \sum_i x_i=0\right\},\\
\mathcal H_{mS}&\cong
\bigoplus_{t\in\{0,\ldots,\lfloor S\rfloor\}^m}
\ \bigoplus_{\alpha_i=1,\ldots,r_s(t_i)}\ell^2(\mathcal X_t).
\end{aligned}
\tag{8.4}
$$

The ladder coefficients are exactly (6.10), now at half-integer $J,x$;
$Z_i|x\rangle=x_i|x\rangle$ and
$K_{\boldsymbol J}=\sum_{\{i,j\}\in E(H)}
(J_i^+J_j^-+J_i^-J_j^+)$. Every $\mathcal X_t$ is nonempty: choose
$m/2$ coordinates $1/2$ and $m/2$ coordinates $-1/2$.
$P_{\mathrm{sym}}$ selects precisely $t=0$. Taking $t_1=1$ and all
other $t_i=0$ gives a nonempty nonsymmetric sector, since
$S-1\geq1/2$ and $r_s(1)=s-1>0$.
The source parameter maps are Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
$n=s$, starting rank $t_i$, up operator $J_i^+=L_i^*$; and Feinsilver,
[§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $s-2t_i=2J_i$. The orthogonal decomposition and its
multiplicities are those supplied representations, not additional
symmetry assumptions on vectors. By (2.4) the operator is ordinary
positive adjacency, with each edge equal to $2(X_iX_j+Y_iY_j)$;
compare Apte–Parekh–Sud,
[v3, Definition 1 and §3.2](https://arxiv.org/html/2506.03441v3).
Their shifted XY block $WI/2-K$ is a different operator.

We use the published nonstrict comparison of
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal local spin $s_p$ is $S$, variable spin $t_p$ is $J_p$,
$M=0$, and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
Its half-integer base case is needed here. In detail, fix the other
half-integer spins and let $\eta_j$ be the minimum at total magnetic
coordinate zero with spin $j$ at $p$. These spaces are nonempty by the
balanced $\pm1/2$ choices above. Adjoining a spin-one pair in
$|1,0\rangle$ to a ground vector $f_j$ preserves total magnetization
and energy: the pair has zero expectation of all three spin components.
The decomposition of $j\otimes1$ is $3/2\oplus1/2$ for $j=1/2$,
and $(j+1)\oplus j\oplus(j-1)$ for $j\geq3/2$.
The squared spin-$(j+1)$ projection at magnetic coordinate $x$ is

$$
\frac{2\binom{2j}{j+x}}{\binom{2j+2}{j+x+1}}
=\frac{(j+1)^2-x^2}{(j+1)(2j+1)}>0.
\tag{8.5}
$$

This is the same symmetric-subset projection as (7.4): $2j$ and
$j+x$ are integers even when $j,x$ are half-integers. Distinct $x$
have orthogonal images, so the projection is nonzero for every
nonzero entangled $f_j$, including endpoint weights. At $j=1/2$ the
other projected contribution has energy at least $\eta_{1/2}$; hence
the nonzero $3/2$ contribution has energy at most $\eta_{1/2}$.
Inductively, the $j$ and $j-1$ contributions have energies at least
$\eta_j$ when $\eta_{j-1}\geq\eta_j$. Their weighted average with
the $j+1$ contribution equals $\eta_j$, proving
$\eta_{j+1}\leq\eta_j$. This consumes the cited nonstrict comparison;
it does not exclude equality or claim every ground vector maximal.

The additional local argument is parity-sensitive. Let $G$ be a
nonempty bipartite graph with an even number of vertices, each carrying
this same half-integer spin $S\geq3/2$. We show that $K_G$ has a
total-zero ground vector not killed by both total ladders. If $G$ has
an edge, more strongly no total-zero ground vector is a total singlet.
Suppose otherwise that $v$ is such a normalized singlet ground vector,
with eigenvalue $e$. The singlet rotation calculation (7.6)–(7.7)
uses no integrality: putting
$T_\alpha=\sum_{\{i,j\}\in E(G)}J_i^\alpha J_j^\alpha$ gives

$$
T_zv=(e/4)v,\qquad
T_z|x\rangle=q_G(x)|x\rangle,\qquad
q_G(x)=\sum_{\{i,j\}\in E(G)}x_ix_j.
\tag{8.6}
$$

Indeed rotation of $2(T_x+T_y)v=ev$ gives the corresponding equations
with $x,z$ and $y,z$; add the last two and subtract the first.
Choose a connected component $C$ with an edge, let
$D=V(G)\setminus C$, and set
$\epsilon_C=0$ if $|C|$ is even and $\epsilon_C=1/2$ if $|C|$ is odd.
The reduced density $\rho_C$ of a total singlet is rotation-invariant.
In its irreducible decomposition it is $\bigoplus_q I_{V_q}\otimes A_q$,
$A_q\succeq0$. All $q$ are integers for even $|C|$ and half-integers
for odd $|C|$: the central $2\pi$ rotation acts by $(-1)^{|C|}$.
Every such $V_q$ contains weight $\epsilon_C$. Therefore

$$
\operatorname{tr}(\rho_C\mathbf1_{Z_C=\epsilon_C})
=\sum_q\operatorname{tr}A_q>0,
\qquad
\sum_q(2q+1)\operatorname{tr}A_q=1.
\tag{8.7}
$$

Here the finite spin decomposition and scalar action on irreducibles
are the same classical unitary representation algebra used in
(6.6)–(6.12) and (7.8). Projecting $v$ onto $Z_C=\epsilon_C$ gives
a nonzero vector $w$ with $Z_D=-\epsilon_C$. No zero weight on an odd
component is used.

On the $\epsilon_C$ slice of $C$, the sign
$(-1)^{\sum_{i\in A_C}(S+x_i)}$, for a bipartition side $A_C$,
conjugates $K_C$ to $-K_C$. Its exponent is an integer.
The configuration graph of that slice is connected by the argument
in §7: the independent $2S$-blow-up of connected $C$ is connected,
its edge transpositions connect all subsets of cardinality
$|C|S+\epsilon_C$, and their block-occupancy quotient is precisely
the allowed spin moves. All allowed coefficients are positive.
Thus Perron–Frobenius and the sign conjugation give a one-dimensional
least eigenspace, spanned by a vector $u_C$ nonzero at every allowed
configuration. Let $e_C(\epsilon_C),e_D(-\epsilon_C)$ be the two
slice minima. The second slice is nonempty because $w\ne0$.
Their tensor product is in the original total-zero space, so
$e\leq e_C(\epsilon_C)+e_D(-\epsilon_C)$. Conversely $w$ is still
an eigenvector of $K_C+K_D$ with eigenvalue $e$, giving the reverse
inequality. Hence $w=u_C\otimes w_D$ with $w_D\ne0$.
For empty $D$, its space is $\mathbb C$, its operator is zero, and
necessarily $\epsilon_C=0$; this includes $C=G$.

Projection commutes also with $T_z$. Fix a configuration $y$ of $D$
with $w_D(y)\ne0$. Equation (8.6) and full support of $u_C$ force
$q_C(x)+q_D(y)=e/4$ for every configuration of $C$ of weight
$\epsilon_C$. This is impossible. Choose $x_i\in\{-1/2,1/2\}$
with sum $\epsilon_C$, and an edge $\{a,b\}$ of $C$. The three
configurations $x$, $x+h$, $x-h$, $h=e_a-e_b$, all have this same
weight and all coordinates in $[-S,S]$, even at $S=3/2$. Since the
graph is simple and this edge has weight one,

$$
q_C(x+h)+q_C(x-h)-2q_C(x)=-2.
\tag{8.8}
$$

Every other edge contributes only a constant or a linear term in the
shift, which cancels. Thus $q_C$ cannot be constant on this slice,
contradicting (8.6). This proves the singlet obstruction for edged
$G$, including disconnected $G$ and isolates.
If $G$ is edgeless, take the product vector with half its sites at
$1/2$ and half at $-1/2$. It is a total-zero ground vector and its
total raising norm squared is
$\sum_i(S-x_i)(S+x_i+1)>0$: the singly raised product vectors are
orthogonal and each coefficient is positive. This proves the required
choice for every nonempty even-order bipartite $G$.

Suppose now a sector $t\ne0$ in (8.4) has minimum $E$. Choose $p$
with $J_p<S$. The nonstrict comparison increases all other spins to
$S$ without increasing the minimum. All resulting sectors occur in
the same original Boolean carrier, so none has minimum below $E$;
there is a ground vector with spin $J_p$ at $p$ and $S$ elsewhere.
As in (7.11)–(7.15), realize the spin at $p$ by its symmetric
$2J_p$ auxiliaries and $S-J_p$ fixed singlet pairs. This is an
intertwining isometry into the actual $2S$ coordinates at $p$,
preserving magnetic coordinates and energy; the remaining symmetric
auxiliaries can be arbitrarily entangled with the other sites.
Since $S-J_p$ is a positive integer, choose one pair and write the
resulting normalized ground vector as $\Psi=|0,0\rangle\otimes f$.
All other pairs remain fixed. Write

$$
A=N_H(p),\qquad R=[m]\setminus(\{p\}\cup A),\qquad
B^\pm=\sum_{i\in A}J_i^\pm.
\tag{8.9}
$$

The neighborhood $A$ is nonempty. Replacing just the chosen pair by
$|1,0\rangle$ gives a unit vector $\Theta$ in the same
$\mathcal H_{mS}$ with Rayleigh quotient $E$: both pair states have
magnetic coordinate zero and zero spin expectation, and there are no
intrablock interactions. Equality at the full-space minimum makes
$\Theta$ a ground vector. The remaining operator satisfies
$K^{\mathrm{rem}}f=Ef$, and the orthogonal pair components give

$$
0=(K-E)\Theta
=\sqrt2|1,1\rangle\otimes B^-f
+\sqrt2|1,-1\rangle\otimes B^+f.
\tag{8.10}
$$

Thus $B^-f=B^+f=0$. Their commutator gives $Z_Af=0$, and the common
ladder kernel is precisely the total-singlet space $\mathcal S_A$.
If $|A|$ is odd, every magnetic weight on $A$ is a half-integer,
so $Z_A$ has no kernel, an immediate contradiction. Hence only even
$|A|$ remains; $f\in\mathcal S_A\otimes\mathcal H_{pR,0}$, where
$\mathcal H_{pR,0}$ denotes the actual remaining auxiliaries at $p$
and sites in $R$ with their joint magnetic coordinate zero.

For singlets on $A$, sandwiching any single-site spin component
between the singlet projections gives zero, since its three
components transform as a vector under simultaneous rotations of
$A$. This is exactly the singlet matrix-element argument of §7,
valid also for half-integer site spins and entangled $f$.
All interactions crossing from $A$ therefore have zero expectation.
There are no edges from $p$ to $R$, so

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{8.11}
$$

Since $H[A]$ is bipartite of nonzero even order, the local argument
above supplies a unit ground vector $u_A$ of $K_A$ on $Z_A=0$,
with energy $e_A$, not killed by both $B^\pm$.
Let $\rho_{pR}$ be the reduced density of this same $f$, retaining
the fixed other pairs at $p$. It is supported on
$\mathcal H_{pR,0}$. The product density

$$
\rho=|0,0\rangle\langle0,0|\otimes
 |u_A\rangle\langle u_A|\otimes\rho_{pR}
\tag{8.12}
$$

belongs to the original $\mathcal H_{mS}$, with all original blocks
and auxiliaries. Each $\langle u_A,J_i^\pm u_A\rangle=0$ because
$u_A$ has definite $Z_A=0$. Consequently its crossing interactions
have zero expectation, and

$$
\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{8.13}
$$

The opposite inequality holds by the full-space definition of $E$,
so equality holds. Spectrally decompose $\rho_{pR}$ into unit vectors
$h$ of its actual joint zero-weight support, with positive weights.
Every $|0,0\rangle\otimes u_A\otimes h$ has energy at least $E$;
their average is $E$, so each is a ground vector. Applying the same
pair replacement (8.10) to any one forces
$B^-u_A=B^+u_A=0$, a contradiction. This comparison retained the
same reduced $pR$ state, rather than choosing separate magnetization
optimizers. For $R=\varnothing$, its tensor factor is $\mathbb C$
and $K_R=0$; the remaining auxiliaries at $p$ are still retained.
If their required zero-weight space were empty, the preceding nonzero
$f$ would already be impossible. In particular an odd-order $A$
with empty $R$, including $m=2$, is covered by the earlier parity
contradiction.

Thus every nonsymmetric sector in (8.4), with every multiplicity
copy, has minimum strictly above $E$. The decomposition reduces both
$K$ and $P_{\mathrm{sym}}$, so all complex ground vectors have only
$t=0$ components. The nonempty finite-dimensional restriction to
$\ker P_{\mathrm{sym}}$ has minimum strictly above $E$, giving
$g(H,s)>0$. On $\operatorname{ran}P_{\mathrm{sym}}$, $K-EI\succeq0$;
on its orthogonal complement, $K-EI\succeq g(H,s)I$. Adding these
quadratic forms proves (8.2) on arbitrary complex superpositions,
and unit normalization gives (8.3).

The added inference relative to §7 is the half-integer neighborhood
obstruction (8.6)–(8.8), with the odd-neighborhood parity exclusion,
and its use in the same-realization replacement (8.11)–(8.13).
The Boolean representations, nonstrict comparison and singlet/product
mechanisms retain their supplied status. For the latter mechanisms,
also compare Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2):
their $R^i$ is the spin-one sum of a pair of spin-half auxiliaries;
their negative Hamiltonian with nonnegative product couplings in the
1 and 3 directions does not supply positive-adjacency strictness on
a possibly nonbipartite $H$. The present conclusion is a
`repo-derived` extension consuming those intermediates. It concerns
all odd $s\geq3$ at exact half filling for even $m$ under the stated
local graph hypothesis. It supplies no quantitative rate, nor an
extension to weights, unequal blocks, other fillings, odd-order
rounded filling or a broader graph class. $\square$

## 追加锚（本行以下为增补区）

## 9. Odd-scale confinement under a vertexwise alternative

**定义 9.1（Odd degree or a bipartite open neighborhood）。** Let $H$
be a finite simple unit-weight graph of even order $m\geq2$, with no
isolated vertices, such that

$$
\text{for every }p\in[m],\qquad
\deg_H(p)\text{ is odd}\quad\text{or}\quad H[N_H(p)]\text{ is bipartite}.
\tag{9.1}
$$

There is no neighborhood condition at an odd-degree vertex. Induced
neighborhoods may have isolates, be edgeless, or be disconnected.
Let $s\geq3$ be any odd integer, $S=s/2$, and $k=mS$. Use the original
$B_i,\Omega,H[\overline{K_s}],\mathcal H_k,K=K_k$ and
$P_{\mathrm{sym}}$ of Definitions 1.1–1.2. In particular $\mathcal H_k$
is the complete complex Boolean $k$-token space, and $K$ is ordinary
positive adjacency. Put

$$
E=\lambda_{\min}(K),\qquad
\mathcal N=\ker P_{\mathrm{sym}},\qquad
g=\lambda_{\min}(K|_{\mathcal N})-E.
\tag{9.2}
$$

The existence of the last minimum is part of the following theorem.

**定理 9.2（Full-space confinement for the vertexwise alternative）。**
For every $H,s$ of Definition 9.1, $\mathcal N$ is nonzero and reduces
$K$, and

$$
\ker(K-EI)\subseteq\operatorname{ran}P_{\mathrm{sym}},\qquad
g>0,\qquad
K-EI\succeq g(I-P_{\mathrm{sym}}).
\tag{9.3}
$$

Every normalized complex $\phi\in\mathcal H_{mS}$ consequently satisfies

$$
\|(I-P_{\mathrm{sym}})\phi\|^2
\leq\frac{\langle\phi,K\phi\rangle-E}{g}.
\tag{9.4}
$$

Proof. We use the supplied chain decomposition (6.6)–(6.10), (8.4),
the half-integer nonstrict comparison proved before (8.6), and the
bipartite neighborhood obstruction (8.6)–(8.8), including its edgeless
case. Their respective hypotheses are important: the decomposition
and nonstrict comparison require no bipartiteness, whereas that local
obstruction concerns a nonempty even-order bipartite graph with the
same spin $S\geq3/2$ at all its vertices. We apply the local obstruction
only to such a graph, not to $H$ itself.

Explicitly, every block has spins $J_i=S-t_i$, with integer
$0\leq t_i\leq\lfloor S\rfloor$ and multiplicity
$r_s(t_i)=\binom{s}{t_i}-\binom{s}{t_i-1}$. In every tensor of chains
retain the entire zero-total-weight slice $\mathcal X_t$ of (8.4).
The operator on it is

$$
K_{\boldsymbol J}=\sum_{\{i,j\}\in E(H)}
(J_i^+J_j^-+J_i^-J_j^+),\qquad
Z_i|x_i\rangle=x_i|x_i\rangle,
\tag{9.5}
$$

with all the endpoint coefficients of (6.10). The source maps for
these classical representations remain Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
$n=s$, starting rank $t_i$, raising operator $L_i^*=J_i^+$; and
Feinsilver, [§§3–4, (16), Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $s-2t_i=2J_i$. These supply orthogonality and every
multiplicity, as used in §§6–8. Equation (2.4) identifies (9.5) with
$K$; each edge is $2(X_iX_j+Y_iY_j)$. In the conventions of
Apte–Parekh–Sud, [v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
this is adjacency $A(F_k(H[\overline{K_s}]))$, rather than their
shifted XY block $WI/2-A(F_k(H[\overline{K_s}]))$.

Each slice is nonempty: take $m/2$ weights $1/2$ and $m/2$ weights
$-1/2$, since every $J_i\geq1/2$. The unique chains with all $t_i=0$
are exactly $\operatorname{ran}P_{\mathrm{sym}}$. Taking $t_1=1$
and the other $t_i=0$ gives a nonzero orthogonal sector, because
$S-1\geq1/2$ and $r_s(1)=s-1>0$. Block permutations commute with
$K$, so $P_{\mathrm{sym}}$ and its orthogonal complement reduce $K$.
Thus $\mathcal N$ is nonzero and its finite-dimensional minimum exists.

For the nonstrict comparison the exact primary parameters are
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412):
maximal spin $s_p=S$, variable spin $t_p=J_p$, total magnetization
$M=0$, and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
The fixed-$M$ conclusion we consume is only that increasing one local
spin by one does not increase the slice minimum, with all other spins
fixed. Its proof in §8 uses the zero-weight triplet $|1,0\rangle$,
not a polarized triplet: it preserves $M$ and has zero Cartesian
expectations. The upper-spin projection (8.5) is positive at every
weight, including endpoints, so projection and induction work also
for entangled vectors, starting at $J_p=1/2$. No exclusion of equality
is imported from this comparison.

Suppose a nonsymmetric sector has minimum $E$, and choose $p$ with
$J_p<S$. Increase all other spins to $S$ using that comparison.
Each resulting sector occurs in the same original $\mathcal H_{mS}$,
so its minimum cannot fall below $E$. We obtain a normalized ground
vector with spin $J_p$ at $p$ and $S$ elsewhere. Realize the spin at
$p$ by the symmetric $2J_p$ auxiliaries and $S-J_p$ fixed singlet
pairs, as in the proof of Theorem 8.2. This is an intertwining isometry
into the original $s$ Boolean coordinates at $p$, preserving magnetic
weight and the energy. Choose one pair and write the vector as
$\Psi=|0,0\rangle\otimes f$, retaining all other pairs in $f$.
The remaining auxiliaries may be arbitrarily entangled with other sites.
Set

$$
A=N_H(p),\qquad R=[m]\setminus(\{p\}\cup A),\qquad
B^\pm=\sum_{i\in A}J_i^\pm,\qquad Z_A=\sum_{i\in A}Z_i.
\tag{9.6}
$$

Here $A\ne\varnothing$. Release just the chosen singlet into
$|1,0\rangle$, giving $\Theta=|1,0\rangle\otimes f$ in the same
$\mathcal H_{mS}$. Both pair states have zero weight and zero spin
expectations. There are no intrablock edges, so
$\langle\Theta,K\Theta\rangle=E$. Equality in the Rayleigh bound at
the actual full-space minimum implies $K\Theta=E\Theta$.
The operator $K^{\mathrm{rem}}$ with this pair omitted satisfies
$K^{\mathrm{rem}}f=Ef$, since the pair ladders annihilate the singlet.
Consequently the same original operator gives

$$
0=(K-EI)\Theta
=\sqrt2\,|1,1\rangle\otimes B^-f
 +\sqrt2\,|1,-1\rangle\otimes B^+f.
\tag{9.7}
$$

Orthogonality yields $B^-f=B^+f=0$. Their commutator
$[B^+,B^-]=2Z_A$ gives $Z_Af=0$. Since all sites of $A$ carry the
half-integer spin $S$, every weight of $Z_A$ is in
$|A|/2+\mathbb Z$. If $\deg_H(p)=|A|$ is odd, zero is absent and
$f=0$, a contradiction. This branch uses no edges of $H[A]$.

It remains that $|A|$ is even. Condition (9.1) now implies that
$H[A]$ is bipartite. The common kernel of the total ladders on $A$
is its total-singlet space $\mathcal S_A$, as used in §8: on a spin-$q$
irreducible both ladder norms vanish only for $q=0$. Thus $f$ is
supported on $\mathcal S_A\otimes\mathcal H_{pR,0}$, where the second
factor comprises the actual remaining auxiliaries at $p$ and all
sites of $R$, jointly at weight zero. Sandwiching any single-site spin
component on $A$ between singlet projections gives zero: simultaneous
rotations fix both singlets, while those three matrix elements transform
as a vector, whose only rotation-invariant value is zero.
All crossing interactions therefore have zero expectation in $f$.
There are no edges from $p$ to $R$, and hence

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{9.8}
$$

Here $K_A,K_R$ are the induced operators. The remaining factors at
$p$ are retained even if $R$ is empty.

Apply precisely the local conclusion proved in §8 around (8.6)–(8.8):
a nonempty even-order bipartite graph, with uniform half-integer
spin $S\geq3/2$, has a normalized zero-weight ground vector $u_A$
not killed by both total ladders. Write its energy as $e_A$.
For an edged graph, the supplied proof excludes any singlet ground
vector, using a connected-component slice of weight $0$ or $1/2$
according to its parity and the finite difference (8.8). Thus it
includes odd components and isolates. For an edgeless graph the
balanced product of weights $\pm1/2$ has positive total raising
norm, so it supplies the same choice. These are the existing local
obstruction and endpoint argument, used here with $G=H[A]$; no new
local-spin assertion is needed.

Let $\rho_{pR}$ be the reduced density of this same $f$ on the
remaining factors. It is supported on $\mathcal H_{pR,0}$. In the
original carrier form

$$
\rho=|0,0\rangle\langle0,0|\otimes
 |u_A\rangle\langle u_A|\otimes\rho_{pR}.
\tag{9.9}
$$

The other fixed pairs at $p$ remain in $\rho_{pR}$. Definite zero
weight gives $\langle u_A,J_i^\pm u_A\rangle=0$ for every $i\in A$,
so every crossing edge has zero expectation in this product density.
Using the minimum $e_A$ on $Z_A=0$ and (9.8),

$$
\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{9.10}
$$

The full-space minimum gives the reverse inequality. Decompose
$\rho_{pR}$ spectrally into unit vectors $h$ with positive weights,
all in its actual zero-weight support. Each
$|0,0\rangle\otimes u_A\otimes h$ has energy at least $E$, and their
average is $E$, so each is a ground vector. Releasing its same pair
and applying (9.7) forces $B^-u_A=B^+u_A=0$, contradicting its choice.
For $R=\varnothing$, $K_R=0$ on its one-dimensional factor; the
remaining auxiliaries at $p$ still belong to $h$. If the required
joint zero-weight space were empty, the original nonzero $f$ would
already be impossible. No componentwise half-filling was imposed.

We have excluded $E$ from every nonsymmetric sector, retaining every
multiplicity copy. The orthogonal decomposition (8.4) therefore puts
every complex ground vector in $t=0$, including arbitrary entangled
superpositions. Finite dimension and $\mathcal N\ne0$ now give $g>0$.
On $\operatorname{ran}P_{\mathrm{sym}}$, $K-EI\succeq0$; on
$\mathcal N$, $K-EI\succeq gI$. Their reducing decomposition has no
cross terms, proving (9.3). Taking its quadratic form on a unit
$\phi$ gives (9.4), using this same $E$ and this same $g$.

The added `repo-derived` inference relative to §8 is the graph
hypothesis (9.1): the published odd-neighborhood exclusion already
dispenses with bipartiteness at odd-degree vertices. The representations,
nonstrict comparison, parity exclusion, local obstruction and strict
replacement all retain their roles from §§6–8. None of these steps
requires $H$ connected or a flat least mode. The universal assertion
for arbitrary even-order $H$ without isolates at every scale $s\geq2$
remains unresolved here. This theorem adds no even-scale assertion;
at odd scales, an even-degree vertex with a nonbipartite neighborhood
is outside its sufficient condition. Failure of that condition is not
a counterexample to confinement. The finite-spectrum argument gives
no quantitative gap or rate. $\square$

**命题 9.3（Complete graph and odd-rim wheels outside the locally
bipartite class）。** All conclusions of Theorem 9.2 hold for $H=K_4$
and for the wheel obtained by joining one hub to every vertex of
$C_{2r+1}$, for every integer $r\geq2$, at every odd $s\geq3$.
These graphs satisfy (9.1) and have even order and no isolates, but
are outside the graph class of Definition 7.1 and Theorem 8.2.

Proof. In $K_4$, $m=4$ and every vertex has degree $3$, so the first
alternative in (9.1) holds everywhere. Every induced open neighborhood
is $K_3$, whose three-cycle is not bipartite. Thus the locally
bipartite condition fails at every vertex.

For the wheel, label the rim cyclically by $v_i$, $i\in\mathbb Z/(2r+1)$,
and denote the hub by $c$. Its order is $2r+2$, which is even.
The hub has odd degree $2r+1$, and every rim vertex has degree $3$;
there are no isolates, and (9.1) again holds everywhere without any
neighborhood restriction. The induced neighborhood of $c$ is exactly
$C_{2r+1}$, which is not bipartite because colors would alternate and
fail to close after an odd number of edges. At a rim vertex $v_i$,
the neighborhood is $\{c,v_{i-1},v_{i+1}\}$. Since $2r+1\geq5$,
the two rim neighbors are distinct and nonadjacent, so this induced
graph is the bipartite path $v_{i-1}-c-v_{i+1}$. The hub's
neighborhood suffices to exclude the wheel from the locally bipartite
class. Applying Theorem 9.2 on the complete original carrier gives
all asserted ground-vector, gap, operator and mass conclusions for
each of these graphs, including $s=3$. These applications do not
impose a neighborhood restriction at the hub or at any other
odd-degree vertex. $\square$

## 追加锚（本行以下为增补区）
## 10. Every even scale for balanced complete multipartite graphs

**定义 10.1（Labelled parts and the original half-filled operator）。**
Let $[m]=C_1\sqcup\cdots\sqcup C_q$ be any labelled partition, with
$p_a=|C_a|\geq1$, and let $H=K_{p_1,\ldots,p_q}$: distinct vertices
are adjacent exactly when they belong to different parts. Assume

$$
q\geq4,\qquad m=\sum_{a=1}^q p_a\text{ is even},\qquad
2\max_a p_a\leq m.
\tag{10.1}
$$

For every integer $S\geq1$, set $s=2S$, $k=mS$, and retain the blocks
$B_i$, graph $H[\overline{K_{2S}}]$, complete complex Boolean space
$\mathcal H_{mS}$, ordinary positive adjacency $K=K_{mS}$ and original
within-$B_i$ projection $P_{\mathrm{sym}}$ of Definitions 1.1–1.2.
Write

$$
E=\lambda_{\min}(K),\qquad \mathcal N=\ker P_{\mathrm{sym}},\qquad
L_a=p_aS.
\tag{10.2}
$$

Part membership in $C_a$ is distinct from membership in a Boolean block
$B_i$: the latter always has the original uniform size $2S$.

**定理 10.2（Strict full-space confinement for balanced multipartite
bases）。** Under Definition 10.1, $\mathcal N$ is nonzero and reduces
$K$. The number

$$
g=\lambda_{\min}(K|_{\mathcal N})-E
\tag{10.3}
$$

is defined and strictly positive, and

$$
\begin{aligned}
\ker(K-EI)&\subseteq\operatorname{ran}P_{\mathrm{sym}},\\
K-EI&\succeq g(I-P_{\mathrm{sym}}).
\end{aligned}
\tag{10.4}
$$

For every normalized complex $\phi\in\mathcal H_{mS}$, with no
symmetry assumption,

$$
\|(I-P_{\mathrm{sym}})\phi\|^2
\leq\frac{\langle\phi,K\phi\rangle-E}{g}.
\tag{10.5}
$$

All these statements use the same entire-carrier minimum $E$ in
(10.2), at every even $s\geq2$.

Proof. The orthogonal Boolean-chain decomposition (6.6)–(6.12) applies
without the flat-mode assumption of Definition 6.1. It retains each
integer spin $J_i=S-t_i$, $0\leq t_i\leq S$, with every multiplicity
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$, and the entire slice
$\sum_i x_i=0$, $-J_i\leq x_i\leq J_i$. Its ladder coefficients are
exactly (6.10), including their zero values at the endpoints. In each
copy the original operator is

$$
K_{\boldsymbol J}
=\sum_{\{i,j\}\in E(H)}(J_i^+J_j^-+J_i^-J_j^+)
=2\sum_{\{i,j\}\in E(H)}(X_iX_j+Y_iY_j).
\tag{10.6}
$$

Here $Z_i|x_i\rangle=x_i|x_i\rangle$,
$X_i=(J_i^++J_i^-)/2$, and $Y_i=(J_i^+-J_i^-)/(2i)$.
The $t=0$ chains are precisely $\operatorname{ran}P_{\mathrm{sym}}$.
The representation sources and their parameters are Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2), Boolean
rank $n=2S$, starting rank $t_i$, up operator $L_i^*=J_i^+$; and
Feinsilver, [§§3–4, (8)–(10), Proposition 4.3 and
§4.2.2](https://arxiv.org/pdf/1102.0368v2), principal number
$2S-2t_i=2J_i$. Equation (2.4) gives (10.6) on the original carrier.
In Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
this $K$ is $A(F_k(H[\overline{K_s}]))$; their XY block $WI/2-K$
is a different operator.

We first obtain a trial bound in that same carrier. Work temporarily
in its all-$J_i=S$ summand and define the collective spin of a graph
part by

$$
\boldsymbol T_a=\sum_{i\in C_a}(X_i,Y_i,Z_i),\qquad
\boldsymbol T=\sum_a\boldsymbol T_a,\qquad
\boldsymbol T_a^2=(T_a^x)^2+(T_a^y)^2+(T_a^z)^2.
\tag{10.7}
$$

The maximal part spin is $L_a=p_aS$: the tensor of the highest-weight
vectors has weight $L_a$ and generates a spin-$L_a$ chain. No larger
spin occurs because all weights are at most $L_a$. The finite unitary
spin decomposition therefore gives the operator bound
$\boldsymbol T_a^2\preceq L_a(L_a+1)I$ on the whole tensor product
of the $p_a$ spin-$S$ factors, not just on its maximal-spin chain.

We consume the classical Clebsch–Gordan rule
$V_u\otimes V_v\cong\bigoplus_{r=|u-v|}^{u+v}V_r$, with integer
steps, for spin representations $V_j$. Its normalization, triangle
range and orthogonality are recorded in
[NIST DLMF, (34.1.1), (34.2.1), (34.3.16)–(34.3.17)](https://dlmf.nist.gov/34.1).
For the integer spins here its relevant content can be seen directly:
the weight character of $V_j$ is $\chi_j(z)=\sum_{x=-j}^jz^x$,
and counting pairs of weights gives
$\chi_u(z)\chi_v(z)=\sum_{r=|u-v|}^{u+v}\chi_r(z)$.
For $u\geq v$ and weight $x\geq0$, both sides have coefficient
$\min\{2v+1,u+v-x+1\}$ when $x\leq u+v$, and zero otherwise;
negative weights give the same counts. Complete reducibility and the
linear independence of these characters, obtained by comparing their
largest powers, give precisely that decomposition.

In particular, for a nonempty list of nonnegative integer spins with
sum $U$ and maximum $M$, the spins occurring in their tensor product
are all integers in

$$
[\max\{0,2M-U\},U].
\tag{10.8}
$$

Here is the endpoint verification needed for its use. For one spin
this is its singleton interval. If the previous interval is $[l,U]$
and another spin is $v$, the two-factor rule gives the union of
$[|r-v|,r+v]$ over its integer $r$. Consecutive such intervals overlap
or have consecutive integer endpoints, so there is no missing integer.
The greatest endpoint is $U+v$; the least is the integer distance from
$v$ to $[l,U]$, namely $\max\{0,l-v,v-U\}$. Substituting
$l=\max\{0,2M-U\}$ gives
$\max\{0,2\max(M,v)-(U+v)\}$, proving (10.8) by induction.
This is the classical coupling rule used as an intermediate.

By (10.1), the integer spins $L_1,\ldots,L_q$ satisfy
$2\max_aL_a\leq\sum_aL_a$. Thus (10.8) supplies a unit total
singlet $v$ in $\bigotimes_a V_{L_a}$. Each factor here is an actual
maximal-part-spin subspace of the original all-$S$ summand. Its
embedding into the Boolean space intertwines the collective operators.
Since a singlet has total $Z=0$, this $v$ belongs to the original
$\mathcal H_{mS}$, with no alteration of filling or blocks.

A total singlet is fixed by simultaneous spin rotations. Consequently
for any two different parts the expectations of
$T_a^xT_b^x$, $T_a^yT_b^y$ and $T_a^zT_b^z$ are equal: rotations
interchanging the axes conjugate one product into another. Since
$H$ has exactly all cross-part edges,

$$
\begin{aligned}
\langle v,Kv\rangle
&=\frac43\sum_{a<b}\langle v,\boldsymbol T_a\mathbin\cdot
 \boldsymbol T_bv\rangle\\
&=\frac23\left\langle v,
 \left(\boldsymbol T^2-\sum_a\boldsymbol T_a^2\right)v\right\rangle
=-\frac23\sum_a L_a(L_a+1).
\end{aligned}
\tag{10.9}
$$

Only Rayleigh's inequality is inferred:

$$
E\leq U_*:=-\frac23\sum_aL_a(L_a+1).
\tag{10.10}
$$

Neither $v$ being an eigenvector of $K$ nor equality in (10.10) is
needed or asserted.

Suppose now that some nonsymmetric sector has minimum $E$. Choose a
vertex $p$ with $J_p<S$. Apply the nonstrict fixed-zero-magnetization
comparison (7.4)–(7.5) to increase every other local spin to $S$.
It requires only integer spins and the bilinear operator (10.6), not
bipartiteness or a flat mode. Each resulting sector occurs in the
same original Boolean carrier, so its minimum is at least $E$ and
hence remains exactly $E$. We obtain a unit ground vector with spin
$J_p$ at $p$ and spin $S$ at every other vertex. Every intermediate
zero-weight slice is nonempty, since each integer-spin factor contains
weight zero.

The primary comparison is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization
paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal on-site spin $s_p$ is $S$, variable on-site spin $t_p$
is our $J_p$, $M=0$, and
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
The fixed-$M$ trial uses the zero-weight triplet $|1,0\rangle$.
Its nonzero upper-spin projection at every weight, including endpoints
and entangled inputs, is (7.4); the induction in §7 proves the
nonstrict comparison used here. No equality exclusion is supplied
by that comparison.

Use the original-carrier singlet-pair realization from §7: realize
the spin $J_p$ by the symmetric space on $2J_p$ of the original
$2S$ auxiliaries at $p$, tensored with $S-J_p$ disjoint singlet pairs.
It intertwines every collective spin component and preserves centered
occupancy. This realizes the required sector even if the initial
minimum came from another multiplicity copy, since (6.12) gives the
same operator on every such copy. Choose one fixed pair and write the
ground vector as $\Psi=|0,0\rangle\otimes f$, where $\|f\|=1$.
The other fixed pairs, if any, remain in $f$, along with arbitrary
entanglement between the remaining auxiliaries and other vertices.
Write

$$
p\in C_a,\qquad A=[m]\setminus C_a=N_H(p),\qquad
B^\pm=\sum_{i\in A}J_i^\pm,\qquad Z_A=\sum_{i\in A}Z_i.
\tag{10.11}
$$

Replacing just this pair by $|1,0\rangle$ gives
$\Theta=|1,0\rangle\otimes f$ in the same $\mathcal H_{mS}$.
Both pair states have weight zero and zero expectations of all spin
components. There are no intrablock edges, so
$\langle\Theta,K\Theta\rangle=E$. For a finite Hermitian operator,
equality at its actual minimum makes the vector a ground vector:
$\sum_\lambda(\lambda-E)|c_\lambda|^2=0$ in an orthonormal
eigenbasis forces all components with $\lambda>E$ to vanish.
Omitting the pair gives $K^{\mathrm{rem}}f=Ef$, because its collective
operators annihilate the singlet. The two orthogonal triplet components
therefore give the original-operator identity

$$
0=(K-EI)\Theta
=\sqrt2\,|1,1\rangle\otimes B^-f
 +\sqrt2\,|1,-1\rangle\otimes B^+f.
\tag{10.12}
$$

It follows that $B^-f=B^+f=0$ and, by their commutator, $Z_Af=0$.
Equivalently all three components of the total spin of $A$ annihilate
$f$, so simultaneous rotations on $A$ fix $f$. This is exactly the
singlet consequence of (7.12), before any use there of a bipartite
neighborhood. It remains valid with every other tensor factor retained.

For $b\ne a$ keep $\boldsymbol T_b$ from (10.7), acting on the
spin-$S$ sites in $C_b$. Let $K_A$ be the induced operator on $A$.
All edges incident to $C_a$ are accounted for by
$T_a^+B^-+T_a^-B^+$; after omitting the chosen pair the same formula
uses the remaining collective spin of $C_a$. This term annihilates
$f$, and there are no edges within $C_a$. Hence
$E=\langle f,K_Af\rangle$. Rotation invariance on $A$ and
$\sum_{b\ne a}\boldsymbol T_bf=0$ now give, on this same entangled
vector,

$$
\begin{aligned}
E
&=\frac43\sum_{\substack{b<c\\b,c\ne a}}
 \langle f,\boldsymbol T_b\mathbin\cdot\boldsymbol T_cf\rangle\\
&=-\frac23\sum_{b\ne a}\langle f,\boldsymbol T_b^2f\rangle\\
&\geq-\frac23\sum_{b\ne a}L_b(L_b+1)
=U_*+\frac23L_a(L_a+1)>U_*.
\end{aligned}
\tag{10.13}
$$

The part-spin bound used in the inequality holds on all part-spin
sectors and copies, so it imposes no further local symmetry within
$A$. The last inequality is strict because $p_a\geq1$ and $S\geq1$.
It contradicts (10.10). Thus no nonsymmetric sector has minimum $E$.
The additional strict inference is (10.9)–(10.13): the balanced
maximal-part singlet trial separates the full-space minimum from the
energy forced by the neighbor singlet. The Boolean representations,
classical spin coupling, nonstrict comparison and singlet release are
consumed intermediates. For the last construction also compare
Benassi–Lees–Ueltschi,
[v3, §4.3, (4.12)–(4.17) and Lemma 9](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the collective spin of one pair of spin-half auxiliaries;
their strictness concerns a negative Hamiltonian with nonnegative
product couplings in the 1 and 3 directions. It is not a strictness
result for the positive adjacency used here.

To finish, block permutations commute with $K$, so $P_{\mathrm{sym}}$
and $I-P_{\mathrm{sym}}$ reduce it. The latter has nonzero range:
take a nonconstant one-particle vector in one block, occupancy $2S-1$
in a second block, and occupancy $S$ in each remaining block.
This is a nonzero vector in $\mathcal N$ of total occupancy $mS$,
including $S=1$. The finite orthogonal decomposition (6.12), with
all multiplicities retained, has excluded $E$ from every summand of
$\mathcal N$. Therefore its spectral minimum is strictly above $E$,
which proves (10.3) and the ground-vector statement in (10.4), also
for arbitrary complex superpositions of sectors and copies. On
$\operatorname{ran}P_{\mathrm{sym}}$ one has $K-EI\succeq0$; on
$\mathcal N$ one has $K-EI\succeq gI$. Adding the quadratic forms
on these reducing subspaces proves (10.4) on the entire carrier.
Its quadratic form on a unit vector gives (10.5).

The proof uses the weak balance inequality in (10.1), including
$2\max p_a=m$, and includes all singleton parts $q=m$, unequal
parts and the minimum scale $s=2$. It supplies no quantitative value
of $g$ or exact formula for $E$. Theorems 6.2, 7.2, 8.2 and 9.2
retain their separate graph, flat-mode and scale hypotheses. Complete
multipartite graphs with two or three parts already have bipartite
open neighborhoods and are covered at even scales by §7; they are
not an added graph class here. Arbitrary $H$, unbalanced multipartite
parts, disconnected bases with only global filling, weights, other
fillings and odd scales are outside this sufficient theorem. Failure
of (10.1) is not a counterexample. The general arbitrary-$H$ confinement
problem remains unresolved here. $\square$

**命题 10.3（The labelled $K_4$ and $K_{3,1,1,1}$ applications）。**
Every labelled realization of $K_4$ and $K_{3,1,1,1}$ satisfies all
conclusions (10.3)–(10.5) at every even $s\geq2$, on its complete
original half-filled carrier. Both graphs lie outside Definition 7.1's
locally bipartite class.

Proof. For $K_4$ take its four singleton parts: $q=m=4$, every
$p_a=1$, and $2\max p_a=2\leq4$. For $K_{3,1,1,1}$ the four
nonempty labelled parts have sizes $3,1,1,1$, so $q=4$, $m=6$ and
$2\max p_a=6=m$. These are finite simple unit-weight graphs with
exactly the cross-part edges, even order and no isolates. Theorem 10.2
therefore applies to each at every integer $S\geq1$, with $k=4S$
and $k=6S$, respectively, and $s=2S$. It retains the original labels
and each original Boolean block; no identification of equal-sized
parts is involved.

More generally, in a complete multipartite graph with $q\geq4$,
the open neighborhood of a vertex in any part contains a triangle:
choose one vertex from each of three other nonempty parts. Its three
cross-part edges are present. A bipartite graph cannot contain this
triangle, so the induced neighborhood is not bipartite. This verifies
the failure of the locally bipartite hypothesis at every vertex of
both examples, independently of their labels. The applications use
the even-scale result just proved; the odd-scale statements of §9
retain their own hypotheses and conclusions. $\square$

## 追加锚（本行以下为增补区）
