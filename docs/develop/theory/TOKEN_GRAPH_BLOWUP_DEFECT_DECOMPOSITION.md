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
take a nonzero one-particle vector orthogonal to constants in one
block, occupancy $2S-1$ in a second block, and occupancy $S$ in each
remaining block. Their tensor product lies in $\mathcal N$ and has
total occupancy $mS$, including $S=1$. The finite orthogonal decomposition (6.12), with
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

## 11. Every even scale for unbalanced complete multipartite graphs

**定义 11.1（A dominant part and the unchanged full carrier）。** Let
$[m]=C_0\sqcup C_1\sqcup\cdots\sqcup C_r$ be a labelled partition,
$p_a=|C_a|\geq1$, and $H=K_{p_0,p_1,\ldots,p_r}$. Assume

$$
r\geq3,\qquad m=\sum_{a=0}^r p_a\text{ is even},\qquad
P=p_0>R=\sum_{a=1}^r p_a.
\tag{11.1}
$$

For every integer $S\geq1$, put $s=2S$, $N=ms$, $k=mS$, and use
exactly the complete complex Boolean space $\mathcal H_{mS}$, ordinary
positive token adjacency $K=K_{mS}$, original blocks $B_i$ of size
$2S$, and within-block permutation projection $P_{\mathrm{sym}}$ of
Definitions 1.1–1.2. Write

$$
E=\lambda_{\min}(K),\qquad \mathcal N=\ker P_{\mathrm{sym}},\qquad
L_a=p_aS,\qquad W=\sum_{a=1}^rL_a=RS.
\tag{11.2}
$$

A graph part $C_a$ consists of $p_a$ original Boolean blocks; none of
those blocks is replaced by a block of size $2L_a$.

**定理 11.2（Strict full-space separation with a dominant part）。**
Under Definition 11.1, $\mathcal N$ is nonzero and reduces $K$, and

$$
\begin{aligned}
\ker(K-EI)&\subseteq\operatorname{ran}P_{\mathrm{sym}},\\
g:=\lambda_{\min}(K|_{\mathcal N})-E&>0,\\
K-EI&\succeq g(I-P_{\mathrm{sym}}).
\end{aligned}
\tag{11.3}
$$

Every normalized complex $\phi\in\mathcal H_{mS}$ satisfies

$$
\|(I-P_{\mathrm{sym}})\phi\|^2
\leq\frac{\langle\phi,K\phi\rangle-E}{g}.
\tag{11.4}
$$

These conclusions hold at every integer $S\geq1$, with all local-spin
sectors, multiplicity copies and their arbitrary superpositions retained.

Proof. Use the complete Boolean-chain decomposition (6.6)–(6.12).
It requires no flat least mode: its integer local spins are
$J_i=S-t_i$, $0\leq t_i\leq S$, with every multiplicity
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$. In each copy retain
all weights $x_i\in\{-J_i,\ldots,J_i\}$ with $\sum_i x_i=0$ and
all coefficients of (6.10), including their endpoint zeros. Each slice
is nonempty because every integer spin contains weight zero. On it,

$$
K_{\boldsymbol J}
=\sum_{\{i,j\}\in E(H)}(J_i^+J_j^-+J_i^-J_j^+)
=2\sum_{\{i,j\}\in E(H)}(X_iX_j+Y_iY_j),
\tag{11.5}
$$

where $Z_i|x_i\rangle=x_i|x_i\rangle$ and
$X_i=(J_i^++J_i^-)/2$, $Y_i=(J_i^+-J_i^-)/(2i)$.
The all-$J_i=S$ summand is precisely
$\operatorname{ran}P_{\mathrm{sym}}$. The classical representation
parameters are Srinivasan, [Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
$n=2S$, starting rank $t_i$, up operator $L_i^*=J_i^+$; and
Feinsilver, [§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $2S-2t_i=2J_i$. The identification with the original
positive adjacency is (2.4). In Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
our $K$ is $A(F_k(H[\overline{K_s}]))$; their shifted XY operator
$W(G_s)I/2-K$, with $W(G_s)$ their total edge weight, is a
different operator.

First construct a trial in the actual all-$S$ summand. On that summand
let $\boldsymbol T_a=\sum_{i\in C_a}(X_i,Y_i,Z_i)$ and
$\boldsymbol T=\sum_a\boldsymbol T_a$. We use the classical coupling
rule and its full integer interval (10.8), proved within Theorem 10.2.
Its two-factor normalization, triangle range and orthogonality are
[NIST DLMF, (34.1.1), (34.2.1), (34.3.16)–(34.3.17)](https://dlmf.nist.gov/34.1).
For the $P$ spin-$S$ factors in $C_0$, that interval is
$[\max\{0,2S-PS\},PS]=[0,PS]$, since $P>R\geq3$.
Thus $C_0$ has an actual collective spin-$W$ subspace, because
$W=RS<PS$. This choice leaves every individual block at spin $S$.
For each $a\geq1$, choose its maximal collective spin $L_a$,
as constructed in (10.7). The list of part spins
$W,L_1,\ldots,L_r$ has sum $2W$ and maximum $W$. Applying (10.8)
to these very subspaces supplies a unit total singlet $v$. Its
intertwining embedding into the Boolean space has total $Z=0$;
therefore $v\in\mathcal H_{mS}$ with the original filling.

Rotations of this singlet equate the three same-axis cross-part
expectations, as in (10.9). On this particular $v$ the part Casimirs
are $W(W+1)$ for $C_0$ and $L_a(L_a+1)$ for $a\geq1$.
Consequently, writing $C=\sum_{a=1}^rL_a(L_a+1)$,

$$
\begin{aligned}
\langle v,Kv\rangle
&=\frac23\left\langle v,
 \left(\boldsymbol T^2-\sum_{a=0}^r\boldsymbol T_a^2\right)v\right\rangle
=-\frac23\bigl(W(W+1)+C\bigr)=:U,\\
E&\leq U.
\end{aligned}
\tag{11.6}
$$

Only the Rayleigh upper bound is used. No claim that $v$ is a ground
vector, or even an eigenvector of $K$, is made.

Suppose a nonsymmetric summand has minimum $E$, and choose a vertex
$p\in C_a$ with $J_p<S$. Apply the nonstrict fixed-$M=0$ comparison
(7.4)–(7.5) to increase every other local spin to $S$. It applies to
arbitrary other integer spins, including zero. Each intermediate
summand is present in the same full Boolean space, so its minimum
cannot fall below $E$; it remains $E$. We obtain a unit ground vector
with spin $J_p$ at $p$ and spin $S$ everywhere else.

The primary comparison is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal on-site spin $s_p$ is $S$, variable spin $t_p$ is $J_p$,
$M=0$, and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
The fixed-$M$ construction in §7 uses the triplet $|1,0\rangle$,
whose Cartesian expectations vanish. Its spin-$(j+1)$ projection has
squared coefficient $((j+1)^2-x^2)/((j+1)(2j+1))>0$ at every
$-j\leq x\leq j$, including endpoints. Orthogonal weight images
make it nonzero also for entangled inputs. The projection-and-induction
argument in (7.4)–(7.5) supplies precisely the nonstrict inequality
used here, not an exclusion of equality.

Realize the spin at $p$ by the symmetric space of $2J_p$ of its
original $2S$ Boolean coordinates and $S-J_p$ fixed singlet pairs,
as in §7 and (10.11)–(10.12). This is an intertwining isometry,
preserving magnetic weight and energy: at weight $x_p$ its occupancy
is $(J_p+x_p)+(S-J_p)=S+x_p$. All multiplicity copies carry
the same operator. Choose one pair and write the resulting ground
vector as $\Psi=|0,0\rangle\otimes f$, $\|f\|=1$, retaining the
other pairs and every remaining tensor factor in $f$. Put

$$
A=[m]\setminus C_a=N_H(p),\qquad
B_A^\pm=\sum_{i\in A}J_i^\pm,\qquad Z_A=\sum_{i\in A}Z_i.
\tag{11.7}
$$

Replace only this pair by $|1,0\rangle$, giving
$\Theta=|1,0\rangle\otimes f$. Both pair states have weight zero
and zero spin expectations, and there is no intrablock interaction.
Thus $\Theta$ remains in the same $\mathcal H_{mS}$ and has Rayleigh
quotient $E$. Equality at the minimum of a finite Hermitian operator
implies its ground-vector equation, by summing
$(\lambda-E)|c_\lambda|^2$ in an orthonormal eigenbasis.
The operator with the pair omitted satisfies $K^{\mathrm{rem}}f=Ef$,
because the pair operators annihilate the singlet. Therefore

$$
0=(K-EI)\Theta
=\sqrt2\,|1,1\rangle\otimes B_A^-f
 +\sqrt2\,|1,-1\rangle\otimes B_A^+f.
\tag{11.8}
$$

Orthogonality gives $B_A^-f=B_A^+f=0$, and their commutator gives
$Z_Af=0$. In the finite spin decomposition this is exactly the
total-singlet subspace on $A$: in a spin-$j$ irreducible both total
ladder norms vanish only at $j=0$. Hence all simultaneous rotations
on $A$ fix this same $f$, even when it is entangled with $C_a$.

For $b\ne a$, $\boldsymbol T_b$ acts on the unchanged spin-$S$
factors in $C_b$. The interaction of $C_a$ with $A$, after omitting
the chosen pair, is $T_{a,\mathrm{rem}}^+B_A^-+
T_{a,\mathrm{rem}}^-B_A^+$, which annihilates $f$. There are no
edges inside $C_a$. Thus, with $K_A$ the induced operator,
$K_Af=Ef$. Singlet rotation invariance on $A$ and
$\sum_{b\ne a}\boldsymbol T_bf=0$ give the same-state identity

$$
E=\langle f,K_Af\rangle
=-\frac23\sum_{b\ne a}\langle f,\boldsymbol T_b^2f\rangle.
\tag{11.9}
$$

On every part $b\ne a$, the maximal-spin bound of (10.7) is
$\boldsymbol T_b^2\preceq L_b(L_b+1)I$, on all its irreducibles
and multiplicities. If $a=0$, (11.9) immediately yields

$$
E\geq-\frac23C=U+\frac23W(W+1)>U,
\tag{11.10}
$$

contradicting (11.6).

If $a\geq1$, the singlet on $A$ imposes a stronger bound on the
unchanged dominant part. Set
$\boldsymbol Q_a=\sum_{1\leq b\leq r,\ b\ne a}\boldsymbol T_b$.
It is the collective spin of $(R-p_a)$ spin-$S$ sites, so every
irreducible has spin at most $W-L_a$ and
$\boldsymbol Q_a^2\preceq(W-L_a)(W-L_a+1)I$. This follows from
the same classical maximal-weight bound as (10.7), with all
multiplicity spaces retained. On the actual $f$ the singlet equation
is $(T_0^\alpha+Q_a^\alpha)f=0$ for $\alpha=x,y,z$. Hence

$$
\langle f,\boldsymbol T_0^2f\rangle
=\sum_{\alpha=x,y,z}\|T_0^\alpha f\|^2
=\sum_{\alpha=x,y,z}\|Q_a^\alpha f\|^2
\leq(W-L_a)(W-L_a+1).
\tag{11.11}
$$

This bound and every other part bound apply to the same entangled
vector. Substitution in (11.9), with its negative coefficient, gives

$$
\begin{aligned}
E&\geq-\frac23\left((W-L_a)(W-L_a+1)+C-L_a(L_a+1)\right)\\
 &=U+\frac43L_a(W+1)>U.
\end{aligned}
\tag{11.12}
$$

The equality uses
$W(W+1)-(W-L_a)(W-L_a+1)+L_a(L_a+1)=2L_a(W+1)$.
Strictness holds since $L_a\geq S\geq1$. This again contradicts
(11.6). The two cases exhaust every possible deficient vertex.
Neither the size of $P-R$ nor equality among minority part sizes is
used; in particular the proof includes $S=1$, singleton minority
parts, the smallest positive imbalance allowed by even $m$, and
arbitrarily large $P$.

Block permutations commute with the original $K$, so
$\operatorname{ran}P_{\mathrm{sym}}$ and $\mathcal N$ reduce it.
The latter is nonzero: in one block take a nonzero one-particle vector
orthogonal to constants, in a second take occupancy $2S-1$, and in
each other block take occupancy $S$. Their tensor has total occupancy
$1+(2S-1)+(m-2)S=mS$ and is in $\mathcal N$, also at $S=1$.
The orthogonal decomposition (6.12) excludes $E$ from every summand
of $\mathcal N$, with every copy included. Its nonempty finite
spectrum therefore has minimum strictly greater than $E$. This proves
$g>0$ and confines every complex ground vector, including arbitrary
superpositions, to $\operatorname{ran}P_{\mathrm{sym}}$.
On that range $K-EI\succeq0$ by the full-space definition of $E$;
on $\mathcal N$, $K-EI\succeq gI$. Adding the quadratic forms on
these orthogonal reducing subspaces proves (11.3), and its quadratic
form on a unit $\phi$ proves (11.4).

The added inference is the dominant-part trial (11.6) together with
the same-state bound (11.11), which makes both forced-singlet energies
strictly exceed a full-carrier upper bound. The Boolean representations,
classical spin coupling and Casimir bounds, fixed-magnetization
nonstrict comparison and original-pair release are consumed
intermediates from §§6–10 and the cited originals. For the two-auxiliary
construction also see Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2):
their $R^i$ is the spin-one sum of a pair, and their negative
Hamiltonian with nonnegative product couplings in directions 1 and 3
has different hypotheses from the positive adjacency here. The
unbalanced inference is a `repo-derived` consequence of the supplied
intermediates, without a priority assertion. $\square$

**推论 11.3（All positive part sizes at every even scale）。** Let
$H=K_{p_1,\ldots,p_q}$ be any labelled finite simple unit-weight
complete multipartite graph, with $q\geq2$, every $p_a\geq1$, and
even $m=\sum_a p_a$. For every even $s=2S\geq2$, on the original
complete complex Boolean $k=mS$-token space, set
$K=K_k$, $E=\lambda_{\min}(K)$ and
$\mathcal N=\ker P_{\mathrm{sym}}$. Then $\mathcal N$ is nonzero
and reducing, $g=\lambda_{\min}(K|_{\mathcal N})-E>0$, and

$$
\begin{aligned}
\ker(K-EI)&\subseteq\operatorname{ran}P_{\mathrm{sym}},&
K-EI&\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
&& (\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{11.13}
$$

Proof. If $q=2$, every induced open neighborhood is independent.
If $q=3$, the neighborhood of a vertex consists of the other two
parts with all cross edges and no within-part edges, so it is complete
bipartite. In either case $H$ has no isolates, and Theorem 7.2 and
Corollary 7.3 apply at every integer $S\geq1$, with exactly this
$E$, $K$ and $P_{\mathrm{sym}}$ and no flat-mode assumption.
For $q\geq4$, if $2\max p_a\leq m$, Definition 10.1 and Theorem
10.2 give all statements, including the weak-balance endpoint.
Otherwise exactly one part has size greater than the sum of the
others: two such parts would have sizes summing to more than $m$.
Name that existing labelled part $C_0$ and the others $C_1,\ldots,C_r$,
where $r=q-1\geq3$. This is a naming of the given parts, with no
quotient of vertices or Boolean blocks. Definition 11.1 holds, and
Theorem 11.2 proves (11.13). These cases are exhaustive.

Corollary 11.3
concerns unit weights, equal even Boolean block sizes and exact global
half filling only. The case $q=1$ has no edges and is excluded by the
original no-isolates domain. The arbitrary finite simple no-isolate
base of even order, including unrestricted disconnected bases under
only global half filling, remains unresolved. No exact formula for
$E$, numerical value or rate for $g$, odd-scale extension for arbitrary
multipartite bases, or extension to weights, unequal blocks or other
fillings is asserted. The separate sufficient statements of §§6–10
retain their hypotheses; the corollary combines §7, §10 and Theorem
11.2 without changing those statements. $\square$

**命题 11.4（The labelled $K_{7,1,1,1}$ application）。** For every
labelled realization of $H=K_{7,1,1,1}$, all conclusions of Corollary
11.3 hold on its original complete complex $k=5s$-token carrier at
every even $s\geq2$. Every induced open neighborhood is nonbipartite,
and $H$ has no modulus-one least adjacency eigenvector. Thus it lies
outside both the locally bipartite-neighborhood class of §7 and the
flat-least-mode class of Assumption 3.1.

Proof. Its four nonempty parts have even total size $m=10$, and its
dominant part has $P=7>3=R$. There are no isolates. Theorem 11.2
applies with $k=mS=10S=5s$ at every $S\geq1$, retaining all ten
original blocks. The open neighborhood of any vertex contains one
vertex from each of three other parts. These three vertices form a
triangle, which rules out bipartiteness at every vertex.

For the flat-mode assertion write $a=A(H)$. Vectors supported on the
seven-vertex part with coordinate sum zero form a six-dimensional
zero eigenspace. Vectors supported on the three singleton vertices
with coordinate sum zero form a two-dimensional eigenspace of
eigenvalue $-1$. The orthogonal complement consists of vectors
constant on the seven-vertex part and constant on the three
singletons. In the orthonormal basis given by the normalized indicators
of those two sets, the adjacency matrix on that complement is

$$
\begin{pmatrix}0&\sqrt{21}\\\sqrt{21}&2\end{pmatrix},
\qquad \operatorname{spec}(a)
=\{0\ (6\text{ times}),\ -1\ (2\text{ times}),\ 1-\sqrt{22},\ 1+\sqrt{22}\}.
\tag{11.14}
$$

The two eigenvalues of the displayed matrix are the roots of
$\theta^2-2\theta-21=0$. Since $\sqrt{22}>2$, the least eigenvalue
is $\lambda=1-\sqrt{22}<-1$, with a one-dimensional eigenspace in
that complement. A complex least eigenvector therefore has a common
coordinate $c$ on the seven-vertex part and $d$ on each singleton,
satisfying $\lambda c=3d$. If every coordinate had modulus one, this
would force $|\lambda|=3$, hence $\sqrt{22}=4$, contrary to
$22\ne16$. Thus Assumption 3.1 fails as well. $\square$


## 追加锚（本行以下为增补区）
## 12. Clique blocks, the spin-one exception and every ground vector

**定义 12.1（Graph blocks and the original Boolean fibres）。** Let $H$
be a finite connected simple unit-weight block graph of even order
$m\geq2$: every maximal two-connected graph block is a clique, and
bridges are also counted as graph blocks $K_2$. Write $\mathfrak B(H)$
for these graph blocks. For every integer $S\geq1$, put $s=2S$ and
$k=mS$, and retain exactly $B_i$, $H[\overline{K_{2S}}]$, the complete
complex Boolean carrier $\mathcal H_{mS}$, positive ordinary token
adjacency $K=K_{mS}$ and the original within-$B_i$ projections $P_i$
and $P_{\mathrm{sym}}$ of Definitions 1.1–1.2. Put

$$
E=\lambda_{\min}(K),\qquad
U=\{p\in V(H):\text{some }C\in\mathfrak B(H)
\text{ contains }p\text{ and }|C|\ne4\}.
\tag{12.1}
$$

A graph block $C$ consists of base vertices, each with its own Boolean
fibre $B_i$ of size $2S$; it is not a Boolean fibre. Only the single
global filling $k=mS$ is prescribed.

**定理 12.2（Block-graph confinement and endpoint localization）。**
Under Definition 12.1, every complex ground vector $v\in\ker(K-EI)$
satisfies

$$
\begin{cases}
P_{\mathrm{sym}}v=v,&S\geq2,\\
P_pv=v\quad\text{for every }p\in U,&S=1.
\end{cases}
\tag{12.2}
$$

In particular, if $U=V(H)$, every ground vector belongs to
$\operatorname{ran}P_{\mathrm{sym}}$ for every integer $S\geq1$.

Proof. Use the complete orthogonal decomposition (6.6)–(6.12), not
just its symmetric summand. A fibre carries each integer spin
$J_i=S-t_i$, $0\leq t_i\leq S$, with multiplicity
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$, and the entire
slice $\sum_i x_i=0$, $-J_i\leq x_i\leq J_i$. Every slice is
nonempty because all these spins have weight zero. Its operators are

$$
\begin{aligned}
Z_i|x_i\rangle&=x_i|x_i\rangle,&
J_i^\pm|x_i\rangle&=b_{J_i}^\pm(x_i)|x_i\pm1\rangle,\\
K_{\boldsymbol J}&=\sum_{\{i,j\}\in E(H)}
(J_i^+J_j^-+J_i^-J_j^+)
=2\sum_{\{i,j\}\in E(H)}(X_iX_j+Y_iY_j).
\end{aligned}
\tag{12.3}
$$

Here $b_J^\pm$ are exactly (6.10), including all endpoint zeros;
$X_i=(J_i^++J_i^-)/2$ and $Y_i=(J_i^+-J_i^-)/(2i)$.
The representation parameters are Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2), Boolean
rank $n=2S$, starting rank $t_i$ and up operator $L_i^*=J_i^+$;
and Feinsilver, [§§3–4, (8)–(10), Proposition 4.3 and
§4.2.2](https://arxiv.org/pdf/1102.0368v2), principal number
$2S-2t_i=2J_i$. These classical representations, with the complete
construction in §6, supply all multiplicity copies. $P_p$ selects
exactly the summands with $t_p=0$; $P_{\mathrm{sym}}$ selects
exactly $t=0$.

The carrier and sign in (12.3) are those of `tokenGraph` in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and [its Blueprint definition](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs):
a move has the two singleton set differences and coefficient one.
Equation (2.4), also the move accounting in the proof-local
`Test.toNbr_bij` and `Test.token_energy` of
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean),
identifies this adjacency with (12.3). Its private
`complex_real_energy`, `complex_real_norm` and `real_complex_rayleigh`
and [the corresponding Blueprint's minimum and result explanations](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
supply the complex Rayleigh convention used below; no pentagon-specific
energy, cut bound or Laplacian-radius assertion is used. In
Apte–Parekh–Sud, [v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
this $K$ is $A(F_k(H[\overline{K_s}]))$, whereas their shifted XY
block is $W(H[\overline{K_s}])I/2-K$.
The top chain's unit occupancy vectors are the two-letter case of
`sector_words_card_multinomial` and `sector_gram` in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean),
with counts $(2S-n_i,n_i)$, including $n_i=0,2S$; their scope and
normalization are [its Blueprint's word-cardinality and sector-Gram statements](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs).
Thus the product Dicke identification of Proposition 6.3 and
[the collective-oscillator supplier, Definitions 1.1–1.2](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
has parameters $d=m$, $N=2S$, $g=0$, $e=1$ and $B=A(H)$:
$a_{i,2S}=L_i/\sqrt{2S}$ and $H_{2S}(A(H))=\hbar K/(2S)$
on this carrier. Its fixed-excitation oscillator approximation is not
applied to the growing excitation number $mS$.

We need a local statement about a disjoint union $G$ of nonempty
cliques, with the same integer spin $S$ at each vertex. Let $K_G$
be (12.3) on its full total-zero-weight space, and let $e_G$ be its
minimum. A total singlet means a vector annihilated by all three
components of $\sum_i(X_i,Y_i,Z_i)$. We prove that $K_G$ has a
zero-weight ground vector which is not a total singlet whenever
$G$ has a singleton component, or has a clique component of order
$n\geq2$ with $(n,S)\ne(3,1)$.

Write $c=S(S+1)$. For a clique $C$ of order $n$, set
$\boldsymbol T_C=\sum_{i\in C}(X_i,Y_i,Z_i)$ and
$Q_C=\sum_{i\in C}Z_i^2$. Expanding the squares gives

$$
K_C=\boldsymbol T_C^2-(T_C^z)^2-ncI+Q_C.
\tag{12.4}
$$

We consume the classical Clebsch–Gordan rule already used in
(10.7)–(10.8): $V_u\otimes V_v$ contains each spin from $|u-v|$
to $u+v$ in integer steps. Its coefficients, triangle range and
orthogonality are [NIST DLMF (34.1.1), (34.2.1),
(34.3.16)–(34.3.17)](https://dlmf.nist.gov/34.1).
In particular, two spin-$S$ sites have the unit singlet

$$
d_S=\frac1{\sqrt{2S+1}}\sum_{x=-S}^S(-1)^{S-x}|S,x\rangle|S,-x\rangle.
\tag{12.5}
$$

This is [DLMF (34.3.1)](https://dlmf.nist.gov/34.3#E1) in the
Clebsch–Gordan convention (34.1.1); alternatively its total ladders
cancel term by term using (6.10). Three spin-$S$ sites also have a
singlet: couple two of them to spin $S$, which occurs because $S$
is an integer, then couple that spin to the remaining spin $S$ by
(12.5). Pairing sites, or taking one such triple and pairing the
others, supplies a unit singlet $w_C$ for every $n\geq2$.
Rotations equate the $x,y,z$ expectations on a singlet, so

$$
K_Cw_C=(Q_C-ncI)w_C,\qquad
\langle w_C,K_Cw_C\rangle=-\frac23nc.
\tag{12.6}
$$

Indeed $\boldsymbol T_Cw_C=0$ in (12.4), and each single-site
Casimir is $cI$, giving $\langle Q_C\rangle=nc/3$.

For $n=2$, the squared coordinates of (12.5) give $Q_C=2x^2$
with positive probabilities at $x=0$ and $x=1$. Hence
$\operatorname{Var}_{d_S}(Q_C)>0$. For every $n\geq4$, choose
$w_C$ as a product with one factor $d_S$ and a singlet on the other
$n-2$ sites. The latter exists also at $n=5$, where it is a triple.
On this product the variance of $Q_C$ is the sum of the variances
on the two factors, and is therefore strictly positive. By (12.6)
these singlet trials are not eigenvectors of $K_C$.

For the remaining case $n=3$, $S\geq2$, take the spin-$S$ chain
of sites 2 and 3, and let its nonzero lowest-weight vector be

$$
h=\sum_{a=0}^S c_a|S,a-S\rangle_2|S,-a\rangle_3.
$$

Its total lowering operator kills it. The coefficient of
$|S,a-S\rangle_2|S,-a-1\rangle_3$ consequently gives

$$
\sqrt{(S-a)(S+a+1)}\,c_a
+\sqrt{(a+1)(2S-a)}\,c_{a+1}=0
\qquad(0\leq a<S).
\tag{12.7}
$$

Both coefficients are strictly positive throughout this range. If
$c_0=0$, the recurrence makes all $c_a$ zero, impossible; thus
$c_0c_1\ne0$. Couple this chain with site 1 by (12.5). The resulting
three-site singlet has nonzero coordinates at both
$(S,-S,0)$ and $(S,1-S,-1)$. The corresponding eigenvalues of $Q_C$
are $2S^2$ and $2S^2-2S+2$, which differ for every $S\geq2$.
Its $Q_C$ variance is positive, so it too is not a $K_C$ eigenvector.
This uses actual endpoint coefficients and includes $S=2$.

Now let $C_1,\ldots,C_b$ be all components of $G$ with orders at
least two, and let $h_0$ be its number of singleton components. Put

$$
A_G=-\frac23c\sum_{a=1}^b|C_a|.
\tag{12.8}
$$

For any unit total singlet $z$ on $G$, simultaneous rotations on
all of $G$ equate its three same-axis edge expectations. On each
component the isotropic edge sum is
$(\boldsymbol T_{C_a}^2-|C_a|cI)/2$. Singleton components have
no edges. Therefore, on this same possibly entangled $z$,

$$
\langle z,K_Gz\rangle
=\frac23\sum_{a=1}^b
\bigl(\langle z,\boldsymbol T_{C_a}^2z\rangle-|C_a|c\bigr)
\geq A_G.
\tag{12.9}
$$

There is an actual total-zero-weight trial
$w=\bigotimes_{a=1}^b w_{C_a}\otimes|S,0\rangle^{\otimes h_0}$
with energy $A_G$, so $e_G\leq A_G$. If one component has
$(|C_a|,S)\ne(3,1)$, choose its positive-variance singlet above.
The operators of distinct components act on distinct tensor factors,
so $\operatorname{Var}_w(K_G)$ is the sum of their variances and
is strictly positive. Thus $w$ is not an eigenvector. Equality
$e_G=A_G$ would force every spectral component of $w$ to have energy
$e_G$, since their nonnegative excesses average to zero. This would
make $w$ an eigenvector. Hence $e_G<A_G$, and (12.9) excludes every
total singlet from the ground space.

If instead $h_0>0$, either $e_G<A_G$, with the same exclusion, or
$e_G=A_G$. In the latter case this $w$ is itself a ground vector,
and its total raising norm squared is $h_0c>0$: all clique factors
are singlets, while raising different singleton factors gives
orthogonal vectors. In either case a nonsinglet ground vector exists.
This also covers an entirely edgeless $G$ and all empty products.
The minimum $e_G$ throughout was over the full global-zero slice;
no minimum was identified with a sum of separately optimized component
minima and no component filling was imposed on arbitrary vectors.

We next apply this local conclusion to $A=N_H(p)$. The graph
$H[A]$ is a disjoint union of cliques

$$
H[A]=\bigsqcup_{\substack{C\in\mathfrak B(H)\\p\in C}}
K_{C\setminus\{p\}}.
\tag{12.10}
$$

Here is the required graph justification. Each edge belongs to a
unique graph block: distinct maximal two-connected blocks cannot
share two vertices, since two two-connected graphs sharing two
vertices have two-connected union; a bridge lies on no cycle.
Thus the blocks containing $p$ partition its incident edges and
hence, because they are cliques, partition its neighbors. If neighbors
from two different such blocks were adjacent, their triangle with
$p$ would be two-connected and would put both incident edges in
one graph block, a contradiction. This proves (12.10), including
bridge components of order one. Connectedness and $m\geq2$ make
$A$ nonempty. Consequently our local conclusion applies at every
$p$ for $S\geq2$, and at every $p\in U$ for $S=1$.

For completeness, use the supplied nonstrict comparison and
singlet replacement at precisely these vertices. The comparison
(7.4)–(7.5) concerns the minimum at fixed total weight zero when one
integer local spin is increased by one. Its primary source is
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal spin $s_p$ is $S$, variable spin $t_p$ is our $J_p$,
$M=0$ and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
The zero-weight triplet $|1,0\rangle$ preserves $M$ and has zero
Cartesian expectations. Its projection from $j\otimes1$ onto
spin $j+1$ has squared coefficient
$((j+1)^2-x^2)/((j+1)(2j+1))>0$ for every $-j\leq x\leq j$,
as (7.4) shows by the symmetric-subset count. Distinct weights have
orthogonal images, so the conclusion holds for entangled inputs.
The projection-and-induction proof in §7 includes the base $j=0$
and arbitrary other integer spins, including zero. We consume only
its nonstrict inequality, not an every-vector equality exclusion.

Suppose a sector of (6.12) with $J_p<S$ has minimum $E$. Increase
all other local spins to $S$ by that comparison. Every intermediate
sector is present in the original $\mathcal H_{mS}$, so its minimum
cannot be below $E$ and must remain $E$. Realize its spin $J_p$ by
the symmetric space on $2J_p$ of the original $2S$ coordinates at
$p$, together with $S-J_p$ fixed singlet pairs. This intertwines
all collective operators, and at weight $x_p$ has occupancy
$(J_p+x_p)+(S-J_p)=S+x_p$. All multiplicity copies in (6.12)
have the same matrix, so this choice loses no sector minimum.
Choose one pair and write its unit ground vector
$\Psi=|0,0\rangle\otimes f$. Keep every other pair and all remaining
auxiliaries in $f$, allowing arbitrary entanglement. Set

$$
R=V(H)\setminus(\{p\}\cup A),\qquad
B^\pm=\sum_{i\in A}J_i^\pm,\qquad Z_A=\sum_{i\in A}Z_i.
$$

Release only this pair to $|1,0\rangle$. The vector
$\Theta=|1,0\rangle\otimes f$ stays in the same original half-filled
carrier. The two pair states have zero weight and zero Cartesian
expectations; there are no intrafibre edges. Hence its Rayleigh
quotient is still $E$ and it is a ground vector. The operator with
the pair omitted satisfies $K^{\mathrm{rem}}f=Ef$. Exactly as in
(7.12), the orthogonal pair weights give

$$
0=(K-EI)\Theta
=\sqrt2|1,1\rangle\otimes B^-f
 +\sqrt2|1,-1\rangle\otimes B^+f.
\tag{12.11}
$$

Thus $B^-f=B^+f=0$, and their commutator gives $Z_Af=0$.
In the finite spin decomposition this common kernel is precisely
the total-singlet subspace $\mathcal S_A$: both ladder norms vanish
in a spin-$q$ irreducible only at $q=0$. Consequently
$f\in\mathcal S_A\otimes\mathcal H_{pR,0}$, where the second
factor is the actual remaining auxiliaries at $p$ and all of $R$
at their joint weight zero.

Sandwiching any single-site spin component on $A$ between its
singlet projections gives zero. Indeed simultaneous rotations fix
both singlets, while the three matrix elements transform as a vector,
whose only rotation-invariant value is zero. This holds also with
operators on the other factors tensored alongside. All interactions
crossing from $A$ therefore have zero expectation in this same $f$.
There are no edges from $p$ to $R$, so

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{12.12}
$$

The local conclusion for (12.10) supplies a unit ground vector $u_A$
on the entire $Z_A=0$ slice, of energy $e_A$, not killed by both
$B^\pm$. Retain the reduced density $\rho_{pR}$ of this very $f$,
which is supported on $\mathcal H_{pR,0}$, and form in the original
carrier

$$
\rho=|0,0\rangle\langle0,0|\otimes
 |u_A\rangle\langle u_A|\otimes\rho_{pR}.
\tag{12.13}
$$

Definite $Z_A=0$ gives $\langle u_A,J_i^\pm u_A\rangle=0$ at
every site. Thus all crossing expectations in this product density
vanish and

$$
\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{12.14}
$$

The reverse inequality follows from the same entire-carrier minimum
$E$. Decompose $\rho_{pR}$ spectrally into unit vectors $h$ with
positive weights, all in its actual joint zero-weight support. Each
$|0,0\rangle\otimes u_A\otimes h$ has energy at least $E$, while
their average equals $E$, so each is a ground vector. Apply the same
pair release (12.11) to any one of them. It forces
$B^-u_A=B^+u_A=0$, contradicting the choice of $u_A$. If $R$ is
empty, its factor is $\mathbb C$ and $K_R=0$, but all remaining
auxiliaries at $p$ stay in $h$. Every replacement uses one actual
joint realization; no independent choice of an optimal $pR$ state
or of its filling is made.

This consumes the singlet/product mechanism of (7.11)–(7.15) with
a new local input (12.4)–(12.10). The two-auxiliary precedent is
Benassi–Lees–Ueltschi, [v3, §4.3, Lemma 9 and
(4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the collective spin of one pair of spin-half auxiliaries;
their negative Hamiltonian with nonnegative product couplings in
directions 1 and 3 does not supply strictness for our positive
adjacency on a nonbipartite base. The extra inference here is the
clique singlet variance and the common bound (12.9), followed by the
block incidence (12.10), not another spin representation or another
nonstrict comparison.

We have excluded energy $E$ from every sector with $J_p<S$ at each
of the stated vertices $p$. The orthogonal decomposition reduces
$K$ and all $P_p$ and retains every multiplicity copy. Therefore
every component of an arbitrary complex ground vector has $t_p=0$
at those vertices. This proves the localization assertion. When all
vertices are so covered, every component has $t=0$, proving full
confinement for all ground vectors, including arbitrary superpositions.
$\square$

**推论 12.3（The spectral consequences in the full-confinement cases）。**
Under Definition 12.1, assume $S\geq2$, or $S=1$ and $U=V(H)$.
Then $\mathcal N=\ker P_{\mathrm{sym}}$ is nonzero and reduces $K$,
and, with the very same $E$ and carrier,

$$
\begin{aligned}
g&=\lambda_{\min}(K|_{\mathcal N})-E>0,\\
K-EI&\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\qquad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{12.15}
$$

Proof. Original fibre permutations commute with $K$, hence their
orthogonal invariant projection $P_{\mathrm{sym}}$ commutes with it.
To see $\mathcal N\ne0$, take a nonzero one-particle vector orthogonal
to constants in one fibre, occupancy $2S-1$ in another, and occupancy
$S$ in every remaining fibre. Their tensor has occupancy
$1+(2S-1)+(m-2)S=mS$ and lies in $\mathcal N$, also when $m=2$
or $S=1$. Theorem 12.2 excludes $E$ from the finite nonempty
spectrum on this reducing subspace, so its minimum is strictly above
$E$. On $\operatorname{ran}P_{\mathrm{sym}}$, $K-EI\succeq0$
by the definition of the whole-carrier minimum. On $\mathcal N$ it
is at least $gI$. Adding their quadratic forms, with no cross terms,
gives the operator inequality on all complex vectors. Its quadratic
form on a unit vector and division by $g>0$ give the mass bound.
This is the finite-spectrum finish of Corollary 7.3 with the new
strictness input; it gives no exact $E$, numerical $g$ or rate.
$\square$

**命题 12.4（A clique with a distinct pendant leaf at every vertex）。**
For every integer $r\geq4$, let $H_r$ have core vertices
$c_1,\ldots,c_r$ forming $K_r$ and distinct leaves
$\ell_1,\ldots,\ell_r$, with the sole leaf edges
$\{c_i,\ell_i\}$. All ground-vector, positive-gap, operator and
normalized-mass conclusions of (12.2) and (12.15) hold on the original
complete complex carrier at every even $s\geq2$. This family is
supplied by neither the locally bipartite-neighborhood condition of
§7, the flat-least-mode condition of §§3–6, nor the complete
multipartite result of Corollary 11.3.

Proof. The graph is finite, simple, connected and unit-weight, of
even order $m=2r$. Its graph blocks are its core $K_r$ and the $r$
bridges $\{c_i,\ell_i\}$. Each vertex belongs to one of these
$K_2$ blocks, so $U=V(H_r)$, even at $r=4$. Theorem 12.2 and
Corollary 12.3 apply at every integer $S\geq1$, with the original
$2r$ fibres of size $s=2S$ and global filling $k=2rS=rs$.

At a core vertex $c_i$, the induced open neighborhood is the disjoint
union of $K_{r-1}$ on the other core vertices and the isolated vertex
$\ell_i$. Since $r-1\geq3$, it contains a triangle and is not
bipartite. Thus Definition 7.1 fails, regardless of the independent
neighborhood at each leaf. This failure applies for every $r\geq4$.

For the flat-mode hypothesis, order the adjacency coordinates as
cores and leaves. Its matrix is

$$
a=\begin{pmatrix}\boldsymbol1\boldsymbol1^{\mathsf T}-I&I\\I&0\end{pmatrix}.
\tag{12.16}
$$

Put $\theta=(-1-\sqrt5)/2<-1$. Choose nonzero $x\in\mathbb R^r$
with $\sum_i x_i=0$ and set $y=x/\theta$. Since
$\theta^2+\theta=1$, (12.16) gives
$a(x,y)=(-x+y,x)=\theta(x,y)$. Hence the actual least eigenvalue
$\lambda$ of $a$ satisfies $\lambda\leq\theta<-1$. But its leaf
equations for any eigenvector $z$ are
$\lambda z_{\ell_i}=z_{c_i}$. If every coordinate had modulus one,
these equations would force $|\lambda|=1$, a contradiction. This
rules out complex as well as real flat least modes, so the conditional
flat-mode suppliers, including Theorem 6.2, do not apply.

Finally, in any complete multipartite graph two distinct nonadjacent
vertices belong to the same part. Here $\ell_1$ is nonadjacent to
both $c_2$ and $\ell_2$, while $c_2$ is adjacent to $\ell_2$.
The first two relations would put all three in one part and forbid
the last edge. Thus $H_r$ is not complete multipartite for any of
these $r$, even with arbitrary labelled or unequal parts. Corollary
11.3 therefore supplies none of these all-even conclusions. The
odd-scale statements of §§8–9 concern a different scale parity.
The assertions follow without an energy formula or a numerical gap.
$\square$

**命题 12.5（The endpoint obstruction and the retained boundary）。**
The sufficient condition $U=V(H)$ is not necessary for confinement.
All even-order complete graphs remain covered at every even $s\geq2$.
At $S=1$, the clique-variance argument in Theorem 12.2 has an
exception at a three-vertex neighborhood component; it gives no
exclusion at a vertex incident only to $K_4$ graph blocks.

Proof. For $H=K_m$ with even $m\geq2$, its only graph block has
order $m$. If $m\ne4$, $U=V(H)$ and Theorem 12.2 applies at all
$S\geq1$. For $m=4$, $U=\varnothing$, but Theorem 10.2, or
Corollary 11.3 with four singleton graph parts, supplies every
conclusion at all these even scales, including $S=1$. Thus the
incidence condition is sufficient and is not necessary. More generally,
block graphs already satisfying Definition 7.1 are included: a graph
block of order at least four puts a triangle in a vertex neighborhood,
while blocks of orders two and three give only singleton and edge
components in (12.10). Every vertex is then in $U$.

To see the actual degeneracy of the new strict-trial step, at $S=1$
on three sites the unit alternating vector

$$
z=\frac1{\sqrt6}\sum_{\pi\in\mathfrak S_3}
\operatorname{sgn}(\pi)|\pi(1,0,-1)\rangle
\tag{12.17}
$$

is a singlet. Its weight is zero, and its total raising and lowering
operators kill it: equal resulting weights occur in pairs of opposite
permutation signs with the same ladder coefficient $\sqrt2$.
Every nonzero coordinate has $Q_C=1^2+0^2+(-1)^2=2$.
Equation (12.4) therefore gives $K_{K_3}z=-4z$.
The three-site singlet is unique, because the two-site coupling
$V_1\otimes V_1=V_0\oplus V_1\oplus V_2$ can couple the third
$V_1$ to spin zero only through its single $V_1$ summand.
Consequently its singlet trial has zero variance, exactly the equality
$2S^2=2S^2-2S+2$ at $S=1$ in (12.7). This auxiliary eigenvector
only exhibits the failure of that strict-variance step. It supplies
no deficient-spin ground vector of the original $H[\overline{K_2}]$
operator at its actual energy $E$.

Thus for general connected even-order block graphs at $s=2$, vertices
incident exclusively to $K_4$ graph blocks remain outside the new
localization exclusion, except where a separate supplied theorem
applies. No actual defect there is asserted. The original arbitrary-$H$
problem, other fillings, weights and unequal Boolean fibres remain
unresolved by these statements. The sufficient results of §§6–11
retain their own graph and scale hypotheses. The additional inference
is the ordinary-proof block-graph conclusion (12.2) and its pendant-leaf
application; no global novelty, optimal threshold or quantitative
spectral rate is asserted. $\square$

## 追加锚（本行以下为增补区）
## 13. The spin-one endpoint for every connected even-order block graph

**定义 13.1（The spin-one carrier and its actual minimum）。** Let $H$
be any finite connected simple unit-weight block graph of even order
$m\geq2$, with graph blocks as in Definition 12.1. Put $S=1$, $s=2$
and $k=m$. Use the original fibres $B_i$, blow-up
$H[\overline{K_2}]$, complete complex Boolean carrier $\mathcal H_m$,
positive ordinary token adjacency $K=K_m$ and original fibre
projections $P_i,P_{\mathrm{sym}}$ of Definitions 1.1–1.2. Set

$$
E=\lambda_{\min}(K),\qquad \mathcal N=\ker P_{\mathrm{sym}},
\tag{13.1}
$$

where $E$ is minimized over this entire carrier. The graph blocks
are cliques of base vertices; every base vertex still has its own
two-coordinate Boolean fibre. There is only the global occupancy
constraint $k=m$.

**定理 13.2（Every ground vector at the spin-one endpoint）。** For
every $H$ of Definition 13.1,

$$
v\in\ker(K-EI)\quad\Longrightarrow\quad P_{\mathrm{sym}}v=v.
\tag{13.2}
$$

The subspace $\mathcal N$ is nonzero and reduces $K$. With this same
$E$,

$$
\begin{aligned}
g&=\lambda_{\min}(K|_{\mathcal N})-E>0,\\
K-EI&\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\qquad(\phi\in\mathcal H_m,\ \|\phi\|=1).
\end{aligned}
\tag{13.3}
$$

These assertions include articulation vertices and vertices incident
exclusively to $K_4$ graph blocks.

Proof. Consume the complete Boolean representation (6.6)–(6.12).
At $s=2$ it is particularly explicit: in each original fibre, its
spin-one chain and spin-zero chain have respective orthonormal bases

$$
\begin{aligned}
|1,-1\rangle&=|\varnothing\rangle,&
|1,0\rangle&=\frac{|\{1\}\rangle+|\{2\}\rangle}{\sqrt2},&
|1,1\rangle&=|\{1,2\}\rangle,\\
\chi=|0,0\rangle&=\frac{|\{1\}\rangle-|\{2\}\rangle}{\sqrt2}.
\end{aligned}
\tag{13.4}
$$

The labels $1,2$ here are coordinates within that fibre. Both chains
have multiplicity one, namely $r_2(0)=r_2(1)=1$ in (6.8). On either
chain $n_i=I+Z_i$; the collective ladders annihilate $\chi$ and act
on the triplet with exactly the coefficients (6.10). Consequently

$$
\mathcal H_m\cong
\bigoplus_{\boldsymbol J\in\{0,1\}^m}
\left(\bigotimes_i V_{J_i}\right)_{Z=0},\qquad
K_{\boldsymbol J}
=\sum_{\{i,j\}\in E(H)}(J_i^+J_j^-+J_i^-J_j^+).
\tag{13.5}
$$

Here $V_j$ is the spin-$j$ representation, $Z=\sum_i Z_i$, and
each displayed summand contains all its zero-total-weight vectors.
Every summand is nonempty, since integer spins have weight zero.
The decomposition is orthogonal and reduces $K$ and all $P_i$.
$P_i$ selects $J_i=1$, so $P_{\mathrm{sym}}$ selects exactly
$\boldsymbol J=(1,\ldots,1)$. This is a decomposition of the whole
carrier, without a symmetry condition on an input vector.

The primary representation maps remain Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
Boolean rank $n=2$, starting rank $t_i=1-J_i$ and up operator
$L_i^*=J_i^+$; and Feinsilver,
[§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $2-2t_i=2J_i$. For normalization, (13.4)'s triplet
is the two-letter case of sector_words_card_multinomial and
sector_gram in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean),
with counts $(2-n_i,n_i)$, including both endpoints; see also
[its word-cardinality and sector-Gram explanations](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs).
Equation (2.4), the singleton-difference tokenGraph definition in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and [its Blueprint](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs),
and the proof-local Test.toNbr_bij and Test.token_energy in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
identify (13.5) with positive adjacency, with coefficient one for
each Boolean token move. Each spin edge is $2(X_iX_j+Y_iY_j)$.
The latter supplier's private complex_real_energy,
complex_real_norm and real_complex_rayleigh, with
[its Blueprint's minimum explanation](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs),
give the same complex Rayleigh convention as (1.2).
In Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/html/2506.03441v3),
$K=A(F_m(H[\overline{K_2}]))$; the shifted XY block
$W(H[\overline{K_2}])I/2-K$ is a different operator.
The Dicke identification with
[the collective-oscillator supplier, Definitions 1.1–1.2](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
has $d=m$, $N=2$, $g=0$, $e=1$, $B=A(H)$,
$a_{i,2}=L_i/\sqrt2$ and $H_2(A(H))=\hbar K/2$ on its two-state
code. Only that exact identification is used; its fixed-low-excitation
approximation supplies no step here.

Suppose a summand of (13.5) with some $J_p=0$ has minimum $E$.
Theorem 12.2 already excludes this when $p\in U$, with $U$ defined
in (12.1). Thus $p\notin U$, and every graph block containing $p$
is $K_4$. Increase every other spin to one by the supplied nonstrict
fixed-zero-weight comparison (7.4)–(7.5). Every intermediate summand
is in the same original carrier and hence has minimum at least $E$;
the comparison says its minimum is at most $E$. All these minima
therefore remain $E$. The primary source is
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412):
$s_i=1$, variable spin $t_i=J_i$, $M=0$ and
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
Only its nonstrict conclusion is consumed. At this scale the only
increase is $0$ to $1$; the source's zero-weight triplet has zero
Cartesian expectations and preserves $M=0$. No equality exclusion
is taken from that comparison.

We thus have a unit ground vector $\Psi=\chi_p\otimes f$ with
spin one at every vertex other than $p$, and total weight zero.
Write

$$
A=N_H(p),\quad R=V(H)\setminus(\{p\}\cup A),\quad
B^\pm=\sum_{i\in A}J_i^\pm,\quad Z_A=\sum_{i\in A}Z_i.
\tag{13.6}
$$

The block incidence (12.10) gives a partition into triples

$$
A=T_1\sqcup\cdots\sqcup T_b,\qquad
H[A]=\bigsqcup_{a=1}^b K_{T_a},\qquad
H[\{p\}\cup T_a]=K_4,\qquad b\geq1.
\tag{13.7}
$$

Indeed the graph blocks through $p$ partition its neighbors, and
neighbors in different such blocks cannot be adjacent, as proved
in (12.10). Connectedness and $m\geq2$ give a neighbor. Vertices of
the triples may themselves be articulation vertices with further
neighbors in $R$; none are removed.

Replace just $\chi_p$ by the triplet $|1,0\rangle_p$. This unit vector
$\Theta$ has the same total weight and the same Rayleigh quotient
$E$, because both local states have zero spin expectations and there
are no intrafibre edges. Equality at the minimum of a finite Hermitian
matrix implies its eigenvector equation: in an orthonormal eigenbasis,
the nonnegative terms $(\lambda-E)|c_\lambda|^2$ sum to zero.
The operator with $p$ omitted satisfies $K_{H-p}f=Ef$. As in the
supplied singlet release (12.11), the original operator therefore gives

$$
0=(K-EI)\Theta
=\sqrt2\,|1,1\rangle_p\otimes B^-f
 +\sqrt2\,|1,-1\rangle_p\otimes B^+f.
\tag{13.8}
$$

Orthogonality gives $B^-f=B^+f=0$, and
$[B^+,B^-]=2Z_A$ gives $Z_Af=0$. The three components of the total
spin of $A$ annihilate $f$, so $f$ is in its total-singlet space
$\mathcal S_A$, tensored with the weight-zero space on $R$.
Equivalently its total Casimir is
$Z_A^2+(B^+B^-+B^-B^+)/2$, whose quadratic form is zero.
The remaining weight on $R$ is zero as a consequence of this equation
and the original global constraint.

Let $K_A,K_R$ be the induced spin operators. A single-site spin
component has zero matrix elements between any two singlets on $A$.
To see this, simultaneous rotations fix those two vectors and rotate
the three matrix elements as a three-dimensional vector; a vector
fixed by all rotations is zero. Thus the singlet projection $Q_A$
satisfies $Q_AJ_i^\alpha Q_A=0$ for $i\in A$ and
$\alpha=x,y,z$. Tensoring this identity with arbitrary operators
on $R$ shows that every edge between $A$ and $R$ has zero expectation
in the same, possibly entangled, $f$. Hence

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{13.9}
$$

Put $\boldsymbol T_a=\sum_{i\in T_a}(X_i,Y_i,Z_i)$. The singlet
bound (12.9), at $S=1$ and with all clique orders three, says

$$
\langle f,K_Af\rangle
=\frac23\sum_{a=1}^b
 \left(\langle f,\boldsymbol T_a^2f\rangle-6\right)
\geq-4b.
\tag{13.10}
$$

For clarity, simultaneous rotations of $A$ equate the three same-axis
edge expectations on this very $f$; each spin-one site's Casimir is
$2I$, and the isotropic edge sum on a triple is
$(\boldsymbol T_a^2-6I)/2$. Since the positive-adjacency edge is
$2(X_iX_j+Y_iY_j)$, these identities give the factor $2/3$ in
(13.10). The nonnegative Casimirs give the inequality without any
separate filling or singlet requirement on individual triples.

Consume the actual three-site singlet $z$ of (12.17), with a labelled
copy $z_a$ on each $T_a$. Its six coordinates are the alternating
permutations of $(1,0,-1)$, each of modulus $1/\sqrt6$.
Opposite permutation signs cancel under either total ladder, its
weight is zero, and $\sum_{i\in T_a}Z_i^2z_a=2z_a$.
The clique identity (12.4) gives
$K_{T_a}z_a=-4z_a$. These are supplied singlet and spectral facts;
no assertion about the full minimum of an isolated triangle is needed.
Set $z_A=\bigotimes_a z_a$, and let $\rho_R$ be the reduced density
of this same $f$ on $R$. It has trace one and weight-zero support.
The original-carrier density

$$
\rho=|\chi_p\rangle\langle\chi_p|\otimes
 |z_A\rangle\langle z_A|\otimes\rho_R
\tag{13.11}
$$

has the original global filling. All its crossing edges have zero
expectation, since each singlet has zero single-site spin expectation.
Equations (13.9)–(13.10) imply

$$
E\leq\operatorname{tr}(K\rho)
=-4b+\langle f,K_Rf\rangle\leq E.
\tag{13.12}
$$

Both inequalities use the actual whole-carrier $E$. Decompose $\rho_R$
spectrally into unit vectors $h$ with positive weights, all at weight
zero. Every $\chi_p\otimes z_A\otimes h$ has energy at least $E$;
their average equals $E$, so each is a ground vector. Choose one and
call it $\Xi$. For $R=\varnothing$, its factor is $\mathbb C$,
$\rho_R=1$, $h=1$ and $K_R=0$; the same argument applies.

Choose any labeling $T_1=\{a_1,a_2,a_3\}$ and put
$D=\{p,a_1,a_2,a_3\}$. This induced graph is the actual $K_4$ of
(13.7). On two spin-one sites use the classical unit singlet
$d_1$ of (12.5), explicitly

$$
d_1=\frac{|1,-1\rangle-|0,0\rangle+|-1,1\rangle}{\sqrt3},
\qquad
w_D=(d_1)_{p,a_1}\otimes(d_1)_{a_2,a_3}.
\tag{13.13}
$$

Here each ket in $d_1$ records the two magnetic coordinates; each
site is in its actual triplet subspace (13.4). The primary coupling
convention is [NIST DLMF (34.1.1) and (34.3.1)](https://dlmf.nist.gov/34.3#E1),
with $j_1=j_2=1$ and coupled spin zero. The total ladders also
annihilate (13.13) directly by their $\sqrt2$ coefficients.
Thus $w_D$ is a unit total singlet with total weight zero and with
zero expectation of every single-site spin component.

On a pair in $d_1$, its total Casimir is zero and each site's is
$2I$, so $\langle\boldsymbol J_i\cdot\boldsymbol J_j\rangle=-2$.
Singlet rotations equate the three same-axis expectations.
Its positive XY edge consequently has expectation
$2(-2/3-2/3)=-8/3$. The other four edges of $K_4$ join different
singlet pairs and have zero expectation in their product. Therefore

$$
\langle w_D,K_Dw_D\rangle=-\frac{16}{3}.
\tag{13.14}
$$

This is the four-singleton-part singlet trial of (10.9), used as a
local intermediate, not an exact energy formula.

In $\Xi$, the same set $D$ has state $\chi_p\otimes z_1$, with
internal energy $-4$. It is a tensor factor independent of all
remaining sites. Every single-site spin expectation in this factor
is zero: the ladders annihilate $\chi_p$, and $z_1$ is a singlet.
The vector on the remaining sites is precisely
$\eta=(\bigotimes_{a=2}^b z_a)\otimes h$.
Replace only this four-site factor by $w_D$, leaving $\eta$
unchanged. The resulting unit vector $\widetilde\Xi=w_D\otimes\eta$
is in the same original $\mathcal H_m$: both four-site factors have
total weight zero, hence occupancy four, and the remaining coordinates
are unchanged. Every edge from $D$ to its complement has zero
expectation both before and after the replacement, by the tensor
product and the zero single-site expectations just established.
All internal edges on the complement have the same expectation.
Thus, even with arbitrary attachments at any vertex of $D$,

$$
\langle\widetilde\Xi,K\widetilde\Xi\rangle
=E-\frac{16}{3}+4=E-\frac43<E,
\tag{13.15}
$$

contradicting the definition of $E$.

This excludes every nonsymmetric summand at energy $E$. An arbitrary
complex ground vector decomposes orthogonally as in (13.5), with each
nonzero component still a ground vector because its projection
commutes with $K$. All its nonsymmetric components therefore vanish,
proving (13.2), including entangled vectors and superpositions.

Finally the original fibre permutations commute with $K$, so
$\mathcal N$ reduces it. It is nonzero: take $\chi$ in one fibre
and a unit one-particle vector in each other fibre. The tensor has
occupancy $m$ and is killed by $P_{\mathrm{sym}}$. This includes
$m=2$. The nonempty finite spectrum of $K|_{\mathcal N}$ excludes
$E$ by (13.2), so its minimum exceeds $E$. On
$\operatorname{ran}P_{\mathrm{sym}}$, $K-EI\succeq0$; on
$\mathcal N$, $K-EI\succeq gI$. The two subspaces are orthogonal
and reducing, so adding their quadratic forms gives the operator
inequality in (13.3) for every complex vector. Its quadratic form
on a unit $\phi$ gives the asserted mass bound.

The added inference is (13.10)–(13.15): the neighbor-singlet bound
permits the product of the supplied triangle singlets, and absorbing
$p$ with one of those triangles into the supplied four-site singlet
trial strictly lowers energy while every crossing expectation stays
zero. The triangle eigenvector's zero variance in Proposition 12.5
is fully retained. The Boolean representation, nonstrict comparison,
localization on $U$, singlet algebra and finite-spectrum finish are
consumed results. For the two-auxiliary construction also see
Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the spin-one sum of a pair of spin-half auxiliaries;
their negative Hamiltonian with nonnegative product couplings in
directions 1 and 3 does not supply this positive-adjacency endpoint.
$\square$

**推论 13.3（Every equal even fibre size on connected even-order block
graphs）。** Let $H$ be any finite connected simple unit-weight block
graph of even order $m\geq2$. For every integer $S\geq1$, put
$s=2S$, $k=mS$ and retain the entire original complex Boolean
carrier $\mathcal H_{mS}$, positive token adjacency $K=K_{mS}$
and original $P_{\mathrm{sym}}$. With
$E=\lambda_{\min}(K)$ and $\mathcal N=\ker P_{\mathrm{sym}}$,

$$
\begin{aligned}
\ker(K-EI)&\subseteq\operatorname{ran}P_{\mathrm{sym}},\\
\mathcal N&\ne\{0\},\qquad K\mathcal N\subseteq\mathcal N,\\
g:=\lambda_{\min}(K|_{\mathcal N})-E&>0,\qquad
K-EI\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\qquad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{13.16}
$$

Proof. At $S=1$ these are Theorem 13.2 with exactly the original
carrier, operator and entire-carrier minimum. For every integer
$S\geq2$, the ground-vector assertion is precisely the supplied
Theorem 12.2 under the same graph hypotheses and parameters
$s=2S$, $k=mS$. Its orthogonal decomposition (6.12) includes all
local spins $J_i=S-t_i$, their multiplicities $r_{2S}(t_i)$ and
the full global-zero-weight slice, so its every-vector assertion
also includes arbitrary complex entangled superpositions.

For completeness the spectral implications use only that assertion.
Original fibre permutations commute with $K$, hence
$P_{\mathrm{sym}}$ and $\mathcal N$ reduce it. A nonconstant
one-particle vector in one fibre, any occupancy-$2S-1$ vector in a
second fibre, and occupancy-$S$ vectors in all others give a nonzero
tensor in $\mathcal N$ with occupancy
$1+(2S-1)+(m-2)S=mS$. This includes $m=2$ and $S=1$.
Every eigenvector of $K|_{\mathcal N}$ is an eigenvector of the
original $K$. Its eigenvalue is at least $E$, and equality is
excluded by the ground-vector assertion. Finite dimension gives
$g>0$. The quadratic forms on
$\operatorname{ran}P_{\mathrm{sym}}$ and $\mathcal N$ are respectively
at least zero and at least $g$ times squared norm after subtracting
$E$. Adding them proves the operator inequality on the entire
carrier, and evaluating at a unit $\phi$ proves the last line.

The added range is $S=1$ at the all-$K_4$-incidence vertices;
the $S\geq2$ assertion and its spectral consequences are consumed
from Theorem 12.2 and Corollary 12.3. All graph-block sizes,
articulation incidences and the boundary $m=2$ remain included.
The conclusion is qualitative and supplies no exact $E$, exact
$g$ or rate. It asserts no extension to arbitrary base graphs,
disconnected bases with only global filling, other fillings,
weighted edges, odd or unequal Boolean fibre sizes. The cited
intermediates and this inference carry no worldwide priority
assertion. $\square$

## 追加锚（本行以下为增补区）
## 14. One bipartite component in each neighborhood and arbitrary-core coronas

**定义 14.1（A component condition on the original base）。** Let $H$
be a finite connected simple unit-weight graph of even order $m\geq2$.
Assume that, for every $p\in V(H)$, the induced open neighborhood
$H[N_H(p)]$ has at least one bipartite connected component. A singleton
component counts as bipartite; the other components are unrestricted.
For any integer $S\geq1$, set $s=2S$, $k=mS$ and use the original
fibres $B_i$, blow-up $H[\overline{K_{2S}}]$, entire complex Boolean
carrier $\mathcal H_{mS}$, positive ordinary token adjacency $K=K_{mS}$
and original within-fibre projection $P_{\mathrm{sym}}$ of Definitions
1.1–1.2. Put

$$
E=\lambda_{\min}(K),\qquad \mathcal N=\ker P_{\mathrm{sym}}.
\tag{14.1}
$$

Only the global token number $mS$ is fixed. In particular, no weight
or occupancy is prescribed separately on a neighborhood component.

**定理 14.2（Confinement from one bipartite neighborhood component）。**
For every $H,S$ of Definition 14.1, every $E$-ground vector lies in
$\operatorname{ran}P_{\mathrm{sym}}$. The actual subspace $\mathcal N$
is nonzero and reduces $K$, and

$$
\begin{aligned}
g&:=\lambda_{\min}(K|_{\mathcal N})-E>0,\\
K-EI&\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\qquad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{14.2}
$$

All local-spin sectors, multiplicity copies and complex superpositions
are included, also when $S=1$ or $m=2$.

Proof. Use the complete Boolean-chain decomposition (6.6)–(6.12).
It does not require a flat least mode. A fibre has every integer spin
$J_i=S-t_i$, $0\leq t_i\leq S$, with multiplicity
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$. Each tensor of
chains retains its entire slice

$$
\mathcal X_t=\{x\in\mathbb Z^m:|x_i|\leq J_i,\ \sum_i x_i=0\}.
\tag{14.3}
$$

Its occupancy at $i$ is $S+x_i$, its ladder coefficients are exactly
$b_{J_i}^{\pm}(x_i)$ of (6.10), including their endpoint zeros, and
its operator is

$$
K_{\boldsymbol J}=\sum_{\{i,j\}\in E(H)}
(J_i^+J_j^-+J_i^-J_j^+)
=2\sum_{\{i,j\}\in E(H)}(X_iX_j+Y_iY_j).
\tag{14.4}
$$

Here $Z_i|x_i\rangle=x_i|x_i\rangle$,
$X_i=(J_i^++J_i^-)/2$ and $Y_i=(J_i^+-J_i^-)/(2i)$.
Every slice (14.3) contains the all-zero configuration.
$P_{\mathrm{sym}}$ selects precisely $t=0$.
The classical representation parameters are Srinivasan,
[Theorem 1.2 and its representation derivation on pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
Boolean rank $n=2S$, starting rank $t_i$, raising operator $L_i^*=J_i^+$;
and Feinsilver, [§§3–4, (8), (10), (16), Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $2S-2t_i=2J_i$. Orthogonality, normalized ladder
coefficients and all multiplicities are the supplied representation,
not restrictions on an input state.

The token convention is the singleton-difference definition
[tokenGraph](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and [its corresponding definition](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs).
The move bijection and energy identity Test.toNbr_bij and
Test.token_energy in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
give the move accounting in (2.4); its complex_real_energy,
complex_real_norm and real_complex_rayleigh, with
[the minimum and result explanations](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs),
give the same complex Rayleigh convention as (1.2).
These inputs concern the carrier, adjacency and quadratic form;
their particular refutations and phase energies are not used.
The top-chain normalization is the two-letter instance of
sector_words_card_multinomial and sector_gram in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and [its cardinality and Gram statements](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs),
with counts $(2S-n_i,n_i)$, including $n_i=0,2S$.
For the exact identification in Proposition 6.3 with
[the collective-oscillator theory, Definitions 1.1–1.2](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
the parameters are $d=m$, $N=2S$, Boolean labels $g=0,e=1$ and
$B=A(H)$: $a_{i,2S}=L_i/\sqrt{2S}$ and
$H_{2S}(A(H))=\hbar K/(2S)$ on this two-state carrier.
No fixed-low-excitation approximation is used at excitation $mS$.
In Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
(14.4) is adjacency $A(F_{mS}(H[\overline{K_{2S}}]))$;
their shifted XY block is the different operator $WI/2-K$.

We first extend the local input of §7. Let $G$ be a nonempty finite
simple unit-weight graph with at least one bipartite connected
component $C$, and let $D=V(G)\setminus C$. Put spin $S$ at every
vertex. Let $K_G$ be the operator (14.4) for $G$ and $e$ its minimum
on the full total-zero-weight space. We show that this ground space
contains a vector not annihilated by both total ladders. No condition
is placed on $G[D]$.

If a ground vector already has this property, there is nothing to
prove. Otherwise choose a unit ground vector $v$ killed by both
ladders. Their commutator also kills it by total $Z$, so all three
total spin components kill it. Thus $v$ is a total singlet, fixed by
all simultaneous spin rotations. Its reduced density on $C$ is
rotation-invariant: conjugating on $C$ can be transferred, using this
invariance of $v$, to a unitary on $D$, which disappears under the
partial trace. In the classical orthogonal spin decomposition of the
$C$ factors it therefore has the form

$$
\rho_C=\bigoplus_q I_{V_q}\otimes A_q,\qquad A_q\succeq0,\qquad
\sum_q(2q+1)\operatorname{tr}A_q=1.
\tag{14.5}
$$

Here $V_q$ is the spin-$q$ representation and the second factor is
its full multiplicity space. To see the decomposition directly, the total operators on $C$ obey
$[L,U]=-2Z_C$, $[Z_C,U]=U$ and $L=U^*$, as in (6.6).
In any nonzero invariant orthogonal remainder, choose a unit vector
$h$ at its smallest weight $-q$. Then $Lh=0$ and
$\|Uh\|^2=2q\geq0$. Repeated commutation gives
$LU^a h=a(2q-a+1)U^{a-1}h$ and
$\|U^a h\|^2=a!(2q)!/(2q-a)!$ for $0\leq a\leq2q$,
with $U^{2q+1}h=0$. The resulting spin-$q$ chain is invariant,
and its orthogonal complement is invariant because $L=U^*$ and
$Z_C=Z_C^*$. Iteration exhausts the finite space. All $q$ are
integers, since all original weights are integers. On inequivalent
chains a rotation-intertwining operator is zero, while between two
spin-$q$ chains it is scalar on the chain coordinate: it preserves
weights and commuting with $U$ makes all its weight-diagonal entries
equal. This gives precisely (14.5), with arbitrary operators on the
multiplicity factors. Every $V_q$ contains exactly one vector of
weight zero. Consequently, with $Z_C=\sum_{i\in C}Z_i$,

$$
\|\mathbf1_{Z_C=0}v\|^2
=\operatorname{tr}(\rho_C\mathbf1_{Z_C=0})
=\sum_q\operatorname{tr}A_q>0.
\tag{14.6}
$$

Set $w=\mathbf1_{Z_C=0}v\ne0$. Since $C$ is a connected component,
$K_G=K_C\otimes I+I\otimes K_D$, and its projection to $Z_C=0$
commutes with $K_G$. Thus $K_Gw=ew$, with $Z_Cw=Z_Dw=0$.
This selects a nonzero part of the same globally feasible vector;
it has not assumed zero weight on components of an arbitrary vector.
All other globally feasible component weights remain in the minimum $e$.

If $C$ is a singleton $\{c\}$, write $w=|S,0\rangle_c\otimes h$,
where $h\ne0$ has $Z_D=0$. This is still a ground vector. For
$B_G^+=\sum_{i\in V(G)}J_i^+$, the two terms in

$$
B_G^+w=\sqrt{S(S+1)}\,|S,1\rangle_c\otimes h
+|S,0\rangle_c\otimes\sum_{i\in D}J_i^+h
\tag{14.7}
$$

are orthogonal. Its squared norm is at least
$S(S+1)\|h\|^2>0$. Normalizing $w$ gives the required choice.
This includes $D=\varnothing$, where its factor is $\mathbb C$.

Suppose instead that $C$ has an edge. For $\alpha=x,y,z$ put
$T_\alpha=\sum_{\{i,j\}\in E(G)}J_i^\alpha J_j^\alpha$.
Since $v$ is a singlet and $2(T_x+T_y)v=ev$, simultaneous rotations
interchanging the axes also give
$2(T_x+T_z)v=ev$ and $2(T_y+T_z)v=ev$.
Adding these last two equations and subtracting the first yields

$$
T_zv=(e/4)v,\qquad
T_z|x\rangle=q_G(x)|x\rangle,\qquad
q_G(x)=\sum_{\{i,j\}\in E(G)}x_ix_j.
\tag{14.8}
$$

The projection defining $w$ commutes with $T_z$, so this equation
also holds on $w$.

On the $Z_C=0$ slice, a bipartition side $C_+$ defines the unitary
sign $U_C|x\rangle=(-1)^{\sum_{i\in C_+}(S+x_i)}|x\rangle$.
Every move crosses the bipartition and changes the exponent by one,
so $U_CK_CU_C^*=-K_C$. The matrix of $K_C$ has nonnegative
entries and its configuration graph on this slice is connected.
Indeed the independent $2S$-blow-up of connected $C$ with an edge
is connected. Its edge transpositions generate all vertex
permutations: the transposition of the endpoints of a path is a
product of the successive edge transpositions and their reverses.
These permutations act transitively on subsets of any fixed
cardinality. Removing steps that leave a subset fixed gives token
paths. Their block-occupancy images connect all configurations
$|x_i|\leq S$, $\sum_{i\in C}x_i=0$, and every nontrivial image
step has the strictly positive coefficients (6.10).
Perron–Frobenius and the sign conjugation therefore show that the
least eigenspace of $K_C$ on this slice is a line with a unit
spanning vector $u_C$ nonzero at every configuration.
This is the connected-component argument of §7; no sign
conjugation on $D$ or on $G$ is asserted.

Let $e_C(0)$ and $e_D(0)$ be the two slice minima. The $D$ slice
is nonempty, since all its spins are integers; if $D$ is empty,
its space is $\mathbb C$, $K_D=0$ and $e_D(0)=0$.
Their product slice is contained in the space defining $e$, so
$e\leq e_C(0)+e_D(0)$. Conversely its operator is at least
$(e_C(0)+e_D(0))I$, and $w\ne0$ is its eigenvector at $e$.
Hence equality holds. Positivity of the two excess operators then
implies $w=u_C\otimes h_D$ with $h_D\ne0$ in the $D$ slice.
This equality of minima is a consequence of the selected ground
vector, not a decomposition assumption on the global minimum.

Choose any configuration $y$ with $h_D(y)\ne0$. Full support of
$u_C$ and (14.8) imply

$$
q_C(x)+q_D(y)=e/4
\qquad\text{for every }x\text{ with }|x_i|\leq S,\quad
\sum_{i\in C}x_i=0.
\tag{14.9}
$$

For the all-zero $x$, $q_C(x)=0$. For an edge $\{a,b\}$ of $C$,
take $x_a=1,x_b=-1$ and all other coordinates zero; then
$q_C(x)=-1$. Both configurations are allowed for every $S\geq1$.
They contradict (14.9). Thus, for an edged bipartite component,
no ground vector of the full $G$ slice can be a singlet. Together
with (14.7) this proves the local choice for every allowed $G$,
including arbitrary nonbipartite components and all empty outside
factors. The local obstruction (7.6)–(7.10) is consumed here with
its bipartite argument confined to $C$; the additional inference
is that unrestricted other components do not invalidate the choice.

Now suppose a nonsymmetric sector in (6.12) has minimum $E$, and
choose $p$ with $J_p<S$. Use the nonstrict fixed-zero-weight
comparison (7.4)–(7.5) to increase every other local spin to $S$.
It applies with arbitrary other integer spins, including zero.
Each intermediate sector occurs in the same original carrier, so
its minimum cannot be below $E$ and must remain $E$.
The primary comparison is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412):
maximal local spin $s_i=S$, variable local spin $t_i=J_i$, $M=0$
and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
Only nonstrict comparison is used. In §7 its zero-weight triplet
has zero Cartesian expectations, and its upper-spin projection has
squared coefficient $((j+1)^2-x^2)/((j+1)(2j+1))>0$ at every
$-j\leq x\leq j$. Distinct weights have orthogonal images, so the
induction applies to entangled inputs, starting at $j=0$ and including
endpoints. No equality exclusion is imported from that comparison.

Realize the resulting spin $J_p$ by the symmetric space on $2J_p$
of the original $2S$ coordinates at $p$ and $S-J_p$ disjoint
singlet pairs, as in §7. This intertwines the collective spins:
the pair operators annihilate each singlet, and at weight $x_p$
the occupancy is $(J_p+x_p)+(S-J_p)=S+x_p$.
All multiplicity copies have the same matrix, so this realization
preserves the minimum even if a different copy supplied it.
Choose one pair and write a unit ground vector as
$\Psi=|0,0\rangle\otimes f$. The remaining original auxiliaries,
all other fixed pairs and arbitrary entanglement stay in $f$.
Put

$$
A=N_H(p),\quad R=V(H)\setminus(\{p\}\cup A),\quad
B_A^\pm=\sum_{i\in A}J_i^\pm,\quad Z_A=\sum_{i\in A}Z_i.
\tag{14.10}
$$

Connectedness gives $A\ne\varnothing$. Release only the chosen
pair into $|1,0\rangle$, giving $\Theta=|1,0\rangle\otimes f$.
Both pair states have weight zero and zero spin expectations; there
are no intrafibre interactions. Thus $\Theta$ lies in the same
$\mathcal H_{mS}$ with Rayleigh quotient $E$. Equality at the actual
minimum implies the eigenvector equation, since the nonnegative
spectral excesses $(\lambda-E)|c_\lambda|^2$ sum to zero.
Omitting the pair gives $K^{\mathrm{rem}}f=Ef$.
Its spin-one coefficients at weight zero are $\sqrt2$, so

$$
0=(K-EI)\Theta
=\sqrt2|1,1\rangle\otimes B_A^-f
+\sqrt2|1,-1\rangle\otimes B_A^+f.
\tag{14.11}
$$

Orthogonality yields $B_A^-f=B_A^+f=0$, and their commutator gives
$Z_Af=0$. In each spin-$q$ irreducible, the two ladder norms can
both vanish only for $q=0$. Hence $f$ is in the total-singlet space
$\mathcal S_A$ on $A$, tensored with the joint zero-weight space of
the remaining auxiliaries at $p$ and all sites of $R$.

For $i\in A$, every single-site spin component has zero matrix
elements between singlets on $A$. Simultaneous rotations fix both
singlets and rotate these three matrix elements as a vector; the
only vector fixed by all rotations is zero. This identity can be
tensored with any operator on the other factors, so crossing
interactions have zero expectation even for entangled $f$.
There are no edges between $p$ and $R$. Therefore

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle,
\tag{14.12}
$$

where $K_A,K_R$ are the induced operators with the unchanged
spin-$S$ factors. The local conclusion just proved, applied to
$G=H[A]$, supplies a unit ground vector $u_A$ on its full $Z_A=0$
slice, with energy $e_A$, not annihilated by both $B_A^\pm$.
Let $\rho_{pR}$ be the reduced density of this same $f$ on all
remaining factors. It has trace one and joint zero-weight support.
In the original half-filled carrier form

$$
\rho=|0,0\rangle\langle0,0|\otimes
|u_A\rangle\langle u_A|\otimes\rho_{pR}.
\tag{14.13}
$$

Since $u_A$ has definite weight zero,
$\langle u_A,J_i^\pm u_A\rangle=0$ for every $i\in A$.
Thus all crossing expectations in (14.13) vanish, and

$$
E\leq\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{14.14}
$$

Both comparisons use the same entire-carrier minimum $E$.
Spectrally decompose $\rho_{pR}$ into unit vectors $h$ with positive
weights, all in its actual joint zero-weight support. Every
$|0,0\rangle\otimes u_A\otimes h$ has energy at least $E$;
their average is $E$, so each is a ground vector. Apply the same
pair release (14.11) to any one. It forces
$(B_A^-u_A)\otimes h=(B_A^+u_A)\otimes h=0$, contrary to the
choice of $u_A$. If $R=\varnothing$, its factor is $\mathbb C$
and $K_R=0$; the remaining original auxiliaries at $p$ are still
retained in $\rho_{pR}$ and $h$. The argument also permits no
remaining auxiliaries, interpreting their tensor product as $\mathbb C$.

This is the strict replacement (7.11)–(7.15) with the enlarged local
input, without separately optimizing any outside state or component
weight. For its two-auxiliary precedent see Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the collective spin of a pair of spin-half auxiliaries;
their strictness concerns a negative Hamiltonian with nonnegative
product couplings in directions 1 and 3. Those hypotheses do not
supply strictness for positive adjacency on the present possibly
nonbipartite $H$.

We have excluded energy $E$ from every $t\ne0$ sector. The orthogonal
decomposition reduces $K$ and $P_{\mathrm{sym}}$ and retains every
copy. Each nonzero component of any complex ground vector is itself
a ground vector, so every such vector has only $t=0$ components.
Fibre permutations commute with $K$, hence $\mathcal N$ reduces it.
It is nonzero: take a nonzero one-particle vector orthogonal to
constants in one fibre, occupancy $2S-1$ in a second fibre, and
occupancy $S$ in every other fibre. The tensor is killed by
$P_{\mathrm{sym}}$ and has occupancy
$1+(2S-1)+(m-2)S=mS$, also for $S=1,m=2$.
The finite nonempty spectrum of $K|_{\mathcal N}$ excludes $E$,
so its minimum is strictly greater than $E$. On
$\operatorname{ran}P_{\mathrm{sym}}$, $K-EI\succeq0$ by the
whole-space definition of $E$; on $\mathcal N$, $K-EI\succeq gI$.
Adding their quadratic forms proves (14.2) on the entire complex
carrier, including all entangled superpositions. Unit normalization
and division by $g>0$ give its last inequality.

The additional graph-domain inference is the local selection
(14.5)–(14.9) with unrestricted $D$, followed by the supplied strict
replacement. The full-state certificate, flat-domain bounds, odd-scale
results, complete multipartite results and all-even block-graph result
of §§1–13 retain their distinct hypotheses and conclusions.
The representations, nonstrict comparison, singlet matrix elements
and finite-spectrum implications are reused intermediates. No exact
$E$, numerical $g$ or rate is supplied. The arbitrary connected
even-order base problem without the component condition remains
unresolved by these results; failure of this sufficient condition
is not a counterexample. Other fillings, weights, odd or unequal
Boolean fibres are outside the assertion. $\square$

**推论 14.3（A pendant leaf at every vertex of an arbitrary core）。**
Let $F$ be any nonempty finite connected simple unit-weight graph.
For every $v\in V(F)$ retain a core vertex $c_v$ and adjoin one
distinct leaf $\ell_v$ whose only neighbor is $c_v$. Let
$H=F\mathbin\circ K_1$ have exactly the core edges of $F$ and
these leaf edges. Then every conclusion of Theorem 14.2 holds on
the original complete complex half-filled carrier of $H$ at every
integer $S\geq1$, including a one-vertex core.

Proof. Write $r=|V(F)|\geq1$. The graph $H$ is finite, simple,
connected and unit-weight, of even order $m=2r\geq2$.
For a core vertex,

$$
H[N_H(c_v)]=F[N_F(v)]\ \sqcup\ \{\ell_v\}.
\tag{14.15}
$$

Indeed $\ell_v$ is adjacent only to $c_v$, which is outside the
open neighborhood; no other leaf is adjacent to $c_v$.
The singleton component in (14.15) is bipartite, regardless of the
other components. For a leaf $\ell_v$, its open neighborhood is
the singleton $\{c_v\}$, also bipartite. Thus Definition 14.1 holds
at every vertex. Theorem 14.2 applies with the original $2r$ fibres
of size $2S$, $k=2rS$, positive adjacency, original projection and
actual whole-carrier minimum. When $r=1$, $H=K_2$, so this includes
$m=2$ and $S=1$, without an outside vertex or a core edge.
Some of these applications are also supplied by previous hypotheses:
if $F$ is a tree, $H$ is a tree and hence a block graph, covered by
Corollary 13.3; clique cores of order at least four are the supplied
Proposition 12.4. The assertion here permits every connected core;
it does not assert that every corona lies outside the prior domains.
$\square$

**命题 14.4（Coronas outside all four supplied graph hypotheses）。**
For every integer $r\geq5$, let $F_r=K_r-\{a,b\}$ be the complete
graph with just the edge $\{a,b\}$ removed, and put
$H_r=F_r\mathbin\circ K_1$. Then $H_r$ has order $2r$ and all
conclusions (14.2) at every integer $S\geq1$. On $H_r$ itself,
the connected block-graph hypothesis of Corollary 13.3, the wholly
bipartite-neighborhood hypothesis of Definition 7.1, the complete
multipartite hypothesis of Corollary 11.3 and the flat-least-mode
hypothesis of Assumption 3.1 all fail.

Proof. The core is connected: its sole nonadjacent pair $a,b$ has
a common neighbor, and every other pair is adjacent. Corollary 14.3
therefore gives order $m=2r$, filling $k=2rS$ and every conclusion,
on the unchanged original carrier. In particular every core vertex
has its own isolated leaf component in its neighborhood, and a leaf
has a singleton neighborhood.

The core $F_r$ is two-connected. Deleting any one of its vertices
leaves a complete graph or a complete graph missing one edge on
$r-1\geq4$ vertices. Either is connected, since any missing pair
still has a third vertex joining them. It is a maximal two-connected
subgraph of $H_r$: a leaf cannot lie in a two-connected subgraph,
as it has degree at most one there. Thus this core is a graph block
of $H_r$. It is not a clique because $a,b$ are nonadjacent.
Consequently $H_r$ is not a block graph in the precise sense of
Definition 12.1 and Corollary 13.3.

At the core vertex $c_a$, the other core neighbors are the
$r-2$ vertices distinct from $a,b$. They induce $K_{r-2}$;
the remaining neighbor is its isolated leaf $\ell_a$.
Since $r-2\geq3$, this neighborhood contains a triangle and is not
bipartite. This disproves the wholly bipartite-neighborhood condition
on $H_r$, while its singleton component still meets Definition 14.1.

In a complete multipartite graph, distinct nonadjacent vertices must
belong to the same independent part. Choose two distinct core labels
$u,v$. In $H_r$, $\ell_u$ is nonadjacent to both $c_v$ and
$\ell_v$, whereas $c_v$ is adjacent to $\ell_v$.
These three relations are incompatible with any complete multipartite
partition. Thus $H_r$ fails that hypothesis, with arbitrary labelled
or unequal parts as well.

Finally let $A=A(F_r)$ and order the base adjacency coordinates as
cores followed by leaves. Then

$$
a_r=A(H_r)=\begin{pmatrix}A&I\ I&0\end{pmatrix}.
\tag{14.16}
$$

Choose any core edge $\{u,v\}$. Give a vector $w$ the coordinates
$w_{c_u}=1$, $w_{c_v}=-1$, $w_{\ell_u}=-1$,
$w_{\ell_v}=1$, and zero elsewhere. Its squared norm is four.
Only the core edge and these two leaf edges contribute to its
adjacency quadratic form, each with endpoint product $-1$ and both
orientations. Hence $\langle w,a_rw\rangle=-6$, and the actual
least base eigenvalue satisfies $\lambda_{\min}(a_r)\leq-3/2<-1$.
For any complex eigenvector $z$ at this least eigenvalue $\lambda$,
the leaf equations in (14.16) are $\lambda z_{\ell_v}=z_{c_v}$.
If every coordinate had modulus one, they would force $|\lambda|=1$,
a contradiction. This rules out the exact complex flat least mode
of Assumption 3.1 on $H_r$; it does not require a formula for that
base eigenvalue or for the many-body $E$.

Thus these coronas exhibit the graph-domain addition while the
classical spin tools and spectral implications remain the supplied
intermediates. No priority assertion or conclusion for arbitrary
connected even-order bases follows from the four failed sufficient
hypotheses. $\square$

## 追加锚（本行以下为增补区）

## 15. Five-rim and flat-neighborhood confinement

**定义 15.1（Two neighborhood classes on the original carrier）。**
Let $H$ be a finite connected simple unit-weight graph of even order
$m\geq2$. For an integer $S\geq1$ use precisely the Boolean fibres
$B_i$ of size $s=2S$, the whole complex space $\mathcal H_{mS}$,
positive token adjacency $K=K_{mS}$ and original fibre-permutation
projection $P_{\mathrm{sym}}$ of Definitions 1.1–1.2. Put

$$
E=\min\operatorname{spec}K,\qquad
\mathcal N=\ker P_{\mathrm{sym}},\qquad
G_p=H[N_H(p)].
\tag{15.1}
$$

Consider the following two conditions on $H$:

(a) For every $p$, $G_p$ is bipartite or isomorphic to $C_5$.

(b) For every $p$, $G_p$ is bipartite, or it has at least one edge
and, writing $a_p=A(G_p)$ and $\lambda_p=\min\operatorname{spec}a_p$,
there is $z\in\mathbb C^{N_H(p)}$ with
$a_pz=\lambda_pz$ and $|z_i|=1$ at every coordinate.

No connectedness is imposed on $G_p$, and isolated vertices are
allowed in the bipartite alternative. The modulus-one condition in
(b) concerns the least eigenvalue of the whole induced neighborhood,
not an independently chosen eigenvalue of each component.

**定理 15.2（Every ground vector in the two neighborhood classes）。**
If (a) holds, then for every integer $S\geq1$; if (b) holds, then for
every integer $S\geq2$, the space $\mathcal N$ is nonzero and reduces
$K$, and

$$
\begin{aligned}
\ker(K-EI)&\subseteq\operatorname{ran}P_{\mathrm{sym}},\\
g&=\min\operatorname{spec}(K|_{\mathcal N})-E>0,\\
K-EI&\succeq g(I-P_{\mathrm{sym}}),\\
\|(I-P_{\mathrm{sym}})\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\quad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{15.2}
$$

Every spectrum, projection and expectation in (15.2) is on the
original full complex carrier. In particular $E$ is not a minimum
restricted in advance to the symmetric space.

Proof. We first supply the local choice needed by the replacement
argument of §14. For a nonempty finite graph $G$ put spin $S$ at
all its $n$ vertices, with the normalized integer-weight bases and
ladders (6.10). Write $J_i^x=X_i$, $J_i^y=Y_i$, $J_i^z=Z_i$ and

$$
\begin{aligned}
K_G&=\sum_{\{i,j\}\in E(G)}(J_i^+J_j^-+J_i^-J_j^+)
=2(T_x+T_y),\\
T_\alpha&=\sum_{\{i,j\}\in E(G)}J_i^\alpha J_j^\alpha,
\qquad B_G^\pm=\sum_iJ_i^\pm,\qquad Z_G=\sum_iZ_i.
\end{aligned}
\tag{15.3}
$$

Let $e_G$ be the minimum of $K_G$ on its entire $Z_G=0$ space,
including all feasible component weights. We claim that this space
has a unit ground vector not killed by both $B_G^\pm$, whenever
$G$ is bipartite and $S\geq1$, or $G=C_5$ and $S\geq1$, or $G$
has an edge and a flat least mode and $S\geq2$.
For the bipartite alternative, this is exactly the local conclusion
(7.6)–(7.10), also included in (14.5)–(14.9). It covers disconnected
bipartite graphs and their singleton components. In the edgeless
case its choice is $\bigotimes_i|S,0\rangle$, whose raised squared
norm is $nS(S+1)>0$. We use that supplied conclusion unchanged.

Suppose now that $G$ has an edge and a modulus-one least eigenvector
$z$, with $a_Gz=\lambda z$. Here $\lambda<0$: an edge-endpoint
difference has negative adjacency quadratic form. If $v$ is any
unit total singlet, simultaneous rotations show that its three
expectations $\langle T_\alpha\rangle_v$ are equal. Put
$F_\alpha=\sum_i e_i\otimes J_i^\alpha v$. The finite-dimensional
spectral quadratic form and the on-site Casimir identity give

$$
\begin{aligned}
\langle v,K_Gv\rangle
&=\frac23\sum_{\alpha=x,y,z}
 \langle F_\alpha,(a_G\otimes I)F_\alpha\rangle\\
&\geq\frac23\lambda\sum_{\alpha,i}\|J_i^\alpha v\|^2
=\frac23\lambda nS(S+1).
\end{aligned}
\tag{15.4}
$$

Indeed each summand before the inequality is $2\langle T_\alpha\rangle_v$,
since both orientations of every edge occur in $a_G$.
The Casimir is $X_i^2+Y_i^2+Z_i^2=S(S+1)I$ on spin $S$.
Neither regularity of $G$ nor simplicity of its least eigenspace
is required. This is the spectral quadratic-form method used in
Schmidt–Schnack–Luban,
[Theorem 1 and its proof](https://arxiv.org/pdf/cond-mat/0101228v1),
and Bärwinkel–Schmidt–Schnack,
[§3](https://arxiv.org/pdf/cond-mat/0210458v2).
Their isotropic-spin bounds have constant-row-sum assumptions, and
the latter's improvements require further homogeneity. We use the
explicit quadratic form (15.4), not those bounds outside their
hypotheses.

For an upper comparison on the same local spin-$S$ zero-weight
space use the supplied phase-subset vector (3.5)–(3.7). Its local
parameters are $m=n$, $s=2S$, $N=2nS$ and $k=nS$.
For $T\subseteq V(G)\times[2S]$ of size $nS$, set

$$
\Phi(T)=\binom{2nS}{nS}^{-1/2}
\prod_{(i,u)\in T}z_i.
\tag{15.5}
$$

It has norm one, is invariant under every within-fibre permutation,
and hence lies in the tensor product of the spin-$S$ factors, not
merely in the larger Boolean space. Its total weight is zero.
The count of subsets containing one specified coordinate and omitting
another is $\binom{2nS-2}{nS-1}$; the squared norm before normalization
is $\binom{2nS}{nS}$. Thus exactly as in (3.7),

$$
e_G\leq\langle\Phi,K_G\Phi\rangle
=\lambda nS^2\frac{2nS}{2nS-1}.
\tag{15.6}
$$

This is the existing complex phase count, not a new trial method.
Its classical fixed-magnetization precedent is
Bärwinkel–Schmidt–Schnack,
[§§2.2–2.3, (14)–(21)](https://arxiv.org/pdf/cond-mat/0210458v2),
where cyclic coupling is assumed; here the actual count uses just
the specified flat vector. In particular (15.6) does not infer a
spin-$S$ upper bound from a minimum over nonsymmetric Boolean states.

For $S\geq2$ the exact scalar comparison is

$$
S^2\frac{2nS}{2nS-1}-\frac23S(S+1)
=\frac{2S\{nS(S-2)+S+1\}}{3(2nS-1)}>0.
\tag{15.7}
$$

Multiplication by $\lambda n<0$ shows that the upper bound (15.6)
is strictly below the singlet lower bound (15.4). Therefore no
zero-weight ground vector can be a singlet. This includes $S=2$,
arbitrary complex vectors, disconnected $G$ and all degeneracies.

It remains to justify $G=C_5$ at $S=1$. Proposition 5.3 supplies
$\lambda=-\phi$, $\phi=(1+\sqrt5)/2$, and its flat Fourier vector.
If a unit singlet were a ground vector with energy $e_G$, (15.4)
and (15.6) would imply

$$
-\frac{20\phi}{3}\leq e_G\leq-\frac{50\phi}{9},
\qquad -12<e_G<-8.
\tag{15.8}
$$

The strict interval follows from $3/2<\phi<9/5$, using
$2<\sqrt5<13/5$. But the singlet eigenvector equation has an
additional constraint. Rotation of $2(T_x+T_y)v=e_Gv$ gives also
$2(T_x+T_z)v=e_Gv$ and $2(T_y+T_z)v=e_Gv$, as in (14.8).
Adding the last two and subtracting the first yields
$T_zv=(e_G/4)v$. In the spin-one weight basis $T_z$ is diagonal,
with values $\sum_{\{i,j\}\in E(C_5)}x_ix_j\in\mathbb Z$ since
$x_i\in\{-1,0,1\}$. A nonzero coordinate of $v$ therefore forces
$e_G\in4\mathbb Z$. There is no such number strictly between
$-12$ and $-8$, contradicting (15.8). Together with (15.7), this
proves the claimed local choice for every stated alternative and
all its endpoints. Being killed by both total ladders is equivalent
to being a total singlet, by their commutator and the spin-chain
ladder coefficients; thus the choice has the exact property required.

We now apply this local conclusion to the entire original carrier.
The Boolean chain decomposition (6.6)–(6.12) retains, independently
at every site, all integer spins $J_i=S-t_i$, $0\leq t_i\leq S$,
with multiplicities
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$, where
$\binom{2S}{-1}=0$. It gives the orthogonal reducing decomposition

$$
\begin{aligned}
\mathcal X_t&=\{x\in\mathbb Z^m:|x_i|\leq S-t_i,\ \sum_ix_i=0\},\\
\mathcal H_{mS}&\cong
\bigoplus_{t\in\{0,\ldots,S\}^m}
\ \bigoplus_{\alpha_i=1,\ldots,r_{2S}(t_i)}\ell^2(\mathcal X_t).
\end{aligned}
\tag{15.9}
$$

Here every $\mathcal X_t$ contains $x=0$, $P_{\mathrm{sym}}$ selects
exactly $t=0$, and on each copy $K$ is (15.3) with site spins $J_i$
and the coefficients (6.10), including their zero endpoint values.
This is the supplied representation, with Feinsilver,
[§§3–4, Propositions 4.1 and 4.3, §4.2.2](https://arxiv.org/pdf/1102.0368v2),
Boolean rank $2S$, starting rank $t_i$, principal number
$2S-2t_i=2J_i$, $T=L_i^*$ and $T^*=L_i$; and Srinivasan,
[Theorem 1.2 and pp. 4–5](https://arxiv.org/pdf/1001.0280v2),
$n=2S$, starting rank $t_i$ and normalized up operator $L_i^*$.
It imposes no symmetry on an input vector.

The supplier correspondences of §§1–5 remain the same in (15.9).
In [OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs),
the two-letter occupancy counts are $(2S-n_i,n_i)$; the full word
cardinality and Gram formulas, including their proof-local counting
recurrences, normalize the top Dicke chain. The exact algebraic map
to [the collective-oscillator supplier](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
is $d=m$, $N=2S$, $g=0$, $e=1$, $B=A(H)$,
$a_i=L_i/\sqrt{2S}$ and $H_{2S}=\hbar K/(2S)$.
No low-excitation approximation is applied at occupancy $mS$.
The singleton-difference adjacency in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
is precisely the coefficient-one move in (2.4).
The complete phase-count supplier
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
provide `Test.move`, `Test.toNbr_bij`, `Test.token_energy`,
`counting_identity`, `W_move`, the phase normalization and the
real/complex Rayleigh comparison used in (3.5)–(3.7).
Their cut and Laplacian refutations are not needed as new conclusions
here. Positive adjacency agrees with Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3);
their shifted XY block is $WI/2-K$, a different operator.

Suppose a summand of (15.9) with $t\ne0$ had minimum $E$.
Choose $p$ with $J_p<S$. By the supplied nonstrict comparison
(7.4)–(7.5), raise all other spins to $S$, leaving $J_p$ unchanged.
Each resulting sector is present in the same carrier (15.9), so its
minimum is at least $E$; nonstrictness makes it at most $E$.
Thus every step preserves the actual minimum $E$.
The original comparison is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412),
with maximal spin $s_p=S$, variable spin $t_p=J_p$, $M=0$ and
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
It supplies existence after increasing spin, not every-ground-vector
strictness. The squared upper-spin projection (7.4) is positive at
every $-j\leq x\leq j$, also $j=0$; distinct weights have orthogonal
images. Hence its nonstrict induction applies to all the entangled
vectors and zero-spin factors just used.

Realize spin $J_p$ by $2J_p$ symmetric original Boolean coordinates
at $p$ together with $S-J_p$ singlet pairs, exactly as in §14.
The collective spins annihilate each pair; the occupancy at weight
$x_p$ is $(J_p+x_p)+(S-J_p)=S+x_p$. Thus this is an actual copy
inside the unchanged original fibre. Every multiplicity copy has
the same operator, so this realization preserves its minimum.
Choose one pair and a unit ground vector
$\Psi=|0,0\rangle\otimes f$, retaining all remaining original
auxiliaries, other fixed singlets and entanglement in $f$.
Put $A=N_H(p)$, $R=V(H)\setminus(\{p\}\cup A)$ and
$B_A^\pm=\sum_{i\in A}J_i^\pm$. Connectedness gives $A\ne\varnothing$.
Release only that pair to $\Theta=|1,0\rangle\otimes f$.
Both pair states have weight zero and zero Cartesian spin expectations;
there is no intrafibre interaction. Therefore $\Theta$ is in the same
$\mathcal H_{mS}$ with expectation $E$, and is a ground eigenvector.
The Rayleigh equality implication follows by expanding in an
orthonormal eigenbasis: all $(\theta-E)|c_\theta|^2$ are nonnegative
and their sum is zero.

Omitting the pair gives $K^{\mathrm{rem}}f=Ef$. The spin-one ladder
coefficients at weight zero are $\sqrt2$, so the ground equation is

$$
0=(K-EI)\Theta
=\sqrt2|1,1\rangle\otimes B_A^-f
 +\sqrt2|1,-1\rangle\otimes B_A^+f.
\tag{15.10}
$$

The two pair weights are orthogonal. Thus $B_A^-f=B_A^+f=0$ and,
by the commutator, $Z_Af=0$. In the complete spin decomposition on
$A$, the common ladder kernel consists exactly of spin-zero chains.
Consequently $f$ is supported on the total-singlet space $\mathcal S_A$
tensored with the joint zero-weight space of all remaining factors
at $p$ and $R$.

For $i\in A$, sandwiching any one-site Cartesian spin component
between the projections onto $\mathcal S_A$ gives zero: simultaneous
rotations fix both singlets and rotate these matrix elements as a
three-vector, whose only rotation-invariant value is zero.
This identity remains true with an arbitrary operator on the other
factors. It therefore removes all crossing expectations even when
$f$ is entangled. Since there are no $p$–$R$ edges, with $K_A,K_R$
the induced spin-$S$ operators one obtains

$$
E=\langle f,K_Af\rangle+\langle f,K_Rf\rangle.
\tag{15.11}
$$

The local choice above, for the actual $G_p=H[A]$, supplies a unit
ground vector $u_A$ on the full $Z_A=0$ slice, with energy $e_A$,
not killed by both $B_A^\pm$. Let $\rho_{pR}$ be the reduced density
of this same $f$ on all the remaining factors. It has trace one and
joint zero-weight support. Form, inside the original half-filled space,

$$
\rho=|0,0\rangle\langle0,0|\otimes
|u_A\rangle\langle u_A|\otimes\rho_{pR}.
\tag{15.12}
$$

Each $\langle u_A,J_i^\pm u_A\rangle$ is zero because $u_A$ has
definite total weight zero. Thus crossing expectations in this product
state vanish, and

$$
E\leq\operatorname{tr}(K\rho)
=e_A+\langle f,K_Rf\rangle
\leq\langle f,K_Af\rangle+\langle f,K_Rf\rangle=E.
\tag{15.13}
$$

The second inequality uses only that the $A$ support of $f$ has weight
zero; it does not replace the other factors by a separately attainable
optimum. Spectrally decompose the same $\rho_{pR}$ into unit vectors
$h$ with positive weights. Each remains in its actual joint
zero-weight support. Their product vectors
$|0,0\rangle\otimes u_A\otimes h$ have energies at least $E$ and
average energy $E$ by (15.13); hence each is an actual ground vector.
Apply the pair release (15.10) to any one. It forces
$(B_A^-u_A)\otimes h=(B_A^+u_A)\otimes h=0$, contradicting the
choice of $u_A$. If $R$ is empty, its factor is $\mathbb C$ and
$K_R=0$; all remaining auxiliaries at $p$ are still retained in
$\rho_{pR}$. If none remain either, their factor is also $\mathbb C$.

This uses the supplied same-carrier replacement (14.10)–(14.14)
with a different local input. Its two-auxiliary precedent is
Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the collective spin of a pair of spin-half auxiliaries;
their strictness assumes a negative Hamiltonian with nonnegative
product couplings in directions 1 and 3. It is not strictness for
the present positive adjacency on nonbipartite bases.

We have excluded $E$ from every deficient-spin sector of (15.9),
retaining all multiplicities and all globally feasible weights.
Any nonzero sector component of a complex ground vector is itself
a ground vector, so only $t=0$ components can occur. Fibre permutations
commute with $K$, making $\mathcal N$ reducing. It is nonzero: choose
a nonzero one-particle vector orthogonal to constants in one fibre,
an occupancy-$(2S-1)$ vector in a second fibre and occupancy-$S$
vectors in all others. The product is killed by $P_{\mathrm{sym}}$
and has total occupancy $1+(2S-1)+(m-2)S=mS$. This includes
$m=2,S=1$. The finite nonempty spectrum of $K|_{\mathcal N}$ excludes
$E$, so $g>0$. On the symmetric subspace $K-EI\succeq0$ by the
full-space definition of $E$, and on its orthogonal complement
$K-EI\succeq gI$. Orthogonal reduction proves the operator inequality
in (15.2) on arbitrary complex superpositions. Its quadratic form and
$\|\phi\|=1$ give the last inequality.

The additional inference is the local singlet-ground exclusion
(15.4)–(15.8) in the original-model replacement, followed by its
neighborhood graph applications below. The spectral quadratic forms,
phase counting, spin comparison, singlet algebra, same-carrier
replacement and finite-spectrum finish are the cited intermediates.
The full-state certificate, flat-mode density estimates, odd-fibre
results, complete multipartite and all-even block-graph results in
§§1–13, and the one-bipartite-neighborhood-component result in §14
retain their original domains. For example $K_2$ satisfies (a) and
(b) but is already covered by the earlier results. Thus these classes
are not assertions that every application adds a new graph domain.
No exact energy, numerical gap or rate follows from the finite-spectrum
argument. The arbitrary connected even-order base problem remains
unresolved here. Other fillings, weights, odd or unequal fibres are
outside (15.2). $\square$

**命题 15.3（The five-rim wheel with arbitrary even rim leaves）。**
Let $h$ be joined to every vertex $v_i$ of a five-cycle
$(v_i)_{i\in\mathbb Z/5\mathbb Z}$. Adjoin $2t$ distinct pendant
vertices, each with its unique neighbor chosen arbitrarily among
the $v_i$, where $t\geq0$ is an integer. Let $H_t$ contain exactly
these cycle, hub and pendant edges. Then $H_t$ satisfies every
conclusion (15.2) for every integer $S\geq1$, on fibres of size
$2S$ and the full half-filled complex carrier. Each $H_t$ fails the
precise hypothesis of Definition 14.1, the block-graph hypothesis of
Corollary 13.3, the complete multipartite hypothesis of Corollary 11.3
and the global flat-least-mode hypothesis of Assumption 3.1.

Proof. This is a connected simple unit-weight graph of even order
$m=6+2t$. The hub neighborhood is exactly $C_5$. At $v_i$ the
induced neighborhood is the path $v_{i-1}$–$h$–$v_{i+1}$ together
with its attached pendant vertices as isolated vertices; it is
bipartite. Every pendant vertex has a singleton neighborhood.
Condition (a) applies, giving (15.2) also at $t=0,S=1$, the
six-vertex wheel with the smallest positive even fibre size.

The hub neighborhood has exactly one component, the nonbipartite
$C_5$. It therefore has no bipartite connected component, disproving
Definition 14.1's exact requirement, not just wholly bipartite
neighborhoods. The six-vertex wheel core is two-connected: deleting
$h$ leaves $C_5$, and deleting a rim vertex leaves $h$ joined to
the remaining rim path. It is a maximal two-connected subgraph of
$H_t$, because a pendant vertex cannot belong to any two-connected
subgraph. It is not a clique, so this graph block contradicts the
block-graph hypothesis. For complete multipartiteness, $v_0$ is
nonadjacent to both $v_2$ and $v_3$, while $v_2,v_3$ are adjacent.
Distinct nonadjacent vertices would have to lie in the same
independent part, which these three relations prohibit.

Let $\lambda_t=\min\operatorname{spec}A(H_t)$ and
$\phi=(1+\sqrt5)/2$. Extend the least Fourier vector of $C_5$ by
zero at the hub and every pendant vertex. Its Rayleigh quotient
is $-\phi$, so $\lambda_t\leq-\phi<-1$. If $t\geq1$ and a
modulus-one vector $z$ satisfied $A(H_t)z=\lambda_tz$, the equation
at any pendant vertex $\ell$ would be
$\lambda_tz_\ell=z_{v_i}$. Taking moduli forces $|\lambda_t|=1$,
a contradiction, regardless of the attachment pattern.

For $t=0$, suppose instead that a global flat least vector existed.
Write $c=z_h\ne0$ and $R=\sum_i z_{v_i}$. The hub equation and
the sum of the rim equations yield

$$
\lambda_0c=R,\qquad \lambda_0R=5c+2R,
\qquad \lambda_0^2-2\lambda_0-5=0.
\tag{15.14}
$$

Since $\lambda_0<0$, this would give $\lambda_0=1-\sqrt6$.
But $(\phi+1)^2=3\phi+2>6$, hence
$-\phi<1-\sqrt6$, contradicting $\lambda_0\leq-\phi$.
Thus the exact complex flat least mode fails even without pendants.
These failures separate this family from the specified earlier
sufficient domains; they are not counterexamples to those theorems
or to confinement on other bases. $\square$

**命题 15.4（Odd-rim wheels at larger even fibres）。**
For every integer $r\geq2$, let $H=K_1\vee C_{2r+1}$ have only
its rim and hub edges. For every integer $S\geq2$, all conclusions
(15.2) hold on its original fibres of size $s=2S\geq4$ and the
full complex $k=(2r+2)S$ carrier. For $r=2$ they also hold at $S=1$
by Proposition 15.3.

Proof. The graph is connected, simple and unit-weight of even order
$2r+2$. Each rim neighborhood is the three-vertex path through the
hub, hence bipartite; the hub neighborhood is $C_{2r+1}$.
Put $q=2r+1$. Its Fourier vectors
$z^{(j)}_i=\exp(2\pi\mathrm i ji/q)$, $0\leq i,j<q$, have
modulus-one coordinates and eigenvalues $2\cos(2\pi j/q)$.
The geometric-sum identity makes distinct such vectors orthogonal,
so they form an eigenbasis. The angles nearest $\pi$ modulo
$2\pi$ are those for $j=r,r+1$; cosine is increasing with distance
from $\pi$ on $[0,\pi]$. Thus these two vectors have the least
eigenvalue $-2\cos(\pi/q)$, and the hub neighborhood has an edge
and the exact flat least mode required in (b). Theorem 15.2 applies.
The case $r=2,S=1$ is precisely the no-pendant case already proved.

For $r\geq3,S=1$ this proof asserts no confinement conclusion:
(15.7) no longer supplies the strict comparison, and the
five-cycle interval (15.8) does not settle these longer rims.
Nor does failure of that comparison refute confinement there.
The longer-odd-rim $s=2$ case and arbitrary connected even-order
bases remain unresolved by these arguments. $\square$

## 追加锚（本行以下为增补区）

## 16. Spin-one confinement for longer odd-rim wheels

**定义 16.1（The original spin-one wheel carrier）。** For every integer
$r\geq3$, put $n=2r+1$, $m=n+1$, and let $H=K_1\vee C_n$ have hub
$h$ and rim $\mathbb Z/n\mathbb Z$, with just the spokes and rim edges.
Use the original equal Boolean fibres $B_i=\{i\}\times[2]$,
$\Omega=\bigsqcup_iB_i$, and the entire complex $m$-particle space
$\mathcal H_m$ of Definitions 1.1–1.2. Thus $s=2$, $|\Omega|=2m$,
$K=K_m$ is positive ordinary token adjacency, and $P_{\mathrm{sym}}$
is the original within-fibre projection. Set

$$
E=\min\operatorname{spec}K,\qquad
\mathcal N=\ker P_{\mathrm{sym}},\qquad
c_n=\cos(\pi/n),\qquad t_n=\frac{49}{50}c_n+\frac7{100}.
\tag{16.1}
$$

The minimum defining $E$ is over all of $\mathcal H_m$.
The sector decomposition (13.4)–(13.5) applies to this carrier
independently of the graph-block hypotheses of Theorem 13.2:

$$
\mathcal H_m\cong\bigoplus_{\boldsymbol J\in\{0,1\}^m}
 \left(\bigotimes_i V_{J_i}\right)_{\sum_i Z_i=0},\qquad
K=\sum_{\{i,j\}\in E(H)}(J_i^+J_j^-+J_i^-J_j^+).
\tag{16.2}
$$

Each original fibre has the unique spin-zero vector
$\chi=(|\{1\}\rangle-|\{2\}\rangle)/\sqrt2$ and the three spin-one
vectors in (13.4). Both multiplicities are one, $n_i=I+Z_i$,
and $P_{\mathrm{sym}}$ selects precisely $\boldsymbol J=(1,\ldots,1)$.
Every sector in (16.2) includes all its globally feasible weights
$|x_i|\leq J_i$, $\sum_i x_i=0$, including the endpoints. No restriction
on complex superpositions or entanglement is imposed.

The representation suppliers in (6.6)–(6.12) specialize as follows:
Srinivasan, [Theorem 1.2 and pp. 3–5](https://arxiv.org/pdf/1001.0280v2),
has Boolean rank $2$, starting rank $1-J_i$ and up operator $L_i^*$;
Feinsilver, [§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
has principal number $2J_i$, $T=L_i^*$ and $T^*=L_i$.
The complete word counts and Gram formulas, with their counting
recurrences, in [OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs)
normalize the triplet with two-letter counts $(2-n_i,n_i)$.
For [the collective-oscillator supplier](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
the exact algebraic map is $d=m$, $N=2$, $g=0$, $e=1$,
$B=A(H)$, $a_i=L_i/\sqrt2$, $H_2=\hbar K/2$;
no low-excitation approximation is used.
The singleton-difference definition in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
gives exactly the coefficient-one moves of (2.4).
These conventions agree with Apte–Parekh–Sud,
[v3, Definition 1 and Fact 2](https://arxiv.org/pdf/2506.03441v3);
the shifted operator $WI/2-K$ in that Fact is a different operator.

**定理 16.2（A full-carrier wheel energy bound）。** For every odd $n\geq7$
with Definition 16.1,

$$
\boxed{\quad E\leq-\frac{4n(n+1)}{2n+1}t_n<-2n.\quad}
\tag{16.3}
$$

Proof. Write $c=c_n$, $\varepsilon=1/10$, and
$u_j=\exp(2\pi\mathrm i rj/n)$ for $j\in\mathbb Z/n\mathbb Z$.
Since $\gcd(r,2r+1)=1$, the $u_j$ run through all $n$th roots of
unity. The vectors $u^k=(u_j^k)_j$, $0\leq k<n$, are orthogonal,
with squared norm $n$: for distinct exponents the inner product is
a geometric sum with ratio a nontrivial $n$th root. Cycle adjacency
$a_C$ satisfies $a_Cu=-2cu$. Also $a_C\preceq2I$, since
$2\operatorname{Re}(\overline{v_j}v_{j+1})\leq|v_j|^2+|v_{j+1}|^2$
for each rim edge and every complex $v$.
Define phases on all base vertices by

$$
w_h=-1,\qquad w_j=\frac{u_j+\varepsilon}{1+\varepsilon u_j}.
\tag{16.4}
$$

The denominators have modulus at least $1-\varepsilon>0$.
The numerator and denominator have the same squared modulus
$1+\varepsilon^2+2\varepsilon\operatorname{Re}u_j$, so $|w_i|=1$
at every vertex. Since $n$ is odd, finite geometric division gives

$$
\begin{aligned}
\frac1{1+\varepsilon u_j}
 &=\frac{\sum_{k=0}^{n-1}(-\varepsilon u_j)^k}{1+\varepsilon^n},\\
w_j&=\mu+A\sum_{k=1}^{n-1}(-\varepsilon)^{k-1}u_j^k,\\
\mu&=\frac{\varepsilon+\varepsilon^{n-1}}{1+\varepsilon^n}
 \geq\varepsilon,\qquad
A=\frac{1-\varepsilon^2}{1+\varepsilon^n}>0.
\end{aligned}
\tag{16.5}
$$

The inequality for $\mu$ follows by subtracting $\varepsilon$:
the numerator of the difference is
$\varepsilon^{n-1}(1-\varepsilon^2)>0$.
Thus the rim vector has the orthogonal decomposition
$w_{\rm rim}=Au+v$, $v\perp u$,
$\|v\|^2=n(1-A^2)$, and $\sum_jw_j=n\mu$.
Self-adjointness and $a_Cu=-2cu$ eliminate its cross terms.
Consequently, with $a_H=A(H)$,

$$
\begin{aligned}
w^*a_Hw
 &=w_{\rm rim}^*a_Cw_{\rm rim}-2n\mu\\
 &\leq-2ncA^2+2n(1-A^2)-2n\mu\\
 &=-2n\bigl((1+c)A^2+\mu-1\bigr).
\end{aligned}
\tag{16.6}
$$

For $n\geq7$, put $\delta=\varepsilon^n<1/100000$. Since $\delta<1$,

$$
(1+\delta)^2\leq1+3\delta
 <1+\frac3{100000}<\frac{9801}{9800},\qquad
A^2=\frac{9801}{10000(1+\delta)^2}>\frac{49}{50}.
\tag{16.7}
$$

Here the last strict rational comparison follows from
$3\cdot9800<100000$. As $c>0$, (16.5)–(16.7) imply

$$
(1+c)A^2+\mu-1
 >\frac{49}{50}c+\frac8{100}>t_n,
\qquad w^*a_Hw\leq-2nt_n.
\tag{16.8}
$$

Lift these phases to a vector on the original carrier, not to a
minimum in an auxiliary spin space. For each $m$-subset $T\subseteq\Omega$ set

$$
\Phi(T)=\binom{2m}{m}^{-1/2}\prod_{(i,a)\in T}w_i.
\tag{16.9}
$$

Its norm is one because every product has modulus one. It is
within-fibre invariant and has exactly $m$ particles. For an ordered
pair of distinct coordinates $x\in B_i$, $y\in B_j$, exactly
$\binom{2m-2}{m-1}$ such subsets contain $x$ and omit $y$.
The phase product in the corresponding adjacency quadratic form is
$\overline{w_i}w_j$. There are four coordinate pairs for every
ordered base edge. Hence, counting both orientations just as in (2.4),

$$
\begin{aligned}
\langle\Phi,K\Phi\rangle
 &=4\frac{\binom{2m-2}{m-1}}{\binom{2m}{m}}w^*a_Hw
 =\frac{2m}{2m-1}w^*a_Hw\\
 &\leq-\frac{4nm}{2m-1}t_n.
\end{aligned}
\tag{16.10}
$$

The ratio is $m^2/((2m)(2m-1))$, by factorial cancellation.
The full-space Rayleigh principle proves the first inequality in
(16.3). For complex vectors it is the same principle: if $K$ is
real symmetric and $z=x+\mathrm i y$, then
$z^*Kz=x^{\mathsf T}Kx+y^{\mathsf T}Ky$ and
$z^*z=\|x\|^2+\|y\|^2$.

The subset count, normalization and real/complex comparison are the
intermediates (3.5)–(3.7), supplied in full by
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs):
`Test.move`, `Test.toNbr_bij`, `Test.token_energy`, `counting_identity`,
`card_move_family`, `W_move` and the proof-local norm and Rayleigh
identities. Their parameters here are $N=2m$, $k=m$, block size $2$,
and coordinate phase $w_i$; no pentagon energy or cut estimate is used.
The phase-subset method also has the classical fixed-magnetization
precedent Bärwinkel–Schmidt–Schnack,
[§§2.2–2.3, (14)–(21)](https://arxiv.org/pdf/cond-mat/0210458v2),
whose cyclic hypotheses are not assumed for the wheel.
The wheel-specific inference is (16.4)–(16.8), followed by the
unchanged full-carrier count.

For the strict endpoint comparison, $\cos x\geq1-x^2/2$ follows by
integrating $\sin x\leq x$ on $x\geq0$. One elementary exact bound
$\pi^2<10$ follows from

$$
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi,
\qquad \left(\frac{22}{7}\right)^2<10.
\tag{16.11}
$$

For the integral identity divide its integrand to obtain
$x^6-4x^5+5x^4-4x^2+4-4/(1+x^2)$ and integrate each term.
It follows that

$$
\begin{aligned}
t_n&>\frac{21}{20}-\frac{49}{10n^2},\\
\frac{21}{20}-\frac{49}{10n^2}
 -\left(1-\frac1{2n+2}\right)
 &=\frac{n^3+11n^2-98n-98}{20n^2(n+1)}>0.
\end{aligned}
\tag{16.12}
$$

Indeed for $v=n-7\geq0$ the numerator is
$v^3+32v^2+203v+98>0$. Therefore
$t_n>(2n+1)/(2n+2)$, which proves the second inequality in (16.3)
with $m=n+1$, including $n=7$. $\square$

**定理 16.3（Every ground vector on the original wheel carrier）。**
For every graph and carrier of Definition 16.1, every $E$-ground
vector lies in $\operatorname{ran}P_{\mathrm{sym}}$.
The actual $\mathcal N$ is nonzero and reducing, and for

$$
g=\min\operatorname{spec}(K|_{\mathcal N})-E
\tag{16.13}
$$

one has $g>0$ and, on the whole original complex carrier,

$$
K-EI\succeq g(I-P_{\mathrm{sym}}),\qquad
\|(I-P_{\mathrm{sym}})\phi\|^2
 \leq\frac{\langle\phi,K\phi\rangle-E}{g}
 \quad(\|\phi\|=1).
\tag{16.14}
$$

Proof. First record the required singlet estimate on the spin-one
rim, as a classical coupling intermediate. Write
$\boldsymbol J_i=(X_i,Y_i,Z_i)$ and
$H_{\rm iso}=\sum_{j\in\mathbb Z/n\mathbb Z}
 \boldsymbol J_j\cdot\boldsymbol J_{j+1}$.
For fixed $j$, the two distinct neighbors carry total spin
$q=0,1,2$, since $V_1\otimes V_1=V_0\oplus V_1\oplus V_2$.
Coupling this spin to the central spin one gives total spins
$l=|q-1|,\ldots,q+1$. These decompositions can be read directly
from weight multiplicities: subtract successively the character
of the largest remaining spin, whose weights are all integers
from its negative to its positive value. Orthogonal invariant
complements give all copies, so none are discarded.
Equivalently these are the triangle and orthogonality rules for
Clebsch–Gordan coupling, [DLMF §§34.1–34.3](https://dlmf.nist.gov/34.1),
as used in (10.8).
The Casimir of a spin-$q$ representation is $q(q+1)I$.
Thus on the complete three-site space the eigenvalues of

$$
h_j=\boldsymbol J_j\cdot(\boldsymbol J_{j-1}+\boldsymbol J_{j+1})
\quad\hbox{are}\quad
\frac{l(l+1)-2-q(q+1)}2.
\tag{16.15}
$$

Their minima for $q=0,1,2$ are respectively $0,-2,-3$.
Therefore $h_j\succeq-3I$, also with arbitrary spectator factors,
and $\sum_jh_j=2H_{\rm iso}$ gives
$H_{\rm iso}\succeq-3nI/2$.
If $f$ is a unit total singlet on the rim, simultaneous rotations
make its three Cartesian edge-sum expectations equal. Since
$K_{C_n}=2\sum_j(X_jX_{j+1}+Y_jY_{j+1})$, this proves

$$
\langle f,K_{C_n}f\rangle
 =\frac43\langle f,H_{\rm iso}f\rangle\geq-2n.
\tag{16.16}
$$

The estimate is on every singlet, not an independently optimized
choice of rim state.

Suppose some sector of (16.2) with a zero spin had minimum $E$.
Choose a zero-spin site $p$. At any other zero-spin site, replace
its one-dimensional factor $\chi$ in a unit sector ground vector
by $|1,0\rangle$. Both factors have weight zero and all three spin
expectations zero. Since there is no intrafibre interaction, the
replacement preserves the energy expectation and total weight.
The new sector minimum is at most $E$ by this trial and at least
$E$ by the definition of the whole-space minimum. Choose a ground
vector in it and repeat at every other zero-spin site.
This is the $j=0$ endpoint of the nonstrict comparison (7.4)–(7.5).
Its original bilinear-spin formulation is Ghassemi
Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412),
with maximal spin $s_i=1$, variable spin $t_i=J_i\in\{0,1\}$,
$M=0$, and $D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$.
Only nonstrict existence is used, with its endpoint trial explicitly
verified here. The spin-one pair realization is also the one in
Benassi–Lees–Ueltschi,
[§§4.1–4.3, Lemma 9](https://arxiv.org/pdf/1510.03215v3);
their nonnegative ferromagnetic product-coupling hypotheses do not
supply strictness for the positive adjacency used here.

We now have a unit actual ground vector $\Psi=\chi_p\otimes f$,
with spin one at every site other than $p$, and
$K_{H-p}f=Ef$. Put $A=N_H(p)$, $R=V(H)\setminus(\{p\}\cup A)$,
and $B^\pm=\sum_{i\in A}J_i^\pm$. Release the factor at $p$ by
$\Theta=|1,0\rangle_p\otimes f$. Its Rayleigh quotient is $E$ by
the same zero-expectation calculation. Since $K-EI\succeq0$ on
the full carrier, equality implies $(K-EI)\Theta=0$. Subtracting
the equation for $f$ gives

$$
0=\sqrt2\,|1,1\rangle_p\otimes B^-f
  +\sqrt2\,|1,-1\rangle_p\otimes B^+f.
\tag{16.17}
$$

The two displayed weight factors are orthogonal, so $B^-f=B^+f=0$.
The commutator $[B^+,B^-]=2Z_A$ also gives $Z_Af=0$.
Consequently $f$ lies in the total-singlet space on $A$, tensored
with the zero-weight space on $R$. Indeed on each total-spin
chain, the two ladder operators have no common kernel unless
that spin is zero. This statement includes all multiplicities and
arbitrary entanglement between $A$ and $R$.

If $p=h$, then $A$ is the entire rim and $R$ is empty.
Equation (16.16) gives $E=\langle f,K_{C_n}f\rangle\geq-2n$,
contradicting (16.3).

If $p$ is a rim vertex, its two rim neighbors are distinct and
nonadjacent for $n\geq7$. The induced graph on $A$ is the
three-vertex path through the hub. The complete bipartite singlet
obstruction (7.6)–(7.10), also used in §§14–15, supplies a unit
zero-weight ground vector $u_A$ of this induced spin-one adjacency
$K_A$, with minimum $e_A$, which is not killed by both $B^\pm$.
Its hypotheses are precisely a nonempty bipartite graph, positive
unit edge coefficients, integer spin $S=1$, and minimum on the
entire zero-weight space. No property of $H[R]$ is required.

Use the reduced density $\rho_R$ of this same $f$ on $R$.
It is supported on $Z_R=0$. A one-site vector spin, sandwiched
between total-singlet projections on $A$, is zero: conjugation
by simultaneous rotations fixes those projections and rotates
that vector, whose only rotation-invariant vector is zero.
Thus all crossing-edge expectations in $f$ vanish, and

$$
E=\langle f,K_Af\rangle+\operatorname{tr}(\rho_RK_R),\qquad
\langle f,K_Af\rangle\geq e_A.
\tag{16.18}
$$

The density
$|\chi_p\rangle\langle\chi_p|\otimes
 |u_A\rangle\langle u_A|\otimes\rho_R$
is on the original globally half-filled carrier. Its edges at $p$
vanish, and its $A$–$R$ edge expectations vanish because $u_A$
has definite weight zero and hence
$\langle u_A,J_i^\pm u_A\rangle=0$. Its energy is therefore
$e_A+\operatorname{tr}(\rho_RK_R)\leq E$; the full-space variational
principle forces equality. Diagonalize this same $\rho_R$ into
unit vectors $h_b$ of weight zero with positive weights. Every
$\chi_p\otimes u_A\otimes h_b$ has energy at least $E$, and their
weighted average is $E$. Each is consequently an actual ground
vector. Release its pair at $p$ once more. Equation (16.17), now
with $f=u_A\otimes h_b$, forces $B^-u_A=B^+u_A=0$, a contradiction.
This is the same-state replacement of (15.10)–(15.13), with the
retained marginal displayed in (16.18); no separate attainability
of local optima is being assumed.

Both possibilities for $p$ are excluded. Every summand in (16.2)
with a zero spin therefore has minimum strictly greater than $E$.
The decomposition is finite, orthogonal and reducing, so every
complex $E$-ground vector, including superpositions of sectors,
belongs to its all-spin-one summand. This proves the confinement.
The vector $\chi_h\otimes\bigotimes_{i\ne h}|1,0\rangle_i$ is a
nonzero vector in $\mathcal N$ with exactly $m$ particles.
Fibre permutations commute with $K$, so $\mathcal N$ reduces $K$.
Its finite nonempty spectrum excludes $E$ by confinement; hence
$g$ in (16.13) is positive. On $\operatorname{ran}P_{\mathrm{sym}}$,
$K-EI\succeq0$; on $\mathcal N$, $K-EI\succeq gI$.
Adding these reducing quadratic forms proves (16.14), and taking
a unit-vector expectation proves its mass bound. $\square$

The supplied five-rim conclusion at every even fibre size and the
longer odd-rim conclusion at $s\geq4$ are Proposition 15.3 and
Proposition 15.4. The additional graph-domain endpoint in
Theorems 16.2–16.3 is exactly $K_1\vee C_n$, odd $n\geq7$, $s=2$,
with the symbolic full-space energy bound (16.3).
Their combination uses the classical three-site coupling lower
bound only through its singlet consequence (16.16), the supplied
sector and local replacement arguments, and the wheel phase
estimate (16.4)–(16.8). It gives no exact value of $E$, quantitative
lower bound for $g$, other filling, changed sign, weighted or
unequal or odd fibres, or physical realization. Arbitrary connected
even-order bases remain outside these conclusions.

## 追加锚（本行以下为增补区）
