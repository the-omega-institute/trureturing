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
