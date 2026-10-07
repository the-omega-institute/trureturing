# Replica spectrum of Gaussian multi-entropy as weighted spanning forests

This volume is reference input. Lean declarations and their checked proof terms carry the mathematical truth; nothing in this volume is kernel-verified. The atomizer is `generic-v1`. Existing text is append-only; corrections and additions belong after the final append anchor.

## 1. Scope

The replica partition functions of the fully symmetric pure Gaussian states of Camargo and Nishida reduce to a replica-level determinant built from a weighted average $Q$ of twist permutations. This volume computes that determinant exactly. The Gram defect $I-Q^\top Q$ is the Laplacian of a weighted Schreier multigraph on the replicas, so the determinant is a spanning-forest polynomial; for the cyclic twists of the multi-entropy its spectrum is given by characters. Consequences: a closed form of the residual constant $D_R(0)$ of every bipartite term, a factorization of the $\mathtt q$-party determinant into its bipartite subdeterminants and a remainder, an exact replica-order-two identity for every $\mathtt q$, an exact finite-squeezing formula for the tripartite genuine multi-entropy for all $n$ and all party sizes, and the closed form of its large-squeezing constant.

## 2. Notation and conventions

**Convention 2.1 (Matrices and weights).** All matrices are real or complex square matrices indexed by a finite set. For a permutation $g$ of a finite set $R$, $M_g$ is the matrix with entries $(M_g)_{r,s}=1$ if $r=g(s)$ and $0$ otherwise. For $u\in R$, $\mathbf 1_u$ is the indicator column vector of $u$. A weight vector is $x=(x_1,\dots,x_{\mathtt q})$ with $\mathtt q\ge2$, every $x_k>0$ and $\sum_k x_k=1$.

**Convention 2.2 (Multigraphs).** A weighted multigraph $\Gamma$ on a finite vertex set $V$ is a finite edge set $E$, an endpoint map sending each $e\in E$ to an unordered pair $\{u_e,v_e\}$ of vertices (with $u_e=v_e$ allowed, a loop), and weights $w_e>0$. Parallel edges are distinct edges. Its Laplacian is $L_\Gamma=\sum_{e\in E}w_e\,b_eb_e^\top$ with $b_e=\mathbf 1_{u_e}-\mathbf 1_{v_e}$; loops contribute $0$. A spanning forest is a subset $F\subseteq E$ without cycles (in particular without loops) and $w(F)=\prod_{e\in F}w_e$. A rooted spanning forest is a pair $(F,\rho)$ of a spanning forest and a set $\rho\subseteq V$ containing exactly one vertex of each tree of $F$ (isolated vertices are trees). If $(F,\rho)$ is rooted then $|F|=|V|-|\rho|$. The tree weight is $\kappa(\Gamma)=\sum_{F}w(F)$ over spanning forests with one tree.

**Convention 2.3 (Characters).** For a finite abelian group $A$, $\widehat A$ is its group of characters $\chi:A\to\mathbb C^\times$. For $A=\mathbb Z_n^d$ and $j\in\mathbb Z_n^d$ write $\chi_j(r)=\omega^{\langle j,r\rangle}$ with $\omega=e^{2\pi i/n}$ and $\langle j,r\rangle=\sum_i j_ir_i$.

**Convention 2.4 (Twists of the multi-entropy).** The $\mathtt q$-party replica set of order $n$ is $A_{n,\mathtt q}=\mathbb Z_n^{\mathtt q-1}$, of size $n^{\mathtt q-1}$. Party $k\le\mathtt q-1$ has twist $r\mapsto r+e_k$ ($e_k$ the $k$-th unit vector) and party $\mathtt q$ has the identity twist; write $t_k=e_k$ for $k<\mathtt q$ and $t_{\mathtt q}=0$. For $\mathtt q=3$ this is the convention $g_A,g_B,g_C$ of Camargo and Nishida, §2.1; for $\mathtt q=2$ it is the cyclic twist of the Rényi entropy. For $j\in\mathbb Z_n^{\mathtt q-1}$ put $j_{\mathtt q}=0$; then $\langle j,t_k-t_l\rangle=j_k-j_l$.

**Convention 2.5 (Bipartitions).** A bipartition of the parties $\{1,\dots,\mathtt q\}$ is an unordered pair $\{S,S^c\}$ of nonempty complementary sets; it is labelled by the side $S$ not containing $\mathtt q$, so the bipartitions correspond to the $2^{\mathtt q-1}-1$ nonempty subsets $S\subseteq\{1,\dots,\mathtt q-1\}$. Its weight is $p_S=\sum_{k\in S}x_k$.

## 3. Replica determinant and the Schreier multigraph

**Definition 3.1 (Replica datum and replica determinant).** A replica datum is a finite nonempty set $R$ with $m=|R|$, permutations $g_1,\dots,g_{\mathtt q}$ of $R$ and a weight vector $x$. Its twist average is $Q=\sum_kx_kM_{g_k}$, its Gram matrix is $G=Q^\top Q$, and its replica determinant is, for real $\varepsilon$,

$$
\Delta(\varepsilon)=\det\Big(\tfrac{(1+\varepsilon)^2}{4}I-\tfrac{(1-\varepsilon)^2}{4}G\Big).
$$

Write $c(\varepsilon)=(1-\varepsilon)^2/4$. Stance: definition.

**Definition 3.2 (Schreier multigraph of a replica datum).** The Schreier multigraph $\Gamma$ of a replica datum has vertex set $R$, edge set $R\times\{(k,l):1\le k<l\le\mathtt q\}$, the edge $(r,k,l)$ joining $r$ and $g_l^{-1}g_k(r)$, with weight $x_kx_l$. Stance: definition.

**Theorem 3.3 (Gram defect is a Laplacian).** For every replica datum, $I-Q^\top Q=L_\Gamma$. Stance: suspected-novel (see §9).

**Proof.** For permutations $g,h$ of $R$, $(M_g^\top M_h)_{r,s}=\sum_u[u=g(r)][u=h(s)]=[s=h^{-1}g(r)]$, so $M_g^\top M_h=M_{h^{-1}g}^\top$ and $M_h^\top M_g=M_{h^{-1}g}$. Hence

$$
Q^\top Q=\sum_kx_k^2I+\sum_{k<l}x_kx_l\big(M_{\pi_{kl}}^\top+M_{\pi_{kl}}\big),\qquad \pi_{kl}=g_l^{-1}g_k .
$$

Since $1=(\sum_kx_k)^2=\sum_kx_k^2+2\sum_{k<l}x_kx_l$,

$$
I-Q^\top Q=\sum_{k<l}x_kx_l\big(2I-M_{\pi_{kl}}-M_{\pi_{kl}}^\top\big).
$$

For fixed $k<l$ and $\pi=\pi_{kl}$, the edges $(r,k,l)$, $r\in R$, contribute

$$
\sum_r(\mathbf 1_r-\mathbf 1_{\pi r})(\mathbf 1_r-\mathbf 1_{\pi r})^\top=2I-\sum_r\mathbf 1_r\mathbf 1_{\pi r}^\top-\sum_r\mathbf 1_{\pi r}\mathbf 1_r^\top ,
$$

because $r\mapsto\pi r$ is a bijection. The $(r,s)$ entry of $\sum_r\mathbf 1_r\mathbf 1_{\pi r}^\top$ is $[s=\pi r]=(M_\pi^\top)_{r,s}$, and the last sum is its transpose. Multiplying by $x_kx_l$ and summing over $k<l$ gives $L_\Gamma$. The identity is algebraic, so loops ($\pi r=r$) need no separate treatment: both sides have a zero contribution there. ∎

**Theorem 3.4 (Forest expansion of the replica determinant).** For every replica datum and every real $\varepsilon$,

$$
\Delta(\varepsilon)=\det\big(\varepsilon I+c(\varepsilon)L_\Gamma\big)=\sum_{(F,\rho)}\varepsilon^{|\rho|}\,c(\varepsilon)^{m-|\rho|}\,w(F),
$$

the sum running over the rooted spanning forests of $\Gamma$. Stance: suspected-novel for the first equality and its application; the second equality applies the literature-attested all-minors matrix-tree theorem (§9).

**Proof.** Since $\tfrac{(1+\varepsilon)^2}{4}-\tfrac{(1-\varepsilon)^2}{4}=\varepsilon$, Theorem 3.3 gives $\tfrac{(1+\varepsilon)^2}{4}I-c(\varepsilon)G=\varepsilon I+c(\varepsilon)(I-G)=\varepsilon I+c(\varepsilon)L_\Gamma$. For any square matrix $B$ indexed by $V$ and scalar $s$, multilinearity of the determinant in the columns gives $\det(sI+B)=\sum_{U\subseteq V}s^{|U|}\det B[V\setminus U]$, where $B[W]$ is the principal submatrix on $W$ and $\det B[\varnothing]=1$. Apply this with $B=cL_\Gamma$: $\det(cL_\Gamma)[V\setminus U]=c^{|V\setminus U|}\det L_\Gamma[V\setminus U]$. By the all-minors matrix-tree theorem (cited step, §9), $\det L_\Gamma[V\setminus U]$ is the sum of $w(F)$ over the spanning forests $F$ of $\Gamma$ each of whose trees contains exactly one vertex of $U$; for $U=\varnothing$ and $V\ne\varnothing$ the sum is empty and $\det L_\Gamma=0$, consistent with $L_\Gamma\mathbf 1=0$. Pairs $(F,U)$ of this kind are exactly the rooted spanning forests with $\rho=U$, and then $|V\setminus U|=m-|\rho|$. ∎

**Corollary 3.5 (Order of vanishing and residual constant).** Let $\Gamma$ have $\gamma$ connected components $C_1,\dots,C_\gamma$. Then $\Delta(\varepsilon)=\varepsilon^\gamma D(\varepsilon)$ for the polynomial

$$
D(\varepsilon)=\sum_{(F,\rho)}\varepsilon^{|\rho|-\gamma}c(\varepsilon)^{m-|\rho|}w(F),\qquad D(0)=4^{-(m-\gamma)}\prod_{i=1}^{\gamma}|C_i|\,\kappa(C_i)>0 .
$$

Moreover $\Delta(\varepsilon)>0$ for $0<\varepsilon\le1$ and $D(\varepsilon)>0$ for $0\le\varepsilon\le1$. In particular, if $\Gamma$ is connected, then $\Delta(\varepsilon)=\varepsilon D(\varepsilon)$ and $D(0)=m\,\kappa(\Gamma)/4^{m-1}$. Stance: suspected-novel.

**Proof.** Every rooted spanning forest has at least $\gamma$ trees, so $|\rho|\ge\gamma$ and $D$ is a polynomial. At $\varepsilon=0$ only the forests with exactly $\gamma$ trees survive; such a forest restricts to a spanning tree of each component, the choices are independent, and each tree $T_i$ of $C_i$ has $|C_i|$ choices of root, so the surviving sum is $\prod_i|C_i|\kappa(C_i)$, multiplied by $c(0)^{m-\gamma}=4^{-(m-\gamma)}$. Every component is connected, so $\kappa(C_i)>0$. For $0\le\varepsilon\le1$ all terms are nonnegative, and the term of the forests with $\gamma$ trees is positive at $\varepsilon<1$; at $\varepsilon=1$ the term $F=\varnothing$, $\rho=V$ contributes $1$. So $D>0$ on $[0,1]$ and $\Delta=\varepsilon^\gamma D>0$ on $(0,1]$. ∎

**Corollary 3.6 (Connectivity criterion).** $\Gamma$ is connected if and only if the group generated by $\{g_l^{-1}g_k:k<l\}$ acts transitively on $R$. If some $g_{k_0}$ is the identity, this holds if and only if the group generated by all $g_k$ acts transitively. Stance: repo-derived.

**Proof.** The edges at a vertex $r$ join it to $\pi_{kl}(r)$, so the components are the orbits of the group generated by the $\pi_{kl}$. If $g_{k_0}=\mathrm{id}$, then $\pi_{kk_0}=g_k$ or $\pi_{k_0k}=g_k^{-1}$, so this group contains every $g_k$; conversely it is contained in the group generated by the $g_k$. ∎

**Remark 3.7 (Simple zero).** For twists containing the identity and acting transitively, Corollaries 3.5 and 3.6 give the simple-zero statement $\Delta(\varepsilon)=\varepsilon D(\varepsilon)$, $D(0)>0$. Beyond this, Corollary 3.5 identifies $D$ as a forest polynomial, computes $D(0)$ as a tree count, and gives the exact order of vanishing $\gamma$ without any transitivity hypothesis. Stance: the simple-zero statement is repo-derived; the forest and tree-count form is suspected-novel.

**Theorem 3.8 (Gaussian replica integral).** Let $N_1,\dots,N_{\mathtt q}\ge1$, $N=\sum_kN_k$ and $x_k=N_k/N$. Split $\{1,\dots,N\}$ into consecutive blocks $B_1,\dots,B_{\mathtt q}$ with $|B_k|=N_k$ and let $P_k$ be the diagonal projection of $\mathbb R^N$ onto the coordinates in $B_k$. Let $u=N^{-1/2}(1,\dots,1)^\top$, $\lambda>0$, $\varepsilon>0$ and
$$
W=\lambda\big(I-(1-\varepsilon)uu^\top\big),\qquad \psi(y)=\exp\big(-\tfrac12y^\top Wy\big)\quad(y\in\mathbb R^N).
$$
For a replica datum $(R,g_1,\dots,g_{\mathtt q},x)$ with this weight vector and $X=(y_r)_{r\in R}\in(\mathbb R^N)^R$ put $y'_r=\sum_kP_ky_{g_k(r)}$ and
$$
\mathcal Z(R,g)=\frac{\int_{(\mathbb R^N)^R}\prod_{r\in R}\psi(y_r)\,\psi(y'_r)\,dX}{\Big(\int_{\mathbb R^N}\psi(y)^2\,dy\Big)^{|R|}} .
$$
Then $\mathcal Z(R,g)=\big(\varepsilon^{|R|}/\Delta(\varepsilon)\big)^{1/2}$, with $\Delta$ the replica determinant of the datum. This holds for every $N\ge2$, including $N_1=N_2=1$. Stance: repo-derived; it uses the literature-attested determinant identities of Sylvester and Schur (§9).

**Proof.** Write $m=|R|$ and $M_k=M_{g_k}$. Let $T=\sum_kM_k^\top\otimes P_k$ act on $\mathbb R^R\otimes\mathbb R^N$; since $(M_k^\top)_{r,s}=[s=g_k(r)]$, $(TX)_r=y'_r$. From $M_kM_l^\top\otimes P_kP_l=\delta_{kl}\,I\otimes P_k$ and $\sum_kP_k=I$ we get $T^\top T=I$. The exponent of the numerator is $-\tfrac12X^\top\mathcal AX$ with $\mathcal A=I\otimes W+T^\top(I\otimes W)T$, which is positive definite because $W$ is ($W$ has eigenvalues $\lambda$ and $\lambda\varepsilon$). The Gaussian integral $\int_{\mathbb R^d}e^{-\frac12z^\top Bz}dz=(2\pi)^{d/2}(\det B)^{-1/2}$ for positive definite $B$ (write $B=O^\top\mathrm{diag}(\beta_i)O$ with $O$ orthogonal and $\beta_i>0$; the substitution $z=O^\top w$ reduces it to $\prod_i\int_{\mathbb R}e^{-\beta_iw_i^2/2}dw_i=\prod_i(2\pi/\beta_i)^{1/2}$), applied to $\mathcal A$ and to $2W$, gives
$$
\mathcal Z(R,g)=\Big(\frac{\det(2W)^m}{\det\mathcal A}\Big)^{1/2}.
$$
Let $u_k=N_k^{-1/2}\mathbf 1_{B_k}$, $V_0=\mathrm{span}\{u_1,\dots,u_{\mathtt q}\}$ and $V_1=V_0^\perp$, the vectors with zero sum on every block. Then $P_ku_l=\delta_{kl}u_l$, $P_kV_1\subseteq V_1$, and $u=\sum_k\sqrt{x_k}\,u_k\in V_0$, so $W$, $T$ and $\mathcal A$ preserve $\mathbb R^R\otimes V_0$ and $\mathbb R^R\otimes V_1$, and both determinants factor over the two summands. On $V_1$, $W=\lambda I$ and $\mathcal A=\lambda(I+T^\top T)=2\lambda I$, so the $V_1$ factors of $\det(2W)^m$ and $\det\mathcal A$ coincide (both are $1$ when $V_1=0$). In the orthonormal basis $u_1,\dots,u_{\mathtt q}$ of $V_0$, $P_k$ becomes the matrix unit $E_{kk}$ and $W$ becomes $\lambda(I_{\mathtt q}-(1-\varepsilon)vv^\top)$ with the unit vector $v=(\sqrt{x_1},\dots,\sqrt{x_{\mathtt q}})^\top$; hence the $V_0$ factor of $\det(2W)^m$ is $(2\lambda)^{\mathtt qm}\varepsilon^m$. Let $Y=I_R\otimes v$, a $\mathtt qm\times m$ matrix with $Y^\top Y=I_m$, let $T_0=\sum_kM_k^\top\otimes E_{kk}$ and $U=[\,Y\ \ T_0^\top Y\,]$. Then the restriction of $\mathcal A$ is
$$
\mathcal A_0=\lambda\big(2I-(1-\varepsilon)(YY^\top+T_0^\top YY^\top T_0)\big)=\lambda\big(2I-(1-\varepsilon)UU^\top\big).
$$
Since $Y^\top T_0^\top Y=\sum_kM_k\,(v^\top E_{kk}v)=\sum_kx_kM_k=Q$, we have $U^\top U=\begin{pmatrix}I&Q\\Q^\top&I\end{pmatrix}$. With $h=(1-\varepsilon)/2$, Sylvester's identity $\det(I-hUU^\top)=\det(I-hU^\top U)$ and the Schur complement for the invertible scalar block $(1-h)I$ give
$$
\det\mathcal A_0=(2\lambda)^{\mathtt qm}\det\begin{pmatrix}(1-h)I&-hQ\\-hQ^\top&(1-h)I\end{pmatrix}=(2\lambda)^{\mathtt qm}\det\big((1-h)^2I-h^2Q^\top Q\big)=(2\lambda)^{\mathtt qm}\Delta(\varepsilon),
$$
because $1-h=(1+\varepsilon)/2$. Dividing, $\det(2W)^m/\det\mathcal A=\varepsilon^m/\Delta(\varepsilon)$. ∎

## 4. Abelian twists and the character spectrum

**Theorem 4.1 (Character spectrum).** Let $R=A$ be a finite abelian group and $g_k(r)=r+t_k$ for $t_1,\dots,t_{\mathtt q}\in A$. For $\chi\in\widehat A$ put

$$
\lambda_\chi=\sum_kx_k\chi(t_k),\qquad \mu_\chi=\sum_{k<l}x_kx_l\,|\chi(t_k)-\chi(t_l)|^2 .
$$

Then $\mu_\chi=1-|\lambda_\chi|^2$, the eigenvalues of $L_\Gamma$ are the $\mu_\chi$, those of $Q^\top Q$ are the $|\lambda_\chi|^2$, and

$$
\Delta(\varepsilon)=\prod_{\chi\in\widehat A}\big(\varepsilon+c(\varepsilon)\mu_\chi\big).
$$

Moreover $\mu_\chi=0$ exactly when $\chi$ is trivial on the difference subgroup $A_0=\langle t_k-t_l\rangle$, and $\gamma=[A:A_0]$. Stance: suspected-novel as a statement about replica determinants; it uses the literature-attested fact that the characters of a finite abelian group form a basis of $\mathbb C^A$ (§9).

**Proof.** Here $\pi_{kl}(r)=r+d_{kl}$ with $d_{kl}=t_k-t_l$. For a character $\chi$, $(M_\pi^\top\chi)(r)=\sum_s[s=r+d]\chi(s)=\chi(d)\chi(r)$ and $(M_\pi\chi)(r)=\chi(r-d)=\overline{\chi(d)}\chi(r)$. By the second display in the proof of Theorem 3.3, $L_\Gamma\chi=\sum_{k<l}x_kx_l(2-\chi(d_{kl})-\overline{\chi(d_{kl})})\chi$, and $2-z-\bar z=|1-z|^2$ for $|z|=1$, while $|1-\chi(t_k-t_l)|=|\chi(t_l)-\chi(t_k)|$. So $L_\Gamma\chi=\mu_\chi\chi$. The characters form a basis, so $\varepsilon I+cL_\Gamma$ is diagonalized by them and Theorem 3.4 gives the product. For unit complex numbers $z_k$ and $\sum x_k=1$,

$$
1-\Big|\sum_kx_kz_k\Big|^2=\sum_{k,l}x_kx_l\big(1-\mathrm{Re}\,z_k\bar z_l\big)=\tfrac12\sum_{k,l}x_kx_l|z_k-z_l|^2=\sum_{k<l}x_kx_l|z_k-z_l|^2 ,
$$

which with $z_k=\chi(t_k)$ gives $\mu_\chi=1-|\lambda_\chi|^2$ and hence the spectrum of $Q^\top Q=I-L_\Gamma$. Since all $x_kx_l>0$, $\mu_\chi=0$ iff $\chi(t_k)=\chi(t_l)$ for all $k,l$, iff $\chi$ is trivial on $A_0$. The number of such characters is $|\widehat{A/A_0}|=[A:A_0]$, which equals $\dim\ker L_\Gamma$; since all weights are positive, $\ker L_\Gamma$ consists of the functions constant on components (from $v^\top L_\Gamma v=\sum_ew_e(v_{u_e}-v_{v_e})^2$), so this is the number of components. ∎

**Corollary 4.2 (Twisted sine products).** For $A=\mathbb Z_n^d$,

$$
\Delta(\varepsilon)=\prod_{j\in\mathbb Z_n^d}\Big(\varepsilon+(1-\varepsilon)^2\sum_{k<l}x_kx_l\sin^2\frac{\pi\langle j,t_k-t_l\rangle}{n}\Big).
$$

If $\Gamma$ is connected, then $n^d\kappa(\Gamma)=\prod_{\chi\ne1}\mu_\chi$ and $D(0)=\prod_{\chi\ne1}(\mu_\chi/4)$. Stance: the sine product is suspected-novel as a replica-determinant formula; the identity $n^d\kappa(\Gamma)=\prod_{\chi\ne1}\mu_\chi$ for Cayley graphs of abelian groups is literature-attested (§9) and also follows by comparing Corollary 3.5 with Theorem 4.1 at $\varepsilon\to0$.

**Proof.** $|\chi_j(t_k)-\chi_j(t_l)|^2=|1-\omega^{\langle j,t_l-t_k\rangle}|^2=4\sin^2(\pi\langle j,t_k-t_l\rangle/n)$ and $c(\varepsilon)\cdot4=(1-\varepsilon)^2$. Dividing Theorem 4.1 by $\varepsilon$ (the factor of the trivial character) and letting $\varepsilon\to0$ gives $D(0)=\prod_{\chi\ne1}c(0)\mu_\chi=\prod_{\chi\ne1}(\mu_\chi/4)$; comparison with $D(0)=n^d\kappa(\Gamma)/4^{n^d-1}$ from Corollary 3.5 gives the tree identity. ∎

## 5. The multi-entropy twists

Throughout this section the datum is that of Convention 2.4: $R=\mathbb Z_n^{\mathtt q-1}$, $t_k=e_k$ ($k<\mathtt q$), $t_{\mathtt q}=0$, weights $x$. Write $\Delta_{\mathtt q}$, $D_{\mathtt q}$, $\Gamma_{\mathtt q}$ for its replica determinant, residual polynomial and Schreier multigraph, and for $j\in\mathbb Z_n^{\mathtt q-1}$ (with $j_{\mathtt q}=0$)

$$
\nu_j=\sum_{k<l}x_kx_l\sin^2\frac{\pi(j_k-j_l)}{n}.
$$

**Proposition 5.1 (Multi-entropy replica determinant).** $\Delta_{\mathtt q}(\varepsilon)=\prod_{j\in\mathbb Z_n^{\mathtt q-1}}(\varepsilon+(1-\varepsilon)^2\nu_j)$. The multigraph $\Gamma_{\mathtt q}$ is the Cayley multigraph of $\mathbb Z_n^{\mathtt q-1}$ with generators $e_k-e_l$ ($e_{\mathtt q}=0$) of weight $x_kx_l$; it is connected, so $\Delta_{\mathtt q}=\varepsilon D_{\mathtt q}$ with $D_{\mathtt q}(0)=n^{\mathtt q-1}\kappa(\Gamma_{\mathtt q})/4^{n^{\mathtt q-1}-1}=\prod_{j\ne0}\nu_j$. For $\mathtt q=2$, $\Gamma_2$ is the $n$-cycle with every edge of weight $x_1x_2$ (two parallel edges when $n=2$, a loop when $n=1$). For $\mathtt q=3$, $\Gamma_3$ is the triangular lattice on the $n\times n$ torus, with weight $x_1x_3$ on the edges in direction $e_1$, $x_2x_3$ in direction $e_2$ and $x_1x_2$ in direction $e_1-e_2$. Stance: suspected-novel.

**Proof.** The product is Corollary 4.2 with $\langle j,t_k-t_l\rangle=j_k-j_l$. The generators $e_k-e_{\mathtt q}=e_k$ generate $\mathbb Z_n^{\mathtt q-1}$, so $A_0=A$ and Theorem 4.1 gives $\gamma=1$. The values of $D_{\mathtt q}(0)$ are Corollaries 3.5 and 4.2, using $\mu_{\chi_j}=4\nu_j$. The description of $\Gamma_2,\Gamma_3$ reads off the generators $\pm(t_k-t_l)$ from Definition 3.2. ∎

**Theorem 5.2 (Bipartite closed form).** Let $\mathtt q=2$, $x=(p,1-p)$ and $b=(1-\varepsilon)^2p(1-p)$. For $0<\varepsilon<1$,

$$
\Delta_2(\varepsilon)=\prod_{j=0}^{n-1}\Big(\varepsilon+b\sin^2\frac{\pi j}{n}\Big)=4^{1-n}\,b^n\sinh^2\!\Big(n\,\mathrm{arsinh}\sqrt{\varepsilon/b}\Big),
$$

and

$$
D_2(0)=n^2\Big(\frac{p(1-p)}{4}\Big)^{n-1}.
$$

Stance: repo-derived proof. The formula for $\Delta_2$ is equivalent, under the identification $\nu^2=1+b/\varepsilon$, to the literature-attested Rényi entropy of a pure Gaussian state with a single nontrivial symplectic eigenvalue $\nu$ (§9); it is not claimed as new. The closed form of $D_2(0)$ is a direct consequence.

**Proof.** For $z\in\mathbb C$, $\prod_{j=0}^{n-1}(z-\omega^j)=z^n-1$ and the same with $\omega^{-j}$, so $\prod_{j}(z^2-2z\cos\theta_j+1)=(z^n-1)^2$ with $\theta_j=2\pi j/n$. Put $z=e^\phi$ with $\phi>0$: $z^2-2z\cos\theta+1=2e^\phi(\cosh\phi-\cos\theta)$, hence

$$
\prod_{j=0}^{n-1}(\cosh\phi-\cos\theta_j)=2^{-n}e^{-n\phi}(e^{n\phi}-1)^2=2^{2-n}\sinh^2\frac{n\phi}{2}.
$$

Now $\varepsilon+b\sin^2(\theta_j/2)=\tfrac b2(1+2\varepsilon/b-\cos\theta_j)$. Choose $\phi>0$ with $\cosh\phi=1+2\varepsilon/b$, i.e. $\sinh(\phi/2)=\sqrt{\varepsilon/b}$. Then the product equals $(b/2)^n2^{2-n}\sinh^2(n\phi/2)$, which is the stated formula; the first equality is Proposition 5.1 with $\nu_j=p(1-p)\sin^2(\pi j/n)$. As $\varepsilon\to0^+$, $s=\mathrm{arsinh}\sqrt{\varepsilon/b}\sim\sqrt{\varepsilon/b}$, so $\sinh^2(ns)\sim n^2\varepsilon/b$ and $\Delta_2(\varepsilon)/\varepsilon\to4^{1-n}n^2(p(1-p))^{n-1}$. Since $D_2$ is a polynomial, this limit is $D_2(0)$. Alternatively $D_2(0)=\prod_{j=1}^{n-1}p(1-p)\sin^2(\pi j/n)$ and $\prod_{j=1}^{n-1}\sin(\pi j/n)=n/2^{n-1}$, which is the case $\phi\to0$ of the product above. ∎

**Theorem 5.3 (Bipartition factorization).** For each nonempty $S\subseteq\{1,\dots,\mathtt q-1\}$ let $X_S=\{j\in\mathbb Z_n^{\mathtt q-1}:j_k=j_l\text{ for }k,l\in S,\ j_k=0\text{ for }k\notin S\}$, a cyclic subgroup of order $n$. Then:

1. For $j\in X_S$ with common value $c$ on $S$, $\nu_j=p_S(1-p_S)\sin^2(\pi c/n)$; thus the factors of Proposition 5.1 indexed by $X_S$ are exactly the factors of the bipartite determinant $\Delta_2$ with $p=p_S$.
2. $X_S\cap X_{S'}=\{0\}$ for $S\ne S'$.
3. With $\mathcal O=\mathbb Z_n^{\mathtt q-1}\setminus\bigcup_SX_S$, the set of $j$ for which $\{0,j_1,\dots,j_{\mathtt q-1}\}$ has at least three elements,

$$
D_{\mathtt q}(\varepsilon)=\prod_{S}D_{2}^{(p_S)}(\varepsilon)\cdot\Omega_{\mathtt q}(\varepsilon),\qquad \Omega_{\mathtt q}(\varepsilon)=\prod_{j\in\mathcal O}\big(\varepsilon+(1-\varepsilon)^2\nu_j\big),
$$

where $D_2^{(p)}$ is the bipartite residual polynomial with weight $p$, $|\mathcal O|=n^{\mathtt q-1}-1-(2^{\mathtt q-1}-1)(n-1)$, every factor of $\Omega_{\mathtt q}(0)$ lies in $(0,\tfrac14]$, and

$$
\Omega_{\mathtt q}(0)=\frac{n^{\mathtt q-1}\kappa(\Gamma_{\mathtt q})}{4^{|\mathcal O|}\,n^{2(2^{\mathtt q-1}-1)}\prod_S\big(p_S(1-p_S)\big)^{n-1}}.
$$

4. For $n=2$, $\mathcal O=\varnothing$ and $D_{\mathtt q}=\prod_SD_2^{(p_S)}$ identically; equivalently $\varepsilon^{2^{\mathtt q-1}-2}\Delta_{\mathtt q}(\varepsilon)=\prod_S\Delta_2^{(p_S)}(\varepsilon)$.

Stance: suspected-novel. For $\mathtt q=3$, $n=2$ item 4 is the fully symmetric case of the determinant identity behind the literature-attested $\mathrm{GM}^{(3)}_2=0$ of Camargo and Nishida, §4.

**Proof.** (1) For $k<l$ both in $S$ or both outside $S$ (the party $\mathtt q$ is outside, with $j_{\mathtt q}=0$), $j_k=j_l$; for one in $S$ and one outside, $|j_k-j_l|=c$ up to sign. So $\nu_j=\sum_{k\in S,l\notin S}x_kx_l\sin^2(\pi c/n)=p_S(1-p_S)\sin^2(\pi c/n)$, and as $c$ runs over $\mathbb Z_n$ these are the factors of Theorem 5.2 with $p=p_S$. (2) A nonzero $j\in X_S$ has support exactly $S$. (3) By (2), $\prod_{j\ne0}$ splits into the products over $X_S\setminus\{0\}$ and over $\mathcal O$; the former are $D_2^{(p_S)}(\varepsilon)=\prod_{c\ne0}(\varepsilon+b_S\sin^2(\pi c/n))$ by (1), and $D_{\mathtt q}(\varepsilon)=\prod_{j\ne0}(\varepsilon+(1-\varepsilon)^2\nu_j)$ by Proposition 5.1. A vector $j$ lies in some $X_S$ iff its coordinates together with $j_{\mathtt q}=0$ take at most two values (the nonzero value, if any, occupying $S$), which gives the description and the count of $\mathcal O$. For $j\in\mathcal O$ the values are not all equal, so some pair has $j_k\ne j_l$ and $\nu_j>0$; the factor at $\varepsilon=0$ is $\nu_j$, which is at most $\tfrac14$ because $4\nu_j=\mu_{\chi_j}=1-|\lambda_{\chi_j}|^2\le1$. The formula for $\Omega_{\mathtt q}(0)$ divides $D_{\mathtt q}(0)$ from Proposition 5.1 by $\prod_SD_2^{(p_S)}(0)$ from Theorem 5.2 and uses $n^{\mathtt q-1}-1-(2^{\mathtt q-1}-1)(n-1)=|\mathcal O|$. (4) For $n=2$ every coordinate is $0$ or $1$, so $\mathcal O=\varnothing$; multiply by $\varepsilon^{2^{\mathtt q-1}-1}$ using $\Delta=\varepsilon D$. ∎

**Corollary 5.4 (The three lines for three parties).** For $\mathtt q=3$ the subgroups $X_{\{1\}}=\{j_2=0\}$, $X_{\{2\}}=\{j_1=0\}$ and $X_{\{1,2\}}=\{j_1=j_2\}$ carry the bipartitions $A|BC$, $B|CA$ and $AB|C$ with weights $x_A$, $x_B$, $x_A+x_B=1-x_C$, and

$$
D_3(\varepsilon)=D_2^{(x_A)}(\varepsilon)\,D_2^{(x_B)}(\varepsilon)\,D_2^{(x_C)}(\varepsilon)\,\Omega_3(\varepsilon),
$$

with $\mathcal O=\{(j_1,j_2):0,j_1,j_2\text{ pairwise distinct}\}$ of size $(n-1)(n-2)$. Stance: suspected-novel.

**Proof.** Theorem 5.3 with $\mathtt q=3$, using that $D_2^{(p)}$ depends on $p$ only through $p(1-p)$, so $D_2^{(1-x_C)}=D_2^{(x_C)}$. ∎

## 6. Fully symmetric Gaussian states

**Definition 6.1 (Squeezing parameter).** For $N\ge2$ and $a\ge1$ let $s=a^2-1$,

$$
e^-=\frac{s(N-2)-\sqrt s\sqrt{sN^2+4(N-1)}}{2a(N-1)},\qquad \varepsilon(a)=\frac{a+(N-1)e^-}{a-e^-}.
$$

Here $e^-$ is the off-diagonal entry of Camargo and Nishida, §3.1. With $J$ the all-ones matrix and $u$ as in Theorem 3.8, the matrix $\mathbf W=(a-e^-)I+e^-J$ equals $\lambda(I-(1-\varepsilon(a))uu^\top)$ with $\lambda=a-e^-$, since its eigenvalue on $u$ is $a+(N-1)e^-$ and on $u^\perp$ is $a-e^-$. Stance: definition (source attested).

**Lemma 6.2 (Range and scaling of the squeezing parameter).** For $a>1$, $0<\varepsilon(a)<1$, and $\varepsilon(1)=1$. Moreover $a^2\varepsilon(a)\to(N-1)/N^2$ as $a\to\infty$. Stance: repo-derived.

**Proof.** At $a=1$, $s=0$, $e^-=0$ and $\varepsilon=1$. Let $a>1$ and $K=\sqrt{s^2N^2+4s(N-1)}$. Since $2a^2=2+2s$,

$$
a+(N-1)e^-=\frac{2+sN-K}{2a}=\frac{2a}{2+sN+K},
$$

because $(2+sN)^2-K^2=4+4s=4a^2$. So $a+(N-1)e^->0$. Since $s^2(N-2)^2<K^2$, $e^-<0$, hence $a-e^->0$ and $\varepsilon>0$; and $\varepsilon<1$ iff $Ne^-<0$. For the limit,

$$
a^2\varepsilon(a)=\frac{a\,(a+(N-1)e^-)}{(a-e^-)/a}=\frac{2a^2/(2+sN+K)}{1-e^-/a}.
$$

As $a\to\infty$, $(2+sN+K)/a^2\to2N$, so the numerator tends to $1/N$; and $e^-/a=\frac{s(N-2)-K}{2a^2(N-1)}\to\frac{(N-2)-N}{2(N-1)}=-\frac1{N-1}$, so the denominator tends to $\frac N{N-1}$. ∎

**Definition 6.3 (Gaussian multi-entropies).** Fix $\mathtt q\ge2$, party sizes $N_1,\dots,N_{\mathtt q}\ge1$, $N=\sum N_k$ (so $N\ge2$), $x_k=N_k/N$, $n\ge2$ and $a>1$. The fully symmetric Gaussian state is $\psi_a(y)=\exp(-\frac12y^\top\mathbf Wy)$ on $\mathbb R^N$ with $\mathbf W$ of Definition 6.1, party $k$ owning the coordinates of the block $B_k$ of Theorem 3.8. Let $Z^{(\mathtt q)}_n$ be the normalized twisted replica integral $\mathcal Z(R,g)$ of Theorem 3.8 for $\psi_a$ and the datum of Convention 2.4, and
$$
S^{(\mathtt q)}_n=\frac{1}{1-n}\,\frac{1}{n^{\mathtt q-2}}\log Z^{(\mathtt q)}_n .
$$
Bipartite entropies $S^{(2)}_n(S)$ use $\mathtt q=2$ with the two merged parties of a bipartition, and
$$
\mathrm{GM}^{(3)}_n=S^{(3)}_n-\tfrac12\big(S^{(2)}_n(AB{:}C)+S^{(2)}_n(BC{:}A)+S^{(2)}_n(CA{:}B)\big).
$$
Stance: definition; it is the multi-entropy and genuine tripartite multi-entropy of Camargo and Nishida, §2.1 and §2.3, for their fully symmetric state of §3.1 (literature-attested). By Lemma 6.2 and Definition 6.1, $\psi_a$ has the form of Theorem 3.8 with $\lambda=a-e^->0$ and $\varepsilon=\varepsilon(a)\in(0,1)$, so
$$
Z^{(\mathtt q)}_n=\Big(\frac{\varepsilon^{n^{\mathtt q-1}}}{\Delta_{\mathtt q}(\varepsilon)}\Big)^{1/2},
$$
and $\Delta_{\mathtt q}(\varepsilon)>0$ by Corollary 3.5, so all logarithms are defined. Theorems 6.4–7.2 below concern the quantities so defined.

**Theorem 6.4 (Exact tripartite genuine multi-entropy).** For $\mathtt q=3$, all $n\ge2$, all $N_A,N_B,N_C\ge1$ and all $a>1$, with $\varepsilon=\varepsilon(a)$, $b_p=(1-\varepsilon)^2p(1-p)$ and $D_2^{(p)}(\varepsilon)=4^{1-n}b_p^n\varepsilon^{-1}\sinh^2(n\,\mathrm{arsinh}\sqrt{\varepsilon/b_p})$ (here $0<\varepsilon<1$ by Lemma 6.2, so $b_p>0$ and Theorem 5.2 applies),

$$
\mathrm{GM}^{(3)}_n=\frac{n-2}{4n}\log\varepsilon+\frac{\log\Omega_3(\varepsilon)}{2n(n-1)}+\frac{2-n}{4n(n-1)}\sum_{p\in\{x_A,x_B,x_C\}}\log D_2^{(p)}(\varepsilon),
$$

$$
\Omega_3(\varepsilon)=\prod_{\substack{j_1,j_2\in\mathbb Z_n\\ 0,j_1,j_2\ \text{distinct}}}\Big(\varepsilon+(1-\varepsilon)^2\big(x_Ax_C\sin^2\tfrac{\pi j_1}{n}+x_Bx_C\sin^2\tfrac{\pi j_2}{n}+x_Ax_B\sin^2\tfrac{\pi(j_1-j_2)}{n}\big)\Big).
$$

Stance: suspected-novel. The source evaluates $\mathrm{GM}^{(3)}_n$ in closed form for $N\le8$ and $n\le4$ (Table 1, §3.2); the formula above covers all $n$ and $N$.

**Proof.** With $\Delta=\varepsilon D$, $\log Z_n^{(3)}=\tfrac12\big((n^2-1)\log\varepsilon-\log D_3\big)$ and $\log Z_n^{(2)}=\tfrac12\big((n-1)\log\varepsilon-\log D_2\big)$. Hence

$$
S^{(3)}_n=-\frac{n+1}{2n}\log\varepsilon+\frac{\log D_3}{2n(n-1)},\qquad S^{(2)}_n=-\frac12\log\varepsilon+\frac{\log D_2}{2(n-1)},
$$

and $\mathrm{GM}^{(3)}_n=\frac{n-2}{4n}\log\varepsilon+\frac{\log D_3}{2n(n-1)}-\frac{1}{4(n-1)}\sum\log D_2$. Insert $\log D_3=\sum\log D_2^{(p)}+\log\Omega_3$ from Corollary 5.4, where the three bipartitions $AB{:}C$, $BC{:}A$, $CA{:}B$ have $p(1-p)$ equal to that of $x_C$, $x_A$, $x_B$, and use $\frac1{2n(n-1)}-\frac1{4(n-1)}=\frac{2-n}{4n(n-1)}$. The expression for $D_2^{(p)}$ is Theorem 5.2 and that of $\Omega_3$ is Theorem 5.3 with $\nu_j$ written out. ∎

**Theorem 6.5 (Large-squeezing constant).** Under the hypotheses of Theorem 6.4,

$$
\lim_{a\to\infty}\Big(\mathrm{GM}^{(3)}_n-\frac{2-n}{2n}\log a\Big)=K_n,
$$

$$
K_n=\frac{n-2}{4n}\Big(\log\frac{N-1}{N^2}-\frac{6\log n}{n-1}-\sum_{p\in\{x_A,x_B,x_C\}}\log\frac{p(1-p)}{4}\Big)+\frac{\log\Omega_3(0)}{2n(n-1)},
$$

with $\Omega_3(0)=\prod_{j\in\mathcal O}\nu_j$ the product of Corollary 5.4 at $\varepsilon=0$, equivalently $\Omega_3(0)=\kappa(\Gamma_3)\big/\big(n^4\,4^{(n-1)(n-2)}\prod_p(p(1-p))^{n-1}\big)$ in terms of the weighted spanning trees of the triangular torus. For $n=2$, $K_2=0$ and $\mathrm{GM}^{(3)}_2=0$ for every $a>1$. Stance: suspected-novel; it contains the leading term $\frac{2-n}{2n}\log a$ conjectured by Camargo and Nishida, Eq. (3.8).

**Proof.** By Theorem 6.4, $\mathrm{GM}^{(3)}_n-\frac{2-n}{2n}\log a=\frac{n-2}{4n}\log(a^2\varepsilon)+\frac{\log\Omega_3(\varepsilon)}{2n(n-1)}+\frac{2-n}{4n(n-1)}\sum\log D_2^{(p)}(\varepsilon)$, using $\log\varepsilon=\log(a^2\varepsilon)-2\log a$. As $a\to\infty$, Lemma 6.2 gives $\varepsilon\to0$ and $a^2\varepsilon\to(N-1)/N^2$; $\Omega_3$ and $D_2^{(p)}$ are polynomials in $\varepsilon$, positive at $0$ (Theorem 5.3 and Corollary 3.5), so their logarithms converge to the values at $0$. With $D_2^{(p)}(0)=n^2(p(1-p)/4)^{n-1}$ (Theorem 5.2), $\frac{2-n}{4n(n-1)}\sum_p\log D_2^{(p)}(0)=-\frac{n-2}{4n}\big(\frac{6\log n}{n-1}+\sum_p\log\frac{p(1-p)}4\big)$. The tree form of $\Omega_3(0)$ is Theorem 5.3(3) with $\mathtt q=3$. For $n=2$, $\mathcal O=\varnothing$, so $\Omega_3\equiv1$ and the coefficients $\frac{n-2}{4n}$, $\frac{2-n}{4n(n-1)}$ vanish. ∎

**Corollary 6.6 (Replica orders three and four).** Write $\sigma_2=N_AN_B+N_BN_C+N_CN_A$, $\sigma_3=N_AN_BN_C$, $e_2=\sigma_2/N^2$ and $\tau_A=x_Bx_C$, $\tau_B=x_Cx_A$, $\tau_C=x_Ax_B$. Then

$$
K_3=\frac1{12}\log\frac{4(N-1)\sigma_2^2}{3\,\sigma_3\,(N-N_A)(N-N_B)(N-N_C)},
$$

$$
K_4=\frac18\Big(\log\frac{N-1}{N^2}-\log16-\sum_{p}\log\frac{p(1-p)}4\Big)+\frac1{24}\sum_{k\in\{A,B,C\}}2\log\frac{e_2+\tau_k}{2}.
$$

In particular $K_3=\tfrac1{12}\log3$ for $(N_A,N_B,N_C)=(1,1,1)$ and $K_3=\tfrac16\log\tfrac53$ for $(2,1,1)$. Stance: suspected-novel.

**Proof.** For $n=3$, $\mathcal O=\{(1,2),(2,1)\}$ and each $\nu_j=\tfrac34(x_Ax_C+x_Bx_C+x_Ax_B)=\tfrac34e_2$, so $\Omega_3(0)=\tfrac9{16}e_2^2$. Then $K_3=\frac1{12}\big(\log\frac{N-1}{N^2}-\log27-\sum_p\log(p(1-p))+3\log4+\log\frac9{16}+2\log e_2\big)=\frac1{12}\log\frac{4(N-1)e_2^2}{3N^2\prod_pp(1-p)}$, and $\prod_pp(1-p)=\sigma_3\prod_k(N-N_k)/N^6$. For $n=4$, $\mathcal O$ has six elements; with $\sin^2(\pi/4)=\sin^2(3\pi/4)=\tfrac12$ and $\sin^2(\pi/2)=1$ one finds $\nu_{(1,2)}=\nu_{(3,2)}=\tfrac12(x_Ax_C+x_Ax_B)+x_Bx_C=\tfrac12(e_2+\tau_A)$, $\nu_{(2,1)}=\nu_{(2,3)}=\tfrac12(e_2+\tau_B)$ and $\nu_{(1,3)}=\nu_{(3,1)}=\tfrac12(e_2+\tau_C)$; insert into Theorem 6.5 with $6\log4/3=\log16$. ∎

## 7. Replica order two for any number of parties

**Theorem 7.1 (Order-two multi-entropy).** In the setting of Definition 6.3 with $n=2$ and any $\mathtt q\ge2$,

$$
S^{(\mathtt q)}_2=2^{2-\mathtt q}\sum_{S}S^{(2)}_2(S),
$$

the sum running over the $2^{\mathtt q-1}-1$ bipartitions of the parties. Stance: suspected-novel. For $\mathtt q=3$ it is the fully symmetric case of $\mathrm{GM}^{(3)}_2=0$, literature-attested for all pure bosonic Gaussian states (Camargo and Nishida, §4); the Gaussian replica reduction is essential (Remark 8.3).

**Proof.** Put $M=2^{\mathtt q-1}$. By Theorem 5.3(4), $\sum_S\log\Delta_2^{(p_S)}=\log\Delta_{\mathtt q}+(M-2)\log\varepsilon$. Then $\sum_SS^{(2)}_2(S)=-\tfrac12\sum_S\big(2\log\varepsilon-\log\Delta_2^{(p_S)}\big)=-\tfrac12\big(2(M-1)-(M-2)\big)\log\varepsilon+\tfrac12\log\Delta_{\mathtt q}=-\tfrac M2\log\varepsilon+\tfrac12\log\Delta_{\mathtt q}$, while $S^{(\mathtt q)}_2=-2^{2-\mathtt q}\cdot\tfrac12\big(M\log\varepsilon-\log\Delta_{\mathtt q}\big)$. ∎

**Corollary 7.2 (Four-party genuine multi-entropy at order two).** Let $\mathtt q=4$ with parties $A,B,C,D$ and let $\mathrm{GM}^{(4)}_n$ be the genuine four-party multi-entropy of Iizuka and Nishida with parameters $\alpha+\beta=\tfrac13$, namely $S^{(4)}_n-\tfrac13\sum S^{(3)}_n(XY{:}Z{:}W)+\alpha\sum S^{(2)}_n(XY{:}ZW)+\beta\sum S^{(2)}_n(XYZ{:}W)$ over the six merges, three pair cuts and four single cuts. For the fully symmetric Gaussian state,

$$
\mathrm{GM}^{(4)}_2=\Big(\beta-\frac14\Big)\Big(\sum_{\text{single cuts}}S^{(2)}_2-\sum_{\text{pair cuts}}S^{(2)}_2\Big),
$$

which vanishes identically for $\beta=\tfrac14$, $\alpha=\tfrac1{12}$. Stance: suspected-novel; the definition of $\mathrm{GM}^{(4)}_n$ is literature-attested (§9).

**Proof.** Write $s_X$ for the entropy of the single cut $X{:}\text{rest}$ and $\mathsf p$ for the three pair cuts. By Theorem 7.1 with $\mathtt q=4$, $S^{(4)}_2=\tfrac14(\sum s+\sum\mathsf p)$. A merge $XY{:}Z{:}W$ is a fully symmetric three-party datum with weights $x_X+x_Y,x_Z,x_W$, so Theorem 7.1 with $\mathtt q=3$ gives $S^{(3)}_2(XY{:}Z{:}W)=\tfrac12(\mathsf p_{XY}+s_Z+s_W)$. Over the six merges each pair cut occurs twice ($XY$ and its complement) and each single cut three times, so $\tfrac13\sum S^{(3)}_2=\tfrac13\sum\mathsf p+\tfrac12\sum s$. Hence $\mathrm{GM}^{(4)}_2=(\tfrac14-\tfrac12+\beta)\sum s+(\tfrac14-\tfrac13+\alpha)\sum\mathsf p$, and $\alpha-\tfrac1{12}=\tfrac14-\beta$. ∎

## 8. Boundaries

**Remark 8.1 (What is not computed).** The remainder $\Omega_{\mathtt q}(0)$ is given only as a finite product of trigonometric sums, equivalently as a weighted spanning-tree count of the Cayley multigraph $\Gamma_{\mathtt q}$; no further closed form in $n$ is claimed, nor its asymptotics as $n\to\infty$.

**Remark 8.2 (Many parties).** For $\mathtt q\ge4$ the volume gives the exact determinants (Proposition 5.1), their bipartite factorization (Theorem 5.3) and the order-two identity (Theorem 7.1). It makes no claim about the large-squeezing law of a genuine $\mathtt q$-party multi-entropy for $\mathtt q\ge4$ and $n\ge3$: such a law depends on the normalization chosen for the genuine combination, and the coefficient of $\log\varepsilon$ must be recomputed from the replica counts for each choice.

**Remark 8.3 (The order-two identity fails for a three-qubit state).** The identity of Theorem 7.1 at $\mathtt q=3$ is not an identity of all pure states. For the W state $\psi_W=3^{-1/2}(|001\rangle+|010\rangle+|100\rangle)$, Iizuka and Nishida (arXiv:2502.07995, §2 and §2.2) give $S^{(3)}_2(\psi_W)=\log3$ and $\mathrm{GM}^{(3)}_2(\psi_W)=\log\tfrac{5\sqrt5}{9}=\tfrac12\log\tfrac{125}{81}\ne0$, and $\mathrm{GM}^{(3)}_2$ is the left side of Theorem 7.1 at $\mathtt q=3$. The Gaussian replica reduction is therefore essential. Stance: the value is literature-attested (§9).

**Remark 8.4 (Open case).** Theorem 7.1 is stated only for fully symmetric Gaussian states; its validity for general pure Gaussian states with $\mathtt q\ge4$ is open.

## 9. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| H. A. Camargo, M. Nishida, *Genuine Multi-Entropy of Fully Symmetric Gaussian States*, arXiv:2609.30754v1, §2.1, §2.3, §3.1, §3.2 Table 1 and Eq. (3.8), §4 | `literature-attested`: the multi-entropy, the twists for three parties, the Gaussian kernel, the fully symmetric state and $e^-$, the exact values of Table 1 for $N\le8$, $n\le4$, the conjectured leading term, and $\mathrm{GM}^{(3)}_2=0$ for pure bosonic Gaussian states via a $\mathbb Z_2\times\mathbb Z_2$ block decomposition at $n=2$. The paper contains no determinant formula for general $n$, no character or spanning-tree form, no closed form of the bipartite Rényi entropy, and no result for $\mathtt q\ge4$ (§6 lists $\mathtt q>3$ as a future direction). |
| N. Iizuka, M. Nishida, *Genuine multi-entropy and holography*, arXiv:2502.07995, §2, §2.2, Eqs. (67)–(68) | `literature-attested`: the definition of $\mathrm{GM}^{(4)}_n$ with $\alpha+\beta=\tfrac13$, used in Corollary 7.2; and, in §2 and §2.2, the W-state values $S^{(3)}_2=\log3$ and $\mathrm{GM}^{(3)}_2=\log(5\sqrt5/9)$, used in Remark 8.3. |
| S. Chaiken, *A combinatorial proof of the all minors matrix tree theorem*, SIAM J. Algebraic Discrete Methods 3 (1982) 319–329; P. Chebotarev, E. Shamis, *The matrix-forest theorem and measuring relations in small social groups*, Autom. Remote Control 58 (1997) 1505–1514 | `literature-attested`: principal minors of a weighted Laplacian count spanning forests rooted in the deleted set; $\det(sI+L)$ is the rooted-forest polynomial. Used inside Theorem 3.4. |
| G. Kirchhoff (1847); N. Biggs, *Algebraic Graph Theory*, 2nd ed., Cambridge 1993, Ch. 6–7 | `literature-attested`: the matrix-tree theorem and the tree count of Cayley graphs of abelian groups via characters; used in Corollary 4.2. |
| J.-P. Serre, *Linear Representations of Finite Groups*, Springer 1977, §3 | `literature-attested`: characters of a finite abelian group form an orthogonal basis; used in Theorem 4.1. |
| A. Serafini, G. Adesso, F. Illuminati, *Unitarily localizable entanglement of Gaussian states*, Phys. Rev. A 71 (2005) 032349; G. Adesso, A. Serafini, F. Illuminati, Phys. Rev. A 70 (2004) 022318 | `literature-attested`: a bisymmetric pure Gaussian state is locally equivalent to a two-mode squeezed state times vacua, so each bipartite cut has one nontrivial symplectic eigenvalue $\nu$ and $\mathrm{tr}\rho^n=2^n/((\nu+1)^n-(\nu-1)^n)$. Theorem 5.2 is equivalent to this with $\nu^2=1+b/\varepsilon$ and is not claimed as new. |
| R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge 2013 | `literature-attested`: Sylvester's identity $\det(I_n+BC)=\det(I_m+CB)$, and the Schur complement determinant formula. Used in Theorem 3.8. |
| — | `repo-derived`: the simple-zero statement of Remark 3.7, Corollary 3.6, Theorem 3.8, Theorem 5.2 (proof), Lemma 6.2. |
| — | `suspected-novel`: Theorems 3.3, 3.4 (as a replica-determinant identity), Corollary 3.5, Theorem 4.1, Corollary 4.2 (sine product), Proposition 5.1, Theorem 5.3, Corollary 5.4, Theorems 6.4, 6.5, Corollary 6.6, Theorem 7.1, Corollary 7.2. Searched: the full text of arXiv:2609.30754v1; the definitions of arXiv:2502.07995; web and arXiv searches for multi-entropy together with Gaussian, replica, spanning tree, Laplacian and matrix-tree. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
