# Schwarz maps in the Tomiyama family with a diagonal perturbation

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

For $d\ge3$ consider the unital maps $\Phi(X)=\lambda X+(1-dq-\lambda)\,\mathrm{diag}(X)+q\,\mathrm{tr}(X)\,I$ on $M_d(\mathbb C)$ with real parameters $\lambda,q$. This volume computes the Schwarz defect $\Phi(X^\ast X)-\Phi(X)^\ast\Phi(X)$ of this family in closed form, reduces the Schwarz property to a family of $d\times d$ Schur-complement conditions indexed by the probability simplex, derives four explicit necessary inequalities with explicit witnesses, determines the Schwarz maps exactly on the slice $q=0$, and shows that the region cut out by the four inequalities is convex. Whether the four inequalities are also sufficient is left open (Open question 6.2); in particular the question quoted in cited fact (a)(iii) is not settled here.

## 2. Notation and cited facts

**Cited facts.**

- (a) A. Bera, B. Bhattacharya, D. Chruściński, *Tomiyama-type maps with a diagonal perturbation*, arXiv:2604.18600v1. (i) Eq. (6): for real $\alpha,\beta$, $\Phi_{\alpha,\beta}=(1-\alpha-\beta)\,\mathrm{id}+\alpha\,\tau_0+\beta\,\Delta$ on $M_d(\mathbb C)$, where $\tau_0(X)=\mathrm{tr}(X)\,I/d$ and $\Delta$ is the projection of a matrix onto its diagonal. (ii) Proposition 2.1, item 2, Eq. (9): $\Phi_{\alpha,\beta}$ is completely positive if and only if $0\le\alpha\le d/(d-1)$ and $-\alpha/d\le\beta\le d/(d-1)-(d+1)\alpha/d$. (iii) Section 4 (Conclusions and outlook) states: “it would be interesting to extend the analysis and study which maps Φα,β and Λμ,ν satisfy Schwarz inequality.”
- (b) A. García-Velo, A. Ibort, *Schwarz maps with symmetry*, arXiv:2601.02282v1. (i) Theorem V.4 (Schwarz $DU(n)$-equivariant maps): for a $DU(n)$-equivariant, unital, Hermiticity-preserving Schwarz map with off-diagonal multipliers $\lambda_{ij}$ and diagonal block $(c_{ij})$, one has $c_{kj}\in[0,1]$ for $k\ne j$ and $c_{jj}\ge|\lambda_{ij}|^2$. (ii) Subsection V.2.2 considers, for $n=3$ and a complex parameter $\lambda\in\mathbb C$, the map with $[\Phi(X)]_{ij}=\lambda X_{ij}$ for $i\ne j$ and $[\Phi(X)]_{ii}=pX_{ii}+\frac{1-p}{2}(X_{jj}+X_{kk})$ for $\{i,j,k\}=\{1,2,3\}$, and Proposition V.4 (Symmetric $DU(3)$ family: exact Schwarz and CP regions), item 1, states that $\Phi$ is Schwarz if and only if “$0 \le p \le 1, \quad |\lambda|^2 \le \frac{1}{2} \min \{p, \, 1 - p\}$”. (iii) In the proof of Proposition V.4, for $X=\alpha E_{ij}+\beta E_{kj}$, the diagonal of $\Phi(X^\dagger X)-\Phi(X)^\dagger\Phi(X)$ is given as “$(j, j): p (|\alpha|^2 + |\beta|^2) - |\lambda|^2 |\alpha + \beta|^2$”, “$(i, i): \frac{1-p}{2} (|\alpha|^2 + |\beta|^2) - |\lambda|^2 |\alpha|^2$” and “$(k, k): \frac{1-p}{2} (|\alpha|^2 + |\beta|^2) - |\lambda|^2 |\beta|^2$”.
- (c) M.-D. Choi, *A Schwarz inequality for positive linear maps on $C^\ast$-algebras*, Illinois J. Math. 18 (1974) 565–574: a unital $2$-positive map, in particular a unital completely positive map, satisfies $\Phi(X^\ast X)\ge\Phi(X)^\ast\Phi(X)$ for all $X$.
- (d) Standard rank-one identities: for an invertible matrix $E$ and vectors $u,w$, put $g=w^{T}E^{-1}u$; then $\det(E+uw^{T})=\det(E)\,(1+g)$, and if $1+g\ne0$, $(E+uw^{T})^{-1}=E^{-1}-E^{-1}uw^{T}E^{-1}/(1+g)$. Proof: with $a=E^{-1}u$, eliminating the lower-right entry of $\begin{pmatrix} I & a\\ -w^{T} & 1\end{pmatrix}$ gives determinant $\det(I+aw^{T})$, and eliminating the upper-left block gives $1+w^{T}a$, so $\det(E+uw^{T})=\det E\,\det(I+aw^{T})=\det(E)(1+g)$; and $(E+uw^{T})\big(E^{-1}-E^{-1}uw^{T}E^{-1}/(1+g)\big)=I+uw^{T}E^{-1}-(1+g)\,uw^{T}E^{-1}/(1+g)=I$.
- (e) A. Albert, *Conditions for positive and nonnegative definiteness in terms of pseudoinverses*, SIAM J. Appl. Math. 17 (1969) 434–440, DOI 10.1137/0117041: positive semidefiniteness of a symmetric block matrix through the generalized Schur complement. Step 4 of the proof of Theorem 3.2 re-derives the special case used here.
- (f) D. Chruściński, B. Bhattacharya, *A class of Schwarz qubit maps with diagonal unitary and orthogonal symmetries*, arXiv:2404.10895, J. Phys. A 57 (2024) 395202: Schwarz qubit maps with diagonal unitary and orthogonal symmetries. This volume makes no statement for $d=2$.

**Convention 2.1 (The family).** Fix an integer $d\ge3$ and real numbers $\lambda,q$. Put $\mu=1-dq-\lambda$ and define $\Phi=\Phi_{\lambda,q}\colon M_d(\mathbb C)\to M_d(\mathbb C)$ by

$$
\Phi(X)=\lambda X+\mu\,\mathrm{diag}(X)+q\,\mathrm{tr}(X)\,I ,
$$

where $\mathrm{diag}(X)$ keeps the diagonal of $X$ and sets all other entries to zero. In the notation of cited fact (a)(i), $\Phi_{\lambda,q}=\Phi_{\alpha,\beta}$ with $\alpha=dq$ and $\beta=\mu$, so $\lambda=1-\alpha-\beta$. The map is unital, trace-preserving and Hermiticity-preserving, and it commutes with conjugation by diagonal unitaries: $\Phi(UXU^\ast)=U\Phi(X)U^\ast$ for every diagonal unitary $U$. Write $p=1-(d-1)q$. The Schwarz defect is $S(X)=\Phi(X^\ast X)-\Phi(X)^\ast\Phi(X)$, and $\Phi$ is called Schwarz if $S(X)\ge0$ (positive semidefinite) for every $X\in M_d(\mathbb C)$. For $X\in M_d(\mathbb C)$ write $D=\mathrm{diag}(X)$, $Y=X-D$ and $\|X\|^2=\mathrm{tr}(X^\ast X)$. Stance: repo-derived (notation fixed in this volume).

**Convention 2.2 (Row data).** Let $\Delta_d=\{t\in\mathbb R^d: t_j\ge0,\ \sum_j t_j=1\}$, and for $t\in\Delta_d$ put $s_j=\sqrt{t_j}$ and $e_j(t)=\mu t_j+q$. For $i\in\{1,\dots,d\}$ let $\sigma^{(i)}=(s_j)_{j\ne i}\in\mathbb R^{d-1}$ and define the real symmetric matrices

$$
P_i(t)=\mathrm{diag}\big(e_j(t)\big)_{j\ne i}+\lambda(1-\lambda)\,\sigma^{(i)}\sigma^{(i)T},\qquad M_i(t)=\begin{pmatrix} A_i(t) & b_i(t)^{T}\\ b_i(t) & P_i(t)\end{pmatrix},
$$

with $A_i(t)=dq(1-dq)\,t_i+q$ and $b_i(t)=\lambda dq\,s_i\,\sigma^{(i)}$. Define $\kappa_i(t)=A_i(t)-b_i(t)^{T}P_i(t)^{+}b_i(t)$ if $P_i(t)\ge0$ and $b_i(t)$ lies in the range of $P_i(t)$, where ${}^{+}$ is the Moore–Penrose inverse, and $\kappa_i(t)=-\infty$ otherwise. When $e_j(t)\ne0$ for all $j\ne i$ put $c_i(t)=\sum_{j\ne i}t_j/e_j(t)$. Stance: repo-derived (notation fixed in this volume).

## 3. The defect identity and the reduction

**Lemma 3.1 (Defect identity).** For every $X\in M_d(\mathbb C)$ and $c\in\mathbb C$ one has $S(X+cI)=S(X)$. If $\mathrm{tr}X=0$, then

$$
S(X)=dq(1-dq)\,D^\ast D+\lambda dq\,(D^\ast Y+Y^\ast D)+\lambda(1-\lambda)\,Y^\ast Y+\mu\,\mathrm{diag}(Y^\ast Y)+q\|X\|^2 I .
$$

Stance: repo-derived.

**Proof.** Since $\Phi$ is Hermiticity-preserving, $\Phi(X^\ast)=\Phi(X)^\ast$, and $\Phi(I)=I$. Expanding, $\Phi\big((X+cI)^\ast(X+cI)\big)=\Phi(X^\ast X)+\bar c\,\Phi(X)+c\,\Phi(X)^\ast+|c|^2I$ and $\Phi(X+cI)^\ast\Phi(X+cI)=\Phi(X)^\ast\Phi(X)+\bar c\,\Phi(X)+c\,\Phi(X)^\ast+|c|^2I$; the difference is $S(X)$. Now let $\mathrm{tr}X=0$ and put $a=1-dq=\lambda+\mu$. Then $\Phi(X)=aD+\lambda Y$, so $\Phi(X)^\ast\Phi(X)=a^2D^\ast D+a\lambda(D^\ast Y+Y^\ast D)+\lambda^2Y^\ast Y$. The matrices $D^\ast Y$ and $Y^\ast D$ have zero diagonal, hence $\mathrm{diag}(X^\ast X)=D^\ast D+\mathrm{diag}(Y^\ast Y)$ and

$$
\Phi(X^\ast X)=aD^\ast D+\lambda(D^\ast Y+Y^\ast D)+\lambda Y^\ast Y+\mu\,\mathrm{diag}(Y^\ast Y)+q\|X\|^2I .
$$

Subtracting and using $a-a^2=dq(1-dq)$ and $\lambda-a\lambda=\lambda dq$ gives the stated identity. ∎

**Theorem 3.2 (Reduction to the simplex).** $\Phi$ is Schwarz if and only if for every $t\in\Delta_d$ the following two conditions hold: (A) $\kappa_i(t)>-\infty$ for every $i$, that is, $P_i(t)\ge0$ and $b_i(t)$ lies in the range of $P_i(t)$; (B) either $\kappa_i(t)\ge0$ for every $i$, or there is exactly one index $k$ with $\kappa_k(t)<0$, one has $\kappa_i(t)>0$ for all $i\ne k$, and $\sum_{i=1}^{d}1/\kappa_i(t)\le0$. Stance: suspected-novel (see §7).

**Proof.** Step 1 (traceless matrices). Every $X$ equals $X_0+cI$ with $\mathrm{tr}X_0=0$, so by Lemma 3.1 it suffices to test traceless $X$.

Step 2 (nonnegative vectors). Let $v\in\mathbb C^d$ be nonzero and let $U$ be the diagonal unitary with $v=U|v|$, where $|v|$ is the entrywise modulus. By diagonal-unitary covariance $S(U^\ast XU)=U^\ast S(X)U$, so $v^\ast S(X)v=|v|^{T}S(U^\ast XU)|v|$, and $U^\ast XU$ is traceless when $X$ is. Since the defect is quadratic in $v$, $\Phi$ is Schwarz if and only if $s^{T}S(X)s\ge0$ for every traceless $X$ and every $s$ of the form $s_j=\sqrt{t_j}$ with $t\in\Delta_d$.

Step 3 (row decomposition). Fix $t\in\Delta_d$ and $s$ as above, and write a traceless $X$ as $D+Y$ with $D=\mathrm{diag}(z_1,\dots,z_d)$, $\sum_iz_i=0$, and $Y=(y_{ij})$ with zero diagonal. Put $w_i=\sum_{j\ne i}y_{ij}s_j$. Then $s^{T}D^\ast Ds=\sum_it_i|z_i|^2$, $s^{T}(D^\ast Y+Y^\ast D)s=2\,\mathrm{Re}\sum_i\bar z_is_iw_i$, $s^{T}Y^\ast Ys=\sum_i|w_i|^2$, $s^{T}\mathrm{diag}(Y^\ast Y)s=\sum_i\sum_{j\ne i}t_j|y_{ij}|^2$ and $\|X\|^2=\sum_i|z_i|^2+\sum_i\sum_{j\ne i}|y_{ij}|^2$, while $s^{T}s=1$. By Lemma 3.1,

$$
s^{T}S(X)s=\sum_{i=1}^{d}\zeta_i^\ast M_i(t)\,\zeta_i ,\qquad \zeta_i=\big(z_i,(y_{ij})_{j\ne i}\big)\in\mathbb C^{d}.
$$

The off-diagonal variables of different rows are disjoint and unconstrained; only $z$ is constrained by $\sum_iz_i=0$.

Step 4 (minimizing one row). Fix $i$, write $M=M_i(t)$, $P=P_i(t)$, $b=b_i(t)$, and let $F(z,\eta)=(z,\eta)^\ast M(z,\eta)=A_i(t)|z|^2+2\,\mathrm{Re}(\bar z\,b^{T}\eta)+\eta^\ast P\eta$ for $z\in\mathbb C$, $\eta\in\mathbb C^{d-1}$. If $P$ has a negative eigenvalue with eigenvector $\eta_0$, then $F(z,\tau\eta_0)\to-\infty$ as $\tau\to\infty$ for every $z$. If $P\ge0$ and $b$ is not in the range of $P$, choose a real $\eta_0$ in the kernel of $P$ with $b^{T}\eta_0>0$; for $z\ne0$, $F(z,-\tau z\eta_0)=A_i(t)|z|^2-2\tau|z|^2b^{T}\eta_0\to-\infty$, while $\inf_\eta F(0,\eta)=0$. If $P\ge0$ and $b=P\beta$, then $F(z,\eta)=(\eta+z\beta)^\ast P(\eta+z\beta)+|z|^2\big(A_i(t)-\beta^{T}P\beta\big)$ and $\beta^{T}P\beta=b^{T}P^{+}b$, so $\inf_\eta F(z,\eta)=\kappa_i(t)|z|^2$. In all cases with $P\ge0$, $\inf_\eta F(0,\eta)=0$, and $\inf_\eta F(z,\eta)=\kappa_i(t)|z|^2$ for $z\ne0$ with the convention $-\infty\cdot|z|^2=-\infty$.

Step 5 (the diagonal form on the hyperplane). By Steps 3 and 4, $s^{T}S(X)s\ge0$ for all traceless $X$ if and only if every $P_i(t)\ge0$ and $\sum_i\kappa_i(t)|z_i|^2\ge0$ for all $z\in\mathbb C^d$ with $\sum_iz_i=0$, terms with $z_i=0$ being omitted. If some $\kappa_k(t)=-\infty$, the vector $z=e_k-e_l$ with $l\ne k$ violates this; hence (A) is necessary. Assume (A). If two values $\kappa_j(t),\kappa_k(t)$ with $j\ne k$ are negative, $z=e_j-e_k$ gives a negative value; if $\kappa_k(t)<0$ and $\kappa_j(t)=0$ for some $j\ne k$, the same vector gives $\kappa_k(t)<0$. If all $\kappa_i(t)\ge0$ the form is nonnegative. In the remaining case $\kappa_k(t)<0$ and $\kappa_i(t)>0$ for $i\ne k$; then $z_k=-\sum_{i\ne k}z_i$ and, by the Cauchy–Schwarz inequality,

$$
\Big|\sum_{i\ne k}z_i\Big|^2\le\Big(\sum_{i\ne k}\frac{1}{\kappa_i(t)}\Big)\Big(\sum_{i\ne k}\kappa_i(t)|z_i|^2\Big),
$$

with equality for $z_i=1/\kappa_i(t)$, $i\ne k$. Since $\kappa_k(t)<0$, this gives $\sum_i\kappa_i(t)|z_i|^2\ge\big(1+\kappa_k(t)\sum_{i\ne k}1/\kappa_i(t)\big)\sum_{i\ne k}\kappa_i(t)|z_i|^2$, with equality at that choice, and $\sum_{i\ne k}\kappa_i(t)|z_i|^2>0$ there. So the form is nonnegative on the hyperplane if and only if $1+\kappa_k(t)\sum_{i\ne k}1/\kappa_i(t)\ge0$; dividing by $\kappa_k(t)<0$, this is $\sum_{i=1}^{d}1/\kappa_i(t)\le0$. Combining with Step 2 proves the theorem. ∎

**Proposition 3.3 (Closed form of the row quantities).** Let $t\in\Delta_d$ and $i\in\{1,\dots,d\}$, and assume $e_j(t)\ne0$ for all $j\ne i$ and $1+\lambda(1-\lambda)c_i(t)\ne0$. Then $P_i(t)$ is invertible, and $P_i(t)\ge0$ holds if and only if either $e_j(t)>0$ for all $j\ne i$ and $1+\lambda(1-\lambda)c_i(t)>0$, or exactly one $e_j(t)$ with $j\ne i$ is negative, $\lambda(1-\lambda)>0$ and $1+\lambda(1-\lambda)c_i(t)<0$. In either case

$$
\kappa_i(t)=q+t_i\left(dq(1-dq)-\frac{\lambda^2d^2q^2\,c_i(t)}{1+\lambda(1-\lambda)c_i(t)}\right),
$$

and otherwise $\kappa_i(t)=-\infty$. If $q>0$ and $\mu+q>0$, then $e_j(t)>0$ for all $t\in\Delta_d$ and all $j$. Stance: repo-derived.

**Proof.** Put $E=\mathrm{diag}(e_j(t))_{j\ne i}$, $\sigma=\sigma^{(i)}$ and $\gamma=\lambda(1-\lambda)$, so $P=P_i(t)=E+\gamma\sigma\sigma^{T}$ and $\sigma^{T}E^{-1}\sigma=c_i(t)$. By the determinant identity of cited fact (d), $\det P=\det E\,(1+\gamma c_i(t))\ne0$. Since $P$ is invertible, $P\ge0$ is equivalent to $P$ being positive definite. If at least two $e_j,e_l$ are negative, the intersection of $\sigma^{\perp}$ with the span of the coordinate vectors $f_j,f_l$ contains a nonzero vector on which $P=E$ is negative. If exactly one $e_j$ is negative and $\gamma\le0$, then $f_j^{T}Pf_j=e_j+\gamma t_j<0$. If exactly one $e_j$ is negative and $\gamma>0$, then $P$ is positive definite on the subspace $\{\eta:\eta_j=0\}$ of dimension $d-2\ge1$, so by the Courant–Fischer minimax principle $P$ has at most one negative eigenvalue; as $\det E<0$, $P$ is positive definite exactly when $\det P>0$, that is, when $1+\gamma c_i(t)<0$. If all $e_j$ are positive and $\gamma\ge0$, $P$ is positive definite and $1+\gamma c_i(t)>0$. If all $e_j$ are positive and $\gamma<0$, $P$ equals $E$ on $\sigma^{\perp}$, so it has at most one negative eigenvalue, and it is positive definite exactly when $1+\gamma c_i(t)>0$. In the positive definite case $P^{+}=P^{-1}$, and the inverse formula of cited fact (d) gives $\sigma^{T}P^{-1}\sigma=c_i(t)-\gamma c_i(t)^2/(1+\gamma c_i(t))=c_i(t)/(1+\gamma c_i(t))$. Since $b_i(t)=\lambda dq\,s_i\sigma$ and $s_i^2=t_i$, the formula for $\kappa_i(t)$ follows. Finally $e_j(t)=\mu t_j+q$ is affine in $t_j\in[0,1]$ with values $q$ and $\mu+q$ at the endpoints. ∎

## 4. Necessary conditions, the slice $q=0$, and convexity

**Theorem 4.1 (Necessary conditions).** If $\Phi$ is Schwarz, then

- (i) $0\le q\le 1/(d-1)$;
- (ii) $\lambda^2\le 1-(d-1)q$;
- (iii) $(d+2)\lambda^2\le(d+2-d^2q)\big(1-(d-2)q\big)$;
- (iv) $(d-1)\lambda^2-(d-2)\lambda\le1-q$, equivalently $(1-\lambda)\big(1+(d-1)\lambda\big)\ge q$.

Stance: (i) and (ii) follow from cited fact (b)(i) applied with $c_{kj}=q$, $c_{jj}=p$ and $\lambda_{ij}=\lambda$, and are literature-attested; (iii) and (iv) are suspected-novel (see §7). The proof below is self-contained.

**Proof.** (i), (ii). For $X=E_{12}$, $X^\ast X=E_{22}$ and $\Phi(X)=\lambda E_{12}$, so $S(E_{12})=\Phi(E_{22})-\lambda^2E_{22}=(p-\lambda^2)E_{22}+q(I-E_{22})$. Hence $q\ge0$ and $\lambda^2\le p$, and then $(d-1)q\le1-\lambda^2\le1$.

(iii). Put $r=1-(d-2)q$. For real $y$ let $X_y=E_{11}-E_{22}+y(E_{12}-E_{21})$ and $v=e_1+e_2$. A direct computation with Lemma 3.1 gives

$$
v^{T}S(X_y)\,v=4\left(\frac{q(d+2-d^2q)}{2}+\lambda dq\,y+\frac{r-\lambda^2}{2}\,y^2\right).
$$

If $q=0$, inequality (iii) reads $\lambda^2\le1$ and follows from (ii). If $q>0$, then (ii) gives $r-\lambda^2\ge r-p=q>0$; taking $y=-\lambda dq/(r-\lambda^2)$, nonnegativity yields $q(d+2-d^2q)(r-\lambda^2)\ge\lambda^2d^2q^2$. Dividing by $q$ and rearranging, $(d+2-d^2q)\,r\ge\lambda^2(d^2q+d+2-d^2q)=(d+2)\lambda^2$, which is (iii).

(iv). Let $X=\sum_{j=2}^{d}E_{1j}$ and $u=\sum_{j=2}^{d}e_j$. Then $X^\ast X=uu^{T}$, $\Phi(X)=\lambda X$, $\mathrm{diag}(uu^{T})=I-E_{11}$ and $\mathrm{tr}(uu^{T})=d-1$, so $S(X)=\lambda(1-\lambda)uu^{T}+\mu(I-E_{11})+(d-1)qI$. Hence

$$
u^{T}S(X)\,u=(d-1)\Big((d-1)\lambda(1-\lambda)+\mu+(d-1)q\Big)=(d-1)\Big(1-q+(d-2)\lambda-(d-1)\lambda^2\Big),
$$

and nonnegativity is (iv). The equivalent form follows from $1+(d-2)\lambda-(d-1)\lambda^2=(1-\lambda)(1+(d-1)\lambda)$. ∎

**Proposition 4.2 (The slice $q=0$).** Let $q=0$. Then $\Phi$ is Schwarz if and only if $-1/(d-1)\le\lambda\le1$. On this slice the Schwarz maps of the family are exactly its completely positive maps. Stance: repo-derived; both proofs are given in full. The second uses only cited fact (c) (Choi's theorem) together with the Kraus form of Schur multipliers, which is proved inline: for $C=\sum_kc_kc_k^\ast\ge0$ one has $C\circ X=\sum_k\mathrm{diag}(c_k)\,X\,\mathrm{diag}(c_k)^\ast$, so $X\mapsto C\circ X$ is completely positive. The completely positive interval is read off cited fact (a)(ii).

**Proof.** For $q=0$, Lemma 3.1 gives $S(X)=(1-\lambda)\big(\lambda\,Y^\ast Y+\mathrm{diag}(Y^\ast Y)\big)$ for traceless $X$, and by the invariance $S(X+cI)=S(X)$, which leaves $Y$ unchanged, the same formula holds for every $X$. If $\lambda>1$ or $\lambda<-1/(d-1)$, then (ii) or (iv) of Theorem 4.1 fails, so $\Phi$ is not Schwarz. If $0\le\lambda\le1$, both $\lambda Y^\ast Y$ and $\mathrm{diag}(Y^\ast Y)$ are positive semidefinite and $1-\lambda\ge0$. Let $-1/(d-1)\le\lambda<0$. For $v\in\mathbb C^d$, each row of $Yv$ is a sum of at most $d-1$ terms, so by the Cauchy–Schwarz inequality

$$
v^\ast Y^\ast Yv=\sum_i\Big|\sum_{j\ne i}y_{ij}v_j\Big|^2\le(d-1)\sum_i\sum_{j\ne i}|y_{ij}|^2|v_j|^2=(d-1)\,v^\ast\mathrm{diag}(Y^\ast Y)\,v .
$$

Hence $\lambda Y^\ast Y+\mathrm{diag}(Y^\ast Y)\ge\big(1+\lambda(d-1)\big)\,\mathrm{diag}(Y^\ast Y)\ge0$, and $S(X)\ge0$. For the last sentence, $q=0$ means $\alpha=0$ and $\beta=1-\lambda$ in cited fact (a)(ii), whose conditions become $0\le1-\lambda\le d/(d-1)$, that is, $-1/(d-1)\le\lambda\le1$.

Second proof. For $q=0$, $\Phi(X)=C\circ X$ is the Schur (entrywise) multiplier by $C=\lambda J+(1-\lambda)I$, where $J$ is the all-ones matrix; the eigenvalues of $C$ are $1+(d-1)\lambda$ and $1-\lambda$, so $C\ge0$ exactly when $-1/(d-1)\le\lambda\le1$. A unital Schwarz map is positive, since $\Phi(X^\ast X)\ge\Phi(X)^\ast\Phi(X)\ge0$; applied to $J\ge0$ this gives $C=\Phi(J)\ge0$. Conversely, if $C=\sum_kc_kc_k^\ast$, then $C\circ X=\sum_k\mathrm{diag}(c_k)\,X\,\mathrm{diag}(c_k)^\ast$, so $\Phi$ is completely positive, and it is Schwarz by cited fact (c). ∎

**Proposition 4.3 (Convexity of the necessary region).** The set $K_d$ of pairs $(\lambda,q)\in\mathbb R^2$ satisfying (i)–(iv) of Theorem 4.1 is a compact convex set. Stance: repo-derived.

**Proof.** The sets defined by (i), by (ii) and by (iv) are convex: (i) is an interval in $q$, and (ii) and (iv) are sublevel sets of the convex functions $\lambda^2+(d-1)q$ and $(d-1)\lambda^2-(d-2)\lambda+q$. On the interval $0\le q\le1/(d-1)$ the affine functions $g_1(q)=d+2-d^2q$ and $g_2(q)=1-(d-2)q$ satisfy $g_1\ge(d-2)/(d-1)>0$ and $g_2\ge1/(d-1)>0$. For positive affine functions $g_1=a_1+b_1q$ and $g_2=a_2+b_2q$, the function $h=\sqrt{g_1g_2}$ satisfies $h''=-(a_1b_2-a_2b_1)^2/(4h^3)\le0$, so $h$ is concave there. Within (i), condition (iii) reads $|\lambda|\le h(q)/\sqrt{d+2}$, which describes the region between the graphs of a concave function and its negative over an interval, a convex set. The intersection of these convex sets is $K_d$. It is closed, and bounded because (i) bounds $q$ and (ii) gives $|\lambda|\le1$. ∎

**Remark 4.4 (Position of the necessary region).** Let $\mathcal S_d$ be the set of $(\lambda,q)$ for which $\Phi_{\lambda,q}$ is Schwarz and $\mathcal T_d$ the set for which it is completely positive. In the coordinates of Convention 2.1, cited fact (a)(ii) reads $0\le q\le1/(d-1)$ and $-p/(d-1)\le\lambda\le p$. By cited fact (c), $\mathcal T_d\subseteq\mathcal S_d$, and by Theorem 4.1, $\mathcal S_d\subseteq K_d$. The set $\mathcal S_d$ is convex as well: for maps $\Phi_1,\Phi_2$ and $0\le\theta\le1$,

$$
\big(\theta\Phi_1(X)+(1-\theta)\Phi_2(X)\big)^\ast\big(\theta\Phi_1(X)+(1-\theta)\Phi_2(X)\big)=\theta\,\Phi_1(X)^\ast\Phi_1(X)+(1-\theta)\,\Phi_2(X)^\ast\Phi_2(X)-\theta(1-\theta)\,Z^\ast Z ,
$$

with $Z=\Phi_1(X)-\Phi_2(X)$, which is the operator convexity of $X\mapsto X^\ast X$; and $\Phi_{\lambda,q}$ depends affinely on $(\lambda,q)$. None of the four conditions of Theorem 4.1 is implied by the other three: $(\lambda,q)=(0,-1/100)$ violates only (i), for every $d\ge3$; for $d=3$, $(\lambda,q)=(1/5,1/2)$ violates only (ii) and $(\lambda,q)=(2/3,1/4)$ violates only (iii); and $(\lambda,q)=(-1,0)$ violates only (iv), for every $d\ge3$. The upper bound in (i) is implied by (ii).

## 5. The symmetric $DU(3)$ proposition of García-Velo and Ibort

**Remark 5.1 (The identity map is Schwarz and violates the quoted criterion).** For $d=3$ the map of cited fact (b)(ii) is $\Phi_{\lambda,q}$ with $q=(1-p)/2$ and real $\lambda$, since $[\Phi_{\lambda,q}(X)]_{ii}=(1-2q)X_{ii}+q(X_{jj}+X_{kk})$. The identity map is the case $p=1$, $\lambda=1$ ($q=0$); its defect is $S(X)=X^\ast X-X^\ast X=0$, so it is Schwarz, while the criterion quoted in cited fact (b)(ii) requires $|\lambda|^2\le\frac12\min\{1,0\}=0$. So the “only if” direction of that criterion fails. The “if” direction fails as well: $p=1/2$, $\lambda=-1/2$ satisfies $|\lambda|^2=\frac14=\frac12\min\{p,1-p\}$, but corresponds to $(\lambda,q)=(-1/2,1/4)$, where $(1-\lambda)(1+2\lambda)=0<q$ violates Theorem 4.1 (iv). The diagonal entries quoted in cited fact (b)(iii) differ from the correct ones: for $X=\alpha E_{ij}+\beta E_{kj}$ with $i,j,k$ distinct, $X^\ast X=(|\alpha|^2+|\beta|^2)E_{jj}$ and $\Phi(X)^\ast\Phi(X)=|\lambda|^2(|\alpha|^2+|\beta|^2)E_{jj}$, because $E_{ji}E_{kj}=0$; hence the defect is the diagonal matrix with entry $(p-|\lambda|^2)(|\alpha|^2+|\beta|^2)$ at $(j,j)$ and $\frac{1-p}{2}(|\alpha|^2+|\beta|^2)$ at $(i,i)$ and $(k,k)$. This test matrix therefore yields only $|\lambda|^2\le p$ and $p\le1$, which are the content of cited fact (b)(i) for this family.

## 6. Boundaries and open questions

**Remark 6.1 (What this volume does not establish).** No characterization of $\mathcal S_d$ by finitely many explicit inequalities is claimed: Theorem 3.2 is an exact criterion quantified over the simplex, and Theorem 4.1 gives necessary conditions only. In particular this volume does not prove that $\mathcal S_d=K_d$ for any $d$, and does not answer the question quoted in cited fact (a)(iii). The parameters $\lambda,q$ are real throughout; complex off-diagonal multipliers, the case $d=2$, and the second family $\Lambda_{\mu,\nu}$ mentioned in cited fact (a)(iii) are not treated.

**Open question 6.2 (Sufficiency of the four inequalities).** For $d\ge3$, is every $(\lambda,q)\in K_d$ a Schwarz parameter, that is, does $\mathcal S_d=K_d$ hold? The witnesses in the proof of Theorem 4.1 are instances of Theorem 3.2 at points of $\Delta_d$ with uniform weight on one, two, or $d-1$ coordinates: the matrix $E_{12}$ tests $t=e_2$ (giving $\lambda^2\le p$) and $t=e_j$ with $j\ne2$ (giving $q\ge0$), the pair $(X_y,e_1+e_2)$ tests $t=(e_1+e_2)/2$, and $(\sum_{j\ge2}E_{1j},u)$ tests $t=u/(d-1)$. A positive answer requires showing that conditions (A) and (B) of Theorem 3.2 hold at every $t\in\Delta_d$ whenever they hold at these points; no such argument is known to this volume. A negative answer requires a point of $K_d$ and a $t\in\Delta_d$ at which (A) or (B) fails.

## 7. Sources and literature status

**Literature status (§3.7 stance for every numbered item).**

| Source | Exact scope and boundary of use |
| --- | --- |
| Bera, Bhattacharya, Chruściński, arXiv:2604.18600v1, Eq. (6), Proposition 2.1 item 2 (Eq. (9)), Section 4 | `literature-attested`: the definition of the family, its completely positive region (used in Proposition 4.2 and Remark 4.4), and the quoted question on the Schwarz property; not used for any Schwarz statement. |
| García-Velo, Ibort, arXiv:2601.02282v1, Theorem V.4, Proposition V.4 and its proof | `literature-attested`: Theorem 4.1 (i) and (ii) as a specialisation of Theorem V.4; the quoted criterion and diagonal entries discussed in Remark 5.1. |
| Choi, Illinois J. Math. 18 (1974) 565–574; Albert, SIAM J. Appl. Math. 17 (1969) 434–440 | `literature-attested`: cited steps only (complete positivity implies the Schwarz inequality; generalized Schur complements). The rank-one inverse and determinant identities of cited fact (d) are standard and proved inline. |
| Schur-multiplier route of Proposition 4.2 | `repo-derived`: the second proof of Proposition 4.2 uses positivity of unital Schwarz maps, the Kraus form $C\circ X=\sum_k\mathrm{diag}(c_k)\,X\,\mathrm{diag}(c_k)^\ast$ for $C=\sum_kc_kc_k^\ast\ge0$ (proved inline), and Choi's theorem (cited fact (c)); no further source is relied on. |
| Chruściński, Bhattacharya, arXiv:2404.10895 | `literature-attested`: the qubit case lies in their class of maps with diagonal unitary and orthogonal symmetries; used only to delimit the scope $d\ge3$. |
| — | `repo-derived`: Convention 2.1, Convention 2.2, Lemma 3.1, Proposition 3.3, Proposition 4.2 and both of its proofs (the second cites only Choi's theorem; the completely positive interval is cited from Bera et al.), Proposition 4.3, Remark 4.4, Remark 5.1, Remark 6.1. |
| — | `suspected-novel`: Theorem 3.2 and Theorem 4.1 (iii), (iv). Searched: the full texts of arXiv:2604.18600v1 and arXiv:2601.02282v1; the abstract of arXiv:2404.10895; A. Rutkowski, *Sufficient conditions for the Kadison–Schwarz property of unital positive maps on $M_3$*, arXiv:2512.18900, which gives sufficient conditions in the Bloch–Gell-Mann representation and meets this family only on the line $\mu=0$ for $d=3$; F. Mukhamedov, D. Chruściński, *Constructing k-Kadison-Schwarz maps*, arXiv:2603.11204, which treats reduction-type and depolarized-type constructions and lists diagonal-unitary covariance as a direction for further work; listings of Chruściński's work on Kadison–Schwarz maps on $M_2(\mathbb C)$; web searches combining Kadison–Schwarz inequality, Schwarz map, diagonal unitary covariance, depolarizing, dephasing, Tomiyama map and dimension $d$. No Schwarz criterion for this family, nor the reduction of Theorem 3.2 for diagonal-unitary covariant maps of this form, was found in the searched scope; this establishes no priority. |

**Scope of the arguments.** Every numbered statement is proved in this volume or cited above; no statement depends on a finite numerical computation.

## 追加锚（本行以下为增补区）
