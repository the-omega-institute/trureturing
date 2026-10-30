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

## 8. Exact two-coordinate boundary criterion in dimension three

**Theorem 8.1 (The entire simplex boundary).** For arbitrary real $\lambda,q$, let $\Phi(X)=\lambda X+(1-3q-\lambda)\mathrm{diag}(X)+q\mathrm{tr}(X)I$ on $M_3(\mathbb C)$ and $S(X)=\Phi(X^\ast X)-\Phi(X)^\ast\Phi(X)$. Define

$$
K_3=\left\{(\lambda,q)\in\mathbb R^2:\ 0\le q\le\frac12,\quad
\lambda^2\le1-2q,\quad
5\lambda^2\le(5-9q)(1-q),\quad
2\lambda^2-\lambda\le1-q\right\}.
$$

Then

$$
(\lambda,q)\in K_3
\quad\Longleftrightarrow\quad
\forall X\in M_3(\mathbb C)\ \forall v\in\mathbb C^3,
\quad |\{j:v_j\ne0\}|\le2\ \Longrightarrow\ v^\ast S(X)v\ge0.
$$

Equivalently, the two conditions (A) and (B) of Theorem 3.2 hold at every $t\in\partial\Delta_3$ exactly for the parameters in $K_3$. This includes nonuniform weights, the vertices of the simplex, all equality parameters and $v=0$. The family agrees with Bera, Bhattacharya and Chruściński, arXiv:2604.18600v1, Eq. (6), under $\alpha=3q$, $\beta=1-3q-\lambda$ (cited fact (a)); no Schwarz criterion from that source is assumed. Stance: repo-derived.

**Proof.** Suppose first that the stated scalar defect is nonnegative for every $X$ and every $v$ supported on at most two coordinates. The computations in Theorem 4.1 give all four inequalities without requiring any other probes. Indeed, $X=E_{12}$ tested on $e_1$ and $e_2$ gives $q\ge0$ and $\lambda^2\le1-2q$, hence $q\le1/2$. The matrices $X_y=E_{11}-E_{22}+y(E_{12}-E_{21})$, tested on $e_1+e_2$, give $5\lambda^2\le(5-9q)(1-q)$, with the $q=0$ case following from $\lambda^2\le1$. Finally $X=E_{12}+E_{13}$, tested on $e_2+e_3$, gives $2\lambda^2-\lambda\le1-q$. These are precisely the witnesses and scalar calculations of Theorem 4.1 at $d=3$.

Conversely, assume $(\lambda,q)\in K_3$. If $q=0$, the inequalities imply $-1/2\le\lambda\le1$: the last inequality is $(2\lambda+1)(\lambda-1)\le0$. Proposition 4.2 therefore gives $S(X)\ge0$ for every complex $X$, which proves the required assertion on this slice, including its endpoints.

Let $q>0$. Lemma 3.1 permits replacing any $X$ by $X-\mathrm{tr}(X)I/3$. Diagonal-unitary covariance removes all phases of the probe as in Step 2 of Theorem 3.2. Conjugation by a permutation matrix also commutes with $\Phi$, since it commutes with taking the diagonal and preserves the trace. Thus, after normalization of any nonzero probe supported on at most two coordinates, it suffices to prove

$$
s^T S(X)s\ge0,\qquad s=(\sqrt u,\sqrt w,0)^T,\qquad w=1-u,\quad 0\le u\le1,
$$

for every traceless complex $X$. The case $v=0$ has scalar defect zero. Initially take $0<u<1$ and put

$$
\begin{aligned}
a&=1-3q,& p&=1-2q,& c&=1-3q-\lambda^2,\\
\gamma&=\lambda(1-\lambda),& B&=a^2-\lambda^2,& x&=uw,\\
d_u&=q+cu,&d_w&=q+cw,&b&=3\lambda q\sqrt{uw}.
\end{aligned}
$$

The second inequality defining $K_3$ implies $p-\lambda^2\ge0$. In particular

$$
d_u=q(1-u)+(p-\lambda^2)u>0,\qquad
d_w=q(1-w)+(p-\lambda^2)w>0.
$$

Write $X=D+Y$, where $D=\mathrm{diag}(z_1,z_2,z_3)$, $z_1+z_2+z_3=0$, and $Y=(y_{ij})$ has zero diagonal. All $z_i$ and $y_{ij}$ are complex. The row decomposition of Theorem 3.2, obtained from Lemma 3.1, specializes to

$$
\begin{aligned}
s^T S(X)s={}&(q+3qau)|z_1|^2+(q+3qaw)|z_2|^2+q|z_3|^2\\
&+2b\,\mathrm{Re}(\bar z_1y_{12}+\bar z_2y_{21})
+d_w|y_{12}|^2+d_u|y_{21}|^2\\
&+q(|y_{13}|^2+|y_{23}|^2)+\eta^\ast P\eta,\\
\eta={}&(y_{31},y_{32})^T,\qquad
P=\begin{pmatrix}d_u&\gamma\sqrt{uw}\\\gamma\sqrt{uw}&d_w\end{pmatrix}.
\end{aligned}
$$

First, $P\ge0$. Its diagonal entries are positive, and

$$
\det P=q(p-\lambda^2)+(c^2-\gamma^2)x
$$

is affine in $x\in[0,1/4]$. At $x=0$ it is nonnegative. At $x=1/4$ it equals

$$
\frac14\bigl(1-q-\lambda^2-\gamma\bigr)
\bigl(1-q-\lambda^2+\gamma\bigr)
=\frac14(1-q-\lambda)(1-q+\lambda-2\lambda^2)\ge0.
$$

The second factor is nonnegative by the fourth inequality defining $K_3$. For the first, $1-q\ge0$ and

$$
(1-q)^2-\lambda^2\ge(1-q)^2-(1-2q)=q^2\ge0,
$$

so $|\lambda|\le1-q$. Affine interpolation proves $\det P\ge0$ for every $x\in[0,1/4]$, including the cases in which $P$ is singular.

Complete the two scalar squares and define

$$
\kappa_1=q+3qau-\frac{b^2}{d_w},\qquad
\kappa_2=q+3qaw-\frac{b^2}{d_u}.
$$

Using the full trace constraint $z_3=-z_1-z_2$ gives the exact identity

$$
\begin{aligned}
s^T S(X)s={}&d_w\left|y_{12}+\frac{b}{d_w}z_1\right|^2
+d_u\left|y_{21}+\frac{b}{d_u}z_2\right|^2\\
&+q(|y_{13}|^2+|y_{23}|^2)+\eta^\ast P\eta
+\begin{pmatrix}z_1\\z_2\end{pmatrix}^{\!\ast}
H(u)\begin{pmatrix}z_1\\z_2\end{pmatrix},\\
H(u)={}&\begin{pmatrix}\kappa_1+q&q\\q&\kappa_2+q\end{pmatrix}.
\end{aligned}
$$

It remains to prove $H(u)\ge0$ on the entire interval $0<u<1$. The identity $ac-3\lambda^2q=B$ gives

$$
\begin{aligned}
d_w(\kappa_1+q)&=q\bigl(2d_w+3aqu+3Bx\bigr),\\
d_u(\kappa_2+q)&=q\bigl(2d_u+3aqw+3Bx\bigr),\\
\det H(u)&=\frac{9q^2}{d_ud_w}
\bigl(Bx+qp\bigr)\bigl(Bx+p-\lambda^2\bigr).
\end{aligned}
$$

For completeness, the last factorization follows by multiplying the first two identities, subtracting $q^2d_ud_w$ and using $u+w=1$:

$$
\bigl(2d_w+3aqu+3Bx\bigr)
\bigl(2d_u+3aqw+3Bx\bigr)-d_ud_w
=9(Bx+qp)(Bx+p-\lambda^2).
$$

Both factors on the right are affine in $x$. Their values at $x=0$ are $qp\ge0$ and $p-\lambda^2\ge0$. At $x=1/4$ they are respectively

$$
\begin{aligned}
\frac B4+qp&=\frac{(1-q)^2-\lambda^2}{4}\ge0,\\
\frac B4+p-\lambda^2&=\frac{(5-9q)(1-q)-5\lambda^2}{4}\ge0.
\end{aligned}
$$

The first uses the second defining inequality of $K_3$, as above, and the second uses its third inequality. Hence $\det H(u)\ge0$ for every $0<u<1$, with no sign assumption on $B$.

To fix the signs of the diagonal entries, at $u=w=1/2$ one has

$$
\kappa_1=\kappa_2
=\frac{q\bigl((5-9q)(1-q)-5\lambda^2\bigr)}{2(1-q-\lambda^2)}\ge0,
\qquad 1-q-\lambda^2\ge q>0.
$$

Thus $H_{11}(1/2)\ge q>0$. For fixed $(\lambda,q)$, $H_{11}(u)$ is continuous on $(0,1)$ and cannot vanish there: a zero would give $\det H(u)=-q^2<0$. The intermediate value theorem therefore implies $H_{11}(u)>0$ throughout $(0,1)$. Since $\det H(u)\ge0$, it follows that $H_{22}(u)\ge q^2/H_{11}(u)>0$ and $H(u)\ge0$. In particular no strictness of the inequalities defining $K_3$ was used; a zero determinant is allowed.

Every term of the completed-square identity is now nonnegative for arbitrary complex variables satisfying $z_1+z_2+z_3=0$. For each fixed traceless $X$, the original scalar $s^T S(X)s$ is continuous in $u\in[0,1]$. Passing to $u=0$ and $u=1$ proves the singleton-probe cases without division by a vanishing $d_u$ or $d_w$. This also covers $q=1/2$, where the second inequality forces $\lambda=0$. Undoing normalization, the permutation, the diagonal unitary and the scalar shift proves the asserted inequality for every complex $X$ and every probe in its stated range.

Finally, Steps 3–5 of Theorem 3.2 apply separately at each fixed $t$. They equate nonnegativity for all traceless complex $X$ with conditions (A) and (B), including the range conditions for singular row blocks. Since $\partial\Delta_3$ is exactly the union of the three edges, the equivalent formulation follows. ∎

**Corollary 8.2 (The remaining full-support criterion).** Put $\Delta_3^\circ=\{t\in\Delta_3:t_1t_2t_3>0\}$. For the family of Theorem 8.1,

$$
\mathcal S_3=
\left\{(\lambda,q)\in K_3:\ \text{conditions (A) and (B) of Theorem 3.2 hold for every }t\in\Delta_3^\circ\right\}.
$$

In particular, if $(\lambda,q)\in K_3$ and $v^\ast S(X)v<0$ for some complex $X$ and $v$, then all three coordinates of $v$ are nonzero. The implication from membership in $K_3$ to the displayed interior conditions is the remaining $d=3$ part of Open question 6.2; no assertion of that implication is made here. Stance: repo-derived.

**Proof.** Theorem 4.1 gives $\mathcal S_3\subseteq K_3$. For parameters in $K_3$, Theorem 8.1 supplies (A) and (B) on $\partial\Delta_3$, and Theorem 3.2 requires them on the union $\Delta_3=\partial\Delta_3\cup\Delta_3^\circ$. This proves the equality. The assertion about a negative probe follows directly from Theorem 8.1. ∎

## 追加锚（本行以下为增补区）
## 9. A sufficient region for unrestricted complex matrices

**Theorem 9.1 (Pair compression and the Schwarz inequality).** For every integer $d\ge3$ and every pair of real numbers $\lambda,q$, put $p=1-(d-1)q$. If

$$
0\le q\le\frac1{d-1},\qquad (d-1)^2\lambda^2\le p,
$$

then the original map

$$
\Phi_{\lambda,q}(X)=\lambda X+(1-dq-\lambda)\operatorname{diag}(X)
+q\operatorname{tr}(X)I_d
$$

satisfies

$$
\forall X\in M_d(\mathbb C)\ \forall v\in\mathbb C^d,\qquad
v^\ast\bigl(\Phi_{\lambda,q}(X^\ast X)
-\Phi_{\lambda,q}(X)^\ast\Phi_{\lambda,q}(X)\bigr)v\ge0.
$$

All inequalities in the hypotheses are weak. In particular $q=0$, $p=0$, $p=1$, equality in $(d-1)^2\lambda^2\le p$, singular defects and probes with zero coordinates are included. In Eq. (6) of Bera, Bhattacharya and Chruściński, arXiv:2604.18600v1, the coordinates are exactly $\alpha=dq$, $\beta=1-dq-\lambda$. This is a sufficient condition for the Schwarz property, without an assumption of complete positivity or $2$-positivity. Stance: repo-derived; the qubit input used below is the cited Proposition 3 of arXiv:2404.10895v1, not a new qubit criterion.

**Proof.** Set $m=d-1$ and $\rho=m\lambda$. The hypotheses give $0\le p\le1$ and $\rho^2\le p$. Consider the unital, Hermiticity-preserving map

$$
T_{p,\rho}\begin{pmatrix}a&b\\c&e\end{pmatrix}
=\begin{pmatrix}pa+(1-p)e&\rho b\\\rho c&(1-p)a+pe\end{pmatrix}
\quad\text{on }M_2(\mathbb C).
$$

The phase-covariant qubit criterion of Chruściński and Bhattacharya, arXiv:2404.10895v1, Proposition 3, Eq. (27), with their $a=b=p$, says that $T_{p,\rho}$ is Schwarz for $\rho^2\le p$. Its special case needed here also has the following direct proof. For a unital Hermiticity-preserving map the defect is unchanged by adding a scalar matrix, as in Lemma 3.1. Multiplication of the input by a scalar $c$ multiplies the defect by $|c|^2$. Thus every qubit input reduces to

$$
A=\begin{pmatrix}f&b\\c&-f\end{pmatrix},\qquad f\in\mathbb R,\quad b,c\in\mathbb C:
$$

subtract half the trace and, if the remaining first diagonal entry is nonzero, multiply by a complex number of modulus one to make it real. At $\rho=\varepsilon\sqrt p$, $\varepsilon\in\{-1,1\}$, multiplication gives

$$
\begin{aligned}
T_{p,\rho}(A^\ast A)-T_{p,\rho}(A)^\ast T_{p,\rho}(A)
&=(1-p)\begin{pmatrix}
4pf^2+|b|^2&2\varepsilon\sqrt p\,f(b-\bar c)\\
2\varepsilon\sqrt p\,f(\bar b-c)&4pf^2+|c|^2
\end{pmatrix},\\
\det\bigl(T_{p,\rho}(A^\ast A)-T_{p,\rho}(A)^\ast T_{p,\rho}(A)\bigr)
&=(1-p)^2|4pf^2+bc|^2.
\end{aligned}
$$

Both diagonal entries and the determinant are nonnegative, so this Hermitian $2\times2$ matrix is positive semidefinite. These formulas also hold at $p=0$ and $p=1$. If $p>0$, every $\rho\in[-\sqrt p,\sqrt p]$ is a convex combination of the two displayed endpoint multipliers. The convexity identity of Remark 4.4, applied on $M_2$, shows that a convex combination of Schwarz maps is Schwarz: its defect is the same convex combination of the two defects plus $\theta(1-\theta)(T_1(A)-T_2(A))^\ast(T_1(A)-T_2(A))$. If $p=0$, the only allowed multiplier is $\rho=0$, already included. Hence $T=T_{p,\rho}$ is Schwarz throughout the required closed region. It is also positive: if $B\ge0$, write $B=A^\ast A$ and use $T(B)\ge T(A)^\ast T(A)\ge0$.

For $i<j$, let $V_{ij}:\mathbb C^2\to\mathbb C^d$ be the coordinate isometry with columns $e_i,e_j$, put $P_{ij}=V_{ij}V_{ij}^\ast$, and define

$$
B_{ij}(X)=V_{ij}\,T(V_{ij}^\ast XV_{ij})\,V_{ij}^\ast.
$$

These maps have output supported on the $\{i,j\}$ coordinate subspace. For every complex $X$, the exact compression identity is

$$
V_{ij}^\ast X^\ast XV_{ij}
-(V_{ij}^\ast XV_{ij})^\ast(V_{ij}^\ast XV_{ij})
=V_{ij}^\ast X^\ast(I_d-P_{ij})XV_{ij}\ge0.
$$

Applying the positive map $T$, followed by its Schwarz inequality on $V_{ij}^\ast XV_{ij}$, and then embedding back, yields

$$
B_{ij}(X^\ast X)\ge B_{ij}(X)^\ast B_{ij}(X).
$$

Define $F(X)=m^{-1}\sum_{i<j}B_{ij}(X)$. Its entries are

$$
[F(X)]_{ii}=pX_{ii}+\frac{1-p}{m}\sum_{j\ne i}X_{jj},\qquad
[F(X)]_{ij}=\frac\rho m X_{ij}\quad(i\ne j).
$$

Since $(1-p)/m=q$ and $\rho/m=\lambda$, these formulas identify $F=\Phi_{\lambda,q}$ on every matrix entry. In particular the source and target algebra is still $M_d(\mathbb C)$.

Fix any $v\in\mathbb C^d$ and abbreviate $w_{ij}=B_{ij}(X)v$, with $w_{ji}=w_{ij}$ when $j<i$. Each coordinate $i$ of the sum $\sum_{i<j}w_{ij}$ receives contributions from exactly the $m$ pairs containing $i$. Complex Cauchy–Schwarz therefore gives

$$
\begin{aligned}
\|F(X)v\|^2
&=\frac1{m^2}\sum_i\left|\sum_{j\ne i}(w_{ij})_i\right|^2\\
&\le\frac1m\sum_i\sum_{j\ne i}|(w_{ij})_i|^2
=\frac1m\sum_{i<j}\|B_{ij}(X)v\|^2.
\end{aligned}
$$

The last equality uses the support of $w_{ij}$ on $\{i,j\}$. Consequently

$$
\begin{aligned}
v^\ast F(X^\ast X)v
&=\frac1m\sum_{i<j}v^\ast B_{ij}(X^\ast X)v\\
&\ge\frac1m\sum_{i<j}\|B_{ij}(X)v\|^2
\ge\|F(X)v\|^2.
\end{aligned}
$$

This holds for every complex $X$ and $v$. There is no division by $p$, $q$, a coordinate of $v$, or an eigenvalue of a defect. Thus all zero, singular and equality cases in the statement follow from the same argument. ∎

## 10. Square-root sections and the actual Schwarz set

**Theorem 10.1 (Local failure of a finite affine description).** Fix any integer $d\ge3$, and let $\mathcal S_d$ denote the actual Schwarz parameter set of the original map of Convention 2.1. Use the affine coordinates $(\lambda,p)$, $p=1-(d-1)q$, and write

$$
\widehat{\mathcal S}_d
=\{(\lambda,p):(\lambda,(1-p)/(d-1))\in\mathcal S_d\}.
$$

For every $0\le p\le1$ one has

$$
\left[-\frac{\sqrt p}{d-1},\frac{\sqrt p}{d-1}\right]
\subseteq\{\lambda:(\lambda,p)\in\widehat{\mathcal S}_d\}
\subseteq[-\sqrt p,\sqrt p].
$$

For no open neighborhood $U$ of $(0,1/(d-1))$ in the original $(\lambda,q)$ plane do there exist finitely many closed affine half-planes $H_1,\ldots,H_N$ such that

$$
\mathcal S_d\cap U=U\cap\bigcap_{j=1}^NH_j.
$$

The same assertion holds at $(0,0)$ in $(\lambda,p)$ coordinates. The displayed inclusions demonstrate square-root order of the two signed section widths; they do not determine their optimal coefficient or a finite nonlinear description of $\mathcal S_d$. Stance: repo-derived; the necessary inequality in the second inclusion is Theorem 4.1(ii), also literature-attested as specified there.

**Proof.** The first inclusion is Theorem 9.1. The second follows from the established necessary condition $\lambda^2\le p$, obtained with $X=E_{12}$ and probe $e_2$. In particular $\widehat{\mathcal S}_d\cap\{p=0\}=\{(0,0)\}$. For every $r\in[0,1]$, the first inclusion supplies both points

$$
z_+(r)=\left(\frac r{d-1},r^2\right),\qquad
z_-(r)=\left(-\frac r{d-1},r^2\right).
$$

Suppose there were such a finite half-plane representation in an open neighborhood $W$ of $(0,0)$. Orient each half-plane as $a_j\lambda+b_jp\ge c_j$. Because the origin belongs to the represented set, $c_j\le0$. If $c_j<0$, its inequality holds strictly throughout some ball about the origin. The finitely many such inequalities therefore impose no restriction in a sufficiently small common ball contained in $W$.

For an active inequality $c_j=0$, both $z_+(r)$ and $z_-(r)$ belong to $W$ for all sufficiently small positive $r$. Hence

$$
\frac{a_j}{d-1}+b_jr\ge0,\qquad
-\frac{a_j}{d-1}+b_jr\ge0.
$$

Taking $r\downarrow0$ shows $a_j=0$, and the inequalities then imply $b_j\ge0$. Every active half-plane thus contains the whole line $p=0$. Choose a nonzero $\lambda$ sufficiently small that $(\lambda,0)$ is in the common ball. It satisfies every inactive inequality strictly and every active inequality weakly, so the assumed representation puts it in $\widehat{\mathcal S}_d$. This contradicts $\lambda^2\le p=0$.

The transformation $(\lambda,q)\mapsto(\lambda,1-(d-1)q)$ is an invertible affine map; it takes open neighborhoods to open neighborhoods and closed affine half-planes to closed affine half-planes. Thus the contradiction proves the assertion in both coordinate systems. Only the necessary upper bound and the two included curves were used. In particular no assertion $\mathcal S_d=K_d$, no exclusion of semialgebraic descriptions, and no optimal cusp coefficient is part of this conclusion. ∎

## 11. Comparison with specified sufficient constructions

**Definition 11.1 (Coordinates and a fixed supplier class).** In this section $m=d-1$, $d\ge3$, and all displayed parameter pairs are $(\lambda,p)$ pairs, with $q=(1-p)/m$. Let

$$
\begin{aligned}
\widehat{\mathcal T}_d
&=\{(\lambda,p):0\le p\le1,\ -p/m\le\lambda\le p\},\\
\mathcal D_d
&=\{(t,(1+mt)/d):-1/d\le t\le1\},\\
G_d&=\left(\frac1{dm},\frac1{d^2}\right),\\
\mathcal H_d&=\operatorname{conv}\bigl(\widehat{\mathcal T}_d\cup\mathcal D_d\cup\{G_d\}\bigr).
\end{aligned}
$$

Here $\widehat{\mathcal T}_d$ is the known completely positive triangle (Remark 4.4 and arXiv:2604.18600v1, Proposition 2.1(2)); $\mathcal D_d$ is the exact Schwarz interval for the depolarizing maps $X\mapsto tX+(1-t)\operatorname{tr}(X)I_d/d$; and $G_d$ is the generalized-reduction supplier specified in the proof below. The exact $q=0$ Schwarz interval remains $-1/m\le\lambda\le1$ by Proposition 4.2. The existing $k$-positive characterization, for each $2\le k\le d$, is the quadrilateral of arXiv:2604.18600v1, Conjecture 2.4, proved in the repository's [k-positive-region result](../../../Blueprint/D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.md). In these coordinates it reads

$$
0\le p\le1,\qquad
\max\left\{-\frac p{k-1},-\frac{d-k+d(k-1)p}{km^2}\right\}\le\lambda\le p.
$$

These known regions, and every valid convex combination of their Schwarz members, are retained as sufficient regions independently of Theorem 9.1. The class $\mathcal H_d$ is precisely the convex hull displayed above; it does not mean the class of all known Schwarz constructions or all possible generalized reductions. The cited depolarizing and reduction facts are used only as intermediate suppliers in the following comparison.

**Proposition 11.2 (Curves, positivity separation and scoped comparison).** Write $z_\pm(r)=(\pm r/m,r^2)$. For every $0<r<1$, both points belong to $\widehat{\mathcal S}_d$. Moreover:

- $z_+(r)$ is not $2$-positive for $0<r<1/m$;
- $z_-(r)$ is not $2$-positive for $(d-2)/d<r<1$;
- for $0<r\le1$, $z_+(r)\in\mathcal H_d$ if and only if $r\ge1/d$;
- the entire interval $(d-2)/d<r<1$ of the negative curve is already contained in $\operatorname{conv}(\widehat{\mathcal T}_d\cup\mathcal D_d)$.

Thus the stated negative continuum and the positive continuum for $r\ge1/d$ are supplied by the cited constructions and their convex combinations. They are not additional independent content beyond those suppliers. The strict comparison at $0<r<1/d$ is only with the explicitly defined class $\mathcal H_d$.

**Proof.** Membership of both curves follows from Theorem 9.1, since $m^2\lambda^2=r^2=p$. For clarity, the classical suppliers in Definition 11.1 can be justified without the invalid intervals discussed in §12. Let $\Psi$ be a unital, trace-preserving positive map which contracts the Hilbert–Schmidt norm, and put

$$
R_{a,\Psi}(X)=\frac{\operatorname{tr}(X)I_d-a\Psi(X)}{d-a},
\qquad 0\le a\le\frac d{d+1}.
$$

This is the $k=1$ sufficient construction of Mukhamedov and Chruściński, arXiv:2603.11204v1, Theorem 3.2, Eqs. (2.8), (3.2)–(3.3), where their $\Delta$ is $\operatorname{tr}(X)I_d/d$. For $k=1$ their condition (2.8) is precisely Hilbert–Schmidt contraction. An elementary proof in this range is as follows. For a traceless complex $X$, define

$$
Z=a(d-a)\Psi(X^\ast X)+a^2\Psi(X)^\ast\Psi(X)\ge0.
$$

Trace preservation and contraction give $\operatorname{tr}Z\le ad\|X\|_F^2$. Since every positive matrix satisfies $Z\le\operatorname{tr}(Z)I_d$, one obtains

$$
\begin{aligned}
(d-a)^2\bigl(R_{a,\Psi}(X^\ast X)-R_{a,\Psi}(X)^\ast R_{a,\Psi}(X)\bigr)
&=(d-a)\|X\|_F^2I_d-Z\\
&\ge\bigl(d-(d+1)a\bigr)\|X\|_F^2I_d\ge0.
\end{aligned}
$$

Unitality and Hermiticity preservation give scalar-shift invariance of the defect, so the same conclusion holds for every complex input. This proves the stated supplier range including both endpoints.

Taking $\Psi=\operatorname{id}$ supplies the depolarizing interval $-1/d\le t\le0$, with $t=-a/(d-a)$. The interval $0\le t\le1$ is completely positive. Conversely Theorem 4.1(ii) on the depolarizing line gives

$$
dt^2\le1+mt\quad\Longleftrightarrow\quad (t-1)(dt+1)\le0,
$$

so $-1/d\le t\le1$ is exact. This agrees with the Tomiyama identity-map case cited in arXiv:2603.11204v1, Remark 3.3; no larger printed interval is used.

For $G_d$, take the completely positive, unital and trace-preserving Schur map

$$
\Psi(X)=-\frac1mX+\frac d m\operatorname{diag}(X).
$$

Its complete positivity is the $q=0$ endpoint of Proposition 4.2. Choi's Schwarz inequality and trace preservation give its Hilbert–Schmidt contraction. At $a=d/(d+1)$ the preceding reduction is exactly

$$
R_{a,\Psi}(X)=\frac1{dm}X-\frac1m\operatorname{diag}(X)
+\frac{d+1}{d^2}\operatorname{tr}(X)I_d,
$$

whose parameters are $G_d$. Thus the CP triangle, the depolarizing interval and this generalized reduction are valid Schwarz suppliers. Convexity is Remark 4.4.

The non-$2$-positive assertions can be read from the existing quadrilateral. Their underlying witnesses also identify the exact strict intervals. Its standard quadratic form is

$$
Q(A)=q\|A\|_F^2+(1-dq-\lambda)\sum_i|A_{ii}|^2
+\lambda|\operatorname{tr}A|^2;
$$

$2$-positivity requires $Q(A)\ge0$ for every matrix of rank at most two, as in the cited quadrilateral proof. The rank-two matrix $E_{11}-E_{22}$ gives $Q=2(p-\lambda)$. At $z_+(r)$ this is $2r(r-1/m)<0$ exactly on the stated positive interval. For the negative curve let $A$ be the rank-two orthogonal projection onto two columns of the normalized discrete Fourier matrix. Then $\operatorname{tr}A=\|A\|_F^2=2$ and every diagonal entry is $2/d$. Thus

$$
Q(A)=\frac2{dm}\bigl(d-2+dp+2m^2\lambda\bigr).
$$

At $z_-(r)$ the expression in parentheses is

$$
dr^2-2mr+d-2=d(r-1)\left(r-\frac{d-2}{d}\right)<0
$$

for $(d-2)/d<r<1$. These are witnesses for failure of $2$-positivity, not witnesses against the Schwarz conclusion. No non-$2$-positive assertion at the endpoints of either stated open interval is inferred.

To compare the positive curve with $\mathcal H_d$, every generating point of $\mathcal H_d$ has $p\ge0$ and satisfies

$$
\lambda\le\frac d m p.
$$

For the CP triangle this follows from $\lambda\le p$; on the depolarizing interval it is equivalent to $mt\le1+mt$; and it is an equality at $G_d$. The inequality survives convex combinations. At $z_+(r)$ it requires $r\ge1/d$, so $0<r<1/d$ lies outside this particular supplier hull.

Conversely, for $1/d\le r\le1$, put

$$
\theta=\frac{d^2(1-r^2)}{d^2-1},\qquad
c=\frac{r+d}{m(dr+1)}.
$$

Here $0\le\theta\le1$ and $0<c\le1$: indeed

$$
m(dr+1)-(r+d)=(d^2-d-1)r-1\ge\frac{d^2-d-1}{d}-1\ge0
$$

for $d\ge3$. Therefore $(c,1)$ is a completely positive $q=0$ parameter. Direct substitution gives the exact convex decomposition

$$
z_+(r)=\theta G_d+(1-\theta)(c,1).
$$

It is valid also at $r=1/d$, when $\theta=1$. This proves the asserted threshold for the declared hull.

Finally let $N_d=(-1/d,1/d^2)\in\mathcal D_d$, $C_d=(0,0)\in\widehat{\mathcal T}_d$, and $B_d=(-1/m,1)\in\widehat{\mathcal T}_d$. For $0\le r\le1$, the polygon $\operatorname{conv}\{C_d,N_d,B_d\}$ contains the point $(-r/m,L(r))$, where

$$
L(r)=\begin{cases}
r/(dm),&0\le r\le m/d,\\
\bigl((d^2-1)r-(d^2-d-1)\bigr)/d,&m/d\le r\le1.
\end{cases}
$$

The first point lies on $C_dN_d$, with weight $dr/m$ at $N_d$; the second lies on $N_dB_d$, obtained by linear interpolation at the specified first coordinate. The point $(-r/m,1)$ is in the CP triangle for every $r\in[0,1]$. If $r>(d-2)/d$ and $r\le m/d$, then $r\ge1/(dm)$ and hence $r^2\ge L(r)$. If $r\ge m/d$, then

$$
r^2-L(r)=(1-r)\left(\frac{d^2-d-1}{d}-r\right)\ge0,
$$

since $(d^2-d-1)/d>1$. In both cases $L(r)\le r^2\le1$, so interpolation between these two points at the same first coordinate puts $z_-(r)$ in $\operatorname{conv}(\widehat{\mathcal T}_d\cup\mathcal D_d)$. This accounts for the whole stated negative continuum using the existing suppliers. ∎

## 12. Limits of the cited criteria and the remaining implication

**Convention 12.1 (Scope of external inputs).** The family and its Schwarz question are Eq. (6) and §4 of Bera, Bhattacharya and Chruściński, arXiv:2604.18600v1. The exact qubit criterion used as an intermediate step of Theorem 9.1 is Chruściński and Bhattacharya, arXiv:2404.10895v1, Proposition 3, Eq. (27), specialized to $a=b=p$, $\mu=0$ and real off-diagonal multiplier $\rho$. Theorem 9.1 combines that criterion with pair compressions and the coordinatewise Cauchy–Schwarz estimate; Theorem 10.1 applies its two signed curves to the actual Schwarz set. Neither statement asserts priority or worldwide absence of another proof. Tomiyama, *On the geometry of positive maps in matrix algebras. II*, Linear Algebra Appl. 69, 169–177, DOI 10.1016/0024-3795(85)90074-6, and Sun and Li, *k Positivity and Schwarz inequality for two linear maps*, Positivity 26, 16, DOI 10.1007/s11117-022-00863-8, are cited through the exact accessible results identified above. Overlap with their unavailable original full texts is not determined.

The generalized-reduction range in §11 uses only the hypotheses and $k=1$ range of arXiv:2603.11204v1, Theorem 3.2, with the proof given there inline. Its Theorem 3.4 cannot supply its whole printed interval (3.10). In fact, take $d=3$, $k=1$, the identity as its input map and $a=3/2$. The identity is unital, trace-preserving, positive and satisfies its condition (2.8); moreover

$$
1-\frac{\sqrt{13}-1}{6}\le\frac32\le1+\frac{\sqrt{13}+1}{6}.
$$

Nevertheless its construction (3.9) is

$$
\Omega(X)=\frac12\bigl(\operatorname{tr}(X)I_3-X\bigr)
=\Phi_{-1/2,\,1/2}(X),
$$

and the existing matrix-unit necessary test of Theorem 4.1 gives

$$
e_2^\ast\bigl(\Omega(E_{12}^\ast E_{12})
-\Omega(E_{12})^\ast\Omega(E_{12})\bigr)e_2=-\frac14.
$$

This source limitation also prevents using a negative depolarizing interval larger than the exact interval in Definition 11.1.

For Rutkowski, arXiv:2512.18900v3, Theorem 1, the general diagonal Gell–Mann hypothesis does contain the $d=3$ original family: its six off-diagonal eigenvalues are $\lambda$ and its two diagonal traceless eigenvalues are $1-3q$. The displayed illustrative family (19), with seven equal eigenvalues and one distinct one, intersects this permutation-symmetric family on $\lambda=1-3q$; that intersection alone does not describe the scope of its general theorem. Its whole printed sufficient criterion is not used here. Indeed, the same $\Omega$ is a positive unital map: for $X\ge0$, $\operatorname{tr}(X)I_3-X\ge0$. It has isotropic Gell–Mann eigenvalues $\mu_i=-1/2$ and hence zero spectral spread. Under the definition (14), $c_3(\mu)=0$: the scalar coefficient of the defect is one third of its trace, is nonnegative by the Hilbert–Schmidt contraction of $\Omega$, and vanishes on $X=I_3$. Thus its printed condition (15) is met, while the displayed matrix-unit defect is negative. This excludes that full printed criterion as a supplier, without making any statement about other corrected estimates. Since $p=0$ and $\lambda=-1/2$, this example is outside $K_3$ and cannot refute the sufficiency of $K_3$.

For García-Velo and Ibort, arXiv:2601.02282v1, only the necessary tests of Theorem V.4 are used, as in Theorem 4.1. Their Proposition V.4 is not a Schwarz or CP supplier here. The identity and the parameter $(\lambda,q)=(-1/2,1/4)$ in the existing Remark 5.1 already refute the two directions of its printed Schwarz criterion; those counterexamples and the complete boundary theorem 8.1 are reused in their entirety. These are limitations of the specified source statements, not independent additional refutations or new classification claims.

**Question 12.2 (The unsupplied full classification).** For every $d\ge3$, does $K_d\subseteq\mathcal S_d$ hold? Since Theorem 4.1 gives the converse inclusion, a negative answer requires a parameter in $K_d$ and genuine complex $X\in M_d(\mathbb C)$, $v\in\mathbb C^d$ with $v^\ast S(X)v<0$. Theorem 9.1 supplies a subset of $\mathcal S_d$ and leaves this implication unresolved. Its complement is not declared pointwise unknown: the CP, exact $q=0$, exact depolarizing, $2$-positive and other valid sufficient constructions in §11 and their convex combinations remain available.

For $d=3$, Theorem 8.1 already supplies all boundary points of the probe simplex. By Corollary 8.2 the remaining condition is exactly that (A) and (B) of Theorem 3.2 hold for every full-support $t\in\Delta_3^\circ$, with their singular-block range conditions, zero coefficients and equality cases unchanged. Theorem 10.1 excludes a finite affine half-plane description near the cusp; it neither settles this full-support condition nor excludes a finite nonlinear or semialgebraic description. The separate Schwarz classification of the transposition family $\Lambda_{\mu,\nu}$ in arXiv:2604.18600v1 is also unresolved here.

## 追加锚（本行以下为增补区）

## 13. The closed small-multiplier strip

**Lemma 13.1 (a denominator-free identity on the parabolic boundary).** Fix $d\ge3$, $m=d-1$, $|\lambda|\le1/d$, and put

$$
q_b=\frac{1-\lambda^2}{m},\qquad k=d\lambda,\qquad
\delta=1-k^2,\qquad h=\frac{m\lambda}{1+\lambda}.
$$

For $t\in\Delta_d$, write $s_j=\sqrt{t_j}$ and let $X=D+Y$ be an arbitrary complex traceless matrix, with $D=\operatorname{diag}(z_1,\ldots,z_d)$ and $Y=(y_{ij})$ of zero diagonal. For the original map at $(\lambda,q_b)$, the following exact identity holds:

$$
\begin{aligned}
\frac{s^T S_b(X)s}{q_b}
={}&\frac{\delta}{m}\sum_a t_a
 \sum_{\substack{i<j\\i,j\ne a}}|z_i-z_j|^2
 +\sum_i\sum_{j\ne i}|\sqrt{t_i}y_{ij}+k\sqrt{t_j}z_i|^2\\
&+\frac12\sum_i\sum_{\substack{j<\ell\\j,\ell\ne i}}
 \left((1+h)|\sqrt{t_\ell}y_{ij}+\sqrt{t_j}y_{i\ell}|^2
 +(1-h)|\sqrt{t_\ell}y_{ij}-\sqrt{t_j}y_{i\ell}|^2\right).
\end{aligned}
\tag{13.1}
$$

Every coefficient on the right is nonnegative. The identity includes every face of the simplex and both signs and endpoints of $\lambda$. Stance: repo-derived.

**Proof.** Here $q_b>0$, $1+\lambda\ge1-1/d>0$, $\delta\ge0$, and

$$
-1\le h\le\frac{d-1}{d+1}<1.
$$

The last bound follows either by cross multiplication with $1+\lambda>0$ or from the positive derivative $m/(1+\lambda)^2$. Put $a=1-dq_b$. Since $p=\lambda^2$, one has

$$
a-\lambda^2=-q_b,\qquad
\frac{\lambda(1-\lambda)}{q_b}=h,\qquad
d a=-k^2-\frac{d\delta}{m}.
$$

The row identity in Step 3 of Theorem 3.2 therefore gives the following coefficients in $s^TS_b(X)s/q_b$: the coefficient of $|z_i|^2$ is $1+da\,t_i$; the coefficient of $|y_{ij}|^2$ is $1-t_j$; the mixed diagonal-row term is $2k\sqrt{t_it_j}\operatorname{Re}(\bar z_i y_{ij})$; and the mixed terms within row $i$ are $2h\sqrt{t_jt_\ell}\operatorname{Re}(\bar y_{ij}y_{i\ell})$.

To verify (13.1), first use the full complex trace constraint:

$$
\begin{aligned}
\sum_{\substack{i<j\\i,j\ne a}}|z_i-z_j|^2
 &=m\sum_{i\ne a}|z_i|^2-\left|\sum_{i\ne a}z_i\right|^2
 =m\sum_i|z_i|^2-d|z_a|^2,\\
\frac1m\sum_a t_a\sum_{\substack{i<j\\i,j\ne a}}|z_i-z_j|^2
 &=\sum_i\left(1-\frac d m t_i\right)|z_i|^2.
\end{aligned}
$$

Consequently the first two sums in (13.1) have $|z_i|^2$ coefficient

$$
\delta\left(1-\frac d m t_i\right)+k^2(1-t_i)
=1+da\,t_i.
$$

For each $y_{ij}$ the second sum contributes $t_i|y_{ij}|^2$ and the last sum contributes $\sum_{\ell\ne i,j}t_\ell|y_{ij}|^2$, whose sum is $(1-t_j)|y_{ij}|^2$. Expanding each plus/minus pair in the last sum gives exactly the mixed coefficient $2h\sqrt{t_jt_\ell}$ above, and the second sum gives exactly $2k\sqrt{t_it_j}$. These exhaust all monomials of the row identity. Thus (13.1) is an identity on the original complex row variables, with no eliminated variable or suppressed multiplier. ∎

**Theorem 13.2 (exact closed strip in every dimension).** For every integer $d\ge3$ and all real $\lambda,q$ with $|\lambda|\le1/d$, the original map of Convention 2.1 is Schwarz if and only if

$$
0\le q\le\frac{1-\lambda^2}{d-1}.
$$

The assertion is for every $X\in M_d(\mathbb C)$ and every $v\in\mathbb C^d$, including singular row blocks, zero-support coordinates and all closed endpoints. Stance: repo-derived.

**Proof.** Necessity is Theorem 4.1(i),(ii). For sufficiency, the upper boundary $q=q_b$ is Lemma 13.1. The lower boundary $q=0$ is Proposition 4.2, since $[-1/d,1/d]\subset[-1/(d-1),1]$. For $0\le q\le q_b$ put $\theta=q/q_b$. The original maps satisfy

$$
\Phi_{\lambda,q}=(1-\theta)\Phi_{\lambda,0}+\theta\Phi_{\lambda,q_b}.
$$

The exact convexity identity in Remark 4.4, evaluated on a traceless $X=D+Y$ and the normalized probe $s$, is

$$
s^TS_q(X)s=(1-\theta)s^TS_0(X)s+\theta s^TS_b(X)s
 +\theta(1-\theta)d^2q_b^2\sum_i t_i|z_i|^2.
\tag{13.2}
$$

Indeed $(\Phi_{\lambda,q_b}-\Phi_{\lambda,0})(X)=-dq_bD$. All three terms are nonnegative, including when $\theta$ is zero or one. Scalar-shift invariance and diagonal-unitary covariance, proved in Lemma 3.1 and Theorem 3.2, transfer these identities to arbitrary complex inputs and probes; the zero probe has defect zero.

This argument also proves the row range claims directly, without any inverse or limiting convention. At any fixed admissible $(\lambda,q,t)$, set $z=0$ and vary one row of $Y$: nonnegativity forces $P_i\ge0$. If a real $w\in\ker P_i$ had $b_i^Tw\ne0$, choose $z_i=1$, $z_j=-1$ for one $j\ne i$, all other diagonal entries zero, and vary that row as $\eta_i=\tau w$. Its contribution has the nonconstant linear term $2\tau b_i^Tw$ and zero quadratic term in $\tau$; all other contributions are fixed. One choice of sign as $|\tau|\to\infty$ contradicts (13.2). Hence $b_i\perp\ker P_i$, equivalently $b_i\in\operatorname{Ran}P_i$, at every singular point as well. Its Moore–Penrose quadratic value is therefore finite. Completing squares exactly as in Step 4 of Theorem 3.2, and minimizing the independent rows, gives the nonnegative restricted form $\sum_i\kappa_i|z_i|^2$ and thus condition (B), with its zero-coefficient cases. No expression $c_i/(1+\gamma c_i)$ is used, so zeros of $e_j$ and of $1+\gamma c_i$, and their intersections, require no denominator cancellation. ∎

**Proposition 13.3 (equality in the strip).** Use the normalized, phase-removed, traceless variables of Lemma 13.1. At $q=q_b$, equality holds if and only if every term on the right of (13.1) with positive coefficient vanishes. Explicitly these conditions are

$$
\begin{gathered}
\delta t_a>0\ \Longrightarrow\ z_i=z_j\quad(i,j\ne a),\\
\sqrt{t_i}y_{ij}+k\sqrt{t_j}z_i=0\quad(i\ne j),\\
(1+h)>0\ \Longrightarrow\ \sqrt{t_\ell}y_{ij}+\sqrt{t_j}y_{i\ell}=0,\\
(1-h)>0\ \Longrightarrow\ \sqrt{t_\ell}y_{ij}-\sqrt{t_j}y_{i\ell}=0
\quad(j<\ell,\ j,\ell\ne i).
\end{gathered}
$$

Zero coefficients impose no condition. At $q=0$, equality holds exactly when $y_{ij}s_j=0$ for all $i\ne j$. For $0<q<q_b$ and a nonzero probe, equality holds exactly when the original input is a scalar matrix. In particular all equality assertions concern the original defect, not a quotient by a singular block. Stance: repo-derived.

**Proof.** The first assertion is the equality criterion for a finite sum of nonnegative squared complex moduli. On $q=0$, Proposition 4.2 gives

$$
s^TS_0(X)s=(1-\lambda)\left(\lambda\|Ys\|^2+\sum_{i\ne j}|y_{ij}s_j|^2\right).
$$

For $\lambda\ge0$ its equality criterion is immediate. For $\lambda<0$, $\|Ys\|^2\le m\sum_{i\ne j}|y_{ij}s_j|^2$ and $1+m\lambda\ge1/d>0$ give the same criterion. If $0<\theta<1$, equality in (13.2) implies both this criterion and $z_is_i=0$ for every $i$. In Lemma 3.1 all terms other than $q_b\|X\|^2I$ then vanish after evaluation on $s$: $Ds=Ys=0$ and $\sum_{i\ne j}t_j|y_{ij}|^2=0$. Thus $s^TS_b(X)s=q_b\|X\|^2$, so the traceless input is zero. Scalar inputs do have zero defect.

At $\lambda=-1/d$, $q_b=(d+1)/d^2$, the row matrix in (13.1), ordered as $(z_i,(y_{ij})_{j\ne i})$, is $q_b(I-ss^T)$ with the corresponding coordinate order. If $t_i>0$, its lower block $q_b(I-\sigma\sigma^T)$ is positive definite; if $t_i=0$, its kernel is $\operatorname{span}\{\sigma\}$ and $b_i=0$. At $d=3$, $t=(1/3,1/3,1/3)$, minimizing a row gives $y_{ij}=z_i$ and $\kappa_i=0$, so the restricted diagonal form is exactly zero, as is (13.1) at those minimizing rows. For any $d$ the same projection description gives the equivalent endpoint equality condition $X=cI+a v^\ast$ with $v^\ast a=0$ for a nonzero original probe $v$. This also includes every zero coordinate of $v$. ∎

## 14. The dimension-three negative cap arc

**Theorem 14.1 (closed negative cap arc).** For every $1/3\le r\le1/2$, the original map on $M_3(\mathbb C)$ with

$$
\lambda=-r,\qquad q=(1+r)(1-2r)
$$

is Schwarz for every complex input and every complex probe. Stance: repo-derived.

**Proof.** Set $L=1+r$, $u=1-2r$, $v=3r-1$. The endpoints $r=1/3$ and $r=1/2$ are respectively Theorem 13.2 and Proposition 4.2. Assume for now $1/3<r<1/2$, so $u,v>0$ and $r-v=u$. The parameter lies in the original $K_3$ because

$$
\begin{gathered}
0<q\le4/9<1/2,\qquad p-r^2=L v>0,\qquad 1-q-r-2r^2=0,\\
(5-9q)(1-q)-5r^2=4r(r+1)(3r-1)(3r+1)>0.
\end{gathered}
\tag{14.1}
$$

Here $4/9-q=(r-1/3)(2r+5/3)$. Theorem 8.1 supplies the whole probe-simplex boundary, with its singular-block range conditions. It remains to prove the original row criterion at every full-support $t=(x,y,z)$.

For row $i$, denote its weight by $x$ and the other two weights by $y,z$. In this paragraph the notation is cyclically permuted for the other rows. With $a=1-3q$, the original quantities are

$$
\begin{aligned}
P_i&=L\begin{pmatrix}u+(5r-2)y&-r\sqrt{yz}\\-r\sqrt{yz}&u+(5r-2)z\end{pmatrix},\\
b_i&=-3rLu\sqrt{x}\,(\sqrt y,\sqrt z)^T,\qquad
A_i=q(1+3ax).
\end{aligned}
$$

Both diagonal entries of $P_i/L$ are positive: the affine function $u+(5r-2)y$ has the positive endpoint values $u$ and $v$. Define

$$
D_i=x(r-vx)+v(y-z)^2.
$$

Its first summand is positive since $x>0$ and $r-vx\ge r-v=u>0$. Multiplying the two diagonal entries and subtracting $r^2yz$, using $y+z=1-x$ and $r=u+v$, gives the exact determinant

$$
\det P_i=L^2uD_i>0.
\tag{14.2}
$$

Thus every row block is positive definite and its inverse is legitimate. Its adjugate has

$$
(\sqrt y,\sqrt z)\operatorname{adj}(P_i/L)(\sqrt y,\sqrt z)^T
=u(1-x)+4v yz.
$$

Consequently

$$
\begin{aligned}
\frac{\kappa_i}{q}
&=1+3ax-\frac{9r^2x\bigl(u(1-x)+4v yz\bigr)}{D_i}
=v\frac{N_i}{D_i},\\
N_i&=\bigl((9r+6)x-(3r+1)\bigr)D_i+9r^2(y-z)^2.
\end{aligned}
\tag{14.3}
$$

For example, this last identity follows by writing $4yz=(1-x)^2-(y-z)^2$ and $a=6r^2+3r-2$: the coefficients of $(y-z)^2$ on the two sides after multiplication by $D_i$ are both $v\bigl(1+(27r^2+9r-6)x\bigr)$; the remaining part on both sides is $v x(r-vx)\bigl((9r+6)x-(3r+1)\bigr)$.

Here is a complete polynomial certificate for the determinant of the trace-zero form. Write

$$
E=xy+xz+yz,\qquad T=xyz,\qquad C=3r^2+r,
$$

and define

$$
\begin{aligned}
f&=f_0+f_1E+f_2T,\\
f_0&=(1-2r)(4r^2+2r-1),\qquad
f_1=4(9r^3-4r+1),\qquad f_2=-4v^2(3r+2),\\
g&=(4E-1)\bigl(1+4(C-1)E\bigr)
 +4T\bigl((8-12C)E+C-2\bigr).
\end{aligned}
$$

Then

$$
N_1N_2D_3+N_1N_3D_2+N_2N_3D_1=-9fg.
\tag{14.4}
$$

To verify the certificate without an unspecified elimination, use $x^3=x^2-Ex+T$ and its two cyclic counterparts. The three $D_i$ and $N_i$ are respectively the values, at $x,y,z$, of the following two quadratic polynomials:

$$
\begin{array}{c|ccc}
 &1&\xi&\xi^2\\ \hline
D(\xi)&d_0=v(1-4E)&d_1=7r-2&d_2=-4v\\
N(\xi)&n_0=1-4E-12v(3r+2)T&n_1=4(6r^2+2r-1)&n_2=-4v(3r+2).
\end{array}
\tag{14.5}
$$

Indeed $(y-z)^2=1-4E+2x-3x^2$ gives the $D$ row; inserting it in (14.3) and replacing the cubic term by $x^2-Ex+T$ gives the $N$ row. For any three coefficients $A,B,H$, multiplying one term from each of the three factors gives

$$
\begin{aligned}
\mathcal N(A,B,H)
:=\prod_{\xi\in\{x,y,z\}}(A+B\xi+H\xi^2)
={}&A^3+A^2B+A^2H(1-2E)+AB^2E+ABH(E-3T)\\
&+AH^2(E^2-2T)+B^3T+B^2HT+BH^2ET+H^3T^2.
\end{aligned}
\tag{14.6}
$$

The mixed sums used here are $\sum x^2=1-2E$, $\sum_{i\ne j}x_i^2x_j=E-3T$, and $\sum_{i<j}x_i^2x_j^2=E^2-2T$; the other terms use $x+y+z=1$ and $xyz=T$. Thus the left side of (14.4) is precisely the coefficient of $\tau^2$ in $\mathcal N(d_0+\tau n_0,d_1+\tau n_1,d_2+\tau n_2)$. Explicitly that coefficient is

$$
\begin{aligned}
&3d_0n_0^2+(d_1n_0^2+2d_0n_0n_1)
 +(d_2n_0^2+2d_0n_0n_2)(1-2E)\\
&+(d_0n_1^2+2n_0d_1n_1)E
 +(n_0n_1d_2+n_0d_1n_2+d_0n_1n_2)(E-3T)\\
&+(d_0n_2^2+2n_0d_2n_2)(E^2-2T)
 +3d_1n_1^2T+(d_2n_1^2+2d_1n_1n_2)T\\
&+(d_1n_2^2+2n_1d_2n_2)ET+3d_2n_2^2T^2.
\end{aligned}
\tag{14.7}
$$

For clarity, all coefficients after substituting (14.5) into (14.7) and dividing by $-9$ are given below. Put $g_1=8-4C$, $g_2=16(C-1)$, $g_3=4(C-2)$, $g_4=32-48C$, so $g=-1+g_1E+g_2E^2+g_3T+g_4ET$.

| Monomial | Coefficient of (14.7) divided by $-9$ |
| --- | --- |
| $1$ | $-f_0$ |
| $E$ | $f_0g_1-f_1$ |
| $E^2$ | $f_0g_2+f_1g_1$ |
| $E^3$ | $f_1g_2$ |
| $T$ | $f_0g_3-f_2$ |
| $ET$ | $f_0g_4+f_1g_3+f_2g_1$ |
| $E^2T$ | $f_1g_4+f_2g_2$ |
| $T^2$ | $f_2g_3$ |
| $ET^2$ | $f_2g_4$ |

All other coefficients are zero. This is the coefficient list of $(f_0+f_1E+f_2T)(-1+g_1E+g_2E^2+g_3T+g_4ET)$, proving (14.4). In particular its multiplier and all variables are specified; no pivot or clearing factor is implicit.

We next prove the signs of the two factors for every full-support simplex point. Since $0<E\le1/3$ and

$$
\frac E T=\frac1x+\frac1y+\frac1z\ge9,
$$

one has $T\le E/9$. Here $f_2<0$, and

$$
f\ge f_0+(f_1+f_2/9)E
\ge\min\left\{f_0,\ f_0+\frac{f_1+f_2/9}{3}\right\}
=\min\{f_0,1/27\}>0.
\tag{14.8}
$$

The last strict sign follows from $u>0$ and $4r^2+2r-1\ge1/9$ for $r\ge1/3$.

For $g$, $2/3<C<5/4$, and its coefficient of $T$ is strictly negative:

$$
4\bigl((8-12C)E+C-2\bigr)<0.
$$

If $E\le1/4$, the factor $1+4(C-1)E$ is positive (it is at least $1-4E/3$), while $4E-1\le0$ and $T>0$. Hence $g<0$.

If $1/4<E\le1/3$, the minimum of $T$ at fixed $E$ is attained at $(1-2b,b,b)$ up to permutation, where

$$
b=\frac{1+\sqrt{1-3E}}3\in[1/3,1/2).
$$

Here is the justification of this minimization. The fixed-$E$ subset of the closed simplex is compact and has no boundary point when $E>1/4$, since a boundary point has $E=x(1-x)\le1/4$. For $E<1/3$ its two constraint gradients are independent. The Lagrange equations for $xyz$ give $yz=A+B(y+z)$ and its cyclic versions. Subtraction gives $(y-x)(z-B)=0$ and its cyclic versions; three distinct weights are impossible, so two weights are equal. The two possible equal weights are $(1\pm s)/3$, $s=\sqrt{1-3E}$. Their products are $(1-3s^2\mp2s^3)/27$, respectively, so the plus choice minimizes the product. At $E=1/3$ the only triple is uniform, giving the same formula.

Because $g$ decreases in $T$, it is bounded above by its value on this minimizing triple. Direct substitution into the displayed formula defining $g$ gives

$$
\begin{aligned}
g&\le-(2b-1)^2 H_C(b),\\
H_C(b)&=72Cb^3-48Cb^2+8Cb-48b^3+44b^2-12b+1.
\end{aligned}
\tag{14.9}
$$

The polynomial $H_C$ is affine in $C$. Its values at the two endpoints of the larger closed interval $[2/3,5/4]$ are strictly positive for $b\in[1/3,1/2]$:

$$
\begin{aligned}
H_{2/3}(b)&=\frac{36b^2-20b+3}{3}
=12(b-5/18)^2+2/27>0,\\
H_{5/4}(b)&=42b^3-16b^2-2b+1\\
&=42(b-1/3)^3+26(b-1/3)^2+\frac43(b-1/3)+\frac19>0.
\end{aligned}
$$

Thus $H_C(b)>0$. Since $b<1/2$, (14.9) proves $g<0$ also in this case.

Finally restrict the diagonal form to $z_1+z_2+z_3=0$. Its matrix on $(z_1,z_2)$ is

$$
H(t)=\begin{pmatrix}\kappa_1+\kappa_3&\kappa_3\\
\kappa_3&\kappa_2+\kappa_3\end{pmatrix}.
$$

Equations (14.2)–(14.4), (14.8) and (14.9) give

$$
\det H(t)=\kappa_1\kappa_2+\kappa_1\kappa_3+\kappa_2\kappa_3
=\frac{-9q^2v^2 f g}{D_1D_2D_3}>0.
\tag{14.10}
$$

At the uniform triple (14.3) gives $\kappa_i=qv>0$, so $H_{11}>0$. Along the segment from that triple to any full-support $t$, the denominators $D_i$ stay positive and (14.10) stays strictly positive. The real continuous entry $H_{11}$ cannot pass through zero, since at such a point $\det H=-\kappa_3^2\le0$. Hence $H_{11}>0$ and $H>0$ throughout the full-support simplex. This is a sign argument on nonvanishing denominators, not an extension across a singular face.

With $\beta_i=P_i^{-1}b_i$, the exact completed-square identity is

$$
s^TS(X)s=\sum_i(\eta_i+z_i\beta_i)^\ast P_i(\eta_i+z_i\beta_i)
 +(z_1,z_2)^\ast H(t)(z_1,z_2),
\qquad \eta_i=(y_{ij})_{j\ne i}.
$$

It is nonnegative for arbitrary complex row variables. The already supplied boundary theorem and the two separately supplied parameter endpoints finish every case. Undoing the scalar shift and diagonal-unitary conjugation proves the assertion on the original complex map. ∎

**Proposition 14.2 (equality and singular faces of the cap).** For $1/3<r<1/2$ and a nonzero probe, equality in Theorem 14.1 is possible for a nonscalar input exactly when the probe has precisely two nonzero coordinates of equal modulus. If $i$ is its missing coordinate, those inputs are

$$
X=cI+\tau e_i v^\ast,\qquad c,\tau\in\mathbb C.
$$

At $r=1/3$ the equality criterion is Proposition 13.3 at its negative endpoint. At $r=1/2$, write $Y=X-\operatorname{diag}(X)$; equality is exactly

$$
y_{ij}v_j=y_{i\ell}v_\ell\quad\text{for each row }i,
\qquad\{j,\ell\}=\{1,2,3\}\setminus\{i\}.
$$

The zero probe always gives equality. Stance: repo-derived.

**Proof.** On full support and the open arc all $P_i$ and $H$ in the proof of Theorem 14.1 are positive definite. The completed-square identity therefore forces every traceless row variable to be zero.

For a two-coordinate normalized probe $s=(\sqrt w,\sqrt{1-w},0)$, $0<w<1$, use the exact boundary squares and $H(w)$ of Theorem 8.1. Its two determinant factors have strictly positive endpoints as affine functions of $w(1-w)\in[0,1/4]$: at zero they are $qp>0$, $p-r^2>0$, and at $1/4$ they are $((1-q)^2-r^2)/4>0$ and the strict third residual in (14.1) divided by four. The first strict sign follows from $(1-q)^2-r^2\ge q^2>0$. Thus $H(w)>0$ by the sign argument already proved there, forcing $z=0$. The positive scalar squares force $y_{12}=y_{21}=y_{13}=y_{23}=0$. For the remaining row the determinant is, by (14.2) with its row weight zero,

$$
L^2uv(2w-1)^2.
$$

It is positive unless $w=1/2$. At that exceptional point the row block is

$$
\frac{Lr}{2}\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
$$

with kernel $\operatorname{span}\{(1,1)^T\}$ and $b_i=0$. Thus precisely $y_{31}=y_{32}$ is free in these coordinates. Undoing phases and normalization gives the stated $\tau e_i v^\ast$ and verifies it by the same squares. In particular the only singular row block on the open arc has an explicitly orthogonal coupling vector, so its Moore–Penrose contribution is zero.

For a singleton probe $t=(1,0,0)$, all off-diagonal coefficients are $q>0$ or $p-r^2>0$ and all $b_i=0$. The diagonal coefficients are $q(1+3a),q,q$, with

$$
1+3a=18r^2+9r-5=(3r-1)(6r+5)>0.
$$

Thus equality forces every traceless variable to vanish. At $r=1/2$, Proposition 4.2 evaluated without an estimate gives the exact scalar identity

$$
v^\ast S(X)v=\frac34\sum_i|y_{ij}v_j-y_{i\ell}v_\ell|^2,
\qquad\{j,\ell\}=\{1,2,3\}\setminus\{i\},
$$

which proves its equality statement on all supports. ∎

## 15. The exact nonpositive region in dimension three

**Theorem 15.1 (classification for $\lambda\le0$ in dimension three).** Let $K_3$ be the original necessary region in Theorem 8.1 and Question 12.2. For all real $\lambda,q$ with $\lambda\le0$, the original map on $M_3(\mathbb C)$ is Schwarz if and only if $(\lambda,q)\in K_3$. Stance: repo-derived.

**Proof.** Necessity is Theorem 4.1. For sufficiency write $\lambda=-r$, $r\ge0$. The second and fourth inequalities defining $K_3$ say

$$
q\le\frac{1-r^2}{2},\qquad q\le(1+r)(1-2r).
$$

Together with $q\ge0$, the latter excludes $r>1/2$. The difference between the two upper bounds is $(r+1)(3r-1)/2$. Hence their minimum is $(1-r^2)/2$ on $[0,1/3]$ and $(1+r)(1-2r)$ on $[1/3,1/2]$. Both bounds are at most $1/2$ on the respective intervals.

The third residual $R(q)=(5-9q)(1-q)-5r^2$ decreases on $0\le q\le1/2$, since $R'(q)=18q-14<0$. It suffices to check it at the active upper bound. The two exact endpoint values are

$$
\begin{aligned}
R((1-r^2)/2)&=\frac{(1-r^2)(1-9r^2)}4\ge0
&& (0\le r\le1/3),\\
R((1+r)(1-2r))&=4r(r+1)(3r-1)(3r+1)\ge0
&& (1/3\le r\le1/2).
\end{aligned}
$$

Thus $K_3\cap\{\lambda\le0\}$ is exactly the union of the two closed regions

$$
\begin{gathered}
0\le r\le1/3,\qquad 0\le q\le(1-r^2)/2,\\
1/3\le r\le1/2,\qquad 0\le q\le(1+r)(1-2r).
\end{gathered}
$$

Theorem 13.2 supplies the first. Theorem 14.1 supplies the upper boundary of the second, and Proposition 4.2 supplies its $q=0$ boundary. At each fixed $r<1/2$, affine interpolation in $q$ and the exact convexity identity of Remark 4.4 supply every intermediate $q$ for every complex input. At $r=1/2$ the interval consists only of $q=0$. The formulas agree at $r=1/3$, where both upper bounds are $4/9$. No strict parameter inequality or probe-support restriction remains. ∎

**Corollary 15.2 (the surviving original-domain implication).** The closed strip $|\lambda|\le1/d$ and the whole nonpositive part of $K_3$ have the full-complex sufficiency property in Question 12.2. In dimension three the remaining implication is $K_3\subseteq\mathcal S_3$ at positive parameters $\lambda>1/3$ outside the already supplied sufficient sets and their convex hull. At such parameters Theorem 8.1 still supplies the entire simplex boundary; the missing assertion is exactly conditions (A),(B) of Theorem 3.2 for every full-support $t$, including their range and equality conditions. For $d>3$, Question 12.2 likewise remains unresolved outside the strip and the sufficient sets already supplied in §§4,9,11 and their convex hull. No full $K_3$ classification, unrestricted all-$d$ classification, or classification of the transposition family is asserted. Stance: repo-derived, by Theorems 13.2, 15.1 and Corollary 8.2.

**Proposition 15.3 (strict gain against the specified suppliers).** Use the supplier hull $\mathcal H_d$ and coordinates $(\lambda,p)$ of Definition 11.1. Every positive boundary point

$$
(\lambda,p)=(r,r^2),\qquad 0<r\le1/d,
$$

and every negative boundary point $(-r,r^2)$ with $0<r<1/d$ supplied by Theorem 13.2 lies outside $\mathcal H_d$ and the pair-compression sufficient region of Theorem 9.1. The positive points are also outside every $k$-positive region with $k\ge2$. In dimension three, every open-arc point of Theorem 14.1 lies outside $\mathcal H_3$, the pair-compression sufficient region and every $k$-positive region with $k\ge2$. These comparisons concern precisely the declared suppliers, without a worldwide absence or priority assertion. Stance: repo-derived.

**Proof.** All generators of $\mathcal H_d$ satisfy $\lambda\le dp/m$ as proved in Proposition 11.2, and also $\lambda\ge-dp$. For the latter, the CP triangle has $\lambda\ge-p/m\ge-dp$; the depolarizing segment has $t+dp=1+dt\ge0$; and $G_d$ has positive coordinates. Both inequalities survive convex combinations. At $(r,r^2)$ the first requires $r\ge m/d$, which fails on the stated interval. At $(-r,r^2)$ the second requires $r\ge1/d$. Theorem 9.1 requires $m^2r^2\le r^2$, which fails for $r>0$ and $m\ge2$. The positive points violate $\lambda\le p$, required by every declared $k$-positive quadrilateral.

For $d=3$, every generator of $\mathcal H_3$ satisfies $3p+16\lambda+5\ge0$: it holds at the CP vertices $(0,0),(-1/2,1),(1,1)$, at the endpoints $(-1/3,1/9),(1,1)$ of the depolarizing segment, and at $G_3=(1/6,1/9)$. On the arc $p=4r^2+2r-1$, this affine expression is

$$
3p-16r+5=2(3r-1)(2r-1)<0.
$$

The pair-compression condition would require $4r^2\le p$, whereas $p-4r^2=2r-1<0$. Finally the $k=2$ quadrilateral requires $\lambda\ge-(1+3p)/8$, but

$$
1+3p-8r=2(3r+1)(2r-1)<0.
$$

Failure of $2$-positivity excludes every $k$-positive supplier with $k\ge2$. The arc endpoints are the already supplied negative depolarizing endpoint and $q=0$ CP endpoint, respectively. ∎

**Convention 15.4 (source hypotheses and evidence boundary).** The original family remains exactly Eq. (6) of Bera, Bhattacharya and Chruściński, arXiv:2604.18600v1, under $\alpha=dq$ and $\beta=1-dq-\lambda$; its §4 Schwarz question is Question 12.2. The external CP and $k$-positive suppliers and the separately justified depolarizing and reduction suppliers are those specified in §§4,11,12, at precisely their stated hypotheses. Theorem 9.1 is reused only at its actual sufficient condition, not at a rescaled multiplier with a different first coordinate. The added sufficiency arguments are (13.1)–(13.2) and (14.1)–(14.10), using the published complex row reduction and the complete simplex-boundary theorem. They do not use the invalid full sufficient criteria of arXiv:2603.11204v1, arXiv:2512.18900v3 or arXiv:2601.02282v1. Their mathematical status is repo-derived prose; they make no Lean/kernel or global novelty claim. Overlap with the unavailable original full texts identified in Convention 12.1 remains undetermined.

## 追加锚（本行以下为增补区）
