# Persistent nodal branches of the Anderson model on cycles

This volume is reference input. Lean declarations and their checked proof terms carry the mathematical truth; nothing in this volume is kernel-verified. The atomizer is `generic-v1`. Existing text is append-only; corrections and additions belong after the final append anchor.

## 1. Scope

Lindblad and Guerrero call a potential bad when the Anderson Hamiltonian $H_t=\Delta+tV$ fails, at every real coupling $t$, to have simple eigenvalues with non-vanishing eigenvectors, and they ask whether every bad potential shares a nontrivial orthogonal symmetry with the Laplacian. This volume gives a symmetry-free algebraic characterization of badness: a potential is bad exactly when, for some site $j$, the characteristic polynomial of $H_t$ and that of its principal submatrix at $j$ have a common factor of positive degree in the spectral variable over $\mathbb R(t)$. The common factor is a persistent nodal branch: for every real $t$ it carries a real eigenvalue with an eigenvector vanishing at $j$. On the cycle of length nine the volume exhibits an explicit cubic nodal branch for the potential $(1,1,-1,1,1,-1,1,-1,-1)$, writes the nodal eigenvector in closed form, and proves that the only matrices commuting with both the Laplacian and this potential are scalars. This potential is therefore bad without any nontrivial shared symmetry, which answers the converse question negatively at length nine. Finally, periodic repetition of a bad potential preserves badness but always creates a shift symmetry, so it cannot transport a symmetry-free example to a longer cycle.

## 2. Notation and conventions

**Convention 2.1 (Cycles and indices).** For $L\ge3$ the sites of the cycle $C_L$ are $\mathbb Z/L\mathbb Z=\{0,1,\dots,L-1\}$, with $i$ adjacent to $i\pm1$. $A_L$ is the adjacency matrix of $C_L$, $\Delta_L=2I-A_L$ its Laplacian, so $(\Delta_L\psi)(i)=2\psi(i)-\psi(i-1)-\psi(i+1)$. $e_i$ denotes the $i$-th standard basis vector and $E_{ij}=e_ie_j^\top$.

**Convention 2.2 (Anderson Hamiltonian).** For a finite simple graph $G$ with Laplacian $\Delta$ and a real vector $v$ indexed by its vertices, $V=\operatorname{diag}(v)$ and $H_t=\Delta+tV$ for $t\in\mathbb R$. This is the operator of Lindblad and Guerrero, §1; on $C_L$ it reads $(H_t\psi)(i)=\sum_{k\sim i}(\psi(i)-\psi(k))+tv_i\psi(i)$.

**Convention 2.3 (Characteristic polynomials).** For an $n\times n$ real symmetric matrix family $H_t$, $n\ge2$, put $p(\lambda,t)=\det(\lambda I-H_t)$, and for a site $j$ let $H_t^{(j)}$ be the principal submatrix obtained by deleting row and column $j$, with $q_j(\lambda,t)=\det(\lambda I-H_t^{(j)})$. When the entries of $H_t$ are polynomials in $t$, both $p$ and $q_j$ lie in $\mathbb R[t][\lambda]$ and are monic in $\lambda$, of degrees $n$ and $n-1$. $\operatorname{Res}_\lambda$ is the resultant in $\lambda$.

**Convention 2.4 (Good and bad potentials).** Following Lindblad and Guerrero, Definition 1.1, $H_t$ has simple eigenvalues if every eigenvalue has multiplicity one, and $V$ is bad if for every $t\in\mathbb R$ the matrix $H_t$ fails to have simple eigenvalues or fails to have non-vanishing eigenvectors; $V$ is good if both properties hold for all but finitely many $t$. When the spectrum is simple, each eigenvector is determined up to a nonzero scalar, so non-vanishing means that every eigenvector has all coordinates nonzero. An eigenvector vanishing at $j$ is a nonzero real vector $z$ with $H_tz=\lambda z$ and $z_j=0$.

**Convention 2.5 (Shared symmetry).** A nontrivial shared symmetry of $(\Delta,V)$ is a real orthogonal matrix $O$ with $O\ne I$, $O\ne-I$, $O\Delta=\Delta O$ and $OV=VO$. The shared commutant of $(\Delta,V)$ is the set of complex matrices commuting with both.

## 3. A symmetry-free criterion for badness

**Lemma 3.1 (Eigenvector zeros and principal submatrices).** Let $H$ be a real symmetric $n\times n$ matrix, $n\ge2$, let $j$ be an index and $\lambda\in\mathbb R$. Then $H$ has an eigenvector for $\lambda$ vanishing at $j$ if and only if $\lambda$ is an eigenvalue of both $H$ and $H^{(j)}$. Stance: literature-attested (§8).

**Proof.** Suppose $Hz=\lambda z$, $z\ne0$, $z_j=0$. Let $z'$ be $z$ with coordinate $j$ removed; then $z'\ne0$, and for $i\ne j$ one has $(H^{(j)}z')_i=\sum_{k\ne j}H_{ik}z_k=(Hz)_i=\lambda z_i$, so $\lambda$ is an eigenvalue of $H^{(j)}$. Conversely let $\lambda$ be an eigenvalue of $H$ and of $H^{(j)}$, let $y'$ be a real eigenvector of $H^{(j)}$ for $\lambda$, and let $y$ extend $y'$ by $y_j=0$. For $i\ne j$ the $i$-th coordinate of $(H-\lambda I)y$ is $((H^{(j)}-\lambda I)y')_i=0$, hence $(H-\lambda I)y=\gamma e_j$ with $\gamma=\sum_kH_{jk}y_k$. If $\gamma=0$, then $y$ is an eigenvector for $\lambda$ vanishing at $j$. If $\gamma\ne0$, then $e_j$ lies in the range of the symmetric matrix $H-\lambda I$, which is the orthogonal complement of its kernel; every $z$ in the nonzero kernel then satisfies $z_j=\langle z,e_j\rangle=0$. ∎

**Theorem 3.2 (Persistent nodal branches).** Let $H_t=\Delta+tV$ where $\Delta$ and $V$ are real symmetric $n\times n$ matrices, $n\ge2$, and fix an index $j$. The following are equivalent:

1. $p$ and $q_j$ have a common factor of positive $\lambda$-degree in $\mathbb R(t)[\lambda]$;
2. there is $g\in\mathbb R[t][\lambda]$, monic in $\lambda$ of degree at least one, dividing both $p$ and $q_j$ in $\mathbb R[t][\lambda]$;
3. $\operatorname{Res}_\lambda(p,q_j)=0$ in $\mathbb R[t]$;
4. for every real $t$, $H_t$ has an eigenvector vanishing at $j$;
5. for infinitely many real $t$, $H_t$ has an eigenvector vanishing at $j$.

Moreover, under these conditions every complex root of $g(\cdot,t_0)$, for every real $t_0$, is a real eigenvalue of $H_{t_0}$ with an eigenvector vanishing at $j$. Stance: repo-derived; the resultant and Gauss-lemma steps are literature-attested (§8).

**Proof.** (1)⇔(3): $p$ and $q_j$ are monic in $\lambda$ over the field $\mathbb R(t)$, so their resultant vanishes exactly when they have a common factor of positive degree. (1)⇒(2): let $h$ be the monic greatest common divisor of $p$ and $q_j$ in $\mathbb R(t)[\lambda]$. Then $p=hu$ with $u$ monic in $\mathbb R(t)[\lambda]$. The ring $\mathbb R[t]$ is integrally closed, so the monic factors in $\mathbb R(t)[\lambda]$ of a monic polynomial in $\mathbb R[t][\lambda]$ have coefficients in $\mathbb R[t]$: their coefficients are symmetric functions of roots that are integral over $\mathbb R[t]$. Hence $h,u\in\mathbb R[t][\lambda]$, and likewise the cofactor of $h$ in $q_j$; take $g=h$. (2)⇒(4): fix $t_0\in\mathbb R$. The polynomial $g(\cdot,t_0)$ is monic of positive degree, so it has a complex root $\lambda_0$. It divides $p(\cdot,t_0)$ and $q_j(\cdot,t_0)$, so $\lambda_0$ is an eigenvalue of the real symmetric matrices $H_{t_0}$ and $H_{t_0}^{(j)}$; in particular $\lambda_0$ is real. Lemma 3.1 gives an eigenvector of $H_{t_0}$ for $\lambda_0$ vanishing at $j$. This also proves the final assertion. (4)⇒(5) is immediate. (5)⇒(3): at each such $t_0$, Lemma 3.1 gives a common root of $p(\cdot,t_0)$ and $q_j(\cdot,t_0)$. Both are monic in $\lambda$, so specialization commutes with the resultant and $\operatorname{Res}_\lambda(p,q_j)(t_0)=\operatorname{Res}_\lambda(p(\cdot,t_0),q_j(\cdot,t_0))=0$. A polynomial in $t$ with infinitely many zeros is zero. ∎

**Corollary 3.3 (Algebraic characterization of bad potentials).** Let $G$ be a finite simple graph with $n\ge2$ vertices, $\Delta$ its Laplacian, $V=\operatorname{diag}(v)$ with $v$ real, and $H_t=\Delta+tV$. Then $V$ is bad if and only if $\operatorname{Res}_\lambda(p,q_j)=0$ in $\mathbb R[t]$ for some vertex $j$. If $\operatorname{Res}_\lambda(p,q_j)\ne0$ for every vertex $j$, then $V$ is good, and the couplings at which $H_t$ fails to have simple eigenvalues with non-vanishing eigenvectors lie among the finitely many real zeros of $\prod_j\operatorname{Res}_\lambda(p,q_j)$. Stance: repo-derived for the resultant characterization; the good/bad dichotomy itself is literature-attested (§8).

**Proof.** If an eigenvalue $\lambda$ of $H_t$ has multiplicity at least two, its real eigenspace $W$ has dimension at least two, and the kernel of the functional $z\mapsto z_j$ on $W$ is nonzero; so a multiple eigenvalue yields, for every $j$, an eigenvector vanishing at $j$. Consequently $H_t$ fails to have simple eigenvalues with non-vanishing eigenvectors if and only if $H_t$ has an eigenvector vanishing at some vertex. If $V$ is bad, then for each $t\in\mathbb R$ there is a vertex $j(t)$ at which some eigenvector of $H_t$ vanishes. There are finitely many vertices and infinitely many $t$, so some $j$ occurs for infinitely many $t$, and Theorem 3.2 (5)⇒(3) gives $\operatorname{Res}_\lambda(p,q_j)=0$. Conversely, $\operatorname{Res}_\lambda(p,q_j)=0$ gives, by Theorem 3.2 (3)⇒(4), an eigenvector vanishing at $j$ for every $t$, so $V$ is bad. If all the resultants are nonzero, then by Theorem 3.2 (5)⇒(3) each vertex $j$ carries a vanishing eigenvector only at finitely many $t$, namely at zeros of $\operatorname{Res}_\lambda(p,q_j)$; outside the union of these finite sets $H_t$ has no eigenvector with a zero coordinate, hence by the first sentence of the proof it has simple eigenvalues and non-vanishing eigenvectors. ∎

**Remark 3.4 (Rational data).** If $\Delta$ and $V$ have rational entries, as for potentials with values in $\{-1,1\}$, then $p,q_j\in\mathbb Q[t][\lambda]$, and the greatest common divisor computed in $\mathbb Q(t)[\lambda]$ coincides with the one in $\mathbb R(t)[\lambda]$, since the Euclidean algorithm does not leave the smaller field. Corollary 3.3 therefore decides badness of a given rational potential by finitely many exact polynomial computations, with no reference to symmetries. Stance: repo-derived.

**Remark 3.5 (Relation to symmetric mechanisms).** Lemma 3.2 of Lindblad and Guerrero produces bad potentials from a shared orthogonal symmetry $O\ne I$ with $O^2\ne I$ or with $Oe_j=e_j$. Corollary 3.3 shows that every bad potential, symmetric or not, is detected by a nodal factor $g$ at some vertex. The examples below are bad potentials whose nodal factor exists although the shared commutant is trivial. Stance: repo-derived.

## 4. Persistent nodal branches on cycles of length eight and nine

**Proposition 4.1 (The length-eight nodal branch).** On $C_8$ let $v=(1,1,1,1,-1,1,-1,-1)$ and $H_t=\Delta_8+t\operatorname{diag}(v)$. For every real $t$ and each root $\alpha$ of $\alpha^2+2t\alpha-2=0$, the vector

$$
z=(1,\,0,\,-1,\,\alpha,\,1-\alpha^2,\,-2t,\,1,\,-\alpha)
$$

satisfies $H_tz=(2+t+\alpha)z$. Consequently $g(\lambda,t)=\lambda^2-4\lambda+2-t^2$ divides both $p$ and $q_1$ in $\mathbb R[t][\lambda]$, and the potential is bad. The only matrices commuting with both $\Delta_8$ and $\operatorname{diag}(v)$ are scalars. Stance: repo-derived; this is the known length-eight counterexample to the converse question, recovered here as an instance of Theorem 3.2.

**Proof.** Write $\lambda=2+t+\alpha$ and $d_i=2+tv_i-\lambda$, so $d_i=-\alpha$ when $v_i=1$ and $d_i=-2t-\alpha$ when $v_i=-1$. The equation at site $i$ is $d_iz_i-z_{i-1}-z_{i+1}=0$. Site 0: $-\alpha-(-\alpha)-0=0$. Site 1: $0-1-(-1)=0$. Site 2: $\alpha-0-\alpha=0$. Site 3: $-\alpha^2+1-(1-\alpha^2)=0$. Site 4 ($v_4=-1$): $(-2t-\alpha)(1-\alpha^2)-\alpha+2t=\alpha^3+2t\alpha^2-2\alpha=\alpha(\alpha^2+2t\alpha-2)=0$. Site 5: $2t\alpha-(1-\alpha^2)-1=\alpha^2+2t\alpha-2=0$. Site 6 ($v_6=-1$): $-2t-\alpha+2t+\alpha=0$. Site 7 ($v_7=-1$): $(-2t-\alpha)(-\alpha)-1-1=\alpha^2+2t\alpha-2=0$. The two roots $\alpha=-t\pm\sqrt{t^2+2}$ give $\lambda=2\pm\sqrt{t^2+2}$, the two roots of $g(\cdot,t)$; both carry eigenvectors vanishing at site 1, so by Lemma 3.1 both are common roots of $p(\cdot,t)$ and $q_1(\cdot,t)$ for every real $t$. The polynomial $g$ is irreducible in $\mathbb R(t)[\lambda]$, because $t^2+2$ is not a square in $\mathbb R(t)$. Since $\operatorname{Res}_\lambda(g,p)$ vanishes at every real $t$, it is zero, so $g$ and $p$ share a factor in $\mathbb R(t)[\lambda]$, which by irreducibility is $g$; as $g$ is monic, the quotient lies in $\mathbb R[t][\lambda]$. The same argument applies to $q_1$. Badness follows from Theorem 3.2.

For the commutant, let $\mathcal A$ be the real unital algebra generated by $A_8$ and $V$, and $P_\pm=\tfrac12(I\pm V)$. The sites with $v_i=1$ are $\{0,1,2,3,5\}$; inside this set the cycle edges form the path $0,1,2,3$, and $5$ is isolated. The path adjacency matrix $B_0$ on four vertices satisfies $B_0^4-3B_0^2+I=0$, its characteristic polynomial being $x^4-3x^2+1$. Hence $B=P_+A_8P_+$ satisfies $B^4-3B^2+P_+=E_{55}\in\mathcal A$. The sites with $v_i=-1$ are $\{4,6,7\}$, with the single internal edge $\{6,7\}$, so $E_{44}=P_--(P_-A_8P_-)^2\in\mathcal A$. From $e_5$ one obtains $A_8e_5=e_4+e_6$, then $e_4=E_{44}A_8e_5$ and $e_6$, then $A_8e_4-e_5=e_3$, $A_8e_3-e_4=e_2$, $A_8e_2-e_3=e_1$, $A_8e_1-e_2=e_0$ and $A_8e_6-e_5=e_7$. So $\mathcal Ae_5=\mathbb R^8$, and the transposition argument in the proof of Theorem 4.6 gives $\mathcal A=M_8(\mathbb R)$ and a scalar commutant. ∎

**Definition 4.2 (The nine-cycle potential).** On $C_9$ put

$$
v=(1,1,-1,1,1,-1,1,-1,-1),\qquad V=\operatorname{diag}(v),\qquad H_t=\Delta_9+tV,
$$

and, for $\lambda,t\in\mathbb R$, $a=2-\lambda+t$, $b=2-\lambda-t$, so that $2+tv_i-\lambda$ equals $a$ when $v_i=1$ and $b$ when $v_i=-1$. Define

$$
c(\lambda,t)=\lambda^3-\lambda^2t-6\lambda^2-\lambda t^2+4\lambda t+9\lambda+t^3+2t^2-3t-3 .
$$

Stance: definition.

**Lemma 4.3 (The cubic in the coordinates $a,b$).** With $a,b$ as in Definition 4.2,

$$
c(\lambda,t)=-\,k(a,b),\qquad k(a,b)=a^2b-2a-b+1 .
$$

The polynomial $k$ is irreducible in $\mathbb R[a,b]$, and $c$ is irreducible in $\mathbb R(t)[\lambda]$. Stance: repo-derived.

**Proof.** Put $\mu=2-\lambda$, so $a=\mu+t$, $b=\mu-t$. Then $a^2b=(\mu+t)^2(\mu-t)=\mu^3+\mu^2t-\mu t^2-t^3$ and $-2a-b+1=-3\mu-t+1$. Substituting $\mu=2-\lambda$, the cubic part is $(2-\lambda)^3=8-12\lambda+6\lambda^2-\lambda^3$, the term $(2-\lambda)^2t=4t-4\lambda t+\lambda^2t$, the term $-(2-\lambda)t^2=-2t^2+\lambda t^2$, and $-3(2-\lambda)=-6+3\lambda$. Summing,

$$
k=-\lambda^3+6\lambda^2+\lambda^2t-9\lambda-4\lambda t+\lambda t^2+3+3t-2t^2-t^3=-c .
$$

For irreducibility write $k=(a^2-1)\,b-(2a-1)$, of degree one in $b$. A factorization into two nonconstant factors would have one factor $f(a)$ free of $b$ and of positive degree, and $f$ would divide both $a^2-1$ and $2a-1$; but $2a-1$ has the single root $\tfrac12$, at which $a^2-1=-\tfrac34\ne0$. So $k$ is irreducible in $\mathbb R[a,b]$. The substitution $(\lambda,t)\mapsto(a,b)$ is an invertible affine change of variables, so $c$ is irreducible in $\mathbb R[\lambda,t]$; since $c$ is monic in $\lambda$, it is primitive over $\mathbb R[t]$, and Gauss's lemma gives irreducibility in $\mathbb R(t)[\lambda]$. ∎

**Theorem 4.4 (A persistent nodal branch on the nine-cycle).** For every real $t$ and every real $\lambda$ with $c(\lambda,t)=0$, the vector $z\in\mathbb R^9$ with coordinates

$$
\begin{aligned}
z_8&=1, & z_0&=b, & z_1&=ab-1, & z_2&=a^2b-a-b, & z_3&=2a-a^2b,\\
z_4&=1-ab, & z_5&=-a, & z_6&=-1, & z_7&=0, &&
\end{aligned}
$$

where $a=2-\lambda+t$ and $b=2-\lambda-t$, satisfies $H_tz=\lambda z$. For every real $t$ such a real $\lambda$ exists. Hence for every real $t$ the matrix $H_t$ has an eigenvector vanishing at site $7$, the potential $V$ is bad, and $c$ divides both $p$ and $q_7$ in $\mathbb R[t][\lambda]$. Stance: suspected-novel (§8).

**Proof.** The equation at site $i$ reads $(2+tv_i-\lambda)z_i-z_{i-1}-z_{i+1}=0$, with coefficient $a$ at the sites $0,1,3,4,6$ and $b$ at the sites $2,5,7,8$. For an arbitrary pair $(\lambda,t)$ the residuals $r_i=((H_t-\lambda I)z)_i$ are:

$$
\begin{aligned}
r_8&=b\cdot1-z_7-z_0=b-0-b=0,\\
r_0&=a\,b-z_8-z_1=ab-1-(ab-1)=0,\\
r_1&=a(ab-1)-z_0-z_2=a^2b-a-b-(a^2b-a-b)=0,\\
r_4&=a(1-ab)-z_3-z_5=a-a^2b-(2a-a^2b)+a=0,\\
r_5&=b(-a)-z_4-z_6=-ab-(1-ab)+1=0,\\
r_6&=a(-1)-z_5-z_7=-a+a-0=0,\\
r_7&=b\cdot0-z_6-z_8=1-1=0,
\end{aligned}
$$

while the two remaining residuals are

$$
\begin{aligned}
r_2&=b(a^2b-a-b)-(ab-1)-(2a-a^2b)=a^2b^2+a^2b-2ab-2a-b^2+1=(b+1)\,k(a,b),\\
r_3&=a(2a-a^2b)-(a^2b-a-b)-(1-ab)=-(a^3b+a^2b-2a^2-ab-a-b+1)=-(a+1)\,k(a,b).
\end{aligned}
$$

The factorizations follow by expanding $(b+1)(a^2b-2a-b+1)=a^2b^2-2ab-b^2+b+a^2b-2a-b+1$ and $(a+1)(a^2b-2a-b+1)=a^3b-2a^2-ab+a+a^2b-2a-b+1$. Hence

$$
(H_t-\lambda I)z=k(a,b)\,\big((b+1)e_2-(a+1)e_3\big),
$$

and by Lemma 4.3 the right side is zero whenever $c(\lambda,t)=0$. Since $z_8=1$, $z$ is a nonzero real eigenvector with $z_7=0$.

For fixed real $t$, Lemma 4.3 shows that $\mu\mapsto k(\mu+t,\mu-t)$ is a real cubic in $\mu$ with leading coefficient $1$; it has a real root $\mu_0$, and $\lambda_0=2-\mu_0$ is a real root of $c(\cdot,t)$. So for every real $t$ the matrix $H_t$ has an eigenvector vanishing at site $7$, and by Convention 2.4 and the first paragraph of the proof of Corollary 3.3 the potential is bad. By Lemma 3.1, $\lambda_0$ is a common root of $p(\cdot,t)$ and $q_7(\cdot,t)$ for every real $t$, so $\operatorname{Res}_\lambda(c,p)$ and $\operatorname{Res}_\lambda(c,q_7)$ vanish on $\mathbb R$ and are zero. Thus $c$ shares a factor with $p$ and with $q_7$ in $\mathbb R(t)[\lambda]$; being irreducible (Lemma 4.3), it divides both, and since $c$ is monic the quotients lie in $\mathbb R[t][\lambda]$. ∎

**Remark 4.5 (Cofactors).** Expansion in the coordinates of Definition 4.2 gives $q_7=(ab-1)\,(k-2)\,k$, that is $q_7=(\lambda^2-4\lambda+3-t^2)\,c\,(c+2)$, and $p=-k\cdot s$ with

$$
s=a^3b^3-a^3b-4a^2b^2+2a^2-ab^3-ab^2+5ab+a+2b^2+2b-2 .
$$

These identities are not used in any proof of this volume. Stance: repo-derived.

**Theorem 4.6 (Trivial shared commutant on the nine-cycle).** Let $v$ be as in Definition 4.2. Every complex $9\times9$ matrix $X$ with $X\Delta_9=\Delta_9X$ and $XV=VX$ is a scalar multiple of $I$. Consequently $(\Delta_9,V)$ has no nontrivial shared symmetry. Stance: suspected-novel (§8).

**Proof.** Since $\Delta_9=2I-A_9$, commuting with $\Delta_9$ is the same as commuting with $A_9$. Let $\mathcal A$ be the real unital algebra generated by $A_9$ and $V$; a matrix commutes with $A_9$ and $V$ exactly when it commutes with every element of $\mathcal A$. It suffices to show $\mathcal A=M_9(\mathbb R)$: a complex matrix commuting with every $E_{ij}$ satisfies $X_{ij}=X_{ii}\delta_{ij}$ and $X_{ii}=X_{jj}$ (compare the entries of $XE_{ij}=E_{ij}X$), so it is scalar.

Put $P_\pm=\tfrac12(I\pm V)\in\mathcal A$, the diagonal projections onto $P=\{0,1,3,4,6\}$ (where $v_i=1$) and $N=\{2,5,7,8\}$ (where $v_i=-1$). Among the nine cycle edges $\{i,i+1\}$, exactly $\{0,1\}$ and $\{3,4\}$ join two sites of $P$, and exactly $\{7,8\}$ joins two sites of $N$. Hence $B=P_+A_9P_+$ is the adjacency matrix of the matching $\{0,1\},\{3,4\}$ on $P$, so $B^2=E_{00}+E_{11}+E_{33}+E_{44}$ and

$$
E_{66}=P_+-B^2\in\mathcal A .
$$

Likewise $C=P_-A_9P_-$ satisfies $C^2=E_{77}+E_{88}$, so $E_{22}+E_{55}=P_--C^2\in\mathcal A$.

The subspace $\mathcal Ae_6$ contains $e_6$; $A_9e_6=e_5+e_7$; $(E_{22}+E_{55})(e_5+e_7)=e_5$, hence also $e_7$; then successively $A_9e_7-e_6=e_8$, $A_9e_5-e_6=e_4$, $A_9e_4-e_5=e_3$, $A_9e_3-e_4=e_2$, $A_9e_2-e_3=e_1$ and $A_9e_1-e_2=e_0$. So $\mathcal Ae_6=\mathbb R^9$. Both generators are symmetric, so $\mathcal A$ is closed under transposition. For $u,w\in\mathbb R^9$ choose $M,N\in\mathcal A$ with $u=Me_6$, $w=Ne_6$; then $uw^\top=ME_{66}N^\top\in\mathcal A$. Every matrix is a sum of such rank-one matrices, so $\mathcal A=M_9(\mathbb R)$.

Finally, a real orthogonal $O$ commuting with $\Delta_9$ and $V$ equals $\omega I$ with $\omega$ real and $\omega^2=1$, so $O=\pm I$. ∎

**Corollary 4.7 (The symmetry converse fails on the nine-cycle).** The potential of Definition 4.2 is bad on $C_9$ and shares no nontrivial orthogonal symmetry with the Laplacian. Hence the converse question of Lindblad and Guerrero, whether every bad potential shares a nontrivial symmetry with the Laplacian, has a negative answer on the cycle of length nine, already under the weakest reading in which any orthogonal $O\ne\pm I$ counts as a symmetry. Stance: suspected-novel (§8).

**Proof.** Theorem 4.4 and Theorem 4.6. ∎

## 5. Periodic lifts

**Proposition 5.1 (Lifting preserves nodal branches and creates a symmetry).** Let $L\ge3$, $k\ge2$, $v$ a real potential on $C_L$, and $\tilde v$ its periodic lift to $C_{kL}$, $\tilde v_i=v_{i\bmod L}$. Write $H_t$ and $\tilde H_t$ for the corresponding Hamiltonians.

1. If $H_tz=\lambda z$ with $z_j=0$, then the lift $\tilde z_i=z_{i\bmod L}$ satisfies $\tilde H_t\tilde z=\lambda\tilde z$ and vanishes at every site congruent to $j$ modulo $L$. In particular, if $v$ is bad then $\tilde v$ is bad.
2. The shift $S$ on $C_{kL}$, $(S\psi)_i=\psi_{i-1}$, satisfies $S^L\Delta_{kL}=\Delta_{kL}S^L$ and $S^L\tilde V=\tilde VS^L$, and $S^L$ is a real orthogonal matrix different from $I$ and $-I$.

Hence a periodic lift of a bad potential is bad but always shares a nontrivial symmetry with the Laplacian; for $k\ge3$ one has $(S^L)^2\ne I$, so by Lemma 3.2 of Lindblad and Guerrero the lifted spectrum is degenerate at every $t$. Stance: repo-derived; the cited degeneracy statement is literature-attested (§8).

**Proof.** (1) Reduction modulo $L$ is a graph homomorphism $C_{kL}\to C_L$ that maps the two neighbours $i\pm1$ of $i$ to the two neighbours of $i\bmod L$, and $\tilde v_i=v_{i\bmod L}$. Therefore $(\tilde H_t\tilde z)_i=(2+t\tilde v_i)\tilde z_i-\tilde z_{i-1}-\tilde z_{i+1}=(H_tz)_{i\bmod L}=\lambda\tilde z_i$. The lift is nonzero, and $\tilde z_i=z_j=0$ when $i\equiv j$. Badness of $v$ means that for every $t$ some eigenvector of $H_t$ vanishes somewhere (proof of Corollary 3.3), and the lift transfers this to $\tilde H_t$. (2) $S$ is a cyclic permutation matrix commuting with $A_{kL}$, hence with $\Delta_{kL}$, and so does $S^L$. Conjugation by $S^L$ maps $\operatorname{diag}(\tilde v_i)$ to $\operatorname{diag}(\tilde v_{i-L})=\tilde V$. The matrix $S^L$ is a permutation matrix, hence orthogonal; it moves $e_0$ to $e_L\ne e_0$ because $0<L<kL$, so $S^L\ne I$, and its entries are nonnegative, so $S^L\ne-I$. If $k\ge3$ then $2L<kL$ and $(S^L)^2e_0=e_{2L}\ne e_0$. ∎

**Remark 5.2 (Lifts do not settle longer cycles).** By Proposition 5.1, the potentials of Proposition 4.1 and Definition 4.2 lift to bad potentials on $C_{8k}$ and $C_{9k}$, but every lift shares the symmetry $S^8$ or $S^9$. Symmetry-free bad potentials on longer cycles therefore require an aperiodic construction; this volume provides none. Stance: repo-derived.

## 6. Boundaries and open questions

**Remark 6.1 (What is not proved).** The volume proves the converse fails at lengths eight and nine. It proves nothing about any other length: neither the existence nor the non-existence of symmetry-free bad $\{\pm1\}$-potentials on $C_L$ for $L\notin\{8,9\}$, nor any minimality statement in $L$.

**Open question 6.2 (Composite lengths).** Determine the set of $L\ge3$ for which $C_L$ carries a bad potential with values in $\{-1,1\}$ and trivial shared commutant. For prime $L$, Lindblad and Guerrero, Proposition 4.1, show that bad potentials are exactly those with a reflection symmetry about a vertex, so prime lengths admit no such potential; the composite lengths other than $8$ and $9$ are open here.

**Open question 6.3 (Structure of nodal factors).** For a bad potential with trivial shared commutant, the nodal factor of Theorem 3.2 has degree two at length eight and degree three at length nine. Is there a description of the nodal factors, for example through transfer matrices of the two letters $a$ and $b$ as in the proof of Theorem 4.4, that predicts which words in $\{1,-1\}^L$ carry a persistent nodal branch?

## 7. Proof dependencies

**Remark 7.1 (Dependency order).** Lemma 3.1 feeds Theorem 3.2, which feeds Corollary 3.3. Proposition 4.1 uses Lemma 3.1, Theorem 3.2 and the transposition argument of Theorem 4.6. Theorem 4.4 uses Lemma 4.3, Lemma 3.1 and the proof of Corollary 3.3. Corollary 4.7 uses Theorems 4.4 and 4.6. Proposition 5.1 uses the proof of Corollary 3.3 and cites Lemma 3.2 of Lindblad and Guerrero.

## 8. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| O. Lindblad, E. Guerrero, *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*, arXiv:2512.00278v1, §1 (operator, Definition 1.1, the converse question after Theorem 1.3), Proposition 2.3, Lemma 3.2, Proposition 4.1 | `literature-attested`: the operator $H_t=\Delta+tV$, the definitions of good and bad potentials, the good/bad dichotomy (Proposition 2.3, proved there by analytic perturbation theory), the two symmetry mechanisms of Lemma 3.2 used in Remark 3.5 and Proposition 5.1, and the prime-length characterization cited in Open question 6.2. The source states the converse as a question and does not use principal minors or resultants. |
| R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge 2013, §4.3 (interlacing for bordered matrices); P. B. Denton, S. J. Parke, T. Tao, X. Zhang, *Eigenvectors from eigenvalues: a survey of a basic identity in linear algebra*, Bull. Amer. Math. Soc. 59 (2022) 31–58 | `literature-attested`: for a Hermitian matrix, the vanishing of an eigenvector coordinate is governed by the spectrum of the corresponding principal submatrix; Lemma 3.1 is the elementary form of this relation, proved in full above. |
| S. Lang, *Algebra*, rev. 3rd ed., Springer 2002, Ch. IV §2 (Gauss's lemma) and Ch. IV §8 (resultant); M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley 1969, Prop. 5.15 | `literature-attested`: resultants of monic polynomials vanish exactly at common factors and commute with specialization; monic factors of monic polynomials over an integrally closed domain have coefficients in that domain; Gauss's lemma. Used in Theorem 3.2, Proposition 4.1 and Lemma 4.3. |
| — | `repo-derived`: Theorem 3.2, Corollary 3.3 (resultant characterization), Remarks 3.4, 3.5, 4.5, 5.2, Proposition 4.1 (the known length-eight counterexample; the nodal-factor identification and the commutant proof are given here), Lemma 4.3, Proposition 5.1. |
| — | `suspected-novel`: Theorem 4.4, Theorem 4.6, Corollary 4.7. Searched: the abstract and the HTML full text of arXiv:2512.00278v1, and web searches combining the authors' names with "bad potential", "symmetry" and "cycle", and the Anderson model on cycles with eigenvectors vanishing for all couplings. No proof or refutation of the converse question at length nine was found in the searched scope; this establishes no priority beyond that scope. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
