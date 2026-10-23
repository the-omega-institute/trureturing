# A reducible non-toral projective collision over $\mathbb Q_2$

## 1. The fixed-source comparison

**Definition 1.1 (Projective conjugacy and invariant subspaces).** Let $G$ be a finite group and write $[A]$ for the class of $A\in GL_3(\mathbb C)$ in $PGL_3(\mathbb C)$. Homomorphisms $\rho_1,\rho_2:G\to PGL_3(\mathbb C)$ are *element-conjugate* if

$$
\forall g\in G\quad\exists h_g\in PGL_3(\mathbb C)
\quad \rho_2(g)=h_g\rho_1(g)h_g^{-1}.
$$

They are *globally conjugate* if one $h$ works for every $g$. Both comparisons use the same original source element $g$, without precomposing either map by an automorphism of $G$. A projective homomorphism is *reducible* if the full inverse image of its image under $GL_3(\mathbb C)\to PGL_3(\mathbb C)$ preserves a nonzero proper complex subspace. Its image is *toral* if it lies in an algebraic torus of $PGL_3(\mathbb C)$, and *non-toral* otherwise. These are the fixed-source and invariant-subspace conventions of [*Irreducible projective rigidity over the dyadic local field*, Definition 1.1](LOCAL_Q2_IRREDUCIBLE_PROJECTIVE_RIGIDITY.md#1-the-fixed-source-comparison).

**Definition 1.2 (The inherited diagonal pair and its extension).** Let $\mu_3\subset\mathbb C^\times$ be the cube roots of unity, let $C_n$ denote a cyclic group of order $n$, and put

$$
N=\{(s,t,z):s,t\in\{1,-1\},\ z\in\mu_3\}
\cong C_2^2\times C_3.
$$

The diagonal pair

$$
D_1(s,t,z)=\operatorname{diag}(1,sz,tz^{-1}),\qquad
D_2(s,t,z)=\operatorname{diag}(1,sz^{-1},tz)
\tag{1.1}
$$

is the prior toral construction of [*Toral character triples: complete source support*, §2.6, equations (2.10)–(2.11)](TORAL_CHARACTER_TRIPLE_SOURCE_SUPPORT.md#26-the-supporting-twelve-element-group), attributed there to [*A twelve-element abelian toral construction over $\mathbb Q_2$*](https://github.com/the-omega-institute/trureturing/issues/20447#issuecomment-6352198106). Its projective faithfulness, element-conjugacy and failure of global matching are inherited results; the formulas and their matching identities are reproduced below as ingredients of the extension.

Let $\theta:N\to N$ be the involution

$$
\theta(s,t,z)=(t,s,z^{-1}),
$$

and define $G_*=N\rtimes_\theta\langle F\rangle$, where $F^2=1$. Thus every element is uniquely $nF^\epsilon$, with $n\in N$ and $\epsilon\in\{0,1\}$, and

$$
(nF^\epsilon)(mF^\delta)
=n\theta^\epsilon(m)F^{\epsilon+\delta},
\tag{1.2}
$$

where the exponent of $F$ is reduced modulo two. Write $P_{ij}$ for the matrix interchanging the $i$th and $j$th standard basis vectors, and set $S=P_{23}$.

**Theorem 1.3 (An explicit degree-twenty-four counterexample).** Fix an algebraic closure of $\mathbb Q_2$. Choose $\alpha,i,\gamma$ in it with

$$
\alpha^4=5,\qquad i^2=-1,\qquad\gamma^3=2,
$$

and put

$$
L=\mathbb Q_2(\alpha,i,\gamma).
\tag{1.3}
$$

Then $L/\mathbb Q_2$ is finite Galois of degree $24$. There is an identification $\operatorname{Gal}(L/\mathbb Q_2)\cong G_*$ under which

$$
\begin{aligned}
\rho_1((s,t,z)F^\epsilon)
&=[D_1(s,t,z)S^\epsilon],\\
\rho_2((s,t,z)F^\epsilon)
&=[D_2(s,t,z)S^\epsilon]
\end{aligned}
\tag{1.4}
$$

are injective homomorphisms to $PGL_3(\mathbb C)$. Both are reducible, both have non-toral image, and they are element-conjugate but not globally conjugate. The restriction to $N$ is exactly the pair (1.1); the assertions beyond that pair are its compatible extension to $G_*$ and the realization (1.3).

Proof. The field realization, the homomorphisms, and the two distinct conjugacy assertions are established in §§2–4.

## 2. The actual dyadic field and its automorphisms

### 2.1. The quadratic field and two independent square classes

Put $u=\alpha^2$ and $K=\mathbb Q_2(u)$, so $u^2=5$. We use the elementary square criterion for an odd unit $a\in\mathbb Z_2^\times$:

$$
a\in(\mathbb Q_2^\times)^2
\quad\Longleftrightarrow\quad a\equiv1\pmod8.
\tag{2.1}
$$

For completeness, a square root of a unit must have valuation zero, and the square of every odd integer is $1$ modulo $8$. Conversely, start with an odd $x_3$ satisfying $x_3^2\equiv a\pmod8$. Given odd $x_n$ with $x_n^2\equiv a\pmod{2^n}$, choose $e_n\in\{0,1\}$ and set

$$
x_{n+1}=x_n+e_n2^{n-1}.
$$

For $n\ge3$ the square changes modulo $2^{n+1}$ by $e_n2^nx_n$. Since $x_n$ is odd, one choice of $e_n$ makes the next congruence hold. The corrections tend to zero $2$-adically, so the sequence converges to a square root of $a$. This proves (2.1).

Since $5\not\equiv1\pmod8$, $[K:\mathbb Q_2]=2$. Also $i\notin K$. Indeed, writing a putative square root of $-1$ as $a+bu$, with $a,b\in\mathbb Q_2$, gives

$$
a^2+5b^2+2ab\,u=-1.
$$

Thus $ab=0$. If $b=0$, then $a^2=-1$, whose residue is $7$ modulo $8$; if $a=0$, then $b^2=-1/5$, whose residue is $3$. Both contradict (2.1).

Set $\beta=i\alpha$. Then $\alpha^2=u$ and $\beta^2=-u$. The two elements $u$ and $-u$ are nonsquares in $K$: each has norm $-5$ to $\mathbb Q_2$, whereas the norm of a square is a square and $-5\equiv3\pmod8$. Their product $-5$ is also a nonsquare in $K$, for a square root of $-5$ divided by $u$ would be a square root of $-1$ in $K$. Consequently their square classes are independent.

Explicitly, $-u$ cannot become a square in $K(\alpha)$. If

$$
(a+b\alpha)^2=-u,\qquad a,b\in K,
$$

then $ab=0$ by the basis $1,\alpha$. The case $b=0$ makes $-u$ a square in $K$; the case $a=0$ gives $b^2=-1$. Both have been excluded. Therefore

$$
E=K(\alpha,\beta)=\mathbb Q_2(\alpha,i),
\qquad [E:K]=4,\qquad [E:\mathbb Q_2]=8.
\tag{2.2}
$$

Its $K$-automorphisms are the independent sign changes

$$
v_{s,t}(\alpha)=s\alpha,\qquad
v_{s,t}(\beta)=t\beta.
\tag{2.3}
$$

The four roots of $X^4-5$ are $\alpha,-\alpha,\beta,-\beta$. Thus $E$ is its splitting field and is Galois over $\mathbb Q_2$.

### 2.2. A well-defined involution exchanging the sign changes

The exchange $\alpha\leftrightarrow\beta$ defines an automorphism of $E$, as follows. Consider the presentation

$$
A=\mathbb Q_2[X,Y]/(X^4-5,\ X^2+Y^2).
\tag{2.4}
$$

Its elements are spanned over $\mathbb Q_2$ by $X^rY^e$ with $0\le r<4$ and $0\le e<2$. Evaluation at $(\alpha,\beta)$ is a surjection $A\to E$. Equation (2.2) and the eight spanning monomials imply that this map is an isomorphism. In $A$ one has $Y^4=X^4=5$, so exchanging $X,Y$ preserves both defining relations. It induces an involution $F_E$ of $E$ with

$$
F_E(\alpha)=\beta,\qquad F_E(\beta)=\alpha,
\qquad F_E(u)=-u.
\tag{2.5}
$$

In particular it is nonidentity and has order two. Applying it on both sides of (2.3) gives

$$
F_Ev_{s,t}F_E^{-1}=v_{t,s}.
\tag{2.6}
$$

### 2.3. The cubic splitting field and the compatible involution

The unit $-3/5$ is $1$ modulo $8$. By (2.1), choose $q\in\mathbb Q_2$ with $q^2=-3/5$, and define

$$
\zeta=\frac{-1+qu}{2}\in K.
$$

Since $(qu)^2=-3$, one has $\zeta^2+\zeta+1=0$ and $\zeta\ne1$. Thus $\zeta$ is a primitive cube root of unity. Moreover $K=\mathbb Q_2(\zeta)$, because $qu=2\zeta+1$, and the nontrivial automorphism of $K/\mathbb Q_2$ sends $\zeta$ to $\zeta^{-1}$.

The polynomial $X^3-2$ is Eisenstein at $2$ over $\mathbb Q_2$, so every root has degree three over $\mathbb Q_2$. It has no root in the quadratic field $K$. A cubic polynomial with no root is irreducible; hence

$$
T=K(\gamma),\qquad [T:K]=3.
\tag{2.7}
$$

It contains all three roots $\gamma,\zeta\gamma,\zeta^2\gamma$. Conversely their ratios contain $\zeta$, so $T$ is exactly the splitting field over $\mathbb Q_2$ and is Galois. Its $K$-group is generated by

$$
\tau(\gamma)=\zeta\gamma,\qquad \tau|_K=1.
$$

The nontrivial automorphism of $K/\mathbb Q_2$, acting on coefficients of $K[X]/(X^3-2)$ and fixing the class of $X$, defines an automorphism $F_T$ of $T$. This description proves well-definedness, since $X^3-2$ has rational coefficients. It has order two and satisfies

$$
F_T(u)=-u,\qquad F_T(\gamma)=\gamma,
\qquad F_T\tau F_T^{-1}=\tau^{-1}.
\tag{2.8}
$$

### 2.4. The compositum and the same-source group

The extensions $E/K$ and $T/K$ are Galois of coprime degrees four and three. Their intersection is $K$, and the elementary Galois degree formula gives linear disjointness over $K$. Thus

$$
L=ET=\mathbb Q_2(\alpha,i,\gamma),\qquad
[L:\mathbb Q_2]=4\cdot3\cdot2=24.
\tag{2.9}
$$

As a compositum of splitting fields, $L/\mathbb Q_2$ is Galois. Restriction identifies its Galois group with the pairs of automorphisms of $E,T$ agreeing on $K$. In particular, $F_E,F_T$ agree on $K$ and define one automorphism $F$ of $L$. Their squares are identities, so $F^2=1$, and $F(u)=-u$ makes $F$ nonidentity.

Restriction over $K$ identifies

$$
\operatorname{Gal}(L/K)
=\operatorname{Gal}(E/K)\times\operatorname{Gal}(T/K)
\cong C_2^2\times C_3.
$$

Fix a primitive complex cube root $\omega$ and label $\tau^k$ by $z=\omega^k$. The $2$-adic root $\zeta$ defines the field automorphism $\tau$; the complex root $\omega$ only labels that cyclic factor for the matrices. Equations (2.6) and (2.8) give, on these actual source automorphisms,

$$
F(s,t,z)F^{-1}=(t,s,z^{-1}).
\tag{2.10}
$$

The restriction to $K$ has kernel $N$ and is split by $F$. Consequently every source automorphism has the unique form $nF^\epsilon$, and (1.2) is its multiplication. This proves the asserted identification with $G_*$ directly from (1.3). The abelian realization in [*Toral character triples*, §3](TORAL_CHARACTER_TRIPLE_SOURCE_SUPPORT.md#3-actual-mathbb-q_2-quotients) realizes the smaller source $N$; it is not the realization used in (2.9).

## 3. Faithful homomorphisms with reducible non-toral images

For $j=1,2$, $D_j:N\to GL_3(\mathbb C)$ is an ordinary homomorphism, and

$$
S^2=I,\qquad
SD_j(s,t,z)S^{-1}=D_j(t,s,z^{-1}).
\tag{3.1}
$$

Thus (1.2) and (3.1) prove directly that

$$
R_j(nF^\epsilon)=D_j(n)S^\epsilon
\tag{3.2}
$$

is a homomorphism to $GL_3(\mathbb C)$. Its projectivization is (1.4). In particular, ordinary lifts are constructed here for these two maps.

To check projective injectivity on $N$, if $D_j(s,t,z)$ is scalar, its first entry makes the scalar $1$. Its other entries imply $z\in\mu_3\cap\{1,-1\}=\{1\}$, and then $s=t=1$. This is the inherited faithfulness calculation of [*Toral character triples*, §2.6](TORAL_CHARACTER_TRIPLE_SOURCE_SUPPORT.md#26-the-supporting-twelve-element-group). For an element $nF$, the last two coordinates of (3.2) form an invertible off-diagonal block, so $R_j(nF)$ is not scalar. Hence both $\rho_j$ have trivial kernel on all of $G_*$.

Every $R_j(g)$ fixes $e_1$. Any matrix in the full inverse image of $\rho_j(G_*)$ is a nonzero scalar multiple of some $R_j(g)$, so that full inverse image preserves $\mathbb Ce_1$. This is a nonzero proper subspace, proving reducibility of both maps in Definition 1.1.

The sign changes $v_{-1,1}$ and $v_{1,-1}$ are distinct and exchanged by $F$, so $G_*$ is nonabelian. Its two projective images are isomorphic to it by injectivity. An algebraic torus is abelian; neither image can therefore be contained in a torus. Both images are non-toral.

## 4. Element-conjugacy and the obstruction to a common conjugator

### 4.1. Every element of the diagonal subgroup

The inherited matching identities [*Toral character triples*, §2.6, equation (2.11)](TORAL_CHARACTER_TRIPLE_SOURCE_SUPPORT.md#26-the-supporting-twelve-element-group) are

$$
\begin{array}{c|c}
\text{sign condition}&\text{identity}\\\hline
s=t&D_2=P_{23}D_1P_{23}^{-1}\\
(s,t)=(1,-1)&D_2=z^{-1}P_{12}D_1P_{12}^{-1}\\
(s,t)=(-1,1)&D_2=zP_{13}D_1P_{13}^{-1}.
\end{array}
\tag{4.1}
$$

For the second row the right side has diagonal entries $(1,z^{-1},-z^{-2})=(1,z^{-1},-z)$; for the third they are $(1,-z^2,z)=(1,-z^{-1},z)$. The first row follows by exchanging the last two entries when $s=t$. These use only $z^3=1$ and exhaust all four sign choices. Therefore (4.1) proves projective conjugacy on each same $n\in N$, including $z=1$ and any repeated eigenvalues.

### 4.2. Every element of the other coset

For $n=(s,t,z)$ the lower blocks of $R_1(nF),R_2(nF)$ are respectively

$$
B_1=\begin{pmatrix}0&sz\\tz^{-1}&0\end{pmatrix},
\qquad
B_2=\begin{pmatrix}0&sz^{-1}\\tz&0\end{pmatrix}.
$$

Both have characteristic polynomial $X^2-st$. Since $st\in\{1,-1\}$, this polynomial has two distinct complex roots. Both blocks are diagonalizable with the same eigenvalue multiset, so there exists $C\in GL_2(\mathbb C)$ with $B_2=CB_1C^{-1}$. The matrix $\operatorname{diag}(1,C)$ conjugates $R_1(nF)$ to $R_2(nF)$. This proves even ordinary conjugacy on this coset, including cases in which a lower-block eigenvalue equals the first eigenvalue $1$. Together with §4.1, it proves element-conjugacy on the entire original group.

### 4.3. No single projective conjugator

Suppose there were $h=[H]\in PGL_3(\mathbb C)$ with

$$
\rho_2(g)=h\rho_1(g)h^{-1}\qquad(g\in G_*),
$$

where $H\in GL_3(\mathbb C)$. Restrict to

$$
V=\{(s,t,1):s,t\in\{1,-1\}\}\subset N.
$$

For $v=(s,t,1)$, both ordinary values equal $D(v)=\operatorname{diag}(1,s,t)$. There is a scalar $c_v\in\mathbb C^\times$ such that

$$
D(v)=c_vHD(v)H^{-1}.
$$

Squaring the equality gives $c_v^2=1$; taking determinants gives $c_v^3=1$. Hence $c_v=1$ for every $v$, and $H$ centralizes $D(V)$. The three coordinate characters $1,s,t$ of $V$ are pairwise distinct. Their common character spaces are precisely the three coordinate lines, so $H$ preserves each line and is diagonal.

It follows that $H$ commutes with every $D_1(n)$. Take $n=(1,1,\omega)$, where $\omega$ is primitive. The required projective equality would then give

$$
\operatorname{diag}(1,\omega^{-1},\omega)
=c\operatorname{diag}(1,\omega,\omega^{-1}).
$$

The first entry forces $c=1$, and the second forces $\omega^{-1}=\omega$, contrary to the order of $\omega$. This is the inherited obstruction on $N$, expressed for an arbitrary projective conjugator as in [*Toral character triples*, §1 and §2.6](TORAL_CHARACTER_TRIPLE_SOURCE_SUPPORT.md#1-characters-and-projective-matching). No common conjugator exists on $G_*$, completing the proof of Theorem 1.3. ∎

**Corollary 4.2 (Failure of reducible non-toral rigidity).** The following universal statement is false: for every finite Galois extension $M/\mathbb Q_2$, every pair of injective homomorphisms $\sigma_1,\sigma_2:\operatorname{Gal}(M/\mathbb Q_2)\to PGL_3(\mathbb C)$ such that $\sigma_1$ is reducible with non-toral image and $\sigma_1,\sigma_2$ are element-conjugate is globally conjugate.

Proof. Take $M=L$ and $\sigma_j=\rho_j$ from Theorem 1.3. Both maps even satisfy the reducibility and non-torality conditions. The projectively irreducible hypothesis in [*Irreducible projective rigidity over the dyadic local field*, Theorem 1.2](LOCAL_Q2_IRREDUCIBLE_PROJECTIVE_RIGIDITY.md#1-the-fixed-source-comparison) is absent here, so that theorem is not an implication applicable to this pair. ∎

## 追加锚（本行以下为增补区）
