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

## 5. Strict-degree rigidity below twenty-four

**Theorem 5.1 (Strict-degree reducible non-toral rigidity).** For every finite Galois extension $M/\mathbb Q_2$ with

$$
[M:\mathbb Q_2]<24,
$$

put $H=\operatorname{Gal}(M/\mathbb Q_2)$. Let

$$
\sigma_1,\sigma_2:H\longrightarrow PGL_3(\mathbb C)
$$

be injective homomorphisms. Assume that the full inverse image of $\sigma_1(H)$ in $GL_3(\mathbb C)$ preserves a nonzero proper complex subspace, that $\sigma_1(H)$ is contained in no algebraic torus, and that

$$
\forall g\in H\quad\exists h_g\in PGL_3(\mathbb C),
\qquad
\sigma_2(g)=h_g\sigma_1(g)h_g^{-1}.
\tag{5.1}
$$

Then there is one $h\in PGL_3(\mathbb C)$ such that

$$
\sigma_2(g)=h\sigma_1(g)h^{-1}\qquad(g\in H).
\tag{5.2}
$$

No reducibility, lift, or other additional hypothesis is imposed on $\sigma_2$.

**Proof.** We keep the original element $g\in H$ throughout. First, reducibility of the second map is forced. If $\sigma_2$ were projectively irreducible, then (5.1), which is symmetric in the two maps, would let us apply Theorem 1.2 of [*Irreducible projective rigidity over the dyadic local field*](LOCAL_Q2_IRREDUCIBLE_PROJECTIVE_RIGIDITY.md#1-the-fixed-source-comparison) with $\sigma_2$ as its first map and $\sigma_1$ as its second. Its hypotheses are exactly met: the source is the actual finite group $H=\operatorname{Gal}(M/\mathbb Q_2)$, both maps are injective, and the same source elements are compared. The resulting global conjugacy would preserve projective irreducibility, contradicting the assumed reducibility of $\sigma_1$. Thus $\sigma_2$ is reducible as well.

For $i=1,2$, let $\widetilde H_i$ be the inverse image of $\sigma_i(H)$ in $SL_3(\mathbb C)$. Since the projective image has order $|H|$, $\widetilde H_i$ is finite of order $3|H|$. The full inverse image in $GL_3(\mathbb C)$ consists of scalar multiples of $\widetilde H_i$, so it has exactly the same invariant subspaces. Reducibility therefore gives an invariant line or plane for $\widetilde H_i$. Average a positive definite Hermitian form over this finite group. The orthogonal complement is invariant too, and we obtain an invariant decomposition

$$
\mathbb C^3=L_i\oplus W_i,
\qquad \dim L_i=1,\quad \dim W_i=2.
$$

Choose a basis adapted to this decomposition. Every matrix representative of $\sigma_i(g)$ has the form $\operatorname{diag}(a,B)$ with $a\in\mathbb C^\times$ and $B\in GL_2(\mathbb C)$. Dividing by $a$ gives the projective representative

$$
R_i(g)=\operatorname{diag}(1,r_i(g)),
\qquad r_i(g)=a^{-1}B.
\tag{5.3}
$$

This representative is independent of the scalar used for the original lift. If representatives for $g$ and $h$ are multiplied, their product is a representative for $gh$ up to a scalar, and the scalar cancels in the ratio of the two blocks. Hence

$$
 r_i:H\longrightarrow GL_2(\mathbb C),\qquad R_i=1\oplus r_i,
\tag{5.4}
$$

are ordinary homomorphisms. This is a derived lift, not an assumption. If $r_i(g)=I_2$, then $R_i(g)=I_3$, so injectivity of $\sigma_i$ gives $g=1$; both $r_i$ are faithful.

The group $H$ is nonabelian. Indeed, if it were abelian, the finite commuting group $r_1(H)$ would be simultaneously diagonalizable, so $R_1(H)$ and hence $\sigma_1(H)$ would lie in a diagonal algebraic torus, contrary to the hypothesis. A reducible finite-dimensional representation of a finite group splits after the same averaging argument. Thus, if either faithful $r_i$ were reducible, it would be a direct sum of two characters and would embed $H$ into an abelian group. Therefore both $r_i$ are irreducible. The projectivizations of $R_1$ and $R_2$ are still element-conjugate by (5.1).

We will use the following elementary ordinary-character interface. If $U,V$ are finite-dimensional complex representations of a finite group with characters $\chi_U,\chi_V$, averaging the action on $\operatorname{Hom}(U,V)$ gives a projection whose trace is

$$
\frac1{|H|}\sum_{g\in H}\chi_V(g)\chi_U(g^{-1}).
\tag{5.5}
$$

For irreducible $U,V$, this dimension is $0$ or $1$: a nonzero intertwiner is an isomorphism, and an endomorphism of an irreducible representation is scalar because an eigenspace is invariant. Averaging also splits every representation into irreducibles. Consequently equal ordinary characters give isomorphic representations, with equal irreducible multiplicities. This is the ordinary-character step used below; it requires only finite-group semisimplicity and no projective lift beyond (5.4).

Suppose first that $3\nmid N$, where $N=|H|$. Choose $q\in\mathbb Z$ with

$$
3q+1\equiv0\pmod N.
$$

Write $d_i=\det R_i$. Define

$$
A_i(g)=d_i(g)^qR_i(g).
\tag{5.6}
$$

These are ordinary homomorphisms, $\det A_i(g)=1$, and $A_i(g)^N=I$. From projective element-conjugacy there are $C_g\in GL_3(\mathbb C)$ and $\zeta_g\in\mathbb C^\times$ with

$$
A_2(g)=\zeta_g C_gA_1(g)C_g^{-1}.
$$

Taking determinants and then $N$th powers gives

$$
\zeta_g^3=1,\qquad \zeta_g^N=1.
$$

Since $\gcd(3,N)=1$, $\zeta_g=1$. Thus $A_1(g)$ and $A_2(g)$ are ordinarily conjugate for every $g$, so their ordinary characters agree. The character interface just proved supplies one fixed $C$ with $A_2=C A_1 C^{-1}$. Projectivizing $C$ proves (5.2) in this case. The determinant normalization is legitimate precisely because the determinant twist is a character, the congruence makes the twist determinant one, and the coprimality removes the projective cube-root ambiguity.

It remains to treat the orders divisible by three. We first isolate the only representation-theoretic lemma needed for the cyclic cases.

**Lemma 5.2 (Cyclic normal subgroup of index two).** Let $K$ be a finite group with a cyclic normal subgroup $A$ of index two. Let $u_1,u_2:K\to GL_2(\mathbb C)$ be irreducible, and suppose the projective maps $1\oplus u_1$ and $1\oplus u_2$ are element-conjugate on the same elements of $K$. Then $u_1$ and $u_2$ are isomorphic.

**Proof.** If $A=1$, then $K$ is cyclic and has no irreducible two-dimensional complex representation, so assume $A=\langle a\rangle$ is nontrivial. Choose $t\notin A$ and let $\varphi$ be conjugation by $t$ on $A$. Since $t^2\in A$ and $A$ is abelian, $\varphi^2=1$.

The restriction of $u_i$ to $A$ is a sum of two characters. They are distinct: if one character occurred twice, $A$ would act by scalars, and an eigenline of $u_i(t)$ would be $K$-invariant. Since the two weight lines are distinct, irreducibility forces $t$ to interchange them; otherwise either line would be $K$-invariant. Write the weights as $\alpha_i,\beta_i$. They are interchanged by $\varphi$, so neither is the trivial character. Put

$$
S_i=\{1,\alpha_i,\beta_i\}\subset\widehat A.
$$

At the generator $a$, element-conjugacy of $1\oplus u_i$ identifies the three eigenvalues up to one scalar and a permutation. That scalar is a ratio of $|A|$th roots of unity, hence is $\lambda\in\mu_{|A|}$ and defines a character $\eta\in\widehat A$ by $\eta(a)=\lambda$. Since $A$ is cyclic, the equality at $a$ is equality of character sets:

$$
S_2=\eta S_1.
\tag{5.7}
$$

Let

$$
B=\{\kappa\in\widehat A:\kappa S_1=S_1\}.
$$

This is a subgroup of $\widehat A$ acting freely on the three-element set $S_1$, so $|B|$ is $1$ or $3$. Because $S_2$ is $\varphi$-invariant, (5.7) gives $\varphi(\eta)\eta^{-1}\in B$, where $\varphi$ acts on characters by precomposition with $\varphi^{-1}$. If $B=1$, then $\eta$ is $\varphi$-fixed. The only $\varphi$-fixed member of $S_1$ is $1$, while $1\in S_2$ implies $\eta^{-1}\in S_1$; hence $\eta=1$. If $|B|=3$, then $S_1$ is one coset of $B$, and because it contains $1$ it equals $B$. Again $1\in\eta S_1$ gives $\eta\in B$, so $\eta S_1=S_1$. In either case

$$
S_2=S_1.
$$

Removing the common character $1$, the restrictions $u_1|_A$ and $u_2|_A$ have the same two weights. Align their weight lines by one fixed change of basis. In that basis,

$$
 u_i(a)=\operatorname{diag}(\alpha(a),\beta(a)),
 \qquad
 u_i(t)=\begin{pmatrix}0&x_i\\y_i&0\end{pmatrix},
\qquad x_i y_i\ne0.
$$

The element $t^2$ lies in the abelian subgroup $A$ and commutes with $t$. Since $A$ and $t$ generate $K$, $t^2$ is central in $K$, so $u_i(t^2)$ is scalar by irreducibility; also $u_i(t)^2=u_i(t^2)$. Since the restrictions on $A$ have been aligned,

$$
 x_1y_1=x_2y_2.
$$

Conjugation by $\operatorname{diag}(x_2/x_1,1)$ centralizes the aligned diagonal action of $A$ and changes the matrix for $t$ in $u_1$ into the matrix for $t$ in $u_2$. Since $A$ and $t$ generate $K$, this is one intertwiner for $u_1$ and $u_2$. The corresponding block matrix $\operatorname{diag}(1,C)$ is a single projective conjugator for the three-dimensional maps. No automorphism of the source has been used. ∎

We now exhaust the orders divisible by three below $24$:

$$
3,6,9,12,15,18,21.
\tag{5.8}
$$

The groups of orders $3$ and $9$ are abelian, since every group of prime or prime-square order is abelian. For order $15$, both Sylow subgroups are normal: the Sylow counts are forced to be one. Their direct product is cyclic of order $15$. These three orders are impossible because $H$ was shown nonabelian.

At order $21$, the Sylow-seven subgroup $P$ is cyclic and normal. In a two-dimensional representation, the restriction to $P$ has either two distinct weight lines or one weight with multiplicity two. In the first case the quotient $H/P$, of order three, cannot interchange two lines, so it fixes both and the representation is reducible. In the second case $P$ acts by scalars. A Sylow-three subgroup $T$ is cyclic, $H=PT$, and an eigenline of $u(T)$ is invariant under both factors. Thus no irreducible two-dimensional representation exists at order $21$.

At order $6$, the Sylow-three subgroup is cyclic, normal, and of index two, so Lemma 5.2 applies.

Consider order $12$. If there are four Sylow-three subgroups, conjugation gives a transitive action on four objects. Its image in $S_4$ has order four or twelve, because it is transitive and its order divides $12$. A kernel of order three would be a normal Sylow-three subgroup, contrary to there being four; hence the action is faithful and $H$ is an index-two subgroup of $S_4$. The index-two subgroup is $A_4$: an index-two subgroup is the kernel of a nontrivial homomorphism $S_4\to C_2$, and the transpositions are conjugate and generate $S_4$, so this homomorphism is the sign map. The normal Klein four subgroup $V\triangleleft A_4$ has three nontrivial characters, cyclically permuted by a three-cycle. The multiset of two characters occurring in the restriction of a two-dimensional representation to $V$ is invariant under this cycle, so every nontrivial character has multiplicity zero. Hence $V$ acts trivially, and the representation is not faithful. This branch cannot occur.

If the Sylow-three subgroup $P$ at order $12$ is normal, it is cyclic of order three. If $H$ centralizes $P$, a Sylow-two subgroup has order four and is abelian, and $H=P\times S$ is abelian. Otherwise the conjugation map $H\to\operatorname{Aut}(P)=C_2$ is onto. Its kernel $A=C_H(P)$ has order six; it contains the central subgroup $P$ and a subgroup of order two, so it is their direct product $C_6$. Thus $A$ is cyclic, normal, and of index two, and Lemma 5.2 applies.

At order $18$, the Sylow-three subgroup $P$ has order nine and is normal, and Cauchy's theorem gives an involution $t$ outside $P$. Thus $H=P\rtimes\langle t\rangle$, with $P\cong C_9$ or $C_3\times C_3$. In the first case Lemma 5.2 applies. In the second case, use the faithful irreducible representation $r_1$ already derived. Its restriction to $P$ has two distinct weight characters $\alpha,\beta$, interchanged by $t$; one weight would make $P$ scalar and give a $t$-eigenline invariant under $H$. Faithfulness makes $\alpha,\beta$ independent in the two-dimensional $\mathbb F_3$ character space of $P$, since their common kernel is the kernel of $r_1|_P$. The involution induced by $t$ therefore interchanges a basis of that space. Its $+1$ and $-1$ eigenspaces, and likewise those of the dual action on $P$, are one-dimensional. Consequently

$$
P=P_+\times P_-,
$$

where $P_+$ and $P_-$ have order three, $t$ centralizes $P_+$ and inverts $P_-$. With generators $z$ of $P_+$ and $a$ of $P_-$,

$$
 z^3=a^3=t^2=1,
\qquad tat^{-1}=a^{-1},
\qquad [z,a]=[z,t]=1.
\tag{5.9}
$$

Thus the actual group forced by the representation is

$$
H\cong C_3\times S_3.
\tag{5.10}
$$

This is obtained from the admitted representation and does not assume a classification of groups of order eighteen.

It remains to compare the two representations in (5.10). The central element $z$ acts in each irreducible $r_i$ as a scalar $c_iI_2$, by the eigenspace argument in the character interface. Faithfulness makes $c_i$ a nontrivial cube root of unity. The eigenvalue multisets of $R_i(z)=1\oplus r_i(z)$ are $\{1,c_i,c_i\}$. Projective element-conjugacy at $z$ preserves the singleton and double multiplicities, so its matching scalar must be $1$ and

$$
 c_1=c_2.
\tag{5.11}
$$

Each restriction $r_i|_{S_3}$ is irreducible: an invariant line for $S_3$ would also be invariant under the scalar action of $z$, contradicting irreducibility of $r_i$. We can compare these restrictions directly. Let $S_3=\langle a,t\mid a^3=t^2=1,\ tat^{-1}=a^{-1}\rangle$. In an irreducible two-dimensional representation, $a$ cannot act as a scalar, since an eigenline of $t$ would then be invariant under all of $S_3$. Its two eigenvalues are distinct and their set is invariant under inversion, hence they are $\omega$ and $\omega^{-1}$ for a primitive cube root $\omega$. After aligning these two weight lines in the two restrictions, the matrix for $t$ is

$$
\begin{pmatrix}0&x_i\\y_i&0\end{pmatrix},
\qquad x_iy_i=1,
$$

because $t^2=1$. The same diagonal conjugation as in Lemma 5.2 aligns the two matrices. Therefore one matrix $C$ intertwines $r_1|_{S_3}$ and $r_2|_{S_3}$; (5.11) shows that it also intertwines the action of $z$. Hence $\operatorname{diag}(1,C)$ globally conjugates $R_1$ and $R_2$, and its projective class gives (5.2).

The orders in (5.8) are exhaustive, while all orders below $24$ that are coprime to three were handled by (5.6). The actual $\mathbb Q_2$ realization is used only to invoke Theorem 1.2 at the first step; the remaining argument is an elementary proof for every group and pair that reaches it. Both ordinary lifts in (5.4), the reducibility of the second map, and all conjugators were derived from the original hypotheses. This proves the theorem. ∎

**Corollary 5.3 (Sharpness of the bound).** Consider the universal statement obtained from Theorem 5.1 by replacing $[M:\mathbb Q_2]<24$ with $[M:\mathbb Q_2]\le B$, while retaining the same fixed-source quantifiers, injectivity of both maps, reducibility and non-torality only for the first map, and no extra condition on the second map. Theorem 5.1 proves this statement for every $B\le23$. Theorem 1.3 of this volume gives an actual degree-$24$ extension of $\mathbb Q_2$ and injective maps satisfying even reducibility and non-torality for both maps, which are element-conjugate but not globally conjugate. Therefore $24$ is the first degree at which this universal rigidity statement fails, and the strict bound $[M:\mathbb Q_2]<24$ is optimal. This uses the existing degree-$24$ construction without reproducing it and makes no assertion about degrees above $24$. ∎

## 追加锚（本行以下为增补区）
