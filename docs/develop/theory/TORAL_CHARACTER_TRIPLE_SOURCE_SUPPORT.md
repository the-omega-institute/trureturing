# Toral character triples: complete source support

## 1. Characters and projective matching

**Definition 1.1 (Character triples).** Write $C_n$ for a cyclic group of order $n$, with $C_1$ trivial, and $\mu_n$ for the complex $n$th roots of unity. For a finite abelian group $A$, a character is a homomorphism $A\to\mathbb C^\times$. A character triple $\chi=(\chi_1,\chi_2,\chi_3)$ defines

$$
D_\chi(g)=\operatorname{diag}(\chi_1(g),\chi_2(g),\chi_3(g)),
\qquad
\overline\chi(g)=[D_\chi(g)]\in PGL_3(\mathbb C).
$$

The triple is *projectively faithful* if $\overline\chi$ is injective, equivalently

$$
\ker(\chi_2/\chi_1)\cap\ker(\chi_3/\chi_1)=\{1\}.
$$

Two triples $\chi,\psi$ are *pointwise matched* if, for every $g\in A$, there exist $\lambda_g\in\mathbb C^\times$ and $\pi_g\in S_3$ such that

$$
\psi_i(g)=\lambda_g\chi_{\pi_g(i)}(g)
\qquad(1\le i\le3).
\tag{1.1}
$$

They are *globally matched* if there exist one character $\eta$ of $A$ and one permutation $\pi\in S_3$ such that

$$
\psi_i=\eta\chi_{\pi(i)}
\qquad(1\le i\le3).
\tag{1.2}
$$

The choices in (1.1) need not vary coherently with $g$. A group *supports* such triples if it admits two projectively faithful, pointwise matched triples that are not globally matched.

These definitions describe conjugacy of toral homomorphisms. Every homomorphism into the diagonal torus of $PGL_3(\mathbb C)$ has a lift $(1,\alpha,\beta)$ by characters, since that torus is isomorphic to $(\mathbb C^\times)^2$. Images contained in arbitrary conjugate tori can first be put into this form separately. Two diagonal matrices have conjugate projective classes exactly when their eigenvalue multisets differ by a scalar, giving (1.1), including repeated eigenvalues.

Global projective conjugacy is equivalent to (1.2). Indeed, if one invertible matrix $H$ implements it, choose scalars $\eta(g)$ with

$$
D_\psi(g)=\eta(g)H D_\chi(g)H^{-1}.
$$

Multiplication at $g,h,gh$ gives $\eta(gh)=\eta(g)\eta(h)$. The resulting isomorphism between the ordinary representations $D_\psi$ and $\eta D_\chi$ equates their character multiplicities, hence their three characters up to one permutation. Conversely, (1.2) supplies a fixed permutation matrix as projective conjugator. The character-multiplicity assertion is also proved explicitly in §2.1 below. This is the finite diagonal instance of the projective-equivalence and ordinary-character interfaces in [1, §2.2, (2.2)] and [2, Proposition 2.1]; no connected-source hypothesis is used.

Multiplying all coordinates of either triple by a character, or permuting its coordinates, preserves projective faithfulness, pointwise matching and global matching. Pointwise matched triples have the same projective kernel: at any given element, one triple has three equal values exactly when the other does.

## 2. Complete support theorem

**Theorem 2.1 (Complete faithful toral source support).** Let

$$
A=C_{2^a}\times C_{2^b m},
\qquad 0\le a\le b,\qquad m\ge1\text{ odd}.
$$

Then $A$ supports projectively faithful, pointwise matched but not globally matched character triples if and only if

$$
(a,b,m)=(1,1,3).
$$

Thus the sole supporting isomorphism type in this family is $C_2\times C_6\cong C_2^2\times C_3$.

Proof. Decompose $A=P\times O$, where $P=C_{2^a}\times C_{2^b}$ and $O=C_m$. The following arguments cover all parameters. The odd-factor, restriction and witness arguments reproduce the inherited finite-character results [5–7] in full. Determinant normalization and character orthogonality are reused ingredients; the regular-element compatibility in §2.5 supplies the exclusion at higher powers of two.

### 2.1. Scalar normalization and character multiplicities

First, characters of any finite abelian group $F$ satisfy

$$
\frac1{|F|}\sum_{x\in F}\rho(x)\tau(x)^{-1}
=\begin{cases}1&\rho=\tau,\\0&\rho\ne\tau.\end{cases}
\tag{2.1}
$$

To see this, the sum $S$ of a nontrivial character $\kappa$ obeys $S=\kappa(y)S$ after translation by any $y$. Choose $y$ with $\kappa(y)\ne1$ to obtain $S=0$. The trivial-character sum is $|F|$. Consequently, equality of sums of characters on every element gives equality of their multiplicities: multiply the equality by $\rho^{-1}$, sum, and apply (2.1). In particular, equal sums of two triples give one fixed permutation matching their characters, even when characters repeat.

On a group $P$ of exponent $2^b$, pointwise projective scalars can be removed by a character twist. Here is a determinant-one version needed for restriction detection. Choose an integer $r$ with

$$
3r+1\equiv0\pmod{2^b}.
$$

For $\theta=\chi,\psi$, define characters of $P\times O$ by

$$
c_\theta(po)=\left(\prod_{i=1}^3\theta_i(p)\right)^r,
\qquad
X_i=c_\chi\chi_i,\quad Y_i=c_\psi\psi_i.
\tag{2.2}
$$

Then $\prod_iX_i(p)=\prod_iY_i(p)=1$ on $P$. Any pointwise scalar at $p$ is a ratio of $2^b$th roots of unity, so lies in $\mu_{2^b}$; taking determinants gives its cube equal to $1$. Since $\gcd(3,2^b)=1$, the scalar is $1$. Thus the multisets $\{X_i(p)\}$ and $\{Y_i(p)\}$ agree for every $p$. Equation (2.1) gives a single permutation $\sigma$ with

$$
Y_i|_P=X_{\sigma(i)}|_P.
\tag{2.3}
$$

### 2.2. Cyclic sources

If $a=0$, $A$ is cyclic, of order $N=2^b m$. Let $g$ be a generator. Choose a scalar $\lambda$ and permutation $\pi$ in (1.1) at $g$. The scalar is a ratio of $N$th roots of unity, so $\lambda^N=1$. It therefore defines a character $\eta$ with $\eta(g)=\lambda$. Equality at the generator implies $\psi_i=\eta\chi_{\pi(i)}$ on all of $A$. This also handles $N=1$, and requires no faithfulness assumption. Hence cyclic sources do not support the required triples.

### 2.3. The odd-factor constraint on $C_2^2\times C_m$

Let $V=C_2^2$. The three restrictions of a projectively faithful triple to $V$ are pairwise distinct. If two coincide, their common ratio is trivial; the only other independent coordinate ratio has values in $\{\pm1\}$, whose kernel on $V$ has at least two elements. A nonidentity element of that kernel is in the projective kernel, a contradiction.

Fix independent characters $\alpha,\beta$ of $V$. Its character group has four elements, and every three-element subset is a translate of $\{1,\alpha,\beta\}$. Independently twist and reorder both triples so that their restrictions are $(1,\alpha,\beta)$. Divide each triple by the character of $O$ in its first coordinate. Identifying $O$ with $\mu_m$, the triples become

$$
\chi(s,t,z)=(1,sz^u,tz^v),\qquad
\psi(s,t,z)=(1,sz^w,tz^x),
\tag{2.4}
$$

where $s=\alpha(g)$, $t=\beta(g)$ range independently over $\{\pm1\}$ and $u,v,w,x\in\mathbb Z/m\mathbb Z$. If the pair is not globally matched, then $(w,x)\ne(u,v)$.

Take a primitive $m$th root $\zeta$; for $m=1$, take $\zeta=1$. At each of the sign patterns $(-1,-1),(-1,1),(1,-1)$, the coordinate values lie in the disjoint cosets $\mu_m$ and $-\mu_m$, with multiplicities $1,2$ in some order. Every matching scalar is a ratio of such values and lies in $\mu_m\cup(-\mu_m)$. A scalar in $-\mu_m$ would exchange the two unequal multiplicities. Hence the scalar lies in $\mu_m$ and the permutation preserves the two cosets, fixing the coordinate in the singleton coset.

The remaining two coordinates are either fixed or interchanged. The identity permutation would force scalar $1$ from the first coordinate, and then $(w,x)=(u,v)$, contrary to the assumption. Interchanging the other coordinates gives, in $\mathbb Z/m\mathbb Z$,

$$
\begin{array}{c|c}
(s,t)&(w,x)\\\hline
(-1,-1)&(v,u)\\
(-1,1)&(u-v,-v)\\
(1,-1)&(-u,v-u).
\end{array}
\tag{2.5}
$$

For example, at $(-1,1)$ the first and third coordinates interchange, giving scalar $\zeta^{-v}$, and hence $w=u-v$, $x=-v$. The other rows follow by the same coordinate equalities; no distinct-eigenvalue assumption is required.

Combining the rows yields $u=-v$ and $3v=0$. If $v=0$, all four exponents vanish, contradicting $(w,x)\ne(u,v)$. Thus $v$ has additive order exactly $3$. The first triple on $O$ is now

$$
z\longmapsto[\operatorname{diag}(1,z^{-v},z^v)].
$$

Its kernel is the kernel of the character $z\mapsto z^v$, whose order is $3$. Projective faithfulness on $O$ therefore forces $m=3$. This proves necessity for every odd $m$, including exclusion of $m=1$.

### 2.4. Restriction detects global matching

Suppose $1\le a\le b$, and put

$$
T=P[2]=\{p\in P:p^2=1\}\cong C_2^2,
\qquad B=T\times O.
$$

For a projectively faithful pointwise matched pair on $A$, global matching on $B$ implies global matching on $A$. To prove this, use the normalization $X,Y$ in (2.2). A matching on $B$ takes the form

$$
Y_i|_B=\epsilon X_{\tau(i)}|_B
\tag{2.6}
$$

with a character $\epsilon$ of $B$ and a permutation $\tau$. On $T$, multiplying the three equalities gives $\epsilon(t)^3=1$. Also $\epsilon(t)^2=1$, so $\epsilon|_T=1$.

Projective faithfulness makes $X_1|_T,X_2|_T,X_3|_T$ pairwise distinct, by the kernel argument of §2.3. Comparing (2.3) and (2.6) on $T$ therefore forces $\sigma=\tau$. Extend the character $\epsilon|_O$ trivially over $P$, writing

$$
\eta'(po)=\epsilon(o).
$$

Then, for every $p\in P,o\in O$,

$$
\begin{aligned}
Y_i(po)
&=Y_i(p)Y_i(o)\\
&=X_{\sigma(i)}(p)\epsilon(o)X_{\sigma(i)}(o)\\
&=\eta'(po)X_{\sigma(i)}(po).
\end{aligned}
$$

Undoing (2.2) gives the common character $c_\psi^{-1}\eta'c_\chi$ and the common permutation $\sigma$ on $A$.

Restriction to a subgroup preserves pointwise matching and projective faithfulness. By contraposition, a non-globally-matched pair on $A$ restricts to one on $B$. Since $B\cong C_2^2\times C_m$, §2.3 forces $m=3$. In particular, for $b\ge2$ only this odd factor remains to be excluded. This restriction argument does not assert that a prescribed matching character on $B$ extends to $A$.

### 2.5. A regular element and compatibility at higher powers of two

The regular-element assertion used here is the following elementary statement. If

$$
H\le\mu_{2^b}^2,\qquad
H\cong C_{2^a}\times C_{2^b},\qquad
1\le a\le b,\quad b\ge2,
$$

then $H$ contains $(x,y)$ with $1,x,y$ pairwise distinct. Indeed, $H$ is noncyclic and has an element $h=(x,y)$ of order at least $4$. The order of an element of a product of two finite $2$-groups is the maximum of its coordinate orders. Swap the coordinates if necessary so that $x$ has order at least $4$.

If $y=1$, choose $k=(u,v)\in H$ with $v\ne1$. Such a $k$ exists, since otherwise $H$ would lie in the cyclic first-coordinate subgroup. In $h^n k=(x^n u,v)$, the first coordinate takes at least four values, and only $1$ and $v$ are forbidden.

If $y\ne1$ and $x\ne y$, $h$ itself has the required property. In the remaining case $x=y$, choose $k=(u,v)$ with $r=u/v\ne1$. Otherwise $H$ would lie in the cyclic diagonal subgroup. Write $h^n k=(rt,t)$, with $t=x^n v$. There are at least four possible $t$, and only $t=1$ and $t=r^{-1}$ are forbidden. The ratio $r\ne1$ already ensures distinct coordinates. This proves the assertion in all cases.

Now let $A=P\times C_3$ with $1\le a\le b$ and $b\ge2$, and take any projectively faithful pointwise matched pair $\chi,\psi$. We show that it is globally matched.

Let

$$
D=\frac{\prod_i\psi_i}{\prod_i\chi_i},
$$

a character of $A$, and choose an integer $q$ with $3q\equiv1\pmod{2^b}$. At $p\in P$, every matching scalar belongs to $\mu_{2^b}$ and has cube $D(p)$. Cubing is an automorphism of $\mu_{2^b}$, so that scalar is uniquely

$$
\eta(p)=D(p)^q.
$$

This is a character of $P$. Extend it trivially across $C_3$ and twist $\psi$ by $\eta^{-1}$. The two triples now have identical value multisets on $P$. By (2.1), a single relabeling makes their restricted characters identical. Write the resulting triples as

$$
\chi_i(p,z)=c_i(p)d_i(z),\qquad
\psi_i(p,z)=c_i(p)e_i(z),
\tag{2.7}
$$

where $c_i$ are characters of $P$ and $d_i,e_i$ are characters of $C_3$.

After these operations the determinant quotient is trivial on $P$. At a mixed element $(p,z)$, every pointwise scalar $\lambda$ is a ratio of character values, so belongs to $\mu_{3\cdot2^b}$. Its cube is the determinant quotient at $(p,z)$, which has odd order. In the unique primary decomposition $\lambda=\lambda_2\lambda_3$, with $\lambda_2\in\mu_{2^b}$ and $\lambda_3\in\mu_3$, this implies $\lambda_2^3=1$. Therefore $\lambda_2=1$ and

$$
\lambda\in\mu_3.
\tag{2.8}
$$

The finite-order bound on $\lambda$ is essential here; a cube-root equation alone would not imply (2.8).

Set $\alpha=c_2/c_1$, $\beta=c_3/c_1$. Projective faithfulness on $P$ says that $p\mapsto(\alpha(p),\beta(p))$ is injective. Its image has precisely the type of $H$ just considered. Hence there is one $p_0\in P$ for which

$$
c_1(p_0),\quad c_2(p_0),\quad c_3(p_0)
\quad\text{are pairwise distinct}.
\tag{2.9}
$$

Keep this same $p_0$ for every $z\in C_3$. A pointwise match at $(p_0,z)$ has the form

$$
c_i(p_0)e_i(z)
=\lambda_z c_{\pi_z(i)}(p_0)d_{\pi_z(i)}(z).
$$

Taking $2$-primary parts and using (2.8) gives $c_i(p_0)=c_{\pi_z(i)}(p_0)$. By (2.9), $\pi_z$ is the identity. Thus $e_i(z)/d_i(z)$ is independent of $i$ for every $z$. The character

$$
\rho=e_1/d_1
$$

therefore equals $e_i/d_i$ for all three coordinates. Equation (2.7) gives a common character twist on $P\times C_3$. Undo the fixed relabeling and the earlier twist to obtain a global match for the original triples.

This compatibility argument applies to arbitrary triples, not just to a chosen extension of the example below. It excludes every remaining higher-$2$-power parameter case.

### 2.6. The supporting twelve-element group

Let $\omega$ be a primitive cube root of unity and set

$$
\Gamma=\{\pm1\}\times\{\pm1\}\times\mu_3
\cong C_2^2\times C_3.
$$

Define triples by the diagonal matrices

$$
D_1(s,t,z)=\operatorname{diag}(1,sz,tz^{-1}),\qquad
D_2(s,t,z)=\operatorname{diag}(1,sz^{-1},tz).
\tag{2.10}
$$

Both are projectively faithful. If one matrix is scalar, its first coordinate makes that scalar $1$. The other coordinates then force $z\in\mu_3\cap\{\pm1\}=\{1\}$, and subsequently $s=t=1$.

Let $P_{ij}$ exchange coordinates $i,j$. The following identities prove pointwise matching and exhaust all sign patterns:

$$
\begin{array}{c|c}
\text{condition}&\text{matrix identity}\\\hline
s=t&D_2=P_{23}D_1P_{23}^{-1}\\
(s,t)=(1,-1)&D_2=z^{-1}P_{12}D_1P_{12}^{-1}\\
(s,t)=(-1,1)&D_2=zP_{13}D_1P_{13}^{-1}.
\end{array}
\tag{2.11}
$$

There is no global match. On $V=\{\pm1\}^2\times\{1\}$ both triples restrict to $(1,s,t)$. If $\psi_i=\epsilon\chi_{\pi(i)}$ globally, multiplying the restrictions on $V$ gives $\epsilon(v)^3=1$, while $\epsilon(v)^2=1$; hence $\epsilon|_V=1$. The three characters $1,s,t$ of $V$ are distinct, so $\pi$ must be the identity. The first coordinate then forces $\epsilon=1$ on all of $\Gamma$. The second coordinates at $(1,1,\omega)$ would give $\omega=\omega^{-1}$, a contradiction. This proves sufficiency.

### 2.7. Exhaustion of the parameter cases

Section 2.2 excludes all $a=0$. For $a\ge1$, the ordering $a\le b$ implies $b\ge1$. If $b=1$, necessarily $a=1$, and §§2.3 and 2.6 give precisely $m=3$. If $b\ge2$, §2.4 first forces $m=3$, and §2.5 excludes that value. These cases exhaust every parameter in the theorem. ∎

**Corollary 2.2 (Regular-element compatibility).** Let $P\cong C_{2^a}\times C_{2^b}$ with $1\le a\le b$ and $b\ge2$. Any pointwise matched character triples on $P\times C_3$, one of which is projectively faithful, admit one common character twist and one common permutation on the whole group. After matching their restrictions on $P$, a single element of $P$ with three distinct coordinate values forces compatibility for every element of $C_3$.

Proof. Pointwise matching makes the projective kernels equal, so both triples are projectively faithful. The construction in §2.5 supplies the regular element, the fixed permutation and the common character explicitly. ∎

**Corollary 2.3 (Obstruction to faithful extension).** Let $P$ be as in Corollary 2.2 and $B=P[2]\times C_3$. A projectively faithful pointwise matched but not globally matched pair on $B$ cannot be the restriction of a projectively faithful pointwise matched pair on $P\times C_3$. The same holds if the two prescribed restrictions are independently twisted by characters or permuted.

Proof. Corollary 2.2 makes any such extended pair globally matched. Restriction of its common character and permutation gives a global match on $B$, a contradiction. Independent twists and permutations preserve the existence of a global match. ∎

## 3. Actual $\mathbb Q_2$ quotients

**Corollary 3.1 (The local-class-field source interface).** Among finite abelian quotients of $G_{\mathbb Q_2}$ admitting a faithful embedding into a torus of $PGL_3(\mathbb C)$, the isomorphism types are exactly

$$
C_{2^a}\times C_{2^b m},\qquad
0\le a\le b,\quad m\ge1\text{ odd}.
\tag{3.1}
$$

Every type in (3.1) is an actual finite continuous quotient. Among them, the ones supporting the character-triple pairs of Theorem 2.1 consist exactly of $C_2\times C_6$. In particular there are continuous, element-conjugate but not globally conjugate homomorphisms $W_{\mathbb Q_2}\to PGL_3(\mathbb C)$ with image of order $12$ in a torus.

Proof. Local reciprocity and the local existence theorem identify finite abelian Galois quotients with finite continuous quotients of $\mathbb Q_2^\times$. The standard decomposition is

$$
\mathbb Q_2^\times\cong
2^{\mathbb Z}\times\{\pm1\}\times(1+4\mathbb Z_2)
\cong\mathbb Z\times C_2\times\mathbb Z_2.
$$

Here the last isomorphism uses the $2$-adic logarithm on $1+4\mathbb Z_2$. Equivalently, the profinite completion is

$$
G_{\mathbb Q_2}^{\mathrm{ab}}
\cong\widehat{\mathbb Z}\times C_2\times\mathbb Z_2.
\tag{3.2}
$$

These are the local-class-field and unit-group facts of [3, Chapter I, Theorems 1.1 and 1.4, paragraph 1.10, and Appendix A, Examples A.5(a),(d)]. In particular, the odd-order part of any finite abelian quotient is cyclic: only the $\widehat{\mathbb Z}$ factor contributes to it.

A finite subgroup of a two-dimensional complex torus has at most two cyclic invariant factors. Indeed, if $N$ is its exponent, it embeds in $\mu_N^2$, and the classification of finite abelian groups gives this bound. Conversely, any finite abelian group with at most two cyclic invariant factors embeds in $(\mathbb C^\times)^2$. Combining the bound with the cyclic odd part gives precisely (3.1), using the Chinese remainder theorem. Each displayed group is a quotient of (3.2): map $\mathbb Z_2$ onto $C_{2^a}$ and $\widehat{\mathbb Z}$ onto $C_{2^b m}$, and kill the $C_2$ factor. Local existence then supplies its finite abelian extension. Theorem 2.1 gives the support assertion independently of this realization argument.

For an explicit realization of the supporting group, take

$$
E=\mathbb Q_2(\sqrt2,\sqrt{-1}),\qquad
U=\mathbb Q_2(\zeta_7),\qquad L=EU.
$$

The elements $2$ and $-2$ have odd $2$-adic valuation and are not squares. The element $-1$ is not a square either, since every odd square is $1$ modulo $8$. Thus $2$ and $-1$ are independent square classes, and $E/\mathbb Q_2$ is biquadratic with group $C_2^2$. The order of $2$ modulo $7$ is $3$, so $U/\mathbb Q_2$ is the unramified cubic extension, with cyclic group $C_3$ [3, Chapter I, §1 and Example I.3.13(a)]. Their coprime degrees give $E\cap U=\mathbb Q_2$, and hence

$$
\operatorname{Gal}(L/\mathbb Q_2)
\cong C_2^2\times C_3\cong\Gamma.
$$

The natural continuous map from $W_{\mathbb Q_2}$ to $G_{\mathbb Q_2}$ has dense image, so its composite with this finite quotient is a continuous surjection $q:W_{\mathbb Q_2}\twoheadrightarrow\Gamma$; see [4, Lemmas 3.1–3.2 and Theorem 4.1]. Compose $q$ with the two maps (2.10). Surjectivity preserves their order-$12$ images and transfers the nonexistence of a common conjugator, while (2.11) preserves element-conjugacy. ∎

## 4. Mathematical scope and references

Theorem 2.1 classifies supporting source groups for faithful toral character triples in its specified family. It does not classify all ordered pairs on the supporting group, all finite projective images, or nonabelian images. Corollary 3.1 supplies a local-class-field realization of the source groups; it asserts no global Langlands correspondence or additional correspondence between these character triples and automata or learning models.

The finite-character support theorem and regular-element compatibility are presented as repository-derived deductions, with ordinary proofs above. Exact equivalence of the complete support statement to a published theorem has not been established here; no priority or current-open-status claim follows. The normalization, orthogonality and explicit witness are inherited ingredients, not additional discoveries. The citations [1–4] support the stated representation-theoretic and local-field interfaces, not a claim of novelty for Theorem 2.1. The mathematical arguments from [5–7] are included above, so none is an unstated premise accessible only through those citations.

1. Morris and Jones, *Projective Representations of Generalized Symmetric Groups*, Séminaire Lotharingien de Combinatoire **50** (2003), B50b, §2.2, equation (2.2). [Full text](https://www.mat.univie.ac.at/~slc/wpapers/s50morris.pdf). Fixed-matrix projective equivalence; for homomorphic ordinary lifts its scalar function is a character, as proved in §1.
2. Fang, Han and Sun, *Conjugacy and element-conjugacy of homomorphisms of compact Lie groups*, Pacific Journal of Mathematics **283** (2016), 75–83, Proposition 2.1. [DOI: 10.2140/pjm.2016.283.75](https://doi.org/10.2140/pjm.2016.283.75); [full text](https://msp.org/pjm/2016/283-1/pjm-v283-n1-p05-s.pdf). Ordinary-character equivalence for compact Hausdorff sources. The connected-source hypothesis of their separate Lemma 3.1 is not used for the finite sources here.
3. J. S. Milne, *Class Field Theory*, version 4.03, Chapter I and Appendix A, at the locations cited in §3. [Full text](https://www.jmilne.org/math/CourseNotes/CFT.pdf). Local reciprocity, local existence, unramified extensions and the multiplicative-group decomposition.
4. Brian Conrad, *Profinite and Weil groups*, Lemmas 3.1–3.2 and Theorem 4.1. [Full text](https://virtualmath1.stanford.edu/~conrad/249BW09Page/handouts/profinite.pdf). Weil-group topology and the finite-quotient interface.
5. trureturing, *Odd cyclic factor support for faithful character triples on $C_2^2\times C_m$*. [Mathematical source](https://github.com/the-omega-institute/trureturing/issues/20457#issuecomment-6352744367). The necessity argument reproduced in §2.3.
6. trureturing, *Restriction detection for faithful projective character triples*. [Mathematical source](https://github.com/the-omega-institute/trureturing/issues/20467#issuecomment-6353139024). The determinant normalization and restriction argument reproduced in §§2.1 and 2.4.
7. trureturing, *A twelve-element abelian toral construction over $\mathbb Q_2$*. [Mathematical source](https://github.com/the-omega-institute/trureturing/issues/20447#issuecomment-6352198106). The witness and explicit field realization reproduced in §§2.6 and 3.

## 追加锚（本行以下为增补区）
