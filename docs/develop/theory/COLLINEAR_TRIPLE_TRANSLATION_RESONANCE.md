# Resonant translation orbits of collinear triples

For a positive integer $n$, put $G_n=(\mathbb Z/n\mathbb Z)^2$. Let $\mathcal T_n$
be the set of unordered three-element subsets $S\subset G_n$ whose first
coordinates are pairwise distinct, whose second coordinates are pairwise
distinct, and whose difference determinant is zero. Write
$A(n)=|\mathcal T_n|$. This is the count in OEIS A146557.

**Theorem 1 (the three-torsion residue).** If $n=3m>0$, there is a
nonnegative integer $q$ such that

\[
  A(n)=n^2q+\frac{2n^2}{3}.
\]

Equivalently, $A(n)\equiv 2n^2/3\pmod{n^2}$. The divisor $n^2/3$ is
therefore always present, but the stronger divisibility by $n^2$ fails for
every positive multiple of three.

**Proof.** Translation by $G_n$ preserves all three defining conditions.
For $S\in\mathcal T_n$, let $H_S$ be its translation stabilizer. The action
of $H_S$ on the three points of $S$ is free: a translation fixing one point
is zero. Consequently $|H_S|$ divides three, so each translation orbit of
triples has size either $n^2$ or $n^2/3$.

Suppose $|H_S|=3$. Its action on $S$ is then transitive, hence $S$ is a
coset of $H_S$. Both coordinate projections of $H_S$ are injective, since
the corresponding coordinates in $S$ are distinct. The subgroup of
elements annihilated by three in $\mathbb Z/n\mathbb Z$ is
$\{0,m,2m\}$; its two nonzero elements are $m$ and $-m$. Thus $H_S$ is
one of exactly two subgroups,

\[
  H_+=\langle(m,m)\rangle,\qquad
  H_-=\langle(m,-m)\rangle.
\]

Every coset of either subgroup is an admissible triple: its two
coordinate projections are injective, and three points on a translate
of one cyclic direction have zero difference determinant. Its
translation stabilizer is precisely that subgroup. Translation acts
transitively on the cosets of each $H_\pm$, while the two families
cannot meet because a coset determines its stabilizer. Hence exactly
two orbits of $\mathcal T_n$ have size $n^2/3$. All remaining orbits
have size $n^2$, proving the formula. $\square$

**Theorem 2 (nonzero stabilizing directions).** Let $n=3m$ with $m>0$,
and let $S\in\mathcal T_n$. If $t\in G_n$ is nonzero and $S+t=S$, then

\[
  t\in\{(m,m),(m,2m),(2m,m),(2m,2m)\}.
\]

**Proof.** Translation by $t$ permutes $S$. Summing the three points
before and after translation gives $3t=0$. For either coordinate $x$
of $t$, this means $n$ divides $3x$ in any integer representative.
Since $n=3m$, the representative is a multiple of $m$; its range
$0\leq x<3m$ leaves only $0,m,2m$. Neither coordinate can be zero:
otherwise translating any point of $S$ gives a second point of $S$
with the same corresponding coordinate, unless the translation fixes
that point, in which case $t=0$. The four stated pairs are therefore
the only possibilities. $\square$

**Theorem 3 (finite translation stabilizers).** Let $G$ be a finite
abelian group, let $S\subseteq G$ be finite, and write
$H=\{t\in G:S+t=S\}$. For every $t\in H$,
$|S|t=0$, and $|H|$ divides $|S|$. If $|H|=|S|$ and $p\in S$, then
$S=p+H$. In particular, if $|S|=3$ and $H$ contains a nonzero element
$t$, then $|H|=3$ and
$S=\{p,p+t,p+2t\}$ for every $p\in S$.

**Proof.** Summing the elements of $S+t=S$ gives
$\sum_{p\in S}p=|S|t+\sum_{p\in S}p$, proving the first assertion.
The action of $H$ on $S$ is free, because a translation fixing one
point is zero. Its orbits therefore all have $|H|$ elements, proving
the divisibility. The orbit of $p$ is contained in $S$ and has
$|H|=|S|$ elements, so it is all of $S$. When $|S|=3$, the divisibility
and $t\ne0$ force $|H|=3$; the three powers $0,t,2t$ exhaust $H$.
$\square$

**Theorem 4 (three-torsion coordinates).** For $m>0$ and
$x\in\mathbb Z/(3m)\mathbb Z$,

\[
  3x=0\quad\Longleftrightarrow\quad x\in\{0,m,2m\}.
\]

**Proof.** For the standard representative $0\leq \bar x<3m$,
$3x=0$ means $3m\mid3\bar x$, equivalently $m\mid\bar x$.
The only such representatives are $0,m,2m$. Conversely, three times
each of these residues is divisible by $3m$. $\square$

**Theorem 5 (fixed-point census).** Let $n>0$ and let $t\in G_n$ have
$3t=0$ and two nonzero coordinates. Then translation by $t$ fixes exactly
$n^2/3$ members of $\mathcal T_n$. In particular, when $n=3m$ with $m>0$,
each of the four nonzero vectors in Theorem 2 fixes $n^2/3$ triples; every
other nonzero vector fixes none.

**Proof.** The cycle $C_t=\{0,t,2t\}$ has three distinct points in each
coordinate. Its difference determinants vanish, so $C_t\in\mathcal T_n$.
Translation by $t$ fixes $C_t$ and hence every translate of it. Conversely,
if $t$ fixes a triple $S$, the three-point translation-cycle theorem applied
at any $p\in S$ gives $S=p+C_t$. Thus the fixed triples form precisely one
translation orbit. The stabilizer of $C_t$ has order dividing three and
contains the nonzero element $t$, so its order is three. Orbit-stabilizer
therefore gives $n^2/3$ fixed triples. For $n=3m$, Theorems 2 and 4 rule out
all other nonzero fixing vectors. $\square$

**Corollary 6 (Burnside form of Theorem 1).** If $n=3m$ with $m>0$ and
$O(n)$ is the number of translation orbits on $\mathcal T_n$, then

\[
  A(n)+4\frac{n^2}{3}=n^2 O(n),\qquad O(n)\ge2.
\]

**Proof.** In Burnside's fixed-point sum, the identity contributes $A(n)$,
the four eligible nonzero vectors contribute $n^2/3$ each by Theorem 5,
and every other term is zero. Since $n^2=3(n^2/3)$ and $A(n)\ge0$, an orbit
count of zero or one would contradict the displayed equality. Setting
$q=O(n)-2$ gives $A(n)=n^2q+2n^2/3$. $\square$

## 7. Prime-modulus census and affine recovery

**Definition 7.1 (prime triples and graph parameters).** Let $p$ be a
prime and put $F=\mathbb Z/p\mathbb Z$. An admissible triple is an
unordered subset $S\subset F^2$ with $|S|=3$ such that both coordinate
projections are injective on $S$ and, for every $u,v,w\in S$,

$$
  (v_x-u_x)(w_y-u_y)=(w_x-u_x)(v_y-u_y).
$$

Thus these are precisely the triples counted by $A(p)$ above, with the
zero-determinant condition stated for all choices of the three points.
Let $\mathcal X_p=\{X\subset F:|X|=3\}$ and let
$\mathcal P_p=F^\times\times F\times\mathcal X_p$. For
$(a,b,X)\in\mathcal P_p$, define its graph triple by

$$
  \Gamma(a,b,X)=\{(x,ax+b):x\in X\}.
$$

**Theorem 7.2 (unique affine recovery and graph inverse).** Every
admissible triple $S$ has a unique nonzero slope $a\in F^\times$ and a
unique intercept $b\in F$ for which $y=ax+b$ at every $(x,y)\in S$.
With $X=\{x:(x,y)\in S\}$, the maps

$$
\begin{aligned}
  \mathcal P_p&\longrightarrow\mathcal T_p,
    &(a,b,X)&\longmapsto\Gamma(a,b,X),\\
  \mathcal T_p&\longrightarrow\mathcal P_p,
    &S&\longmapsto(a,b,\{x:(x,y)\in S\})
\end{aligned}
$$

are mutually inverse. In particular, the recovered parameters describe
the original point set exactly, rather than only a containing line.

**Proof.** Choose distinct points $u,v\in S$. The two coordinate
injectivity assumptions give $v_x-u_x\ne0$ and $v_y-u_y\ne0$.
Since $F$ is a field, set

$$
  a=\frac{v_y-u_y}{v_x-u_x},\qquad b=u_y-au_x.
$$

The numerator is nonzero, so $a\ne0$. For each $w\in S$, the
determinant equation for $u,v,w$, after division by $v_x-u_x$, gives
$w_y-u_y=a(w_x-u_x)$, hence $w_y=aw_x+b$. If another pair
$(a',b')$ fits every point of $S$, subtraction of its equations at $u$
and $v$ gives $a'(v_x-u_x)=v_y-u_y$. Division forces $a'=a$, and
its equation at $u$ then gives $b'=b$. Thus recovery is independent of
the chosen pair of points.

The first-coordinate projection is injective on $S$, so its image $X$
has exactly three elements. Each point of $S$ lies in
$\Gamma(a,b,X)$. Conversely, each $x\in X$ is the first coordinate
of a point of $S$, whose second coordinate must be $ax+b$. This proves
$S=\Gamma(a,b,X)$.

For any parameters $(a,b,X)$, the graph map is injective because its
first coordinate is $x$, so its image has three elements. Its second
coordinate is injective because $a\ne0$: equality $ax+b=ax'+b$
forces $x=x'$. For graph points indexed by $x,z,t$, their difference
determinant vanishes since

$$
  (z-x)\bigl(a(t-x)\bigr)=(t-x)\bigl(a(z-x)\bigr).
$$

The graph triple is therefore admissible. Its first-coordinate image
is $X$, and uniqueness of affine recovery returns its original $a$
and $b$. Both compositions are the identity, proving the claimed
bijection. $\square$

**Theorem 7.3 (complete prime census).** For every prime $p$,

$$
  A(p)=p(p-1)\binom p3.
$$

**Proof.** The bijection of Theorem 7.2 reduces the count to independent
choices of $a\in F^\times$, $b\in F$, and $X\in\mathcal X_p$.
These sets have cardinalities $p-1$, $p$, and $\binom p3$,
respectively. Multiplying gives the formula. The sets $X$ are unordered,
so no further division by a permutation factor is needed. No lower
bound $p>3$ was used. $\square$

## 8. Translation classes and the two smallest primes

**Theorem 8.1 (translation criterion in graph coordinates).** For
$(a,b,X),(a',b',X')\in\mathcal P_p$, their graph triples are in the
same translation orbit in $F^2$ if and only if

$$
  a'=a\quad\text{and}\quad
  \exists h\in F,\quad X'=h+X,
  \qquad h+X=\{h+x:x\in X\}.
$$

More precisely, translation by $(h,k)$ obeys

$$
  (h,k)+\Gamma(a,b,X)
    =\Gamma(a,b+k-ah,h+X).
$$

**Proof.** For a point $(x,ax+b)$, put $x'=h+x$. Its translated
second coordinate is

$$
  k+ax+b=a(h+x)+(b+k-ah)=ax'+(b+k-ah).
$$

This identifies the whole translated set with the asserted graph.
If it equals $\Gamma(a',b',X')$, uniqueness in Theorem 7.2 gives
$a'=a$, $X'=h+X$, and $b'=b+k-ah$. Conversely, if $a'=a$ and
$X'=h+X$, choose $k=b'-b+ah$. The displayed transformation then
sends the first graph triple to the second. Thus the intercept imposes
no additional restriction on the translation orbit. $\square$

**Theorem 8.2 (the complete $p=2$ and $p=3$ cases).** There are no
admissible triples for $p=2$, and there are exactly six for $p=3$:

$$
\begin{aligned}
  A(2)&=0,\\
  \mathcal T_3&=
    \{\Gamma(a,b,F):a\in\{1,2\},\ b\in F\},\\
  A(3)&=6.
\end{aligned}
$$

For $p=3$, these six triples form exactly two translation orbits,
one for each nonzero slope. Each orbit has three triples, and
$\Gamma(a,b,F)$ has translation stabilizer

$$
  H_a=\{(h,ah):h\in F\}.
$$

**Proof.** When $p=2$, an injective first-coordinate projection of a
three-element set into the two-element field is impossible. Equivalently,
$\mathcal X_2$ is empty and $\binom23=0$.

When $p=3$, the only three-element subset of $F$ is $F$ itself. There
are two nonzero slopes and three intercepts; Theorem 7.2 shows that all
six graph triples are admissible, distinct, and exhaustive. Accordingly,
$3(3-1)\binom33=6$. Since $h+F=F$ for every $h$, Theorem 8.1
identifies precisely the three intercept choices for each fixed slope
as one orbit. A translation fixes such a graph exactly when
$b+k-ah=b$, or $k=ah$, giving the displayed stabilizer of size three.
For $n=3$, these two stabilizers are the subgroups $H_+$ and $H_-$
of Theorem 1, and its two exceptional orbits exhaust $\mathcal T_3$.
$\square$

## 追加锚（本行以下为增补区）
