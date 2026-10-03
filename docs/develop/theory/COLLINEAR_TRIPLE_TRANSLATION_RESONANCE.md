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

## 9. Affine graph stabilizers over commutative rings

**Theorem 9.1 (affine graph translation stabilizer).** Let $R$ be any
commutative ring, let $X\subset R$ be a nonempty finite set, and let
$a,b\in R$. Define

$$
  \Gamma_{a,b}(X)=\{(x,ax+b):x\in X\},\qquad
  \operatorname{Stab}_R(X)=\{h\in R:h+X=X\}.
$$

Then the translation stabilizer of the graph is

$$
  \operatorname{Stab}_{R^2}(\Gamma_{a,b}(X))
    =\{(h,ah):h\in\operatorname{Stab}_R(X)\}.
$$

The map $h\mapsto(h,ah)$ is an injective additive homomorphism and
identifies these two stabilizers. There is no domain, prime-modulus,
unit-slope, nonzero-slope, or three-element assumption.

**Proof.** Translation by $(h,k)$ gives the graph identity

$$
  (h,k)+\Gamma_{a,b}(X)
    =\Gamma_{a,b+k-ah}(h+X).
$$

Indeed, put $x'=h+x$ in a translated graph point; its second coordinate
is $k+ax+b=ax'+b+k-ah$. If the translated graph equals the original,
their first-coordinate projections give $h+X=X$. Choose $x\in X$.
The unique points above this same first coordinate in the two equal
graphs have second coordinates $ax+b+k-ah$ and $ax+b$. Additive
cancellation gives $k=ah$. Conversely, $h+X=X$ and $k=ah$ make the
displayed translated graph equal to the original. Finally, distributivity
gives $a(h+h')=ah+ah'$, and the first coordinate makes the slope map
injective. $\square$

The nonempty condition cannot be omitted uniformly. An empty graph is
fixed by every translation, so its stabilizer is all of $R^2$; the
abscissa stabilizer of the empty set is all of $R$, whose image under
the slope map is only $\{(h,ah):h\in R\}$. For $R=\mathbb Z$ and
$a=0$, the translation $(0,1)$ fixes the empty graph and is outside
that image. The stated equality still includes the zero ring whenever
$X$ is nonempty.

## 10. Fixed-slope translation census for arbitrary moduli

**Theorem 10.1 (slope-filtered fixed-point census).** For each
nonnegative integer $n$ and each $a\in\mathbb Z/n\mathbb Z$, let

$$
  \mathcal V_a=
    \{X\subset\mathbb Z/n\mathbb Z:|X|=3,
      \ x\mapsto ax\text{ is injective on }X\}.
$$

Translation by any $t\in\mathbb Z/n\mathbb Z$ preserves
$\mathcal V_a$, without a positivity assumption on $n$. If $n>0$
and $t\ne0$, the exact fixed-point count is

$$
  |\operatorname{Fix}_t(\mathcal V_a)|=
  \begin{cases}
    n/3,&3t=0\text{ and }at\ne0,\\
    0,&\text{otherwise}.
  \end{cases}
$$

Only injectivity on the individual set $X$ is required; multiplication
by $a$ need not be injective on the whole ring, and $a$ need not be a unit.

**Proof.** Translation is a bijection and hence preserves cardinality.
If $a(t+x)=a(t+y)$ with $x,y\in X$, cancellation of $at$ gives
$ax=ay$, and injectivity on $X$ gives $x=y$. Thus it also preserves
the injectivity condition for every $n$.

Suppose $t+X=X$ and $|X|=3$. Summing the elements on both sides and
cancelling their sum gives $3t=0$. If $at=0$, each $x\in X$ and its
distinct translate $x+t\in X$ have equal images, which excludes
$X\in\mathcal V_a$. This proves the zero cases for nonzero $t$.

Now assume $3t=0$ and $at\ne0$. Both $t$ and $at$ have additive
order three: their orders divide the prime three and neither is zero.
Consequently

$$
  C_t=\{0,t,2t\}
$$

has three elements, its image under multiplication by $a$ has three
elements, and $t+C_t=C_t$. For any fixed $X$, choose $x\in X$.
Invariance puts $x,x+t,x+2t$ in $X$; these are distinct and exhaust
its three elements. Therefore the fixed members are precisely the
translates of $C_t$. Its translation stabilizer is $C_t$: every element
of this subgroup fixes it, and a stabilizing $h$ lies in $C_t$ because
$h=h+0\in h+C_t=C_t$. Ordinary orbit-stabilizer now counts its
translates as $n/3$. $\square$

For $n=6$, $a=2$, and $t=2$, the fixed family is exactly

$$
  \operatorname{Fix}_2(\mathcal V_2)
    =\bigl\{\{0,2,4\},\{1,3,5\}\bigr\}.
$$

These are distinct even and odd cosets, so the count is two despite the
nonunit slope. For $n=3$, $a=1$, and $t=1$, the only fixed member is
$\{0,1,2\}$, giving count one. Further boundary values are

$$
\begin{aligned}
  n=6:&\quad |\operatorname{Fix}_2(\mathcal V_3)|=0,
    \qquad |\operatorname{Fix}_1(\mathcal V_2)|=0,\\
  n=9:&\quad |\operatorname{Fix}_3(\mathcal V_2)|=3,
    \qquad |\operatorname{Fix}_3(\mathcal V_3)|=0,\\
  n=3:&\quad |\operatorname{Fix}_1(\mathcal V_0)|=0,
    \qquad |\operatorname{Fix}_0(\mathcal V_1)|=1,\\
  n=2:&\quad |\operatorname{Fix}_1(\mathcal V_1)|=0.
\end{aligned}
$$

In each row, $\mathcal V_a$ is taken in the indicated modulus. The
zero-translation value for $n=3$ shows why $t\ne0$ belongs in the
counting statement: identity translation fixes the whole class. For
$n=1$, there is no nonzero $t$.

This census keeps the slope fixed and counts admissible abscissa sets.
Enumeration across different slopes requires an overlap analysis before
their counts can be combined.

## 11. Homomorphism-filtered translation census

**Theorem 11.1 (homomorphism-filtered fixed-point census).** Let $G$
be a finite abelian group, let $A$ be any abelian group, and let
$f:G\to A$ be an additive homomorphism. Put

$$
  \mathcal V_f=\{X\subset G:|X|=3,
    \ f\text{ is injective on }X\}.
$$

Translation by $G$ preserves $\mathcal V_f$. For every nonzero
$t\in G$,

$$
  |\operatorname{Fix}_t(\mathcal V_f)|=
  \begin{cases}
    |G|/3,&3t=0\text{ and }f(t)\ne0,\\
    0,&\text{otherwise}.
  \end{cases}
$$

The codomain $A$ may be infinite. Preservation itself holds for any
abelian $G$, without a finiteness assumption.

**Proof.** Translation preserves cardinality, and
$f(t+x)=f(t)+f(x)$ shows by cancellation that injectivity on $X$
implies injectivity on $t+X$. If $t+X=X$ with $|X|=3$, summing
gives $3t=0$. If $f(t)=0$, then $x$ and $x+t$ are distinct members
with equal images, so no such $X$ is in $\mathcal V_f$.

When $3t=0$ and $f(t)\ne0$, both $t$ and $f(t)$ have order three.
The subgroup $C_t=\{0,t,2t\}$ therefore belongs to $\mathcal V_f$.
Every translate of it is admissible and fixed by $t$. Conversely, any
fixed three-element set contains the three distinct points
$x,x+t,x+2t$ for each $x$ in it, so it is exactly $x+C_t$. Thus the
fixed family is one translation orbit of $C_t$. Its stabilizer is
exactly $C_t$, since a stabilizing $h$ must satisfy
$h=h+0\in h+C_t=C_t$. Orbit-stabilizer gives $|G|/3$ members.
Neither classification nor counting uses finiteness of $A$. $\square$

Theorem 10.1 is the case $G=A=\mathbb Z/n\mathbb Z$ and $f(x)=ax$.
An infinite-codomain example is $G=\mathbb Z/3\mathbb Z$,
$A=(\mathbb Z/3\mathbb Z)\times\mathbb Z$, and $f(x)=(x,0)$.
For $t=1$, the sole three-element subset is all of $G$, it is
$f$-injective, and it is fixed, giving count one.

For $G=(\mathbb Z/3\mathbb Z)^2$ and $f(x,y)=x$, all eight nonzero
directions have order three. Exactly six survive the kernel condition:

$$
  D=\{(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)\}.
$$

Each direction in $D$ fixes three admissible triples. The two nonzero
kernel directions $(0,1)$ and $(0,2)$ each fix none. The survivors pair
into the three distinct order-three subgroups

$$
\begin{aligned}
  H_0&=\{0,(1,0),(2,0)\},\\
  H_1&=\{0,(1,1),(2,2)\},\\
  H_2&=\{0,(1,2),(2,1)\}.
\end{aligned}
$$

The directions $(1,0),(2,0)$ have fixed family equal to the cosets of
$H_0$; $(1,1),(2,2)$ have the cosets of $H_1$; and $(1,2),(2,1)$
have the cosets of $H_2$. For each $i\in\{0,1,2\}$ those cosets are
exactly

$$
  \{H_i,\ (0,1)+H_i,\ (0,2)+H_i\}.
$$

They form one translation orbit of size three. The three orbits are
pairwise disjoint, since the stabilizer of a coset is its corresponding
subgroup and $H_0,H_1,H_2$ are distinct.

## 追加锚（本行以下为增补区）
