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

**Theorem 7 (prime-modulus census).** For every prime $p$, the same
unordered, coordinate-distinct, zero-determinant triples satisfy

\[
  A(p)=p(p-1)\binom p3.
\]

**Proof.** In the field $\mathbb Z/p\mathbb Z$, choose two points of an
admissible triple. Their distinct first coordinates determine a unique
affine line $y=ax+b$. The zero-determinant condition places its third
point on this line, and distinct second coordinates imply $a\ne0$.
Conversely, a nonzero slope $a$, an intercept $b$, and an unordered
three-element set $X$ of first coordinates determine exactly the
admissible triple $\{(x,ax+b):x\in X\}$. These constructions are inverse.
There are $p-1$ choices for $a$, $p$ for $b$, and $\binom p3$ for $X$.
The argument includes $p=2$, when there is no such $X$, and $p=3$.

Translation by $(h,k)$ sends the parameters $(a,b,X)$ to
$(a,b+k-ah,h+X)$: the slope is invariant, the intercept shifts by
$k-ah$, and the first-coordinate set shifts by $h$. $\square$
