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
