# Signed right-maximum weights on separable permutations

## 1. Permutations and signed cuts

**Definition 1.1 (Strict records and block sums).** For $n\in\mathbb N$, let
$\mathfrak S_n$ be the permutations of $\{0,\ldots,n-1\}$. A position $i$ of
$\pi\in\mathfrak S_n$ is a right maximum if $\pi(j)<\pi(i)$ for every $j>i$.
Let $r(\pi)$ count these positions. For $\alpha\in\mathfrak S_m$ and
$\beta\in\mathfrak S_h$, their direct and skew sums are

$$
\begin{aligned}
(\alpha\oplus\beta)(i)&=\begin{cases}\alpha(i)&i<m,\\m+\beta(i-m)&m\le i<m+h,\end{cases}\\
(\alpha\ominus\beta)(i)&=\begin{cases}h+\alpha(i)&i<m,\\\beta(i-m)&m\le i<m+h.\end{cases}
\end{aligned}
$$

These definitions allow $m=0$ and $h=0$. A proper direct cut of a permutation
of length $n$ is an integer $c$ with $0<c<n$ such that every value before $c$
is smaller than every value at or after $c$. A proper skew cut reverses this
inequality. Write $s=0$ for direct cuts and $s=1$ for skew cuts.

**Definition 1.2 (Avoidance and record fibers).** Let $A_n$ be the permutations
of length $n$ avoiding the classical patterns $2413$ and $3142$. Let $B_{s,n}$
be the members of $A_n$ with no proper cut of sign $s$, and let $P_{s,n}$ be
those with a proper cut of sign $s$. For all $s\in\{0,1\}$ and $n,k\in\mathbb N$,
put

$$
\begin{aligned}
U(n,k)&=|\{\pi\in A_n:r(\pi)=k\}|,& j(s,n)&=|B_{s,n}|,\\
J(s,n,k)&=|\{\pi\in B_{s,n}:r(\pi)=k\}|,&
D(s,n,k)&=|\{\pi\in P_{s,n}:r(\pi)=k\}|.
\end{aligned}
$$

The empty permutation has zero records and belongs to $A_0$ and both $B_{s,0}$.
Following Chen, Kitaev and Zhang, an irreducible permutation has positive
length and no proper direct cut. A reducible permutation has a proper direct
cut. Thus the empty permutation is in neither of these two classes, the
singleton is irreducible, and the reducible class at length one is empty.
Their Section 1.2 uses strict, unshifted record counts.

## 2. Record identities

**Theorem 2.1 (Arbitrary signed block sums).** For every $m,h\in\mathbb N$,
every $\alpha\in\mathfrak S_m$ and every $\beta\in\mathfrak S_h$, without
an avoidance hypothesis,

$$
r(\alpha\oplus\beta)=
\begin{cases}r(\alpha)&h=0,\\r(\beta)&h>0,\end{cases}
\qquad
r(\alpha\ominus\beta)=r(\alpha)+r(\beta).
$$

Proof. Partition the positions into $i<m$ and $m\le i<m+h$. In either sum,
the order comparisons among suffix values are exactly those of $\beta$;
therefore a suffix position is a right maximum exactly when its position
in $\beta$ is a right maximum. In a direct sum with $h>0$, every prefix value
is smaller than every suffix value, so no prefix position is a right maximum.
For $h=0$ the suffix is empty and the comparisons in the prefix are those
of $\alpha$. In a skew sum, every prefix value exceeds every suffix value.
Consequently a prefix position is a right maximum precisely when it exceeds
every later prefix value, which is exactly the right-maximum condition in
$\alpha$. Count the two disjoint sets of record positions. This also proves
the formulas when either set of positions is empty.

**Theorem 2.2 (Signed proper-cut record convolution).** For every
$s\in\{0,1\}$ and every $n,k\in\mathbb N$, define

$$
\begin{aligned}
C(0,n,k)&=\sum_{0<c<n}j(0,c)U(n-c,k),\\
C(1,n,k)&=\sum_{0<c<n}\sum_{b=0}^{k}J(1,c,b)U(n-c,k-b).
\end{aligned}
$$

Then $D(s,n,k)=C(s,n,k)$. The outer sums range over natural integers $c$;
each factor has its indicated dependent length $c$ or $n-c$. The inner sum
ranges over $0\le b\le k$, so $k-b$ is ordinary nonnegative subtraction.
The identities include $n=0$, $n=1$, and all $k$, including $k>n$.

Proof. Use the least proper cut of sign $s$ to identify $P_{s,n}$ with the
disjoint union over $0<c<n$ of $B_{s,c}\times A_{n-c}$. This is the signed
minimum-cut decomposition: standardizing the prefix and suffix preserves
avoidance; a smaller cut in the prefix would contradict leastness; conversely
the signed block sum of a prefix with no proper cut of sign $s$ and an arbitrary
avoiding suffix has least cut $c$. The block sum preserves avoidance in both
directions. The signed decomposition is the classical separable-permutation
decomposition of Fu, Lin and Zeng, Proposition 2.1; the direct and skew record
mechanisms also occur in Chen, Kitaev and Zhang, Section 2.

For a direct cut, $n-c>0$, and Theorem 2.1 makes the total record count exactly
the suffix count. Thus the record-$k$ fiber at $c$ is
$B_{0,c}\times\{\beta\in A_{n-c}:r(\beta)=k\}$, with cardinality
$j(0,c)U(n-c,k)$. For a skew cut, Theorem 2.1 gives
$r(\alpha)+r(\beta)=k$. Partition this fiber by $b=r(\alpha)$.
Nonnegativity gives $0\le b\le k$ and $r(\beta)=k-b$; conversely these two
record counts sum to $k$. The fiber is therefore the disjoint union of
$\{\alpha\in B_{1,c}:r(\alpha)=b\}\times
\{\beta\in A_{n-c}:r(\beta)=k-b\}$ over $b=0,\ldots,k$.
Count the products and then the cuts. The length identity $c+(n-c)=n$
identifies the reconstructed permutation's positions with the original ones
without changing their order or record count. At $n=0$ and $n=1$ there is no
proper cut; both sides are zero. No restriction on $k$ was used.

## 追加锚（本行以下为增补区）
