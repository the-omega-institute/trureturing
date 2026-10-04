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

## 3. Positive actual record series

**Definition 3.1 (Positive series).** In $\mathbb Q[[t]][[y]]$, put

$$
\begin{aligned}
U&=\sum_{n\ge1,k\ge0}U(n,k)t^ny^k,&
J&=\sum_{n\ge1,k\ge0}J(0,n,k)t^ny^k,\\
R&=\sum_{n\ge1,k\ge0}D(0,n,k)t^ny^k,&
I_0&=\sum_{n\ge1}j(0,n)t^n,\\
I&=I_0\quad\text{as a constant series in }y,&
q&=\sum_{n\ge1}|A_n|t^n,\qquad z=ty.
\end{aligned}
$$

Every coefficient is an actual finite cardinality. The empty permutation is
excluded from all six positive series. Scalar series are embedded as constant
series in $y$; no evaluation at $y=1$ is used in these definitions.

**Theorem 3.2 (Actual positive record equations and support).** Every
permutation of positive length $n$ has between $1$ and $n$ right maxima.
Consequently every positive record fiber vanishes at $k=0$ and $k>n$.
The actual series of Definition 3.1 satisfy

$$
\begin{aligned}
U&=J+R,& R&=IU,& J&=z+(z+R)U,\\
2I_0&=q+t,& I_0(1+q)&=q,& q&=tL(t),\\
q&=t+tq+q^2,& U&=(1+q)J,&
J&=z+z(1+q)J+q(1+q)J^2,
\end{aligned}
$$

where $L(t)=\sum_{m\ge0}\operatorname{largeSchroder}(m)t^m$ is the
large Schröder series. The length-zero coefficients of $U,J,R,I_0,q$ are
zero. Their length-one coefficients are respectively $y,y,0,1,1$.
The positive no-proper-skew-cut record series is $z+R$. In particular
the singleton term in the skew decomposition is $z$, whereas a proper-cut
class is empty at lengths zero and one.

Proof. Partition each actual record fiber into members with a proper direct
cut and members without one. Apply Theorem 2.2 to obtain $R=IU$.
For $n\ge2$, the pointwise separable cut dichotomy identifies no proper skew
cut with a proper direct cut, and no proper direct cut with a proper skew
cut, without changing the underlying permutation or any record. At length
one the no-cut fiber contributes $z$, and both proper-cut fibers are empty.
The skew convolution therefore gives $J=z+(z+R)U$. These equalities follow
coefficientwise from finite sums over $0<c<n$ and $0\le b\le k$.
For a nonempty permutation the last position is a right maximum, and the
set of right maxima is a subset of its $n$ positions; this gives support.

The actual scalar count identities give $2I_0=q+t$ and $q=tL$.
The existing large Schröder quadratic gives $q=t+tq+q^2$.
These identities imply $I_0(1+q)=q$. Multiplying $U=J+I_0U$ by
$1+q$ gives $U=(1+q)J$, and hence $R=qJ$.
Substituting in the skew equation gives the stated quadratic for $J$.
All scalar counts here are defined directly; none is inferred from an
assumed correspondence between an unmarked generating function and a
weighted record series.

## 追加锚（本行以下为增补区）

## 4. Rising comparison at records two and three

**Theorem 4.1 (Actual rising comparison).** For every $n\ge4$, the
actual direct-indecomposable separable record fibers satisfy
$J(0,n,2)\le J(0,n,3)$. Thus this adjacent comparison holds for every
$n\ge5$ in the right-maximum irreducible clause of CKZ Conjecture 2.

Proof. Coefficient extraction from the actual quadratic of Theorem 3.2
gives $J_1=t$, $J_2=t^2(1+q)^2$, and
$J_3=t^3(1+q)^3(1+2q)$, where $J_k=[y^k]J$.
Using $t(1+q)=q(1-q)$, their difference is $t^2P(q)$, with

$$
P(x)=-1-x+2x^2+x^3-3x^4-2x^5.
$$

Put $K(x)=1-2x-x^2$ and
$N(x)=x^2(9-2x-31x^2-32x^3-10x^4)$.
The formal derivative of $q=t+tq+q^2$ gives
$K(q)q'=(1+q)^2$. Hence

$$
\frac{d}{dt}\bigl(P(q(t))+1+t\bigr)
=\left(\frac{N}{K}\right)(q(t)).
$$

The exact coefficients of $N/K$ at indices zero through seven are
$0,0,9,16,10,4,8,20$. At every index $m\ge8$, its coefficient is twice
the preceding coefficient plus the coefficient two indices earlier.
This recurrence proves that every coefficient is nonnegative. The actual
scalar series $q$ has nonnegative coefficients and zero constant term,
so formal composition preserves nonnegativity coefficientwise. Integration
over $\mathbb Q$ preserves nonnegativity at every positive index.
The correction $1+t$ changes only indices zero and one; multiplication
by $t^2$ therefore gives the comparison at every length $n\ge4$.
This argument is an unbounded coefficient proof and does not infer the
comparison from a finite list of permutation rows.

## 追加锚（本行以下为增补区）
