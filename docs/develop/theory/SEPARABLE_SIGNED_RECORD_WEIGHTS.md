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

## 5. Actual record transports and the complete rising side

**Definition 5.1 (The four positive record fibers).** Let $i_t(n,k)$ count
the literal $2413/3142$ avoiders of positive length $n$ with no proper
direct cut and exactly $k$ strict records of type $t$. Let $d_t(n,k)$ count
the avoiders with a proper direct cut and exactly $k$ such records. The
types are right maximum, left minimum, left maximum and right minimum,
with their strict comparisons as in Section 1. Both positive classes are
empty at length zero. Put $\delta(n,k)=1$ when $n=k=1$ and zero otherwise.

**Theorem 5.2 (Actual transports and rising laws).** For all natural
lengths $n$ and record indices $k$,

$$
\begin{aligned}
i_{\mathrm{lmin}}(n,k)&=i_{\mathrm{rmax}}(n,k),\\
d_{\mathrm{lmax}}(n,k)+\delta(n,k)&=i_{\mathrm{rmax}}(n,k),\\
d_{\mathrm{rmin}}(n,k)+\delta(n,k)&=i_{\mathrm{rmax}}(n,k).
\end{aligned}
$$

For each of these four class/statistic pairs, its count at zero records
vanishes at every positive length; its count at one record vanishes for
every $n\ge2$. For every $n\ge4$ and every $k<3$, its count at $k$ is at
most its count at $k+1$.

Proof. Reverse positions, complement values by $v\mapsto n-1-v$, and
compose these involutions. Each operation preserves the actual avoidance
class: complement interchanges the two forbidden patterns, position
reversal also interchanges them, and both embeddings and strict value
comparisons transport explicitly. Complement changes a cut's sign;
reversal changes its sign and sends the cut position $c$ to $n-c$.
Their composition preserves the sign. The pointwise separable cut
dichotomy at $n\ge2$ identifies the opposite no-cut class with the
proper-cut class. The transported record-position sets give exact
record-fiber bijections: reverse sends right maxima to left maxima,
complement sends right maxima to right minima, and their composition
sends right maxima to left minima. At length one all record types have
count one, while neither proper-cut class has a member; this gives the
displayed singleton corrections. At length zero positivity excludes
the empty permutation from both source classes.

The last position of a nonempty permutation is a right maximum. If it
is the only right maximum, the largest value must occur there, because
the position of the largest value is itself a right maximum. At length
at least two the last value then yields a proper direct cut at $n-1$.
Thus an irreducible permutation of length at least two has neither zero
nor one right maximum. The exact transports give the same zero fibers
for the other three pairs. Nonnegative cardinalities give the first two
adjacent rising comparisons; Theorem 4.1 gives the comparison from two
to three, transported to the other pairs at every $n\ge4$. No declining
comparison or full peak-three conclusion is asserted here.

## 追加锚（本行以下为增补区）

## 6. The first declining comparison

**Definition 6.1 (Strict comparisons in Definition 5.1).** A left maximum at
position $i$ exceeds every value at positions $j<i$; a left minimum is
below every value at positions $j<i$; a right minimum is below every value
at positions $j>i$. The right-maximum comparison is Definition 1.1.
These four counts are strict and unshifted, including the empty and
singleton conventions of Definition 5.1.

**Theorem 6.2 (Actual decline from three to four).** For each of
$(\mathrm{irreducible},\mathrm{rmax})$,
$(\mathrm{irreducible},\mathrm{lmin})$,
$(\mathrm{reducible},\mathrm{lmax})$ and
$(\mathrm{reducible},\mathrm{rmin})$, its actual record-fiber cardinality
satisfies $a(n,4)\le a(n,3)$ for every natural length $n$, and
$a(n,4)<a(n,3)$ for every $n\ge3$.

Proof. The actual quadratic of Theorem 3.2 gives

$$
J_4=t^4(1+q)^4(1+5q+5q^2).
$$

Together with $J_3=t^3(1+q)^3(1+2q)$ and
$t(1+q)=q(1-q)$, this yields $J_3-J_4=t^3F(q)$, where

$$
F(x)=1+4x+2x^2-8x^3-6x^4+11x^5+15x^6+5x^7.
$$

Put $K(x)=1-2x-x^2$. The numerator of $(1+x)^2F'(x)/K(x)$ is

$$
N(x)=4+12x-12x^2-68x^3-17x^4+176x^5+270x^6+160x^7+35x^8.
$$

The quotient has exact coefficients
$4,20,32,16,47,286,889,2224,5372$ through index eight. At every
index $m\ge9$ its coefficient is twice the preceding coefficient plus
the coefficient two places earlier. Matching coefficients proves the
quotient identity and its nonnegative infinite tail. In particular,
$N/K-20x$ has nonnegative coefficients.

The actual scalar series $q=tL(t)$ has zero constant term and positive
coefficients at every positive index: the large Schröder recurrence,
with initial value one and nonnegative summands, gives positivity.
Differentiation of its quadratic gives $K(q)q'=(1+q)^2$.
Thus $\frac{d}{dt}F(q(t))=(N/K)(q(t))$, whose constant coefficient is
four and whose positive-index coefficients dominate those of $20q(t)$.
All derivative coefficients are strictly positive. Since $F(q(0))=1$,
formal integration over $\mathbb Q$ shows that every coefficient of
$F(q(t))$ is strictly positive. Multiplication by $t^3$ proves the weak
comparison at every length and the strict comparison at every $n\ge3$.
The transports of Theorem 5.2 give the other three comparisons. Their
singleton corrections vanish at record indices three and four.

## 追加锚（本行以下为增补区）

## 7. An unbounded sign law for the record kernels

Definition 5.1 uses this volume's local numbering. Its source-class and
statistic locators are Chen–Kitaev–Zhang, arXiv:2404.18517v1, Sections 1
and 1.2; the full peak-three question is Section 3, Conjecture 2, page 17.
The positive classes, proper cuts and strict unshifted comparisons are
those of Definitions 1.1, 5.1 and 6.1 in this volume.

**Definition 7.1 (Motzkin record kernels).** Work in $\mathbb Q[[u]][[z]]$.
Let $C(w)$ be the Catalan series supplied by Mathlib, with
$C(w)=1+wC(w)^2$. Put

$$
\begin{aligned}
a(u)&=u(3+2u),& b(u)&=u(1+u)^3,& c(u)&=u(4+3u)=4b(u)-a(u)^2,\\
M(z)&=\frac{1}{1-az}C\left(\frac{bz^2}{(1-az)^2}\right),&
T_r(u)&=[z^r]M(z).
\end{aligned}
$$

Every denominator here has constant one. Define

$$
G_r(u)=(1+u)^2(T_r+T_{r+1})
-u(1-u)(1+u)(T_r+2T_{r+1}+T_{r+2}).
$$

The name record Newton kernel denotes this exact expression. Its
correspondence with the normalized actual record coefficients is a
separate obligation. The actual scalar $q(t)$ is the positive avoider
series of Theorem 3.2, with $q=tL(t)$ for the large Schröder series $L$.

**Theorem 7.2 (Every kernel is nonnegative after actual substitution).**
For every natural $r$ and $n$,

$$
[t^n]G_r(q(t))\ge0.
$$

Proof. Catalan substitution gives $M=1+azM+bz^2M^2$. Differentiating
this quadratic and eliminating the quadratic term gives

$$
z(1-2az-cz^2)M'+(2-3az-cz^2)M=2.
$$

The eliminated factor $2bz^2M+az-1$ has constant $-1$ and is nonzero.
Coefficient extraction gives $T_0=1$, $T_1=a$, and for every $r\ge0$,

$$
(r+4)T_{r+2}=(2r+5)aT_{r+1}+(r+1)cT_r.
$$

The actual scalar has nonnegative coefficients and satisfies
$q=t+tq+q^2$. Thus $t(1+q)=q(1-q)$ and
$(1-2q-q^2)q'=(1+q)^2$. For any polynomial $f(u)$ with $f(0)\ge0$,
an exact nonnegative series $V(u)$ satisfying

$$
(1-2u-u^2)V(u)=(1+u)^2f'(u)
$$

proves $f(q(t))$ is nonnegative: the chain rule gives
$(f(q(t)))'=V(q(t))$, and formal integration divides each positive-index
coefficient by its positive index. To construct $V$, match its initial
coefficients through one index past the numerator's degree. Beyond that
degree the coefficient identity is the universal recurrence
$v_{m+2}=2v_{m+1}+v_m$. Nonnegative consecutive initial values therefore
prove all later coefficients nonnegative. This is an exact polynomial
certificate followed by induction, rather than a finite-length test.

Apply this certificate rule to $G_0,\ldots,G_{11}$ and to the four
polynomials $E_1T_1,E_1T_2,E_2T_{13},E_2T_{14}$, where

$$
\begin{aligned}
E_1&=(1+u)^2(1-u-2u^2+3u^3),\\
E_2&=(1+u)^2(1-2u-2u^2+4u^3).
\end{aligned}
$$

The exact coefficient vectors are part of the Lean theorem's local
certificates. For any fixed $E$, multiplying the universal recurrence
by $E$ shows that nonnegativity of $(ET_s)(q(t))$ and
$(ET_{s+1})(q(t))$ propagates to every index at least $s$: both $a(q(t))$
and $c(q(t))$ are nonnegative, and division by $r+4$ preserves the sign.
Consequently $(E_1T_r)(q(t))$ is nonnegative for every $r\ge1$, and
$(E_2T_r)(q(t))$ is nonnegative for every $r\ge13$.

For every $r$, the same recurrence gives the exact reduction

$$
(r+4)G_r=(r+4)(E_1T_r+E_2T_{r+1})
+3u(1-u)(1+u)(cT_r+aT_{r+1}).
$$

The $T_r$ themselves are nonnegative by the recurrence and $T_0=1$,
$T_1=a$. After actual substitution the last summand is
$3t(1+q)^2(c(q)T_r(q)+a(q)T_{r+1}(q))$, so it is nonnegative.
For $r\ge12$ both other summands are nonnegative by the propagated
laws. Division by $r+4$ proves the remaining indices, and the twelve
base certificates finish the result.

The normalized actual $J_k$ formula and its Newton transform remain
separate obligations. The sign law alone does not prove the actual
comparison $a(n,k+1)\le a(n,k)$ for arbitrary $k\ge4$, the global maximum
at three, or the full conjecture.

## 追加锚（本行以下为增补区）

## 8. Actual record coefficients and the binomial kernel expansion

**Definition 8.1 (Actual fibers and independent variables).** For every
$n,k\in\mathbb N$, let $a_{X,s}(n,k)$ count the literal permutations in
$\operatorname{Av}_n(2413,3142)$ in class $X$ with exactly $k$ records of
type $s$, where

$$
(X,s)\in\{(\mathrm{irreducible},\mathrm{rmax}),
(\mathrm{irreducible},\mathrm{lmin}),
(\mathrm{reducible},\mathrm{lmax}),
(\mathrm{reducible},\mathrm{rmin})\}.
$$

The classes and strict, unshifted records are Definitions 1.1, 5.1 and
6.1. In particular, irreducibility requires positive length and no proper
direct cut; reducibility requires a proper direct cut. Both classes exclude
the empty permutation, and only the irreducible class contains the
singleton. Write $i(n,k)=a_{\mathrm{irreducible},\mathrm{rmax}}(n,k)$ and
retain the actual series

$$
q(t)=\sum_{n\ge1}|\operatorname{Av}_n(2413,3142)|t^n,\qquad
J(t,y)=\sum_{n\ge1,k\ge0}i(n,k)t^ny^k,\qquad J_k(t)=[y^k]J(t,y).
$$

Use independent variables $u,x,z$. In $\mathbb Q[u][[z]]$ take exactly the
kernels of Definition 7.1, with $H=1+u$, $a=u(3+2u)$ and $b=uH^3$:

$$
M(z,u)=\frac{1}{1-az}C\!\left(\frac{bz^2}{(1-az)^2}\right),\quad
T_r(u)=[z^r]M(z,u),\quad
G_r=H^2(T_r+T_{r+1})-u(1-u)H(T_r+2T_{r+1}+T_{r+2}).
$$

Here $C(w)=\sum_{j\ge0}C_jw^j$ is the Catalan series, $C(0)=1$ and
$C=1+wC^2$. All inverses in $z$ have constant term one, and every $T_r$
is a polynomial in $u$. Substitution of $u=q(t)$ into a polynomial is
therefore defined; substitution into a series in $u$ is also defined
because $q(0)=0$.

The source parameters are those of Chen, Kitaev and Zhang,
[*Distributions of statistics on separable permutations*,
arXiv:2404.18517v1](https://arxiv.org/pdf/2404.18517v1), Sections 1, 1.2
and 2.2. The same definitions and equations (20)--(22) occur in their
[author manuscript](https://zhangbiaomath.github.io/papers/2024-dam-separable-perms.pdf).
The correspondence is

| Source notation or convention | Notation here |
| --- | --- |
| A permutation $\pi_1\cdots\pi_n$ of $[n]$ | The permutation $p(i)=\pi_{i+1}-1$ of $\{0,\ldots,n-1\}$ |
| A reducibility split at source index $j$, $2\le j\le n$ | A proper direct cut $c=j-1$, $0<c<n$ |
| $S(t)$, excluding the empty permutation | $q(t)$ |
| $I(t)$, the unmarked irreducible series | $I_0(t)$ of Definition 3.1 |
| $S(t,y)$, with only rmax marked | $U(t,y)$ of Definition 3.1 |
| $I(t,y)$, with only rmax marked | $J(t,y)$ |
| Source $y$ and the source record index $k$ | The same $y$ and $k$, without an index shift |

The independent $u$ in $M$ is specialized to the unmarked series $q(t)$;
it is unrelated to the source's lmin marker. Likewise, $q(t)$ here is
unrelated to the source's descent marker. Reindexing positions and values
by the displayed order-preserving bijections preserves every strict record
comparison and every cut condition.

**Theorem 8.2 (The actual-fiber identity).** One has $J_0=0$, $J_1=t$,
and for every integer $k\ge2$,

$$
J_k(t)=t^kH(q(t))^2
\sum_{r=0}^{k-2}\binom{k-2}{r}T_r(q(t)).
$$

For every integer $k\ge3$, the exact adjacent difference is

$$
J_k(t)-J_{k+1}(t)
=t^k\sum_{r=0}^{k-3}\binom{k-3}{r}G_r(q(t)).
$$

Both sums are finite, and every scalar multiplier in the second sum is
a nonnegative integer.

Proof. Use the actual scalar and weighted equations of Theorem 3.2:

$$
q=t+tq+q^2,\qquad
J=ty+ty(1+q)J+q(1+q)J^2,\qquad [y^0]J=0.
$$

These are the actual-fiber equations, with the source correspondence in
Definition 8.1. More explicitly, source equation (20) gives
$U-J=I_0U=qJ$, whence $U=(1+q)J$. Equation (22) then gives
$J=ty(1+U)+(U-J)U$, which is precisely the displayed weighted quadratic.
Equation (21) is consistent with this reduction because
$I_0(1+q)=q$, as in Theorem 3.2. Thus the coefficients being extracted
are the actual positive permutation fibers.

First work over the polynomial ring $\mathbb Q[u]$. There is a unique
$F(x,u)\in x\mathbb Q[u][[x]]$ satisfying

$$
F=x+HxF+uHF^2.
$$

Indeed, if $F=\sum_{k\ge1}p_k(u)x^k$, the equation recursively specifies

$$
p_1=1,\qquad
p_k=Hp_{k-1}+uH\sum_{j=1}^{k-1}p_jp_{k-j}\quad(k\ge2).
$$

Every term on the right has a smaller positive index, proving both
existence and uniqueness coefficient by coefficient. The actual quadratic
has the corresponding recurrence

$$
J_1=t,\qquad
J_k=tH(q)J_{k-1}+qH(q)\sum_{j=1}^{k-1}J_jJ_{k-j}\quad(k\ge2).
$$

Induction therefore gives $J_k=t^kp_k(q)$ for every $k\ge1$.
Equivalently $J(t,y)=F(ty,q(t))$. This substitution is legitimate in
$\mathbb Q[[t]][[y]]$: at each fixed $y$-degree there is a single
polynomial coefficient $p_k(q)$ multiplied by $t^k$. The equality is
proved by recurrence and does not require division by $t$.

To compute $F$, the defining Catalan equation gives, for the very same
$M$ as in Definition 7.1,

$$
(1-az)M=1+bz^2M^2,\qquad M=1+azM+bz^2M^2.
$$

For example, its explicit coefficient expansion is

$$
M=\sum_{j\ge0}C_jb^jz^{2j}(1-az)^{-2j-1},\qquad
T_r=\sum_{j=0}^{\lfloor r/2\rfloor}
 C_j\binom{r}{2j}a^{r-2j}b^j.
$$

The coefficient formula follows by expanding $(1-az)^{-2j-1}$: its
coefficient at $z^{r-2j}$ is $\binom{r}{2j}a^{r-2j}$, and terms with
$2j>r$ vanish. In particular the series constructed here has exactly the
supplied polynomial coefficients, with $T_0=1$ and $T_1=a$.

Set

$$
B(x,u)=\frac{1}{1-x}M\!\left(\frac{x}{1-x},u\right),\qquad
B_m(u)=[x^m]B(x,u).
$$

The inner substitution has zero constant term. Substituting
$z=x/(1-x)$ and $M=(1-x)B$ into the quadratic for $M$ gives

$$
(1-x)B=1+axB+bx^2B^2,\qquad
B=1+(1+a)xB+bx^2B^2.
$$

Now $1+a=H(1+2u)$ and $b=uH^3$. Put $\widetilde F=x+x^2H^2B$.
Direct expansion yields

$$
\begin{aligned}
x+Hx\widetilde F+uH\widetilde F^2
 &=x+x^2H^2\bigl(1+H(1+2u)xB+uH^3x^2B^2\bigr)\\
 &=x+x^2H^2B=\widetilde F.
\end{aligned}
$$

Since $\widetilde F$ has zero constant term, uniqueness gives
$F=\widetilde F$. Hence $p_k=H^2B_{k-2}$ for $k\ge2$.
The definition of $B$ also gives

$$
B(x,u)=\sum_{r\ge0}T_r(u)\frac{x^r}{(1-x)^{r+1}},\qquad
B_m(u)=\sum_{r=0}^m\binom{m}{r}T_r(u).
$$

Here the coefficient of $x^{m-r}$ in $(1-x)^{-r-1}$ is
$\binom{m}{r}$; only $r\le m$ contributes. Combining this equality with
$J_k=t^kp_k(q)$ proves the first displayed formula of the theorem.
The zero-record fiber is empty at every positive length, giving $J_0=0$.

For the difference formula, let $m=k-3\ge0$. Pascal's identity, extending
binomial coefficients by zero outside their usual range, gives

$$
\begin{aligned}
B_{m+1}&=\sum_{r=0}^m\binom mr(T_r+T_{r+1}),\\
B_{m+2}&=\sum_{r=0}^m\binom mr(T_r+2T_{r+1}+T_{r+2}).
\end{aligned}
$$

For the first equality, the coefficient of $T_j$ on the right is
$\binom mj+\binom m{j-1}=\binom{m+1}j$, including $j=0,m+1$.
Applying that identity twice proves the second equality, including
$j=0,m+2$. Thus no endpoint term is omitted.
The scalar quadratic gives $tH(q)=q(1-q)$. Therefore

$$
\begin{aligned}
J_k-J_{k+1}
 &=t^k\bigl(H(q)^2B_{m+1}(q)-tH(q)^2B_{m+2}(q)\bigr)\\
 &=t^k\bigl(H(q)^2B_{m+1}(q)
             -q(1-q)H(q)B_{m+2}(q)\bigr)\\
 &=t^k\sum_{r=0}^m\binom mr
   \bigl(H^2(T_r+T_{r+1})
       -u(1-u)H(T_r+2T_{r+1}+T_{r+2})\bigr)\big|_{u=q}.
\end{aligned}
$$

The last parenthesis is exactly $G_r$. The formula includes $k=3$,
when $m=0$ and the sum consists of $G_0(q)$ alone. In that case the
polynomial $G_0$ is the $F$ of Theorem 6.2, so this endpoint agrees with
the existing first-decline formula.

The weighted quadratic and its low coefficients are the intermediates
of Theorem 3.2 and
[RecordPeak.actual_record_rising](../../../D5/S1/Words/Patterns/Separable/RecordPeak.lean);
the same actual quadratic occurs in the proof of
[RecordFirstDecline.actual_four_record_first_decline](../../../D5/S1/Words/Patterns/Separable/RecordFirstDecline.lean).
The inference here is the all-$k$ identity
$F=x+x^2H^2(1-x)^{-1}M(x/(1-x),u)$ and its two binomial shifts,
which identify every actual adjacent difference with the fixed kernels.

**Theorem 8.3 (The four distributions have a weak maximum at three).**
For each pair $(X,s)$ in Definition 8.1, every $n\in\mathbb N$ and every
$k\ge3$ satisfy

$$
a_{X,s}(n,k+1)\le a_{X,s}(n,k).
$$

For each such pair, every $n\ge5$ and every $k\in\mathbb N$ satisfy

$$
\begin{aligned}
k<3&\ \Longrightarrow\ a_{X,s}(n,k)\le a_{X,s}(n,k+1),\\
k\ge3&\ \Longrightarrow\ a_{X,s}(n,k+1)\le a_{X,s}(n,k),\\
a_{X,s}(n,k)&\le a_{X,s}(n,3).
\end{aligned}
$$

These are the full four distributions, with a weak peak as in
Chen--Kitaev--Zhang, arXiv:2404.18517v1, Section 3, Conjecture 2,
page 17, and Table 4.

Proof. Theorem 7.2, supplied by
[RecordNewtonPositivity.actual_q_record_newton_nonnegative](../../../D5/S1/Words/Patterns/Separable/RecordNewtonPositivity.lean),
gives $[t^h]G_r(q(t))\ge0$ for every $r,h\in\mathbb N$.
For $k\ge3$, take the coefficient of $t^n$ in Theorem 8.2. Since $J$
counts the positive actual fibers and $i(0,k)=0$, this gives the exact
rational identity, at every natural $n$,

$$
i(n,k)-i(n,k+1)=
\begin{cases}
\displaystyle\sum_{r=0}^{k-3}\binom{k-3}{r}
 [t^{n-k}]G_r(q(t)),&n\ge k,\\
0,&n<k.
\end{cases}
$$

Every summand in the first case is nonnegative by the cited sign law;
the second case is zero. Consequently $i(n,k+1)\le i(n,k)$ for all
natural $n$ and all $k\ge3$.

Use the exact transports of Theorem 5.2, supplied by
[RecordTransport.actual_four_record_transports_and_rising](../../../D5/S1/Words/Patterns/Separable/RecordTransport.lean):

$$
a_{\mathrm{irreducible},\mathrm{lmin}}(n,j)=i(n,j),\qquad
a_{\mathrm{reducible},\mathrm{lmax}}(n,j)+\delta(n,j)=i(n,j),\qquad
a_{\mathrm{reducible},\mathrm{rmin}}(n,j)+\delta(n,j)=i(n,j).
$$

Here $\delta(n,j)=1$ exactly at $n=j=1$. If $k\ge3$, both
$\delta(n,k)$ and $\delta(n,k+1)$ vanish for every $n$. The three
transport identities therefore carry the declining inequality to the
other three distributions at every natural length, including zero and
one. No positive-class convention changes at these endpoints.

For $n\ge5$, Theorem 5.2 supplies all three rising comparisons $k<3$
for these same four distributions; its hypothesis is only $n\ge4$.
Fix one pair and such an $n$. If $k<3$, the finite rising chain from $k$
to $3$ gives $a_{X,s}(n,k)\le a_{X,s}(n,3)$. If $k=3$ this is equality.
If $k>3$, apply the declining comparison successively at
$3,4,\ldots,k-1$ to obtain the same bound. These chains prove both
unimodality and the global weak maximum at three.

Every record-position set is a subset of the $n$ positions, so all four
fibers are zero for $k>n$. At length zero both positive classes are empty;
at length one the two irreducible distributions have their sole mass at
$k=1$ and the two reducible distributions are zero. These facts agree
with the all-length declining law and include the zero tails in the
unimodality assertion. The sign law, the rising laws, the transports and
the strict first decline of Theorem 6.2 are cited inputs; the all-index
actual-fiber identity of Theorem 8.2 supplies their connection to every
remaining declining comparison.

## 追加锚（本行以下为增补区）
