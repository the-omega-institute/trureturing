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
