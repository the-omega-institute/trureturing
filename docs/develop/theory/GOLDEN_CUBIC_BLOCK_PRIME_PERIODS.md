# Prime periods of the golden cubic blocks

Let $F_0=0$, $F_1=1$, $L_0=2$, and $L_1=1$ be the Fibonacci and Lucas
sequences. For a natural number $j\geq 1$ set $n=3^{j+1}$ and
$B_j=L_{3^j}^2+3$, $C_j=L_{3^j}^2+1$. Let $\phi$ be the golden
quadratic integer satisfying $\phi^2=\phi+1$. Write
$Q=\begin{pmatrix}1&1\\1&0\end{pmatrix}$, and let $\tau_p$ denote the
multiplicative order of $Q$ over $\mathbb Z/p\mathbb Z$.

## 1. Exact periods at prime factors

**Theorem 1.1 (Lucas block).** For every natural number $j\geq 1$ and every prime
$p$ dividing $B_j$, one has $\tau_p=2\cdot 3^{j+1}$.

The rank of apparition of $p$ is $2n$. The cubic Lucas identity gives
$L_n=L_{3^j}B_j$, so $L_n=0$ modulo $p$. In the quadratic golden algebra,
the element $\phi^n$ has trace zero and norm $-1$, since $n$ is odd.
Its quadratic identity therefore gives $(\phi^n)^2=1$ modulo $p$.
Thus the order of $\phi$ divides $2n$. Conversely, the second coordinate
of $\phi^t$ is $F_t$; if $\phi^t=1$, then $p$ divides $F_t$, so the rank
$2n$ divides $t$. The faithful multiplication-matrix representation sends
$\phi$ to $Q$ and preserves its order. Hence $\tau_p=2n$.

**Theorem 1.2 (Fibonacci block).** For every natural number $j\geq 1$ and every
prime $p$ dividing $C_j$, one has $\tau_p=4\cdot 3^{j+1}$.

The rank of apparition of $p$ is $n$, so $F_n=0$ modulo $p$.
The Fibonacci-coordinate formula for $\phi^n$ makes it the scalar
$F_{n-1}$ modulo $p$. Cassini's identity at this odd $n$ gives
$F_{n-1}^2=-1$ modulo $p$. The block $C_j$ is odd, hence $p\ne2$;
therefore $-1\ne1$ modulo $p$. Consequently $\phi^n$ has order exactly
four. The rank $n$ divides the order of $\phi$, because every return
$\phi^t=1$ forces $F_t=0$ modulo $p$. The order-of-a-power formula now
gives $\operatorname{ord}(\phi)=4n$, and the faithful matrix representation
transfers this order to $Q$.

## 追加锚（本行以下为增补区）

## 2. Native periods of block powers

For $j\geq 1$, retain $B_j=L_{3^j}^2+3$ and $C_j=L_{3^j}^2+1$.
For a prime $p$ dividing either block, let $h_p$ be the valuation of
$F_{\rho(p)}$ at $p$, where $\rho(p)$ is the first positive Fibonacci zero
modulo $p$. Write $\pi(m)$ for the order of $Q$ modulo the positive integer
$m$.

**Theorem 2.1 (native block-power periods).** The prime supports of all
$B_j$ and $C_j$ are pairwise disjoint, including across distinct indices.
For every $j,a,b\geq 1$,

$$
\begin{aligned}
\pi(C_j^a)&=4\cdot3^{j+1}C_j^{a-1},\\
\pi(B_j^b)&=2\cdot3^{j+1}B_j^{b-1},\\
\pi(C_j^aB_j^b)&=4\cdot3^{j+1}C_j^{a-1}B_j^{b-1}.
\end{aligned}
$$

Proof. A prime of $C_j$ has rank $3^{j+1}$, and a prime of $B_j$ has
rank $2\cdot3^{j+1}$. Equality of the ranks would force equal indices
and equal block types, giving the support claim. The corresponding matrix
periods are $4\cdot3^{j+1}$ and $2\cdot3^{j+1}$, respectively. If $p$
occurs in a block to exponent $h_p$, the original Fibonacci valuation
law and the matrix identity $Q^n=F_nQ+F_{n-1}I$ show that $Q$ first
returns modulo $p^{a h_p}$ after its prime-level period multiplied by
$p^{(a-1)h_p}$. In particular the depth is measured in the original
Fibonacci sequence; it is not reset to one. Every block is coprime to
six, so these extra prime powers are coprime to the common base period.
The Chinese remainder theorem takes the least common multiple of the
local periods, yielding the three displayed formulas.

The local depth step uses the exact matrix lift: if $t$ is the period
modulo $p$, then $F_t$ and $F_{t-1}-1$ have the same positive $p$-adic
valuation. Indeed $t$ is even and Cassini gives
$(F_{t-1}-1)(F_{t-1}+1)=F_t(F_t-F_{t-1})$; the latter two factors are
$p$-adic units for $p>5$. Thus $Q^t=I+p^{h_p}A$ with $A$ nonzero modulo
$p$. Binomial expansion raises the depth by exactly one on each $p$th
power and preserves it on prime-to-$p$ powers. Every return exponent
is a multiple of $t$, giving the exact local period used above.

The block ranks, original valuations, and prime-level periods are the
preceding results; the block-power conclusion is the new assertion of
this section. No claim that $h_p=1$ is used.

## 追加锚（本行以下为增补区）

## 3. Entry ranks and original depths of block factors

Retain $B_j=L_{3^j}^2+3$ and $C_j=L_{3^j}^2+1$ for $j\geq1$. For a
prime $p$, let $\rho(p)$ be the least positive index with $p\mid F_{\rho(p)}$.
The valuations below are taken in the original Fibonacci sequence.

**Theorem 3.1 (Fibonacci block rank).** For every $j\geq1$ and prime
$p\mid C_j$,
$$
\rho(p)=3^{j+1},\qquad v_p(C_j)=v_p(F_{\rho(p)}).
$$

Proof. Put $n=3^j$. The cubic Fibonacci identity is
$F_{3n}=F_n C_j$. The Lucas discriminant identity and the block
congruence exclude $p\mid F_n$ and $p=3$. Therefore $p\mid F_{3n}$,
while $p\nmid F_n$. The first-zero rank divides $3n$, so it must be
$3n=3^{j+1}$. Since $p\nmid F_n$, the product identity gives
$v_p(C_j)=v_p(F_{3n})$.

**Theorem 3.2 (Lucas block rank).** For every $j\geq1$ and prime
$p\mid B_j$,
$$
\rho(p)=2\cdot3^{j+1},\qquad
\left(\frac5p\right)=1,\qquad
v_p(B_j)=v_p(F_{\rho(p)}).
$$

Proof. Put $n=3^j$ and $r=3n$. The cubic Lucas identity gives
$L_r=L_n B_j$, and the duplication identity gives $F_{2r}=F_rL_r$.
The discriminant identity and the block congruences exclude $p=2,3,5$
and show that $p$ divides neither $F_n$, $L_n$, $F_{2n}$ nor $F_r$.
Thus $p\mid F_{2r}$, but its first-zero rank cannot divide $r$ or
$2n$. Since the rank divides $2r=2\cdot3^{j+1}$, it equals $2r$.
At $L_r=0$ modulo $p$, the odd-index discriminant identity gives
$5F_r^2=4$ modulo $p$, so five is a quadratic residue. Both $F_r$
and $L_n$ are $p$-units, and $F_{2r}=F_rL_nB_j$ gives the valuation.

## 追加锚（本行以下为增补区）

## 4. Cubic block congruences

Write $x_j=L_{3^j}$, $B_j=x_j^2+3$, and $C_j=x_j^2+1$ for $j\geq1$.

**Theorem 4.1 (Lucas congruences).** For every $j\geq1$,
$x_j\equiv4\pmod{72}$, $v_2(x_j)=2$,
$B_j\equiv1\pmod9$, $x_j^2\equiv1\pmod5$, and
$B_j\equiv19\pmod{80}$. Moreover $x_{j+1}=x_jB_j$.

**Theorem 4.2 (Fibonacci congruences).** For every $j\geq1$,
$F_{3^j}\equiv2\pmod4$, $v_2(F_{3^j})=1$, and
$F_{3^{j+1}}=F_{3^j}C_j$.

**Theorem 4.3 (interlevel residues).** If $1\leq i<j$, then
$B_j\equiv3\pmod{B_i^2}$.

**Theorem 4.4 (block product).** For every $j\geq1$,
$$
L_{3^j}=4\prod_{i=1}^{j-1}B_i.
$$

## 5. Finite Fibonacci rank closure

For every natural $p$, let $\rho(p)$ be the least positive $r$ for which
$p\mid F_r$ when $p$ is prime, and set $\rho(p)=1$ otherwise. For a
finite set $S$ of primes greater than five, set
$B=\max(5,\sup S)$, where $\sup\varnothing=0$,
$H_0=S\cup\{2,3,5\}$, and
$T(H)=H\cup\bigcup_{p\in H}\operatorname{PrimeDivisors}(\rho(p))$.
Let $U$ be the set of primes at most $B$, and set $H(S)=T^{|U|}(H_0)$.

**Theorem 5.1 (finite least closure).** For every such $S$, $H(S)$
contains $H_0$; every element of $H(S)$ is prime and at most $B$;
$T(H(S))=H(S)$; and $H(S)$ is contained in every finite $K$ satisfying
$H_0\subseteq K$ and $T(K)\subseteq K$.

## 6. Prime-to-index original depth

Retain the least positive Fibonacci entry rank $\rho(p)$ for each prime $p$.

**Theorem 6.1 (original rank depth).** If a prime $p$ divides $F_n$
but does not divide $n$, then
$$
v_p(F_n)=v_p(F_{\rho(p)}).
$$

## 7. Faithful golden matrix

For each natural modulus $m$, write a golden residue as $z=a+b\phi$,
where $\phi^2=\phi+1$. On the basis $(\phi,1)$, multiplication by $z$
has matrix
$$
M_m(z)=\begin{pmatrix}a+b&b\\b&a\end{pmatrix}
\quad\text{over }\mathbb Z/m\mathbb Z.
$$

**Theorem 7.1 (faithful period representation).** The map $M_m$ is an
injective ring homomorphism for every natural modulus $m$. It sends
$\phi$ to $Q=\begin{pmatrix}1&1\\1&0\end{pmatrix}$, and the
multiplicative orders of $\phi$ and $Q$ are equal.

## 追加锚（本行以下为增补区）

## 8. Oriented cubic factors and the original-depth balance

Retain $x_j=L_{3^j}$, $B_j=x_j^2+3$, and the original depth
$h_p=v_p(F_{\rho(p)})$ for $j\geq1$ and $p\mid B_j$. In the Eisenstein
integers $\mathbb Z[\omega]$, let $\omega^2+\omega+1=0$ and
$\lambda=1+2\omega$. A generator is *primary* when it is congruent to
$1$ modulo $3$. For a prime ideal away from $3$, write
$(a/\mathfrak p)_3$ for its cubic residue symbol, and extend the symbol
multiplicatively to coprime ideal denominators. The classical cubic
reciprocity and supplementary laws used below are the identities in
Dunn and Radziwill, *Bias in cubic Gauss sums: Patterson's conjecture*,
arXiv:2109.07463v3, equations (1.4)-(1.5). No conditional analytic
result of that paper is used.

**Theorem 8.1 (oriented block factorization).** Put
$\eta_j=-2+(x_j-1)\omega=\omega(x_j+\lambda)$. Then

$$
N(\eta_j)=B_j,\qquad
\eta_j\equiv1+\lambda^3\pmod9.
$$

The ideals $(\eta_j)$ and $(\overline{\eta_j})$ are coprime. For each
rational prime $p\mid B_j$, exactly one prime above $p$ divides
$\eta_j$; write $\varpi_{j,p}$ for its primary generator. Then

$$
\eta_j=\prod_{p\mid B_j}\varpi_{j,p}^{h_p},
\qquad N(\varpi_{j,p})=p.
$$

The norm follows from the Eisenstein norm form, and the congruence from
$x_j\equiv4\pmod9$. A common prime ideal of $\eta_j$ and its conjugate
would divide $2\lambda$, whereas $\gcd(B_j,6)=1$. Every prime factor of
$B_j$ is congruent to $1$ modulo $3$, so it splits. The norm identifies
the exponent in the oriented factorization with $v_p(B_j)=h_p$.
Both sides are primary; hence the remaining unit is $1$.

**Theorem 8.2 (cubic balance).** For every $j\geq1$,

$$
\prod_{p\mid B_j}\left(\frac{3}{\varpi_{j,p}}\right)_3^{h_p}
=\omega.
$$

If $(3/\varpi_{j,p})_3=\omega^{c_{j,p}}$ with
$c_{j,p}\in\{0,1,2\}$, equivalently

$$
\sum_{p\mid B_j}h_pc_{j,p}\equiv1\pmod3.
$$

The supplementary laws applied to Theorem 8.1 give
$(\omega/\eta_j)_3=1$ and $(\lambda/\eta_j)_3=\omega^2$.
Since $3=-\lambda^2$ and $-1$ is a cube, their product gives
$(3/\eta_j)_3=\omega$. Multiplicativity and the oriented factorization
give the displayed product and sum.

**Corollary 8.3 (noncube block).** Every $B_j$ has a prime factor $p$
with $3\nmid h_p$ and
$3^{(p-1)/3}\not\equiv1\pmod p$. In particular, $B_j$ is not a
cube in $\mathbb Z$. The cubic balance has a nonzero summand, which
supplies this factor. A cube would make every $h_p$ divisible by $3$.

## 追加锚（本行以下为增补区）

## 9. Scalar contraction of an Eisenstein factor

Let $E=\mathbb Z[\omega]$, where $\omega^2+\omega+1=0$. For an odd natural
number $b$, put $\eta_b=-2+b\omega$ and $B_b=b^2+2b+4$.

**Theorem 9.1 (scalar contraction and quotient).** The principal ideal of
$\eta_b$ contracts to $B_b\mathbb Z$:

$$
(\eta_b)\cap\mathbb Z=B_b\mathbb Z.
$$

The scalar inclusion also induces a ring isomorphism

$$
\mathbb Z/B_b\mathbb Z\;\xrightarrow{\ \sim\ }\;E/(\eta_b).
$$

To verify the contraction, write an Eisenstein integer as $u+v\omega$. The
coefficient of $\omega$ in $\eta_b(u+v\omega)$ is
$bu-(b+2)v$. Since $b$ is odd, $b$ and $b+2$ are coprime; a scalar
multiple therefore has $u=(b+2)t$ and $v=bt$ for some integer $t$,
and its scalar coefficient is $-B_bt$. Conversely,
$B_b=\eta_b\overline{\eta_b}$ belongs to $(\eta_b)$.
For surjectivity of the induced map, $\gcd(b,B_b)=1$ because
$B_b\equiv4\pmod b$ and $b$ is odd. In the quotient, $B_b=0$ and
$b\omega=2$; Bezout coefficients for $b$ and $B_b$ consequently express
$\omega$ as the image of an integer. Every quotient class is an integer
combination of $1$ and $\omega$, hence lies in the scalar image.

## 追加锚（本行以下为增补区）

## 10. Square-class groups and an explicit original-depth escape bound

### 10.1 Fixed objects and classical input

Keep the original positive Fibonacci values. For a prime $p$ write
$\rho(p)=\min\{r\geq1:p\mid F_r\}$ and $h_p=v_p(F_{\rho(p)})$.
For $p>5$, $h_p=v_p(F_{p-(5/p)})$; thus WSS means $h_p\geq2$.
For a positive integer $a$ let $\operatorname{Supp}(a)$ be its prime
support, and put
$$d(n)=\prod_{v_p(F_n)\ {\rm odd}}p\qquad(n\geq1).$$
The positive rational square-class group is
$$\mathcal G=\mathbb Q_{>0}^{\times}/(\mathbb Q_{>0}^{\times})^2
 \simeq\bigoplus_{p\ {\rm prime}}\mathbb F_2.$$
The coordinate of $[a]$ at $p$ is $v_p(a)\bmod2$. For a finite prime
set $H$, let $\mathcal G_H=\langle[p]:p\in H\rangle$; it is isomorphic
to $(\mathbb Z/2)^{|H|}$. The condition $[F_n]\in\mathcal G_H$ is
exactly $\operatorname{Supp}(d(n))\subseteq H$.

Two classical inputs are used with their full hypotheses. First, the
Fibonacci valuation formulas of Lengyel, as restated in Medina-Rowland,
Theorem 1.4, are
$$
v_p(F_n)=
\begin{cases}h_p+v_p(n),&\rho(p)\mid n,\\0,&\rho(p)\nmid n,
\end{cases}\quad(p\ne2,5),\qquad v_5(F_n)=v_5(n),
$$
and
$$v_2(F_n)=\begin{cases}0,&3\nmid n,\\1,&n\equiv3\pmod6,\\
v_2(n)+2,&6\mid n.\end{cases}$$
The small ranks are $\rho(2)=3$, $\rho(3)=4$, $\rho(5)=5$.
Second, the classical Fibonacci square-class theorem says that the only
nonsingleton classes of positive indices are $\{1,2,12\}$ and $\{3,6\}$.
It is stated in Ribenboim, *FFF: (Favorite Fibonacci Flowers)* (2005),
(3.4), with attribution to his earlier paper. In particular, distinct
indices whose ratio is $25$ never have square-equivalent Fibonacci
values. These classical results are inputs, not new proofs of square-class
rigidity or consequences of the coordinate-ring formalization.
The source scopes are recorded in
`Library/Recurrence/ribenboim2005squareclasses.md`.

### 10.2 Support descent for a specified square-class subgroup

A finite prime set $H$ is rank-closed if
$\operatorname{Supp}(\rho(p))\subseteq H$ for every $p\in H$.
Throughout this section assume $\{2,3,5\}\subseteq H$ and define
$$R_H=\operatorname{lcm}_{p\in H}\rho(p).$$
Then $60\mid R_H$ and $\operatorname{Supp}(R_H)\subseteq H$.

**Lemma 10.1 (support descent).** If $[F_n]\in\mathcal G_H$, then
$\operatorname{Supp}(n)\subseteq H$.

Proof. Suppose otherwise and choose the largest prime $\ell\mid n$
outside $H$. It exceeds five. Every prime $p\mid F_\ell$ has exact
rank $\ell$ and satisfies $p>\ell$: the rank divides $p-1$ or $p+1$,
and the putative equality $p+1=\ell$ is excluded by parity. The rank
cannot be one, and the small primes are excluded by their small ranks.
If such a $p$ divided $n$, maximality of $\ell$ outside $H$ would imply
$p\in H$, whose rank-closure would imply $\ell\in H$, a contradiction.
Thus $p\nmid n$, and the prime-to-index valuation formula gives
$v_p(F_n)=v_p(F_\ell)=h_p$.
The nonsquare $F_\ell$ has an odd-exponent factor $p$. It remains odd in
$F_n$, hence lies in $H$ by hypothesis. Its rank again forces
$\ell\in H$, the same contradiction. This is the earlier OSE
largest-prime-outside-closure argument with a square-class hypothesis.

### 10.3 Odd witnesses in prime-power quotient layers

**Lemma 10.2 (prime-power layer).** Let $q\ne5$ be prime, let $s\geq1$,
and exclude $(q,s)=(2,1)$. The actual positive integer
$$C_{q,s}=F_{q^s}/F_{q^{s-1}}$$
is greater than one, is coprime to $F_{q^{s-1}}$, and is not a square.
Every prime $p\mid C_{q,s}$ satisfies
$$\rho(p)=q^s,\qquad p\ne q,\qquad v_p(C_{q,s})=h_p.$$
In particular there is such a $p$ with odd original depth.

Proof. Fibonacci divisibility and strict growth give the integer quotient
and positivity; the omitted case has quotient one. The rank bound shows
$q\nmid F_{q^s}$ for odd $q\ne5$, since $\rho(q)>1$ is prime to $q$.
For $q=2$, $\rho(2)=3$ gives the same exclusion. An old prime
$p\mid F_{q^{s-1}}$ is therefore different from $q$. For odd $p\ne5$
its valuation is unchanged under multiplication of the index by $q$.
Five cannot occur because $q\ne5$. If the old prime is two, necessarily
$q=3$ and both indices are odd multiples of three, so both valuations
are one. This proves coprimality.
Any new prime has rank a divisor of $q^s$ which does not divide
$q^{s-1}$, hence exactly $q^s$. The same valuation formulas give its
original depth, including $p=2$ at $(q,s)=(3,1)$ and $p=3$ at $(2,2)$.
If the quotient were square, the distinct positive indices $q^{s-1}$
and $q^s$ would lie in one classical square class. Inspection of the
two exceptional classes leaves only the excluded pair $1,2$.
Thus the quotient has an odd-exponent prime.
For $q\geq7$ the rank and nonsquare layer mechanism is already present
in PBC.3. The small-index clauses here ensure it can be used for every
prime except the ramified prime five.

The exclusion of five is essential to this cancellation argument:
$F_{25}/F_5=5\cdot3001$ still shares a factor five with $F_5$.
No nonsquare statement about that quotient with five removed is assumed.

### 10.4 A divisibility bound replacing an unspecified height cutoff

**Theorem 10.3 (explicit rank budget).** For every $n\geq1$,
$$\boxed{[F_n]\in\mathcal G_H\quad\Longrightarrow\quad n\mid5R_H.}
 \tag{GSE1}$$
More precisely,
$$v_q(n)\leq v_q(R_H)\ (q\ne5),\qquad
  v_5(n)\leq v_5(R_H)+1.$$

Proof. Lemma 10.1 puts all index primes in $H$. Let $q\ne5$ divide $n$
and suppose $e=v_q(n)>v_q(R_H)$. Lemma 10.2 applies to $(q,e)$:
the only excluded case is impossible since $4\mid R_H$.
Choose an odd-exponent prime $p$ in $C_{q,e}$. Its rank $q^e$ cannot
divide $R_H$, so $p\notin H$. Consequently $p\nmid n$, by Lemma 10.1.
Since $q^e\mid n$, the original prime-to-index valuation gives
$v_p(F_n)=h_p$, an odd integer. This contradicts
$\operatorname{Supp}(d(n))\subseteq H$. The primes two and three
cannot be this $p$, because they already belong to $H$.
This proves all non-five bounds, without assuming their depths equal one.

Set $a=v_5(R_H)\geq1$. If $e=v_5(n)\geq a+2$, put $m=n/25$.
For every $p\in H$, the condition $\rho(p)\mid n$ is equivalent to
$\rho(p)\mid m$: only the five-exponent has decreased, and it remains
at least the five-exponent of every rank. For $p\in H\setminus\{2,5\}$
the valuation formulas then give the same valuation in $F_n$ and $F_m$.
At five the valuations differ by two. At two, division of an index by
$25$ preserves its two-valuation and divisibility by three, so the small
valuation formula gives equality. Outside $H$, primes do not divide $n$
or $m$. Any such prime occurring in $F_m$ also occurs in $F_n$, with the
same original valuation, which is even by the square-class hypothesis.
Other outside primes have even valuation in $F_n$ and zero in $F_m$.
Thus all valuation parities agree:
$$[F_n]=[F_m]\quad\hbox{in }\mathcal G.$$
But $n/m=25$ and $m<n$, contradicting the classical square-class
exceptions. Hence $e\leq a+1$. These prime-exponent bounds prove GSE1.

The group step is the explicit cancellation of an EVEN shift in the
valuation vector once rank-divisibility thresholds are preserved.
No claim is made that $n\mapsto[F_n]$ is a homomorphism.

### 10.5 Original odd-depth support: exact finite candidate sets

For positive $n$ define
$$U(n)=\{p>5:p\mid F_n,\ p\nmid n,\ h_p\text{ odd}\},$$
$$T(n)=\{p>5:p\mid F_n,\ h_p\geq3\text{ odd}\}.$$
For a finite set $S$ of primes greater than five let $H(S)$ be the
closure of Section 5, and put $R_S=R_{H(S)}$.

**Corollary 10.4 (finite-support divisor set).** One has
$$\boxed{U(n)\subseteq S\quad\Longrightarrow\quad n\mid5R_S.}
 \tag{GSE2}$$
If $\mathcal P(S)=\{n\geq1:F_n\text{ powerful},\ T(n)\subseteq S\}$,
then
$$\boxed{\mathcal P(S)=
 \{n\mid5R_S:F_n\text{ powerful},\ T(n)\subseteq S\}.}\tag{GSE3}$$
In particular the earlier OSE bound can be combined with the divisor bound:
$$\#\mathcal P(S)\leq
 \min\bigl(2^{|H(S)|}-4,\ \tau(5R_S)\bigr).$$

Proof. The existing OSE support descent gives
$[F_n]\in\mathcal G_{H(S)}$ from $U(n)\subseteq S$; Theorem 10.3 applies.
In a powerful value, an external odd original depth is at least three,
so $U(n)\subseteq T(n)$. This proves both inclusions in GSE3 and the
stated bounds. The $2^{|H|}-4$ estimate is the earlier square-class
count, not newly claimed here.

**Proposition 10.5 (an exact finite procedure).** Both the set
$\{n\geq1:U(n)\subseteq S\}$ and $\mathcal P(S)$ can be computed by
examining the divisors of $5R_S$. Complete factorization of those large
Fibonacci values is unnecessary.

Proof. Compute the finite closure and its ranks, then factor $5R_S$ and
enumerate its divisors. Every such divisor is supported in $H(S)$.
For each candidate $n$, compute $F_n$ and remove all powers of primes
in $H(S)$, giving a positive remaining integer $Z_n$. An integer square
root decides whether $Z_n$ is square. If it is not, the candidate fails
the necessary kernel-support condition. If it is, every outside factor
has even valuation and is prime to $n$, so it has even original depth.
Hence all members of $U(n)$ and $T(n)$ belong to $H(S)$ and can be
checked individually using the known ranks and $h_p$ there. Powerfulness
holds exactly when none of the removed positive exponents equals one;
the outside exponents are already even. This decides both sets.
This is a termination statement with explicit cutoff $5R_S$, not a
polynomial-time bound. Ranks, closure and the cutoff may still be large.

For the specified set $S=\{13\}$, its closure is
$H(S)=\{2,3,5,7,13\}$ and $R_S=840$. The procedure has 48 candidate
divisors of 4200. Exact evaluation gives
$$\{n\geq1:U(n)\subseteq\{13\}\}
 =\{1,2,3,4,5,6,7,12\}.$$
The completeness of this finite certificate uses GSE2, rather than a
freely chosen scan cutoff. Thirteen is not asserted to be WSS.

### 10.6 Uniform escape in terms of the largest allowed original prime

For an integer $Q\geq5$ define
$$Y_Q=\max\left(5,\left\lfloor\frac{Q+1}{2}\right\rfloor\right),
 \qquad L(Y)=\operatorname{lcm}(1,2,\ldots,Y).$$

**Theorem 10.6 (uniform lcm escape).** For every positive $n$,
$$\boxed{U(n)\subseteq\{p:p\leq Q\}
 \quad\Longrightarrow\quad n\mid10L(Y_Q).}\tag{GSE4}$$
Equivalently, if $n\nmid10L(Y_Q)$, there is a prime $p>Q$ such that
$$p\mid F_n,\qquad p\nmid n,\qquad h_p\text{ is odd}.$$
If $F_n$ is powerful, that same witness has odd $h_p\geq3$ and is WSS.

Proof. Let $H_Q$ consist of all primes at most $Q$. It is rank-closed
and contains $H(S)$ for $S=\{p:5<p\leq Q\}$; in fact this seed is
already $H_Q$. For $p>5$ in $H_Q$, the relevant bound $p-(5/p)$ has
form $2k$ with $1\leq k\leq Y_Q$. Hence $\rho(p)\mid2L(Y_Q)$.
The ranks three, four and five at the small primes divide this integer
too. It follows that $R_{H_Q}\mid2L(Y_Q)$. Apply GSE2 to obtain GSE4.
The remaining assertions are its contrapositive and the definition of
powerfulness. The existence of a powerful $F_n$ with the displayed
nondivisibility is not assumed or proved by this implication.

**Corollary 10.7 (size growth of an actual external odd-depth witness).**
Set $P_U(n)=\max(\{5\}\cup U(n))$. Then
$$\log n\leq\log10+\psi(Y_{P_U(n)}),\qquad
 \liminf_{n\to\infty}\frac{P_U(n)}{\log n}\geq2.\tag{GSE5}$$
Here $\psi(Y)=\log L(Y)$ is the Chebyshev function.

Proof. Apply GSE4 with $Q=P_U(n)$ and take logarithms. The bound implies
$P_U(n)\to\infty$ as $n\to\infty$. The classical prime number theorem
in the form $\psi(Y)\sim Y$ and $Y_Q\sim Q/2$ give the liminf.
No optimality claim is made for the constant two. On any unbounded
sequence of powerful Fibonacci indices, $P_U(n)>5$ eventually and
is the size of an original odd-super-depth WSS factor. This is a
conditional application to that sequence, not a proof that it exists.

### 10.7 Group comparison and the unremoved WSS obligation

The group $\mathcal G_H$ keeps parity of original and transported
valuations, while the rank thresholds keep their actual index support.
Lemma 10.2 supplies new support in the layers; Theorem 10.3 forces a
forbidden repeated square class if an exponent remains too large.
The outcome is an explicit divisor bound, rather than just the finite
cardinality $|\mathcal G_H|$.

A different group occurs in a first lift at an odd prime. For a fixed
return matrix $g=I+pA$ modulo $p^2$,
$$g^k=I+kpA\pmod{p^2}.$$
If $A$ is nonzero modulo $p$, then $g^k=I$ exactly when $p\mid k$.
Thus a zero sum among copies of this one defect merely multiplies the
index by $p$. It does not make the original defect vanish. This is the
already-known local lifting mechanism; a cyclic zero-sum theorem alone
cannot provide the missing original WSS witness.

Theorem 10.3, its cutoff and its original-depth escape corollaries are
ordinary deductions using the classical inputs stated in 10.1. They do
not decide the whole WSS zero set or exclude every $P^2Q^3$ golden block.
The square-class theorem is a separate formalization prerequisite.
The prime-power layer statement for primes at least seven and OSE's
support descent retain their earlier repository attribution.

## 追加锚（本行以下为增补区）
