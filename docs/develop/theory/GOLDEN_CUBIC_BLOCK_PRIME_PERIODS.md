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

For the ramified supplementary value, put $b=x_j-1$,
$\delta=-\eta_j=2-b\omega$, and $c=2-b=3-x_j$. The associated ideals
of $\delta$ and $\eta_j$ agree. The congruence $x_j\equiv4\pmod{72}$
makes $b$ odd, $3\mid b$, and $c\equiv-1\pmod9$. In the primary
convention $a+b\omega$ with $a=3m-1$ and $3\mid b$, the denominator
$\delta$ has $m=1$. Lemvig's ramified supplementary law, Theorem
3.9(2) in *Cubic and quartic reciprocity*, then gives
$(1-\omega/\delta)_3=\omega^2$. Equivalently, its primitive-case
calculation uses $\delta=2(1-\omega)+c\omega$: the character at the
denominator $2$ evaluates $\delta$ as $\omega$, while the character
at $c$ evaluates $\delta$ as $1$. At $j=1$ one has $c=-1$, so the
latter value follows directly because $-1$ is a cube; no reciprocity
law is applied to a unit denominator. For $j\geq2$, the primary
elements $\delta$, $2$, and $c$ are pairwise coprime where required,
their norms avoid $3$ and are unequal, and cubic reciprocity applies.
The congruence $\delta\equiv2(1-\omega)\pmod c$ and the rational
supplementary laws $ (2/c)_3=(1-\omega/c)_3=1$ give the latter value.
Since $N(\delta)=B_j\equiv1\pmod9$, the other supplementary law gives
$(\omega/\delta)_3=1$. As $\lambda=\omega(1-\omega)$, this proves
$(\lambda/\eta_j)_3=\omega^2$ and $(\omega/\eta_j)_3=1$.
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

## 11. The pure-cubic order of an actual Lucas block

Retain $j\geq1$, $x_j=L_{3^j}$, $B_j=x_j^2+3$, and the original
depth $h_p=v_p(F_{\rho(p)})$ for $p\mid B_j$. Section 8.3 supplies the
noncube input for $B_j$; its formal verification remains a prerequisite.
Write uniquely

$$
B_j=d_jc_j^3,\qquad
d_j=\prod_{p\mid B_j}p^{h_p\bmod3},\qquad
R_j=\operatorname{rad}(d_j)
   =\prod_{p\mid B_j,\,3\nmid h_p}p,
$$

where $d_j$ is cubefree and $c_j$ is positive. In particular $R_j>1$.
Let $\theta_j$ be the positive real cube root of $B_j$ and set
$k_j=\mathbb Q(\theta_j)$. The polynomial $T^3-B_j$ is irreducible
over $\mathbb Q$. Since $B_j\equiv1\pmod9$, the integer
$a_j=(B_j-1)/9$ is defined; put
$\beta_j=(1+\theta_j+\theta_j^2)/3$.

**Theorem 11.1 (order and original-depth index).** The rank-three
lattice

$$
\mathcal A_j=\mathbb Z\cdot1+\mathbb Z\cdot\theta_j
                    +\mathbb Z\cdot\beta_j
$$

is an order in $k_j$. Its multiplication table is

$$
\begin{aligned}
\theta_j^2&=3\beta_j-\theta_j-1,\\
\theta_j\beta_j&=\beta_j+3a_j,\\
\beta_j^2&=\beta_j+a_j\theta_j+2a_j.
\end{aligned}
$$

The order discriminant, field discriminant and normalization index are

$$
\boxed{\operatorname{disc}(\mathcal A_j)=-3B_j^2,\qquad
\Delta(k_j)=-3R_j^2,\qquad
I_j=[\mathcal O_{k_j}:\mathcal A_j]=B_j/R_j.}
$$

For each prime $p\mid B_j$, one has $p\mid I_j$ exactly when
$h_p\geq2$, equivalently when $p$ is a Wall--Sun--Sun prime. Thus

$$
\boxed{\operatorname{rad}(I_j)
 =\prod_{p\mid B_j,\,h_p\geq2}p.}
$$

In particular, this specified order is maximal exactly when every
prime factor of $B_j$ has original depth one.

Proof. Reduction by $\theta_j^3=B_j=1+9a_j$ gives the multiplication
table and closure of the lattice under multiplication. The trace Gram
matrix on $(1,\theta_j,\beta_j)$ is

$$
\begin{pmatrix}
3&0&1\\0&0&B_j\\1&B_j&(2B_j+1)/3
\end{pmatrix},
$$

whose determinant is $-3B_j^2$. The fields generated by the cube roots
of $B_j$ and $d_j$ coincide. At $p\ne3$, a prime with
$h_p\bmod3\ne0$ is tamely and totally ramified with discriminant
exponent two; all other primes away from three are unramified. At three,
$B_j=1+9a_j$ is a cube in $\mathbb Q_3$: the substitution
$(1+3z)^3=1+9(z+3z^2+3z^3)$ gives a Hensel equation with derivative
one modulo three. The cubic field therefore has discriminant exponent
one at three. Its one real and one complex pair give the negative sign,
so $\Delta(k_j)=-3R_j^2$. The order-index discriminant relation yields
$I_j=B_j/R_j$. For $p\mid B_j$, its index exponent is $h_p-1$ when
$3\nmid h_p$, and $h_p$ when $3\mid h_p$; it vanishes exactly at
$h_p=1$.

The order-index relation and tame different formula used here are the
classical results recorded in Sutherland, MIT 18.785 Lecture 12,
Theorem 12.27 and Proposition 12.28. The pure-cubic specialization and
its original-depth interpretation are the calculation above; no general
pure-cubic discriminant formula is imported as an extra premise.

## 追加锚（本行以下为增补区）

## 12. Two actual non-torsion cubic twists

Retain the integers of Section 11 and set $f_j=F_{3^j}$.

**Theorem 12.1 (two twists on every actual layer).** For every $j\geq1$,
without a Wall--Sun--Sun assumption, the nonsingular curves

$$
E_j^-:Y^2=X^3-3d_j^2,\qquad E_j^+:Y^2=X^3+125d_j^2
$$

have integral rational points

$$
S_j^-=(d_jc_j,d_jx_j),\qquad
S_j^+=(5d_jc_j,25d_jf_j).
$$

Both points have infinite order. For distinct $i,j$, the curves $E_i^-$
and $E_j^-$ represent distinct rational cubic-twist classes, as do
$E_i^+$ and $E_j^+$. Without factoring $B_j$, the curves obtained by
replacing $d_j$ by $B_j$ and $c_j$ by $1$ have the integral rational
points $(B_j,B_jx_j)$ and $(5B_j,25B_jf_j)$, respectively; these points
also have infinite order.

Proof. The identities $x_j^2=B_j-3$, $5f_j^2=B_j+1$ and
$B_j=d_jc_j^3$ verify all four point equations. The curve constants
are nonzero. Since $B_j$ is odd, so are $d_j$ and $c_j$; Section 4 gives
$v_2(x_j)=2$ and $v_2(f_j)=1$. Each displayed abscissa is odd. On
$Y^2=X^3+b$, the tangent formula gives

$$
X(2S)=\frac{9X(S)^4}{4Y(S)^2}-2X(S).
$$

Its first term has 2-adic valuation $-6$ for either minus point and
$-4$ for either plus point, while its second term has valuation $1$.
Thus each double is finite with nonintegral abscissa. The classical
Nagell--Lutz integrality theorem for rational torsion on an integral
Weierstrass model implies that none of these points is torsion. The
prime supports of $B_i$ and $B_j$ are disjoint by Section 2 and the
supports of $d_i$ and $d_j$ are nonempty by Corollary 8.3. Hence
$d_i/d_j$ is not a rational cube; within either sign, the ratio of
curve constants $(d_i/d_j)^2$ is not a rational sixth power. This
proves the twist assertion.

The Nagell--Lutz input is Sutherland, MIT 18.782 Lecture 24,
Theorem 24.21. These are rational-rank witnesses on the displayed
twists. They do not decide a new Wall--Sun--Sun prime or assert the
degree-three isogeny nonimage condition of the separate GIR2a claim.

## 追加锚（本行以下为增补区）

## 13. The actual points are outside the cubic-isogeny images

Retain $j\geq1$ and the notation $d_j,c_j,x_j,f_j,S_j^-,S_j^+$
of Sections 11 and 12. For $b\ne0$, let
$\varphi_b:E_{-27b}\to E_b$ be the degree-three isogeny from
$t^2=s^3-27b$ to $Y^2=X^3+b$.

**Theorem 13.1 (nonimage on every actual layer).** For every
$j\geq1$, without a Wall--Sun--Sun assumption,
$S_j^-$ is not in the rational image of $\varphi_{-3d_j^2}$,
and $S_j^+$ is not in the rational image of
$\varphi_{125d_j^2}$.

Proof. For an affine source point with $s\ne0$, the isogeny is
given by

$$
\varphi_b(s,t)=\left(
 \frac{s^3-108b}{9s^2},
 \frac{t(s^3+216b)}{27s^3}
\right).
$$

Since $t^2=s^3-27b$, direct expansion gives, in
$\mathbb Q(\sqrt b)$,

$$
Y+\sqrt b=
 \left(\frac{t+9\sqrt b}{3s}\right)^3.
$$

The point at infinity, and any source point with $s=0$, map to
infinity. Thus an affine point in the rational image must make
$Y+\sqrt b$ a cube in $\mathbb Q(\sqrt b)$.

By Corollary 8.3 choose $p\mid B_j$ for which
$e_p=h_p\bmod3$ belongs to $\{1,2\}$. Section 3.2 gives
$v_p(B_j)=h_p$ and $p>5$; Section 11 gives $v_p(d_j)=e_p$.

For $S_j^-$, take $\sqrt b=d_j\sqrt{-3}$. Then

$$
Y+\sqrt b=d_j(x_j+\sqrt{-3}).
$$

Section 8.1 shows that $p$ splits in $\mathbb Q(\sqrt{-3})$
and that $x_j+\sqrt{-3}$ has valuations $h_p$ and $0$ at
the two primes above $p$. Consequently $Y+\sqrt b$ has
valuations $h_p+e_p$ and $e_p$, congruent to $2e_p$ and
$e_p$ modulo three. Neither is divisible by three, so this
element is not a cube.

For $S_j^+$, take $\sqrt b=5d_j\sqrt5$. Then

$$
\begin{aligned}
Y+\sqrt b
 &=25d_jf_j+5d_j\sqrt5\\
 &=5\sqrt5\,d_j(\sqrt5f_j+1).
\end{aligned}
$$

The factors $\sqrt5f_j+1$ and $\sqrt5f_j-1$ have product
$B_j$ and difference $2$. Section 3.2 gives
$(5/p)=1$, so $p$ splits in $\mathbb Q(\sqrt5)$.
These two factors are coprime at the primes above $p$;
conjugation exchanges them up to sign. Hence
$\sqrt5f_j+1$ has valuations $h_p$ and $0$ at those
two primes. Since $p>5$, $5\sqrt5$ is a unit there.
The valuations of $Y+\sqrt b$ are again $h_p+e_p$
and $e_p$, neither divisible by three. This element
is not a cube either. The cubic identity rules out a
rational preimage in both cases.

The result concerns these two specified points and their
isogeny images. It does not compute a Selmer group or
isolate a Wall--Sun--Sun depth pattern.

## 追加锚（本行以下为增补区）

## Erratum to Section 2

In the Cassini factorization in Theorem 2.1, read "the factors
$F_{t-1}+1$ and $F_t-F_{t-1}$" in place of "the latter two factors".
The right-hand factor $F_t$ is divisible by $p$ and is not one of the
units used in that argument.

## 追加锚（本行以下为增补区）

## 14. Exact lifting in the golden residue ring

For a positive integer $q$, let $R_q=(\mathbb Z/q\mathbb Z)[\phi]$ with
$\phi^2=\phi+1$. The order below is multiplicative order in $R_q$.

**Theorem 14.1 (two-coordinate prime-power order).** Let $p$ be prime,
$m\geq1$, $n\geq0$, and $m+2\leq pm$. If $a,b\in\mathbb Z$ are not both
divisible by $p$, then

$$
\operatorname{ord}_{R_{p^{m+n}}}
  \bigl(1+p^m(a+b\phi)\bigr)=p^n.
$$

The prime-power binomial expansion supplies the return after $p^n$
powers. If an earlier $p$-power returned, cancellation modulo the next
power of $p$ in each golden coordinate would force both $p\mid a$ and
$p\mid b$. This contradicts the hypothesis and gives the exact order.
## 15. Exact period iteration of cubic block products

Retain $B_j=L_{3^j}^2+3$ and $C_j=L_{3^j}^2+1$ for $j\geq1$, and let
$\pi(m)$ be the order of $Q$ modulo a positive integer $m$. Write
$\pi^{\circ0}(m)=m$ and $\pi^{\circ(n+1)}(m)=\pi(\pi^{\circ n}(m))$.

**Theorem 15.1 (first arrival at the Fibonacci period fixed point).**
Let $I,J$ be finite sets of positive integer indices with nonempty union.
Put $K=\max(I\cup J)$ and

$$
M=\prod_{j\in I}C_j\prod_{j\in J}B_j,\qquad
\varepsilon=\begin{cases}4,&I\ne\varnothing,\\2,&I=\varnothing.\end{cases}
$$

Then the complete forward trajectory after its first two steps is

$$
\pi(M)=\varepsilon3^{K+1},\qquad
\pi^{\circ(2+t)}(M)=8\cdot3^{\max(1,K-t)}\quad(t\geq0).
$$

In particular, $\pi^{\circ(K+1)}(M)=24$, while
$\pi^{\circ n}(M)\ne24$ for every $0\leq n<K+1$.

Proof. The exact block ranks and original depths give disjoint prime
supports. At each prime factor of a selected block the prime-level matrix
period is $4\cdot3^{j+1}$ for $C_j$ or $2\cdot3^{j+1}$ for $B_j$. Its
exponent in $M$ equals its original depth, so the prime-power lift adds
no factor. The Chinese remainder theorem and the largest selected index
therefore give $\pi(M)=\varepsilon3^{K+1}$.

The direct small-modulus returns are $\pi(2)=3$, $\pi(4)=6$, and
$\pi(8)=12$. The identity $Q^8=I+3A$, with
$A=\left(\begin{smallmatrix}11&7\\7&4\end{smallmatrix}\right)$ nonzero
modulo three, has exact first depth one. The two-coordinate prime-power
lift of Theorem 14.1, together with the order eight modulo three, gives
$\pi(3^b)=8\cdot3^{b-1}$ for every $b\geq1$. CRT now yields

$$
\pi(\varepsilon3^{K+1})=8\cdot3^K,\qquad
\pi(8\cdot3^u)=8\cdot3^{\max(1,u-1)}\quad(u\geq1).
$$

Induction on $t$ gives the displayed trajectory. The exponent reaches
one for the first time when $t=K-1$, which is iteration $K+1$.
Earlier terms from the second iterate have exponent at least two; the
first iterate has the wrong power of two, and $M$ is odd. Thus none of
the preceding terms is 24. The value 24 is fixed by the same recurrence.

## 追加锚（本行以下为增补区）

## 16. Ideal factorization of odd Eisenstein factors

**Theorem 16.1 (explicit oriented ideal product).** Let
$E=\mathbb Z[\omega]$, where $\omega^2+\omega+1=0$. For an odd natural
number $b$, put $\eta_b=-2+b\omega$ and $B_b=b^2+2b+4$. For each
rational prime $p$ dividing $B_b$, put $P_{b,p}=(\eta_b,p)$. Then

$$
(\eta_b)=\prod_{p\mid B_b}P_{b,p}^{v_p(B_b)}.
$$

Proof. The scalar quotient $E/(\eta_b)\cong\mathbb Z/B_b\mathbb Z$
identifies $E/P_{b,p}$ with $\mathbb Z/p\mathbb Z$, so the absolute
ideal norm of $P_{b,p}$ is $p$. The product on the right is contained
in $(\eta_b)$: modulo $(\eta_b)$, it is generated by
$\prod_{p\mid B_b}p^{v_p(B_b)}=B_b=0$. Multiplicativity of ideal norm
shows that this product and $(\eta_b)$ both have norm $B_b$.
Containment and equality of norms give equality of the two ideals.

The primary generators and the replacement of $v_p(B_b)$ by the
original depth $h_p$ in Theorem 8.1 are separate assertions.

## 追加锚（本行以下为增补区）

## 17. The integral third-cyclotomic model

**Theorem 17.1 (Eisenstein cyclotomic equivalence).** Let
$E=\mathbb Z[\omega]$ be the quadratic algebra with
$\omega^2+\omega+1=0$, and let $\mathcal O_3$ be the ring of integers of
$\mathbb Q(\zeta_3)$, where $\zeta_3$ is a primitive third root of unity.
There exists an equivalence of $\mathbb Z$-algebras

$$
E\simeq_{\mathbb Z\text{-alg}}\mathcal O_3.
$$

Proof. The basis $(1,\omega)$ makes $E$ a power-basis algebra of degree
two. A primitive third root gives an integral power basis of
$\mathcal O_3$, also of degree two. Both generators satisfy the third
cyclotomic polynomial $X^2+X+1$. Since their power bases have degree
two, this polynomial is the minimal polynomial of each generator.
The two power bases therefore give the claimed $\mathbb Z$-algebra
equivalence.

## 追加锚（本行以下为增补区）

## 18. Binary valuation descent on integral Mordell curves

For $b\in\mathbb Z$, write $E_b$ for the rational affine model
$Y^2=X^3+b$. A point in this section is a nonsingular rational affine
point, including when the full model has a singularity elsewhere.

**Theorem 18.1 (negative binary abscissa valuation).** If $P=(x,y)$ is a
nonsingular rational affine point on $E_b$ and $v_2(x)<0$, then $P$ has
infinite additive order.

Proof. Since $b$ is integral, both $x^3+b$ and $x^3-8b$ have valuation
$3v_2(x)$, which is negative. Thus $y\ne0$, and the tangent formula gives

$$
X(2P)=\frac{x(x^3-8b)}{4(x^3+b)},\qquad
v_2(X(2P))=v_2(x)-2.
$$

The same calculation applies to every successive double. Their
abscissa valuations are $v_2(x)-2n$ for $2^nP$, so these points are
pairwise distinct. A finite-order point cannot have infinitely many
distinct multiples.

**Theorem 18.2 (unit abscissa and positive ordinate valuation).** If
$P=(x,y)$ is a nonsingular rational affine point on $E_b$ with $x\ne0$,
$v_2(x)=0$, and $v_2(y)>0$, then $P$ has infinite additive order.

Proof. The tangent formula gives

$$
X(2P)=\left(\frac{3x^2}{2y}\right)^2-2x.
$$

The first term has valuation $-2-2v_2(y)<0$, while the second has
valuation $1$. Hence $v_2(X(2P))<0$. Theorem 18.1 applies to $2P$;
finite order of $P$ would imply finite order of $2P$, a contradiction.

## 追加锚（本行以下为增补区）

## 19. Explicit affine cubic-map obstruction

Retain $B_j=L_{3^j}^2+3=d_jc_j^3$ and the two points $S_j^-$ and
$S_j^+$ from Sections 11 and 12. For rational $b,X,Y$, let
$\mathcal A_b(X,Y)$ mean that rational numbers $s,t$ exist with

$$
s\ne0,\qquad t^2=s^3-27b,\qquad
X=\frac{s^3-108b}{9s^2},\qquad
Y=\frac{t(s^3+216b)}{27s^3}.
$$

**Theorem 19.1 (actual points have no affine cubic-map preimage).**
For every $j\geq1$,

$$
\neg\mathcal A_{-3d_j^2}(d_jc_j,d_jL_{3^j})
\quad\text{and}\quad
\neg\mathcal A_{125d_j^2}(5d_jc_j,25d_jF_{3^j}).
$$

Proof. Since $B_j$ is not a cube, some prime $p$ divides $d_j$ to an
exponent $e\in\{1,2\}$. The block congruences give $p>5$. Write
$k=v_p(c_j)\geq0$. For either displayed point, $v_p(X)=e+k$ and
$v_p(b)=2e$, while $v_p(9)=v_p(108)=0$. A putative affine preimage
would satisfy

$$
s^3=9Xs^2+108b.
$$

Put $r=v_p(s)\in\mathbb Z$. The three terms have valuations
$3r$, $e+k+2r$, and $2e$. If $r\leq0$, or if $e=2$ and $r=1$,
the first valuation is strictly smaller than the other two. In every
remaining case the last valuation is strictly smaller than the other
two. A sum cannot have exactly one term of least $p$-adic valuation,
so no such $s$ exists.

The statement uses the displayed rational affine relation. Identifying
that relation with the rational image of a global degree-three isogeny
requires the separate map construction and image theorem of Section 13.

## 追加锚（本行以下为增补区）

## 20. Exact period at an odd Fibonacci modulus

**Theorem 20.1 (Fibonacci modulus period).** For every odd integer
$n\geq5$, the order of the Fibonacci matrix $Q$ modulo $F_n$ is

$$
\pi(F_n)=4n.
$$

Proof. The Fibonacci-coordinate formula makes $\phi^n$ the scalar
$F_{n-1}$ modulo $F_n$. Cassini's identity gives
$F_{n-1}^2=-1\pmod{F_n}$ for odd $n$. Since $F_n\geq5$, this scalar has
order four, so the order of $\phi$ divides $4n$. Conversely, every
return $\phi^t=1$ modulo $F_n$ implies $F_n\mid F_t$. The Fibonacci gcd
identity and strict growth from index two imply $n\mid t$. The
order-of-a-power identity then forces the order of $\phi$ to be $4n$.
The faithful golden multiplication matrix identifies that order with
the order of $Q$.
## 追加锚（本行以下为增补区）

## 21. Primary associates in the Eisenstein order

Let $E=\mathbb Z[\omega]$, where $\omega^2+\omega+1=0$, and write
$N(a+b\omega)=a^2-ab+b^2$. An element is *primary* when it is congruent
to $1$ modulo $3E$.

**Theorem 21.1 (primary associate normalization).** If $z\in E$ has
$N(z)\equiv1\pmod3$, then there is a unit $u\in E$ with $N(u)=1$ and

$$
uz\equiv1\pmod{3E}.
$$

Proof. Modulo $3$, the norm form is $(a+b)^2$. Its value is $1$ exactly
on the six residue pairs $(1,0)$, $(2,0)$, $(0,1)$, $(0,2)$, $(1,1)$,
and $(2,2)$. These are precisely the residues of the six units
$\pm1$, $\pm\omega$, and $\pm(1+\omega)$; each has norm $1$. Choose
the inverse of the unit with the same residue as $z$. Its product with
$z$ is $1$ modulo $3E$ and its norm is $1$.

## 追加锚（本行以下为增补区）

## 22. Nonsquare quotients on dyadic Fibonacci layers from k = 1

**Theorem 22.1 (dyadic quotient obstruction).** For every natural number
$k\geq1$, the exact integer quotient

$$
Q_k=\frac{F_{2^{k+1}}}{F_{2^k}}
$$

satisfies $Q_1\equiv3\pmod5$ and $Q_k\equiv2\pmod5$ for $k\geq2$.
Consequently no $Q_k$ is a square. This supplies the dyadic nonsquare
case of Lemma 10.2.

Proof. Fibonacci--Lucas doubling identifies $Q_k=L_{2^k}$.
The initial values are $L_2=3$ and $L_4=7$. For $k\geq2$, the index
$2^k$ is even, so Lucas doubling gives
$L_{2^{k+1}}=L_{2^k}^2-2$. The residue $2$ is fixed by
$u\mapsto u^2-2$ modulo five. Induction therefore gives the stated
residue at every later layer. The square residues modulo five are
$0$, $1$, and $4$, excluding both $2$ and $3$.

## 追加锚（本行以下为增补区）

## 23. The five-adic Fibonacci valuation from the golden coordinate

**Theorem 23.1 (exact five-adic depth).** For every positive integer
$n$, the original Fibonacci number satisfies

$$v_5(F_n)=v_5(n).$$

Proof. Write $\phi^n=a+b\phi$ in the integral basis
$1,\phi$, so $b=F_n$ and
$a^2+ab-b^2=N(\phi^n)=(-1)^n$. Direct multiplication in
$\mathbb Z[\phi]$ gives

$$
F_{5n}=5F_n Q(a,b),\qquad
Q(a,b)=a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

Modulo five, $Q(a,b)=(a+3b)^4$. If $a+3b$ vanished modulo five,
substituting $a=-3b$ into the norm would give
$a^2+ab-b^2=5b^2=0$ modulo five, contradicting
$N(\phi^n)=(-1)^n$. Thus $5\nmid Q(a,b)$, and the displayed
factorization gives $v_5(F_{5n})=v_5(F_n)+1$ for $n>0$.

The least positive Fibonacci zero modulo five is at index five:
$F_5=5$, whereas $F_1,F_2,F_3,F_4$ are nonzero modulo five.
The Fibonacci entry-point theorem therefore gives
$5\mid F_n$ exactly when $5\mid n$. For $5\nmid n$, both
valuations in the conclusion are zero. If $5\mid n$, write
$n=5m$ with $0<m<n$ and apply the preceding one-step equality
and strong induction to $m$.

This proves the five-adic input used in Section 10. It does not
establish the square-class rigidity invoked there.

## 追加锚（本行以下为增补区）

## 24. A dyadic budget from odd Fibonacci support

For a prime $p$, let $\rho(p)$ be its first positive Fibonacci zero
index. For a finite set $H$ of primes, put

$$
R_H=\operatorname{lcm}_{p\in H}\rho(p).
$$

**Theorem 24.1 (dyadic rank budget).** Suppose $3\in H$ and $n\geq1$.
If every prime factor of $n$ belongs to $H$, and every prime factor
$p$ of $F_n$ for which $v_p(F_n)$ is odd belongs to $H$, then

$$
v_2(n)\leq v_2(R_H).
$$

Proof. Since $\rho(3)=4$ and $3\in H$, one has $4\mid R_H$.
Suppose $e=v_2(n)>v_2(R_H)$, so $e\geq3$ and $2^e\mid n$.
The exact quotient

$$
C_e=\frac{F_{2^e}}{F_{2^{e-1}}}
$$

is not a square by Theorem 22.1. Choose a prime $p\mid C_e$ for which
$v_p(C_e)$ is odd. Both Fibonacci values in this quotient are odd,
so $p\ne2$. The entry rank $\rho(p)$ divides $2^e$. If it divided
$2^{e-1}$, then $p$ would divide both Fibonacci values. The
prime-to-index valuation identity, applied to their indices, would
give equal $p$-valuations, contradicting $v_p(C_e)>0$. Hence
$\rho(p)=2^e$ and $p\nmid F_{2^{e-1}}$, so
$v_p(F_{2^e})=v_p(C_e)$ is odd.

If $p\in H$, its rank would divide $R_H$, contrary to
$e>v_2(R_H)$. Thus $p\notin H$. Since $p\mid F_{2^e}$ and
$2^e\mid n$, Fibonacci divisibility gives $p\mid F_n$.
The prime-support hypothesis for $n$ implies $p\nmid n$.
The prime-to-index valuation identity now gives

$$
v_p(F_n)=v_p(F_{\rho(p)})=v_p(F_{2^e}),
$$

which is odd. The odd-support hypothesis therefore puts $p$ in $H$,
a contradiction.

## 追加锚（本行以下为增补区）

## 25. A ternary budget from odd Fibonacci support

Retain the Fibonacci entry ranks $\rho(p)$ and, for a finite set $H$ of
primes, $R_H=\operatorname{lcm}_{p\in H}\rho(p)$.

**Theorem 25.1 (ternary rank budget).** Suppose $2\in H$ and $n\geq1$.
If every prime factor of $n$ belongs to $H$, and every prime factor
$p$ of $F_n$ for which $v_p(F_n)$ is odd belongs to $H$, then

$$
v_3(n)\leq v_3(R_H).
$$

Proof. The first Fibonacci zero modulo two is at index three, so
$3=\rho(2)\mid R_H$. If $e=v_3(n)>v_3(R_H)$, then $e\geq2$; put
$j=e-1\geq1$. The frozen cubic Fibonacci identity gives the exact
positive quotient

$$
C_j=\frac{F_{3^{j+1}}}{F_{3^j}}=L_{3^j}^2+1.
$$

The frozen Lucas congruence $L_{3^j}^2\equiv1\pmod5$ implies
$C_j\equiv2\pmod5$, so $C_j$ is not a square. Choose a prime
$p\mid C_j$ with odd $v_p(C_j)$. The cubic-block rank and original-depth
theorem gives $\rho(p)=3^{j+1}=3^e$ and
$v_p(C_j)=v_p(F_{\rho(p)})$. If $p\in H$, its rank divides $R_H$,
contradicting $e>v_3(R_H)$. Thus $p\notin H$.

Since $3^e\mid n$, the entry-point theorem gives $p\mid F_n$.
The index-support hypothesis gives $p\nmid n$, and the prime-to-index
valuation theorem yields
$v_p(F_n)=v_p(F_{\rho(p)})=v_p(C_j)$, which is odd. The odd-support
hypothesis puts $p$ in $H$, a contradiction. This settles the
three-exponent branch under the stated support conditions; it does not
assert the unrestricted GSE1 divisor bound or the five-exponent branch.

## 追加锚（本行以下为增补区）

## 26. Degree of the actual Lucas-block Kummer tower

Let $K=\mathbb Q(\omega)$, where $\omega^2+\omega+1=0$. For $j\geq1$,
retain the actual block $B_j=L_{3^j}^2+3$ and let
$\beta_j=\sqrt[3]{B_j}$ be its positive real cube root. Put
$K_0=K$ and $K_m=K(\beta_1,\ldots,\beta_m)$ for $m\geq1$.

**Theorem 26.1 (Lucas-block Kummer tower degree).** For every
$J\geq1$,

$$
[K_J:K]=3^J.
$$

Proof. First the classes $[B_j]$ are independent in
$K^\times/(K^\times)^3$. Indeed, suppose for some finite set of indices
and exponents $e_j\in\{0,1,2\}$ that
$\prod_j B_j^{e_j}=u^3$ with $u\in K^\times$.
Taking the norm to $\mathbb Q$ gives
$\prod_j B_j^{2e_j}=N_{K/\mathbb Q}(u)^3$.
For each $j$, the noncube property of $B_j$ and unique factorization
of integers supply a prime $p_j\mid B_j$ whose exponent
$v_{p_j}(B_j)$ is not divisible by three. The prime-support
disjointness of Theorem 2.1 makes $p_j$ divide no other block in
the product. Its valuation in the norm equation gives
$3\mid2e_jv_{p_j}(B_j)$, hence $e_j=0$.

We use the following descent in each cubic stage. Suppose
$K_i=K_{i-1}(\beta_i)$ has degree three. It is a cyclic Galois
extension: $K_{i-1}$ contains $\omega$, and the conjugates of
$\beta_i$ are $\beta_i,\omega\beta_i,\omega^2\beta_i$.
Choose its generator $\sigma$ with
$\sigma(\beta_i)=\omega\beta_i$. If $a\in K_{i-1}^\times$ is a cube
in $K_i$, write $z^3=a$ with $z\in K_i^\times$. Then
$(\sigma z/z)^3=1$, so $\sigma z/z=\omega^k$ for some
$k\in\{0,1,2\}$. The quotient $c=z/\beta_i^k$ is fixed by
$\sigma$, hence belongs to $K_{i-1}$, and

$$
a=c^3B_i^k.
$$

Induct on $m$. At $m=1$, independence says that $B_1$ is not a cube
in $K_0$. For the inductive step, if $B_m$ were a cube in $K_{m-1}$,
apply the descent successively through
$K_{m-1}/K_{m-2},\ldots,K_1/K_0$.
At the bottom it would give
$B_m\prod_{i=1}^{m-1}B_i^{e_i}\in(K^\times)^3$ for suitable
$e_i\in\{0,1,2\}$, contrary to independence. Thus $B_m$ is not a
cube in $K_{m-1}$. The cubic polynomial $X^3-B_m$ is irreducible
over that field, so $[K_m:K_{m-1}]=3$; multiplication of degrees
proves the formula.

The general Kummer correspondence behind this degree calculation is
given in J. S. Milne, *Fields and Galois Theory*, v5.10 (2022),
Theorem 5.30 and Remark 5.32, pp. 75-76. The conclusion concerns the
degree over $\mathbb Q(\omega)$; it makes no discriminant or
ramification assertion.

## 追加锚（本行以下为增补区）

## 27. Root-choice invariant Lucas-block tower

Let $K=\mathbb Q(\omega)$ as in Section 26, fix an algebraic closure
$\overline K$, and put $B_j=L_{3^j}^2+3$ for $j\geq1$. For every family
$(\gamma_j)_{j\geq1}$ in $\overline K$ with $\gamma_j^3=B_j$, define
$T_0=K$ and $T_{m+1}=T_m(\gamma_{m+1})$.

**Theorem 27.1 (degree for every root choice).** For every such family
and every $J\geq0$,

$$
[T_J:K]=3^J.
$$

Proof. We prove the stronger induction claim that a noncube natural
number $a$ coprime to $B_1,\ldots,B_m$ remains a noncube in $T_m$.
For $m=0$, a cube root of $a$ in $K$ would make $X^3-a$ reducible over
$\mathbb Q$, since the quadratic extension $K/\mathbb Q$ cannot contain
a root of an irreducible cubic. A rational cube root of an integer is
an integer, contradicting the hypothesis on $a$.

Suppose the claim holds at $m$. Apply it first to $a=B_{m+1}$:
the noncube theorem and pairwise coprimality of the actual Lucas
blocks give its hypotheses. Thus $X^3-B_{m+1}$ is irreducible over
$T_m$, and $T_{m+1}/T_m$ has degree three. Because $\omega\in T_m$,
this extension is cyclic. The cubic descent of Section 26 shows that
if another eligible $a$ became a cube in $T_{m+1}$, then
$aB_{m+1}^e$ would be a cube in $T_m$ for some $0\leq e\leq3$.
Coprimality of $a$ and $B_{m+1}$ implies that this product is still
not an integer cube: a prime exponent of $a$ not divisible by three
is unchanged in the product. Pairwise coprimality of the blocks makes
the product coprime to every earlier $B_i$, contradicting the induction
claim.

The empty tower has degree one; multiplying the stage degrees proves
the formula. The conclusion is independent of the selected cubic
roots and does not assert a discriminant or ramification law.

## 追加锚（本行以下为增补区）

## 28. Odd-index Fibonacci twenty-five layers

**Theorem 28.1 (normalized odd-index layer modulo seven).** For every
positive odd integer $n$, there is a natural number $d_n$ such that

$$
F_{25n}=25F_nd_n,\qquad d_n\equiv5\pmod 7.
$$

In particular, $d_n$ is not a square.

Proof. The addition identity for Fibonacci numbers, together with
$F_7=13$ and $F_8=21$, gives $F_{r+8}\equiv-F_r\pmod7$ for every
$r\geq0$. Since $25n=n+8(3n)$ and $n$ is odd,
$F_{25n}\equiv-F_n\pmod7$. The first positive index at which seven
divides a Fibonacci number is eight, and the strong divisibility
identity gives $7\mid F_r$ if and only if $8\mid r$. Thus $F_n$ is
nonzero modulo seven.

Strong divisibility also gives $F_n\mid F_{25n}$. The five-adic
identity $v_5(F_r)=v_5(r)$ for positive $r$ shows that the quotient
$F_{25n}/F_n$ has five-adic valuation two, so it equals $25d_n$ for
some natural number $d_n$. Cancelling $F_n$ modulo seven now yields
$25d_n\equiv-1\pmod7$, hence $d_n\equiv5\pmod7$. The quadratic
residues modulo seven are $0,1,2,4$, so $d_n$ is not a square.

## 追加锚（本行以下为增补区）

## 29. Five-adic rank budget from odd Fibonacci support

For a prime $p$, let $\rho(p)$ be its first positive Fibonacci zero.
For a finite set $H$ of primes, put
$R_H=\operatorname{lcm}_{p\in H}\rho(p)$.

**Theorem 29.1 (five-adic rank budget).** Suppose $5\in H$ and $n>0$.
Assume every prime dividing $n$ belongs to $H$, and every prime occurring
to odd multiplicity in $F_n$ belongs to $H$. Then

$$v_5(n)\leq v_5(R_H)+1.$$

Proof. Write $a=v_5(R_H)$ and $e=v_5(n)$, and suppose
$e\geq a+2$. Apply Theorem 28.1 to the positive odd index $5^a$:

$$F_{5^{a+2}}=25F_{5^a}d,\qquad d\text{ is not a square}.$$

The exact five-adic valuation of Fibonacci numbers gives $v_5(d)=0$.
Choose a prime $p$ occurring to odd multiplicity in $d$; thus $p\ne5$.
It divides $F_{5^{a+2}}$. Its first entry rank is a power $5^j$ with
$j\leq a+2$. If $j\leq a$, then $p$ also divides $F_{5^a}$.
Since $p$ divides neither index, the prime-to-index valuation law makes
its valuations in these two Fibonacci numbers equal. Their displayed
product identity would then force $v_p(d)=0$, a contradiction. Hence
$j>a$. If $p\in H$, its rank divides $R_H$, contradicting
$v_5(R_H)=a$; therefore $p\notin H$.

Now $5^{a+2}\mid n$, so $p\mid F_n$. The index-support hypothesis gives
$p\nmid n$. The prime-to-index valuation law transfers the odd value
$v_p(d)=v_p(F_{5^{a+2}})$ to $v_p(F_n)$. This contradicts the assumed
odd-prime support of $F_n$ and proves the bound. No square-class
classification or rank-closure premise is used here.

## 追加锚（本行以下为增补区）

## 30. Modular obstructions in prime-power Fibonacci layers

**Theorem 30.1 (twenty-eight residue classes).** Let $q\geq7$ be a
prime, and suppose

$$
q\pmod {120}\notin\{1,49,71,119\}.
$$

For every $k\geq0$, the positive integer

$$
Q_{q,k}=\frac{F_{q^{k+1}}}{F_{q^k}}
$$

is not a square. The quotient is an integer by Fibonacci divisibility.

Proof. Among the $32$ residue classes coprime to $120$, the stated
condition is equivalent to the union of the following three tests:
$q\bmod12\in\{5,7\}$, $q\bmod8\in\{3,5\}$, or
$q\bmod20\in\{3,7,13,17\}$. The Fibonacci pairs
$(F_{12},F_{13})$, $(F_8,F_9)$, and $(F_{20},F_{21})$ reduce to
$(0,1)$ modulo $8$, $3$, and $5$, respectively. Thus these are
periods for the Fibonacci sequence in the indicated moduli.

In the first test, the indices $q^k$ alternate between $1$ and $q$
modulo $12$. The two Fibonacci residues modulo $8$ are $1$ and $5$,
so $Q_{q,k}\equiv5\pmod8$; the denominator residue is a unit. In the
second test, the indices alternate between $1$ and $q$ modulo $8$.
Their Fibonacci residues modulo $3$ are $1$ and $2$, so
$Q_{q,k}\equiv2\pmod3$. In the third test, powers of $q$ modulo $20$
run through $1,q,9,9q$ (with possible repetitions). The Fibonacci
residues modulo $5$ give $Q_{q,k}\equiv2$ or $3\pmod5$, according to
the residue of $q$. The denominator is again a unit. None of $5$
modulo $8$, $2$ modulo $3$, or $2,3$ modulo $5$ is a square residue.

This proves only the specified residue classes. It does not prove
Lemma 10.2 for $q\equiv1,49,71,119\pmod{120}$ or the general
Fibonacci square-class rigidity used there.

## 追加锚（本行以下为增补区）

## 31. Cubic characters on prime ideals and factored denominators

Let $E=\mathbb Z[\omega]$, where $\omega^2+\omega+1=0$. For a maximal
ideal $P\subset E$ with finite residue field $E/P$ of cardinality
$q\equiv1\pmod3$, assume $3\notin P$. Put
$\mu_3=\{1,\omega,\omega^2\}\subset E$.

**Theorem 31.1 (local cubic character and composite denominator).** For
every $a\notin P$, there is a unique $\chi_P(a)\in\mu_3$ such that

$$
\chi_P(a)\equiv a^{(q-1)/3}\pmod P.
$$

For $a,b\notin P$, one has
$\chi_P(ab)=\chi_P(a)\chi_P(b)$. Given a finite indexed family
$(P_i)_{i\in S}$ of such ideals and multiplicities $e_i\geq0$, define
the character of the specified factored denominator by

$$
\chi_{(P,e)}(a)=\prod_{i\in S}\chi_{P_i}(a)^{e_i},
\qquad a\notin P_i\text{ for every }i\in S.
$$

It is multiplicative in $a$, and addition of multiplicities gives

$$
\chi_{(P,e+f)}(a)=\chi_{(P,e)}(a)\chi_{(P,f)}(a).
$$

This definition uses the prime-ideal factors and their multiplicities;
it does not use a single Euler exponent in the quotient by a composite
ideal. In particular, the oriented factorization in Theorem 8.1
supplies the denominator factors and multiplicities for $\eta_j$.

Proof. The nonzero class of $a$ in the field $E/P$ satisfies
$a^{q-1}=1$, so $a^{(q-1)/3}$ is a root of $T^3-1$. This polynomial
factors as $(T-1)(T-\omega)(T-\omega^2)$. The three displayed roots
remain distinct modulo $P$: their pairwise differences have norm
three, and $3\notin P$. This proves existence and uniqueness of
$\chi_P(a)$. The Euler condition for $ab$ is the product of the
conditions for $a$ and $b$, so uniqueness proves local
multiplicativity. Multiplying these local equalities over $S$ proves
numerator multiplicativity; the identity
$z^{e_i+f_i}=z^{e_i}z^{f_i}$ proves the denominator law.

## 追加锚（本行以下为增补区）

## 32. A modulus-31 obstruction for two prime-power layers

**Theorem 32.1 (two remaining residue classes).** Let $q\geq7$ be a
prime with $q\equiv49$ or $71\pmod{120}$. For every $k\geq0$, the
integer quotient

$$
C_{q,k+1}=\frac{F_{q^{k+1}}}{F_{q^k}}
$$

is positive and satisfies

$$
C_{q,k+1}\equiv
\begin{cases}
27\pmod{31},&k\text{ even},\\
23\pmod{31},&k\text{ odd}.
\end{cases}
$$

In particular, $C_{q,k+1}$ is not a square. This covers the $49$ and
$71$ classes left open by Theorem 30.1; it does not address the $1$
and $119$ classes or the complete prime-power statement of Lemma 10.2.

Proof. The Fibonacci pair $(F_n,F_{n+1})$ has period $30$ modulo $31$:
$F_{30}\equiv0$ and $F_{31}\equiv1\pmod{31}$. In the two stated
classes, $q\equiv19$ or $11\pmod{30}$, respectively, and both residues
square to $1$ modulo $30$. Consequently $q^k\equiv1\pmod{30}$ for
even $k$ and $q^k\equiv19$ or $11\pmod{30}$ for odd $k$. Since
$F_1\equiv1$ and $F_{11}\equiv F_{19}\equiv27\pmod{31}$, the values
$F_{q^k}$ alternate between $1$ and $27$ modulo $31$. Fibonacci
divisibility makes the displayed quotient an integer; positivity
follows from positivity of both Fibonacci values. Its residue is $27$
on even $k$ and $27^{-1}\equiv23\pmod{31}$ on odd $k$.
Neither $27$ nor $23$ is a square modulo $31$.
## 33. Nonsquare Fibonacci quotients beyond the modular classes

For $m\geq0$ let $U_0(X)=0$, $U_1(X)=1$, and
$U_{m+2}(X)=XU_{m+1}(X)+U_m(X)$. Write $L_n$ for the Lucas number.

**Theorem 33.1 (all higher odd prime-power layers).** Let $q=2r+1$ be
odd with $r\geq119$. If $x$ is an integer greater than two and

$$
x^2-4>128\cdot6^r,
$$

then $U_q(x)$ is not a square. Consequently, for every odd $n\geq q$,
the positive integer $F_{qn}/F_n$ is not a square. In particular, if
$q\geq239$ is an odd prime and $k\geq1$, then
$F_{q^{k+1}}/F_{q^k}$ is not a square.

Proof. The roots of the recurrence polynomial occur in opposite pairs:

$$
U_q(X)=\prod_{i=1}^{r}
  \left(X^2+4\cos^2\frac{\pi i}{q}\right).
$$

Put $\lambda_i=4\cos^2(\pi i/q)<4$ and
$A(t)=\prod_{i=1}^{r}(1+\lambda_i t)$. The coefficient of $t$ in
$A$ is $q-2$, as also follows by comparing the next-to-leading
coefficient in the recurrence; it is odd. Let
$S(t)=\sqrt{A(t)}=\sum_{j\geq0}s_jt^j$ be the branch with $S(0)=1$.
Each factor is nonzero on $|t|\leq1/4$, so this branch is analytic
there. On the boundary, $|S(t)|\leq2^{r/2}$, and Cauchy's estimate gives

$$
|s_j|\leq 2^{r/2}4^j. \tag{33.1}
$$

All $s_j$ are dyadic rationals. Indeed, expanding $S=(1+(A-1))^{1/2}$
uses only the coefficients
$\binom{1/2}{m}=(-1)^{m-1}C_{m-1}/2^{2m-1}$, where $C_{m-1}$ is an
integer Catalan number. Set $e_j=j+v_2(j!)=2j-\operatorname{popcount}(j)$.
In the coefficient of $t^j$, the $m=j$ summand is
$\binom{1/2}{j}(q-2)^j$ and has valuation $-e_j$; every $m<j$
summand has strictly larger valuation. Therefore

$$
v_2(s_j)=-e_j,\qquad 2^{e_j}s_j\in\mathbb Z,\qquad s_j\ne0
\quad(j\geq1). \tag{33.2}
$$

Take $J=\lceil r/2\rceil$, $\delta=2J-r\in\{0,1\}$, and
$D=2^{e_J}\leq2^r$. For $x>2$ define

$$
T=x^r\sum_{j=0}^{J}s_jx^{-2j},\qquad
R=x^rS(x^{-2})-T.
$$

Equation (33.2) makes $Dx^\delta T$ an integer: its $j$th summand is
$Ds_jx^{2(J-j)}$. By (33.1) and a geometric tail estimate,

$$
Dx^\delta|R|
\leq\frac{D\,2^{r/2+2J+2}}{x^2-4}<1. \tag{33.3}
$$

The strict inequality follows from $e_J\leq2J-1$,
$2^{r/2}\leq(3/2)^r$, and $x^2-4>128\cdot6^r$.
The first omitted term has absolute value at least
$2^{-e_{J+1}}x^{-2-\delta}$. The remaining terms have absolute sum
at most

$$
\frac{2^{r/2}4^{J+2}x^{-2-\delta}}{x^2-4}.
$$

Their ratio to the first omitted term is at most
$2^{r/2+4J+6-\operatorname{popcount}(J+1)}/(x^2-4)$.
Since this exponent is at most $(5/2)r+7$ and
$2^{(5/2)r+7}\leq128\cdot6^r$, the ratio is less than one. Thus
$R\ne0$. If $U_q(x)$ were the square of an integer $M$, positivity and
the product formula would give $M=x^rS(x^{-2})$ after choosing the
nonnegative root. But $Dx^\delta M$ and $Dx^\delta T$ are integers,
while their difference is nonzero and has absolute value less than one
by (33.3), a contradiction.

For the Fibonacci conclusion, the odd-index Binet identity gives
$F_{qn}/F_n=U_q(L_n)$; equivalently, multiplication by $n$ turns the
characteristic-root product into $-1$ and yields the stated recurrence.
The odd-index Lucas subsequence $A_r=L_{2r+1}$ starts with $A_0=1$,
$A_1=4$ and satisfies $A_{r+2}=3A_{r+1}-A_r$. Induction gives
$A_r\geq(5/2)^r$, and $L_n\geq L_q$ when $n\geq q$. The exact
inequality $4\cdot25^{119}>513\cdot24^{119}$ and monotonicity of
$(25/24)^r$ imply, for all $r\geq119$,

$$
L_n^2-4\geq(25/4)^r-4>128\cdot6^r.
$$

The first assertion now applies to $x=L_n$. Taking $n=q^k$ proves the
last assertion.

## 34. Scope of the higher-layer argument

Theorem 33.1 is a derivation from the recurrence polynomial, an analytic
coefficient bound, and a dyadic valuation calculation. It covers the
remaining $q\equiv1,119\pmod{120}$ classes when $k\geq1$; Theorems
30.1 and 32.1 cover the other classes. The initial layer $k=0$ for
those two residue classes, and hence the full Lemma 10.2, remain open
for independent formal proof. The displayed argument is a mathematical
proof in the theory source; it has not yet been verified by Lean.

## 追加锚（本行以下为增补区）

## 35. An explicit odd-index Lucas growth threshold

**Theorem 35.1 (Lucas threshold for the nonsquare estimate).** Let
$r,n$ be nonnegative integers with $r\geq119$ and $n\geq2r+1$. Then

$$
L_n^2-4>128\cdot6^r.
$$

Proof. Put $A_j=L_{2j+1}$. The Lucas recurrence gives
$A_0=1$, $A_1=4$, and
$A_{j+2}=3A_{j+1}-A_j$. Simultaneous induction gives $A_j>0$ and
$2A_{j+1}\geq5A_j$: if these hold at $j$, then
$2A_{j+2}-5A_{j+1}=A_{j+1}-2A_j\geq A_j/2>0$.
Consequently $2^jA_j\geq5^j$ for every $j$.

Direct integer calculation gives
$4\cdot25^{119}>513\cdot24^{119}$. Multiplying the inequality by
$25/24>1$ extends it to every $j\geq119$. Since $6^j>16$ there,

$$
25^j>128\cdot24^j+4\cdot4^j.
$$

Squaring $2^jA_j\geq5^j$ and using this strict inequality yields
$A_j^2-4>128\cdot6^j$. Finally, $L_n\geq L_{2r+1}=A_r$ because
the positive-index Lucas numbers increase; this follows directly from
$L_{m+1}=F_m+F_{m+2}$ and the monotonicity of Fibonacci numbers.
Thus the displayed bound holds for $n\geq2r+1$.

## 追加锚（本行以下为增补区）

## 36. The first two coefficients of the Fibonacci recurrence polynomial

**Theorem 36.1 (near-leading recurrence coefficients).** Keep the
recurrence polynomial $U_m(X)$ of Section 33. For every integer
$m\geq1$, its leading coefficient, at $X^{m-1}$, is $1$. For every
$m\geq3$, its coefficient at $X^{m-3}$ is $m-2$. In particular, the
coefficient at $X^{q-3}$ for odd $q=2r+1$ is the odd integer $q-2$.

The two formulas follow together from the recurrence
$U_{m+2}=XU_{m+1}+U_m$: multiplication by $X$ shifts the old
coefficients, and the leading coefficient of $U_m$ contributes one to
the next-to-leading coefficient two steps later. The recurrence also
bounds the degree of $U_m$ by $m-1$, so no higher term contributes.

## 追加锚（本行以下为增补区）

## 37. The third coefficient layer of the Fibonacci recurrence polynomial

**Theorem 37.1 (third near-leading coefficient).** For the recurrence
polynomial $U_m(X)$ of Section 33 and every $m\geq5$, the coefficient
at $X^{m-5}$ is

$$
\frac{(m-3)(m-4)}2.
$$

This is the next coefficient layer after Theorem 36.1. The recurrence
transfers it from the preceding polynomial two steps earlier and receives
the second-layer coefficient from the $XU_{m-1}$ term; the leading term
of the remaining summand is too large in degree to contribute.

## 追加锚（本行以下为增补区）

## 38. Odd-index Fibonacci quotient and the recurrence polynomial

**Theorem 38.1 (odd-index recurrence bridge).** Let $n$ be an odd
positive integer. For every $m\geq0$, the recurrence polynomial from
Section 33 satisfies

$$
F_n U_m(L_n)=F_{mn}.
$$

In particular, for $m\geq1$ the integer quotient $F_{mn}/F_n$ equals
$U_m(L_n)$. To see the identity, put $a=\varphi^n$ in the integral
golden ring. Its norm is $-1$ and its trace is $L_n$, so its quadratic
equation reads $a^2=L_n a+1$. The golden coordinate of $a^m$ therefore
obeys the defining recurrence of $U_m$, starts at zero, and has first
value $F_n$. The same coordinate of $a^m=\varphi^{mn}$ is $F_{mn}$.
## 39. A Chebyshev representation of the recurrence polynomial

Let $P_0(X)=0$, $P_1(X)=1$, and
$P_{m+2}(X)=XP_{m+1}(X)+P_m(X)$, so that $P_m$ is the recurrence
polynomial used in Section 33. Over the complex numbers, for every
$m\geq1$,

$$
P_m(X)=(-i)^{m-1}\,U_{m-1}\!\left(\frac{iX}{2}\right),
$$

where $U_k$ is the classical Chebyshev polynomial of the second kind
normalized by $U_0=1$, $U_1=2X$, and
$U_{k+2}=2XU_{k+1}-U_k$. The identity is an equality after mapping the
integer coefficients of $P_m$ into $\mathbb C$. It follows by matching
the initial values and the two recurrences; the factor $(-i)^{m-1}$
converts the minus sign in the Chebyshev recurrence into the plus sign
in $P_m$.
## 40. Opposite-root symmetry at odd order

For the same recurrence polynomial $P_m$, every odd index gives an even
polynomial:

$$
P_{2r+1}(-X)=P_{2r+1}(X)\qquad(r\geq0).
$$

Consequently, if $z$ is a complex root of $P_{2r+1}$, then $-z$ is also
a root. This is the algebraic form of the
opposite pairing used before the trigonometric root formula; it does not
assert the locations or simplicity of the roots.
## 41. The transported root multiset

**Theorem 41.1 (exact complex roots of the odd recurrence polynomial).** For every
$r\geq0$, after mapping the integer recurrence polynomial $P_{2r+1}$ to
$\mathbb C[X]$, its root multiset is

$$
\left\{-2i\cos\frac{(k+1)\pi}{2r+1}:0\leq k<2r\right\},
$$

with each index occurring once. This follows by transporting the real root
multiset of the Chebyshev polynomial of the second kind through the linear
substitution $X\mapsto iX/2$ and then using the complex Chebyshev bridge.
The result identifies the root locations and multiplicities; it does not
yet establish the analytic square-root estimates or the dyadic valuation
argument in Theorem 33.1.

## 42. The exact dyadic valuation of half-binomial coefficients

**Theorem 42.1 (half-binomial valuation).** For every $j\geq0$,

$$
v_2\binom{1/2}{j}=-j-v_2(j!).
$$

Multiply the generalized binomial coefficient by $2^j j!$. Its falling
factorial formula becomes the product of the odd integers $1-2k$ for
$0\leq k<j$. Every factor is prime to $2$, so the product is nonzero
and has dyadic valuation zero. Subtracting the valuations of $2^j$
and $j!$ gives the formula. The result supplies the exact valuation of
the $m=j$ term in (33.2); strict separation from all $m<j$ terms and
the non-square conclusion of Theorem 33.1 still require further proof.

## 43. Dyadic dominance in a finite half-binomial sum

**Theorem 43.1 (last-term valuation).** Let $j\geq1$ and let
$c_0,\ldots,c_j$ be integers with $c_j$ odd. Then

$$
v_2\left(\sum_{m=0}^{j}\binom{1/2}{m}c_m\right)
=-j-v_2(j!).
$$

The exponent $e_m=m+v_2(m!)$ strictly increases with $m$. By Theorem
42.1, the last summand has valuation $-e_j$ because $c_j$ is odd.
Every earlier nonzero summand has valuation at least $-e_m>-e_j$;
zero summands do not affect the sum. The ultrametric valuation law
therefore gives the displayed equality. To obtain the particular
coefficient $s_j$ in (33.2), one must still identify its finite
binomial expansion and prove that its last integer coefficient is odd.

## 44. Dyadic valuation of a formal square-root coefficient

**Theorem 44.1 (half-binomial substitution).** Let
$Q(t)\in\mathbb Z[[t]]$ have zero constant coefficient and an odd
coefficient of $t$. Define the rational formal power series

$$
S_Q(t)=\sum_{m\geq0}\binom{1/2}{m}Q(t)^m.
$$

For every $j\geq1$,

$$
v_2([t^j]S_Q)=-j-v_2(j!).
$$

Only $m\leq j$ contributes to $[t^j]S_Q$, because $Q(0)=0$.
Each $[t^j]Q^m$ is an integer. The coefficient of $t^j$ in $Q^j$
is the $j$th power of the coefficient of $t$ in $Q$, hence is odd.
Theorem 43.1 applies to this finite sum. In Theorem 33.1 the input
is $Q=A-1$; identifying its linear coefficient with $q-2$ connects
this statement to the valuation claim in (33.2).

## 45. The coordinate quotient of a pure-cubic order

**Theorem 45.1 (triangular order lattice).** Let $c,d$ be positive
integers, $k$ an integer, and $v\in\{1,-1\}$. In $\mathbb Z^3$, let
$A_{c,d,k,v}$ be the lattice generated by

$$
(1,0,0),\qquad (0,c,0),\qquad (-kv,-kvc,vd).
$$

Then

$$
\mathbb Z^3/A_{c,d,k,v}\simeq
  (\mathbb Z/c\mathbb Z)\times(\mathbb Z/d\mathbb Z).
$$

The third generator changes the first coordinate freely, its middle
coordinate by a multiple of $c$, and its last coordinate by a multiple
of $d$. Since $v$ is a unit, the lattice is exactly the set of triples
whose middle and last coordinates are divisible by $c$ and $d$.
Reduction of those two coordinates is surjective with this kernel.

For Theorem 11.1, write $B=c^3mn^2$, put $d=c^2n$, and choose
$v\in\{1,-1\}$ and $k\in\mathbb Z$ with $d=v+3k$. The change from
the maximal-order basis $(1,\alpha,\gamma)$ to the displayed order
basis $(1,\theta,\beta)$ has the three columns above. Applying the
quotient result to the actual field still requires a verified
identification of these bases and of the original-depth radical.

## 46. Coordinates of the actual pure-cubic order

**Theorem 46.1 (order coordinate divisibility).** Let $K/\mathbb Q$ be
a cubic number field with a power basis generated by $\alpha$, where
$\alpha^3=mn^2$. Assume $m,n$ are positive, squarefree and coprime.
Take integers $c>0$, $a,k$ and $v\in\{1,-1\}$ satisfying
$c^3mn^2=1+9a$ and $c^2n=v+3k$. Put

$$
\gamma=\frac{1+c\alpha+v\alpha^2/n}{3},\qquad
\theta=c\alpha,\qquad
\beta=\frac{1+\theta+\theta^2}{3}.
$$

The maximal integral basis is $(1,\alpha,\gamma)$. For every
$u,r,s\in\mathbb Z$, the element $u+r\alpha+s\gamma$ belongs to the
order $\mathbb Z+\mathbb Z\theta+\mathbb Z\beta$ if and only if
$c\mid r$ and $c^2n\mid s$. More precisely,

$$
\beta=-kv-kvc\alpha+vc^2n\gamma.
$$

The forward implication compares the unique coordinates in the
maximal integral basis. Conversely, write $r=cb$ and $s=c^2nt$;
because $v^2=1$, changing the third order coefficient to $vt$ and
adjusting the first two coefficients gives the required order
expression. This identifies the actual order lattice with the
triangular lattice of Theorem 45.1 for $d=c^2n$. The claim is about
the displayed pure-cubic field under these hypotheses; applying it
to the original-depth radical still requires that radical's field
and parameter identification.

## 47. The Catalan formula for half-binomial coefficients

**Theorem 47.1 (dyadic Catalan formula).** For every $j\geq1$,

$$
\binom{1/2}{j}
  =(-1)^{j-1}\frac{C_{j-1}}{2^{2j-1}},
$$

where $C_i$ is the integer Catalan number. Thus
$2^{2j-1}\binom{1/2}{j}$ is an integer, independently of the
valuation formula in Theorem 42.1.

Let $C(X)=\sum_{i\geq0}C_iX^i$. Its formal recurrence is
$C(X)=1+XC(X)^2$. Put $T(X)=C(-X/4)$ and
$S(X)=1+(X/2)T(X)$. The recurrence gives $S(X)^2=1+X$ and
$S(0)=1$. The formal binomial series
$B(X)=\sum_{j\geq0}\binom{1/2}{j}X^j$ also satisfies
$B(X)^2=1+X$ and $B(0)=1$. Since $S+B$ has invertible constant
coefficient $2$, the factorization $(S-B)(S+B)=0$ implies $S=B$.
Comparing the coefficient of $X^j$ gives the formula. This supplies
the dyadic-integrality input needed in (33.2); identifying the
specific substitution $A-1$ remains a separate step.

## 48. Additive coordinates in the actual pure-cubic integer ring

**Theorem 48.1 (integral coordinate equivalence).** Under the hypotheses
of Theorem 46.1, let $\mathcal O_K$ be the full ring of integers of $K$.
The map

$$
\Phi:\mathbb Z^3\longrightarrow\mathcal O_K,\qquad
(u,r,s)\longmapsto u+r\alpha+s\gamma
$$

is an isomorphism of additive groups. Its values are algebraic integers
by the integral-basis characterization. Every algebraic integer has
such a triple of integer coordinates, and the triple is unique because
$(1,\alpha,\gamma)$ is a rational basis of $K$. Addition and negation
act coordinatewise. The next step toward Theorem 11.1 is to transport
the order lattice through this equivalence and identify its quotient
with the two cyclic coordinate factors.

## 49. Trace pairing of a Lucas cubic block

**Theorem 49.1 (Lucas-block trace matrix).** Let $j\geq1$, put
$B_j=L_{3^j}^2+3$, and let $K/\mathbb Q$ have a cubic power basis
$(1,\theta,\theta^2)$ with $\theta^3=B_j$. Set
$\beta=(1+\theta+\theta^2)/3$. Then the trace pairing on
$(1,\theta,\beta)$ has matrix

$$
\begin{pmatrix}
3&0&1\\0&0&B_j\\1&B_j&(2B_j+1)/3
\end{pmatrix}.
$$

Indeed, the minimal polynomial of $\theta$ is $T^3-B_j$, so the
traces of $1,\theta,\theta^2$ are $3,0,0$. Reducing products by
$\theta^3=B_j$ gives
$\operatorname{Tr}(\beta)=1$,
$\operatorname{Tr}(\theta\beta)=B_j$, and
$\operatorname{Tr}(\beta^2)=(2B_j+1)/3$. This computes the trace
matrix in Theorem 11.1 under its cubic power-basis hypothesis; it does
not identify the field discriminant or the normalization index.
