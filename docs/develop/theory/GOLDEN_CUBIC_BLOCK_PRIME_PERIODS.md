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
The square-class source scopes are recorded in
[Ribenboim's source note](../../../Library/Factorization/ribenboim2005squareclasses.md).
The Lucas square and twice-square classifications used in the supporting
formalization are Cohn's classical results, recorded in
[Cohn's source note](../../../Library/Factorization/cohn1964squarefibonacci.md).

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
in the form $\psi(Y)\sim Y$, with the consumed quantitative version recorded in
[the PrimeNumberTheoremAnd source note](../../../Library/Weil/primenumbertheoremand2026medium.md),
and $Y_Q\sim Q/2$ give the liminf.
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
## 50. A dyadic analytic obstruction to integer values

**Theorem 50.1 (dyadic series nonintegrality).** Let $r\geq1$ and
$x>2$ be integers. For $j\geq0$, put $e_j=j+v_2(j!)$. Let
$(s_j)_{j\geq0}$ be a complex sequence with $s_0=1$, such that
$2^{e_j}s_j$ is an odd integer for every $j\geq1$ and

$$
|s_j|\leq(\sqrt2)^r4^j\qquad(j\geq0).
$$

Suppose that $\sum_{j\geq0}s_jx^{-2j}=\mu$ and
$128\cdot6^r<x^2-4$. Then

$$
x^r\mu\notin\mathbb Z.
$$

**Proof.** Set $J=\lfloor(r+1)/2\rfloor$, $q=x^2$, and
$C=(\sqrt2)^r$. The exponents $e_j$ increase strictly, since
$j!\mid(j+1)!$. Thus

$$
T=\sum_{j=0}^J2^{e_J}s_jx^{2(J-j)}\in\mathbb Z.
$$

For $N\geq0$, the tail $R_N=\sum_{j\geq N}s_jq^{-j}$ satisfies

$$
|R_N|\leq\frac{C(4/q)^N}{1-4/q}.
$$

The factorial valuation bound $v_2(j!)<j$ for $j\geq1$,
$2J\leq r+1$, and $\sqrt2\leq3/2$ give

$$
2^{e_J}C4^{J+1}\leq8\cdot6^r,
\qquad
2^{e_{J+1}}C4^{J+2}\leq128\cdot6^r.
$$

Since the odd integer $2^{e_{J+1}}s_{J+1}$ is nonzero,
$|s_{J+1}|\geq2^{-e_{J+1}}$. The second estimate and the assumed
gap therefore imply

$$
|R_{J+2}|
 \leq\frac{C4^{J+2}}{q-4}q^{-(J+1)}
 <2^{-e_{J+1}}q^{-(J+1)}
 \leq|s_{J+1}q^{-(J+1)}|.
$$

Hence $R_{J+1}\ne0$. The first estimate also yields

$$
0<|2^{e_J}x^{2J}\mu-T|
 \leq\frac{2^{e_J}C4^{J+1}}{q-4}<1.
$$

If $x^r\mu=M\in\mathbb Z$, then $r\leq2J$ makes
$2^{e_J}x^{2J}\mu=2^{e_J}x^{2J-r}M$ an integer. Its difference
from $T$ is a nonzero integer of modulus less than one, a
contradiction. This analytic and arithmetic argument supplies the
nonintegrality step in Theorem 33.1; the polynomial factorization
and coefficient identification supply its application hypotheses.

## 51. A Lucas modulus obstruction at every nontrivial odd index

**Theorem 51.1 (odd-index Fibonacci nonsquares).** For every odd integer
$m\geq3$, the Fibonacci number $F_m$ is not a square.

**Proof.** Write $m=4t+1$ or $m=4t-1$, where $t\geq1$, and factor
$t=2^r s$ with $s$ odd. Put $n=2^r$ and $L=L_{2n}$. Lucas doubling,
starting from $L_2=3$, gives $L\equiv3\pmod4$: each subsequent
doubling replaces an odd Lucas number by its square minus two.
Moreover $L>0$ by $L_{u+1}=F_u+F_{u+2}$.

In the golden integer ring, set $x=\varphi^{2n}$. Its norm is one
and its trace is $L$, so $x^2+1=Lx$. Reduction modulo $L$ gives
$\varphi^{4n}=-1$. Raising this to the odd power $s$ gives
$\varphi^{4ns}=-1$. If $m=4ns+1$, multiplication by $\varphi$
and comparison of the $\varphi$ coordinate give $F_m=-1\pmod L$.
If $m+1=4ns$, the constant coordinate of
$\varphi^m\varphi=-1$ gives the same congruence, since multiplication
by $\varphi$ sends the $\varphi$ coordinate to the constant coordinate.

The Jacobi symbol satisfies $(-1\mid L)=-1$ because $L\equiv3\pmod4$.
Thus $-1$ is not a square modulo $L$, and neither is the integer $F_m$.
This is the Lucas-modulus obstruction in Cohn's classical argument
(*On Square Fibonacci Numbers*, J. London Math. Soc. 39 (1964),
537--540). It supplies the initial layer $k=0$ in the two residue
classes left by Theorems 30.1 and 32.1. The higher quotient layers
use Theorem 33.1; the coprimality and entry-rank clauses of Lemma 10.2
require their separate valuation arguments.

## 追加锚（本行以下为增补区）

## 54. Inert Eisenstein quotients and conjugation Frobenius

Let $E=\mathbb Z[\omega]$, with $\omega^2+\omega+1=0$. Every element
$z\in E$ has unique integer coordinates
$z=\operatorname{re}(z)+\operatorname{im}(z)\omega$. Quadratic
conjugation is determined by $\overline\omega=\omega^2=-1-\omega$, so

$$
\overline{a+b\omega}=(a-b)-b\omega
\qquad(a,b\in\mathbb Z).
$$

For a rational prime $\ell$, put $\mathbb F_\ell=\mathbb Z/\ell\mathbb Z$
and let

$$
K_\ell=\mathbb F_\ell\oplus\mathbb F_\ell u_\ell,
\qquad u_\ell^2+u_\ell+1=0,
$$

where multiplication is extended from the displayed relation. Write
$\operatorname{re}_\ell$ and $\operatorname{im}_\ell$ for the two
$\mathbb F_\ell$ coordinates in this quadratic algebra. For an integer
$a$, write $[a]_\ell$ for its residue in $\mathbb F_\ell$. Let
$I_\ell=(\ell)\subset E$, and denote the actual quotient map by
$q_\ell:E\to E/I_\ell$.

**Theorem 54.1 (the actual inert quotient and its Frobenius action).**
For every rational prime $\ell$ satisfying $\ell\equiv2\pmod3$, the
ideal $I_\ell$ is maximal, and

$$
\#(E/I_\ell)=\ell^2,
\qquad \operatorname{char}(E/I_\ell)=\ell.
$$

There exists a ring equivalence

$$
e_\ell:E/I_\ell\xrightarrow{\ \sim\ }K_\ell
$$

such that, for every $z\in E$, both coordinate identities hold:

$$
\begin{aligned}
\operatorname{re}_\ell\bigl(e_\ell(q_\ell(z))\bigr)
  &=[\operatorname{re}(z)]_\ell,\\
\operatorname{im}_\ell\bigl(e_\ell(q_\ell(z))\bigr)
  &=[\operatorname{im}(z)]_\ell.
\end{aligned}
$$

For every $z\in E$, Frobenius on this actual quotient is quadratic
conjugation:

$$
q_\ell(z)^\ell=q_\ell(\overline z).
$$

The one equivalence $e_\ell$ satisfies the coordinate conditions for
all $z$ simultaneously. The prime $\ell=2$ is included: $E/(2)$ has
four elements, and $q_2(z)^2=q_2(\overline z)$ for every $z\in E$.

Proof. First, the polynomial $X^2+X+1$ has no root in
$\mathbb F_\ell$. At $\ell=2$, its values at both $0$ and $1$ are
$1$. For an odd prime $\ell\equiv2\pmod3$, one has $\ell\ne3$.
If $r^2+r+1=0$, then $(2r+1)^2=-3$. The discriminant splitting
criterion states that, for an odd prime different from three,
$-3$ is a square in $\mathbb F_\ell$ exactly when
$\ell\equiv1\pmod3$. This excludes the proposed root. Consequently
$K_\ell$ is a field.

Define coordinate reduction by

$$
\rho_\ell:E\longrightarrow K_\ell,
\qquad a+b\omega\longmapsto[a]_\ell+[b]_\ell u_\ell.
$$

The defining quadratic relation makes $\rho_\ell$ a ring
homomorphism. It is surjective because both residue coordinates have
integer representatives. Its kernel is exactly $I_\ell$: the two
coordinates of its image vanish precisely when $\ell\mid a$ and
$\ell\mid b$, which is equivalent to
$a+b\omega=\ell(c+d\omega)$ for integers $c,d$. The quotient
isomorphism theorem therefore gives $e_\ell$, with the asserted
coordinate formulas. Since the target is a field, the kernel is
maximal. The two coordinates give $\#K_\ell=\ell^2$, and the scalar
inclusion $\mathbb F_\ell\hookrightarrow K_\ell$ gives
characteristic $\ell$.

The relation in $K_\ell$ implies $u_\ell^3=1$. Since
$\ell\equiv2\pmod3$, it follows that
$u_\ell^\ell=u_\ell^2=-1-u_\ell$. For all
$A,B\in\mathbb F_\ell$, the characteristic-$\ell$ power identity
and $A^\ell=A$, $B^\ell=B$ yield

$$
\begin{aligned}
(A+B u_\ell)^\ell
  &=A+B u_\ell^\ell\\
  &=(A-B)-B u_\ell.
\end{aligned}
$$

For $z=a+b\omega$, the right-hand side is
$e_\ell(q_\ell(\overline z))$. As $e_\ell$ preserves powers and is
injective, the displayed identity proves
$q_\ell(z)^\ell=q_\ell(\overline z)$. The argument uses no oddness
assumption in its Frobenius step and includes $\ell=2$.

The ring $E$ is the Eisenstein quadratic model used in Sections 9 and
17; this statement supplies its actual rational-prime quotient model.
The discriminant input is
`D5.S3.PrimeForms.Splitting.EisensteinCriterion.neg_three_isSquare_iff`.
The quadratic algebra, quotient isomorphism theorem, and finite-field
power laws are the classical results provided by the pinned Mathlib
modules `Mathlib.Algebra.QuadraticAlgebra.Basic`,
`Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Mathlib.RingTheory.Ideal.Maps`, `Mathlib.Algebra.CharP.CharAndCard`,
and `Mathlib.FieldTheory.Finite.Basic`. Coordinate reduction,
identification of its kernel with $(\ell)$, and the resulting
conjugation transport give the concrete Eisenstein specialization.
The prime and congruence hypotheses are part of the statement; it does
not assert this maximality or Frobenius formula for other rational
primes or for a composite modulus.

## 追加锚（本行以下为增补区）

## 55. Interlevel cubic characters and conjugate-complete constraints

This section continues the actual golden block family of Sections 4 and 8.
For every $j\geq1$, put $x_j=L_{3^j}$ and $B_j=x_j^2+3$. For a prime
$p\mid B_j$, retain its original Fibonacci depth
$h_p=v_p(F_{\rho(p)})=v_p(B_j)$. In
$E=\mathbb Q(\omega)$, with $\omega^2+\omega+1=0$ and
$\lambda=1+2\omega$, retain the primary factor
$\eta_j=-2+(x_j-1)\omega=\omega(x_j+\lambda)$ and its unique oriented
primary factors $\varpi_{j,p}$ from Theorem 8.1. Thus
$\eta_j=\prod_{p\mid B_j}\varpi_{j,p}^{h_p}$ and
$N(\varpi_{j,p})=p$. The symbols $(a/\mathfrak p)_3$ use that same
orientation and the multiplicative extension to coprime denominators.
Theorem 8.2 gives the weighted original-depth value
$\prod_{p\mid B_j}(3/\varpi_{j,p})_3^{h_p}=\omega$.
For $i<j$, the block product and congruences of Section 4 give
$B_i\mid x_j$, $B_j\equiv3\pmod{B_i^2}$, and disjoint prime supports.
Every block prime is greater than five and is congruent to
$1\pmod{2\cdot3^{j+1}}$ at level $j$. Classical cubic reciprocity
for coprime primary elements and the supplementary values of
Dunn--Radziwill, arXiv:2109.07463v3, equations (1.4)--(1.5), are
the arithmetic inputs. The conclusions below continue
Problems/wall-sun-sun-golden-unit-lift.md, GCR.3--GCR.11.

**Theorem 55.1 (GCR2, interlevel phase).** For every $1\leq i<j$,

$$
\left(\frac{\eta_j}{\eta_i}\right)_3
=\left(\frac{\eta_i}{\eta_j}\right)_3=\omega^2.
$$

If
$(\varpi_{i,p}/\varpi_{j,q})_3=\omega^{e_{p,q}}$, with exponents read
modulo three, then the actual cross-support depth balance is

$$
\sum_{p\mid B_i}\sum_{q\mid B_j}h_p h_q e_{p,q}
\equiv2\pmod3.
$$

Proof. Since $B_i\mid x_j$ and $\eta_i\mid B_i$,
$\eta_j\equiv-2-\omega=\omega\lambda\pmod{\eta_i}$.
The supplementary laws and the Section 8 normalization evaluate the
first symbol as $\omega^2$. The two primary factors are coprime, so
cubic reciprocity gives the second. Expanding each denominator and
numerator by Theorem 8.1, with its original exponents $h_p,h_q$,
gives the displayed double sum.

**Theorem 55.2 (GCR3, each earlier oriented prime).** For every
$1\leq i<j$ and each individual prime $p\mid B_i$, define
$\kappa_{i,p}=(\lambda/\varpi_{i,p})_3$. Then

$$
\prod_{q\mid B_j}
\left(\frac{\varpi_{i,p}}{\varpi_{j,q}}\right)_3^{h_q}
=\kappa_{i,p}.
$$

Proof. Since $p\equiv1\pmod9$, the exponent $(p-1)/3$ is divisible by
three, so $(\omega/\varpi_{i,p})_3=1$. The interlevel congruence
$\eta_j\equiv\omega\lambda\pmod{\varpi_{i,p}}$ therefore yields
$(\eta_j/\varpi_{i,p})_3=\kappa_{i,p}$. Cubic reciprocity and the
oriented factorization of $\eta_j$ yield the product. The assertion
retains every earlier prime, including primes with $3\mid h_p$.

For $j\geq1$, let $S_j$ be the set of distinct rational primes
dividing $B_i$ for some $1\leq i<j$, put $t_j=|S_j|$, and write
$\varpi_p=\varpi_{i,p}$ for the unique earlier level containing $p$.
Let $\kappa_p=(\lambda/\varpi_p)_3$. Set

$$
\mathcal M_j=E\bigl(\sqrt[3]{\varpi_p}:p\in S_j\bigr).
$$

**Theorem 55.3 (GCR3a, oriented Kummer vector).** For every
$j\geq1$, independently of any Wall--Sun--Sun assumption,

$$
[\mathcal M_j:E]=3^{t_j},\qquad
\operatorname{Gal}(\mathcal M_j/E)
\simeq(\mathbb Z/3\mathbb Z)^{t_j}.
$$

In coordinates acting on the specified cube roots, the weighted
product of arithmetic Frobenius elements at the current oriented
prime ideals is

$$
\prod_{q\mid B_j}\operatorname{Frob}_{(\varpi_{j,q})}^{h_q}
=(\kappa_p)_{p\in S_j}.
$$

For comparison, with
$E_j=\mathbb Q(\sqrt p:p\in S_j)$, one has
$[E_jE:E]=2^{t_j}$ and
$[E_jE\mathcal M_j:E]=6^{t_j}$. This compares fields; it gives
neither statistical independence on the actual Fibonacci support
nor a lower bound $6^{t_j}$ for a block factor. At $j=1$, the support
is empty and all group and product assertions have their trivial
meaning.

Proof. If $\prod_{p\in S_j}\varpi_p^{a_p}$ is a cube in $E$,
valuation at each selected prime ideal gives $3\mid a_p$.
Kummer theory over $E$, which contains the cube roots of unity,
therefore gives degree $3^{t_j}$ and the stated Galois group;
see Milne, Fields and Galois Theory, Theorem 5.30 and Remark 5.32.
Current block primes avoid three and every earlier support, so the
specified current ideals are unramified. Frobenius on
$\sqrt[3]{\varpi_p}$ multiplies it by
$(\varpi_p/\varpi_{j,q})_3$, and Theorem 55.2 gives each coordinate
of the weighted product. Independent rational-prime square classes
give $[E_j:\mathbb Q]=2^{t_j}$. This totally real field meets $E$
in $\mathbb Q$; the two Galois extensions over $E$ have coprime
degrees, giving the final degree.

**Theorem 55.4 (GCR4, the conditional two-factor block).** Suppose
$j\geq1$ and the actual integer $B_j=P^2Q^3$ for distinct rational
primes $P,Q$. Then $h_P=2$, $h_Q=3$, and

$$
\left(\frac3{\varpi_{j,P}}\right)_3=\omega^2,\qquad
\left(\frac{\varpi_p}{\varpi_{j,P}}\right)_3=\kappa_p^2
\quad(p\in S_j),\qquad
\left(\frac{\eta_i}{\varpi_{j,P}}\right)_3=\omega
\quad(1\leq i<j).
$$

In particular, three is not a cube modulo $P$. The older quadratic
conditions also give $(p/Q)=1$ for every $p\in S_j$ and
$Q\equiv19\pmod{40}$. When $j\geq2$, the integer congruence further
requires

$$
P^6\equiv11\pmod{19},\qquad
P\bmod19\in\{4,6,9,10,13,15\}.
$$

Proof. The depth-three factor contributes one to any cubic character.
Theorem 8.2 therefore gives
$(3/\varpi_{j,P})_3^2=\omega$. Squaring is its own inverse on the
group of cube roots of unity, giving the first value. The same
operation applied to Theorems 55.2 and 55.1 gives the remaining two.
The rational noncube assertion is the residue-field interpretation
of the first value. For $j\geq2$, $B_1=19$ and
$B_j\equiv3\pmod{B_1^2}$ imply
$P^2Q^3\equiv3\pmod{19}$; taking sixth powers and using the
cube-root-of-unity condition yields $P^6\equiv11\pmod{19}$.
Checking the eighteen nonzero residues gives the listed classes.
These are necessary conditions; they do not exclude or construct
such a block.

For each $p\in S_j$, retain the primary generator $\varpi_p$ and
its conjugate $\overline{\varpi_p}$. Their product is the rational
prime $p$, both factors are primary, and $p\equiv1\pmod9$.

**Theorem 55.5 (GCC1, conjugate and rational balances).** For every
$j\geq1$ and every $p\in S_j$,

$$
\prod_{q\mid B_j}
\left(\frac{\overline{\varpi_p}}{\varpi_{j,q}}\right)_3^{h_q}
=\kappa_p^{-1},\qquad
\prod_{q\mid B_j}
\left(\frac{p}{\varpi_{j,q}}\right)_3^{h_q}=1.
$$

If exactly one current prime $P\mid B_j$ has $3\nmid h_P$, then
for every $p\in S_j$,

$$
p^{(P-1)/3}\equiv1\pmod P.
$$

This applies when $B_j=P^2Q^3$. No individual cubic-residuosity
conclusion is made when two or more current depths are nonzero
modulo three.

Proof. The defining residue-field exponent gives
$(\overline a/\overline b)_3
=\overline{(a/b)_3}$. Since
$\overline\lambda=-\lambda$ and $-1$ is a cube,
$(\lambda/\overline{\varpi_p})_3=\kappa_p^{-1}$.
Also $(\omega/\overline{\varpi_p})_3=1$ because
$p\equiv1\pmod9$. As $p\mid x_j$, both prime factors of $p$
divide $x_j$, and
$\eta_j\equiv\omega\lambda\pmod{\overline{\varpi_p}}$.
Cubic reciprocity and Theorem 8.1 give the first product.
Multiplying it by Theorem 55.2 and using
$\varpi_p\overline{\varpi_p}=p$ gives the second.
If only $P$ has depth nonzero modulo three, the other terms are
one, and exponentiation by $h_P$ is invertible on cube roots of
unity. The residue field at $\varpi_{j,P}$ is $\mathbb F_P$.

**Theorem 55.6 (GCC2, the inert-prime-two balance).** For every
$j\geq1$,

$$
\left(\frac2{\eta_j}\right)_3
=\prod_{q\mid B_j}
\left(\frac2{\varpi_{j,q}}\right)_3^{h_q}
=\omega.
$$

If $B_j=P^2Q^3$ for distinct primes, then in the direction selected
by $\eta_j$,

$$
\left(\frac2{\varpi_{j,P}}\right)_3
=\left(\frac3{\varpi_{j,P}}\right)_3=\omega^2,
$$

so two and three are noncubes modulo $P$, while twelve and eighteen
are cubes. Their multiplicative orders satisfy

$$
v_3(\operatorname{ord}_P(2))
=v_3(\operatorname{ord}_P(3))
=v_3(P-1)=j+1.
$$

Proof. The primary element $-2$ generates the inert prime ideal
above two, and its residue field has four elements. Since $x_j$ is
even, $\eta_j\equiv\omega\pmod2$. Reciprocity for $-2$ and
$\eta_j$, and the exponent $(4-1)/3=1$ at that prime, give
$(2/\eta_j)_3=(-2/\eta_j)_3=(\eta_j/-2)_3=\omega$.
Factor $\eta_j$ to obtain the first product. In the two-factor case,
the depth-three contribution is one; invert squaring on cube roots
of unity and use Theorem 55.4 for the value at three.
Multiplicativity gives the cube claims for twelve and eighteen.

To compute the exact ternary order, put $r_j=3^{j+1}$ and temporarily
$B_0=4$. The recurrence yields
$B_{j+1}-1=(B_j-1)((B_j-1)^2-3)$.
Starting from $B_0-1=3$ gives
$v_3(B_j-1)=j+1$ and
$(B_j-1)/r_j\equiv(-1)^j\pmod3$.
Every current block prime is $1\pmod{2r_j}$.
Expanding $P^2Q^3$ modulo $3r_j$ gives
$2(P-1)/r_j\equiv(-1)^j\pmod3$, hence
$v_3(P-1)=j+1$. A noncube in the cyclic group
$\mathbb F_P^\times$ retains its full three-primary order.
The general balances at two and three need not have the same
witnessing prime; this shared-prime conclusion uses $P^2Q^3$.

Set $t=t_j=|S_j|$ and define

$$
\widehat{\mathcal M}_j
=E\bigl(\sqrt[3]{\varpi_p},\sqrt[3]{\overline{\varpi_p}}
:p\in S_j\bigr),\qquad
\mathcal L_j=\widehat{\mathcal M}_j
\bigl(\sqrt[3]2,\sqrt[3]3\bigr).
$$

**Theorem 55.7 (GCC3, the conjugate-complete Kummer field).** For
every $j\geq1$, without a Wall--Sun--Sun assumption,

$$
[\widehat{\mathcal M}_j:E]=3^{2t},\qquad
[\mathcal L_j:E]=3^{2t+2}.
$$

The first field is the normal closure over $\mathbb Q$ of
$\mathcal M_j$; both fields are Galois over $\mathbb Q$.
Choose conjugate pairs of cube roots and real cube roots of two
and three. In additive coordinates
$(u,v,(a_p,b_p)_{p\in S_j})$ for
$\operatorname{Gal}(\mathcal L_j/E)$, complex conjugation acts by

$$
c(u,v,(a_p,b_p)_p)c^{-1}
=(-u,-v,(-b_p,-a_p)_p).
$$

For each $p\in S_j$, choose $k_p\in\mathbb Z/3\mathbb Z$ with
$\kappa_p=\omega^{k_p}$, and define the coordinate tuple
$g_j=(2,2,(2k_p,-2k_p)_{p\in S_j})$ independently of any
factorization hypothesis on $B_j$. The weighted current
Frobenius product is

$$
\prod_{q\mid B_j}\operatorname{Frob}_{(\varpi_{j,q})}^{h_q}
=(1,1,(k_p,-k_p)_{p\in S_j}).
$$

Under $B_j=P^2Q^3$, the oriented Frobenius at $P$ is $g_j$.

Proof. The earlier factors $\varpi_p,\overline{\varpi_p}$ have
valuation one at their separate prime ideals and zero at the other
listed ideals. Valuation above two detects the exponent of two;
valuation at $\lambda$ detects twice the exponent of three.
Thus these $2t+2$ classes are independent in
$E^\times/(E^\times)^3$. Kummer theory gives both degrees and the
elementary abelian groups. Conjugation exchanges paired radicands,
fixes the real radicands, and inverts $\omega$, yielding the action
and normality over $\mathbb Q$. Current oriented ideals avoid two,
three, and earlier supports, so their Frobenius coordinates are the
cubic symbols. Theorems 55.2, 55.5, and 55.6 and the Section 8
three-balance give the displayed vector. Under $P^2Q^3$, cubing
kills the $Q$ contribution and squaring is invertible.
For rational $p=\varpi_p\overline{\varpi_p}$, the coordinate
$a_p+b_p$ at $g_j$ is zero, so this is complete splitting at $P$
in every $T^3-p$. The one-direction degree $3^t$ of Theorem 55.3
cannot replace the conjugate-complete degree $3^{2t}$.

**Theorem 55.8 (GCC4, compatibility density).** Fix $j\geq1$ and
its actual earlier support. Let
$m_j=80\cdot3^{j+2}$. For every fixed unit residue $a\bmod m_j$
with $a\equiv1\pmod3$, the unrestricted rational primes
$P\equiv a\pmod{m_j}$ for which one prime of $E$ above $P$
has Frobenius $g_j$ in $\mathcal L_j/E$ have Dirichlet density

$$
\frac{2}{\varphi(m_j)3^{2t+2}}>0.
$$

This does not impose $P\mid B_j$, $h_P=2$, or a second prime $Q$.
It is compatibility of necessary character conditions among
unrestricted primes, not realization of the actual factorization.

Proof. Put $C=\mathbb Q(\zeta_{m_j})$, which contains $E$.
First $\mathcal L_j\cap C=E$. Any nontrivial intersection would
contain an elementary abelian cubic extension over $E$.
The three-Sylow subgroup of $\operatorname{Gal}(C/E)$ is cyclic, so
this would contain its unique degree-three subextension
$E(\zeta_9)=E(\sqrt[3]\omega)$. Kummer correspondence would place
the class of $\omega$ in the span of the radicands defining
$\mathcal L_j$. Valuations at each earlier oriented and conjugate
prime, at two, and at $\lambda$ force every such radicand exponent
to vanish modulo three. The remaining assertion that $\omega$
is a cube in $E$ is false: its cube root would have order nine,
while $E$ has only six roots of unity.

The residue $a$ specifies an automorphism $\sigma_a$ of $C$
fixing $E$ and combines with $g_j$ to an element of
$\operatorname{Gal}(\mathcal L_jC/\mathbb Q)$.
Elements fixing $E$ commute with $g_j$. Complex conjugation takes
$g_j$ to $(1,1,(2k_p,-2k_p)_p)$, a different element, and fixes
$\sigma_a$ under conjugation because $C/\mathbb Q$ is abelian.
This conjugacy class has two elements; the group has order
$\varphi(m_j)3^{2t+2}$. The Chebotarev density theorem yields
the displayed density. Sutherland, MIT 18.785 Lecture 28,
Theorem 28.9, is a classical locator. The proof uses neither GRH
nor an effective least-prime bound.

Compatible unit classes also satisfy $(5/a)=1$ and
$a\equiv1+2(-1)^j r_j\pmod{6r_j}$, where $r_j=3^{j+1}$:
choose an odd compatible class modulo sixteen, a nonzero square
class modulo five, and apply CRT. For fixed $j$, the primes with
the exact Fibonacci period required here form the finite support
of $B_j$; the positive density among unrestricted primes supplies
no prime in that finite support.

**Theorem 55.9 (GCC5, exact cubic Thue descent).** Suppose
$j\geq1$ and $B_j=P^2Q^3$ for distinct rational primes $P,Q$.
Write the oriented primary generators
$\pi=\varpi_{j,P}=a+b\omega$ and
$\gamma=\varpi_{j,Q}=u+v\omega$, and put

$$
\begin{aligned}
A&=a^2-b^2,&D&=2ab-b^2,\\
U&=u^3-3uv^2+v^3,&V&=3uv(u-v).
\end{aligned}
$$

Then $\eta_j=\pi^2\gamma^3$ gives the exact integer system

$$
\begin{aligned}
f_\pi(u,v)
&:=Au^3-3Du^2v+3(D-A)uv^2+Av^3=-2,\\
g_\pi(u,v)&:=DU+(A-D)V=L_{3^j}-1,\\
u^2-uv+v^2&=Q.
\end{aligned}
$$

The generators satisfy their primary congruences. The cubic form
$f_\pi$ is irreducible over $\mathbb Q$, has discriminant
$81P^4$, and has a totally real cyclic cubic splitting field.
For each fixed $\pi$, $f_\pi(u,v)=-2$ has only finitely many
integer solutions. Conversely, fix a primary $\pi$ of prime norm
$P$ and integers $u,v$ whose norm $Q=u^2-uv+v^2$ is a distinct
prime. If $f_\pi(u,v)=-2$ and
$g_\pi(u,v)+1=L_{3^j}$ exactly, then $B_j=P^2Q^3$.

Proof. Eisenstein multiplication gives
$\pi^2=A+D\omega$, $\gamma^3=U+V\omega$, and their product
has coefficients $AU-DV$ and $DU+(A-D)V$. Compare with
$\eta_j=-2+(L_{3^j}-1)\omega$. For all integer
$a,b,u,v$, the norm identity is

$$
f_\pi(u,v)^2-f_\pi(u,v)g_\pi(u,v)+g_\pi(u,v)^2
=(a^2-ab+b^2)^2(u^2-uv+v^2)^3.
$$

The binary-cubic discriminant calculation for coefficients
$(A,-3D,3(D-A),A)$ gives
$81(A^2-AD+D^2)^2=81(a^2-ab+b^2)^4=81P^4$.
Its Hessian, in the standard binary-cubic normalization, is
$9P^2(u^2-uv+v^2)$. Also $A\ne0$: either $a=b$ or
$a=-b$ would contradict primality of $P$. If $f_\pi$ had a
rational projective zero, take nonzero $z=u+v\omega$.
The resulting rational multiple relation for $\pi^2z^3$,
divided by its conjugate, gives

$$
(z/\overline z)^3
=\omega^2(\overline\pi/\pi)^2.
$$

At $(\pi)$, the valuation on the left is divisible by three
and that on the right is $-2$, a contradiction. A reducible
rational cubic has a rational projective zero, so $f_\pi$ is
irreducible. Its positive square discriminant gives Galois group
$A_3$ and a totally real cyclic splitting field. Classical
Thue finiteness applies for each fixed irreducible form and
nonzero right-hand side. The converse follows from the norm
identity with the prime norms and exact Lucas coordinate.
Dropping that coordinate produces a different Diophantine problem.
The fixed-input Thue framework is described by von Kaenel--Matschke,
arXiv:1605.06079, Sections 5.1--5.3; no complete solution list
or uniform bound as $P$ varies follows here.

## 56. Common golden cubic fields and independent fixed-curve points

This section continues Library/ArithUnits/dunn2024cubicreciprocity.md,
GIR.3--GIR.5, using the actual blocks and positive roots of
Sections 11--13. For $j\geq1$, let
$\theta_j=\sqrt[3]{B_j}>0$, $k_j=\mathbb Q(\theta_j)$,
$x_j=L_{3^j}$, and $f_j=F_{3^j}$. Write
$B_j=d_jc_j^3$ uniquely with positive $c_j$ and cubefree
$d_j=\prod_{p\mid B_j}p^{e_p}$, where
$e_p\equiv h_p\pmod3$ and $e_p\in\{0,1,2\}$.
Let $R_j=\operatorname{rad}(d_j)>1$.
Theorem 11.1 gives the original-depth index and field discriminant;
Theorem 12.1 supplies actual infinite-order points on both rational
twists. For $J\geq1$, define

$$
F_J=\mathbb Q(\theta_1,\ldots,\theta_J),\qquad
N_J=F_J(\omega),\qquad
R^{(J)}=\prod_{j=1}^J R_j.
$$

The conclusions below continue the named Library source.

**Theorem 56.1 (GIR3, common field and discriminants).** For every
$J\geq1$,

$$
[F_J:\mathbb Q]=3^J,\qquad
[N_J:\mathbb Q]=2\cdot3^J,\qquad
\operatorname{Gal}(N_J/\mathbb Q)
\simeq(\mathbb Z/3\mathbb Z)^J\rtimes C_2.
$$

Complex conjugation acts by inversion on the cubic coordinates.
$F_J$ has signature $(1,(3^J-1)/2)$: its designated embedding lies
in $\mathbb R$, but it is not totally real. The exact absolute
discriminants and root discriminant are

$$
\begin{aligned}
|\Delta(F_J)|
&=3^{(3^J-1)/2}(R^{(J)})^{2\cdot3^{J-1}},\\
|\Delta(N_J)|
&=3^{3^J}(R^{(J)})^{4\cdot3^{J-1}},\\
\operatorname{rd}(N_J)
&=\sqrt3\,(R^{(J)})^{2/3}.
\end{aligned}
$$

Proof. Suppose $\prod_{j=1}^J B_j^{a_j}$ is a cube in $E$.
For each $j$, choose a prime $p\mid B_j$ with
$3\nmid h_p$. The block supports are disjoint. Valuation at either
prime of $E$ over $p$ gives $3\mid a_jh_p$ and hence $3\mid a_j$.
Thus the block classes are independent in
$E^\times/(E^\times)^3$. Kummer theory gives degree $3^J$
over $E$. Positive cube roots are fixed by conjugation, which
inverts $\omega$, yielding the semidirect action. Since $F_J$
lies in $\mathbb R$ in the chosen embedding, $F_J\cap E=\mathbb Q$.
An embedding is real exactly when all positive cube roots map to
their unique real conjugates; precisely one does, giving the
signature.

At a rational prime $p\mid R^{(J)}$, exactly one radicand has
valuation nonzero modulo three. Over the maximal unramified
local extension, units have cube roots because $p\ne3$, so
inertia in $N_J$ has order three and translates one coordinate.
No other prime away from three ramifies. At three, each actual
$B_j\equiv1\pmod9$ is a cube in $\mathbb Q_3$ by the Hensel
calculation in Theorem 11.1; a completion of $N_J$ is
$\mathbb Q_3(\omega)$, with inertia order two and residue
degree one.

All these ramification steps are tame. The tame discriminant
exponent is the extension degree minus the number of inertia
orbits on embeddings. On the $3^J$ embeddings of $F_J$, a
nonzero coordinate translation has $3^{J-1}$ orbits;
inversion has one fixed point and $(3^J-1)/2$ two-cycles.
This gives the first discriminant formula. On the regular
action for $N_J$, inertia orders three and two give exponents
$4\cdot3^{J-1}$ and $3^J$, respectively. Taking the
$(2\cdot3^J)$-th root gives the root discriminant.
No bounded-root-discriminant claim is made as $J$ increases.

Fix the two curves over $\mathbb Q$,

$$
\mathcal E^-:y^2=x^3-3,\qquad
\mathcal E^+:y^2=x^3+125.
$$

**Theorem 56.2 (GIR4, independent points on both fixed curves).**
For every $J\geq1$ and $1\leq j\leq J$, the actual points

$$
P_j^-=(\theta_j,x_j),\qquad
P_j^+=(5\theta_j,25f_j)
$$

belong to $\mathcal E^-(F_J)$ and $\mathcal E^+(F_J)$,
respectively. For each sign, these $J$ points are
$\mathbb Z$-linearly independent even modulo the
$\mathbb Q$-rational points. Over $N_J$, let
$\iota(x,y)=(\omega x,y)$. Then the $2J$ points
$P_j^\pm,\iota(P_j^\pm)$ are
$\mathbb Z$-linearly independent even modulo the
$E$-rational points. Consequently

$$
\operatorname{rank}\mathcal E^\pm(F_J)
\geq\operatorname{rank}\mathcal E^\pm(\mathbb Q)+J,\qquad
\operatorname{rank}\mathcal E^\pm(N_J)
\geq\operatorname{rank}\mathcal E^\pm(E)+2J.
$$

Both fixed curves therefore have infinite rank over the
explicit union of the $F_J$. The field degree is $3^J$;
this is not a fixed-number-field or uniformly bounded-degree
construction.

Proof. The curve equations are
$x_j^2=B_j-3$ and $625f_j^2=125(B_j+1)$.
Over $k_j$, dividing the raw $B_j$-twist point coordinates
of Theorem 12.1 by $\theta_j^2$ and
$\theta_j^3=B_j$ identifies them with the displayed fixed-curve
points. Their infinite order follows from that theorem.
For each $j$, the automorphism
$\sigma_j\in\operatorname{Gal}(N_J/E)$ multiplies
$\theta_j$ by $\omega$ and fixes the other roots. It sends
$P_j$ to $\iota P_j$ and fixes $P_i$ for $i\ne j$.
The three CM rotations lie on one horizontal line, giving
$1+\iota+\iota^2=0$, and

$$
(\iota-1)(\iota^2-1)=[3],\qquad
(a+b\iota)(a+b\iota^2)=[a^2-ab+b^2].
$$

Apply $\sigma_j-1$ and then $\iota^2-1$ to a relation
$\sum_i a_iP_i$ equal to a $\mathbb Q$-rational point.
It follows that $[3a_j]P_j=O$, hence $a_j=0$.
For a relation
$\sum_i(a_i+b_i\iota)P_i$ equal to an $E$-rational
point, apply $\sigma_j-1$, then $\iota^2-1$, then
$a_j+b_j\iota^2$. This yields
$[3(a_j^2-a_jb_j+b_j^2)]P_j=O$.
The positive quadratic norm and infinite order force
$a_j=b_j=0$. The same reasoning after multiplying a
torsion relation by its order gives independence modulo the
indicated base-field point groups.

Choose one fixed absolute normalization of canonical height
$\widehat h$ and write
$H_j^\pm=\widehat h(P_j^\pm)>0$.

**Theorem 56.3 (GIR5, the constructed height lattice).**
For each sign and every $J\geq1$, different layers,
including their CM rotations, are orthogonal under the
canonical-height pairing. On
$(P_1^\pm,\iota P_1^\pm,\ldots,
P_J^\pm,\iota P_J^\pm)$ the Gram matrix is block diagonal,
with $j$-th block

$$
H_j^\pm
\begin{pmatrix}1&-1/2\\-1/2&1\end{pmatrix}.
$$

Its determinant is

$$
(3/4)^J\prod_{j=1}^J(H_j^\pm)^2>0.
$$

On the $J$ real points alone the matrix is diagonal with
entries $H_j^\pm$. This determinant belongs to the constructed
subgroup; it is not the full Mordell--Weil regulator.

Proof. Canonical height and its bilinear pairing are Galois
invariant. The automorphism $\iota$ preserves height because
its multiplier on the $x$ coordinate is a root of unity.
For $i\ne j$, $\sigma_j$ fixes the $i$-th point and cycles
the three rotations of the $j$-th point. All three pairings
with the fixed point are equal, and their sum is zero by
$1+\iota+\iota^2=0$, so each vanishes. Within one layer,
$P+\iota P=-\iota^2P$ has height $H$.
Bilinearity gives $H=2H+2\langle P,\iota P\rangle$,
so the off-diagonal entry is $-H/2$. Each block has
determinant $3H^2/4$, and multiplying proves the formula.
Neither saturation nor a basis of all rational points is
established, and no numerical height value is used.

## 追加锚（本行以下为增补区）


## 57. Trace and norm denominators on a smooth Weierstrass curve

Let $F$ be a field and let $W$ be a smooth Weierstrass curve over $F$,
with coefficients $a_1,a_2,a_3,a_4,a_6$. Write

$$
A(X)=a_1X+a_3,\qquad
B(X)=X^3+a_2X^2+a_4X+a_6.
$$

The quadratic coordinate relation is $Y^2+A(X)Y-B(X)=0$.
The expressions $2p-qA$ and $p^2-pqA-q^2B$ are respectively
the trace and norm numerators of $p+qY$. Their denominator
criterion supplies the coordinate divisibility needed in the
integral-closure construction for the actual curves of Section 56.

**Theorem 57.1 (trace and norm denominator criterion).** For all
$p,q,d\in F[X]$ with $d\ne0$, if

$$
d\mid 2p-qA,\qquad d^2\mid p^2-pqA-q^2B,
$$

then $d\mid p$ and $d\mid q$. This assertion includes fields of
characteristic two and three.

Proof. Fix a prime polynomial $\pi$ dividing $d$. If
$\pi\nmid q$, division in $F[X]/(\pi)$ supplies a polynomial $g$
with $p\equiv gq\pmod\pi$. The trace and norm divisibilities then
give $\pi\mid2g-A$ and $\pi^2\mid g^2-gA-B$.
Differentiating the latter relation and using the former gives
$\pi\mid a_1g+B'$. Over the residue field at $\pi$, the point
$(X,-g)$ therefore lies on $W$ and both partial derivatives
vanish. This contradicts smoothness. Thus $\pi\mid q$; the norm
relation also gives $\pi\mid p$. Divide $p,q$ by $\pi$ and
cancel $\pi$ and $\pi^2$ from the trace and norm divisibilities.
Factorization induction on $d$ finishes the argument; units divide
both coordinates.

The source of this denominator criterion is
TauCetiProject/TauCeti, commit
`33c2099c678ea391f7ea3e0ddaf945a76a625e5d`,
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean`;
the same source appears at commit
`65482a19dabd31843aab0cf8469c5e7613988eba` under Apache-2.0.
The criterion alone does not construct the global point map,
the Galois action on the common fields, or the canonical height.

## 追加锚（本行以下为增补区）


## 58. Cubic reciprocity at distinct oriented rational primes

Write $\mathcal E=\mathbb Z[\omega]$, with
$\omega^2+\omega+1=0$. For a maximal ideal $P$ with finite residue
field of cardinality $p\equiv1\pmod3$, let $\chi_P(a)$ be the
cube root of unity selected by the Euler criterion in
$\mathcal E/P$, as in Section 8.

**Theorem 58.1 (primary cubic reciprocity at distinct rational norms).**
Let $p,q$ be distinct rational primes, both congruent to one modulo
three. Let $P,Q$ be maximal ideals of $\mathcal E$ whose residue
fields have cardinalities $p,q$. Suppose that $\pi,\rho\in\mathcal E$
satisfy

$$
P=(\pi),\qquad Q=(\rho),\qquad
N(\pi)=p,\qquad N(\rho)=q,\qquad
3\mid\pi-1,\qquad3\mid\rho-1.
$$

Then

$$
\chi_Q(\pi)=\chi_P(\rho).
$$

Proof. The primary normalization of the cubic Jacobi sum is
$J=-\pi$. In a finite extension of the residue field at $Q$
containing the additive character values, the Gauss cube identity
and the $q$-power Frobenius computation give

$$
\chi_P(q)=\chi_Q(\pi)\chi_Q(\bar\pi)^2.
$$

Apply the same computation after exchanging $p$ and $q$.
The norm identities and distinct rational characteristics ensure
that all four arguments are nonzero in the relevant residue
fields, so these characters multiply and take values in
$\{1,\omega,\omega^2\}$. With

$$
A=\chi_Q(\pi),\quad B=\chi_Q(\bar\pi),\quad
C=\chi_P(\rho),\quad D=\chi_P(\bar\rho),
$$

the two computations read $CD=AB^2$ and $AB=CD^2$.
Since $B^3=D^3=1$, their quotient gives $BD=1$ and then $A=C$.
The assertion applies to the disjoint supports of different
actual Lucas blocks in Section 55. It does not address two
conjugate prime factors with equal rational norm.

The classical primary reciprocity statement and its normalization
are described in Dunn--Radziwill, arXiv:2109.07463v3,
equations (1.4)--(1.5). The argument above uses the Gauss and
Jacobi sum identities in the pinned Mathlib library and retains
both Frobenius directions.

## 追加锚（本行以下为增补区）


## 59. Simultaneous square periods and sinks in a finite support

Let $S$ be a nonempty finite set of rational primes greater than five,
and put $M=\prod_{p\in S}p$. Let $Q$ be the Fibonacci matrix
$\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$.
Write $\pi(m)$ for its order modulo $m$ and $\pi_s(m)$ for the order
of $Q^s$ modulo $m$. For each $p\in S$, retain the original rank
$\rho(p)$ and depth $h_p=v_p(F_{\rho(p)})$. Put $\tau_p=\pi(p)$.
Draw a directed edge $p\longrightarrow q$ when $p\mid\tau_q$;
a sink has no outgoing edge to any member of $S$.
These are the objects of PCL.3--PCL.4 in
Problems/wall-sun-sun-golden-unit-lift.md.

**Theorem 59.1 (finite-support square period ratio).** Every edge
$p\longrightarrow q$ satisfies $p<q$, so the directed graph has
no nonempty directed cycle. For every $s\geq1$ with
$\gcd(s,M)=1$,

$$
\frac{\pi_s(M^2)}{\pi_s(M)}
=\prod_{\substack{p\in S\\p\text{ is a sink}\\h_p=1}}p.
$$

Consequently,

$$
\pi_s(M^2)=\pi_s(M)
\quad\Longleftrightarrow\quad
h_p\geq2\text{ for every sink }p\in S.
$$

If the periods are equal, the largest prime of $S$ has
original Fibonacci depth at least two.

Proof. The split and inert prime-period bounds give
$\tau_q\mid q-1$ or $\tau_q\mid2(q+1)$, and $q\nmid\tau_q$.
Any prime divisor $p$ of these bounds is smaller than $q$;
in the inert case an odd $p$ divides $(q+1)/2$. Thus every
edge strictly increases its prime label, and the maximum is a sink.
The Chinese remainder equivalence identifies the matrix orders
modulo $M$ and $M^2$ with the least common multiples of the
orders on their prime and prime-square factors. The exact lift is
$\pi(p^2)=\tau_p p^{\max(2-h_p,0)}$.
A depth-one factor $p$ is already present in the least common
multiple of the $\tau_q$ exactly when some edge leaves $p$.
The factors not already present are therefore precisely the
depth-one sinks; they are pairwise coprime and coprime to that
least common multiple. Taking the order of $Q^s$ divides each
order by its gcd with $s$. Since $s$ is coprime to $M$, none of
the remaining sink factors cancels, giving the displayed ratio.
The product equals one exactly when it is empty. Positivity
of all original depths then gives the equivalence and maximum
prime consequence.

The equal-period test detects all sinks at once. It does not
imply depth at least two for nonsinks whose prime factor is
already masked by another residue period.

## 追加锚（本行以下为增补区）


## 60. Largest-prime depth under arbitrary period iteration

Let $Q$ be the Fibonacci matrix and let $\pi(m)$ denote its
order over $\mathbb Z/m\mathbb Z$. For a prime $P>5$, write
$\rho(P)$ for the first positive Fibonacci index divisible by
$P$, and put $h_P=v_P(F_{\rho(P)})$. Iteration $\pi^{\circ n}$
means repeated application of the period function, with
$\pi^{\circ0}(m)=m$.

**Theorem 60.1 (original-depth loss for every positive modulus).**
Let $m$ be any positive integer whose largest prime divisor
is $P>5$, and put $a=v_P(m)$. For every integer $n\geq0$,

$$
v_P(\pi^{\circ n}(m))=\max(a-nh_P,0).
$$

The prime $P$ divides the $n$th iterate exactly when

$$
n<\left\lceil\frac{a}{h_P}\right\rceil
=\frac{a+h_P-1}{h_P}\quad\text{with integer division}.
$$

Thus its first disappearance occurs at iteration
$\lceil a/h_P\rceil$, and it never returns. Every positive
fixed point of $\pi$ has no prime divisor greater than five.
If $\pi(m^2)=\pi(m)$ for the same $m$ and $P$, then
$h_P\geq2a$.

Proof. The determinant of $Q$ is $-1$, so its reduction is
invertible over every finite residue ring. In particular all
periods, and hence all iterates of a positive modulus, are positive.
The Chinese remainder decomposition identifies each period with
the least common multiple of its prime-power periods. At a prime
$q>5$, the exact lift is
$\pi(q^b)=\pi(q)q^{\max(b-h_q,0)}$; every prime divisor of
$\pi(q)$ is smaller than $q$.

For the small primes, direct matrix returns and binomial lifting give

$$
\pi(2^{u+2})\mid6\cdot2^u,\qquad
\pi(3^{u+1})\mid8\cdot3^u,\qquad
\pi(5^{u+1})\mid20\cdot5^u\qquad(u\geq0).
$$

The remaining moduli $2$ and $1$ have periods $3$ and $1$.
Consequently none of the small-prime factors contributes a prime
greater than five. No prime larger than $P$ is created, and only
the factor $P^a$ can contribute $P$ to the next period. The
factorization of a least common multiple takes the maximum local
valuation, so the next $P$-valuation is $\max(a-h_P,0)$.
Induction gives the displayed formula even after $P$ disappears.
Since $h_P>0$, the first-zero threshold follows. A fixed point
containing a prime greater than five contradicts the strict
decrease at its largest prime. Finally, equality of the periods
of $m$ and $m^2$ gives
$\max(2a-h_P,0)=\max(a-h_P,0)$; with $a>0$ this forces
$2a\leq h_P$.

This is PCL12 for arbitrary positive moduli in
Problems/wall-sun-sun-golden-unit-lift.md. It neither classifies
all fixed points nor bounds the total time to a fixed point, and
it places no upper bound on the original depth $h_P$.

## 追加锚（本行以下为增补区）


## 61. Exact masking for arbitrary finite prime-power support

Let $S$ be a nonempty finite set of distinct primes greater than five.
Write $Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$,
$\pi(m)$ for the order of $Q$ modulo a positive integer $m$, and
$\pi_s(m)$ for the order of $Q^s$ modulo $m$. For $p\in S$, let
$\tau_p=\pi(p)$, let $\rho(p)$ be the first positive Fibonacci index
divisible by $p$, and keep its original depth
$h_p=v_p(F_{\rho(p)})$. Fix positive integers $a_p$ and $s$, and put

$$
M_0=\prod_{p\in S}p,\qquad
m=\prod_{p\in S}p^{a_p},\qquad
T=\operatorname{lcm}_{p\in S}\tau_p,\qquad
\beta_p=v_p(T),\qquad u_p=v_p(s).
$$

**Theorem 61.1 (combined coupling and stride masking).** For every
choice above, without an assumption that any depth equals one,

$$
\pi_s(m)=\frac{T}{\gcd(T,s)}
  \prod_{p\in S}p^{\max(0,a_p-h_p-\max(\beta_p,u_p))}.
$$

Fix $p_0\in S$. For $e\geq1$, let
$m_e=p_0^e\prod_{q\in S\setminus\{p_0\}}q$, keeping every other
support exponent equal to one. Then

$$
\pi_s(m_e)=\pi_s(M_0)
  p_0^{\max(0,e-h_{p_0}-\max(\beta_{p_0},u_{p_0}))}.
$$

Consequently $\pi_s(m_e)>\pi_s(M_0)$ holds exactly when
$e>h_{p_0}+\max(\beta_{p_0},u_{p_0})$. The first contributing
exponent is $h_{p_0}+\max(\beta_{p_0},u_{p_0})+1$.

Proof. The exact prime-power lift gives
$\pi(p^{a_p})=\tau_p p^{\max(a_p-h_p,0)}$, where
$p\nmid\tau_p$ and $h_p>0$. Chinese remaindering makes
$\pi(m)$ the least common multiple of these local periods.
At a support prime $p$, its valuation is
$\max(\beta_p,a_p-h_p)$; at every prime outside $S$, it is
the valuation of $T$. The order-of-a-power identity gives
$\pi_s(m)=\pi(m)/\gcd(\pi(m),s)$, so the resulting support-prime
valuation exceeds that of $T/\gcd(T,s)$ by

$$
\max(\max(\beta_p,a_p-h_p)-u_p,0)
 -\max(\beta_p-u_p,0)
=\max(0,a_p-h_p-\max(\beta_p,u_p)).
$$

The factors outside $S$ agree. Unique prime factorization gives
the first formula. Setting every exponent except $a_{p_0}=e$
to one makes their excess valuations zero because $h_q>0$.
At $e=1$ the target excess also vanishes. Its exponent becomes
positive exactly beyond the stated threshold, and the baseline
period is positive.

The depth in this formula is that of the original Fibonacci
sequence. Neither a stride plateau nor a coupled-period plateau
identifies the depth by itself.

## 追加锚（本行以下为增补区）


## 62. Cubic towers certified by saturated base-field tests

Let $K\subseteq L$ be fields and let $\zeta\in K$ be a primitive
cube root of unity. Fix $J\in\mathbb N$, elements $a_j\in K$ and
$\beta_j\in L$ for $1\leq j\leq J$, with
$\beta_j^3=a_j$. Put

$$
K_0=K,\qquad K_m=K(\beta_1,\ldots,\beta_m)
\quad(0\leq m\leq J).
$$

For each $0\leq n<J$, let $P_n$ be a predicate on $K$. These
predicates describe tests in the base field; they are not tests
assumed to hold in an extension field.

**Theorem 62.1 (saturated noncube tests determine the tower degree).**
Suppose that for every $0\leq n<J$ the following conditions hold:

- if $P_n(a)$, then there is no $c\in K$ with $c^3=a$;
- for every $1\leq i\leq n$ and every $e\in\mathbb N$,
  $P_n(a)$ implies $P_n(a a_i^e)$;
- $P_n(a_{n+1})$ holds.

Then

$$
[K_J:K]=3^J.
$$

In particular every $a_j$ in the stated range is nonzero; this is
a consequence of the tests, since zero is a cube, and requires
no additional nonvanishing assumption. The conclusion includes
$J=0$.

Proof. The invariant is that whenever $0\leq m\leq n<J$ and
$P_n(a)$ holds, $a$ has no cube root in $K_m$. For $m=0$ this
is the first condition. Suppose the invariant is established
through $m$. Applying it to $P_m(a_{m+1})$ makes
$T^3-a_{m+1}$ irreducible over $K_m$, so adjoining
$\beta_{m+1}$ has degree three. In a degree-three extension
containing a primitive cube root of unity, cubic descent says
that a cube root of $a$ in $K_{m+1}$ would imply
$a a_{m+1}^e=c^3$ for some nonnegative exponent $e$ and
some $c\in K_m$. For $m+1\leq n$, saturation gives
$P_n(a a_{m+1}^e)$, contradicting the induction invariant
in $K_m$. This establishes the invariant at the next stage.
The fresh test therefore makes every adjoining degree exactly
three, and the degree multiplication law gives the result.

A useful choice of $P_n(a)$ is nonvanishing together with a
valuation of $a$ whose integer logarithm is not divisible by
three. Earlier radicands with valuation one leave that test
unchanged under multiplication. For the conjugate-complete
field in Theorem 55.7, the required valuation data belong to
the actual principal prime ideals of the oriented factors and
their conjugates, together with the primes above two and three.
The theorem supplies the tower-degree step after those data
are proved; it does not by itself identify that field's Galois
coordinates, Frobenius elements, or cyclotomic intersections.

## 追加锚（本行以下为增补区）

## 63. Cubic orbit independence modulo a fixed subgroup

**定理 63.1（Cubic orbit independence）。** Let $G$ be an additive
commutative group, $H$ an additive subgroup, and $J$ a nonnegative
integer. For $i\in\{0,\ldots,J-1\}$ let $P_i\in G$. Let $T:G\to G$
and $\sigma_j:G\to G$ be additive homomorphisms. Suppose every
$\sigma_j$ fixes every element of $H$, and that

$$
\begin{aligned}
\sigma_j(P_i)&=\begin{cases}T(P_i)&i=j,\\P_i&i\ne j,\end{cases}\\
\sigma_j(T(P_i))&=\begin{cases}T^2(P_i)&i=j,\\T(P_i)&i\ne j.\end{cases}
\end{aligned}
$$

Suppose also that $P_i+T(P_i)+T^2(P_i)=0$ and that $P_i$ has
infinite additive order for every $i$. Then, for all integer
coefficient families $a_i,b_i$,

$$
\sum_{i=0}^{J-1}\bigl(a_iP_i+b_iT(P_i)\bigr)\in H
\quad\Longrightarrow\quad
\forall i,\ a_i=b_i=0.
$$

The homomorphisms need not be invertible. No commutation between
$T$ and $\sigma_j$ is assumed outside the displayed orbit values.
The result includes the empty family.

Proof. Apply $\sigma_j$ to the given sum. All terms with $i\ne j$
are fixed, and the sum is fixed because it belongs to $H$.
Cancellation gives

$$
a_j(TP_j-P_j)+b_j(T^2P_j-TP_j)=0.
$$

Use the cubic trace relation and write $x=a_j+b_j$ and
$y=2b_j-a_j$. The preceding equality implies
$xP_j+yTP_j=0$. Apply $T$ and subtract $y$ times the trace
relation to obtain $-yP_j+(x-y)TP_j=0$. Eliminating $TP_j$ gives

$$
\bigl(x(x-y)+y^2\bigr)P_j=0.
$$

Infinite additive order forces $x(x-y)+y^2=0$. The identity

$$
2\bigl(x(x-y)+y^2\bigr)=x^2+y^2+(x-y)^2
$$

then forces $x=y=0$. Hence $a_j+b_j=2b_j-a_j=0$, so
$a_j=b_j=0$. This works for every $j$.

For GIR4, $H$ is the image of the base-field point group in the
common extension field, and $T$ is the cubic coordinate rotation.
The displayed action, cubic trace and infinite-order hypotheses
must be established for the actual fixed-curve points. The
abstract theorem alone does not establish those arithmetic
hypotheses or a numerical rank bound. It uses cancellation,
additive functoriality and the positive Eisenstein quadratic norm;
it is a synthesis of these elementary structures.

## 追加锚（本行以下为增补区）

## 64. Prime-power quotient traces and the tame different

The two statements below are licensed ports of Tau Ceti's quotient-trace
and different results at immutable revision
`33c2099c678ea391f7ea3e0ddaf945a76a625e5d`, as identified in
Library/ArithUnits/tauceti2026tamedifferent.md. Their scope is general
Dedekind-domain algebra; identifying the actual golden-block inertia
and converting the different into the discriminants in Theorem 56.1
requires separate arithmetic bridges.

**定理 64.1（Prime-power quotient trace）。** Let $A$ and $B$ be
commutative rings, with $B$ a module-finite $A$-algebra and a Dedekind
domain. Let $p$ and $P$ be maximal ideals of $A$ and $B$, with
$P\ne0$. Let $n\geq0$ be an integer. Suppose $B/P^n$ and $B/P$ carry
$A/p$-algebra structures whose scalar actions extend their natural
$A$-actions. For every $z\in B$,

$$
\operatorname{Tr}_{(B/P^n)/(A/p)}(\bar z)
=n\operatorname{Tr}_{(B/P)/(A/p)}(\bar z).
$$

The trace is the trace of multiplication on the finite-dimensional
residue-field algebra; the formula includes the zero algebra at $n=0$.
No separability of the residue extension is needed.

Proof. Choose $a\in P^n\setminus P^{n+1}$. Multiplication by $a$ and
the quotient projection give an exact sequence

$$
0\longrightarrow B/P\longrightarrow B/P^{n+1}
\longrightarrow B/P^n\longrightarrow0.
$$

The first map is injective because $ax\in P^{n+1}$ with
$a\notin P^{n+1}$ forces $x\in P$. Exactness in the middle follows
from $P^n/P^{n+1}$ being generated by the class of $a$; the
Dedekind ideal calculation supplies the required lift. Multiplication
by $z$ preserves this sequence. Split it over $A/p$ and conjugate
the multiplication operator into two diagonal blocks. The diagonal
blocks are multiplication by $\bar z$ on $B/P$ and $B/P^n$;
the off-diagonal block has zero trace. This gives the trace recurrence.
Induction starting from the zero quotient proves the formula.

**定理 64.2（Different divisibility at a coprime prime power）。**
Let $A$ and $B$ be Dedekind domains, with $B$ a module-finite,
torsion-free $A$-algebra and $\operatorname{Frac}(B)$ separable over
$\operatorname{Frac}(A)$. Let $p\ne0$ be a maximal ideal of $A$,
let $P$ be a maximal ideal of $B$ lying over $p$, and let $e\geq0$.
Suppose an ideal $Q$ of $B$ satisfies

$$
pB=P^eQ,\qquad P^e+Q=B.
$$

Then, writing $\mathfrak D_{B/A}$ for the different ideal,

$$
P^e\mid\mathfrak D_{B/A}
\quad\Longleftrightarrow\quad
(B/P)/(A/p)\text{ is inseparable}
\ \lor\ e\cdot1_{A/p}=0.
$$

The residue algebra structures are the natural structures induced by
the lying-over relation. Separability on the right refers to the
residue-field extension, distinct from fraction-field separability.

Proof. The trace-dual definition of the different and the fractional
ideal identity $I^{-1}=Q/(pB)$, for $IQ=pB$, give

$$
I\mid\mathfrak D_{B/A}
\quad\Longleftrightarrow\quad
\operatorname{Tr}_{B/A}(Q)\subseteq p.
$$

Apply this with $I=P^e$. The Chinese remainder isomorphism
$B/pB\simeq(B/P^e)\times(B/Q)$ and Theorem 64.1 show that for
$x\in Q$ the reduction of its integral trace is
$e\operatorname{Tr}_{(B/P)/(A/p)}(\bar x)$. If the residue extension
is inseparable, its trace vanishes; if $e$ vanishes in $A/p$, the
same product vanishes. Conversely, in the separable case choose a
residue with nonzero trace. Chinese remaindering lifts it to an
element of $Q$ with the same residue modulo $P$. When $e$ is nonzero
in $A/p$, this element has nonzero reduced integral trace, excluding
$P^e\mid\mathfrak D_{B/A}$.

For the ramification index $e=e(P/p)$, the pinned universal lower
bound $P^{e-1}\mid\mathfrak D_{B/A}$ and the criterion above give
different exponent $e-1$ whenever the residue extension is separable
and its characteristic does not divide $e$. This is an application
of the two bounds, with no additional theorem declaration.

For GIR3, the remaining inputs are the actual inertia order three
at primes dividing the cubefree block radical, absence of other
ramification away from three, the actual comparison of completions
above three with the cubic cyclotomic base, and its ramification
index two. The first discriminant also needs the inertia action on
the embeddings of the non-Galois positive-root field, or an equivalent
tower calculation. The global different norm and discriminant
identity then supply the two exponents in Theorem 56.1. These actual
arithmetic inputs are not assumptions hidden in Theorems 64.1–64.2.

## 追加锚（本行以下为增补区）

## 65. Quadratic height constructions and arithmetic transport

The height normalization in this section is the absolute logarithmic
height attached to admissible absolute values. On an affine Weierstrass
point group, write $x(P)$ for its nonzero homogeneous two-coordinate
representative, including the point at infinity, and set
$h(P)=h(x(P))$. The coordinate convention is the one used by the
homogeneous addition-and-subtraction map in Mathlib. The following
constructions supply the height pairing used in GIR5; they do not
identify a basis of the entire Mordell–Weil group.

**定理 65.1（Symmetric-square addition and subtraction）。**
Let $F$ be any field and $W$ an affine Weierstrass curve over $F$.
For its nonsingular point group and any $P,Q$, let $s(P,Q)$ be the
three homogeneous coefficients of the unordered pair of their
projective $x$-coordinates. There is $t\in F^\times$ such that

$$
t\,s(P+Q,P-Q)=\operatorname{addSubMap}_W(s(P,Q)).
$$

The assertion includes points at infinity, inverse points and
doubling, in every characteristic. The map on the right is the
homogeneous quadratic addition-and-subtraction map of the Weierstrass
coefficients.

Proof. Infinity and inverse-point cases reduce to their homogeneous
representatives. For distinct finite points, substitute the affine
addition formula and clear the two nonzero coordinate differences.
For doubling, the duplication denominator and numerator cannot both
vanish at a nonsingular point: their simultaneous vanishing, together
with the curve equation, forces both partial derivatives to vanish.
Use the nonzero one as the projective scale. Substitution then gives
the same three-coordinate identity, including characteristic two.

**定理 65.2（Canonical-height construction with its full comparison）。**
Let $F$ carry admissible absolute values and let $W/F$ be elliptic.
Define

$$
\widehat h(P)=\lim_{n\to\infty}\frac{h(2^nP)}{2\,4^n}.
$$

For every $P$ the displayed sequence converges. There is one real
constant $D$, depending on the curve and height system, such that
for all $P$,

$$
\left|\widehat h(P)-\tfrac12 h(P)\right|\le D.
$$

For all $P,Q$ the same construction satisfies

$$
\widehat h(P+Q)+\widehat h(P-Q)
=2\bigl(\widehat h(P)+\widehat h(Q)\bigr).
$$

No Northcott hypothesis is needed for these assertions.

Proof. Projective height is invariant under the nonzero scale in
Theorem 65.1. The symmetric-square height differs from $h(P)+h(Q)$
by a uniformly bounded amount, and the homogeneous quadratic
addition-and-subtraction map changes height by twice the input
height up to a uniformly bounded amount. Hence

$$
\left|h(P+Q)+h(P-Q)-2(h(P)+h(Q))\right|\le C
$$

with a constant uniform in both points. Put $Q=P$ to bound the
successive differences of $h(2^nP)/(2\,4^n)$ by a summable geometric
sequence. Completeness gives convergence, and summing this bound
gives the uniform comparison with $h(P)/2$. Apply the full two-point
bound to $2^nP,2^nQ$, divide by $2\,4^n$, and pass to the limit;
its error tends to zero and gives the exact parallelogram law.

**定理 65.3（Quadratic maps from a parallelogram law）。**
Let $M,N$ be additive commutative groups, with injective doubling on
$N$. If $f:M\to N$ satisfies

$$
f(x+y)+f(x-y)=2f(x)+2f(y)\qquad(x,y\in M),
$$

then there is a quadratic map $Q:M\to N$ over $\mathbb Z$ whose
underlying function is $f$. Its companion bilinear map is
$b(x,y)=f(x+y)-f(x)-f(y)$. In particular, the construction supplies
both integer quadratic scaling and biadditivity of $b$.

Proof. Substitution at zero and cancellation of doubling give
$f(0)=0$; substitution at $0,x$ gives evenness. The recurrence at
$nx,x$ gives $f(nx)=n^2f(x)$ by two-step induction, and evenness
extends it to integers. Applying the parallelogram identity to
three points and cancelling doubling gives the three-variable
polarization identity. That identity proves additivity of $b$ in
each argument, so $f$ and $b$ define the required quadratic map.
Injective doubling is essential: on $\mathbb Z/2\mathbb Z$ the
constant function one satisfies the displayed identity but does not
vanish at zero.

**定理 65.4（Galois invariance of scalar absolute height）。**
Let $K$ be a number field and $\sigma$ a $\mathbb Q$-automorphism of
$K$. For every $x\in K$, its absolute multiplicative height satisfies

$$
H(\sigma(x))=H(x).
$$

Proof. Write $x=a/b$ with integral $a,b$ and $b\ne0$. The automorphism
of the ring of integers transports the ideal generated by $a,b$;
the quotient-ring isomorphism preserves its absolute norm and thus
the finite-place contribution to the homogeneous pair height.
At infinite places the automorphism permutes the places and preserves
their real or complex multiplicities. Reindex that product and use
the ideal-norm formula for the finite-place product. The homogeneous
pair height is unchanged, which gives the stated scalar identity.

**定理 65.5（Group transport under an admissible variable change）。**
Let $F$ be a field, $W/F$ an elliptic Weierstrass curve and $C$ an
admissible change of Weierstrass variables, with nonzero scale.
The coordinate change induces an additive equivalence

$$
(C\mathbin{\cdot}W)(F)\simeq W(F)
$$

between their nonsingular point groups, including infinity.

Proof. Substitute the coordinate change in the curve equation and
its partial derivatives to preserve nonsingularity. The inverse
variable change gives the inverse point map. Substitution in the
negation, distinct-point addition and doubling formulas shows that
the point map preserves the group law. Thus the coordinate
bijection is an additive equivalence.

Theorem 65.1 and the naïve-height definition are adapted from Mathlib
revision `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`. The canonical-height
construction, quadratic-map construction and point variable-change
construction are adapted from TauCeti revision
`934db6ae0034643ffe7b5180242f9ec4c00a56ae`. The scalar-height transport
proof combines the ideal-norm and infinite-place results of the
repository's pinned Mathlib. These are applications and compatibility
adaptations of existing height theory; they are not an originality
claim. Immutable source paths, copyright statements, full license
text and the condition for replacing a port by a pinned upstream
declaration are recorded in `Library/ArithUnits/tauceti2026canonicalheight.md`.

## 追加锚（本行以下为增补区）

## 66. Persistent noncube tests and the complete earlier-support field

Use the fields, radicands and specified cube roots of Section 62.
The predicates in the following assertion are tests on the base field,
including a terminal predicate $P_J$.

**Theorem 66.1 (terminal noncube persistence).**
Suppose that for every $0\le n\le J$, $P_n(a)$ excludes a cube
root of $a$ in $K$, and is preserved under multiplication by
$a_i^e$ for $1\le i\le n$ and $e\in\mathbb N$. Suppose also that
$P_n(a_{n+1})$ holds for $0\le n<J$. Then

$$
[K_J:K]=3^J,\qquad
P_J(a)\Longrightarrow \forall x\in K_J,\quad x^3\ne a.
$$

This includes the empty tower. Theorem 62.1 requires no terminal
predicate: apply this assertion to
$Q_n(a)=(n<J)\land P_n(a)$, whose terminal predicate is empty,
and take its degree conclusion.

Proof. Induct on $m$ with the invariant that for
$0\le m\le n\le J$, $P_n(a)$ excludes a cube root in $K_m$.
The base case is the base-field test. The fresh predicate proves
that the next cubic polynomial is irreducible. Cubic descent from
a hypothetical cube root at the next stage produces a cube root
in the preceding stage of $a a_{m+1}^e$. Saturation puts this
element in the same predicate and the preceding invariant
excludes it. Thus the invariant persists through $m=J$.
Multiplication of the degree-three stage degrees gives $3^J$.

**Theorem 66.2 (complete earlier-support degree and unit obstruction).**
Let $j\in\mathbb N$, $E=\mathbb Q(\zeta_3)$ and
$\Omega$ be an algebraic closure of $E$. Put

$$
B_i=L_{3^i}^{\,2}+3,\qquad
S_j=\bigcup_{1\le i<j}\{p:p\text{ is a rational prime dividing }B_i\}.
$$

There is a single choice of primary Eisenstein factors
$\pi_p$ for $p\in S_j$ such that $(\pi_p)$ is prime,
$N(\pi_p)=p$, $\pi_p\equiv1\pmod3$,
$p\equiv1\pmod3$ and $\pi_p$ is coprime to its conjugate.
Factors at distinct rational primes are coprime in all four
primary/conjugate combinations. This same choice satisfies

$$
\eta_i=\prod_{p\mid B_i}\pi_p^{\delta_p}
\quad(1\le i<j),\qquad
\delta_p=v_p(F_{\rho(p)}).
$$

Choose cube roots in $\Omega$ of each $\pi_p$, each
$\overline\pi_p$, and of $2$ and $3$. For the field $M_j$
generated over $E$ by these same roots,

$$
[M_j:E]=3^{\,2|S_j|+2},\qquad
\forall x\in M_j,\quad x^3\ne\zeta_3.
$$

The support is the earlier range $1\le i<j$. For $j\le1$
this support is empty and the two rational radicands remain.

Proof. Pairwise coprimality of the blocks makes their prime
supports disjoint, so the primary factorizations can be selected
consistently. The principal prime-ideal valuations for the primary
factors and their conjugates, and the valuations above $2$ and
$3$, give a diagonal matrix: each corresponding radicand has
integer valuation not divisible by three, while every other
radicand has valuation zero. All these valuations vanish on
$\zeta_3$. Moreover $\zeta_3$ is not a cube in $E$: a cube
root would be a primitive ninth root of unity, contrary to the
cyclotomic root-of-unity bound in $E$.
For the successive saturation tests, include the fresh radicand
and the multiplicative span of $\zeta_3$ with powers of all
radicands. A cube equation in the latter span would force every
radicand exponent to be divisible by three, by the diagonal
valuations. Removing their cubes would make $\zeta_3$ a cube
in $E$. Theorem 66.1 therefore gives both the full degree and
the terminal unit obstruction in the same generated field.

The persistence argument extends the saturated-test construction
of Section 62. The actual support and oriented products use the
primary factorization and block coprimality results already stated
in this volume. The unit obstruction supplies a condition needed
for the cyclotomic intersection argument of Theorem 55.8;
the intersection, its Frobenius identification and its rational-prime
density require their own proofs.

## 追加锚（本行以下为增补区）

## 67. Finite diagonal valuations and a retained noncube

**Theorem 67.1 (finite valuation degree and unit obstruction).**
Let $K$ be a field containing a primitive cube root of unity,
$L/K$ a field extension and $I$ a finite set. For each $i\in I$,
choose $a_i\in K\setminus\{0\}$ and $b_i\in L$ with $b_i^3=a_i$,
where base-field elements are identified with their images in $L$.
Choose multiplicative valuations $\nu_i$ with values in the
zero-extended multiplicative group of integers. Write
$v_i(x)=\log(\nu_i(x))$ for $x\ne0$, and suppose

$$
3\nmid v_i(a_i),\qquad \nu_i(a_k)=1\quad(i\ne k).
$$

Let $u\in K\setminus\{0\}$ be a noncube such that $v_i(u)=0$
for every $i\in I$. For the field $M=K(b_i:i\in I)$,

$$
[M:K]=3^{|I|},\qquad \forall x\in M,\quad x^3\ne u.
$$

The statement includes $I=\varnothing$, when $M=K$.

Proof. Order the finite set and construct the radical tower of
Section 66. At every nonterminal stage, the valuation of the next
radicand has logarithm not divisible by three and vanishes on all
preceding radicands. It therefore excludes a cube and remains
unchanged after multiplication by powers of preceding radicands.
For the terminal test, use the elements
$u\prod_{i\in I}a_i^{e_i}$ with $e_i\in\mathbb N$.
If such an element were $c^3$ in $K$, applying $v_i$ gives
$3v_i(c)=e_i v_i(a_i)$. Since three does not divide $v_i(a_i)$,
it divides every $e_i$. Dividing $c$ by
$\prod_i a_i^{e_i/3}$ would then give a cube root of $u$ in $K$,
contrary to the hypothesis. Multiplication by any radicand power
preserves this terminal set by increasing the corresponding
exponent. Theorem 66.1 now gives the full degree and the noncube
obstruction in the same generated field.

The actual valuations and unit in Theorem 66.2 satisfy these
conditions. This assertion does not identify any cyclotomic
intersection or prime-density event.

## 追加锚（本行以下为增补区）


## 68. The actual complete radical and cyclotomic intersection

**Theorem 68.1 (complete roots and the actual cyclotomic intersection).**
For every $j\in\mathbb N$, let $E=\mathbb Q(\zeta_3)$ and let
$\Omega$ be an algebraic closure of $E$. Put $m_j=80\cdot3^{j+2}$
and let $S_j$ be the earlier support of Theorem 66.2. There are
primary factors $\pi_p$ and cube roots $r_v\in\Omega$, with

$$
I_j=(S_j\times\{0,1\})\sqcup\{0,1\},
$$

satisfying all the primary-prime, norm, congruence, pairwise
coprimality and oriented-product conditions of Theorem 66.2.
The roots at $(p,0)$ and $(p,1)$ cube to $\pi_p$ and
$\overline{\pi_p}$, respectively; the last two roots cube to
$2$ and $3$. For the field $M_j=E(r_v:v\in I_j)$,

$$
[M_j:E]=3^{2|S_j|+2},\qquad
\forall x\in M_j,\quad x^3\ne\zeta_3.
$$

Moreover $M_j/E$ is Galois, and there is a group isomorphism

$$
e:\operatorname{Gal}(M_j/E)\longrightarrow
(\mathbb Z/3\mathbb Z)^{I_j}
$$

such that $\sigma(r_v)=\zeta_3^{e(\sigma)_v}r_v$ for every
$\sigma$ and every $v$. There is a primitive $m_j$-th root
$\zeta\in\Omega$ for which, in this same ambient field,

$$
M_j\cap E(\zeta)=E.
$$

The same primary factors and the same root family supply every
condition and the intersection. The statement includes $j\le1$,
when the earlier support is empty and the two rational radicands
remain.

Proof. Take the complete root family and its retained unit
obstruction from Theorem 66.2; Kummer theory gives its coordinate
Galois action. Choose a primitive $m_j$-th root in $\Omega$ and
write $C=E(\zeta)$. This is the actual rational $m_j$-th
cyclotomic field, because three divides $m_j$ and $C$ contains
the embedded third cyclotomic field. Write
$Q=E(\zeta^{m_j/9})\subseteq C$. Its relative degree over $E$
is three, and it contains a cube root of the distinguished
$\zeta_3$; primitive-root comparison supplies this assertion
without assuming compatible choices of primitive roots.

The Galois group of $C/E$ is the kernel of restriction of
$(\mathbb Z/m_j\mathbb Z)^\times$ to the third roots of unity.
The Chinese remainder decomposition at $80$ and $3^{j+2}$
shows that the subgroup of cubes has index three. Every
nontrivial quotient of exponent three therefore has order three
and has this same kernel. Now $T=M_j\cap C$ is Galois over
$E$, and its Galois group has exponent three as a quotient of
the coordinate group of $M_j/E$. If $T\ne E$, the restriction
maps onto $\operatorname{Gal}(T/E)$ and onto
$\operatorname{Gal}(Q/E)$ have the same kernel. Galois
correspondence gives $T=Q$. The cube root of $\zeta_3$ in
$Q\subseteq M_j$ contradicts the retained unit obstruction.
Thus $T=E$.

The assertion supplies the intersection used in Theorem 55.8.
It does not identify a Frobenius event, compute a prime density,
or produce a prime in the finite support of the current block.

## 追加锚（本行以下为增补区）


## 69. Local and Galois structure of the actual common cubic fields

For each integer $j\geq1$, retain the actual Lucas block
$B_j=L_{3^j}^2+3$ and its designated positive real cube root
$\theta_j=B_j^{1/3}$. Put $\omega=\exp(2\pi i/3)$ and
$E=\mathbb Q(\omega)$. For every integer $J\geq0$, define the
actual subfields of $\mathbb C$

$$
F_J=\mathbb Q(\theta_1,\ldots,\theta_J),\qquad
N_J=E(\theta_1,\ldots,\theta_J),
$$

with $F_0=\mathbb Q$ and $N_0=E$. Write

$$
c_j=\prod_{p\mid B_j}p^{\lfloor v_p(B_j)/3\rfloor},\qquad
 d_j=B_j/c_j^3,\qquad
 R_J=\prod_{j=1}^J\operatorname{rad}(d_j),\qquad R_0=1.
$$

Thus $c_j$ is the largest positive integer whose cube divides
$B_j$; it is not the ordinary real cube root rounded down.
Here $\operatorname{rad}(a)$ is the product of the distinct
rational prime divisors of the positive integer $a$.
For a number field $K$, write $\mathcal O_K$ for its integer ring.
For primes $\mathfrak P\mid\mathfrak p$, write
$e(\mathfrak P/\mathfrak p)$ and $f(\mathfrak P/\mathfrak p)$
for the ramification index and residue degree. All primes below
are nonzero prime ideals. The inertia group at $\mathfrak P$
is the subgroup acting trivially on its residue field.
These assertions give separate local and group statements used
by the discriminant calculation of Theorem 56.1.

**Theorem 69.1 (compatible completion collapse at three).**
For every $J\geq0$, $E$ and $N_J$ are number fields. For every
prime $\mathfrak p$ of $\mathcal O_E$ above $(3)$ and every
prime $\mathfrak P$ of $\mathcal O_{N_J}$ above $\mathfrak p$,
there is a continuous surjective unital ring homomorphism

$$
\iota_{\mathfrak p,\mathfrak P}:E_{\mathfrak p}\longrightarrow
(N_J)_{\mathfrak P}
$$

between their adic completions, such that for every $x\in E$
its value on the image of $x$ equals the image of $x$ through
$E\hookrightarrow N_J\hookrightarrow(N_J)_{\mathfrak P}$.

Proof. Each actual block is congruent to one modulo nine.
The three-adic Hensel construction gives a cube root of each
block in the completion of the base. Embed the generated tower
into that completion using those roots, extend the compatible
base embedding to the specified tower completion, and identify
the closure of the base with the entire completion.

**Theorem 69.2 (relative ramification at three with its completion map).**
For every $J\geq0$, $E$ and $N_J$ are number fields. For every
$\mathfrak p\mid(3)$ in $\mathcal O_E$ and every
$\mathfrak P\mid\mathfrak p$ in $\mathcal O_{N_J}$,
there is a continuous surjective ring homomorphism
$\iota_{\mathfrak p,\mathfrak P}:E_{\mathfrak p}\to(N_J)_{\mathfrak P}$
agreeing with both embeddings of every $x\in E$, and

$$
e(\mathfrak P/\mathfrak p)=1.
$$

Proof. The compatible completion map transports the base
valuation to the tower valuation. Surjectivity identifies their
value groups, so the relative ramification index is one.

**Theorem 69.3 (relative residue degree at three).**
For every $J\geq0$, $E$ and $N_J$ are number fields. For every
$\mathfrak p\mid(3)$ in $\mathcal O_E$ and every
$\mathfrak P\mid\mathfrak p$ in $\mathcal O_{N_J}$,

$$
f(\mathfrak P/\mathfrak p)=1.
$$

Proof. Approximate an integral element of the tower completion
by an element of the dense image of the base, close enough to
preserve its residue. The compatible surjective completion map
therefore makes the base residue-field map surjective.

**Theorem 69.4 (rational Galois action and actual conjugation).**
For every $J\geq0$, $N_J/\mathbb Q$ is Galois. There is an
automorphism $c\in\operatorname{Gal}(N_J/\mathbb Q)$ satisfying
$c(x)=\overline x$ in the designated complex embedding for all
$x\in N_J$, with $c^2=1$ and $c\ne1$. For every
$\sigma\in\operatorname{Gal}(N_J/E)$, regard $\sigma$ also as a
rational automorphism. Then

$$
c\sigma c=\sigma^{-1}.
$$

Proof. The field contains every conjugate of each radical and
of $\omega$, so it is a splitting field. Conjugation fixes the
positive roots and inverts $\omega$. The same-root cubic
coordinate action consequently changes every exponent to its
negative under conjugation; the generators determine the whole
automorphism.

**Theorem 69.5 (the conjugation subgroup is self-normalizing).**
For every $J\geq0$, there is an actual conjugation automorphism
$c\in\operatorname{Gal}(N_J/\mathbb Q)$ with
$c(x)=\overline x$ for all $x\in N_J$, $c^2=1$ and $c\ne1$,
such that

$$
N_{\operatorname{Gal}(N_J/\mathbb Q)}(\langle c\rangle)
=\langle c\rangle.
$$

Proof. An automorphism normalizing the nontrivial order-two
subgroup commutes with conjugation. Its radical-coordinate
part equals its inverse. A group of exponent three has no
nonidentity element satisfying that equality, leaving precisely
the two elements of the conjugation subgroup.

**Theorem 69.6 (primes above three and the unique fixed prime).**
For every $J\geq0$, $N_J$ is a number field and there is an
automorphism $c$ acting as complex conjugation on every element.
There are exactly $3^J$ primes of $\mathcal O_{N_J}$ above
$(3)$. Every such prime $\mathfrak P$ satisfies

$$
e(\mathfrak P/(3))=2,\qquad f(\mathfrak P/(3))=1.
$$

Exactly one of these primes is fixed by $c$.

Proof. Combine relative completion collapse with the quadratic
cyclotomic ramification at three. Galois transitivity and the
fundamental identity give the number of primes. The decomposition
subgroup has order two; self-normalization of conjugation makes
its action have exactly one fixed prime.

**Theorem 69.7 (inertia fixes all unit radical coordinates).**
For every $J\geq0$, every rational prime $p\ne3$, every prime
$\mathfrak P$ of $\mathcal O_{N_J}$ above $(p)$ and every
$\sigma$ in its inertia group, $\sigma$ fixes $\omega$.
For every integer $j$ with $1\leq j\leq J$, if $p\nmid d_j$,
then $\sigma$ fixes the designated element $\theta_j$ of $N_J$.

Proof. Distinct cubic roots of unity have distinct reductions
away from three. Divide each radical by its integral cube factor;
when $p\nmid d_j$ the result is a unit. An inertia automorphism
cannot multiply that unit by a nontrivial cubic root of unity,
because its residue must remain fixed.

**Theorem 69.8 (inertia has at most three elements at a block prime).**
For every $J\geq0$, every $1\leq j\leq J$, every rational
prime $p\ne3$ dividing $B_j$, and every prime
$\mathfrak P$ of $\mathcal O_{N_J}$ above $(p)$,

$$
\#I_{\mathfrak P}(N_J/\mathbb Q)\leq3.
$$

Proof. The actual block supports are disjoint. Inertia fixes the
base and every other radical coordinate. The image of the one
remaining radical can have only its three cubic conjugates, and
those generator images determine the automorphism.

**Theorem 69.9 (rational degrees and signature of the positive-root field).**
For every $J\geq0$,

$$
[N_J:\mathbb Q]=2\cdot3^J,\qquad [F_J:\mathbb Q]=3^J.
$$

The field $F_J$ is a number field with exactly one real place
and $(3^J-1)/2$ complex places. The assertion includes
$F_0=\mathbb Q$ with signature $(1,0)$.

Proof. The cubic tower degree over $E$ gives the first degree.
The positive-root field lies in the real numbers and has trivial
intersection with $E$ over $\mathbb Q$, giving the second.
A real embedding must select the unique real conjugate of each
radical. Thus precisely one embedding is real; the others pair
under conjugation.

**Theorem 69.10 (semidirect product with coordinate inversion).**
For every $J\geq0$, there exists an action
$\phi:C_2\to\operatorname{Aut}(C_3^J)$ whose nonidentity element
sends each vector $x$ to $x^{-1}$, and a group isomorphism

$$
C_3^J\rtimes_\phi C_2
\simeq\operatorname{Gal}(N_J/\mathbb Q).
$$

Here $C_3^J$ is the product of $J$ cyclic groups, with the empty
product equal to the trivial group.

Proof. Restrict rational automorphisms to the actual cyclotomic
base. The kernel is the cubic-coordinate group and conjugation
splits the order-two quotient. Its action on that kernel is
inversion. Transport the split extension along the actual
coordinate and cyclic-quotient equivalences.

**Theorem 69.11 (a nonzero cubic valuation forces ramification).**
For every $J\geq0$, every $1\leq j\leq J$, every rational
prime $p$ for which $3\nmid v_p(B_j)$, and every prime
$\mathfrak P$ of $\mathcal O_{N_J}$ above $(p)$,

$$
3\mid e(\mathfrak P/(p)).
$$

Proof. The valuation of the actual root equation
$\theta_j^3=B_j$ equals the ramification index times the base
valuation of $B_j$. Its left side is divisible by three, while
the given base valuation is not.

**Theorem 69.12 (no ramification outside the cubefree support).**
For every $J\geq0$, every rational prime $p\ne3$ satisfying
$3\mid v_p(B_j)$ for every $1\leq j\leq J$, and every prime
$\mathfrak P$ of $\mathcal O_{N_J}$ above $(p)$,

$$
e(\mathfrak P/(p))=1.
$$

Proof. Every normalized radical is a unit at this prime.
Inertia fixes the base and all radical coordinates, hence is
trivial. The Galois ramification-inertia identity gives the
ramification index.

**Theorem 69.13 (sixth power of the absolute different).**
For every $J\geq0$, let $\mathfrak D_J$ be the different ideal
of $\mathcal O_{N_J}$ over $\mathbb Z$. As ideals of
$\mathcal O_{N_J}$,

$$
\mathfrak D_J^6=(3)^3(R_J)^4.
$$

Proof. At primes over three, the absolute ramification index is
two and the tame different multiplicity is one. At primes
in the cubefree support, the index is three and the different
multiplicity is two. Every other prime is unramified and its
different multiplicity is zero. Unique factorization of ideals
then gives the displayed equality at every prime.

## 追加锚（本行以下为增补区）

## 70. Conditional original-depth support descent

**Theorem 70.1 (conditional index and squarefree-kernel support).**
Let $S$ be a finite set of rational primes greater than five, let
$H(S)$ be its Fibonacci-rank closure from Section 5, and let $n\geq1$.
Assume that for every prime $\ell>5$ dividing $n$ there is a prime
$p\mid F_\ell$ with odd $v_p(F_\ell)$. Also assume that every prime
$p>5$ satisfying

$$
p\mid F_n,\qquad p\nmid n,\qquad
v_p(F_{\rho(p)})\text{ is odd}
$$

belongs to $S$. Then

$$
\operatorname{Supp}(n)\subseteq H(S),\qquad
\prod_{\substack{p\mid F_n\\v_p(F_n)\text{ odd}}}p
\ \bigm|\ \prod_{p\in H(S)}p,
$$

where the product on the left ranges over the distinct prime divisors
of $F_n$ with odd valuation.

Proof. If some index prime lies outside $H(S)$, choose the largest
such prime $\ell$. Since $2,3,5\in H(S)$, it exceeds five. The first
assumption gives an odd-exponent prime $p\mid F_\ell$. Its exact
Fibonacci entry rank is $\ell$, and the rank bound together with
parity gives $p>\ell$. If $p\mid n$, maximality puts $p$ in $H(S)$;
rank closure would then put $\ell$ in $H(S)$, a contradiction. Thus
$p\nmid n$. Its odd valuation in $F_\ell=F_{\rho(p)}$ and the second
assumption put $p$ in $S$, again contradicting rank closure. This
proves the index-support statement.

For a prime with odd valuation in $F_n$, the primes at most five
already belong to $H(S)$. A larger prime dividing $n$ belongs there
by the index-support statement. For a larger prime not dividing $n$,
the original prime-to-index valuation identity gives
$v_p(F_n)=v_p(F_{\rho(p)})$, so the second assumption puts it in $S$.
Every prime in the squarefree-kernel product therefore belongs to
$H(S)$, proving the divisibility of products.

The prime-index assumption is explicit. For primes $\ell>5$,
Theorem 51.1 and prime factorization of the positive nonsquare
$F_\ell$ supply it. The conclusion uses the actual original-depth
valuation, including primes that divide the chosen index.

## 追加锚（本行以下为增补区）

## 71. Cubic coordinate actions, elliptic independence and height blocks

**Theorem 71.1 (coordinate rotations from the Galois degree).**
Let $L/K$ be a finite Galois extension, let $J\geq0$, and let
$\zeta\in K$ be a primitive cube root of unity. Suppose nonzero
$\beta_1,\ldots,\beta_J\in L$ have cubes in $K$, generate $L$ over
$K$, and satisfy $[L:K]=3^J$. For each $j$ there is a
$K$-automorphism sending $\beta_j$ to $\zeta\beta_j$ and fixing
every other $\beta_i$.

Proof. Each automorphism determines its vector of cubic rotations.
The generator assumption makes this map to $\{0,1,2\}^J$
injective. The Galois degree makes the two finite cardinalities
equal, so the map is surjective. Choose the vector supported at $j$.

**Theorem 71.2 (Galois structure and generators of the actual complex tower).**
For every $J\geq0$, the extension $N_J/E$ of Section 56 is Galois
and is generated by elements whose images in $\mathbb C$ are
the chosen positive cube roots $\theta_1,\ldots,\theta_J$.

Proof. Since $E$ contains the cube roots of unity, adjoining one
nonzero $\theta_j$ gives the splitting field of the separable
polynomial $X^3-B_j$. The finite compositum is Galois. Its
generators and its defining adjoin are exactly those of $N_J$.

**Theorem 71.3 (horizontal cubic trace on a Mordell curve).**
Let $F$ be a characteristic-zero field containing $\mathbb Q$,
let $c\in\mathbb Z$, and let $\zeta\in F$ be a primitive cube
root of unity. If $x\ne0$ and the three points below are
nonsingular on $y^2=x^3+c$ over $F$, then

$$
(x,y)+(\zeta x,y)+(\zeta^2x,y)=O.
$$

Proof. The chord through the first two distinct abscissas is
horizontal. Its third intersection has the same ordinate and
abscissa $-(x+\zeta x)=\zeta^2x$, by $1+\zeta+\zeta^2=0$.
The chord addition law gives the sum.

**Theorem 71.4 (coefficient elimination modulo a fixed subgroup).**
Let $G$ be an abelian group, $A\leq G$, and let $P_1,\ldots,P_J$
have infinite order. Let $T:G\to G$ and $s_j:G\to G$ be additive
maps, with each $s_j$ fixing $A$ pointwise. Suppose
$P_i+TP_i+T^2P_i=0$. Suppose $s_j$ fixes $P_i,TP_i$ when
$i\ne j$, and sends $P_j,TP_j$ to $TP_j,T^2P_j$, respectively.
For integers $a_i,b_i$, the relation

$$
\sum_{i=1}^J(a_iP_i+b_iTP_i)\in A
$$

forces all $a_i=b_i=0$.

Proof. Applying $s_j-1$ and using the trace gives
$uP_j+vTP_j=0$, with $u=a_j+b_j$ and $v=2b_j-a_j$.
Apply $T$ and eliminate $TP_j$ to get
$(u^2-uv+v^2)P_j=0$. Infinite order forces this positive
quadratic norm to vanish, so $u=v=0$ and $a_j=b_j=0$.

**Theorem 71.5 (Mordell families independent modulo base-field points).**
Let $L/K$ be a compatible extension of fields containing
$\mathbb Q$, with $L$ of characteristic zero. Let $c,d\in\mathbb Z$,
$d\ne0$, and suppose $\mathcal E_c:y^2=x^3+c$ is elliptic.
Fix a primitive cube root $\zeta\in L$, nonzero $\beta_i\in L$,
and integers $y_i$. Suppose the points $P_i=(d\beta_i,y_i)$ are
nonsingular and have infinite order. Suppose $K$-automorphisms
$s_j$ fix $\zeta$, rotate $\beta_j$ to $\zeta\beta_j$ and fix
the other roots. There is an additive automorphism $T$ of
$\mathcal E_c(L)$ acting by $T(x,y)=(\zeta x,y)$ such that

$$
\sum_{i=1}^J(a_iP_i+b_iTP_i)\in
\operatorname{image}\bigl(\mathcal E_c(K)\to\mathcal E_c(L)\bigr)
\quad\Longrightarrow\quad a_i=b_i=0\text{ for every }i.
$$

Proof. The variable change for $\zeta^2$ constructs $T$.
Field automorphisms fix the base-field image and commute with
this point rotation. Their coordinate actions and Theorem 71.3
give the hypotheses of Theorem 71.4 for the same family and $T$.

**Theorem 71.6 (canonical-height Gram blocks for a Mordell family).**
Let $L/K$ be a compatible extension of fields containing
$\mathbb Q$, with $L$ a number field, and suppose
$\mathcal E_c:y^2=x^3+c$, $c\in\mathbb Z$, is elliptic.
Let $T$ act by $(x,y)\mapsto(\zeta x,y)$ for a primitive cube
root $\zeta\in L$. Suppose the infinite-order points $P_i$
satisfy $P_i+TP_i+T^2P_i=O$. Suppose $K$-automorphisms $s_j$
fix $P_i,TP_i$ for $i\ne j$, and send $P_j,TP_j$ to $TP_j,T^2P_j$.
Use the absolute canonical height and its pairing normalized by

$$
\widehat h(P)=\lim_{n\to\infty}\frac{h_x([2^n]P)}{2\cdot4^n},
\qquad
\langle P,Q\rangle=
\frac{\widehat h(P+Q)-\widehat h(P)-\widehat h(Q)}2.
$$

All $H_i=\widehat h(P_i)$ are positive. Different layers are
orthogonal; the Gram matrix of the $P_i$ is $\operatorname{diag}(H_i)$.
The Gram matrix of $(P_i,TP_i)$ has diagonal blocks
$H_i\begin{pmatrix}1&-1/2\\-1/2&1\end{pmatrix}$ and determinant

$$
\left(\frac34\right)^J\prod_{i=1}^J H_i^2>0.
$$

Proof. Absolute height is invariant under field automorphisms.
Root-of-unity scaling preserves logarithmic abscissa height,
hence canonical height through the doubling limit. Apply $s_j$
and the cubic trace to the associated pairing to obtain cross-layer
orthogonality. Within one layer these identities give $-H_i/2$.
Northcott finiteness and the quadratic height law imply that
zero-height points are torsion, so infinite order gives $H_i>0$.
The determinant of each block is $3H_i^2/4$; multiply these
determinants. The empty product at $J=0$ is one.

This determinant is for the displayed subgroup; no saturation
or full Mordell--Weil regulator is asserted. These statements
supply the coordinate, independence and height relations used
in Theorems 56.2 and 56.3.

## 追加锚（本行以下为增补区）

## 73. Exact ternary valuation and signed native Lucas quotient

**Theorem 73.1 (native scaled ternary unit).**
Let $K=\mathbb Q(\sqrt5)$ and let $\phi=(1+\sqrt5)/2$ be the golden
unit in $R=\mathbb Z[\phi]$. Conjugation sends $\phi$ to
$\bar\phi=1-\phi$, and $\phi^2=\phi+1$,
$\phi\bar\phi=-1$, and $\phi^{-1}=\phi-1$.
For $z\in R$ write $\operatorname{Tr}(z)=z+\bar z$ and
$N(z)=z\bar z$. Every $z=a+b\phi$ with $a,b\in\mathbb Z$ has
$\operatorname{Tr}(z)=2a+b\in\mathbb Z$. Define the actual Lucas
sequence and its ternary layers by

$$
L_n=\operatorname{Tr}(\phi^n)\quad(n\in\mathbb N),\qquad
A_j=L_{3^j}^2+2\quad(j\in\mathbb N).
$$

For a nonzero integer $a$, let $v_3(a)$ be the largest
$e\in\mathbb N$ for which $3^e\mid a$. Then for every natural
number $j\geq1$,

$$
\begin{aligned}
v_3(A_j)&=j+1,\\
\frac{A_j}{3^{j+1}}&\equiv(-1)^j\pmod3.
\end{aligned}
$$

The quotient in the second assertion is exact integer division.

Proof. Taking traces of $\phi^0=1$ and $\phi$ gives $L_0=2$ and
$L_1=1$. Taking traces of
$\phi^{n+2}=\phi^{n+1}+\phi^n$ also gives the Lucas recurrence,
so the trace definition agrees with the sequence used in the
preceding sections.

For every positive odd $n$, put $a=\phi^n$ and $b=\bar\phi^n$.
Then $a+b=L_n$ and $ab=N(\phi^n)=(-1)^n=-1$. Consequently

$$
L_{3n}=a^3+b^3=(a+b)^3-3ab(a+b)=L_n^3+3L_n.
$$

For $k\in\mathbb N$, the index $3^k$ is positive and odd. Thus
$x_k=L_{3^k}$ satisfies $x_{k+1}=x_k(x_k^2+3)$, and the native
values $A_k=x_k^2+2$ satisfy

$$
\begin{aligned}
A_{k+1}
&=x_k^2(x_k^2+3)^2+2\\
&=(x_k^2+2)\bigl((x_k^2+2)^2-3\bigr)\\
&=A_k(A_k^2-3).
\end{aligned}
$$

Since $3^0=1$ and $L_1=1$, the initial value is $A_0=3$.
We prove by induction on every $k\in\mathbb N$ that there is an
integer $u_k$ such that

$$
A_k=3^{k+1}u_k,\qquad u_k\equiv(-1)^k\pmod3.
$$

At $k=0$, take $u_0=1$. Given such an integer $u_k$, define

$$
u_{k+1}=u_k\bigl(3(3^k)^2u_k^2-1\bigr)\in\mathbb Z.
$$

Using the derived recurrence and the induction hypothesis gives

$$
\begin{aligned}
A_{k+1}
&=3^{k+1}u_k\bigl(3^{2k+2}u_k^2-3\bigr)\\
&=3^{k+2}u_k\bigl(3(3^k)^2u_k^2-1\bigr)\\
&=3^{k+2}u_{k+1}.
\end{aligned}
$$

Modulo three, the factor in parentheses is $-1$, so

$$
u_{k+1}\equiv-u_k\equiv-(-1)^k=(-1)^{k+1}\pmod3.
$$

This completes the induction. Its first successor gives
$L_3=4$, $A_1=18$, and $u_1=2$.

For each $k$, the equality $A_k=3^{k+1}u_k$ proves
$3^{k+1}\mid A_k$ and justifies the integrality of the quotient.
Since $3^{k+1}>0$, exact integer division recovers the same integer
$A_k/3^{k+1}=u_k$, giving the signed congruence. The residue
$u_k\equiv(-1)^k\pmod3$ is nonzero, so $3\nmid u_k$.
If $3^{k+2}$ divided $A_k=3^{k+1}u_k$, cancellation of the
nonzero factor $3^{k+1}$ would force $3\mid u_k$.
As $A_k=L_{3^k}^2+2>0$, its valuation is defined and therefore
$v_3(A_k)=k+1$. Restricting these two conclusions to $j\geq1$
proves the assertions.

## 追加锚（本行以下为增补区）



## 74. Global rational reduction obstruction for a depth-three golden prime

**Definition 74.1 (global nonsingular and formal subgroups).**
For a prime Q>5, let

 E_Q: Y^2=X(X+5Q)(X-15Q).

Write G_0(Q) for the subgroup of E_Q(\mathbb Q) whose points have nonsingular reduction modulo Q on this displayed integral model, and write G_1(Q) for its subgroup reducing to the point at infinity. These are subgroups of the global rational-point group, not the entire local groups E_Q(\mathbb Q_Q).

**Theorem 74.2 (vanishing of the global nonsingular reduction image).**
Let j>=1, and suppose

 B_j=L_(3^j)^2+3=P^2 Q^3

for distinct rational primes P,Q. Then

 G_0(Q)=G_1(Q).

In particular the image of G_0(Q) in the nonsingular group of the reduced cuspidal cubic, isomorphic to the additive group F_Q, is zero.

Proof. The fixed-golden clock gives P,Q>5 and 2*3^(j+1) dividing Q-1. The quadratic constraint for this actual factorization gives Q=19 modulo 40. These are the TBN3, DCE5 and GPC1 statements in [the golden-unit-lift dossier](../../../Problems/wall-sun-sun-golden-unit-lift.md). Consequently Q=19 modulo 120 and Q>=19.

We use the full two-Selmer bound of Goto, *A study on the Selmer groups of elliptic curves with a rational 2-torsion* (2002), [Section 2 and Table 9](https://www.ma.noda.tus.ac.jp/u/tg/files/thesis.pdf), printed p49 / PDF p48. The types in that table are prime residue classes modulo 24, as specified before Table 5. Its row 5 x 19 gives s_3(-n)=1 without a Legendre-sign restriction. Here s_3(-n) is dim_F2 Sel_2 minus 2 for y^2=x(x+n)(x-3n). Taking n=5Q proves rank E_Q(\mathbb Q)<=1. This is the full two-Selmer convention, not the potentially larger sum of two-isogeny bounds.

We also use the nonsingular reduction homomorphism, the torsion-free formal kernel over Q_Q for Q>=3, prime-to-ell torsion injection at good reduction ell, and the quadratic canonical-height law; see Silverman, *The Arithmetic of Elliptic Curves*, [IV.6.3–6.4, VII.1–3 and VIII.9](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf). The height estimate needed below is proved explicitly.

**1. An actual branch gives a non-torsion formal point**

The displayed integral model has discriminant 2304*(5Q)^6. At Q>=19 its valuation is 6<12, so the model is minimal at Q. Its reduction is the cuspidal cubic Y^2=X^3, and the indicated nonsingular and formal subgroups therefore have the standard reduction meanings.

Put x=L_(3^j), f=F_(3^j), s=PQ. Since 3^j is odd,

 x^2+3=Qs^2,
 x^2+4=5f^2.

The point

 R=(5Q(x^2+3), 25Q^2 x s f)

lies on E_Q: its three factors are 5Q(x^2+3), 5Q(x^2+4), and 5Q*x^2. Their product equals the displayed Y-coordinate squared.

Let T=(0,0), the rational point of order 2. The 2-torsion translation formula on Y^2=X^3-10QX^2-75Q^2X is

 X(R+T)=(-75Q^2)/X(R).

Thus S=R+T has

 X(S)=-15Q/B_j=-15/(P^2 Q^2).

In particular v_Q(X(S))=-2, so S is a nonzero point of the formal kernel G_1(Q). The formal group is torsion-free for Q>=3, hence S is non-torsion. The rank bound above therefore gives rank E_Q(\mathbb Q)=1.

**2. The global nonsingular subgroup is infinite cyclic**

G_0(Q) is a subgroup of the finitely generated rank-one group E_Q(\mathbb Q), and it contains S. It has rank 1.

It has no torsion. Indeed, a torsion point in G_0(Q) injects into the additive reduction group F_Q because the formal kernel is torsion-free, so its order divides Q. But E_Q has good reduction at 7: Q=19 mod 120 ensures Q is not 7, and its discriminant is 2304*(5Q)^6, supported only at 2,3,5,Q. The curve y^2=x(x+1)(x-3) has 8 points over F7, and all its nonzero quadratic twists also have8 points (trace zero; equivalently a seven-residue count). Thus #E_Q(F7)=8. Prime-to-7 torsion injects into this group, ruling out Q-torsion for Q>=19.

Consequently G_0(Q)=Z H for some H. Suppose its reduction image is nonzero. Then H reduces to a nonzero element of the additive group F_Q, of exact order Q. Since S lies in the kernel, S=[m]H with a nonzero integer m divisible by Q.

**3. Explicit height bound on the fixed base, no conjectural height estimate**

For any non-torsion A on E_Q put z(A)=X(A)/(5Q). The quadratic-twist isomorphism to

 E: w^2=z(z+1)(z-3)

preserves canonical height. More directly, the elementary rational-height inequality |h(X/(5Q))-h(X)|<=log(5Q), applied to every [2^k]A, shows that the difference disappears after multiplication by 4^(-k) in the canonical-height limit. Thus hhat(A)=(1/2) lim_(k->infinity) 4^(-k) h(z([2^k]A)) with the standard normalization. The duplication map on these rational z-coordinates is:

 D(z)=(z^2+3)^2/[4z(z+1)(z-3)].

For coprime integers a,b, b>0, put H_0=max(|a|,b),

 F=(a^2+3b^2)^2,
 G=4ab(a+b)(a-3b).

Then H_0^4 <= max(|F|,|G|) <=24 H_0^4. Also gcd(F,G) divides 144:

- A common prime other than 2,3 cannot divide a or b, and a=-b or a=3b would force it to divide 4 or 12.
- If 3 divides a, then 3 does not divide b and v_3(a^2+3b^2)=1, so v_3(F)=2. If 3 does not divide a, 3 does not divide F.
- At 2, F is odd unless a,b are both odd. In that case a^2+3b^2=4 mod8, hence v_2(F)=4.

Thus, for logarithmic rational height h,

 4h(z)-log144 <= h(D(z)) <=4h(z)+log24.

Telescoping the canonical-height limit gives

 (1/2)h(z)-log144/6 <= hhat(A) <= (1/2)h(z)+log24/6,

and in particular |hhat(A)-(1/2)h(z)|<1. None of the duplication denominators is zero because A is non-torsion.

**4. Lower height from a nonzero global reduction**

Since H reduces to a finite nonzero nonsingular point on Y^2=X^3, both its coordinates are Q-adic units. Therefore v_Q(z(H))=-1. Its rational height is at least log Q, so

 hhat(H)>(1/2)log Q-1>1/3.

For the last inequality use Q>=19>16 and log2>2/3. Since Q divides m,

 hhat(S)=m^2 hhat(H)>Q^2/3.

**5. Upper height from the ORIGINAL golden clock**

The base coordinate of S is z(S)=-3/B_j. Since 3 does not divide B_j, h(z(S))=log B_j. Write N=3^j and phi=(1+sqrt5)/2. For odd N>=3,

 L_N=phi^N-phi^(-N)<phi^N,
 B_j<2phi^(2N),
 log B_j<N+1,

using 2log phi<1 and log2<1. The actual rank constraint gives N< Q/6. Hence

 hhat(S)<(1/2)log B_j+1<Q/12+3/2.

But Q^2/3>Q/12+3/2 for every Q>=3, a contradiction. The global reduction image must therefore be zero, proving the statement.


**Theorem 74.3 (one-point certificate excluding the depth-three role).**
Let Q>5 be prime. If there are rational numbers a,b satisfying

 b^2=a(a+5Q)(a-15Q),     v_Q(a)=v_Q(b)=0,

then there are no j>=1 and prime P distinct from Q such that

 L_(3^j)^2+3=P^2 Q^3.

Proof. The displayed rational point reduces to a finite nonsingular point of Y^2=X^3, because both coordinates are nonzero modulo Q. Hence it belongs to G_0(Q) but not G_1(Q). Theorem 74.2 contradicts the proposed golden factorization. This conclusion concerns only the depth-three role in this factorization; it asserts neither non-WSS status for Q in other settings nor existence of such certificates for infinitely many primes.

## 75. A quartic prime family excluded from the depth-three role

The construction below is an elementary rational-conic parametrization, not a new general method for constructing theta-congruent twists. This application supplies explicit certificates for Theorem 74.3 while retaining the original golden blocks. General twist-point parametrizations via products of linear factors modulo squares are classical: see M. Kan, *theta-congruent numbers and elliptic curves*, Acta Arith. 94(2) (2000), 153–160, lemma proof on p.154, [primary journal text](https://matwbn.icm.edu.pl/ksiazki/aa/aa94/aa9422.pdf). All identities and local-unit assertions needed here are proved below.

**Definition 75.1 (the represented prime family).** Put

$$\mathcal F(m,n)=4m^4-2m^3n+11m^2n^2+2mn^3+4n^4.$$

Let $\mathcal Q$ be the set of primes $Q>5$ represented as $Q=\mathcal F(m,n)$ by integers $m,n$. This definition asserts neither infinitely many prime values nor infinitely many members in the actual golden prime supports.

**Theorem 75.2 (uniform quartic-family exclusion).** For every $Q\in\mathcal Q$, every $j\ge1$, and every prime $P\ne Q$,

$$\boxed{L_{3^j}^{\,2}+3\ne P^2Q^3.}$$

Thus the depth-three prime in an actual surviving $P^2Q^3$ block cannot be represented by $\mathcal F$ over the integers.

**Proof.** Choose $m,n$ with $Q=\mathcal F(m,n)$ and put

$$u=m^2+mn-n^2,\qquad v=m^2-4mn-n^2,\qquad r=m^2+n^2.$$

The identity $v+2iu=(1+2i)(m+in)^2$ and its norm, or direct polynomial expansion, give

$$4u^2+v^2=5r^2,\qquad Q=3u^2+v^2=5r^2-u^2.$$

Consequently $T=(-15u^2,75uvr)$ is an integral point on $E_Q:Y^2=X(X+5Q)(X-15Q)$. Indeed,

$$X(T)+5Q=5v^2,\qquad X(T)-15Q=-75r^2,$$

and the product of the three factors is $5625u^2v^2r^2=Y(T)^2$.

We verify that both coordinates are $Q$-adic units. First $\gcd(m,n)=1$: otherwise a common divisor $d>1$ would have $d^4\mid Q$ by homogeneity, contradicting primality. If $Q\mid u$, the equation $Q=3u^2+v^2$ implies $Q\mid v$. Then $u-v=5mn$ and $Q>5$ imply $Q\mid m$ or $Q\mid n$. Substitution in $u=m^2+mn-n^2$ forces the other divisibility, contradicting coprimality. Hence $Q\nmid u$. If $Q\mid v$, then $Q\mid3u^2$, again impossible. If $Q\mid r$, the equation $Q=5r^2-u^2$ forces $Q\mid u$. Thus $Q\nmid uvr$, and $Q\nmid75$ gives the required unit coordinates. This also excludes zero $u,v,r$, since zero is divisible by $Q$. There are no omitted zero-coordinate exceptions. Theorem 74.3 proves the conclusion. ∎

**Lemma 75.3 (compatibility with the required prime class).** Every $Q\in\mathcal Q$ satisfies $Q\equiv19\pmod{120}$.

**Proof.** Coprimality excludes both $m,n$ being even. If they have opposite parity, $u,v$ are odd, and $Q=3u^2+v^2$ is divisible by four, impossible. Thus both are odd. Hence $u$ is odd, $r\equiv2\pmod8$, and $Q=5r^2-u^2\equiv3\pmod8$. Modulo five, $u\equiv(m+3n)^2$, so $Q\equiv-(m+3n)^4\equiv-1\pmod5$ because $Q\ne5$. Finally $Q\equiv v^2\equiv1\pmod3$ because $Q\ne3$. These combine to give $19$ modulo $120$. ∎

The lemma is a compatibility check, not the exclusion argument. The family is not disjoint from actual golden prime support: $\mathcal F(1,1)=19=L_3^2+3$. This example is not a new individual exclusion. The theorem is uniform in all integer parameters and all original layers; it does not replace exact golden support by unrestricted splitting. No assertion is made that infinitely many represented primes have pure ternary golden period, that every other cross-level necessary condition is independent of the representation, or that a member cannot be WSS in another depth vector. The parametrization and congruence lemma are elementary; the global exclusion uses Section 74's height and reduction obstruction. This is a paper proof with no Lean certification claim.


## 76. The original integral orbit forces a primitive global generator

**Theorem 76.1 (primitive generator and simultaneous formal reduction).** Suppose $j\ge1$, $N=3^j$, and

$$B_N=L_N^2+3=P^2Q^3$$

for distinct primes $P,Q$. On $E_Q:Y^2=X(X+5Q)(X-15Q)$, let $G_0(Q)$ be the global rational subgroup of Definition 74.1, let $T_0=(0,0)$, and put

$$R=(5QB_N,25Q^2 L_N(PQ)F_N),\qquad S=R+T_0.$$

Then

$$\boxed{G_0(Q)=\mathbb Z S.}$$

In particular every point of $G_0(Q)$ reduces to infinity at both $Q$ and $P$. Reduction at $P$ is good. This asserts primitivity in the specified global subgroup, not a choice of generator of the full Mordell–Weil group modulo torsion.

**Proof.** Section 74 supplies $P,Q>5$, $Q\ge19$, and the conditional conclusions that $G_0(Q)=G_1(Q)$ is torsion-free of rank one and that $S$ is non-torsion with

$$X(S)=-\frac{15}{P^2Q^2},\qquad z(S)=\frac{X(S)}{5Q}=-\frac3{B_N}.$$

Choose a generator $H$ of $G_0(Q)$ and its sign so that $S=[m]H$ with $m>0$.

First $m$ is odd. For a real non-torsion point $U$, Section 74's duplication formula gives

$$z(2U)=\frac{(z(U)^2+3)^2}{4z(U)(z(U)+1)(z(U)-3)}>0,$$

because the denominator is $4Y(U)^2/(5Q)^3>0$. An even $m$ would therefore contradict $X(S)<0$. Set $K=H+T_0$. Since $m$ is odd and $T_0$ has order two,

$$[m]K=[m]H+T_0=S+T_0=R.$$

The point $K$ is non-torsion and integral. To see the latter, the displayed integral model has discriminant $2^8 3^2 5^6 Q^6$, whose valuation is less than twelve at every prime, so it is locally minimal everywhere. If a rational point on this model is nonintegral at a prime $\ell$, its $X$-coordinate has negative valuation and it belongs to the formal kernel. That kernel is a subgroup at every prime, including $2,3,5,Q$. Thus a nonintegral $K$ would make its nonzero multiple $[m]K=R$ nonintegral at the same prime, contradicting the displayed integer coordinates of $R$. No prime-to-$\ell$ assumption on $m$ is needed. These are the standard formal-kernel facts of Silverman, [VII.1–3](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf).

For the split cubic, complete two-descent gives the squareclass homomorphism whose coordinates at a non-two-torsion point $U$ are $X(U)$, $X(U)+5Q$, and $X(U)-15Q$ modulo rational squares. See Silverman, [X.1, Proposition 1.4](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf), printed p.315 / PDF p.327; the third class follows from the curve equation. Odd multiplication preserves these classes. At $R$ they are $(5,Q,5Q)$, because

$$X(R)=5(PQ^2)^2,\quad X(R)+5Q=Q(5F_N)^2,\quad X(R)-15Q=5Q L_N^2.$$

Consequently

$$X(K)=5a^2,\qquad X(K)+5Q=Qb^2,\qquad X(K)-15Q=5Qd^2$$

for rational $a,b,d$. They are integers: each left side is integral, and each coefficient $5,Q,5Q$ is squarefree, so a reduced denominator would require an impossible square factor in that coefficient. The equality $5a^2+5Q=Qb^2$ gives $Q\mid a$. Write $a=Qc$. The remaining equalities yield

$$X(K)=5Q^2c^2,\qquad d^2+3=Qc^2,\qquad b^2=5(Qc^2+1).$$

Hence $5\mid b$; writing $b=5f$ gives $d^2+4=5f^2$. Here $c\ne0$ because $K$ is non-torsion, $d\ne0$ because $Qc^2=3$ is impossible, and $f\ne0$. Take $d,f$ positive by changing their signs.

We recall the elementary integral negative-Pell classification, with its argument to fix the exact orbit: every positive solution of $d^2+4=5f^2$ is $(L_n,F_n)$ for an odd $n\ge1$. The two integers have the same parity. The solution with $d=1$ is $(1,1)$. If $d>1$, then $d\ge4$, and

$$d'=\frac{3d-5f}{2},\qquad f'=\frac{3f-d}{2}$$

are positive integers with $d'^2+4=5f'^2$ and $d'<d$. Positivity follows from $9d^2-25f^2=4d^2-20>0$ and $9f^2-d^2=4f^2+4>0$; strict decrease follows from $d<5f$. Descent ends at $(1,1)$. Its inverse multiplies $(d'+f'\sqrt5)/2$ by $\phi^2$, where $\phi=(1+\sqrt5)/2$, so $(d+f\sqrt5)/2=\phi^n$ for a positive odd $n$. This gives precisely the stated Lucas and Fibonacci coordinates.

Thus $Q\mid L_n^2+3$. The odd-index identities

$$L_{3n}=L_n(L_n^2+3),\qquad F_{6n}=F_{3n}L_{3n}$$

imply $Q\mid F_{6n}$. The original exact rank is $\rho(Q)=2\cdot3^{j+1}=6N$, by TBN3 in [the golden-unit-lift dossier](../../../Problems/wall-sun-sun-golden-unit-lift.md). Rank divisibility gives $6N\mid6n$, hence $N\mid n$ and $n\ge N$. In particular

$$z(K)=\frac{X(K)}{5Q}=Qc^2=L_n^2+3\ge B_N.$$

The original integral orbit is essential in this step; an arbitrary rational Pell solution does not supply an integer index $n$.

Write $c_0=\log144/6$ and $u_0=\log24/6$. The uniform bounds proved in Section 74, and invariance of canonical height under torsion translation, give

$$\widehat h(K)=\widehat h(H)\ge\tfrac12\log B_N-c_0,\qquad
\widehat h(R)=\widehat h(S)\le\tfrac12\log B_N+u_0.$$

Set $t=\tfrac12\log B_N$. Since $R=[m]K$,

$$m^2(t-c_0)\le t+u_0.$$

But $B_N\ge19>12$, so $t-c_0>0$ and

$$8t=4\log B_N>4\log12>3\log12+\frac{\log24}{6}=9c_0+u_0,$$

using $24<12^6$. Thus $9(t-c_0)>t+u_0$ and $m<3$. The positive odd integer $m$ must equal one. Hence $H=S$ and $G_0(Q)=\mathbb ZS$.

The entire group already lies in $G_1(Q)$ by Section 74. At $P$, the discriminant is a unit because $P>5$ and $P\ne Q$, and $v_P(X(S))=-2$ gives $\operatorname{red}_P(S)=O$. Therefore every point of $G_0(Q)$ also reduces to infinity at $P$. ∎

**Corollary 76.2 (one-point second-prime exclusion).** Let $P,Q>5$ be distinct primes. If there is a rational point $U\in E_Q(\mathbb Q)$ with nonsingular reduction at $Q$ and nonzero reduction at $P$, then

$$L_{3^j}^{\,2}+3\ne P^2Q^3\qquad\text{for every }j\ge1.$$

**Proof.** A hypothetical factorization puts $U$ in the global group of Theorem 76.1, whose reduction at $P$ is zero, a contradiction. ∎

This certificate may use a point in the $Q$-formal kernel; it does not require that point to generate any rational subgroup. Neither existence of a certificate for every pair, an infinite family of certificates, nor a general non-WSS conclusion follows. The rank-one hypothesis used in the proof is obtained only from the hypothetical actual factorization through Section 74, without a parity conjecture or finiteness assumption on a Tate–Shafarevich group.


**Corollary 76.3 (full rational group and reduction image).** Under the hypotheses of Theorem 76.1,

$$E_Q(\mathbb Q)=\mathbb Z S\oplus E_Q[2],\qquad
\operatorname{red}_P(E_Q(\mathbb Q))=E_Q(\mathbb F_P)[2].$$

The group on the right has exactly the four points $O,(0,0),(-5Q,0),(15Q,0)$ reduced modulo $P$.

**Proof.** First $[2]U\in G_0(Q)$ for every $U\in E_Q(\mathbb Q)$. This is immediate for two-torsion and for $U\in G_0(Q)$. Otherwise $U$ reduces to the cusp at $Q$, so $k=v_Q(X(U))\ge1$. The duplication formula is

$$X(2U)=\frac{(X(U)^2+75Q^2)^2}{4X(U)(X(U)+5Q)(X(U)-15Q)}.$$

If $k\ge2$, the shifted factors each have valuation one. The curve equation forces $k+2$ to be even, and the numerator has valuation four, so $v_Q(X(2U))=2-k\le0$.

If $k=1$, write $X(U)=Qw$ with $w$ a $Q$-adic unit. The even valuation of

$$Y(U)^2=Q^3w(w+5)(w-15)$$

forces exactly one of $w+5,w-15$ to have a positive, odd valuation $t$. Their difference is $20$, a unit at $Q>5$. At the respective residues $w=-5$ and $w=15$, the expression $w^2+75$ is $100$ or $300$, also a unit at $Q>5$. Thus $v_Q(X(2U))=4-(3+t)=1-t\le0$.

Negative $X$-valuation gives reduction to infinity, while zero valuation gives a finite nonsingular point on $Y^2=X^3$. This proves $[2]U\in G_0(Q)$ in all cases. Theorem 76.1 now writes $[2]U=[k]S$ for an integer $k$. If $k$ were odd, its $X$-coordinate would have the negative squareclass $-15$ of $X(S)$, by complete two-descent. It would therefore be negative. But the nonzero double $[2]U$ has positive $X$ by the real duplication formula. Hence $k=2l$, and $U-[l]S$ is rational two-torsion. Non-torsion of $S$ makes the sum direct.

The four rational two-torsion points reduce distinctly at $P>5$, $P\ne Q$. The point $S$ reduces to infinity, proving the image equality. ∎

**Corollary 76.4 (explicit second-prime support from one rational point).** Let $P,Q>5$ be distinct primes and let $U=(x,y)\in E_Q(\mathbb Q)$ be a point which is not two-torsion. Write $\operatorname{den}(x)>0$ for the denominator of $x$ in lowest terms and $\operatorname{num}(y)\ne0$ for the numerator of $y$ in lowest terms. An actual factorization $L_{3^j}^2+3=P^2Q^3$ necessarily satisfies

$$\boxed{P\mid\operatorname{den}(x)\operatorname{num}(y).}$$

**Proof.** If $P$ divides neither factor, $x$ is $P$-integral and the integral curve equation makes $y$ $P$-integral as well. Its reduced numerator being a unit makes $y$ a unit. Thus $U$ reduces to a finite point with nonzero $Y$-coordinate, which is not two-torsion. This contradicts Corollary 76.3. ∎

For a fixed $Q$ and one supplied non-two-torsion rational point, the nonzero integer in Corollary 76.4 gives a finite explicit set containing every possible second prime. The point need not be a generator or satisfy a nonsingular-reduction test at $Q$. This does not assert that such a point or a new excluded pair has been exhibited for every $Q$.



## 77. A prime squareclass controls every even initial depth

**Theorem 77.1 (the original generator with a simple odd-depth factor allowed).** Let $j\ge1$, $N=3^j$, and suppose the actual golden block satisfies

$$B_N=L_N^2+3=QC^2$$

for a rational prime $Q$ and a positive integer $C$. Thus $Q$ is the only prime of odd initial depth; no all-WSS hypothesis or assumption $Q\mid C$ is imposed. On $E_Q:Y^2=X(X+5Q)(X-15Q)$ put

$$R=(5QB_N,25Q^2L_NCF_N),\qquad T_0=(0,0),\qquad S=R+T_0.$$

Then

$$\boxed{G_0(Q)=\mathbb ZS,\qquad E_Q(\mathbb Q)=\mathbb ZS\oplus E_Q[2].}$$

Moreover the global formal subgroup is exactly

$$\boxed{G_1(Q)=\begin{cases}Q\mathbb ZS,&h_Q=1,\\\mathbb ZS,&h_Q\ge3,\end{cases}\qquad h_Q=1+2v_Q(C).}$$

The nonsingular global reduction image at $Q$ is respectively all of $\mathbb F_Q$ or zero. For every prime $p\mid C$ with $p\ne Q$, reduction is good and

$$\operatorname{red}_p(E_Q(\mathbb Q))=E_Q(\mathbb F_p)[2].$$

**Proof.** TBN3 and GPC5 in [the golden-unit-lift dossier](../../../Problems/wall-sun-sun-golden-unit-lift.md) give $p>5$, $\rho(p)=6N$ and $v_p(B_N)=h_p$ for every prime $p\mid B_N$. GPC5 gives the squarefree kernel $19$ modulo $120$, so here $Q\equiv19\pmod{120}$ without an all-WSS assumption. Goto's full two-Selmer bound, [Section 2 and Table 9](https://www.ma.noda.tus.ac.jp/u/tg/files/thesis.pdf), type $5\times19$, therefore gives $\operatorname{rank}E_Q(\mathbb Q)\le1$ as in Section 74.

The torsion-freeness argument for $G_0(Q)$ in Section 74 is independent of the factorization pattern. The formal kernel at $Q\ge19$ is torsion-free. Torsion in $G_0(Q)$ therefore injects into the additive nonsingular group $\mathbb F_Q$ and has order dividing $Q$. Good reduction at seven, where this curve has eight points, rules out such torsion. The displayed model is minimal at every prime because its discriminant is $2^8 3^2 5^6Q^6$, with every nonzero valuation below twelve.

The identities $B_N=QC^2$ and $L_N^2+4=5F_N^2$ show directly that $R$ is integral on $E_Q$. Translation by $T_0$ gives

$$X(S)=-\frac{15}{C^2},\qquad z(S)=\frac{X(S)}{5Q}=-\frac3{B_N}.$$

The point $S\ne O$ lies in $G_0(Q)$: it is formal if $Q\mid C$, and has unit coordinates and finite nonsingular reduction if $Q\nmid C$. Torsion-freeness of $G_0(Q)$ proves that $S$ is non-torsion in both cases. In particular this argument does not invoke the vanishing-image theorem 74.2 in the new case $h_Q=1$. The rank is one, and $G_0(Q)=\mathbb ZH$.

Choose the sign of $H$ so $S=[m]H$ with $m>0$. A nonzero real double has positive $X$ by the duplication formula, whereas $X(S)<0$, so $m$ is odd. Put $K=H+T_0$; then $[m]K=R$. The formal-kernel argument of Theorem 76.1 proves that $K$ is integral at every prime, including $2,3,5,Q$: a nonintegral point belongs to the formal kernel, whose nonzero multiples remain nonintegral. This needs no condition on the prime divisors of $m$.

Complete two-descent, [Silverman X.1, Proposition 1.4](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf), preserves squareclasses under odd multiplication. At $R$ the three classes are again $(5,Q,5Q)$, since

$$X(R)=5(QC)^2,\quad X(R)+5Q=Q(5F_N)^2,\quad X(R)-15Q=5QL_N^2.$$

As in the explicit descent of Theorem 76.1, integrality and squarefreeness of $5,Q,5Q$ therefore give integers $c,d,f$ with

$$X(K)=5Q^2c^2,\qquad d^2+3=Qc^2,\qquad d^2+4=5f^2.$$

After choosing positive $d,f$, the integral negative-Pell classification proved there gives $(d,f)=(L_n,F_n)$ for an odd integer $n\ge1$. The equation $Q\mid L_n^2+3$, the identities $L_{3n}=L_n(L_n^2+3)$ and $F_{6n}=F_{3n}L_{3n}$, and the original exact rank $\rho(Q)=6N$ imply $N\mid n$. Consequently

$$z(K)=L_n^2+3\ge B_N.$$

The uniform height bounds of Section 74 now give, with $t=\tfrac12\log B_N$, $c_0=\log144/6$ and $u_0=\log24/6$,

$$m^2(t-c_0)\le t+u_0.$$

Exactly as in Theorem 76.1, $B_N\ge19>12$ implies $9(t-c_0)>t+u_0$. Thus $m<3$ and the positive odd integer $m$ is one. This proves $G_0(Q)=\mathbb ZS$. The proof also applies when $C=1$.

The local duplication computation of Corollary 76.3 uses only $Q>5$ and proves $[2]U\in G_0(Q)$ for every rational point $U$. Write $[2]U=[k]S$. If $k$ is odd, its $X$-coordinate has the negative squareclass $-15$ of $X(S)$, contrary to positivity of a nonzero real double. Hence $k$ is even and $U\in\mathbb ZS+E_Q[2]$. Non-torsion of $S$ makes the sum direct.

If $Q\nmid C$, the reduction of $S$ is nonzero in the additive group $\mathbb F_Q$ and has order $Q$, giving $G_1(Q)=Q\mathbb ZS$. If $Q\mid C$, the generator is formal and $G_1(Q)=\mathbb ZS$. Finally, for $p\mid C$, $p\ne Q$, the discriminant is a $p$-unit and $v_p(X(S))=-2v_p(C)<0$. The generator reduces to infinity and the four rational two-torsion points reduce distinctly, proving the last assertion. ∎

**Theorem 77.2 (full cofactor denominator certificate).** Under the hypotheses of Theorem 77.1, every rational point $U$ which is not two-torsion satisfies

$$\boxed{C^2\mid\operatorname{den}(X(2U)),\qquad B_N\le Q\operatorname{den}(X(2U)).}$$

Here denominators are positive and in lowest terms. In standard coprime coordinates $X(U)=A/D^2$, $Y(U)=B/D^3$, $D>0$, one also has

$$\boxed{C\mid DB.}$$

**Proof.** Theorem 77.1 writes $U=[l]S+T$ with $T\in E_Q[2]$ and $l\ne0$. Hence $2U=[2l]S\ne O$. For $p\mid C$ put $e=v_p(C)>0$. Since $p>5$, $v_p(X(S))=-2e$, and the standard formal parameter $t=-X/Y$ has valuation $e$. The formal multiplication series on this integral model has integral $p$-adic coefficients and zero constant term, so multiplication by every integer preserves $p^e\mathbb Z_p$. The formal Laurent expansion for $X$ then gives

$$v_p(X(2U))\le-2e.$$

These standard integral formal-group facts are recorded in [Silverman IV.1–2 and VII.2](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf). They apply also at $p=Q$ when $Q\mid C$; good reduction is unnecessary. Taking the product over all primes of $C$ proves the denominator divisibility and the bound for $B_N$.

In the standard coordinates, duplication gives

$$X(2U)=\frac{(A^2+75Q^2D^4)^2}{4D^2B^2}.$$

Its reduced denominator divides $4D^2B^2$, so $C^2\mid4D^2B^2$. Since $C$ is odd, comparison of valuations gives $C\mid DB$. The premise on $U$ ensures $B\ne0$ and $2U\ne O$. ∎

**Corollary 77.3 (an integral nonsingular point forces a prime block).** Let $Q>5$ be prime. If $E_Q$ has an affine integral point $U$ with nonsingular reduction at $Q$, then every actual equality $B_N=QC^2$ as in Theorem 77.1 has $C=1$, hence $B_N=Q$.

**Proof.** The point belongs to $G_0(Q)=\mathbb ZS$, so $U=[k]S$ with $k\ne0$. If a prime $p$ divided $C$, then $S$ would belong to the formal kernel at $p$. Its nonzero multiple $U$ would also be formal, with negative $X$-valuation, contradicting integrality of $U$. Thus $C$ has no prime divisor and equals one. ∎

**Corollary 77.4 (quartic prime-squareclass rigidity).** Use the integer polynomial and parameters of Section 75:

$$Q=4m^4-2m^3n+11m^2n^2+2mn^3+4n^4>5\quad\text{prime},$$

$$u=m^2+mn-n^2,\qquad v=m^2-4mn-n^2,\qquad r=m^2+n^2.$$

If an actual block satisfies $B_N=QC^2$, then necessarily

$$\boxed{C=1,\quad u^2=1,\quad v^2=L_N^2,\quad r=F_N,\quad h_Q=1.}$$

In particular, if $|m^2+mn-n^2|\ne1$, the prime $Q$ cannot be the sole odd-depth prime of any actual golden ternary block. For every prime $Q$ in this quartic family, a nontrivial square cofactor $C>1$ is impossible; this includes every mixed-depth pattern $P^2Q$ with distinct primes.

**Proof.** Section 75 supplies the integral point $U=(-15u^2,75uvr)$ and proves $Q\nmid uvr$, including all zero and coprimality exceptions. Thus $U$ is nonsingular at $Q$, and Corollary 77.3 gives $C=1$ and $Q=B_N$. Theorem 77.1 writes $U=[k]S$ with $k\ne0$. Its negative $X$-coordinate forces $k$ to be odd.

Both base coordinates have the same rational height:

$$z(U)=-\frac{3u^2}{Q},\qquad z(S)=-\frac3Q,\qquad h(z(U))=h(z(S))=\log Q.$$

Indeed $Q=3u^2+v^2$, $v\ne0$ and $Q\nmid u$, so the first fraction is reduced and its denominator exceeds its numerator in absolute value. The uniform height bounds, with $t=\tfrac12\log Q$, give

$$k^2(t-c_0)\le t+u_0.$$

As above, $Q\ge19$ implies $|k|<3$, hence $k=\pm1$. Equality of the $X$-coordinates of $U$ and $S$ gives $u^2=1$. The identities $Q=3u^2+v^2=5r^2-u^2$ then give $v^2=L_N^2$ and $r^2=F_N^2$. Since $r=m^2+n^2>0$, one has $r=F_N$. Finally $C=1$ gives $h_Q=1$. ∎

The new scope includes a simple odd-depth factor: in $P^2Q$, $P$ would be WSS while $Q$ would be non-WSS, and a $Q$-unit point alone does not invoke the earlier depth-three exclusion. The integral-point argument excludes this mixed pattern for the displayed quartic family. The denominator theorem also constrains all even exponents and arbitrary one-odd-prime all-WSS vectors. Multiple odd-depth primes are outside its rank-one argument. No new numerical previously surviving pair, infinitude of prime quartic values, independence from all older congruences, universal point existence, or global WSS decision is asserted.


## 78. Two odd depths with mutual quadratic nonresidue

**Theorem 78.1 (composite squareclass and the original generator).** Let $N=3^j$, $j\ge1$, and suppose the actual golden block is

$$B_N=L_N^2+3=DC^2,\qquad D=qr,$$

where $q,r$ are distinct primes and $C$ is a positive integer. Suppose

$$\left(\frac qr\right)=-1.$$

On $E_D:Y^2=X(X+5D)(X-15D)$ define $G_0$ to be the intersection of the global rational nonsingular subgroups at $q$ and $r$. Put

$$R=(5DB_N,25D^2L_NCF_N),\qquad T_0=(0,0),\qquad S=R+T_0.$$

Then

$$\boxed{G_0=\mathbb ZS,\qquad E_D(\mathbb Q)=\mathbb ZS\oplus E_D[2].}$$

Every rational $U\notin E_D[2]$ satisfies

$$\boxed{C^2\mid\operatorname{den}X(2U),\qquad B_N\le D\operatorname{den}X(2U).}$$

If there is an affine integral point $U\in G_0$, then $C=1$. Here the denominator is positive and reduced. In particular, this criterion applies to the original all-WSS profiles $q^3r^5$ and $p^2q^3r^3$ when the two odd-depth primes have mutual symbol $-1$.

**Proof: the full Selmer input.** TBN3 and GPC5 give

$$q,r>5,\quad q,r\equiv1\pmod6,\quad (5/q)=(5/r)=1,\quad D\equiv19\pmod{120}.$$

The primes have opposite residues $1,4$ modulo five, but both are quadratic residues modulo five. Their ordered residue types modulo $24$ are $(1,19)$ or $(7,13)$. Reciprocity gives $(q/r)=(r/q)$.

Use the full two-descent local formulas of Feng, Liu, Pan and Tian, *Quadratic twists of tiling number elliptic curves*, [arXiv:2405.11132](https://arxiv.org/pdf/2405.11132), §3.1.1–3.1.3, printed pages 9–10. Their model is $y^2=x(x-m)(x+3m)$; here $m=-5D<0$ and $m\equiv1\pmod{24}$. Write $[a/p]=(1-(a/p))/2\in\mathbb F_2$ and $\beta=[r/q]$. For primes $(5,q,r)$ put $d_i=[-1/p_i]$, $t_i=[2/p_i]$. The two ordered types give, respectively,

$$(d,t)=((0,0,1),(1,0,1))\quad\hbox{or}\quad((0,1,0),(1,0,1)).$$

The source's zero-row-sum matrix and character vectors are

$$A=\begin{pmatrix}0&0&0\\0&\beta&\beta\\0&\beta&\beta\end{pmatrix},\qquad z_3=(1,d_q,d_r),\qquad z_{-3}=(1,0,0).$$

For the full Selmer group represent the descent classes by

$$b_1=(-1)^e3^a5^{x_0}q^{x_1}r^{x_2},\qquad b_2=2^b5^{y_0}q^{y_1}r^{y_2}.$$

These forms exhaust the candidates: the real condition is $b_2>0$, the local condition at two makes $b_1$ odd, and the local condition at three makes $3\nmid b_2$. The local conditions at three and two then give

$$b=y_0+a,\qquad e=y_0+d_qx_1+d_rx_2,$$

$$y_0+x_0+t_qx_1+t_rx_2+d_qy_1+d_ry_2=0.$$

In fact the two equations at two are $[-1/b_1]+b=0$ and $[-1/b_1]+[2/b_1]+[-1/(b_2/2^b)]=0$. All operations in this descent calculation are over $\mathbb F_2$.

For $x=(x_0,x_1,x_2)^T$, $y=(y_0,y_1,y_2)^T$, the exact conditions at $5,q,r$ are

$$(A+\operatorname{diag}(d))x+\operatorname{diag}(1,0,0)y=ed+a(1,d_q,d_r)^T,\qquad Ay=(y_0+a)t.$$

Together these are seven equations in $(a,x_0,x_1,x_2,y_0,y_1,y_2)$. With $\beta=1$, for either residue type they reduce to the four independent equations

$$a+y_0=0,\qquad x_0+x_2+y_0+y_2=0,\qquad x_1+x_2=0,\qquad y_1+y_2=0.$$

Thus the full Selmer dimension is three. Subtracting the dimension two of the rational two-torsion image bounds the Mordell–Weil rank by one. For comparison, if $\beta=0$, the reduced equations are $a+y_0=0$ and $x_0+x_2+y_0+y_2=0$ for type $(1,19)$, or $a+y_0=0$ and $x_0+x_2+y_0+y_1=0$ for type $(7,13)$. The full Selmer dimension is then five; that case is not covered by the rank-one argument. No inference from rank parity or finiteness of $\Sha$ is used.

**Proof: the integral golden orbit.** The model discriminant is $2^8 3^2 5^6D^6$. Because $D$ is squarefree, every nonzero discriminant valuation is less than twelve, so this model is minimal at every prime. At either $\ell\mid D$, its reduction is $Y^2=X^3$, with nonsingular group $\mathbb F_\ell$ under addition. TBN3 gives $\ell\ge19$. Its formal subgroup is torsion-free, so torsion in $G_0$ would have order dividing $\ell$. Good reduction at seven excludes this: the base curve $y^2=x(x+1)(x-3)$ and each nonzero quadratic twist over $\mathbb F_7$ have eight points.

The Pell identity $L_N^2+4=5F_N^2$ verifies $R\in E_D(\mathbb Q)$, and translation gives

$$X(S)=-15/C^2,\qquad z(S):=X(S)/(5D)=-3/B_N.$$

For each $\ell\mid D$, the point $S$ is formal if $\ell\mid C$, and finite nonsingular otherwise. Thus $S$ is nonzero in the torsion-free group $G_0$. The Selmer bound makes the rank exactly one. Choose a generator $H$ of $G_0$ with $S=mH$, $m>0$.

Every nonzero real double has positive $X$, by

$$X(2V)=\frac{(X(V)^2+75D^2)^2}{4Y(V)^2}>0.$$

Since $X(S)<0$, the integer $m$ is odd. Set $K=H+T_0$, so $mK=R$. A nonintegral point lies in a local formal kernel, and every nonzero multiple remains there. The integrality of $R$ therefore forces $K$ to be integral at every prime, including $2,3,5,q,r$.

Odd multiplication preserves the complete two-descent classes. The classes of $R$ are $(5,D,5D)$, so

$$X(K)=5a^2,\quad X(K)+5D=Db^2,\quad X(K)-15D=5Dd^2$$

for integers $a,b,d$: all three squareclass representatives are squarefree. Since $D\mid a^2$ and $D$ is squarefree, write $a=Dc$. It follows that

$$d^2+3=Dc^2,\qquad b=5f,\qquad d^2+4=5f^2.$$

The three coordinates $c,d,f$ are nonzero. The integral negative-Pell descent from §77 gives $|d|=L_n$, $|f|=F_n$ for an odd positive $n$. Either $\ell\mid D$ divides $L_n^2+3$, hence divides $F_{6n}$. Its original exact rank is $6N$, so $N\mid n$ and $n\ge N$. Consequently

$$z(K)=Dc^2=L_n^2+3\ge B_N.$$

The scaled coordinate $z=X/(5D)$ has the same duplication function $(z^2+3)^2/[4z(z+1)(z-3)]$ used in §74. Its uniform height constants remain $c_0=\log144/6$, $u_0=\log24/6$. The difference between $h(X/(5D))$ and $h(X)$ is bounded by $\log(5D)$, so it vanishes in the canonical-height doubling limit. With $t=\log B_N/2$, the height argument gives

$$m^2(t-c_0)\le t+u_0.$$

As $B_N\ge19$ and $9(t-c_0)>t+u_0$, the positive odd integer $m$ equals one. Thus $G_0=\mathbb ZS$.

For completeness, $2U\in G_0$ for every rational $U$. At $\ell\mid D$, write $D=\ell D'$ with $D'$ a unit. For a point reducing to the cusp put $k=v_\ell(X(U))\ge1$. If $k\ge2$, both shifted factors have valuation one, $k$ is even, and $v_\ell(X(2U))=2-k\le0$. If $k=1$, write $X=\ell w$. Exactly one of $w+5D',w-15D'$ has positive odd valuation $v$. The numerator $w^2+75D'^2$ is a unit, with residue $100D'^2$ or $300D'^2$, so $v_\ell(X(2U))=1-v\le0$. Nonsingular and two-torsion points are immediate. Now $2U=kS$; if $k$ were odd its $X$ squareclass would be negative, namely $-15$, impossible for a nonzero real double. Thus $k=2h$ and $U-hS\in E_D[2]$, proving the full direct sum.

If $U\notin E_D[2]$, write $U=hS+T$ with $h\ne0$. At any $p\mid C$ the formal parameter of $S$ has valuation $v_p(C)$. Integral formal multiplication by $2h$ preserves this lower bound, so $v_p(X(2U))\le-2v_p(C)$. This also covers $p=q,r$ and proves the denominator divisibility. If $U\in G_0$ is affine integral, then $U=hS$ with $h\ne0$. A prime dividing $C$ would make $U$ formal and nonintegral; hence $C=1$.

The group and descent inputs are Silverman, *The Arithmetic of Elliptic Curves*, IV.1–2 and IV.6, VII.1–3, VIII.9, and X.1 Proposition 1.4; see [the primary text](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf). The height and integral-Pell estimates are the explicit ones in §§74,76–77.

**Corollary 78.2 (a supplied integral certificate for two odd depths).** Let integers $m,n$ give the squarefree integer

$$D=4m^4-2m^3n+11m^2n^2+2mn^3+4n^4=qr,$$

where $q,r>5$ are distinct primes, $q,r\equiv1\pmod6$, $D\equiv19\pmod{120}$, and $(q/r)=-1$. Put

$$u=m^2+mn-n^2,\quad v=m^2-4mn-n^2,\quad r_0=m^2+n^2.$$

If $B_N=DC^2$ is an actual golden ternary block, then

$$\boxed{C=1,\qquad u^2=1,\qquad v^2=L_N^2,\qquad r_0=F_N.}$$

In particular, $|u|>1$ excludes $D$ as the squarefree kernel of every such actual block. Any member of this family excludes the two-odd-prime all-WSS profiles with $C>1$.

**Proof.** The classical two-conic parametrization already used in §75 gives

$$D=3u^2+v^2=5r_0^2-u^2,\qquad 4u^2+v^2=5r_0^2.$$

Thus $U=(-15u^2,75uvr_0)$ is integral on $E_D$. The values $u,v,r_0$ are nonzero: vanishing of $u$ or $v$ requires a rational root of a quadratic with nonsquare discriminant, and $r_0=0$ forces $D=0$. Squarefreeness of $D$ forces $\gcd(m,n)=1$. If $p\mid D$ also divides $u$, then $p\mid v$ and $v-u=-5mn$ gives $p\mid mn$. The second identity gives $p\mid r_0$, so $p\mid m,n$, a contradiction. Divisibility of $v$ or $r_0$ likewise forces divisibility of $u$. Therefore $\gcd(D,uvr_0)=1$, and $U$ is nonsingular at both odd-depth primes.

Theorem 78.1 forces $C=1$ and $U=kS$ with $k\ne0$. Negative $X(U)$ makes $k$ odd. Since $0<3u^2<D$, $\gcd(u,D)=1$ and $3\nmid D$, both $z(U)=-3u^2/D$ and $z(S)=-3/D$ have height $\log D$. The same uniform height constants force $|k|<3$, hence $k=\pm1$. Comparing $X$ gives $u^2=1$, and the two conic identities give the remaining equalities.

This application supplies an explicit conditional restriction for composite squareclass. The Selmer formulas and quartic parametrization are classical inputs. No infinitude of the prime-factorization family, previously surviving numerical pair, independence from every earlier support condition, or conclusion in the mutual-residue case is asserted.


## 79. Quartic descent in the mutual-residue branch

**Theorem 79.1 (an explicit Cassels pairing).** Let $q,r$ be distinct primes with

$$q\equiv1\pmod{24},\qquad r\equiv19\pmod{24},\qquad (5/q)=(5/r)=(q/r)=1.$$

Put $D=qr$ and $E_D:y^2=x(x+5D)(x-15D)$. In the complete two-descent pair convention $(x,x+5D)$, the classes

$$\lambda=(q,1),\qquad \mu=(1,q)$$

belong to the full two-Selmer group, and their multiplicative Cassels pairing is

$$\boxed{\langle\lambda,\mu\rangle=\left(\frac{-5r}{q}\right)_4.}$$

Here the rational quartic symbol of the quadratic residue $-5r$ is its $(q-1)/4$ power modulo $q$, identified with $\{1,-1\}$. If this symbol is $-1$, then $\operatorname{rank}E_D(\mathbb Q)\le1$, without assuming finiteness of $\Sha$.

Consequently, if $B_N=DC^2$ is an actual golden ternary block and this quartic symbol is $-1$, all conclusions of Theorem 78.1 hold: the original translated point generates the full free rational group, every non-two-torsion point supplies the denominator bound, and an affine integral point nonsingular at both $q,r$ forces $C=1$. The quartic-parametrization conclusion of Corollary 78.2 also holds with its mutual-nonresidue hypothesis replaced by the hypotheses of this theorem and the negative quartic symbol.

**Proof: Selmer space and pairing convention.** Since at most one prime is three modulo four, reciprocity gives $(r/q)=1$. The corrected local computation in §78 for type $(1,19)$ and $\beta=0$ gives full Selmer dimension five, with equations

$$a=y_5,\qquad x_5+x_r+y_5+y_r=0$$

in coordinates $(a,x_5,x_q,x_r,y_5,y_q,y_r)$. The two classes in the statement satisfy these equations. The rational two-torsion classes $(-3,5qr)$ and $(-5qr,1)$, together with $(-15,5)$, $\lambda$ and $\mu$, are independent: their respective binary coordinate masks are $113,14,19,4,32$. The $x_r$, $y_r$, $a$, $x_q$, and $y_q$ coordinates successively verify independence. Thus the pure Selmer dimension is three.

Use the tangent-plane pairing formula in Shukla–Stoll, *The Cassels–Tate pairing on 2-Selmer groups of elliptic curves*, [arXiv:2302.01640](https://arxiv.org/pdf/2302.01640), §3.2, equations (3.9)–(3.10), printed pages 6–7. Its roots here are $0,-5qr,15qr$. The formula is independent of choices and agrees with the Cassels–Tate pairing. The same primary source, printed page 2, states that the Mordell–Weil image lies in the kernel, which is the image of the four-Selmer group. These statements require no finiteness of $\Sha$.

The triple for $\lambda$ is $(q,1,q)$. Its auxiliary conics are

$$H_1:z_2^2-qz_3^2=20qr t^2,\qquad H_2:z_1^2-z_3^2=15r t^2,\qquad H_3:z_2^2-qz_1^2=5qr t^2.$$

Since $\lambda$ is locally soluble everywhere, each conic is. The Hasse principle gives rational $a,b$ with

$$a^2-qb^2=5qr.$$

Normalization to $t=1$ is valid because a nontrivial rational point with $t=0$ would make $q$ a square. Choose $Q_3=(t,z_1,z_2)=(1,b,a)$, $Q_1=(t,z_2,z_3)=(1,2a,2b)$ and

$$Q_2=(t,z_1,z_3)=\left(1,\frac{15r+1}{2},\frac{1-15r}{2}\right).$$

The relevant tangent forms are

$$L_2=\frac{15r+1}{2}z_1-\frac{1-15r}{2}z_3-15rt,\qquad L_3=az_2-qbz_1-5qrt.$$

The triple for $\mu$ is $(1,q,q)$, so the pairing is

$$\prod_v(L_2(P_v)L_3(P_v),q)_v,$$

where $P_v$ is a local covering point avoiding tangent zeros and $(\ ,\ )_v$ denotes the quadratic Hilbert symbol. Dividing the conic equations or tangent forms by nonzero rational constants does not change this global product, by Hilbert reciprocity.

**Proof: the places away from $q$.** At $2,3,5,r$ and infinity, $q$ is locally a square, by its residues, the displayed quadratic symbols, and positivity. All these factors are one. The same holds at every other place where $q$ is a square.

Let $p\nmid30qr$ be odd and $q$ a nonsquare unit in $\mathbb Q_p$. The norm equation forces $a,b$ to be $p$-integral: otherwise their leading terms cannot cancel modulo $p$, contradicting the unit right side. Thus both chosen tangent points are integral on smooth conics modulo $p$, with $t=1$, and both tangent forms are primitive since their $t$ coefficients are units.

A primitive integral local covering point has $t$ a unit. Otherwise $H_3$ and nonsquareness of $q$ force $p\mid z_1,z_2$, and $H_2$ then forces $p\mid z_3$, contradicting primitivity. Normalize $t=1$. Each nonzero tangent evaluation has even valuation. Indeed, if the reduced point differs from the tangency point, the evaluation is a unit. Near the tangency point an integral change of coordinates puts the smooth conic and its tangent into the form

$$a_0XZ+b_0Y^2+c_0YZ+d_0Z^2=0,\qquad Z=0,$$

with $a_0,b_0$ units. Near $(1,0,0)$ one has

$$Z(a_0X+c_0Y+d_0Z)=-b_0Y^2,$$

so the valuation of the tangent coordinate $Z$ is even. This applies to both $L_2$ and $L_3$. Local points can avoid their finitely many zero loci on the smooth covering. Since the Hilbert symbol with a nonsquare unit at an odd prime depends only on valuation parity, the factor is one. This accounts also for possible auxiliary primes in the rational conic solution.

**Proof: the factor at $q$.** The terms in $a^2-qb^2$ have opposite valuation parity, while their difference has valuation one. Therefore $v_q(b)=0$ and $v_q(a)\ge1$. Write $a=qA$ with $A$ integral at $q$, so

$$b^2+5r=qA^2,\qquad b^2\equiv-5r\pmod q.$$

Take $t=1$, $z_1=-b$, $z_2=qA$, and use Hensel's lemma to choose $z_3^2=b^2-15r$ with $z_3\equiv-2b\pmod q$. This is a local covering point. Direct substitution gives

$$L_3=2qb^2,\qquad L_2\equiv\frac{b(3b+1)^2}{2}\pmod q.$$

If $3b+1\equiv0\pmod q$, choose the other root, $z_3\equiv2b$. Then

$$L_2\equiv-\frac{3b(b-1)^2}{2}\pmod q.$$

This square factor is nonzero in that exceptional case because $q>3$. Thus one choice always makes $L_2$ a unit. As $(2/q)=(-1/q)=(-3/q)=1$, the $L_3$ Hilbert factor is one and the $L_2$ factor is $(b/q)$. From $b^2\equiv-5r\pmod q$ this equals $(-5r/q)_4$, proving the formula.

A negative pairing value gives rank at least two for the alternating form on the three-dimensional pure Selmer space. Its radical has dimension at most one and contains the Mordell–Weil image modulo finite torsion. Hence the rational rank is at most one. Under an actual-block premise, §78's original point is nonzero in the torsion-free intersection of nonsingular subgroups, so the rank is exactly one. The rest of its integral-preimage, original Pell-index, height and denominator proof depends only on this rank bound and the unchanged original support inputs, proving the stated consumers.

This gives a quartic-symbol guard in the mutual-residue type $(1,19)$. The type $(7,13)$, the positive quartic-symbol subcase, and unrestricted higher-rank cases are not decided. No infinitude, previously surviving numerical pair, priority over all literature, or global WSS conclusion is asserted.


## 80. Direct Cassels obstruction to the golden squareclass

**Theorem 80.1 (pairing with the actual golden class).** Let $q,r$ be distinct primes satisfying

$$q\equiv1\pmod{24},\qquad r\equiv19\pmod{24},\qquad (5/q)=(5/r)=(q/r)=1.$$

Suppose integers $a,b,c$ satisfy the primitive norm-certificate conditions

$$a^2-qb^2=5qr c^2,\quad \gcd(a,b,c)=1,\quad c>0,\quad \gcd(c,30qr)=1,$$
$$24\mid a,\qquad b\equiv3c\pmod4,\qquad 5\nmid b.$$

Put $D=qr$ and $E_D:y^2=x(x+5D)(x-15D)$. In the complete two-descent pair convention $(x,x+5D)$, let $\lambda=(q,1)$ and $\sigma=(-15,5)$. These are full two-Selmer classes, and their **multiplicative** Cassels pairing is

$$\boxed{\langle\lambda,\sigma\rangle=-(b/5).}$$

Consequently, a certificate with $(b/5)=+1$ excludes $D$ as the squarefree kernel of every original golden ternary block

$$B_N=L_N^2+3=D C^2,\qquad N=3^j,\quad j\ge1,\quad C\in\mathbb Z_{>0}.$$

This conclusion includes $C=1$ and does not require an independently supplied elliptic point or a Mordell--Weil generator.

**Proof.** The corrected mutual-residue, type $(1,19)$ calculation in §§78--79 supplies both Selmer classes. The triple for $\lambda$ is $(q,1,q)$, with auxiliary conics

$$H_1:z_2^2-qz_3^2=20qr t^2,\quad H_2:z_1^2-z_3^2=15r t^2,\quad H_3:z_2^2-qz_1^2=5qr t^2.$$

Use conic points $(z_2,z_3,t)=(2a,2b,c)$ on $H_1$, $(z_2,z_1,t)=(a,b,c)$ on $H_3$, and $(z_1,z_3,t)=((15r+1)/2,(1-15r)/2,1)$ on $H_2$. Tangent forms, up to global rational factors, are

$$L_1=a z_2-qb z_3-10qr c t,$$
$$L_2=\frac{15r+1}{2}z_1-\frac{1-15r}{2}z_3-15r t,\qquad L_3=a z_2-qb z_1-5qr c t.$$

The triple for $\sigma$ is $(-15,5,-3)$. The primary tangent formula [Shukla--Stoll, §3.2, (3.9)--(3.10)](https://arxiv.org/pdf/2302.01640) therefore gives

$$\langle\lambda,\sigma\rangle=\prod_v(L_1(P_v),-15)_v(L_2(P_v),5)_v(L_3(P_v),-3)_v.$$

Here each $P_v$ is a local point of the covering, chosen off the finite tangent-zero loci. Retaining the primitive integral norm point is important: its scaling contributions cannot be discarded.

For $p\nmid30qr$, all three conics are smooth modulo $p$, their chosen conic points and tangents are primitive, and a primitive covering point projects primitively to each conic. Indeed, vanishing of all coordinates in one projection forces the remaining coordinate to vanish by another covering equation. A primitive tangent on a smooth unimodular conic has even valuation at any nonzero integral-projective evaluation: away from its tangency reduction it is a unit; near tangency, integral coordinates give

$$a_0XZ+b_0Y^2+c_0YZ+d_0Z^2=0,\qquad a_0,b_0\in\mathbb Z_p^\times,$$

with tangent $Z=0$ and $X$ a unit. Then $Z(a_0X+c_0Y+d_0Z)=-b_0Y^2$ proves even valuation. Since all three second Hilbert arguments are units, every good-prime contribution is one. This includes auxiliary primes dividing $a,b$ or $c$ individually.

At $q$, the numbers $-15,5,-3$ are local squares. At $r$, the hypotheses make $5$ a square and $r\equiv1\pmod3$ makes $-3$ a square, hence $-15$ is a square too. These places contribute one. At the real place take $a>0$, permissible by changing its sign, so $a>\sqrt q\,|b|$. For $t=1$, $z_1=z$ large and positive, choose $z_2=+\sqrt{q(z^2+5r)}$ and $z_3=+\sqrt{z^2-15r}$. Then $L_1,L_3>0$, while the second argument of the $L_2$ factor is positive. The real contribution is one.

For $p=2,3,5$ write $\alpha=a/c$, $\beta=b/c$. They are locally integral, $\alpha$ is divisible by $24$ in the relevant local sense, and $\beta$ is a unit at all three primes. At $3$ this follows from $\alpha^2-q\beta^2=5qr$; the other two cases follow from the hypotheses. Use

$$t=1,\quad z_1=-\beta,\quad z_2=\alpha,\quad z_3^2=\beta^2-15r.$$

The norm relation ensures the other conic equations. Set $\ell_1=L_1/c$, $\ell_3=L_3/c$ for these local calculations only; then $\ell_3=2q\beta^2$.

At $2$, the identity $\beta^2-15r=\alpha^2/q-20r$ has valuation two and unit part $1\pmod8$, so $z_3$ exists with valuation one. Moreover,

$$L_2\equiv3(1-\beta)\equiv2\pmod4,\qquad v_2(L_3)=1.$$

Since $-15$ is a $2$-adic square and $-3$ has squareclass $5$, the factor is $(L_2L_3,5)_2=+1$: the extension $\mathbb Q_2(\sqrt5)$ is unramified and the valuation is even.

At $3$, choose $z_3\equiv\beta\pmod3$. Then

$$\ell_1\equiv1,\qquad L_2\equiv2\beta,\qquad \ell_3\equiv2\pmod3.$$

The three normalized Hilbert factors are respectively $+1,+1,-1$. Restoring the two factors of $c$ contributes $(c,45)_3=(c,5)_3=1$, since both arguments are units. Thus the factor at $3$ is $-1$.

At $5$, choose $z_3\equiv\beta\pmod5$. Hensel expansion gives

$$z_3\equiv\beta-\frac{15r}{2\beta}\pmod{25},\qquad \ell_1\equiv\frac{5qr}{2}\pmod{25},\qquad L_2\equiv-\beta\pmod5.$$

Thus $v_5(\ell_1)=1$. The unit part $qr/2$ is a nonresidue modulo $5$, as is the unit part $-3$ of $-15$, so the odd-prime Hilbert formula gives $(\ell_1,-15)_5=+1$. The other normalized factors are $(L_2,5)_5=(\beta/5)$ and $(\ell_3,-3)_5=1$. Restoring $c$ contributes $(c,45)_5=(c,5)_5=(c/5)$, giving total $(b/5)$. Multiplication over all places proves the boxed formula.

If an original block existed, its genuine rational point $R=(5D B_N,25D^2L_N C F_N)$ and translate $S=R+(0,0)$ would satisfy

$$X(S)=-15/C^2,\qquad X(S)+5D=5L_N^2/C^2.$$

Its descent pair is exactly $\sigma=(-15,5)$. The rational Mordell--Weil image lies in the Cassels-pairing radical, as recalled in the cited paper's introduction, so $\langle\lambda,\sigma\rangle=+1$. Hence every such certificate must satisfy $(b/5)=-1$. A certificate with the opposite symbol excludes the original block for every $C$. No finiteness assumption on $\Sha$ is used. This argument does not use the rank-one guard of §79 and remains valid when that section's quartic symbol is $+1$. ∎

**Certificate-choice independence.** The sign in Theorem 80.1 cannot be freely changed by choosing another normalized primitive norm certificate. For two such points $Q=(a,b,c)$ and $Q'=(a',b',c')$, put $G=aa'-qbb'-5qrcc'$. If $G\ne0$, the Gram determinant identity on $H_3$ gives, at a common evaluation point away from tangent zeros,

$$2G L_3L'_3=5q^2r\det(Q,Q',P)^2.$$

Thus $L'_3/L_3$ has squareclass $k=5q^2r/(2G)$. On $H_1$ the corresponding points are $(2a,2b,c)$ and $(2a',2b',c')$, their inner product is $4G$, and the quadratic-form determinant is $20q^2r$. Since $L_1$ is half the associated bilinear evaluation, $L'_1/L_1$ has the same squareclass $k$. The global pairing ratio is therefore

$$\prod_v(k,-15)_v(k,-3)_v=\prod_v(k,5)_v=1$$

by Hilbert reciprocity. If $G=0$, the two isotropic vectors are orthogonal in a nondegenerate ternary quadratic space and hence proportional; primitivity and $c,c'>0$ make the representatives equal. Consequently every admissible certificate has the same $(b/5)$. Weak approximation on the rational conic controls $\beta=b/c$, but does not control the $5$-character of the primitive global denominator $c$; the retained factor $(c/5)$ is essential.

**Corollary 80.2 (an explicit conditional prime family).** Let $q$ be prime, $q\equiv1\pmod{24}$ and $(5/q)=1$. Suppose integers $A,b$ satisfy

$$24\mid A,\quad b\equiv3\pmod4,\quad \gcd(qA,b)=1,\quad (b/5)=+1,$$

and

$$r=(qA^2-b^2)/5$$

is a positive prime greater than $5$, distinct from $q$, with $(5/r)=1$. Then $qr$ cannot be the squarefree kernel of any original golden ternary block.

**Proof.** Set $a=qA,c=1$. The norm equation and primitive certificate conditions follow immediately. Coprimality forces $\gcd(b,6)=1$, so $r\equiv-5\equiv19\pmod{24}$. Reduction modulo $q$ gives $(r/q)=(-5/q)=1$, and reciprocity gives $(q/r)=1$. Apply Theorem 80.1. ∎

For a potentially additional family one may impose $qr\equiv19\pmod{120}$; otherwise the old squarefree-kernel congruence already excludes it. All certificate and primality premises are retained. No existence or infinitude of prime values, previously surviving numerical pair, independence from every earlier support condition, exhaustive priority claim, or universal WSS exclusion is asserted.


## 81. A fixed-golden-field residue test from the original orbit

Write $\mathcal R(a,b,c)=(-1)^{[a,b,c]}$ for the multiplicative version of Stevenhagen's additive Rédei symbol. We use [Stevenhagen, *Rédei reciprocity, governing fields, and negative Pell*](https://arxiv.org/pdf/1806.06250), Corollary 5.2, Definitions 7.5--7.8, Theorem 7.9, and equations (45)--(48). The defining hypotheses are pairwise Hilbert symbols $+1$ at every place and $\gcd(\Delta(a),\Delta(b),\Delta(c))=1$; the discriminants need not be pairwise coprime. All infinite and dyadic conditions below are retained.

**Theorem 81.1 (the original Fibonacci coordinate supplies the extension).** Let $q,r$ be distinct primes with

$$q\equiv1\pmod{24},\qquad r\equiv19\pmod{24},\qquad (5/q)=(5/r)=(q/r)=1,$$

and put $D=qr$. If $B_N=L_N^2+3=D C^2$ for $N=3^j$, where $j,C$ are positive integers, then

$$\boxed{\mathcal R(5,-D,q)=\mathcal R(5,q,-D)=1.}$$

**Proof.** For $(5,-D,q)$ the discriminants are $5,-D,q$, whose three-way gcd is one. The Hilbert symbols $(5,q)_p$ are trivial by $5$-splitting and $q\equiv1\pmod8$. For $(5,-D)_p$, the places $q,r,5$ give $(5/q),(5/r),(-D/5)=1$; at $2$ both arguments are $1\pmod4$. For $(-D,q)_p$, the places $q,r$ give $(r/q),(q/r)=1$, using $(-q,q)_q=1$, while $q$ is a square at $2$. All other finite places are unit pairs; the infinite symbols are trivial. Thus the primary theorem applies, including the shared ramified argument $q$.

The original identities and the Fibonacci recurrence modulo four give

$$5F_N^2-1=D C^2,\qquad F_N\equiv2\pmod4.$$

Indeed, $N\equiv3\pmod6$ and the Fibonacci recurrence modulo four has period six. In $K_0=\mathbb Q(\sqrt5)$, with $\mathcal O_0=\mathbb Z[\phi]$ and $\phi=(1+\sqrt5)/2$, set

$$\beta=-1-F_N\sqrt5=(F_N-1)-2F_N\phi\equiv1\pmod{4\mathcal O_0},\qquad N_{K_0/\mathbb Q}(\beta)=-D C^2.$$

Put $E=\mathbb Q(\sqrt5,\sqrt{-D})$, $K=\mathbb Q(\sqrt{-5D})$, and $F=E(\sqrt\beta)$. The norm-field construction in Corollary 5.2 makes $F/K$ cyclic quartic and $F/E$ quadratic. We check that $F/K$ is unramified at every finite place, which suffices for Definition 7.6 here.

At an odd $p\nmid5D$, the elements $\beta,\bar\beta$ cannot have a common prime divisor above $p$, since their sum is $-2$. At a split prime dividing $C$, exactly one has positive valuation, and that valuation is even; an inert prime cannot divide either. Hence adjoining $\sqrt\beta$ is unramified, as are the quadratic factors defining $E$ and $K$ at such $p$. This includes every additional prime and repeated power in $C$.

At $p=q$ or $r$, choose the split place of $K_0$ where $F_N\sqrt5\equiv1\pmod p$. There $\beta\equiv-2$ is a unit; at the conjugate place its valuation is $1+2v_p(C)$. Since $\beta\bar\beta=-D C^2$ is a square in $E$, either conjugate defines the same quadratic extension of $E$. Locally $E/K$ is trivial because $5$ is a square in $\mathbb Q_p$, and the unit description makes $F/K$ unramified. At $5$, $-D$ is a square in $\mathbb Q_5$, so again locally $E=K$; $\beta$ is a unit with residue $-1$, and its quadratic extension is unramified.

At $2$, the ring $\mathcal O_0\otimes\mathbb Z_2$ is unramified quadratic. Write $\beta=1+4t$. The element $(1+\sqrt\beta)/2$ satisfies $T^2-T-t$, whose derivative is a unit modulo two, so adjoining $\sqrt\beta$ is unramified. Also $5\equiv-D\equiv5\pmod8$ and $-5D\equiv1\pmod8$: $K$ is split at two and $E$ is unramified quadratic. Thus $F/K$ is unramified there as well. This uses the full golden integer ring.

The resulting extension is minimally ramified in the primary definition. Equations (45)--(48) evaluate the third argument $q$ at the conjugate-unit place, giving

$$\mathcal R(5,-D,q)=(-2/q)=1.$$

This remains valid when $q\mid C$, since the unit residue is still $-2$. Rédei reciprocity proves the other equality. ∎

**Theorem 81.2 (an explicit residue test).** Under the prime hypotheses of Theorem 81.1, suppose

$$q=u^2-5v^2,\qquad u>0,\quad u\equiv1\pmod4,\quad4\mid v.$$

For either root $s^2\equiv5\pmod r$, every original block in Theorem 81.1 requires

$$\boxed{\left(\frac{u+vs}{r}\right)=\left(\frac{2u}{q}\right)=\left(\frac{u}{5}\right).}$$

Thus the opposite sign excludes $D$ as the squarefree kernel for every $C$ and every ternary index.

**Proof.** The element $\gamma=u+v\sqrt5$ has norm $q$, is totally positive, and is $1\pmod{4\mathcal O_0}$. Primality gives $\gcd(u,v)=1$ and $q\nmid2u$. The field $F_q=\mathbb Q(\sqrt5,\sqrt q,\sqrt\gamma)$ is minimally ramified over $K_q=\mathbb Q(\sqrt{5q})$. At odd primes outside $5q$, $\gamma$ is a unit. At $5$ it is a unit and $q$ splits. At $q$, the conjugate unit is $2u$; since $\gamma\bar\gamma=q$ is a square in $E_q=\mathbb Q(\sqrt5,\sqrt q)$, one has $E_q(\sqrt\gamma)=E_q(\sqrt{\bar\gamma})$, allowing that unit conjugate or its corresponding conjugate prime. The same local argument as in Theorem 81.1 gives unramified extension at these primes. At two, $\gamma\equiv1\pmod{4\mathcal O_0}$ and $q\equiv1\pmod8$ give unramified extension by the same étale quadratic polynomial.

The negative third argument in $\mathcal R(5,q,-D)$ includes infinity. Total positivity of $\gamma$ makes that factor $+1$. The finite factors at $q,r$ are $(2u/q)$ and $(u+vs/r)$. The two choices of $s$ have product of residues $q$, whose Legendre symbol modulo $r$ is $+1$, so the factor is independent of the choice. Hence

$$\mathcal R(5,q,-D)=\left(\frac{2u}{q}\right)\left(\frac{u+vs}{r}\right).$$

Theorem 81.1 gives the first boxed equality. Since $q\equiv1\pmod8$, $u>0$ is odd and $u\equiv1\pmod4$, quadratic reciprocity for Jacobi symbols gives

$$\left(\frac{2u}{q}\right)=\left(\frac{u}{q}\right)=\left(\frac{q}{u}\right)=\left(\frac{-5v^2}{u}\right)=\left(\frac{-5}{u}\right)=\left(\frac{u}{5}\right).$$

Coprimality makes all these symbols defined and removes $v^2$. ∎

**Theorem 81.3 (the primary generator exists on actual golden support).** Let $q$ be a prime. If $q\equiv1\pmod{24}$, $(5/q)=1$, and the original golden rank is $\rho(q)=6N$ with $N$ odd, then integers $u,v$ satisfying the representation and sign conditions of Theorem 81.2 exist. Therefore that representation is not an extra existence premise for an actual pair in Theorem 81.1.

**Proof.** The triple $(5,-1,q)$ is admissible: $\phi$ has norm $-1$, the pair $(5,q)$ is locally split, $(-1,q)_p=1$ at every place because $q\equiv1\pmod4$, and $\gcd(5,-4,q)=1$. The norm element $\phi$ defines

$$F_0=\mathbb Q(\sqrt5,i,\sqrt\phi)=\mathbb Q(\sqrt5,i,\sqrt{1+2i}).$$

For example, if $w^2=\phi$, then $(w+i/w)^2=1+2i$, or equivalently $(\phi+i)^2=\phi(1+2i)$. At odd primes $\phi$ is a unit; the norm-field construction is unramified at the remaining odd ramified place $5$. At two this is exactly the $2$-minimally ramified model displayed immediately before Stevenhagen's Definition 7.5 for $(a,b)=(-1,5)$. Thus

$$\mathcal R(5,-1,q)=\left(\frac{\phi\bmod q}{q}\right).$$

Either split embedding gives the same sign because $N(\phi)=-1$ and $(-1/q)=1$. Binet's formula identifies the original rank with the order of $-\phi^2$. From $\operatorname{ord}_q(-\phi^2)=6N$ and $N$ odd, its $3N$-th power is $-1$, giving $\phi^{6N}=1$. Since $q\equiv1\pmod8$ and $6N\mid q-1$, one has $6N\mid(q-1)/2$, so $\phi$ is a quadratic residue. Reciprocity now gives $\mathcal R(5,q,-1)=1$.

The ring $\mathcal O_0$ is norm-Euclidean: rounding both coefficients in the basis $1,\phi$ leaves $t+s\phi$ with $|t|,|s|\le1/2$, and

$$|N(t+s\phi)|=|t^2+ts-s^2|\le5/16<1.$$

Thus a prime above $q$ has a generator of norm $\pm q$; multiplication by $\phi$ if needed gives a generator $\pi$ of norm $q$. The unit group of $\mathcal O_0/4\mathcal O_0$ has twelve elements. Its norm-to-$(\mathbb Z/4)^\times$ kernel has six elements, exactly $\{\pm\phi^{2k}:k=0,1,2\}$: $\phi$ has norm $-1$, $\phi^2$ has order three modulo four, and $-1$ has order two. Since $N(\pi)\equiv1\pmod4$, multiplication by one of these global norm-one units produces $\delta\equiv1\pmod{4\mathcal O_0}$ with norm $q$.

The finite-prime argument of Theorem 81.2, which uses norm $q$ and the primary congruence but not positivity, makes $\mathbb Q(\sqrt5,\sqrt q,\sqrt\delta)$ a permitted minimally ramified field. Its infinite Artin factor is $\mathcal R(5,q,-1)=1$. The two real signs of $\delta$ agree because its norm is positive, so triviality of this factor forces total positivity.

Finally write $\delta=1+4(m+n\phi)=u+v\sqrt5$, with $u=1+4m+2n$ and $v=2n$. If $n$ were odd, then $q=u^2-5v^2\equiv5\pmod8$, contradicting $q\equiv1\pmod8$. Thus $4\mid v$, $u\equiv1\pmod4$, and total positivity gives $u>0$. ∎

For an actual block, the existing rank input TBN3 supplies $\rho(q)=6N$, so Theorems 81.2--81.3 give a residue test using a constructible primary prime generator in the fixed golden field and the second prime. They do not require the auxiliary norm certificate of §80 or use weak approximation to choose its sign. The relation with every earlier Cassels and support condition has not been classified; no independence from all prior tests, previously surviving numerical pair, prime-family infinitude, or universal WSS exclusion is asserted. The residue type $(7,13)$ remains outside these statements.


The companion residue type $(7,13)$ is treated in [Theorem 82.1 of the continuation](GOLDEN_CUBIC_BLOCK_PRIME_PERIODS_CONTINUATION.md#82-the-second-mutual-residue-type), with its distinct dyadic minimality condition and negative Rédei value.

## 追加锚（本行以下为增补区）
