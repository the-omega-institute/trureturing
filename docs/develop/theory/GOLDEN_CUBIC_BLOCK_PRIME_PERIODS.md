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

## 8. Cubic coordinate discriminant and index form

For $j\geq1$ put $B_j=L_{3^j}^2+3$ and $a_j=(B_j-1)/9$; Theorem 4.1
shows that $a_j$ is an integer. Use the free rank-three integer
coordinate ring with basis $(1,\theta,\beta)$ and multiplication
$\theta^2=3\beta-\theta-1$,
$\theta\beta=\beta+3a_j$, and
$\beta^2=\beta+a_j\theta+2a_j$.
Let $G_j$ be its regular-trace Gram matrix on this basis. For
$\alpha=r+b\theta+c\beta$, let $I_j(r,b,c)$ be the matrix whose columns
are the coordinates of $(1,\alpha,\alpha^2)$ on the same basis.

**Theorem 8.1 (coordinate discriminant and signed index form).** For every
$j\geq1$ and every $r,b,c\in\mathbb Z$,

$$
\begin{aligned}
\det G_j&=-3B_j^2,\\
\det I_j(r,b,c)&=3b^3+3b^2c+bc^2-a_jc^3,\\
9\det I_j(r,b,c)&=(3b+c)^3-B_jc^3.
\end{aligned}
$$

The multiplication table gives
$G_j=\begin{pmatrix}3&0&1\\0&0&B_j\\1&B_j&6a_j+1\end{pmatrix}$.
Its determinant is the first formula. Multiplying $\alpha$ in the
coordinate ring gives the second determinant, and $B_j=9a_j+1$ gives
the third. These are statements about the constructed coordinate ring;
identifying it with an order in $\mathbb Q(\sqrt[3]{B_j})$ and computing
the maximal-order index remain separate GIR1 obligations.

## 追加锚（本行以下为增补区）
