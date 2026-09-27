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
