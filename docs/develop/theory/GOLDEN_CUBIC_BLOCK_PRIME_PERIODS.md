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
