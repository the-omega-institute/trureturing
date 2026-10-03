# Frobenius bounds for golden matrix periods

> This volume uses `generic-v1` digestion. Its existing text is append-only;
> later corrections belong in a new numbered section after the final append
> anchor.

## 1. Scope and notation

This volume is mathematical reference input. Formal truth is determined by the
Lean declarations and their axiom closures, not by this prose. Let $F_0=0$,
$F_1=1$, and $F_{n+2}=F_{n+1}+F_n$. For a prime $p>5$, write

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\tau_p=\operatorname{ord}_{\operatorname{Mat}_2(\mathbb Z/p\mathbb Z)}(Q),
\qquad \varepsilon_p=\left(\frac{5}{p}\right).
$$

The matrix $Q$ is invertible modulo $p$: its determinant is $-1$.
Consequently $\tau_p$ is positive. Since $p>5$, the Legendre symbol
$\varepsilon_p$ is either $1$ or $-1$.

## 2. Prime-branch period bounds

**Theorem 2.1 (golden Frobenius bounds).** For every prime $p>5$, both
implications below hold:

$$
\begin{aligned}
\varepsilon_p=1
  &\quad\Longrightarrow\quad \tau_p\mid p-1
     \quad\text{and}\quad p\nmid\tau_p,\\
\varepsilon_p=-1
  &\quad\Longrightarrow\quad \tau_p\mid 2(p+1)
     \quad\text{and}\quad p\nmid\tau_p.
\end{aligned}
$$

Proof. The Fibonacci entry congruences give
$F_{p-\varepsilon_p}\equiv0\pmod p$ and
$F_p\equiv\varepsilon_p\pmod p$. In the golden quadratic algebra over
$\mathbb Z/p\mathbb Z$, let $\phi^2=\phi+1$. Its power coordinates satisfy
$\phi^n=F_{n-1}+F_n\phi$ for $n\geq1$. Multiplication by $\phi$ on the
basis $(\phi,1)$ is the matrix $Q$, and the multiplication-matrix map is
injective. Thus $\phi$ and $Q$ have the same multiplicative order.

If $\varepsilon_p=1$, then $F_{p-1}\equiv0$ and $F_p\equiv1$, so
$\phi^p=\phi$. The identity $\phi(\phi-1)=1$ makes $\phi$ a unit; hence
$\phi^{p-1}=1$ and $\tau_p\mid p-1$.

If $\varepsilon_p=-1$, then $F_{p+1}\equiv0$ and $F_p\equiv-1$, so
$\phi^{p+1}=-1$. Squaring gives $\phi^{2(p+1)}=1$, and therefore
$\tau_p\mid2(p+1)$.

Finally, $p$ divides neither $p-1$ nor $2(p+1)$: in the latter case,
primality would force $p\mid2$ or $p\mid p+1$, both impossible for
$p>5$. The corresponding divisibility bound in each branch therefore
implies $p\nmid\tau_p$.

## 3. Source and verification boundary

The entry congruences are the result named
`fibonacci_apparition_entry_point` in `D5/S3/Arith/GoldenApparition.lean`.
The faithful multiplication-matrix representation is the result named
`golden_matrix_faithful` in `D5/S3/Arith/GoldenMatrixPeriodBridge.lean`.
The exact two-branch statement appears as `golden_prime_period_bounds` in
`D5/S3/Arith/GoldenPrimePeriodBounds.lean`. This volume adds no assertion
that either divisibility bound is always an equality. Its literature status
is `repo-derived`; no independent originality claim is made.

## 追加锚（本行以下为增补区）
